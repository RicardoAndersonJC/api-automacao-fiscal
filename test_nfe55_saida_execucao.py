"""Fluxo da execução: chave real nas pendências, uma onda por execução e cursor no fim."""

import unittest
from pathlib import Path
from unittest.mock import MagicMock, patch

import requests

import nfe55_saida_worker as worker
from nfe55_saida_discovery import chave_artificial, modulo11_dv
from nfe55_saida_transport import Rota

CFG = {
    "cUF": "27", "AAMM": "2611", "CNPJ": "12345678000199", "modelo": "55", "serie": "001",
    "tpEmis": "1", "nNF_semente": 9, "chave_semente": "2" * 44,
}


def chave_real(n: int, aamm: str = "2611") -> str:
    base = chave_artificial(CFG, n, aamm)[:35] + "73918264"
    return base + modulo11_dv(base)


def pendencia(n: int, com_chave: bool = True) -> dict:
    item = {"aamm": "2611", "nnf": n, "ultimo_erro": "O portal não devolveu o XML desta chave."}
    if com_chave:
        item["chave"] = chave_real(n)
    return item


class ExecucaoTest(unittest.TestCase):
    def executar(self, lacunas=(), baixar=None, consultar=None, opcoes=None):
        eventos: list[tuple[str, dict]] = []

        def callback(run_id, token, evento, **dados):
            eventos.append((evento, dados))
            return False

        rotas = [Rota("r1", "http://10.0.0.1:8080"), Rota("r2", "http://10.0.0.2:8080")]
        worker._vaga.acquire(blocking=False)
        base = {"chave": CFG["chave_semente"], "max_numeracoes": 1, "stop_217": 3, "lacunas_abertas": list(lacunas)}
        base.update(opcoes or {})
        with patch.object(worker, "_pfx", return_value=(Path("c.pem"), Path("k.pem"))), \
                patch.object(worker, "cfg_da_chave", return_value=dict(CFG)), \
                patch.object(worker, "_rotas_proxy", return_value=rotas), \
                patch.object(worker, "_lote_ativo", return_value=True), \
                patch.object(worker, "_tamanho_lote", return_value=2), \
                patch.object(worker, "_abrir_sessao", return_value=MagicMock()), \
                patch.object(worker, "_ponto_de_partida", return_value=("2611", 10)), \
                patch.object(worker.time, "sleep"), \
                patch.object(worker, "_baixar_na_faixa", side_effect=baixar or (lambda *a, **k: ("", "sem_xml"))), \
                patch.object(worker, "_consultar", side_effect=consultar or (lambda *a, **k: "<cStat>217</cStat>")), \
                patch.object(worker, "_callback", side_effect=callback):
            worker._executar("run", "tok", b"", b"pfx", "senha", base)
        return eventos

    def test_pendencia_usa_a_chave_real_e_uma_onda_por_execucao(self):
        chamadas = []

        def baixar(cert, key, ch, transporte, limitador, avisar=None):
            chamadas.append(ch)
            return f"<nfeProc>{ch}</nfeProc>", ""

        eventos = self.executar([pendencia(n) for n in range(1, 7)], baixar=baixar)
        self.assertEqual(chamadas, [chave_real(1), chave_real(2)])
        fim = [d for e, d in eventos if e == "done"][-1]
        self.assertEqual(fim["salvas"], 2)
        self.assertIn("guardadas para a próxima vez", fim["mensagem"])

    def test_onda_sem_xml_para_os_downloads_e_informa_o_motivo(self):
        chamadas = []

        def baixar(cert, key, ch, transporte, limitador, avisar=None):
            chamadas.append(ch)
            return "", "timeout"

        eventos = self.executar([pendencia(n) for n in range(1, 7)], baixar=baixar)
        self.assertEqual(len(chamadas), 2)
        falhas = [d for e, d in eventos if e == "download_falhou"]
        self.assertTrue(all("Tempo esgotado" in d["erro"] for d in falhas))
        self.assertIn("não devolveu XML neste lote", [d for e, d in eventos if e == "done"][-1]["mensagem"])

    def test_pendencia_sem_chave_e_reconsultada_antes_do_download(self):
        chamadas = []
        consultas = []

        def consultar(sessao, cfg, nnf, aamm):
            consultas.append((aamm, nnf))
            if nnf == 5:
                return f"<cStat>613</cStat><xMotivo>Chave difere [{chave_real(5)}]</xMotivo>"
            return "<cStat>217</cStat>"

        def baixar(cert, key, ch, transporte, limitador, avisar=None):
            chamadas.append(ch)
            return f"<nfeProc>{ch}</nfeProc>", ""

        eventos = self.executar([pendencia(5, com_chave=False)], baixar=baixar, consultar=consultar)
        self.assertEqual(consultas[0], ("2611", 5))
        self.assertEqual(chamadas, [chave_real(5)])
        self.assertNotIn(chave_artificial(CFG, 5, "2611"), chamadas)
        descobertas = [d for e, d in eventos if e == "descoberta"]
        self.assertEqual(descobertas[0]["chave"], chave_real(5))

    def test_fim_da_numeracao_volta_o_cursor_e_nao_cria_lacunas(self):
        eventos = self.executar(opcoes={"max_numeracoes": 50})
        fim = [d for e, d in eventos if e == "done"][-1]
        self.assertEqual((fim["aamm"], fim["nnf"]), ("2611", 10))
        self.assertEqual(fim["lacunas"], [])
        self.assertFalse([d for e, d in eventos if e == "descoberta"])

    def test_erro_na_consulta_guarda_o_cursor(self):
        def consultar(*a, **k):
            raise requests.ReadTimeout("Read timed out. (read timeout=75)")

        eventos = self.executar(consultar=consultar)
        evento, dados = eventos[-1]
        self.assertEqual(evento, "error")
        self.assertEqual((dados["aamm"], dados["nnf"]), ("2611", 10))
        self.assertIn("timed out", dados["erro"])


if __name__ == "__main__":
    unittest.main()
