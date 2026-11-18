"""Fluxo da execução: lote recusado nos mesmos IPs e cursor guardado em falha."""

import unittest
from pathlib import Path
from unittest.mock import MagicMock, patch

import requests

import nfe55_saida_worker as worker
from nfe55_saida_transport import Rota

CFG = {"CNPJ": "12345678000199", "AAMM": "2611", "nNF_semente": 9, "chave_semente": "2" * 44}


def chave(n: int) -> str:
    return f"27{'2611'}12345678000199550010{n:09d}1{'0' * 8}"[:44].ljust(44, "0")


class ExecucaoTest(unittest.TestCase):
    def executar(self, chaves_faltantes, baixar=None, consultar=None):
        eventos: list[tuple[str, dict]] = []

        def callback(run_id, token, evento, **dados):
            eventos.append((evento, dados))
            return False

        rotas = [Rota("r1", "http://10.0.0.1:8080"), Rota("r2", "http://10.0.0.2:8080")]
        worker._vaga.acquire(blocking=False)
        with patch.object(worker, "_pfx", return_value=(Path("c.pem"), Path("k.pem"))), \
                patch.object(worker, "cfg_da_chave", return_value=dict(CFG)), \
                patch.object(worker, "_rotas_proxy", return_value=rotas), \
                patch.object(worker, "_lote_ativo", return_value=True), \
                patch.object(worker, "_tamanho_lote", return_value=2), \
                patch.object(worker, "_abrir_sessao", return_value=MagicMock()), \
                patch.object(worker, "_ponto_de_partida", return_value=("2611", 10)), \
                patch.object(worker, "chaves_para_recuperar", return_value=chaves_faltantes), \
                patch.object(worker, "_baixar_na_faixa", side_effect=baixar or (lambda *a, **k: ("", "sem_xml"))), \
                patch.object(worker, "_consultar", side_effect=consultar or (lambda *a, **k: "")), \
                patch.object(worker, "_callback", side_effect=callback):
            worker._executar("run", "tok", b"", b"pfx", "senha", {"chave": CFG["chave_semente"], "max_numeracoes": 1})
        return eventos

    def test_para_quando_o_lote_seguinte_volta_todo_sem_xml(self):
        chamadas = []

        def baixar(cert, key, ch, transporte, limitador, avisar=None):
            chamadas.append(ch)
            if len(chamadas) <= 2:
                return f"<nfeProc>{ch}</nfeProc>", ""
            return "", "timeout"

        faltantes = [chave(n) for n in range(1, 7)]
        eventos = self.executar(faltantes, baixar=baixar)
        self.assertEqual(len(chamadas), 4, "não deve tentar o 3º lote")
        falhas = [d for e, d in eventos if e == "download_falhou"]
        self.assertEqual(len(falhas), 2)
        self.assertTrue(all("Tempo esgotado" in d["erro"] for d in falhas))
        fim = [d for e, d in eventos if e == "done"]
        self.assertEqual(len(fim), 1)
        self.assertIn("próxima vez", fim[0]["mensagem"])
        self.assertEqual(fim[0]["salvas"], 2)

    def test_primeiro_lote_sem_xml_nao_encerra(self):
        chamadas = []

        def baixar(cert, key, ch, transporte, limitador, avisar=None):
            chamadas.append(ch)
            return "", "sem_xml"

        with patch.object(worker, "avancar_sobre_recuperadas", return_value=("2611", 10)), \
                patch.object(worker, "avancar", side_effect=RuntimeError("parar aqui")):
            eventos = self.executar([chave(n) for n in range(1, 5)], baixar=baixar)
        self.assertEqual(len(chamadas), 4, "sem XML salvo antes, não é recusa dos mesmos IPs")
        self.assertEqual(eventos[-1][0], "error")

    def test_erro_na_consulta_guarda_o_cursor(self):
        def consultar(*a, **k):
            raise requests.ReadTimeout("Read timed out. (read timeout=75)")

        eventos = self.executar([], consultar=consultar)
        evento, dados = eventos[-1]
        self.assertEqual(evento, "error")
        self.assertEqual((dados["aamm"], dados["nnf"]), ("2611", 10))
        self.assertIn("timed out", dados["erro"])


if __name__ == "__main__":
    unittest.main()
