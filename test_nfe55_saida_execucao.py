"""Fluxo da execução: chave real nas pendências, uma onda por execução e cursor no fim."""

import unittest
from datetime import datetime, timedelta, timezone
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

        def baixar(cert, key, ch, transporte, limitador, avisar=None, bloqueio=None):
            chamadas.append(ch)
            return f"<nfeProc>{ch}</nfeProc>", ""

        eventos = self.executar([pendencia(n) for n in range(1, 7)], baixar=baixar)
        self.assertEqual(chamadas, [chave_real(1), chave_real(2)])
        fim = [d for e, d in eventos if e == "done"][-1]
        self.assertEqual(fim["salvas"], 2)
        self.assertIn("guardadas para a próxima vez", fim["mensagem"])

    def test_onda_sem_xml_para_os_downloads_e_informa_o_motivo(self):
        chamadas = []

        def baixar(cert, key, ch, transporte, limitador, avisar=None, bloqueio=None):
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

        def baixar(cert, key, ch, transporte, limitador, avisar=None, bloqueio=None):
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


class PaginaPortalTest(unittest.TestCase):
    def test_classifica_pagina_sem_xml(self):
        self.assertEqual(worker.classificar_pagina(200, "", "<p>Muitas consultas. Tente novamente mais tarde</p>")[0], "limite")
        self.assertEqual(worker.classificar_pagina(200, "", "<div>NF-e inexistente na base</div>")[0], "indisponivel")
        self.assertEqual(worker.classificar_pagina(200, "https://x/Erro/Forbidden", "")[0], "acesso")
        self.assertEqual(worker.classificar_pagina(200, "", "<html>ok</html>")[0], "sem_xml")
        self.assertIn("indisponível", worker._motivo_download("indisponivel"))

    def test_pagina_de_limite_vira_limite_no_download(self):
        class Limitador:
            limitado = 0

            def begin_download(self, notify_wait=None, lane="download"):
                return "call", None

            def note_remote_limit(self):
                self.limitado += 1

            def finish_download_probe(self, probe, *, succeeded):
                return None

        limitador = Limitador()
        with patch.object(worker, "_baixar", side_effect=worker.PortalSemXml("limite", "bloqueio")):
            xml, erro = worker._baixar_na_faixa(Path("c"), Path("k"), "1" * 44, worker.saida_rede.GestorSaida([Rota("r", "http://10.0.0.9:8080")], enabled=True), limitador)
        self.assertEqual((xml, erro, limitador.limitado), ("", "limite", 1))

    def test_sonda_com_limite_para_o_lote_e_guarda_o_horario_do_bloqueio(self):
        chamadas = []
        fim = datetime.now(timezone.utc) + timedelta(hours=3)

        def baixar(cert, key, ch, transporte, limitador, avisar=None, bloqueio=None):
            chamadas.append(ch)
            if bloqueio is not None:
                bloqueio.registrar(fim)
            return "", "limite"

        eventos = ExecucaoTest.executar(self, [pendencia(n) for n in range(1, 7)], baixar=baixar)
        self.assertEqual(len(chamadas), 1)  # só a sonda: as outras chaves não gastam tentativa
        done = [d for e, d in eventos if e == "done"][-1]
        quando = worker.texto_bloqueio(fim.replace(second=0, microsecond=0))
        self.assertIn(f"Download bloqueado pela SVRS até {quando}", done["mensagem"])
        self.assertEqual(done["svrs_bloqueado_ate"][:16], fim.isoformat()[:16])
        falha = [d for e, d in eventos if e == "download_falhou"][0]
        self.assertIn("bloqueado pela SVRS até", falha["erro"])

    def test_sonda_ok_libera_o_restante_do_lote(self):
        chamadas = []

        def baixar(cert, key, ch, transporte, limitador, avisar=None, bloqueio=None):
            chamadas.append(ch)
            return "<xml/>", ""

        with patch.object(worker, "_callback", return_value=False):
            rotas = [Rota(f"r{i}", f"http://10.0.0.{i}:8080") for i in range(1, 5)]
            with patch.object(worker, "_baixar_na_faixa", side_effect=baixar),                     patch.object(worker, "_tamanho_lote", return_value=4):
                saida = worker._descarregar_lote(Path("c"), Path("k"), [chave_real(n) for n in range(1, 5)], rotas, sondar=True)
        self.assertEqual(len(chamadas), 4)
        self.assertEqual(chamadas[0], chave_real(1))
        self.assertEqual([c for c, _x, _e in saida], [chave_real(n) for n in range(1, 5)])

    def test_le_o_horario_de_bloqueio_da_pagina(self):
        ate = worker.bloqueado_ate_svrs("Acesso ao Download do XML bloqueado at&eacute; 19/11/2026 20:12")
        self.assertEqual(ate, datetime(2026, 11, 19, 23, 12, tzinfo=timezone.utc))
        self.assertIsNone(worker.bloqueado_ate_svrs("Consulta normal"))

    def test_bloqueio_ignora_passado_e_limita_a_24h(self):
        bloqueio = worker.Bloqueio()
        bloqueio.registrar(datetime.now(timezone.utc) - timedelta(minutes=5))
        self.assertIsNone(bloqueio.ate)
        bloqueio.registrar(datetime.now(timezone.utc) + timedelta(days=5))
        self.assertLessEqual(bloqueio.ate, datetime.now(timezone.utc) + timedelta(hours=24, seconds=1))

    def test_frase_de_bloqueio_de_ip_e_limite(self):
        for texto in ("IP não autorizado devido múltiplas consultas", "IP n&atilde;o autorizado devido m&uacute;ltiplas consultas"):
            self.assertEqual(worker.classificar_pagina(200, "", texto), ("limite", "ip bloqueado"))

    def test_download_usa_cabecalhos_de_navegador(self):
        chamadas = []

        class Resposta:
            def __init__(self, url, texto):
                self.url, self.text, self.status_code = url, texto, 200

        def enviar(sessao, dono, metodo, url, **kwargs):
            chamadas.append((metodo, kwargs.get("headers") or {}))
            if metodo == "get":
                return Resposta("https://dfe-portal.svrs.rs.gov.br/NFeSSL/DownloadXMLDFe?x=1", '<input name="__T" value="1">')
            return Resposta(url, "IP não autorizado devido múltiplas consultas")

        with patch.object(worker, "_abrir_sessao_rota", return_value=MagicMock()),                 patch.object(worker, "_enviar_rota", side_effect=enviar):
            with self.assertRaises(worker.PortalSemXml) as erro:
                worker._baixar(Path("c"), Path("k"), "1" * 44, transporte=MagicMock())
        self.assertEqual(erro.exception.categoria, "limite")
        get, post = chamadas
        self.assertIn("Mozilla/5.0", get[1]["User-Agent"])
        self.assertEqual(post[1]["Origin"], "https://dfe-portal.svrs.rs.gov.br")
        self.assertEqual(post[1]["Referer"], "https://dfe-portal.svrs.rs.gov.br/NFeSSL/DownloadXMLDFe?x=1")


if __name__ == "__main__":
    unittest.main()
