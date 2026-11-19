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
    def setUp(self):
        worker._ritmos.clear()

    def tearDown(self):
        worker._ritmos.clear()

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
        # Lote de 2, cada chave repetida até 3 vezes como no código base.
        self.assertEqual(len(chamadas), 2 * worker.TENTATIVAS_POR_CHAVE)
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


class RitmoTest(unittest.TestCase):
    def relogio(self):
        estado = {"t": 0.0}
        return estado, (lambda: estado["t"]), (lambda s: estado.__setitem__("t", estado["t"] + s))

    def test_ritmo_igual_ao_codigo_base(self):
        estado, clock, sleep = self.relogio()
        ritmo = worker.RitmoCertificado(55, 5, clock=clock, sleep=sleep)
        self.assertEqual(ritmo.restante(), 0.0)  # primeiro download não espera
        ritmo.sucesso(primeira=True)
        estado["t"] = 20
        self.assertEqual(ritmo.restante(), 35.0)  # conta desde o último sucesso
        ritmo.recusa()
        self.assertEqual(ritmo.intervalo, 60.0)
        estado["t"] = 50
        self.assertEqual(ritmo.espera_repeticao(), 10.0)  # recusa não zera o relógio
        for _ in range(3):
            ritmo.sucesso(primeira=True)
        self.assertEqual(ritmo.intervalo, 55.0)
        for _ in range(40):
            ritmo.recusa()
        self.assertEqual(ritmo.intervalo, worker.INTERVALO_MAXIMO)

    def test_sem_sucesso_repete_apos_um_passo(self):
        _estado, clock, sleep = self.relogio()
        ritmo = worker.RitmoCertificado(55, 5, clock=clock, sleep=sleep)
        ritmo.recusa()
        self.assertEqual(ritmo.espera_repeticao(), 5.0)

    def baixar_em_ritmo(self, respostas, chaves, bloqueio=None, paralelo=1):
        estado, clock, sleep = self.relogio()
        ritmo = worker.RitmoCertificado(55, 5, clock=clock, sleep=sleep)
        rotas = [Rota(f"r{i}", f"http://10.0.0.{i}:8080") for i in range(1, 4)]
        chamadas, concluidas = [], []
        fila = list(respostas)

        def baixar(cert, key, ch, transporte, limitador, avisar=None, bloqueio=None):
            chamadas.append((estado["t"], ch, transporte.current().proxy_url))
            xml, erro, ate = fila.pop(0)
            if ate and bloqueio is not None:
                bloqueio.registrar(ate)
            return xml, erro

        with patch.object(worker, "_baixar_na_faixa", side_effect=baixar):
            worker._descarregar_em_ritmo(
                Path("c"), Path("k"), chaves, rotas, ritmo,
                ao_concluir=lambda c, x, e: concluidas.append((c, bool(x), e)), bloqueio=bloqueio,
                paralelo=paralelo,
            )
        return chamadas, concluidas

    def test_um_por_vez_com_intervalo_e_ip_em_rodizio(self):
        chamadas, concluidas = self.baixar_em_ritmo([("<x/>", "", None)] * 3, ["a" * 44, "b" * 44, "c" * 44])
        self.assertEqual([t for t, _c, _p in chamadas], [0.0, 55.0, 110.0])
        self.assertEqual(len({p for _t, _c, p in chamadas}), 3)
        self.assertEqual([ok for _c, ok, _e in concluidas], [True, True, True])

    def test_repete_a_mesma_chave_em_outro_ip(self):
        chamadas, concluidas = self.baixar_em_ritmo(
            [("", "sem_xml", None), ("<x/>", "", None)], ["a" * 44],
        )
        self.assertEqual([c for _t, c, _p in chamadas], ["a" * 44, "a" * 44])
        self.assertNotEqual(chamadas[0][2], chamadas[1][2])
        self.assertEqual(concluidas, [("a" * 44, True, "")])

    def test_bloqueio_com_horario_para_na_hora(self):
        fim = datetime.now(timezone.utc) + timedelta(hours=24)
        chamadas, concluidas = self.baixar_em_ritmo(
            [("", "limite", fim)], ["a" * 44, "b" * 44], bloqueio=worker.Bloqueio(),
        )
        self.assertEqual(len(chamadas), 1)
        self.assertEqual(concluidas, [("a" * 44, False, "limite")])

    def test_nota_indisponivel_nao_repete(self):
        chamadas, concluidas = self.baixar_em_ritmo(
            [("", "indisponivel", None), ("<x/>", "", None)], ["a" * 44, "b" * 44],
        )
        self.assertEqual([c for _t, c, _p in chamadas], ["a" * 44, "b" * 44])
        self.assertEqual([ok for _c, ok, _e in concluidas], [False, True])

    def test_blocos_em_paralelo_por_ip_diferente(self):
        estado, clock, sleep = self.relogio()
        ritmo = worker.RitmoCertificado(55, 5, clock=clock, sleep=sleep)
        rotas = [Rota(f"r{i}", f"http://10.0.0.{i}:8080") for i in range(1, 11)]
        chamadas = []
        trava = __import__("threading").Lock()

        def baixar(cert, key, ch, transporte, limitador, avisar=None, bloqueio=None):
            with trava:
                chamadas.append((estado["t"], ch, transporte.current().proxy_url))
            return "<x/>", ""

        chaves = [f"{n:044d}" for n in range(12)]
        concluidas = []
        with patch.object(worker, "_baixar_na_faixa", side_effect=baixar):
            worker._descarregar_em_ritmo(Path("c"), Path("k"), chaves, rotas, ritmo,
                                         ao_concluir=lambda c, x, e: concluidas.append(c), paralelo=5)
        tempos = sorted({t for t, _c, _p in chamadas})
        # sonda de 1, depois blocos de 5, 5 e 1; após 3 blocos com sucesso de primeira o ritmo cai 5 s
        self.assertEqual(tempos, [0.0, 55.0, 110.0, 160.0])
        self.assertEqual(sorted(concluidas), chaves)
        self.assertEqual(len([1 for t, _c, _p in chamadas if t == 0.0]), 1)
        segundo_bloco = [p for t, _c, p in chamadas if t == 55.0]
        self.assertEqual(len(set(segundo_bloco)), 5)

    def test_recusada_volta_no_bloco_seguinte_por_outro_ip(self):
        estado, clock, sleep = self.relogio()
        ritmo = worker.RitmoCertificado(55, 5, clock=clock, sleep=sleep)
        rotas = [Rota(f"r{i}", f"http://10.0.0.{i}:8080") for i in range(1, 5)]
        vistos = {}

        def baixar(cert, key, ch, transporte, limitador, avisar=None, bloqueio=None):
            vistos.setdefault(ch, []).append(transporte.current().proxy_url)
            if ch == "a" * 44 and len(vistos[ch]) == 1:
                return "", "limite"
            return "<x/>", ""

        concluidas = []
        with patch.object(worker, "_baixar_na_faixa", side_effect=baixar):
            worker._descarregar_em_ritmo(Path("c"), Path("k"), ["a" * 44, "b" * 44], rotas, ritmo,
                                         ao_concluir=lambda c, x, e: concluidas.append((c, bool(x))), paralelo=2)
        self.assertEqual(len(vistos["a" * 44]), 2)
        self.assertNotEqual(vistos["a" * 44][0], vistos["a" * 44][1])
        self.assertEqual(sorted(concluidas), [("a" * 44, True), ("b" * 44, True)])
        self.assertEqual(ritmo.intervalo, 60.0)  # houve recusa: +5 s


if __name__ == "__main__":
    unittest.main()
