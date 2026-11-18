import os
import unittest
from pathlib import Path
from unittest.mock import patch

import requests

import nfe55_saida_worker as worker
import nfe55_saida_transport as saida_rede
from nfe55_saida_transport import Rota as OutboundRoute


class Transporte:
    def __init__(self, url="http://proxy.example:8080", failover=True):
        self.url = url
        self.failover = failover
        self.limited = 0
        self.failures = 0
        self.success = 0

    def apply(self, session):
        session.proxies.clear()
        session.proxies.update({"http": self.url, "https": self.url})

    def note_infrastructure_failure(self):
        self.failures += 1
        return self.failover

    def note_remote_limit(self):
        self.limited += 1

    def note_success(self):
        self.success += 1


class ProxySaidaTest(unittest.TestCase):
    def test_sessao_usa_proxy_e_mantem_verify(self):
        transporte = Transporte()
        with patch.object(worker, "_transporte", return_value=transporte):
            sessao = worker._abrir_sessao(Path("cert.pem"), Path("key.pem"))
        self.assertEqual(sessao.proxies["https"], "http://proxy.example:8080")
        self.assertNotEqual(sessao.verify, False)
        self.assertTrue(str(sessao.verify).endswith("nexus_nfe55_svrs_ca.pem"))

    def test_limite_nao_troca_proxy(self):
        transporte = Transporte()
        respostas = [
            unittest.mock.Mock(status_code=429, ok=False, text="limite"),
            unittest.mock.Mock(status_code=200, ok=True, text="ok"),
        ]
        sessao = requests.Session()
        sessao.proxies.update({"https": "http://proxy.example:8080"})
        with patch.object(worker, "_transporte", return_value=transporte), patch.object(worker, "_esperar_limite"), patch.object(sessao, "post", side_effect=respostas) as post:
            resposta = worker._enviar(sessao, "post", "https://nfe.svrs.rs.gov.br/ws", data=b"<soap/>")
        self.assertEqual(resposta.status_code, 200)
        self.assertEqual(transporte.limited, 1)
        self.assertEqual(transporte.failures, 0)
        self.assertEqual(sessao.proxies["https"], "http://proxy.example:8080")
        self.assertEqual(post.call_count, 2)
        self.assertNotEqual(post.call_args.kwargs.get("verify"), False)

    def test_falha_de_proxy_troca_saida(self):
        transporte = Transporte(url="http://proxy-2.example:8080")
        sessao = requests.Session()
        sessao.post = unittest.mock.Mock(side_effect=[requests.exceptions.ProxyError("falha"), unittest.mock.Mock(status_code=200, ok=True, text="ok")])
        with patch.object(worker, "_transporte", return_value=transporte), patch.object(worker, "_esperar_limite"):
            worker._enviar(sessao, "post", "https://nfe.svrs.rs.gov.br/ws", data=b"<soap/>")
        self.assertEqual(transporte.failures, 1)
        self.assertEqual(sessao.proxies["https"], "http://proxy-2.example:8080")

    def test_teto_do_lote_e_100(self):
        with patch.dict(os.environ, {"NFE55_PROXY_BATCH_SIZE": "500"}):
            self.assertEqual(worker._tamanho_lote(), 100)
        with patch.dict(os.environ, {"NFE55_PROXY_BATCH_SIZE": "0"}):
            self.assertEqual(worker._tamanho_lote(), 1)

    def test_cursor_continua_depois_da_semente(self):
        cfg = {"AAMM": "2609", "nNF_semente": 109456}
        self.assertEqual(worker._ponto_de_partida(cfg, {"cursor_aamm": "2609", "cursor_nnf": 109456}), ("2609", 109457))
        self.assertEqual(worker._ponto_de_partida(cfg, {"cursor_aamm": "2610", "cursor_nnf": 12}), ("2610", 12))
        self.assertEqual(worker._ponto_de_partida(cfg, {}), ("2609", 109457))

    def test_dispara_so_com_lote_cheio(self):
        self.assertFalse(worker._dispara_lote(99, 100))
        self.assertTrue(worker._dispara_lote(100, 100))
        self.assertFalse(worker._dispara_lote(100, 1))

    def test_webshare_pede_no_maximo_100(self):
        rotas = [OutboundRoute(f"outbound-{i}", f"http://10.0.0.{i}:8080") for i in range(1, 5)]
        with patch.dict(os.environ, {
            "NFE55_PROXY_BATCH_SIZE": "250",
            "NFE55_PROXY_WEBSHARE_API_KEY": "chave-teste",
            "NFE55_PROXY_WEBSHARE_PLAN_ID": "plano",
        }), patch("nfe55_saida_transport.rotas_webshare", return_value=rotas) as lista:
            recebidas = worker._rotas_proxy()
        lista.assert_called_once_with("chave-teste", "plano", 100)
        self.assertEqual(len(recebidas), 4)
        self.assertTrue(worker._lote_ativo(recebidas))

    def test_uma_rota_nao_ativa_o_lote(self):
        rota = [OutboundRoute("outbound-1", "http://10.0.0.1:8080")]
        with patch.dict(os.environ, {"NFE55_PROXY_WEBSHARE_API_KEY": "chave-teste"}), patch(
            "nfe55_saida_transport.rotas_webshare", return_value=rota,
        ):
            recebidas = worker._rotas_proxy()
        self.assertEqual(len(recebidas), 1)
        self.assertFalse(worker._lote_ativo(recebidas))

    def test_lote_de_100_usa_um_proxy_por_chave(self):
        rotas = [OutboundRoute(f"outbound-{i}", f"http://10.1.0.{i}:8080", "user", "secret") for i in range(1, 101)]
        vistos: list[str] = []

        def baixar(cert_path, key_path, chave, transporte=None):
            vistos.append(transporte.current().proxy_url)
            self.assertNotIn("secret", transporte.current().proxy_url or "")
            self.assertTrue(str(cert_path))
            return f"<nfeProc>{chave}</nfeProc>"

        class Limitador:
            def begin_download(self, notify_wait=None, lane="download"):
                self.assert_lane = lane
                return "call", None

            def finish_download_probe(self, probe, *, succeeded):
                return None

            def note_remote_limit(self):
                raise AssertionError("sucesso não pode marcar limite")

        with patch.object(worker, "_baixar", side_effect=baixar), patch.object(worker, "_limitador", return_value=Limitador()):
            saida = worker._descarregar_lote(Path("cert.pem"), Path("key.pem"), [f"{i:044d}" for i in range(100)], rotas)
        self.assertEqual(len(saida), 100)
        self.assertEqual(len(set(vistos)), 100)
        self.assertTrue(all(xml for _chave, xml, erro in saida))
        self.assertTrue(all(erro == "" for _chave, _xml, erro in saida))

    def test_lote_avisa_conforme_cada_xml_volta(self):
        rotas = [OutboundRoute(f"outbound-{i}", f"http://10.2.0.{i}:8080") for i in range(1, 4)]
        avisos: list[str] = []

        def baixar(cert_path, key_path, chave, transporte=None):
            return f"<nfeProc>{chave}</nfeProc>"

        class Limitador:
            def begin_download(self, notify_wait=None, lane="download"):
                return "call", None

            def finish_download_probe(self, probe, *, succeeded):
                return None

        with patch.object(worker, "_baixar", side_effect=baixar), patch.object(worker, "_limitador", return_value=Limitador()):
            worker._descarregar_lote(
                Path("cert.pem"), Path("key.pem"), ["a", "b", "c"], rotas,
                ao_concluir=lambda chave, xml, erro: avisos.append(chave),
            )
        self.assertEqual(sorted(avisos), ["a", "b", "c"])

    def test_limite_na_rota_nao_troca_o_ip(self):
        rota = OutboundRoute("outbound-1", "http://10.9.9.9:8080", "user", "secret")
        gestor = saida_rede.GestorSaida([rota], enabled=True)
        respostas = [
            unittest.mock.Mock(status_code=429, ok=False, text="limite"),
            unittest.mock.Mock(status_code=429, ok=False, text="limite"),
        ]
        for resposta in respostas:
            resposta.raise_for_status.side_effect = requests.HTTPError(response=resposta)
        sessao = requests.Session()
        gestor.apply(sessao)
        proxy_antes = sessao.proxies["https"]

        class Limitador:
            def __init__(self):
                self.limite = 0

            def begin_download(self, notify_wait=None, lane="download"):
                return "call", None

            def finish_download_probe(self, probe, *, succeeded):
                if succeeded:
                    raise AssertionError("429 não é sucesso")

            def note_remote_limit(self):
                self.limite += 1

        limitador = Limitador()
        with patch.object(worker, "_enviar_rota", wraps=worker._enviar_rota), patch.object(worker, "_esperar_limite"), patch.object(sessao, "get", side_effect=respostas), patch.object(worker, "_abrir_sessao_rota", return_value=sessao):
            xml, erro = worker._baixar_na_faixa(Path("cert.pem"), Path("key.pem"), "1" * 44, gestor, limitador)
        self.assertEqual(xml, "")
        self.assertEqual(erro, "limite")
        self.assertEqual(limitador.limite, 1)
        self.assertEqual(sessao.proxies["https"], proxy_antes)
        self.assertIn("10.9.9.9", proxy_antes)


if __name__ == "__main__":
    unittest.main()
