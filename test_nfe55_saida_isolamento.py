"""A NF-e de saída não compartilha estado nem configuração com a NFC-e."""

import ast
import os
import unittest
from pathlib import Path
from unittest.mock import patch

import nfe55_saida_transport as saida_rede

AQUI = Path(__file__).parent


class RelogioFalso:
    def __init__(self):
        self.agora = 0.0

    def __call__(self):
        return self.agora

    def dormir(self, segundos):
        self.agora += segundos


class IsolamentoTest(unittest.TestCase):
    def setUp(self):
        saida_rede.reiniciar_estado()

    def tearDown(self):
        saida_rede.reiniciar_estado()

    def test_codigo_da_saida_nao_importa_nfce(self):
        for nome in ("nfe55_saida_worker.py", "nfe55_saida_transport.py", "nfe55_saida_discovery.py"):
            arvore = ast.parse((AQUI / nome).read_text(encoding="utf-8"))
            modulos = set()
            for no in ast.walk(arvore):
                if isinstance(no, ast.Import):
                    modulos.update(alias.name for alias in no.names)
                elif isinstance(no, ast.ImportFrom) and no.module:
                    modulos.add(no.module)
            self.assertFalse([m for m in modulos if "nfce" in m.lower()], nome)

    def test_sem_nfe55_reaproveita_proxies_da_nfce(self):
        env = {
            "NFCE_PROXY_PILOT_URL": "http://nfce.example:8080",
            "NFCE_PROXY_PILOT_USERNAME": "u",
            "NFCE_PROXY_PILOT_PASSWORD": "p",
            "NFCE_PROXY_BATCH_SIZE": "7",
            "PROXY_ENABLED": "true",
            "PROXY_URL": "http://nfce-principal.example:8080",
        }
        with patch.dict(os.environ, env, clear=True):
            rotas = saida_rede.rotas_configuradas()
            self.assertEqual([r.proxy_url for r in rotas], ["http://nfce.example:8080"])
            self.assertEqual(rotas[0].username, "u")
            self.assertTrue(saida_rede.proxy_configurado())
            self.assertEqual(saida_rede.tamanho_lote(), 7)

    def test_sem_proxy_algum_usa_conexao_direta(self):
        with patch.dict(os.environ, {"PROXY_ENABLED": "true", "PROXY_URL": "http://x.example:1"}, clear=True):
            self.assertEqual(saida_rede.rotas_configuradas(), [])
            self.assertFalse(saida_rede.proxy_configurado())
            self.assertFalse(saida_rede.transporte_compartilhado().enabled)

    def test_nfe55_tem_prioridade_sobre_nfce(self):
        env = {
            "NFE55_PROXY_URL": "http://saida.example:8080",
            "NFCE_PROXY_PILOT_URL": "http://nfce.example:8080",
            "NFCE_PROXY_PILOT_WEBSHARE_API_KEY": "chave-nfce",
        }
        with patch.dict(os.environ, env, clear=True):
            self.assertEqual([r.proxy_url for r in saida_rede.rotas_configuradas()], ["http://saida.example:8080"])

    def test_saida_usa_variaveis_proprias(self):
        env = {
            "NFE55_PROXY_URL": "http://saida-1.example:8080",
            "NFE55_PROXY_URL_2": "http://saida-2.example:8080",
            "NFE55_PROXY_USERNAME": "u",
            "NFE55_PROXY_PASSWORD": "p",
        }
        with patch.dict(os.environ, env, clear=True):
            rotas = saida_rede.rotas_configuradas()
        self.assertEqual([r.proxy_url for r in rotas], ["http://saida-1.example:8080", "http://saida-2.example:8080"])
        self.assertEqual(rotas[1].username, "u")

    def test_limite_da_saida_nao_toca_limitador_da_nfce(self):
        try:
            import nfce_download_worker as nfce
        except Exception as exc:  # dependências da NFC-e ausentes no ambiente de teste
            self.skipTest(f"nfce_download_worker indisponível: {exc}")
        limitador_nfce = nfce.SvrsRateLimiter(0.1, 60, cooldown_seconds=60)
        with patch.object(nfce, "shared_rate_limiter", return_value=limitador_nfce):
            saida_rede.limitador_compartilhado().note_remote_limit()
        self.assertEqual(saida_rede.limitador_compartilhado().estado(), "cooldown")
        self.assertEqual(limitador_nfce.download_state(), "available")

    def test_cooldown_libera_uma_sonda(self):
        relogio = RelogioFalso()
        limitador = saida_rede.LimitadorSaida(60, cooldown=60, clock=relogio, sleep=relogio.dormir)
        limitador.note_remote_limit()
        status, sonda = limitador.begin_download(lane="a")
        self.assertEqual(status, "call")
        self.assertIsNotNone(sonda)
        self.assertEqual(limitador.begin_download(lane="b"), ("skip", None))
        limitador.finish_download_probe(sonda, succeeded=True)
        self.assertEqual(limitador.estado(), "available")
        self.assertEqual(limitador.begin_download(lane="b")[0], "call")

    def test_mesma_faixa_espera_intervalo(self):
        relogio = RelogioFalso()
        limitador = saida_rede.LimitadorSaida(60, cooldown=60, clock=relogio, sleep=relogio.dormir)
        self.assertEqual(limitador.begin_download(lane="ip-1"), ("call", None))
        self.assertEqual(limitador.begin_download(lane="ip-2"), ("call", None))
        self.assertEqual(relogio.agora, 0.0)
        self.assertEqual(limitador.begin_download(lane="ip-1"), ("call", None))
        self.assertEqual(relogio.agora, 60.0)

    def test_cooldown_proprio_com_fallback(self):
        with patch.dict(os.environ, {}, clear=True):
            self.assertEqual(saida_rede.cooldown_segundos(), 60.0)
        with patch.dict(os.environ, {"SEFAZ_COOLDOWN_SECONDS": "5"}, clear=True):
            self.assertEqual(saida_rede.cooldown_segundos(), 5.0)
        with patch.dict(os.environ, {"NFE55_COOLDOWN_SECONDS": "90", "SEFAZ_COOLDOWN_SECONDS": "5"}, clear=True):
            self.assertEqual(saida_rede.cooldown_segundos(), 90.0)


if __name__ == "__main__":
    unittest.main()
