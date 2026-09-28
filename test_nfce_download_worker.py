import unittest

import os

import requests

from nfce_download_worker import (
    CANCELLED_QUEUE_ERROR,
    OutboundRoute,
    OutboundTransportManager,
    SvrsRateLimiter,
    TransportCircuitBreaker,
    access_key,
    apply_discovery_step,
    callback_backoff_seconds,
    certificate_mismatch_stops,
    clamp_download_interval,
    client_error_is_permanent,
    classify_portal_body,
    discovery_action,
    discovery_download_plan,
    discovery_scan_complete,
    download_failure_message,
    download_retries_immediately,
    download_retries_same_key,
    extract_downloaded_xml,
    failure_policy,
    handle_discovered_key,
    log_attempt,
    next_aamm,
    parked_note_is_eligible,
    parse_seed_xml,
    reset_shared_rate_limiter,
    sefaz_max_retries,
    shared_rate_limiter,
    should_request_xml,
    svrs_ca_bundle,
    transient_backoff_seconds,
)


SEED = b'''<?xml version="1.0"?><nfeProc xmlns="http://www.portalfiscal.inf.br/nfe"><NFe><infNFe Id="NFe27260808850821000129650010000280491313219441"><ide><cUF>27</cUF><mod>65</mod><serie>1</serie><nNF>28049</nNF><dhEmi>2026-08-01T12:00:00-03:00</dhEmi><tpEmis>1</tpEmis></ide><emit><CNPJ>08850821000129</CNPJ><xNome>TESTE</xNome></emit></infNFe></NFe></nfeProc>'''


class NfceWorkerTest(unittest.TestCase):
    def test_parse_seed(self):
        cfg = parse_seed_xml(SEED)
        self.assertEqual(cfg["cnpj"], "08850821000129")
        self.assertEqual(cfg["aamm"], "2608")
        self.assertEqual(cfg["number"], 28049)

    def test_next_month(self):
        self.assertEqual(next_aamm("2612"), "2701")

    def test_access_key_has_valid_length(self):
        cfg = parse_seed_xml(SEED)
        self.assertEqual(len(access_key(cfg, 28050, "2608")), 44)

    def test_extract_xml(self):
        raw = 'prefix &lt;nfeProc xmlns="http://www.portalfiscal.inf.br/nfe"&gt;&lt;NFe/&gt;&lt;/nfeProc&gt; suffix'
        self.assertIn("<nfeProc", extract_downloaded_xml(raw) or "")

    def test_svrs_ca_bundle_is_pinned(self):
        self.assertTrue(svrs_ca_bundle().endswith("svrs-ca-bundle.pem"))

    def test_download_interval_stays_between_60_and_120(self):
        self.assertEqual(clamp_download_interval(0), 60)
        self.assertEqual(clamp_download_interval(15), 60)
        self.assertEqual(clamp_download_interval(50), 60)
        self.assertEqual(clamp_download_interval(60), 60)
        self.assertEqual(clamp_download_interval(90), 90)
        self.assertEqual(clamp_download_interval(120), 120)
        self.assertEqual(clamp_download_interval(300), 120)

    def test_portal_rate_limit_is_not_a_missing_xml(self):
        page = "<html><body>Muitas consultas. Tente novamente mais tarde.</body></html>"
        self.assertEqual(classify_portal_body(200, page), "rate_limit")
        self.assertEqual(classify_portal_body(429, "ok"), "rate_limit")
        message = download_failure_message("rate_limit")
        self.assertIn("Limite da SVRS", message)
        self.assertNotIn("nenhum XML", message)

    def test_portal_unavailable_is_explicit(self):
        page = "<html>NFC-e cancelada. Documento inexistente.</html>"
        self.assertEqual(classify_portal_body(200, page), "unavailable")
        self.assertIn("cancelada ou indisponível", download_failure_message("unavailable"))

    def test_cstat_100_enqueues_the_consulted_key(self):
        consulted = "1" * 44
        action, key = discovery_action("100", consulted, "")
        self.assertEqual(action, "found")
        self.assertEqual(key, consulted)

    def test_cstat_613_enqueues_the_other_key(self):
        consulted = "1" * 44
        real = "2" * 44
        action, key = discovery_action("613", consulted, real)
        self.assertEqual(action, "found")
        self.assertEqual(key, real)

    def test_cstat_613_without_a_different_key_does_not_advance(self):
        consulted = "1" * 44
        aamm, nnf, action, _key = apply_discovery_step(
            "2608", 10, "2608", 11, "613", consulted, consulted, True,
        )
        self.assertEqual(action, "hold")
        self.assertEqual((aamm, nnf), ("2608", 10))

    def test_failed_ack_does_not_pass_the_number(self):
        aamm, nnf, action, key = apply_discovery_step(
            "2608", 10, "2608", 11, "613", "1" * 44, "2" * 44, False,
        )
        self.assertEqual(action, "found")
        self.assertEqual(key, "2" * 44)
        self.assertEqual((aamm, nnf), ("2608", 10))

    def test_acked_find_advances_only_after_ack(self):
        aamm, nnf, action, _key = apply_discovery_step(
            "2608", 10, "2608", 11, "100", "1" * 44, "", True,
        )
        self.assertEqual((aamm, nnf, action), ("2608", 11, "found"))

    def test_limiter_spaces_download_pairs_by_90s_and_soap_by_100ms(self):
        now = [0.0]

        def clock() -> float:
            return now[0]

        def sleep(seconds: float) -> None:
            now[0] += seconds

        limiter = SvrsRateLimiter(soap_seconds=0.1, download_seconds=90, clock=clock, sleep=sleep)
        self.assertEqual(limiter.wait("download"), 0.0)
        self.assertAlmostEqual(limiter.wait("download"), 90.0)
        self.assertAlmostEqual(limiter.wait("download"), 90.0)
        self.assertEqual(limiter.wait("soap"), 0.0)
        self.assertAlmostEqual(limiter.wait("soap"), 0.1)

    def test_company_stays_open_until_the_gap_closes_the_scan(self):
        self.assertFalse(discovery_scan_complete("cap", 3))
        self.assertTrue(discovery_scan_complete("cap", 0))
        self.assertFalse(discovery_scan_complete("hold", 0))
        self.assertFalse(discovery_scan_complete("ack", 0))
        self.assertTrue(discovery_scan_complete("gap", 0))
        self.assertTrue(discovery_scan_complete("gap", 4))

    def test_timeout_retries_three_times_and_rate_limit_does_not(self):
        self.assertTrue(download_retries_immediately("timeout", 0))
        self.assertTrue(download_retries_immediately("timeout", 1))
        self.assertFalse(download_retries_immediately("timeout", 2))
        self.assertFalse(download_retries_immediately("rate_limit", 0))
        self.assertFalse(download_retries_immediately("unavailable", 0))

    def test_empty_page_retries_the_same_key_after_60s(self):
        self.assertTrue(download_retries_same_key("no_xml", 0))
        self.assertFalse(download_retries_same_key("rate_limit", 1))
        self.assertFalse(download_retries_same_key("no_xml", 2))
        self.assertFalse(download_retries_same_key("unavailable", 0))
        now = [0.0]

        def clock() -> float:
            return now[0]

        def sleep(seconds: float) -> None:
            now[0] += seconds

        limiter = SvrsRateLimiter(download_seconds=90, clock=clock, sleep=sleep)
        self.assertEqual(limiter.wait("download"), 0.0)
        limiter.arm_same_key_retry(60)
        self.assertAlmostEqual(limiter.wait("download"), 60.0)

    def test_shared_limiter_keeps_one_clock(self):
        reset_shared_rate_limiter()
        first = shared_rate_limiter(0.1, 90)
        second = shared_rate_limiter(0.1, 90)
        self.assertIs(first, second)
        reset_shared_rate_limiter()

    def test_callback_backoff_is_half_then_one_then_two(self):
        self.assertEqual(callback_backoff_seconds(0), 0.5)
        self.assertEqual(callback_backoff_seconds(1), 1.0)
        self.assertEqual(callback_backoff_seconds(2), 2.0)

    def test_attempt_log_drops_secrets(self):
        record = log_attempt(
            run_id="run-1",
            empresa_id="empresa-1",
            aamm="2608",
            nnf=11,
            chave="eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9.payload.sig",
            etapa="download",
            tentativa=1,
            duracao_ms=12,
            http=200,
            categoria="ok",
            retry=False,
        )
        self.assertEqual(record["chave"], "")
        self.assertNotIn("senha", record)
        self.assertNotIn("token", record)
        self.assertEqual(record["etapa"], "download")

    def test_soap_found_and_missing_plan(self):
        self.assertEqual(discovery_action("217", "1" * 44, "")[0], "absent")
        self.assertEqual(
            discovery_download_plan(found=False, xml_already_saved=False),
            "continue",
        )

    def test_found_without_xml_downloads_in_the_same_run(self):
        calls = []

        def download():
            calls.append("xml")
            return "ok"

        outcome = handle_discovered_key(
            xml_already_saved=False,
            download=download,
        )
        self.assertEqual(outcome, "download")
        self.assertEqual(calls, ["xml"])
        self.assertTrue(should_request_xml(xml_already_saved=False))

    def test_seventh_key_downloads_in_the_same_run(self):
        calls = []

        def download():
            calls.append("xml")
            return "ok"

        outcome = handle_discovered_key(
            xml_already_saved=False,
            download=download,
        )
        self.assertEqual(outcome, "download")
        self.assertEqual(calls, ["xml"])
        self.assertEqual(
            discovery_download_plan(found=True, xml_already_saved=False),
            "download",
        )

    def test_saved_xml_is_not_downloaded_again(self):
        def download():
            raise AssertionError("xml já salvo")

        outcome = handle_discovered_key(
            xml_already_saved=True,
            download=download,
        )
        self.assertEqual(outcome, "skip_saved")
        self.assertFalse(should_request_xml(xml_already_saved=True))

    def test_cancelled_park_without_xml_is_eligible(self):
        self.assertTrue(parked_note_is_eligible(ultimo_erro=CANCELLED_QUEUE_ERROR, xml_exists=False))
        self.assertFalse(parked_note_is_eligible(ultimo_erro=CANCELLED_QUEUE_ERROR, xml_exists=True))
        self.assertFalse(
            parked_note_is_eligible(
                ultimo_erro="[fora-da-fila] NFC-e sem XML no portal da SVRS após 3 tentativas.",
                xml_exists=False,
            )
        )

    def test_transient_backoff_grows_with_jitter_and_cap(self):
        self.assertEqual(transient_backoff_seconds(0, 0), 1)
        self.assertEqual(transient_backoff_seconds(1, 0), 2)
        self.assertEqual(transient_backoff_seconds(2, 0), 4)
        self.assertEqual(transient_backoff_seconds(0, 0.25), 1.25)
        self.assertLessEqual(transient_backoff_seconds(8, 5), 30)
        os.environ["SEFAZ_MAX_RETRIES"] = "99"
        try:
            self.assertEqual(sefaz_max_retries(), 3)
        finally:
            del os.environ["SEFAZ_MAX_RETRIES"]
        self.assertFalse(download_retries_immediately("timeout", 2))
        self.assertEqual(failure_policy("timeout"), "backoff")
        self.assertEqual(failure_policy("http"), "backoff")
        self.assertEqual(failure_policy("rate_limit"), "cooldown")

    def test_503_without_block_text_is_transient_and_429_cools_down(self):
        self.assertEqual(classify_portal_body(503, "upstream"), "http")
        self.assertEqual(classify_portal_body(500, "erro"), "http")
        self.assertEqual(classify_portal_body(429, ""), "rate_limit")
        self.assertEqual(classify_portal_body(200, "<html>bloqueio temporario</html>"), "rate_limit")

    def test_cooldown_blocks_then_half_open_probe_recovers_or_cools_again(self):
        now = [0.0]

        def clock() -> float:
            return now[0]

        def sleep(seconds: float) -> None:
            now[0] += seconds

        limiter = SvrsRateLimiter(download_seconds=60, cooldown_seconds=60, clock=clock, sleep=sleep)
        limiter.note_remote_limit()
        self.assertEqual(limiter.download_state(), "cooldown")
        self.assertFalse(limiter.download_admission())
        self.assertEqual(limiter.begin_download(), "call")
        self.assertGreaterEqual(now[0], 60)
        self.assertEqual(limiter.download_state(), "half_open")
        self.assertEqual(limiter.begin_download(), "skip")
        limiter.note_download_ok()
        self.assertEqual(limiter.download_state(), "available")
        recovered_at = now[0]
        self.assertEqual(limiter.begin_download(), "call")
        self.assertGreaterEqual(now[0] - recovered_at, 60)
        limiter.note_remote_limit()
        now[0] += 60
        self.assertEqual(limiter.download_state(), "half_open")
        limiter.note_remote_limit()
        self.assertEqual(limiter.download_state(), "cooldown")
        self.assertFalse(limiter.download_admission())

    def test_circuit_opens_probes_and_closes(self):
        now = [0.0]
        breaker = TransportCircuitBreaker(threshold=3, cooldown_seconds=60, clock=lambda: now[0])
        self.assertTrue(breaker.allow_call())
        self.assertEqual(breaker.state, "closed")
        breaker.note_transport_failure()
        breaker.note_transport_failure()
        self.assertEqual(breaker.state, "closed")
        breaker.note_transport_failure()
        self.assertEqual(breaker.state, "open")
        self.assertFalse(breaker.allow_call())
        now[0] += 60
        self.assertTrue(breaker.allow_call())
        self.assertEqual(breaker.state, "half_open")
        self.assertFalse(breaker.allow_call())
        breaker.note_transport_failure()
        self.assertEqual(breaker.state, "open")
        now[0] += 60
        self.assertTrue(breaker.allow_call())
        breaker.note_success()
        self.assertEqual(breaker.state, "closed")
        self.assertTrue(breaker.allow_call())

    def test_certificate_and_cnpj_do_not_retry(self):
        self.assertTrue(client_error_is_permanent("certificate"))
        self.assertTrue(client_error_is_permanent("cnpj"))
        self.assertTrue(certificate_mismatch_stops("111", "222"))
        self.assertFalse(certificate_mismatch_stops("111", "111"))
        self.assertFalse(download_retries_immediately("certificate", 0))
        self.assertEqual(failure_policy("cnpj"), "permanent")

    def test_proxy_disabled_keeps_direct_connection(self):
        manager = OutboundTransportManager.from_env({"PROXY_ENABLED": "false", "PROXY_URL": "http://proxy.example:8080"})
        self.assertFalse(manager.enabled)
        self.assertIsNone(manager.requests_proxies())
        session = requests.Session()
        session.verify = "icp-brasil-v10.pem"
        manager.apply(session)
        self.assertEqual(session.verify, "icp-brasil-v10.pem")
        self.assertFalse(session.verify is False)
        self.assertEqual(session.proxies, {})
        self.assertEqual(
            manager.public_status(),
            {
                "enabled": False,
                "routes": 0,
                "outbound_id": "direct",
                "outbound_health": "healthy",
            },
        )

    def test_proxy_enabled_is_used_and_verify_stays(self):
        manager = OutboundTransportManager.from_env(
            {
                "PROXY_ENABLED": "true",
                "PROXY_URL": "http://proxy.example:8080",
                "PROXY_USERNAME": "user",
                "PROXY_PASSWORD": "secret-pass",
            }
        )
        self.assertTrue(manager.enabled)
        proxies = manager.requests_proxies()
        self.assertIsNotNone(proxies)
        self.assertIn("proxy.example:8080", proxies["https"])
        session = requests.Session()
        session.verify = "icp-brasil-v10.pem"
        manager.apply(session)
        self.assertEqual(session.verify, "icp-brasil-v10.pem")
        self.assertNotEqual(session.verify, False)
        status = manager.public_status()
        self.assertTrue(status["enabled"])
        self.assertEqual(status["routes"], 1)
        self.assertEqual(status["outbound_id"], "outbound-1")
        self.assertNotIn("proxy_url", status)

    def test_proxy_infrastructure_failover_does_not_follow_remote_limit(self):
        manager = OutboundTransportManager(
            [
                OutboundRoute("outbound-1", "http://a.example:8080"),
                OutboundRoute("outbound-2", "http://b.example:8080"),
            ],
            enabled=True,
            cooldown_seconds=60,
        )
        self.assertEqual(manager.current().outbound_id, "outbound-1")
        self.assertTrue(manager.note_infrastructure_failure())
        self.assertEqual(manager.current().outbound_id, "outbound-2")
        self.assertEqual(manager.routes[0].health, "unhealthy")
        stuck = manager.current().outbound_id
        manager.note_remote_limit()
        self.assertEqual(manager.current().outbound_id, stuck)

    def test_log_drops_proxy_credentials(self):
        record = log_attempt(
            run_id="run-1",
            empresa_id="empresa-1",
            aamm="2608",
            nnf=12,
            chave="3" * 44,
            etapa="download",
            tentativa=1,
            duracao_ms=10,
            http=429,
            categoria="rate_limit",
            resultado="http://user:secret-pass@proxy.example:8080",
            proxy_enabled=True,
            outbound_id="outbound-1",
            outbound_health="healthy",
            cooldown="cooldown",
            circuit_state="closed",
        )
        self.assertNotIn("secret-pass", str(record))
        self.assertEqual(record["resultado"], "[redacted-url]")
        self.assertEqual(record["outbound_id"], "outbound-1")
        self.assertNotIn("proxy_password", record)


if __name__ == "__main__":
    unittest.main()
