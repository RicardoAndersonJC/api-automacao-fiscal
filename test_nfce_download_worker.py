import unittest

import os

import requests
from unittest.mock import patch
import nfce_download_worker as worker
import threading


class RemoteResponseLoggingTests(unittest.TestCase):
    def test_two_jobs_can_run_without_waiting_for_first_to_finish(self):
        started = threading.Barrier(2)
        def task():
            started.wait(timeout=2)
            return True
        if worker.NFCE_WORKERS < 2:
            self.skipTest("NFCE_WORKERS explicitamente configurado como 1")
        first = worker._executor.submit(task)
        second = worker._executor.submit(task)
        self.assertTrue(first.result(timeout=3))
        self.assertTrue(second.result(timeout=3))

    def test_waiting_job_rechecks_cooldown_and_only_one_probe_is_allowed(self):
        now = [0.0]
        calls = [0]
        def sleep(seconds):
            now[0] += seconds
            calls[0] += 1
            if calls[0] == 1:
                limiter.note_remote_limit()
        limiter = worker.SvrsRateLimiter(download_seconds=90, cooldown_seconds=60,
                                        clock=lambda: now[0], sleep=sleep)
        self.assertEqual(limiter.begin_download(), "call")
        self.assertEqual(limiter.begin_download(), "call")
        self.assertEqual(now[0], 150)
        self.assertEqual(limiter.begin_download(), "skip")

    def test_retry_cannot_shorten_shared_download_interval(self):
        now = [0.0]
        limiter = worker.SvrsRateLimiter(download_seconds=90, clock=lambda: now[0],
                                        sleep=lambda seconds: now.__setitem__(0, now[0] + seconds))
        limiter.begin_download()
        limiter.arm_same_key_retry(1)
        limiter.begin_download()
        self.assertEqual(now[0], 90)

    def test_xml_entities_are_preserved_in_raw_and_html_encoded_xml(self):
        xml = '<nfeProc><NFe><xNome>LYRA &amp; PAES</xNome><xProd>A &lt; B</xProd></NFe></nfeProc>'
        self.assertEqual(worker.extract_downloaded_xml(xml), xml)
        encoded = worker.html.escape(xml)
        self.assertEqual(worker.extract_downloaded_xml('<pre>' + encoded + '</pre>'), xml)
        self.assertEqual(worker.extract_downloaded_xml(worker.html.escape(encoded)), xml)

    def test_captcha_response_logs_evidence_without_form_secrets(self):
        response = requests.Response()
        response.status_code = 200
        response.url = "https://dfe-portal.svrs.rs.gov.br/NFCESSL/DownloadXMLDFe?token=secret"
        response._content = b'<html>recaptcha<input name="token" value="private-value"></html>'
        response.headers["Content-Type"] = "text/html"
        with patch.object(worker._logger, "info") as output:
            worker._log_remote_response(response, "portal_get", worker.time.perf_counter(),
                                        {"tentativa": 1, "empresa_id": "company"})
        logged = output.call_args.args[0]
        self.assertIn('"categoria": "no_xml"', logged)
        self.assertIn('captcha_present', logged)
        self.assertIn('"status_http": 200', logged)
        self.assertNotIn("private-value", logged)
        self.assertNotIn("token=secret", logged)

    def test_captcha_script_is_not_evidence_of_rate_limit(self):
        self.assertEqual(worker.classify_portal_body(
            200, '<script src="https://www.google.com/recaptcha/api.js"></script>'), "no_xml")
        self.assertEqual(worker.classify_portal_body(429, ""), "rate_limit")

    def test_get_captcha_does_not_override_post_result(self):
        get_response = requests.Response()
        get_response.status_code = 200
        get_response.url = worker.SVRS_DOWNLOAD_GET_URL
        get_response._content = b'<script src="recaptcha/api.js"></script>'
        post_response = requests.Response()
        post_response.status_code = 200
        post_response.url = worker.SVRS_DOWNLOAD_POST_URL
        post_response._content = b'<html><title>Erro no processamento do Portal</title></html>'
        with patch.object(worker._logger, "info"), patch.object(requests.Session, "get", return_value=get_response), \
                patch.object(requests.Session, "post", return_value=post_response):
            _, kind, _, _ = worker._download(requests.Session(), "1" * 44)
        self.assertEqual(kind, "no_xml")

    def test_soap_logs_status_and_reason(self):
        response = requests.Response()
        response.status_code = 200
        response.url = worker.SVRS_CONSULTA_URL
        response._content = b'<retConsSitNFe><cStat>217</cStat><xMotivo>NF-e nao consta</xMotivo></retConsSitNFe>'
        with patch.object(worker._logger, "info") as output:
            worker._log_remote_response(response, "consulta_soap", worker.time.perf_counter(),
                                        {"tentativa": 1})
        logged = output.call_args.args[0]
        self.assertIn('"cstat": "217"', logged)
        self.assertIn("NF-e nao consta", logged)

from nfce_download_worker import (
    CANCELLED_QUEUE_ERROR,
    MAX_PENDING_PER_RUN,
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
    def test_portal_access_denied_is_not_a_missing_invoice(self):
        from nfce_download_worker import _portal_http_failure
        import requests
        for status in (401, 403):
            self.assertEqual(classify_portal_body(status, ""), "access_denied")
        self.assertEqual(classify_portal_body(200, '<a href="/Erro/Forbidden">erro</a>'), "access_denied")
        response = requests.Response()
        response.status_code = 200
        response.url = "https://dfe-portal.svrs.rs.gov.br/Erro/Forbidden"
        response._content = b"<html>Erro no processamento do Portal</html>"
        kind, message = _portal_http_failure(response)
        self.assertEqual(kind, "access_denied")
        self.assertIn("preservada", message)
        self.assertEqual(failure_policy(kind), "backoff")
        self.assertFalse(download_retries_same_key(kind, 0))

    def test_parse_seed(self):
        cfg = parse_seed_xml(SEED)
        self.assertEqual(cfg["cnpj"], "08850821000129")
        self.assertEqual(cfg["aamm"], "2608")
        self.assertEqual(cfg["number"], 28049)

    def test_next_month(self):
        self.assertEqual(parse_seed_xml(SEED.replace(b"2026-08-01", b"2026-09-01"))["aamm"], "2609")
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

    def test_pending_batch_is_unlimited(self):
        self.assertEqual(MAX_PENDING_PER_RUN, 0)

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
        self.assertFalse(discovery_scan_complete("cap", 0))
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

    def test_empty_page_retry_preserves_the_global_interval(self):
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
        self.assertAlmostEqual(limiter.wait("download"), 90.0)

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

    def test_matrix_certificate_preserves_branch_emitter(self):
        self.assertFalse(certificate_mismatch_stops("12345678000100", "12345678000200"))
        self.assertFalse(certificate_mismatch_stops("12345678000200", "12345678000100"))
        self.assertTrue(certificate_mismatch_stops("99345678000100", "12345678000200"))
        self.assertTrue(certificate_mismatch_stops("12345678", "12345678000200"))

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


class MissingNotesRecoveryTests(unittest.TestCase):
    def run_worker(self, responses, options=None, callback_effect=None, downloads=None):
        import tempfile
        from pathlib import Path
        from contextlib import ExitStack
        from unittest.mock import Mock
        with tempfile.TemporaryDirectory() as directory, ExitStack() as stack:
            job = worker.Job(id="test", owner_id="test", directory=Path(directory))
            defaults = dict(start_aamm="2608", start_number=15103, max_numbers=7,
                            month_trigger=8, month_window=30, stop_gap=80)
            defaults.update(options or {})
            for name, value in [("_certificate_files", (None, None, "08850821000129")),
                                ("svrs_ca_bundle", "ca"), ("_new_svrs_session", Mock()),
                                ("shared_rate_limiter", Mock()), ("current_aamm", "2610"),
                                ("_download_one", ({}, "<nfeProc><NFe /></nfeProc>", "", "ok"))]:
                stack.enter_context(patch.object(worker, name, return_value=value))
            if downloads is not None:
                stack.enter_context(patch.object(worker, "_download_one", side_effect=downloads))
            consult = stack.enter_context(patch.object(worker, "_consult_logged", side_effect=responses))
            callback = stack.enter_context(patch.object(worker, "_callback", side_effect=callback_effect))
            worker.run_job(job, SEED, b"pfx", "", defaults)
            return job, callback.call_args_list, consult.call_args_list

    def test_six_saved_then_timeout_keeps_cursor_and_requests_resume(self):
        responses = [("100", "Autorizada", str(index) * 44) for index in range(1, 7)] + [("", "timeout", "")]
        job, callbacks, _ = self.run_worker(responses)
        self.assertEqual(job.status, "completed")
        self.assertEqual(len([call for call in callbacks if call.args[1] == "file"]), 6)
        completed = [call.kwargs for call in callbacks if call.args[1] == "completed"][-1]
        self.assertEqual(completed["cursor_nnf"], 15109)
        self.assertTrue(completed["pause_for_svrs"])
        self.assertIn("Pausa temporária na SVRS", completed["message"])
        self.assertNotIn("limite", completed["message"])
        self.assertFalse(completed["scan_complete"])

    def test_absence_must_be_acknowledged_before_cursor_moves(self):
        def fail_absent(job, event, **payload):
            if event == "absent":
                raise RuntimeError("callback indisponível")
        job, callbacks, _ = self.run_worker([("217", "Ausente", "")], callback_effect=fail_absent)
        completed = [call.kwargs for call in callbacks if call.args[1] == "completed"][-1]
        self.assertEqual(completed["cursor_nnf"], 15103)
        self.assertTrue(completed["pause_for_svrs"])

    def test_missing_recovery_uses_real_key_without_moving_pending_only_cursor(self):
        real = "9" * 44
        job, callbacks, consults = self.run_worker([("613", "Chave divergente", real)],
            dict(pending_only=True, missing_notes=[dict(id="missing", aamm="2608", nnf=25747)]))
        self.assertEqual(job.status, "completed", job.error)
        self.assertEqual(consults[0].args[2:4], (25747, "2608"))
        discovered = [call for call in callbacks if call.args[1] == "discovered"]
        self.assertEqual(discovered[0].kwargs["key"], real)
        completed = [call.kwargs for call in callbacks if call.args[1] == "completed"][-1]
        self.assertFalse(completed["include_cursor"])
        self.assertEqual(completed["cursor_nnf"], 15103)

    def test_absent_missing_note_is_retained_as_retry_without_download(self):
        job, callbacks, _ = self.run_worker([("217", "Ausente", "")] * 2,
            dict(pending_only=True, missing_notes=[dict(aamm="2608", nnf=25747)]))
        self.assertEqual(len([call for call in callbacks if call.args[1] == "missing_attempt"]), 1)
        self.assertFalse(any(call.args[1] in {"file", "discovered"} for call in callbacks))

    def test_missing_payload_is_validated_and_capped(self):
        import json
        self.assertEqual(len(worker.normalize_missing_notes(json.dumps([dict(aamm="2608", nnf=1)] * 2))), 1)
        for payload in ["{}", '[{"aamm":"2613","nnf":1}]', '[{"aamm":"2608","nnf":true}]', json.dumps([dict(aamm="2608", nnf=1)] * 21)]:
            with self.assertRaises(ValueError):
                worker.normalize_missing_notes(payload)

    def test_soap_timeout_returns_hold_instead_of_losing_completed_work(self):
        from unittest.mock import Mock
        cfg = worker.parse_seed_xml(SEED)
        with patch.object(worker, "_consult", side_effect=requests.ReadTimeout("read timeout=45")):
            self.assertEqual(worker._consult_logged(Mock(), cfg, 15110, "2608", "test", "test"), ("", "timeout", ""))

    def test_gap_crossing_month_recovers_in_upper_competence(self):
        job, callbacks, consults = self.run_worker([("217", "Ausente", ""), ("217", "Ausente", ""), ("613", "Real", "9" * 44)],
            dict(pending_only=True, missing_notes=[dict(aamm="2608", aamm_final="2609", nnf=25747)]))
        self.assertEqual([call.args[3] for call in consults], ["2608", "2608", "2609"])
        discovered = [call for call in callbacks if call.args[1] == "discovered"][0]
        self.assertEqual(discovered.kwargs["aamm"], "2609")

    def test_month_probe_absence_is_acknowledged_before_switching(self):
        responses = [("217", "Ausente", ""), ("217", "Ausente", ""),
                     ("217", "Ausente", ""), ("613", "Real", "9" * 44)]
        job, callbacks, _ = self.run_worker(responses, dict(month_trigger=2, month_window=2, max_numbers=4))
        absent = [call.kwargs for call in callbacks if call.args[1] == "absent"]
        self.assertIn(dict(aamm="2609", number=15104), absent)
        completed = [call.kwargs for call in callbacks if call.args[1] == "completed"][-1]
        self.assertEqual((completed["cursor_aamm"], completed["cursor_nnf"]), ("2609", 15105))

    def test_old_gap_rotates_twelve_month_windows_between_attempts(self):
        for attempts, expected_start, expected_end, count in [(0, "2501", "2512", 12), (1, "2601", "2602", 2), (2, "2501", "2512", 12)]:
            with self.subTest(attempts=attempts):
                job, callbacks, consults = self.run_worker([("217", "Ausente", "")] * (count * 2),
                    dict(pending_only=True, missing_notes=[dict(aamm="2501", aamm_final="2602", nnf=25747, tentativas=attempts)]))
                self.assertEqual(job.status, "completed", job.error)
                self.assertEqual(len(consults), count * 2)
                self.assertEqual(consults[0].args[3], expected_start)
                self.assertEqual(consults[-1].args[3], expected_end)
                self.assertEqual(len([call for call in callbacks if call.args[1] == "missing_attempt"]), 1)

    def test_missing_summary_separates_absent_keys_and_failed_xml(self):
        notes = [dict(aamm="2608", nnf=n) for n in (25747, 25748, 25749)]
        responses = [("613", "Real", "8" * 44), ("613", "Real", "9" * 44), ("217", "Ausente", ""), ("217", "Ausente", "")]
        downloads = [({}, "<nfeProc><NFe /></nfeProc>", "", "ok"), ({}, None, "XML ainda indisponível", "no_xml")]
        job, callbacks, consults = self.run_worker(responses,
            dict(pending_only=True, missing_notes=notes), downloads=downloads)
        self.assertEqual(job.status, "completed", job.error)
        self.assertEqual((job.missing_attempted, job.missing_recovered, job.missing_not_located), (3, 1, 1))
        self.assertIn("3 numerações verificadas · 1 XML recuperados · 1 não localizadas nesta tentativa", job.message)
        self.assertIn("1 ainda aguardando XML ou consulta", job.message)
        completed = [call.kwargs for call in callbacks if call.args[1] == "completed"][-1]
        self.assertEqual(completed["missing_attempted"], 3)
        self.assertEqual(completed["consulted"], 0)
        self.assertFalse(completed["include_cursor"])
        self.assertEqual(completed["cursor_nnf"], 15103)

    def test_four_missing_absences_are_explicit_without_affecting_scan_counters(self):
        notes = [dict(aamm="2608", nnf=n) for n in (60597, 60634, 60922, 61143)]
        job, callbacks, _ = self.run_worker([("217", "Ausente", "")] * 9,
            dict(missing_notes=notes, max_numbers=1))
        self.assertEqual(job.status, "completed", job.error)
        self.assertIn("4 numerações verificadas · 0 XML recuperados · 4 não localizadas nesta tentativa", job.message)
        self.assertEqual(job.public()["missing_attempted"], 4)
        completed = [call.kwargs for call in callbacks if call.args[1] == "completed"][-1]
        self.assertEqual(completed["consulted"], 1)
        self.assertEqual(completed["cursor_nnf"], 15104)

    def test_contingency_fallback_100_queues_the_confirmed_alternate_key(self):
        job, callbacks, consults = self.run_worker([("217", "Ausente", ""), ("100", "Autorizada", "")],
            dict(pending_only=True, missing_notes=[dict(aamm="2608", nnf=60597)]))
        self.assertEqual(job.status, "completed", job.error)
        self.assertEqual([call.args[1]["emission_type"] for call in consults], ["1", "9"])
        expected = worker.access_key({**worker.parse_seed_xml(SEED), "emission_type": "9"}, 60597, "2608")
        discovered = [call for call in callbacks if call.args[1] == "discovered"][0]
        self.assertEqual(discovered.kwargs["key"], expected)
        self.assertEqual(job.missing_recovered, 1)
        completed = [call.kwargs for call in callbacks if call.args[1] == "completed"][-1]
        self.assertFalse(completed["include_cursor"])
        self.assertEqual(completed["cursor_nnf"], 15103)

    def test_contingency_fallback_613_queues_real_response_key(self):
        real = "7" * 44
        job, callbacks, consults = self.run_worker([("217", "Ausente", ""), ("613", "Real", real)],
            dict(pending_only=True, missing_notes=[dict(aamm="2608", nnf=60597)]))
        self.assertEqual([call for call in callbacks if call.args[1] == "discovered"][0].kwargs["key"], real)
        self.assertEqual(len(consults), 2)

    def test_inconclusive_consultation_does_not_trigger_emission_fallback(self):
        job, callbacks, consults = self.run_worker([("", "timeout", "")],
            dict(pending_only=True, missing_notes=[dict(aamm="2608", nnf=60597)]))
        self.assertEqual(len(consults), 1)
        self.assertEqual(job.missing_not_located, 0)
        self.assertEqual(len([call for call in callbacks if call.args[1] == "missing_attempt"]), 1)

    def test_both_emission_types_absent_count_one_missing_attempt(self):
        job, callbacks, consults = self.run_worker([("217", "Ausente", "")] * 2,
            dict(pending_only=True, missing_notes=[dict(aamm="2608", nnf=60597)]))
        self.assertEqual(len(consults), 2)
        self.assertEqual(job.missing_attempted, 1)
        self.assertEqual(job.missing_not_located, 1)
        self.assertEqual(len([call for call in callbacks if call.args[1] == "missing_attempt"]), 1)

    def test_contingency_seed_falls_back_to_normal_emission(self):
        with patch.dict(globals(), SEED=SEED.replace(b"<tpEmis>1</tpEmis>", b"<tpEmis>9</tpEmis>")):
            job, callbacks, consults = self.run_worker([("217", "Ausente", ""), ("100", "Autorizada", "")],
                dict(pending_only=True, missing_notes=[dict(aamm="2608", nnf=60597)]))
        self.assertEqual([call.args[1]["emission_type"] for call in consults], ["9", "1"])
        self.assertEqual([call for call in callbacks if call.args[1] == "discovered"][0].kwargs["key"][34], "1")
