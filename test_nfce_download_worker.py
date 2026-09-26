import unittest

from nfce_download_worker import (
    MAX_PENDING_PER_RUN,
    SvrsRateLimiter,
    access_key,
    apply_discovery_step,
    callback_backoff_seconds,
    clamp_download_interval,
    classify_portal_body,
    discovery_action,
    discovery_scan_complete,
    download_failure_message,
    download_retries_immediately,
    extract_downloaded_xml,
    log_attempt,
    next_aamm,
    parse_seed_xml,
    svrs_ca_bundle,
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
        self.assertTrue(svrs_ca_bundle().endswith("icp-brasil-v10.pem"))

    def test_download_interval_stays_between_90_and_120(self):
        self.assertEqual(clamp_download_interval(15), 90)
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

    def test_pending_batch_is_capped_at_six(self):
        self.assertLessEqual(MAX_PENDING_PER_RUN, 6)

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


if __name__ == "__main__":
    unittest.main()
