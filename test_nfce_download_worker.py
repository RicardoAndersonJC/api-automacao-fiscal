import unittest
from pathlib import Path

from nfce_download_worker import access_key, extract_downloaded_xml, next_aamm, parse_seed_xml, svrs_ca_bundle


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
        bundle = Path(svrs_ca_bundle()).read_text(encoding="ascii")
        pinned = Path(__file__).with_name("icp-brasil-v10.pem").read_text(encoding="ascii")
        self.assertIn(pinned.strip(), bundle)
        self.assertGreaterEqual(bundle.count("BEGIN CERTIFICATE"), 2)


if __name__ == "__main__":
    unittest.main()
