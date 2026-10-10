import tempfile
import unittest
from datetime import datetime, timedelta, timezone
from pathlib import Path
from unittest.mock import patch

from cryptography import x509
from cryptography.hazmat.primitives import hashes
from cryptography.hazmat.primitives.asymmetric import rsa
from cryptography.hazmat.primitives.serialization import (
    Encoding, NoEncryption, PrivateFormat, pkcs12,
)
from cryptography.x509.oid import NameOID

import nfce_download_worker as worker


class ClientChainTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root_key = rsa.generate_private_key(public_exponent=65537, key_size=2048)
        cls.issuer_key = rsa.generate_private_key(public_exponent=65537, key_size=2048)
        cls.leaf_key = rsa.generate_private_key(public_exponent=65537, key_size=2048)
        cls.root = cls.make_cert("Test Root", cls.root_key, None, cls.root_key, True)
        cls.issuer = cls.make_cert("Test Issuer", cls.issuer_key, cls.root, cls.root_key, True)
        cls.leaf = cls.make_cert("Company:33266186000184", cls.leaf_key,
                                 cls.issuer, cls.issuer_key, False)

    @staticmethod
    def make_cert(name, key, issuer, signing_key, ca, expired=False):
        now = datetime.now(timezone.utc)
        subject = x509.Name([x509.NameAttribute(NameOID.COMMON_NAME, name)])
        return (x509.CertificateBuilder()
                .subject_name(subject).issuer_name(issuer.subject if issuer else subject)
                .public_key(key.public_key()).serial_number(x509.random_serial_number())
                .not_valid_before(now - timedelta(days=2))
                .not_valid_after(now + timedelta(days=-1 if expired else 30))
                .add_extension(x509.BasicConstraints(ca=ca, path_length=None), critical=True)
                .sign(signing_key, hashes.SHA256()))

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.directory = Path(self.temp.name)
        self.location = patch.object(worker, "__file__", str(self.directory / "worker.py"))
        self.location.start()
        self.addCleanup(self.location.stop)

    def bundle(self, *certificates):
        (self.directory / "nfce-client-ca-chain.pem").write_bytes(
            b"".join(c.public_bytes(Encoding.PEM) for c in certificates))

    def test_missing_chain_completed_in_exported_pem(self):
        self.bundle(self.root, self.issuer)
        blob = pkcs12.serialize_key_and_certificates(
            b"client", self.leaf_key, self.leaf, None, NoEncryption())
        cert_path, key_path, cnpj = worker._certificate_files(blob, "", self.directory)
        actual = x509.load_pem_x509_certificates(cert_path.read_bytes())
        self.assertEqual(actual, [self.leaf, self.issuer])
        self.assertEqual(cnpj, "33266186000184")
        self.assertIn(b"PRIVATE KEY", key_path.read_bytes())

    def test_existing_chain_deduplicated_and_root_omitted(self):
        self.bundle(self.root, self.issuer)
        actual = worker._client_certificate_chain(
            self.leaf, [self.root, self.issuer, self.issuer])
        self.assertEqual(actual, [self.issuer])

    def test_unrelated_certificates_not_sent(self):
        self.bundle(self.root)
        self.assertEqual(worker._client_certificate_chain(self.leaf, [self.root]), [])

    def test_existing_other_issuer_chain_preserved_without_bundle(self):
        self.assertEqual(worker._client_certificate_chain(
            self.leaf, [self.root, self.issuer]), [self.issuer])

    def test_wrong_issuer_signature_rejected(self):
        wrong_key = rsa.generate_private_key(public_exponent=65537, key_size=2048)
        fake = self.make_cert("Test Issuer", wrong_key, self.root, self.root_key, True)
        self.bundle(fake, self.root)
        with self.assertRaisesRegex(ValueError, "invalida"):
            worker._client_certificate_chain(self.leaf, None)

    def test_expired_intermediate_rejected(self):
        expired = self.make_cert("Test Issuer", self.issuer_key, self.root,
                                 self.root_key, True, expired=True)
        self.bundle(expired, self.root)
        with self.assertRaisesRegex(ValueError, "expirada"):
            worker._client_certificate_chain(self.leaf, None)

    def test_non_ca_intermediate_rejected(self):
        invalid = self.make_cert("Test Issuer", self.issuer_key, self.root,
                                 self.root_key, False)
        self.bundle(invalid, self.root)
        with self.assertRaisesRegex(ValueError, "invalida"):
            worker._client_certificate_chain(self.leaf, None)


if __name__ == "__main__":
    unittest.main()
