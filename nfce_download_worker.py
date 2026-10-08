"""Worker assíncrono de download de NFC-e via SVRS.

Integração no servidor FastAPI existente::

    from integrations.python.nfce_download_worker import router as nfce_router
    app.include_router(nfce_router)

O estado de execução é temporário. Jobs internos entregam cada XML ao Supabase
configurado no servidor usando token efêmero validado no banco.
"""

from __future__ import annotations

import base64
import csv
import hashlib
import html
import io
import json
import logging
import os
import random
import re
import secrets
import sys
import shutil
import tempfile
import threading
import time
import zipfile
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass, field
from datetime import datetime, timedelta, timezone
from html.parser import HTMLParser
from pathlib import Path
from typing import Any
from urllib.parse import quote, urlparse
from xml.etree import ElementTree as ET

import requests

_logger = logging.getLogger("nfce_download")
_logger.setLevel(logging.INFO)
if not _logger.handlers:
    _handler = logging.StreamHandler(sys.stdout)
    _handler.setFormatter(logging.Formatter("%(message)s"))
    _logger.addHandler(_handler)
_logger.propagate = False
from cryptography import x509
from cryptography.hazmat.primitives import hashes
from cryptography.hazmat.primitives.serialization import Encoding, NoEncryption, PrivateFormat, pkcs12
from cryptography.x509.oid import NameOID
from fastapi import APIRouter, File, Form, Header, HTTPException, UploadFile
from fastapi.responses import FileResponse

SVRS_CONSULTA_URL = "https://nfce.svrs.rs.gov.br/ws/NfeConsulta/NfeConsulta4.asmx"
SVRS_DOWNLOAD_GET_URL = "https://dfe-portal.svrs.rs.gov.br/NFCESSL/DownloadXMLDFe"
SVRS_DOWNLOAD_POST_URL = "https://dfe-portal.svrs.rs.gov.br/BpeSSL/DownloadXmlDfe"
SOAP_ACTION = "http://www.portalfiscal.inf.br/nfe/wsdl/NFeConsultaProtocolo4/nfeConsultaNF"
REQUEST_TIMEOUT = int(os.getenv("NFCE_REQUEST_TIMEOUT", "45"))
JOB_TTL_SECONDS = int(os.getenv("NFCE_JOB_TTL_SECONDS", "21600"))
MAX_UPLOAD_BYTES = int(os.getenv("NFCE_MAX_UPLOAD_BYTES", str(2 * 1024 * 1024)))
MAX_NUMERACOES = int(os.getenv("NFCE_MAX_NUMERACOES", "10000"))
MAX_QUEUED_JOBS = int(os.getenv("NFCE_MAX_QUEUED_JOBS", "10"))
WORK_ROOT = Path(os.getenv("NFCE_WORK_ROOT", tempfile.gettempdir())) / "nexus_nfce_jobs"
WORK_ROOT.mkdir(parents=True, exist_ok=True)
ICP_BRASIL_CA_PATH = Path(__file__).with_name("icp-brasil-v10.pem")
ICP_BRASIL_CA_SHA256 = "6E0BFF069A26994C15DE2C4888CC54AF84882E5495B7FBF66BE9CCFFEC7489F6"

router = APIRouter(prefix="/nfce/download-jobs", tags=["NFC-e"])
_jobs_lock = threading.Lock()
_jobs: dict[str, "Job"] = {}
# Um download por vez. Quem roda uma empresa não soma taxa no portal.
_executor = ThreadPoolExecutor(max_workers=max(1, int(os.getenv("NFCE_WORKERS", "1"))))
DOWNLOAD_CONCURRENCY = 1
# Compatibilidade com o health-check da API. Zero significa sem limite por lote.
MAX_PENDING_PER_RUN = 0
# Piso de 1 min entre downloads. Limite não confirmado pela documentação oficial.
SVRS_INTERVAL_MIN_SECONDS = 60
SVRS_INTERVAL_MAX_SECONDS = 120
PORTAL_EMPTY_RETRY_SECONDS = 60
# Piso operacional configurado. Limite não confirmado pela documentação oficial.
SEFAZ_COOLDOWN_SECONDS = 60
SEFAZ_BACKOFF_BASE_SECONDS = 1.0
SEFAZ_BACKOFF_MAX_SECONDS = 30.0
SEFAZ_MAX_RETRIES_CAP = 3
CIRCUIT_FAILURE_THRESHOLD = 5
CANCELLED_QUEUE_ERROR = "[fora-da-fila] Fila cancelada"
PORTAL_EMPTY_RETRY_LIMIT = 3
WORKER_BUSY_DETAIL = (
    "O worker já está ocupado com outros downloads de NFC-e. "
    "Aguarde o lote atual; esta empresa volta sozinha para a fila."
)
_auth_cache: dict[str, tuple[float, str]] = {}


@dataclass
class Job:
    id: str
    owner_id: str
    directory: Path
    status: str = "queued"
    message: str = "Aguardando processamento"
    progress: int = 0
    consulted: int = 0
    found: int = 0
    downloaded: int = 0
    current_number: int | None = None
    current_competence: str | None = None
    error: str | None = None
    created_at: float = field(default_factory=time.time)
    updated_at: float = field(default_factory=time.time)
    zip_path: Path | None = None
    callback_token: str | None = None
    external_run_id: str | None = None
    empresa_id: str = ""
    organizacao_id: str = ""

    def public(self) -> dict[str, Any]:
        return {
            "id": self.id,
            "status": self.status,
            "message": self.message,
            "progress": self.progress,
            "consulted": self.consulted,
            "found": self.found,
            "downloaded": self.downloaded,
            "current_number": self.current_number,
            "current_competence": self.current_competence,
            "error": self.error,
            "download_ready": self.status == "completed" and bool(self.zip_path),
            "created_at": datetime.fromtimestamp(self.created_at, timezone.utc).isoformat(),
            "updated_at": datetime.fromtimestamp(self.updated_at, timezone.utc).isoformat(),
        }


def _digits(value: str) -> str:
    return re.sub(r"\D", "", value or "")


def svrs_ca_bundle() -> str:
    try:
        certificate = x509.load_pem_x509_certificate(ICP_BRASIL_CA_PATH.read_bytes())
    except (OSError, ValueError) as exc:
        raise RuntimeError("Cadeia ICP-Brasil v10 ausente ou inválida.") from exc
    fingerprint = certificate.fingerprint(hashes.SHA256()).hex().upper()
    if fingerprint != ICP_BRASIL_CA_SHA256:
        raise RuntimeError("Fingerprint da cadeia ICP-Brasil v10 não confere.")
    # A consulta NFC-e usa ICP-Brasil, enquanto o portal de download usa
    # GlobalSign. O mesmo Session precisa confiar nas duas cadeias.
    bundle_path = WORK_ROOT / "svrs-ca-bundle.pem"
    if not bundle_path.exists():
        public_roots = Path(requests.certs.where()).read_bytes()
        separator = b"" if public_roots.endswith(b"\n") else b"\n"
        bundle_path.write_bytes(public_roots + separator + ICP_BRASIL_CA_PATH.read_bytes())
        bundle_path.chmod(0o600)
    return str(bundle_path)


def _local_name(element: ET.Element) -> str:
    return element.tag.split("}", 1)[-1]


def parse_seed_xml(xml_bytes: bytes) -> dict[str, Any]:
    if len(xml_bytes) > MAX_UPLOAD_BYTES:
        raise ValueError("XML semente excede o limite permitido.")
    try:
        root = ET.fromstring(xml_bytes)
    except ET.ParseError as exc:
        raise ValueError("XML semente inválido.") from exc

    inf_nfe = next((e for e in root.iter() if _local_name(e) == "infNFe"), None)
    emit = next((e for e in root.iter() if _local_name(e) == "emit"), None)
    if inf_nfe is None or emit is None:
        raise ValueError("O arquivo não contém uma NFC-e válida (infNFe/emit).")

    def value(parent: ET.Element, tag: str, required: bool = True) -> str:
        for elem in parent.iter():
            if _local_name(elem) == tag and (elem.text or "").strip():
                return (elem.text or "").strip()
        if required:
            raise ValueError(f"Tag obrigatória ausente: {tag}.")
        return ""

    model = value(inf_nfe, "mod")
    if model != "65":
        raise ValueError("O XML semente deve ser NFC-e modelo 65.")
    cnpj = _digits(value(emit, "CNPJ"))
    if len(cnpj) != 14:
        raise ValueError("CNPJ do emitente inválido no XML semente.")
    key = inf_nfe.attrib.get("Id", "")
    key = key[3:47] if key.startswith("NFe") else ""
    emission = value(inf_nfe, "dhEmi", False)
    if len(key) == 44 and key.isdigit():
        aamm = key[2:6]
    elif re.match(r"^\d{4}-\d{2}", emission):
        aamm = emission[2:4] + emission[5:7]
    else:
        raise ValueError("Não foi possível determinar a competência do XML.")
    return {
        "cnpj": cnpj,
        "company_name": value(emit, "xNome", False) or "EMPRESA",
        "cuf": value(inf_nfe, "cUF").zfill(2),
        "aamm": aamm,
        "model": model,
        "series": value(inf_nfe, "serie").zfill(3),
        "number": int(value(inf_nfe, "nNF")),
        "emission_type": value(inf_nfe, "tpEmis", False) or "1",
    }


def next_aamm(aamm: str) -> str:
    year, month = 2000 + int(aamm[:2]), int(aamm[2:4]) + 1
    if month == 13:
        year, month = year + 1, 1
    return f"{year % 100:02d}{month:02d}"


def aamm_order(aamm: str) -> int:
    return (2000 + int(aamm[:2])) * 100 + int(aamm[2:4])


def current_aamm() -> str:
    now = datetime.now()
    return f"{now.year % 100:02d}{now.month:02d}"


def access_key(cfg: dict[str, Any], number: int, aamm: str) -> str:
    base = (
        cfg["cuf"] + aamm + cfg["cnpj"] + cfg["model"].zfill(2)
        + cfg["series"].zfill(3) + f"{number:09d}"
        + cfg["emission_type"] + "00000001"
    )
    weights, total = (2, 3, 4, 5, 6, 7, 8, 9), 0
    for index, digit in enumerate(reversed(base)):
        total += int(digit) * weights[index % len(weights)]
    dv = 11 - total % 11
    return base + ("0" if dv >= 10 else str(dv))


def soap_request(key: str) -> str:
    return (
        '<?xml version="1.0" encoding="utf-8"?>'
        '<soap12:Envelope xmlns:soap12="http://www.w3.org/2003/05/soap-envelope">'
        '<soap12:Body><nfeDadosMsg xmlns="http://www.portalfiscal.inf.br/nfe/wsdl/NFeConsultaProtocolo4">'
        '<consSitNFe versao="4.00" xmlns="http://www.portalfiscal.inf.br/nfe">'
        f'<tpAmb>1</tpAmb><xServ>CONSULTAR</xServ><chNFe>{key}</chNFe>'
        '</consSitNFe></nfeDadosMsg></soap12:Body></soap12:Envelope>'
    )


def extract_status(text: str) -> tuple[str, str, str]:
    status_match = re.search(r"<cStat>(\d+)</cStat>", text)
    reason_match = re.search(r"<xMotivo>(.*?)</xMotivo>", text, re.S)
    keys = sorted(set(re.findall(r"(?<!\d)\d{44}(?!\d)", text or "")))
    return (
        status_match.group(1) if status_match else "",
        html.unescape(reason_match.group(1).strip()) if reason_match else "",
        keys[-1] if keys else "",
    )


def format_wait(seconds: int) -> str:
    minutes, rest = divmod(max(0, int(seconds)), 60)
    if minutes and rest:
        return f"{minutes} min {rest} s"
    if minutes:
        return f"{minutes} min"
    return f"{rest} s"


def clamp_download_interval(seconds: int) -> int:
    """Mantém o espaço entre downloads da SVRS entre 1 min e 2 min."""
    try:
        value = int(seconds)
    except (TypeError, ValueError):
        value = SVRS_INTERVAL_MIN_SECONDS
    return max(SVRS_INTERVAL_MIN_SECONDS, min(SVRS_INTERVAL_MAX_SECONDS, value))


def sefaz_cooldown_seconds() -> float:
    try:
        value = float(os.getenv("SEFAZ_COOLDOWN_SECONDS", str(SEFAZ_COOLDOWN_SECONDS)))
    except (TypeError, ValueError):
        value = float(SEFAZ_COOLDOWN_SECONDS)
    return max(1.0, value)


def sefaz_backoff_base() -> float:
    try:
        value = float(os.getenv("SEFAZ_BACKOFF_BASE", str(SEFAZ_BACKOFF_BASE_SECONDS)))
    except (TypeError, ValueError):
        value = SEFAZ_BACKOFF_BASE_SECONDS
    return max(0.1, value)


def sefaz_backoff_max() -> float:
    try:
        value = float(os.getenv("SEFAZ_BACKOFF_MAX", str(SEFAZ_BACKOFF_MAX_SECONDS)))
    except (TypeError, ValueError):
        value = SEFAZ_BACKOFF_MAX_SECONDS
    return max(sefaz_backoff_base(), value)


def sefaz_max_retries() -> int:
    """Teto 3. Não aumenta o máximo que já estava em produção."""
    try:
        value = int(os.getenv("SEFAZ_MAX_RETRIES", str(SEFAZ_MAX_RETRIES_CAP)))
    except (TypeError, ValueError):
        value = SEFAZ_MAX_RETRIES_CAP
    return max(1, min(SEFAZ_MAX_RETRIES_CAP, value))


def transient_backoff_seconds(attempt: int, jitter_seconds: float | None = None) -> float:
    """Backoff exponencial da tentativa transitória. attempt 0 é a primeira repetição."""
    if jitter_seconds is None:
        jitter_seconds = random.uniform(0, sefaz_backoff_base())
    raw = (sefaz_backoff_base() * (2 ** max(0, int(attempt)))) + max(0.0, float(jitter_seconds))
    return min(sefaz_backoff_max(), raw)


def failure_policy(kind: str) -> str:
    """cooldown, backoff, same_key ou permanent. Limite do portal não entra no retry."""
    if kind == "rate_limit":
        return "cooldown"
    if kind in {"timeout", "http", "proxy", "network"}:
        return "backoff"
    if kind == "no_xml":
        return "same_key"
    if kind in {"certificate", "cnpj", "unavailable", "circuit_open"}:
        return "permanent" if kind in {"certificate", "cnpj", "unavailable"} else "backoff"
    return "permanent"


def certificate_mismatch_stops(cert_cnpj: str, emit_cnpj: str) -> bool:
    return bool(cert_cnpj) and cert_cnpj != emit_cnpj


def client_error_is_permanent(kind: str) -> bool:
    return kind in {"certificate", "cnpj"}


def discovery_download_plan(
    *,
    found: bool,
    xml_already_saved: bool,
) -> str:
    """continue, skip_saved ou download; não limita a quantidade por execução."""
    if not found:
        return "continue"
    if xml_already_saved:
        return "skip_saved"
    return "download"


def should_request_xml(*, xml_already_saved: bool) -> bool:
    return not xml_already_saved


def parked_note_is_eligible(*, ultimo_erro: str | None, xml_exists: bool) -> bool:
    """Cancelamento do operador sem XML volta à fila. Falha permanente e XML salvo não voltam."""
    if xml_exists:
        return False
    text = str(ultimo_erro or "")
    if "após 3 tentativas" in text or "apos 3 tentativas" in text:
        return False
    return text == CANCELLED_QUEUE_ERROR


def handle_discovered_key(
    *,
    xml_already_saved: bool,
    download,
) -> str:
    """skip_saved, pause ou download. download() devolve ok, pause ou failed."""
    plan = discovery_download_plan(
        found=True,
        xml_already_saved=xml_already_saved,
    )
    if plan != "download":
        return plan
    status = download()
    if status == "pause":
        return "pause"
    return "download"


class SvrsRateLimiter:
    """Relógio único do processo. SOAP e download não dividem o mesmo espaçamento.

    O canal de download tem available, cooldown e half_open.
    O teste injeta clock e sleep. Produção usa time.monotonic e time.sleep.
    Vários processos Render exigiriam coordenação no banco. Hoje há um processo.
    """

    def __init__(
        self,
        soap_seconds: float = 0.1,
        download_seconds: float = 90,
        clock: Any = None,
        sleep: Any = None,
        cooldown_seconds: float | None = None,
    ) -> None:
        self.soap_seconds = max(0.0, float(soap_seconds))
        self.download_seconds = max(0.0, float(download_seconds))
        self.cooldown_seconds = (
            float(cooldown_seconds) if cooldown_seconds is not None else sefaz_cooldown_seconds()
        )
        self._clock = clock or time.monotonic
        self._sleep = sleep or time.sleep
        self._lock = threading.Lock()
        self._next = {"soap": 0.0, "download": 0.0}
        self._download_state = "available"
        self._cooldown_until = 0.0
        self._probe_issued = False

    def download_state(self) -> str:
        with self._lock:
            self._roll_download_state_locked(float(self._clock()))
            return self._download_state

    def download_admission(self) -> bool:
        """False enquanto o cooldown não venceu ou a sonda half_open já saiu."""
        with self._lock:
            now = float(self._clock())
            self._roll_download_state_locked(now)
            if self._download_state == "cooldown":
                return False
            if self._download_state == "half_open" and self._probe_issued:
                return False
            return True

    def _roll_download_state_locked(self, now: float) -> None:
        if self._download_state == "cooldown" and now >= self._cooldown_until:
            self._download_state = "half_open"
            self._probe_issued = False

    def note_remote_limit(self) -> None:
        with self._lock:
            now = float(self._clock())
            self._download_state = "cooldown"
            self._cooldown_until = now + self.cooldown_seconds
            self._probe_issued = False
            self._next["download"] = self._cooldown_until

    def note_download_ok(self) -> None:
        with self._lock:
            if self._download_state == "half_open":
                self._download_state = "available"
                self._probe_issued = False
                now = float(self._clock())
                self._next["download"] = now + self.download_seconds

    def begin_download(self) -> str:
        """call libera uma requisição. skip não chama o portal."""
        mode = "allow"
        with self._lock:
            now = float(self._clock())
            self._roll_download_state_locked(now)
            if self._download_state == "cooldown":
                delay = max(0.0, self._cooldown_until - now)
                mode = "cooldown"
            elif self._download_state == "half_open" and self._probe_issued:
                return "skip"
            elif self._download_state == "half_open":
                self._probe_issued = True
                delay = 0.0
                mode = "probe"
            else:
                delay = self._next.get("download", 0.0) - now
                if delay < 0:
                    delay = 0.0
                self._next["download"] = now + delay + self.download_seconds
                mode = "allow"
        if delay > 0:
            self._sleep(delay)
            if mode == "cooldown":
                with self._lock:
                    self._roll_download_state_locked(float(self._clock()))
                    self._download_state = "half_open"
                    self._probe_issued = True
        return "call"

    def wait(self, channel: str) -> float:
        if channel == "download" and self.download_state() == "cooldown":
            decision = self.begin_download()
            if decision == "skip":
                return 0.0
            return 0.0
        spacing = self.soap_seconds if channel == "soap" else self.download_seconds
        with self._lock:
            now = float(self._clock())
            delay = self._next.get(channel, 0.0) - now
            if delay < 0:
                delay = 0.0
            self._next[channel] = now + delay + spacing
        if delay > 0:
            self._sleep(delay)
        return delay

    def arm_same_key_retry(self, seconds: float) -> None:
        """A próxima espera do download desta chave fica em `seconds`, sem furar o cooldown."""
        with self._lock:
            now = float(self._clock())
            target = now + max(0.0, float(seconds))
            if self._download_state == "cooldown":
                target = max(target, self._cooldown_until)
            self._next["download"] = target


def discovery_action(status: str, artificial: str, real_key: str) -> tuple[str, str]:
    """absent avança o cursor. found só avança depois do ack. hold não passa do número."""
    if status == "217":
        return "absent", ""
    if status == "100" and len(artificial) == 44:
        return "found", artificial
    if status == "613" and len(real_key) == 44 and real_key != artificial:
        return "found", real_key
    return "hold", ""


def apply_discovery_step(
    safe_aamm: str,
    safe_nnf: int,
    aamm: str,
    number: int,
    status: str,
    artificial: str,
    real_key: str,
    acked: bool,
) -> tuple[str, int, str, str]:
    """Cursor novo, ação e chave. Sem ack, o cursor fica no valor anterior."""
    action, key = discovery_action(status, artificial, real_key)
    if action == "hold" or not acked:
        return safe_aamm, safe_nnf, action, key
    return aamm, number, action, key


def discovery_scan_complete(reason: str, found_count: int = 0) -> bool:
    """Gap fecha a varredura. Teto sem nenhuma chave também fecha, e a fila segue.
    Teto com chave encontrada continua a mesma empresa. Pausa e falha de ack continuam abertas.
    """
    if reason == "gap":
        return True
    return reason == "cap" and found_count == 0


def download_retries_immediately(kind: str, attempt: int) -> bool:
    """attempt começa em 0. Limite da SVRS e XML ausente não repetem na hora."""
    limit = 3 if kind in {"timeout", "http"} else 1
    return attempt + 1 < limit


def download_retries_same_key(kind: str, attempt: int) -> bool:
    """Página sem XML: a mesma chave volta depois de 60 s, até 3 vezes. Limite entra em cooldown."""
    if kind != "no_xml":
        return False
    return attempt + 1 < PORTAL_EMPTY_RETRY_LIMIT


_shared_limiter: SvrsRateLimiter | None = None
_shared_limiter_guard = threading.Lock()


def shared_rate_limiter(soap_seconds: float, download_seconds: float) -> SvrsRateLimiter:
    """Um relógio para o processo. O job seguinte não começa do zero."""
    global _shared_limiter
    with _shared_limiter_guard:
        if _shared_limiter is None:
            _shared_limiter = SvrsRateLimiter(
                soap_seconds=soap_seconds,
                download_seconds=download_seconds,
            )
        else:
            _shared_limiter.soap_seconds = max(_shared_limiter.soap_seconds, float(soap_seconds))
            _shared_limiter.download_seconds = max(
                _shared_limiter.download_seconds,
                float(download_seconds),
            )
        return _shared_limiter


def reset_shared_rate_limiter() -> None:
    global _shared_limiter
    with _shared_limiter_guard:
        _shared_limiter = None


class TransportCircuitBreaker:
    """Aberto só por falha de transporte. Limite do portal não abre o circuito."""

    def __init__(
        self,
        threshold: int = CIRCUIT_FAILURE_THRESHOLD,
        cooldown_seconds: float | None = None,
        clock: Any = None,
    ) -> None:
        self.threshold = max(1, int(threshold))
        self.cooldown_seconds = (
            float(cooldown_seconds) if cooldown_seconds is not None else sefaz_cooldown_seconds()
        )
        self._clock = clock or time.monotonic
        self._lock = threading.Lock()
        self.state = "closed"
        self.failures = 0
        self.open_until = 0.0
        self.probe_used = False

    def allow_call(self) -> bool:
        with self._lock:
            now = float(self._clock())
            if self.state == "open":
                if now < self.open_until:
                    return False
                self.state = "half_open"
                self.probe_used = False
            if self.state == "half_open":
                if self.probe_used:
                    return False
                self.probe_used = True
                return True
            return True

    def note_success(self) -> None:
        with self._lock:
            self.state = "closed"
            self.failures = 0
            self.probe_used = False

    def note_transport_failure(self) -> None:
        with self._lock:
            now = float(self._clock())
            if self.state == "half_open":
                self.state = "open"
                self.open_until = now + self.cooldown_seconds
                self.probe_used = False
                return
            self.failures += 1
            if self.failures >= self.threshold:
                self.state = "open"
                self.open_until = now + self.cooldown_seconds


_shared_circuit: TransportCircuitBreaker | None = None
_shared_circuit_guard = threading.Lock()


def shared_transport_circuit() -> TransportCircuitBreaker:
    global _shared_circuit
    with _shared_circuit_guard:
        if _shared_circuit is None:
            _shared_circuit = TransportCircuitBreaker()
        return _shared_circuit


def reset_shared_transport_circuit() -> None:
    global _shared_circuit
    with _shared_circuit_guard:
        _shared_circuit = None


@dataclass
class OutboundRoute:
    outbound_id: str
    proxy_url: str | None = None
    username: str = ""
    password: str = ""
    health: str = "healthy"
    unhealthy_until: float = 0.0


class OutboundTransportManager:
    """Saída de rede. PROXY_ENABLED=false usa a conexão direta do processo.

    Falha de proxy pode trocar de saída. Resposta de limite da SVRS não troca.
    """

    def __init__(
        self,
        routes: list[OutboundRoute],
        enabled: bool = False,
        cooldown_seconds: float | None = None,
        clock: Any = None,
    ) -> None:
        self.routes = routes or [OutboundRoute("direct", None)]
        self.enabled = enabled and any(route.proxy_url for route in self.routes)
        self.cooldown_seconds = (
            float(cooldown_seconds) if cooldown_seconds is not None else sefaz_cooldown_seconds()
        )
        self._clock = clock or time.monotonic
        self._lock = threading.Lock()
        self.index = 0

    @classmethod
    def from_env(cls, environ: dict[str, str] | None = None) -> "OutboundTransportManager":
        env = environ if environ is not None else os.environ
        enabled = str(env.get("PROXY_ENABLED", "false")).strip().lower() in {"1", "true", "yes", "sim"}
        if not enabled:
            return cls([OutboundRoute("direct", None)], enabled=False)
        specs = [("outbound-1", "PROXY_URL", "PROXY_USERNAME", "PROXY_PASSWORD")]
        specs += [
            (f"outbound-{number}", f"PROXY_URL_{number}", f"PROXY_USERNAME_{number}", f"PROXY_PASSWORD_{number}")
            for number in (2, 3)
        ]
        routes: list[OutboundRoute] = []
        for outbound_id, url_key, user_key, password_key in specs:
            proxy_url = str(env.get(url_key) or "").strip()
            if not proxy_url:
                continue
            routes.append(
                OutboundRoute(
                    outbound_id,
                    proxy_url,
                    str(env.get(user_key) or ""),
                    str(env.get(password_key) or ""),
                )
            )
        if not routes:
            return cls([OutboundRoute("direct", None)], enabled=False)
        return cls(routes, enabled=True)

    def current(self) -> OutboundRoute:
        with self._lock:
            self._refresh_locked(float(self._clock()))
            return self.routes[self.index]

    def _refresh_locked(self, now: float) -> None:
        for route in self.routes:
            if route.health == "unhealthy" and now >= route.unhealthy_until:
                route.health = "healthy"
        if self.routes[self.index].health == "healthy":
            return
        for step in range(1, len(self.routes) + 1):
            candidate = (self.index + step) % len(self.routes)
            if self.routes[candidate].health == "healthy":
                self.index = candidate
                return

    def _proxy_auth_url(self, route: OutboundRoute) -> str:
        raw = str(route.proxy_url or "")
        if not route.username:
            return raw
        parsed = urlparse(raw)
        host = parsed.hostname or ""
        port = f":{parsed.port}" if parsed.port else ""
        scheme = parsed.scheme or "http"
        user = quote(route.username, safe="")
        password = quote(route.password, safe="")
        return f"{scheme}://{user}:{password}@{host}{port}"

    def requests_proxies(self) -> dict[str, str] | None:
        if not self.enabled:
            return None
        route = self.current()
        if not route.proxy_url:
            return None
        url = self._proxy_auth_url(route)
        return {"http": url, "https": url}

    def apply(self, session: requests.Session) -> None:
        """Define o proxy da sessão. Não altera session.verify."""
        session.proxies.clear()
        proxies = self.requests_proxies()
        if proxies:
            session.proxies.update(proxies)

    def note_infrastructure_failure(self) -> bool:
        with self._lock:
            now = float(self._clock())
            current = self.routes[self.index]
            current.health = "unhealthy"
            current.unhealthy_until = now + self.cooldown_seconds
            origin = self.index
            for step in range(1, len(self.routes) + 1):
                candidate = (origin + step) % len(self.routes)
                if candidate != origin and self.routes[candidate].health == "healthy":
                    self.index = candidate
                    return True
            return False

    def note_remote_limit(self) -> None:
        """Limite da SVRS não troca a saída."""
        return None

    def note_success(self) -> None:
        with self._lock:
            self.routes[self.index].health = "healthy"
            self.routes[self.index].unhealthy_until = 0.0

    def public_status(self) -> dict[str, Any]:
        """Estado operacional sem URL, usuario ou senha do proxy."""
        route = self.current()
        return {
            "enabled": self.enabled,
            "routes": len(self.routes) if self.enabled else 0,
            "outbound_id": route.outbound_id if self.enabled else "direct",
            "outbound_health": route.health,
        }


_shared_transport: OutboundTransportManager | None = None
_shared_transport_guard = threading.Lock()


def shared_outbound_transport() -> OutboundTransportManager:
    global _shared_transport
    with _shared_transport_guard:
        if _shared_transport is None:
            _shared_transport = OutboundTransportManager.from_env()
        return _shared_transport


def reset_shared_outbound_transport() -> None:
    global _shared_transport
    with _shared_transport_guard:
        _shared_transport = None


def callback_backoff_seconds(attempt: int, jitter_seconds: float = 0) -> float:
    return (0.5 * (2 ** attempt)) + max(0.0, jitter_seconds)


_LOG_SECRET = re.compile(
    r"senha|password|pfx|private|jwt|service_role|authorization|token|secret|apikey",
    re.I,
)


def _redact_log_value(value: Any) -> Any:
    if value is None or isinstance(value, (int, float, bool)):
        return value
    text = str(value)
    if "BEGIN " in text or text.startswith("eyJ") or "Bearer " in text:
        return ""
    if "://" in text and "@" in text:
        return "[redacted-url]"
    return value


def log_attempt(
    *,
    run_id: str = "",
    empresa_id: str = "",
    aamm: str = "",
    nnf: int | None = None,
    chave: str = "",
    etapa: str,
    tentativa: int,
    duracao_ms: int,
    http: int | None = None,
    categoria: str,
    retry: bool = False,
    proxima_tentativa: str = "",
    fase: str = "",
    resultado: str = "",
    backoff: str = "",
    cooldown: str = "",
    circuit_state: str = "",
    proxy_enabled: bool | None = None,
    outbound_id: str = "",
    outbound_health: str = "",
    failover: bool = False,
    cstat: str = "",
    detalhe: str = "",
) -> dict[str, Any]:
    """Registro da tentativa. Senha, PFX, JWT, token e URL com credencial não entram."""
    raw = {
        "event": "nfce_attempt",
        "timestamp": datetime.now(timezone.utc).isoformat(),
        "run_id": run_id,
        "empresa_id": empresa_id,
        "aamm": aamm,
        "nnf": nnf,
        "chave": chave,
        "etapa": etapa,
        "fase": fase or etapa,
        "tentativa": tentativa,
        "duracao_ms": duracao_ms,
        "http": http,
        "status_http": http,
        "cstat": cstat,
        "detalhe": detalhe,
        "categoria": categoria,
        "resultado": resultado or categoria,
        "retry": retry,
        "backoff": backoff,
        "cooldown": cooldown,
        "circuit_state": circuit_state,
        "proxima_tentativa": proxima_tentativa,
        "proxy_enabled": proxy_enabled,
        "outbound_id": outbound_id,
        "outbound_health": outbound_health,
        "failover": failover,
    }
    record: dict[str, Any] = {}
    for key, value in raw.items():
        if _LOG_SECRET.search(key):
            continue
        record[key] = _redact_log_value(value)
    _logger.info(json.dumps(record, ensure_ascii=False))
    return record


class _PortalDiagnostics(HTMLParser):
    def __init__(self):
        super().__init__()
        self.in_title = False
        self.title: list[str] = []
        self.forms: list[dict[str, str]] = []
        self.fields: set[str] = set()

    def handle_starttag(self, tag, attrs):
        values = dict(attrs)
        if tag == "title":
            self.in_title = True
        elif tag == "form":
            action = urlparse(values.get("action") or "")
            self.forms.append({"method": (values.get("method") or "get").lower(),
                               "action_path": action.path[:200]})
        elif tag in {"input", "select", "textarea"} and values.get("name"):
            self.fields.add(values["name"][:100])

    def handle_endtag(self, tag):
        if tag == "title":
            self.in_title = False

    def handle_data(self, data):
        if self.in_title:
            self.title.append(data)


def _log_remote_response(response: requests.Response, phase: str, started: float,
                         context: dict[str, Any] | None = None) -> None:
    text = response.text
    sample = html.unescape(text or "")[:8000].lower()
    status, reason, _ = extract_status(text) if phase == "consulta_soap" else ("", "", "")
    endpoint = urlparse(response.url or "")
    page = _PortalDiagnostics()
    if phase.startswith("portal_"):
        page.feed(text)
    # Only allowlisted evidence is emitted; never log HTML forms, cookies or XML bodies.
    evidence = {
        "endpoint": f"{endpoint.hostname or ''}{endpoint.path}",
        "content_type": response.headers.get("Content-Type", "")[:120],
        "response_bytes": len(response.content),
        "redirect_statuses": [item.status_code for item in response.history],
        "block_signals": [hint for hint in _RATE_LIMIT_HINTS if hint in sample],
        "unavailable_signals": [hint for hint in _UNAVAILABLE_HINTS if hint in sample],
        "xMotivo": _redact_log_value(reason[:500]),
        "has_xml": bool(extract_downloaded_xml(text)) if phase == "portal_post" else False,
        "page_title": _redact_log_value(" ".join(page.title).strip()[:200]),
        "forms": page.forms[:10],
        "field_names": sorted(page.fields)[:50],
        "captcha_present": "captcha" in sample,
        "certificate_required": "exige certificado digital" in sample,
        "processing_error": "erro no processamento" in sample,
        "xml_markup_present": any(marker in text for marker in (
            "<nfeProc", "<NFe", "&lt;nfeProc", "&lt;NFe")),
    }
    log_attempt(
        **(context or {}), etapa=phase, duracao_ms=int((time.perf_counter() - started) * 1000),
        http=response.status_code, categoria=status or classify_portal_body(response.status_code, text),
        cstat=status, detalhe=json.dumps(evidence, ensure_ascii=False),
    )


_RATE_LIMIT_HINTS = (
    "muitas consultas",
    "muitas requisi",
    "excesso de requis",
    "too many",
    "bloqueio",
    "bloqueado",
    "tente novamente mais tarde",
    "limite de acesso",
    "acesso temporariamente",
)
_UNAVAILABLE_HINTS = (
    "cancelad",
    "inexistente",
    "não encontr",
    "nao encontr",
    "documento inválido",
    "documento invalido",
    "denegad",
    "chave de acesso inválida",
    "chave de acesso invalida",
)


def classify_portal_body(status_code: int, text: str) -> str:
    """rate_limit no 429 ou no HTML de bloqueio. 503 sem esse texto é falha transitória."""
    sample = html.unescape(text or "")[:8000].lower()
    if status_code == 429 or any(hint in sample for hint in _RATE_LIMIT_HINTS):
        return "rate_limit"
    if any(hint in sample for hint in _UNAVAILABLE_HINTS):
        return "unavailable"
    if status_code >= 500:
        return "http"
    return "no_xml"


def download_failure_message(kind: str, status_code: int = 0) -> str:
    if kind == "rate_limit":
        return (
            "Limite da SVRS: muitas consultas em sequência. "
            "Esta NFC-e continua na fila. O lote pausa 1 min para não tomar bloqueio."
        )
    if kind == "unavailable":
        return (
            "NFC-e sem XML no portal da SVRS (cancelada ou indisponível). "
            "Não é falha de conexão."
        )
    if kind == "timeout":
        return (
            "A SVRS não respondeu a tempo. "
            "A chave continua na fila e será tentada de novo com intervalo de 1 min."
        )
    if kind == "http":
        code = f" HTTP {status_code}" if status_code else ""
        return (
            f"A SVRS retornou erro{code}. "
            "A chave continua na fila para o próximo lote."
        )
    if kind == "circuit_open":
        return (
            "Consulta à SVRS em pausa depois de falhas de rede seguidas. "
            "Esta NFC-e continua na fila."
        )
    if kind == "proxy":
        return (
            "A saída de rede configurada falhou antes de alcançar a SVRS. "
            "Esta NFC-e continua na fila."
        )
    return (
        "O portal da SVRS respondeu, mas não trouxe o XML desta chave. "
        "Nova tentativa no próximo lote."
    )


def extract_downloaded_xml(text: str) -> str | None:
    cleaned = text.replace(r'\"', '"').replace(r"\/", "/")
    # Validate before decoding: XML entities such as &amp; must stay intact.
    for _ in range(3):
        for opening, closing in (("<nfeProc", "</nfeProc>"), ("<NFe", "</NFe>")):
            start, end = cleaned.find(opening), cleaned.rfind(closing)
            if start >= 0 and end > start:
                candidate = cleaned[start : end + len(closing)].strip()
                try:
                    ET.fromstring(candidate)
                    return candidate
                except ET.ParseError:
                    continue
        decoded = html.unescape(cleaned)
        if decoded == cleaned:
            break
        cleaned = decoded
    return None


def _xml_emission_date(xml: str) -> str:
    match = re.search(r"<dhEmi>([^<]+)</dhEmi>", xml)
    return match.group(1).strip() if match else ""


def _anon_headers() -> dict[str, str]:
    anon_key = os.getenv(
        "SUPABASE_ANON_KEY",
        "eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9.eyJpc3MiOiJzdXBhYmFzZSIsInJlZiI6InZxaHRieWllY3N4eHByaWtwbnVzIiwicm9sZSI6ImFub24iLCJpYXQiOjE3NjYwNjU3OTUsImV4cCI6MjA4MTY0MTc5NX0.aOvciVxs4NjCpHEYZXQziJy-0PQpcy4h-E2CbMZWKJ8",
    )
    return {
        "Content-Type": "application/json",
        "apikey": anon_key,
        "Authorization": f"Bearer {anon_key}",
    }


def _callback(job: Job, event: str, **payload: Any) -> None:
    """Entrega somente ao Supabase configurado no servidor; nunca aceita URL do cliente."""
    if not job.callback_token or not job.external_run_id:
        return
    supabase_url = os.getenv("SUPABASE_URL", "https://vqhtbyiecsxxprikpnus.supabase.co").rstrip("/")
    parsed = urlparse(supabase_url)
    if parsed.scheme != "https" or parsed.hostname != "vqhtbyiecsxxprikpnus.supabase.co":
        raise RuntimeError("Destino persistente NFC-e não autorizado.")
    request_body = {
        "action": "callback", "event": event,
        "run_id": job.external_run_id, "token": job.callback_token, **payload,
    }
    last_error = ""
    timeout = 12 if event == "progress" else REQUEST_TIMEOUT
    attempts = 1 if event == "progress" else 3
    started = time.perf_counter()
    http_status: int | None = None
    categoria = "CALLBACK_ERROR"
    for attempt in range(attempts):
        try:
            response = requests.post(
                f"{supabase_url}/functions/v1/nfce-download",
                json=request_body,
                headers=_anon_headers(),
                timeout=timeout,
            )
            http_status = response.status_code
            if response.ok:
                categoria = "SUCCESS"
                log_attempt(
                    run_id=job.external_run_id or "",
                    empresa_id=job.empresa_id,
                    aamm=str(payload.get("aamm") or ""),
                    nnf=payload.get("number") if isinstance(payload.get("number"), int) else None,
                    chave=str(payload.get("key") or ""),
                    etapa="callback",
                    tentativa=attempt + 1,
                    duracao_ms=int((time.perf_counter() - started) * 1000),
                    http=http_status,
                    categoria=categoria,
                    retry=attempt > 0,
                )
                return
            try:
                body = response.json()
                detail = str(body.get("error") or body.get("message") or "")
            except (ValueError, AttributeError):
                detail = response.text.strip()
            detail = re.sub(r"\s+", " ", detail)[:500] or response.reason
            last_error = f"Callback NFC-e falhou ({response.status_code}): {detail}"
            if response.status_code < 500:
                break
        except requests.RequestException as exc:
            last_error = f"Callback NFC-e indisponível: {exc}"
        if attempt < attempts - 1:
            time.sleep(callback_backoff_seconds(attempt, secrets.randbelow(250) / 1000))
    log_attempt(
        run_id=job.external_run_id or "",
        empresa_id=job.empresa_id,
        aamm=str(payload.get("aamm") or ""),
        nnf=payload.get("number") if isinstance(payload.get("number"), int) else None,
        chave=str(payload.get("key") or ""),
        etapa="callback",
        tentativa=attempts,
        duracao_ms=int((time.perf_counter() - started) * 1000),
        http=http_status,
        categoria=categoria,
        retry=attempts > 1,
    )
    if event == "progress":
        return
    raise RuntimeError(last_error or "Callback NFC-e falhou sem resposta.")


def _certificate_files(pfx_bytes: bytes, password: str, directory: Path) -> tuple[Path, Path, str]:
    if len(pfx_bytes) > MAX_UPLOAD_BYTES:
        raise ValueError("Certificado excede o limite permitido.")
    if not pfx_bytes or len(pfx_bytes) < 64:
        raise ValueError("Certificado PFX vazio ou incompleto.")
    if pfx_bytes[:1] != b"\x30" and not pfx_bytes.startswith(b"\x80"):
        head = pfx_bytes[:32].lstrip()
        if head.startswith((b"-----BEGIN", b"MII", b"{", b"<")):
            raise ValueError(
                "Certificado não está em formato PFX/P12 binário "
                "(recebido texto/PEM/base64)."
            )
    try:
        key, cert, chain = pkcs12.load_key_and_certificates(
            pfx_bytes, password.encode("utf-8") if password else None
        )
    except ValueError as exc:
        message = str(exc).lower()
        if "password" in message or "mac" in message or "invalid" in message:
            raise ValueError(
                "Senha do certificado inválida ou PFX corrompido."
            ) from exc
        raise ValueError(f"Certificado ou senha inválidos: {exc}") from exc
    except Exception as exc:
        raise ValueError(f"Certificado ou senha inválidos: {exc}") from exc
    if key is None or cert is None:
        raise ValueError("O PFX não contém certificado e chave privada.")
    cert_path, key_path = directory / "client-cert.pem", directory / "client-key.pem"
    cert_data = cert.public_bytes(Encoding.PEM)
    for item in chain or []:
        cert_data += item.public_bytes(Encoding.PEM)
    cert_path.write_bytes(cert_data)
    key_path.write_bytes(key.private_bytes(Encoding.PEM, PrivateFormat.PKCS8, NoEncryption()))
    cert_path.chmod(0o600)
    key_path.chmod(0o600)
    subject = cert.subject.rfc4514_string()
    common_names = cert.subject.get_attributes_for_oid(NameOID.COMMON_NAME)
    identity = " ".join([subject] + [item.value for item in common_names])
    cnpjs = re.findall(r"(?<!\d)(\d{14})(?!\d)", identity)
    return cert_path, key_path, cnpjs[-1] if cnpjs else ""


def _update(job: Job, **values: Any) -> None:
    with _jobs_lock:
        for key, value in values.items():
            setattr(job, key, value)
        job.updated_at = time.time()


def _consult(session: requests.Session, cfg: dict[str, Any], number: int, aamm: str,
             log_context: dict[str, Any] | None = None) -> tuple[str, str, str]:
    artificial = access_key(cfg, number, aamm)
    started = time.perf_counter()
    response = session.post(
        SVRS_CONSULTA_URL,
        data=soap_request(artificial).encode("utf-8"),
        headers={"Content-Type": f'application/soap+xml; charset=utf-8; action="{SOAP_ACTION}"'},
        timeout=REQUEST_TIMEOUT,
    )
    _log_remote_response(response, "consulta_soap", started, log_context or {"tentativa": 1, "chave": artificial})
    response.raise_for_status()
    status, reason, _ = extract_status(response.text)
    real_key = next(
        (key for key in re.findall(r"(?<!\d)\d{44}(?!\d)", response.text) if key != artificial),
        "",
    )
    return status, reason, real_key


def _consult_logged(
    session: requests.Session,
    cfg: dict[str, Any],
    number: int,
    aamm: str,
    run_id: str,
    empresa_id: str,
    circuit: TransportCircuitBreaker | None = None,
    transport: OutboundTransportManager | None = None,
) -> tuple[str, str, str]:
    started = time.perf_counter()
    http_status: int | None = None
    categoria = "UNKNOWN"
    error_type = ""
    failover = False
    route = transport.current() if transport else None
    try:
        if circuit and not circuit.allow_call():
            categoria = "circuit_open"
            return "", "circuit_open", ""
        status, reason, real_key = _consult(session, cfg, number, aamm, {
            "run_id": run_id, "empresa_id": empresa_id, "aamm": aamm,
            "nnf": number, "chave": access_key(cfg, number, aamm), "tentativa": 1,
            "outbound_id": route.outbound_id if route else "direct",
        })
        categoria = status or "UNKNOWN"
        if circuit:
            circuit.note_success()
        if transport:
            transport.note_success()
        return status, reason, real_key
    except requests.exceptions.ProxyError as exc:
        error_type = type(exc).__name__
        categoria = "proxy"
        failover = bool(transport and transport.note_infrastructure_failure())
        if failover and transport:
            transport.apply(session)
            route = transport.current()
        if circuit:
            circuit.note_transport_failure()
        return "", "proxy", ""
    except requests.HTTPError as exc:
        error_type = type(exc).__name__
        http_status = exc.response.status_code if exc.response is not None else None
        categoria = "REMOTE_5XX" if http_status and http_status >= 500 else "HTTP"
        if circuit and http_status and http_status >= 500:
            circuit.note_transport_failure()
        raise
    except requests.Timeout as exc:
        error_type = type(exc).__name__
        categoria = "TIMEOUT"
        if circuit:
            circuit.note_transport_failure()
        raise
    except requests.RequestException as exc:
        error_type = type(exc).__name__
        categoria = "NETWORK_ERROR"
        if circuit:
            circuit.note_transport_failure()
        raise
    finally:
        log_attempt(
            run_id=run_id,
            empresa_id=empresa_id,
            aamm=aamm,
            nnf=number,
            chave=access_key(cfg, number, aamm),
            etapa="consulta",
            tentativa=1,
            duracao_ms=int((time.perf_counter() - started) * 1000),
            http=http_status,
            categoria=categoria,
            detalhe=error_type,
            retry=failover,
            cstat=categoria if categoria.isdigit() else "",
            circuit_state=circuit.state if circuit else "",
            proxy_enabled=bool(transport and transport.enabled),
            outbound_id=route.outbound_id if route else "direct",
            outbound_health=route.health if route else "healthy",
            failover=failover,
        )


def _new_svrs_session(
    cert_path: Path,
    key_path: Path,
    verify_path: str,
    transport: OutboundTransportManager | None = None,
) -> requests.Session:
    """Session com certificado cliente e verify no bundle. Proxy só se estiver ligado."""
    session = requests.Session()
    session.cert = (str(cert_path), str(key_path))
    session.verify = verify_path
    if transport is not None:
        transport.apply(session)
    return session


def _consult_one(cert_path: Path, key_path: Path, verify_path: str, cfg: dict[str, Any], number: int, aamm: str) -> tuple[int, str, str, str]:
    session = _new_svrs_session(cert_path, key_path, verify_path)
    try:
        status, reason, real_key = _consult(session, cfg, number, aamm)
        return number, status, reason, real_key
    finally:
        session.close()


def _portal_http_failure(response: requests.Response) -> tuple[str, str] | None:
    if response.status_code < 400:
        return None
    kind = classify_portal_body(response.status_code, response.text)
    if kind == "rate_limit" or response.status_code == 429:
        return "rate_limit", download_failure_message("rate_limit", response.status_code)
    if kind == "unavailable":
        return "unavailable", download_failure_message("unavailable")
    return "http", download_failure_message("http", response.status_code)


def _download_one(
    cert_path: Path,
    key_path: Path,
    verify_path: str,
    item: dict[str, Any],
    limiter: SvrsRateLimiter | None = None,
    run_id: str = "",
    empresa_id: str = "",
    notify=None,
    session: requests.Session | None = None,
    transport: OutboundTransportManager | None = None,
    circuit: TransportCircuitBreaker | None = None,
) -> tuple[dict[str, Any], str | None, str, str]:
    """Até 3 tentativas. Limite do portal entra em cooldown. Página sem XML repete a chave.

    O limitador espaça cada par GET+POST. GET e POST da mesma chave não esperam.
    verify permanece no bundle passado em verify_path.
    """
    owns_session = session is None
    active_session = session or _new_svrs_session(cert_path, key_path, verify_path, transport)
    interval = clamp_download_interval(int(item.get("_download_interval_seconds", SVRS_INTERVAL_MIN_SECONDS)))
    active = limiter or SvrsRateLimiter(soap_seconds=0.1, download_seconds=interval)
    breaker = circuit
    route = transport.current() if transport else None
    try:
        kind = "no_xml"
        message = download_failure_message("no_xml")
        for attempt in range(sefaz_max_retries()):
            if breaker and not breaker.allow_call():
                kind = "circuit_open"
                message = download_failure_message("circuit_open")
                log_attempt(
                    run_id=run_id,
                    empresa_id=empresa_id,
                    aamm=str(item.get("AAMM") or ""),
                    nnf=int(item["nNF"]) if item.get("nNF") is not None else None,
                    chave=str(item.get("chave_real") or ""),
                    etapa="download",
                    tentativa=attempt + 1,
                    duracao_ms=0,
                    http=None,
                    categoria=kind,
                    retry=False,
                    circuit_state=breaker.state,
                    proxy_enabled=bool(transport and transport.enabled),
                    outbound_id=route.outbound_id if route else "direct",
                    outbound_health=route.health if route else "healthy",
                )
                return item, None, message, kind
            if attempt and kind == "no_xml":
                active.arm_same_key_retry(PORTAL_EMPTY_RETRY_SECONDS)
                if notify:
                    notify(attempt)
            elif attempt and failure_policy(kind) == "backoff":
                delay = transient_backoff_seconds(attempt - 1)
                active.arm_same_key_retry(delay)
                if notify:
                    notify(attempt)
            slot = active.begin_download()
            if slot == "skip":
                active.note_remote_limit()
                kind = "rate_limit"
                message = download_failure_message("rate_limit")
                return item, None, message, kind
            if notify and attempt == 0:
                notify(attempt)
            started = time.perf_counter()
            http_status: int | None = None
            error_type = ""
            failover = False
            try:
                xml, kind, message, http_status = _download(active_session, item["chave_real"], {
                    "run_id": run_id, "empresa_id": empresa_id,
                    "aamm": str(item.get("AAMM") or ""), "nnf": item.get("nNF"),
                    "chave": str(item["chave_real"]), "tentativa": attempt + 1,
                    "outbound_id": route.outbound_id if route else "direct",
                })
                if xml:
                    kind = "ok"
            except requests.Timeout as exc:
                error_type = type(exc).__name__
                xml, kind, message = None, "timeout", download_failure_message("timeout")
                if breaker:
                    breaker.note_transport_failure()
            except requests.exceptions.ProxyError as exc:
                error_type = type(exc).__name__
                xml, kind, message = None, "proxy", download_failure_message("proxy")
                failover = bool(transport and transport.note_infrastructure_failure())
                if failover and transport:
                    transport.apply(active_session)
                    route = transport.current()
                if breaker:
                    breaker.note_transport_failure()
            except requests.RequestException as exc:
                error_type = type(exc).__name__
                text = str(exc)
                if "429" in text:
                    xml, kind, message = None, "rate_limit", download_failure_message("rate_limit")
                else:
                    xml, kind, message = None, "http", download_failure_message("http")
                    if breaker:
                        breaker.note_transport_failure()
            if kind == "ok":
                if breaker:
                    breaker.note_success()
                active.note_download_ok()
                if transport:
                    transport.note_success()
            elif kind == "rate_limit":
                active.note_remote_limit()
                if transport:
                    transport.note_remote_limit()
            elif kind == "http" and breaker and http_status is not None and http_status >= 500:
                breaker.note_transport_failure()
            proxima = ""
            if kind == "rate_limit":
                proxima = (datetime.now(timezone.utc) + timedelta(seconds=active.cooldown_seconds)).isoformat()
            log_attempt(
                run_id=run_id,
                empresa_id=empresa_id,
                aamm=str(item.get("AAMM") or ""),
                nnf=int(item["nNF"]) if item.get("nNF") is not None else None,
                chave=str(item.get("chave_real") or ""),
                etapa="download",
                tentativa=attempt + 1,
                duracao_ms=int((time.perf_counter() - started) * 1000),
                http=http_status,
                categoria=kind,
                detalhe=error_type,
                retry=(
                    download_retries_immediately(kind, attempt)
                    or download_retries_same_key(kind, attempt)
                    or (kind == "proxy" and failover)
                ),
                proxima_tentativa=proxima,
                backoff=str(transient_backoff_seconds(attempt, 0)) if failure_policy(kind) == "backoff" else "",
                cooldown=active.download_state() if kind == "rate_limit" else "",
                circuit_state=breaker.state if breaker else "",
                proxy_enabled=bool(transport and transport.enabled),
                outbound_id=route.outbound_id if route else "direct",
                outbound_health=route.health if route else "healthy",
                failover=failover,
            )
            if xml:
                return item, xml, "", "ok"
            if kind == "rate_limit":
                return item, None, message, kind
            if kind == "proxy" and failover:
                continue
            if download_retries_immediately(kind, attempt) or download_retries_same_key(kind, attempt):
                continue
            return item, None, message, kind
        return item, None, message, kind
    finally:
        if owns_session:
            active_session.close()


def _download(session: requests.Session, key: str,
              log_context: dict[str, Any] | None = None) -> tuple[str | None, str, str, int | None]:
    context = log_context or {"chave": key, "tentativa": 1}
    started = time.perf_counter()
    get_response = session.get(
        SVRS_DOWNLOAD_GET_URL,
        params={"OrigemSite": "2", "Ambiente": "1", "ChaveAcessoDfe": key},
        headers={"User-Agent": "Mozilla/5.0", "Accept": "text/html,application/xml;q=0.9,*/*;q=0.8"},
        timeout=REQUEST_TIMEOUT,
    )
    _log_remote_response(get_response, "portal_get", started, context)
    blocked = _portal_http_failure(get_response)
    if blocked:
        return None, blocked[0], blocked[1], get_response.status_code
    hidden: dict[str, str] = {}
    for tag in re.findall(r"<input\b[^>]*>", get_response.text, re.I):
        if not re.search(r'\btype=["\']?hidden["\']?', tag, re.I):
            continue
        name = re.search(r'\bname=["\']([^"\']+)["\']', tag, re.I)
        value = re.search(r'\bvalue=["\']([^"\']*)["\']', tag, re.I)
        if name:
            hidden[name.group(1)] = value.group(1) if value else ""
    hidden.update({"sistema": "Nfce", "OrigemSite": "SiteSefaz", "Ambiente": "1", "ChaveAcessoDfe": key})
    started = time.perf_counter()
    post_response = session.post(
        SVRS_DOWNLOAD_POST_URL,
        data=hidden,
        headers={
            "User-Agent": "Mozilla/5.0",
            "Accept": "text/html,application/xml;q=0.9,*/*;q=0.8",
            "Content-Type": "application/x-www-form-urlencoded",
            "Origin": "https://dfe-portal.svrs.rs.gov.br",
            "Referer": get_response.url,
        },
        timeout=REQUEST_TIMEOUT,
    )
    _log_remote_response(post_response, "portal_post", started, context)
    blocked = _portal_http_failure(post_response)
    if blocked:
        return None, blocked[0], blocked[1], post_response.status_code
    xml = extract_downloaded_xml(post_response.text)
    if xml:
        return xml, "ok", "", post_response.status_code
    kind = classify_portal_body(post_response.status_code, post_response.text)
    return None, kind, download_failure_message(kind, post_response.status_code), post_response.status_code


def _live_jobs_locked() -> list[Job]:
    """Job sem atualização há 8 min não ocupa vaga. O download real avisa a cada XML."""
    now = time.time()
    live: list[Job] = []
    for item in _jobs.values():
        if item.status not in {"queued", "running"}:
            continue
        if now - float(item.updated_at) > 8 * 60:
            item.status = "failed"
            item.error = "Sem sinal do worker; a vaga foi liberada."
            item.message = "Vaga liberada"
            item.updated_at = now
            continue
        live.append(item)
    return live


def run_job(job: Job, seed_bytes: bytes, pfx_bytes: bytes, password: str, options: dict[str, Any]) -> None:
    if job.status == "failed":
        return
    cert_path: Path | None = None
    key_path: Path | None = None
    session: requests.Session | None = None
    try:
        _update(job, status="running", message="Validando XML e certificado", progress=1)
        cfg = parse_seed_xml(seed_bytes)
        if aamm_order(cfg["aamm"]) > aamm_order(current_aamm()):
            raise ValueError("A competência do XML semente está no futuro.")
        cert_path, key_path, cert_cnpj = _certificate_files(pfx_bytes, password, job.directory)
        if certificate_mismatch_stops(cert_cnpj, cfg["cnpj"]):
            raise ValueError("O CNPJ do certificado é diferente do emitente do XML.")

        verify_path = svrs_ca_bundle()
        transport = shared_outbound_transport()
        circuit = shared_transport_circuit()
        session = _new_svrs_session(cert_path, key_path, verify_path, transport)
        saved_keys = {str(key) for key in (options.get("saved_keys") or []) if str(key)}
        records: list[dict[str, Any]] = []
        pending_items = list(options.get("pending_items") or [])
        interval_seconds = clamp_download_interval(
            int(options.get("download_interval_seconds", SVRS_INTERVAL_MIN_SECONDS))
        )
        pending_only = bool(options.get("pending_only"))
        paused_for_svrs = False
        limiter = shared_rate_limiter(
            float(options.get("query_interval_ms", 100)) / 1000,
            interval_seconds,
        )
        xml_dir = job.directory / "xml"
        xml_dir.mkdir(exist_ok=True)

        # Reprocessa primeiro a fila persistente enviada pela Edge Function.
        # Pendências NÃO contam como "encontradas" da varredura e NÃO avançam o cursor.
        # Processa todas as pendências prontas. Só uma resposta de contenção da
        # SVRS pausa a execução; não existe mais corte artificial em 6 notas.
        pending_saved = 0
        pending_failed = 0
        if pending_items:
            pending_queue = list(pending_items)
            pending_total = len(pending_queue)
            _update(
                job,
                message=f"Recuperando {pending_total} pendência(s) até esgotar a fila",
                progress=2,
            )
            _callback(
                job,
                "progress",
                consulted=0,
                found=0,
                downloaded=0,
                pending_total=pending_total,
                mode="pending_recovery",
                message=f"Recuperando pendências: 0/{pending_total}",
            )

            for pending_index, pending in enumerate(pending_queue, 1):
                item = {
                    "AAMM": str(pending["aamm"]),
                    "nNF": int(pending["nnf"]),
                    "cStat": "PENDENTE",
                    "xMotivo": "Reprocessamento de pendência",
                    "chave_real": str(pending["chave"]),
                    "_download_interval_seconds": interval_seconds,
                }

                def notify_attempt(attempt: int) -> None:
                    espera = PORTAL_EMPTY_RETRY_SECONDS if attempt else interval_seconds
                    _callback(
                        job,
                        "progress",
                        consulted=0,
                        found=0,
                        downloaded=pending_saved,
                        pending_total=pending_total,
                        pending_failed=pending_failed,
                        mode="pending_recovery",
                        message=(
                            f"Aguardando {format_wait(espera)} · pendência "
                            f"{pending_index}/{pending_total} · tentativa {attempt + 1}"
                        ),
                    )

                item, xml, last_download_error, failure_kind = _download_one(
                    cert_path, key_path, verify_path, item, limiter,
                    run_id=job.external_run_id or "",
                    empresa_id=job.empresa_id,
                    notify=notify_attempt,
                    session=session,
                    transport=transport,
                    circuit=circuit,
                )

                if xml:
                    full_xml = '<?xml version="1.0" encoding="UTF-8"?>\n' + xml
                    _callback(
                        job,
                        "file",
                        key=item["chave_real"],
                        aamm=item["AAMM"],
                        number=item["nNF"],
                        emitted_at=_xml_emission_date(xml),
                        advance_cursor=False,
                        consulted=0,
                        found=0,
                        item_index=pending_index,
                        mode="pending_recovery",
                        xml_base64=base64.b64encode(
                            full_xml.encode("utf-8")
                        ).decode("ascii"),
                    )
                    (xml_dir / f'{item["chave_real"]}-procNFe.xml').write_text(
                        full_xml, encoding="utf-8"
                    )
                    pending_saved += 1
                    saved_keys.add(str(item["chave_real"]))
                else:
                    failure_reason = last_download_error or download_failure_message(failure_kind)
                    pending_failed += 1
                    _callback(
                        job,
                        "download_failed",
                        key=item["chave_real"],
                        aamm=item["AAMM"],
                        number=item["nNF"],
                        error=failure_reason,
                        error_kind=failure_kind,
                        consulted=0,
                        found=0,
                        item_index=pending_index,
                        mode="pending_recovery",
                    )

                message = (
                    f"Recuperando pendências: {pending_index}/{pending_total} · "
                    f"{pending_saved} salvas · {pending_failed} falhas"
                )
                _update(
                    job,
                    downloaded=pending_saved,
                    message=message,
                    progress=min(60, 2 + int(pending_index / max(1, pending_total) * 58)),
                )
                _callback(
                    job,
                    "progress",
                    consulted=0,
                    found=0,
                    downloaded=pending_saved,
                    pending_total=pending_total,
                    pending_failed=pending_failed,
                    mode="pending_recovery",
                    message=message,
                )

                if failure_kind in {"rate_limit", "circuit_open", "proxy"}:
                    paused_for_svrs = True
                    break

                if pending_index < pending_total and interval_seconds and not paused_for_svrs:
                    wait_message = (
                        f"Aguardando {format_wait(interval_seconds)} · pendência "
                        f"{pending_index}/{pending_total}"
                    )
                    _update(job, message=wait_message)
                    _callback(
                        job,
                        "progress",
                        consulted=0,
                        found=0,
                        downloaded=pending_saved,
                        pending_total=pending_total,
                        pending_failed=pending_failed,
                        mode="pending_recovery",
                        message=wait_message,
                    )

            _callback(
                job,
                "progress",
                consulted=0,
                found=0,
                downloaded=pending_saved,
                pending_total=pending_total,
                pending_failed=pending_failed,
                mode="pending_recovery",
                message=(
                    (
                        f"Pausa por limite da SVRS · {pending_saved} salvas · "
                        "o restante segue no próximo lote"
                    )
                    if paused_for_svrs
                    else (
                        f"Pendências processadas: {pending_saved} salvas · "
                        f"{pending_failed} sem XML"
                    )
                ),
            )

            if pending_only or paused_for_svrs:
                _update(
                    job,
                    status="completed",
                    message=(
                        "Pausa por limite da SVRS"
                        if paused_for_svrs
                        else "Todas as pendências prontas foram processadas"
                    ),
                    progress=100,
                    downloaded=pending_saved,
                )
                _callback(
                    job,
                    "completed",
                    consulted=0,
                    found=0,
                    downloaded=pending_saved,
                    pending_saved=pending_saved,
                    pending_failed=pending_failed,
                    pause_for_svrs=paused_for_svrs,
                    include_cursor=False,
                    message=(
                        (
                            f"Pausa por limite da SVRS · {pending_saved} salvas. "
                            "As demais NFC-e continuam na fila e seguem em 1 min."
                        )
                        if paused_for_svrs
                        else (
                            f"Pendências processadas: {pending_saved} salvas · "
                            f"{pending_failed} sem XML"
                        )
                    ),
                )
                return

        if pending_only:
            _update(job, status="completed", message="Pendências aguardando a próxima tentativa", progress=100, downloaded=pending_saved)
            _callback(
                job,
                "completed",
                consulted=0,
                found=0,
                downloaded=pending_saved,
                pending_saved=pending_saved,
                pending_failed=pending_failed,
                pause_for_svrs=paused_for_svrs,
                include_cursor=False,
                message="Nenhuma pendência pronta neste momento. A fila segue quando a próxima tentativa chegar.",
            )
            return

        found: list[dict[str, Any]] = []
        current_month = str(options.get("start_aamm") or cfg["aamm"])
        start_number = int(options.get("start_number") if options.get("start_number") is not None else cfg["number"])
        number = start_number + 1
        consecutive_217, gap_start, last_probe = 0, None, number - 1
        probed_this_gap = False
        max_numbers = options["max_numbers"]
        last_progress_at = 0.0
        # Cursor já gravado. Só anda depois de ausência (217) ou de ack HTTP 200 da chave.
        safe_aamm = current_month
        safe_nnf = start_number

        def acknowledge(aamm: str, n_nf: int, status: str, real_key: str) -> bool:
            """Grava a chave na fila antes de o chamador mover o cursor. hold/falha = False."""
            artificial = access_key(cfg, n_nf, aamm)
            action, found_key = discovery_action(status, artificial, real_key)
            if action == "absent":
                return True
            if action != "found":
                return False
            _callback(
                job, "discovered",
                key=found_key, aamm=aamm, number=n_nf,
                consulted=len(records), found=len(found) + 1,
            )
            found.append({
                "AAMM": aamm, "nNF": n_nf, "cStat": status,
                "xMotivo": "", "chave_real": found_key, "download_status": "NA_FILA",
            })
            return True

        halt_reason: str | None = None

        def download_found(aamm: str, n_nf: int, found_key: str) -> None:
            """Baixa toda chave encontrada; só pausa se a SVRS pedir contenção."""
            nonlocal halt_reason, pending_saved, pending_failed, paused_for_svrs

            def do_download() -> str:
                nonlocal pending_saved, pending_failed, paused_for_svrs
                item = {
                    "AAMM": aamm,
                    "nNF": n_nf,
                    "chave_real": found_key,
                    "_download_interval_seconds": interval_seconds,
                }
                _item, xml, error, kind = _download_one(
                    cert_path,
                    key_path,
                    verify_path,
                    item,
                    limiter,
                    run_id=job.external_run_id or "",
                    empresa_id=job.empresa_id,
                    session=session,
                    transport=transport,
                    circuit=circuit,
                )
                if xml:
                    full_xml = '<?xml version="1.0" encoding="UTF-8"?>\n' + xml
                    _callback(
                        job,
                        "file",
                        key=found_key,
                        aamm=aamm,
                        number=n_nf,
                        emitted_at=_xml_emission_date(xml),
                        advance_cursor=False,
                        consulted=len(records),
                        found=len(found),
                        mode="discovery",
                        xml_base64=base64.b64encode(full_xml.encode("utf-8")).decode("ascii"),
                    )
                    (xml_dir / f"{found_key}-procNFe.xml").write_text(full_xml, encoding="utf-8")
                    pending_saved += 1
                    saved_keys.add(found_key)
                    return "ok"
                pending_failed += 1
                _callback(
                    job,
                    "download_failed",
                    key=found_key,
                    aamm=aamm,
                    number=n_nf,
                    error=error or download_failure_message(kind),
                    error_kind=kind,
                    consulted=len(records),
                    found=len(found),
                    mode="discovery",
                )
                if kind in {"rate_limit", "circuit_open", "proxy"}:
                    paused_for_svrs = True
                    return "pause"
                return "failed"

            outcome = handle_discovered_key(
                xml_already_saved=found_key in saved_keys,
                download=do_download,
            )
            if outcome == "pause":
                halt_reason = "hold"
                paused_for_svrs = True

        def report_progress(message: str, force: bool = False) -> None:
            nonlocal last_progress_at
            now = time.time()
            if not force and now - last_progress_at < 8:
                return
            last_progress_at = now
            _update(
                job,
                message=message,
                consulted=len(records),
                found=len(found),
                current_number=number,
                current_competence=current_month,
                progress=min(65, 2 + int(len(records) / max(1, max_numbers) * 63)),
            )
            _callback(
                job, "progress",
                consulted=len(records), found=len(found), downloaded=job.downloaded,
                message=message, current_number=number, current_competence=current_month,
                mode="discovery",
            )

        report_progress(f"Consultando {current_month} a partir da nNF {number}", force=True)
        scan_reason = "cap"
        while len(records) < max_numbers:
            _update(
                job,
                message=f"Consultando {current_month} nNF {number}",
                current_number=number,
                current_competence=current_month,
                progress=min(65, 2 + int(len(records) / max_numbers * 63)),
            )
            limiter.wait("soap")
            status, reason, real_key = _consult_logged(
                session, cfg, number, current_month,
                job.external_run_id or "", job.empresa_id,
                circuit, transport,
            )
            report_progress(f"Consultando {current_month} nNF {number}")
            record = {"AAMM": current_month, "nNF": number, "cStat": status, "xMotivo": reason, "chave_real": real_key}
            records.append(record)
            artificial = access_key(cfg, number, current_month)
            try:
                acked = acknowledge(current_month, number, status, real_key)
            except Exception:
                acked = False
            safe_aamm, safe_nnf, action, _found_key = apply_discovery_step(
                safe_aamm, safe_nnf, current_month, number, status,
                artificial, real_key, acked,
            )
            if action == "found" and _found_key:
                record["chave_real"] = _found_key
                download_found(current_month, number, _found_key)
            if halt_reason:
                scan_reason = halt_reason
                break
            if action == "hold" or not acked:
                scan_reason = "hold" if action == "hold" else "ack"
                break
            if action != "absent":
                consecutive_217, gap_start, last_probe = 0, None, number
                probed_this_gap = False
                number += 1
                continue
            gap_start = number if gap_start is None else gap_start
            consecutive_217 += 1
            if consecutive_217 >= options["month_trigger"] and not probed_this_gap:
                probed_this_gap = True
                following = next_aamm(current_month)
                if aamm_order(following) <= aamm_order(current_aamm()):
                    probe_start = max(gap_start, last_probe + 1)
                    probe_end = probe_start + options["month_window"] - 1
                    switched = False
                    for probe in range(probe_start, probe_end + 1):
                        if len(records) >= max_numbers:
                            break
                        limiter.wait("soap")
                        status2, reason2, real2 = _consult_logged(
                            session, cfg, probe, following,
                            job.external_run_id or "", job.empresa_id,
                            circuit, transport,
                        )
                        probe_record = {"AAMM": following, "nNF": probe, "cStat": status2, "xMotivo": reason2, "chave_real": real2}
                        records.append(probe_record)
                        probe_key_artificial = access_key(cfg, probe, following)
                        action2, _ignored = discovery_action(status2, probe_key_artificial, real2)
                        if action2 == "absent":
                            continue
                        if action2 == "hold":
                            break
                        try:
                            probe_acked = acknowledge(following, probe, status2, real2)
                        except Exception:
                            probe_acked = False
                        safe_aamm, safe_nnf, action2, _probe_key = apply_discovery_step(
                            safe_aamm, safe_nnf, following, probe, status2,
                            probe_key_artificial, real2, probe_acked,
                        )
                        if not probe_acked:
                            break
                        if action2 == "found" and _probe_key:
                            download_found(following, probe, _probe_key)
                        if halt_reason:
                            break
                        if action2 == "found":
                            current_month, number = following, probe + 1
                            consecutive_217, gap_start, last_probe, switched = 0, None, probe, True
                            probed_this_gap = False
                            break
                    last_probe = probe_end
                    if halt_reason:
                        scan_reason = halt_reason
                        break
                    if switched:
                        continue
            if consecutive_217 >= options["stop_gap"]:
                scan_reason = "gap"
                break
            number += 1

        _update(
            job, consulted=len(records), found=len(found),
            message=(
                f"{pending_saved} XML salvos nesta execução · {len(found)} chave(s) encontradas"
                if pending_saved
                else f"{len(found)} chave(s) encontradas. As que ficaram sem vaga seguem na fila."
            ),
            progress=68,
        )
        _callback(
            job, "progress",
            consulted=len(records), found=len(found), downloaded=pending_saved,
            message=(
                f"{pending_saved} XML salvos nesta execução · {len(found)} chave(s) encontradas"
                if pending_saved
                else f"{len(found)} chave(s) encontradas. As que ficaram sem vaga seguem na fila."
            ),
            mode="discovery",
        )
        downloaded = pending_saved
        summary = io.StringIO()
        writer = csv.DictWriter(summary, fieldnames=["AAMM", "nNF", "cStat", "xMotivo", "chave_real", "download_status"], delimiter=";")
        writer.writeheader()
        for item in records:
            item.setdefault("download_status", "")
            writer.writerow(item)
        zip_path = job.directory / f'nfce_{cfg["cnpj"]}_{int(time.time())}.zip'
        with zipfile.ZipFile(zip_path, "w", zipfile.ZIP_DEFLATED) as archive:
            archive.writestr("resumo.csv", summary.getvalue().encode("utf-8-sig"))
            for xml_path in xml_dir.glob("*.xml"):
                archive.write(xml_path, arcname=f"XML/{xml_path.name}")
        if scan_reason in {"hold", "ack"}:
            paused_for_svrs = True
        completion_message = "Processamento concluído"
        if paused_for_svrs:
            completion_message = (
                f"Pausa por limite da SVRS · {downloaded} XML salvos. "
                "O restante continua na fila e segue em 1 min."
            )
        elif pending_saved or pending_failed:
            completion_message = (
                f"Concluído · pendências {pending_saved} salvas/"
                f"{pending_failed} falhas · varredura {len(found)} na fila"
            )
        _update(
            job,
            status="completed",
            message=completion_message,
            progress=100,
            consulted=len(records),
            found=len(found),
            downloaded=downloaded,
            zip_path=zip_path,
        )
        _callback(
            job, "completed", consulted=len(records), found=len(found), downloaded=downloaded,
            cursor_aamm=safe_aamm, cursor_nnf=safe_nnf, include_cursor=True,
            scan_complete=discovery_scan_complete(scan_reason, len(found)),
            pending_saved=pending_saved, pending_failed=pending_failed,
            pause_for_svrs=paused_for_svrs,
            message=completion_message,
        )
    except Exception as exc:
        _update(job, status="failed", message="Falha no processamento", error=str(exc), progress=100)
        try:
            _callback(job, "failed", error=str(exc))
        except Exception:
            pass
    finally:
        password = ""  # reduz o tempo de vida da referência ao segredo
        for path in (cert_path, key_path):
            if path:
                path.unlink(missing_ok=True)
        if session is not None:
            session.close()


def _cleanup_expired() -> None:
    cutoff = time.time() - JOB_TTL_SECONDS
    expired: list[Job] = []
    with _jobs_lock:
        for job_id, job in list(_jobs.items()):
            if job.updated_at < cutoff and job.status in {"completed", "failed"}:
                expired.append(_jobs.pop(job_id))
    for job in expired:
        shutil.rmtree(job.directory, ignore_errors=True)


def _bearer_token(authorization: str | None) -> str:
    if not authorization or not authorization.lower().startswith("bearer "):
        raise HTTPException(status_code=401, detail="Autenticação necessária.")
    return authorization.split(" ", 1)[1].strip()


def _authenticate(authorization: str | None) -> str:
    token = _bearer_token(authorization)
    digest = hashlib.sha256(token.encode()).hexdigest()
    cached = _auth_cache.get(digest)
    if cached and cached[0] > time.time():
        return cached[1]
    supabase_url = os.getenv("SUPABASE_URL", "https://vqhtbyiecsxxprikpnus.supabase.co").rstrip("/")
    # A chave anon é pública por definição e já está presente no cliente web.
    anon_key = os.getenv(
        "SUPABASE_ANON_KEY",
        "eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9.eyJpc3MiOiJzdXBhYmFzZSIsInJlZiI6InZxaHRieWllY3N4eHByaWtwbnVzIiwicm9sZSI6ImFub24iLCJpYXQiOjE3NjYwNjU3OTUsImV4cCI6MjA4MTY0MTc5NX0.aOvciVxs4NjCpHEYZXQziJy-0PQpcy4h-E2CbMZWKJ8",
    )
    if not supabase_url or not anon_key:
        if os.getenv("NFCE_ALLOW_UNAUTHENTICATED", "").lower() == "true":
            return digest
        raise HTTPException(status_code=503, detail="Autenticação do worker não configurada.")
    try:
        response = requests.get(
            f"{supabase_url}/auth/v1/user",
            headers={"Authorization": f"Bearer {token}", "apikey": anon_key},
            timeout=10,
        )
    except requests.RequestException as exc:
        raise HTTPException(status_code=503, detail="Não foi possível validar a sessão.") from exc
    if response.status_code != 200:
        raise HTTPException(status_code=401, detail="Sessão inválida ou expirada.")
    user_id = str(response.json().get("id") or "")
    if not user_id:
        raise HTTPException(status_code=401, detail="Sessão inválida.")
    try:
        permission_response = requests.post(
            f"{supabase_url}/rest/v1/rpc/user_has_module_access",
            headers={
                "Authorization": f"Bearer {token}",
                "apikey": anon_key,
                "Content-Type": "application/json",
            },
            json={"_module_name": "downloads_xml"},
            timeout=10,
        )
    except requests.RequestException as exc:
        raise HTTPException(status_code=503, detail="Não foi possível validar a permissão.") from exc
    if permission_response.status_code != 200:
        raise HTTPException(status_code=503, detail="Falha ao validar a permissão do módulo.")
    if permission_response.json() is not True:
        raise HTTPException(status_code=403, detail="Sem permissão para Downloads XML.")
    _auth_cache[digest] = (time.time() + 300, user_id)
    return user_id


def _validate_internal_run(run_id: str, token: str) -> None:
    supabase_url = os.getenv("SUPABASE_URL", "https://vqhtbyiecsxxprikpnus.supabase.co").rstrip("/")
    anon_key = os.getenv(
        "SUPABASE_ANON_KEY",
        "eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9.eyJpc3MiOiJzdXBhYmFzZSIsInJlZiI6InZxaHRieWllY3N4eHByaWtwbnVzIiwicm9sZSI6ImFub24iLCJpYXQiOjE3NjYwNjU3OTUsImV4cCI6MjA4MTY0MTc5NX0.aOvciVxs4NjCpHEYZXQziJy-0PQpcy4h-E2CbMZWKJ8",
    )
    try:
        response = requests.post(
            f"{supabase_url}/rest/v1/rpc/claim_nfce_download_run",
            headers={"apikey": anon_key, "Authorization": f"Bearer {anon_key}", "Content-Type": "application/json"},
            json={"p_run_id": run_id, "p_token": token}, timeout=10,
        )
    except requests.RequestException as exc:
        raise HTTPException(status_code=503, detail="Não foi possível validar o job persistente.") from exc
    if response.status_code != 200 or response.json() is not True:
        raise HTTPException(status_code=401, detail="Job persistente inválido ou já utilizado.")


def _owned_job(job_id: str, owner_id: str) -> Job:
    with _jobs_lock:
        job = _jobs.get(job_id)
    if not job or job.owner_id != owner_id:
        raise HTTPException(status_code=404, detail="Processamento não encontrado.")
    return job


@router.post("/internal", status_code=202)
async def create_internal_job(
    run_id: str = Form(...),
    run_token: str = Form(...),
    xml_semente: UploadFile = File(...),
    certificado: UploadFile = File(...),
    senha: str = Form(...),
    inicio_aamm: str = Form(...),
    inicio_nnf: int = Form(...),
    data_referencia: str = Form(...),
    pendentes_json: str = Form("[]"),
    intervalo_download_segundos: int = Form(60),
    somente_pendentes: str = Form("false"),
    empresa_id: str = Form(""),
    organizacao_id: str = Form(""),
) -> dict[str, Any]:
    _cleanup_expired()
    _validate_internal_run(run_id, run_token)
    if not re.fullmatch(r"\d{4}", inicio_aamm) or inicio_nnf < 0:
        raise HTTPException(status_code=400, detail="Cursor NFC-e inválido.")
    if not re.fullmatch(r"\d{4}-\d{2}-\d{2}", data_referencia):
        raise HTTPException(status_code=400, detail="Data de referência inválida.")
    try:
        pending_items = json.loads(pendentes_json or "[]")
    except json.JSONDecodeError as exc:
        raise HTTPException(status_code=400, detail="pendentes_json inválido.") from exc
    if not isinstance(pending_items, list):
        raise HTTPException(status_code=400, detail="pendentes_json deve ser uma lista.")
    normalized_pending: list[dict[str, Any]] = []
    seen_pending: set[str] = set()
    for raw in pending_items:
        if not isinstance(raw, dict):
            raise HTTPException(status_code=400, detail="Item pendente inválido.")
        key = _digits(str(raw.get("chave") or ""))
        aamm = str(raw.get("aamm") or "")
        try:
            nnf = int(raw.get("nnf"))
        except (TypeError, ValueError) as exc:
            raise HTTPException(status_code=400, detail="nNF pendente inválida.") from exc
        if len(key) != 44 or not key.isdigit() or not re.fullmatch(r"\d{4}", aamm) or nnf < 0:
            raise HTTPException(status_code=400, detail="Metadados de pendência inválidos.")
        if key in seen_pending:
            continue
        seen_pending.add(key)
        normalized_pending.append({"chave": key, "aamm": aamm, "nnf": nnf})
    with _jobs_lock:
        active_jobs = _live_jobs_locked()
        org = organizacao_id.strip()
        if org and not re.fullmatch(r"[0-9a-fA-F-]{36}", org):
            org = ""
        if org and any(item.organizacao_id == org for item in active_jobs):
            raise HTTPException(status_code=429, detail=WORKER_BUSY_DETAIL)
        if len(active_jobs) >= MAX_QUEUED_JOBS:
            raise HTTPException(status_code=429, detail=WORKER_BUSY_DETAIL)
    seed_bytes = await xml_semente.read(MAX_UPLOAD_BYTES + 1)
    pfx_bytes = await certificado.read(MAX_UPLOAD_BYTES + 1)
    try:
        parse_seed_xml(seed_bytes)
    except ValueError as exc:
        raise HTTPException(status_code=400, detail=str(exc)) from exc
    if not pfx_bytes or len(pfx_bytes) > MAX_UPLOAD_BYTES:
        raise HTTPException(status_code=400, detail="Certificado ausente ou maior que o limite.")
    job_id = secrets.token_urlsafe(24)
    directory = WORK_ROOT / job_id
    directory.mkdir(mode=0o700)
    empresa = empresa_id.strip()
    if empresa and not re.fullmatch(r"[0-9a-fA-F-]{36}", empresa):
        empresa = ""
    job = Job(
        id=job_id, owner_id=f"run:{run_id}", directory=directory,
        callback_token=run_token, external_run_id=run_id, empresa_id=empresa,
        organizacao_id=org,
    )
    with _jobs_lock:
        active_now = [item for item in _jobs.values() if item.status in {"queued", "running"}]
        if org and any(item.organizacao_id == org for item in active_now):
            raise HTTPException(status_code=429, detail=WORKER_BUSY_DETAIL)
        if len(active_now) >= MAX_QUEUED_JOBS:
            raise HTTPException(status_code=429, detail=WORKER_BUSY_DETAIL)
        _jobs[job_id] = job
    if not (0 <= intervalo_download_segundos <= 300):
        raise HTTPException(status_code=400, detail="Intervalo de download inválido.")
    pending_only = str(somente_pendentes or "").strip().lower() in {"1", "true", "yes", "sim"}
    options: dict[str, Any] = {
        "month_trigger": 8, "month_window": 30, "stop_gap": 80,
        "max_numbers": min(1000, MAX_NUMERACOES),
        "query_interval_ms": int(os.getenv("NFCE_QUERY_INTERVAL_MS", "100")),
        "download_interval_seconds": clamp_download_interval(intervalo_download_segundos),
        "pending_only": pending_only,
        "start_aamm": inicio_aamm,
        "start_number": inicio_nnf, "reference_date": data_referencia,
        "pending_items": normalized_pending,
    }
    _executor.submit(run_job, job, seed_bytes, pfx_bytes, senha, options)
    return job.public()


@router.post("/internal/status")
async def internal_job_status(job_id: str = Form(""), run_id: str = Form("")) -> dict[str, Any]:
    with _jobs_lock:
        job = _jobs.get(job_id) if job_id else None
        if job is None and run_id:
            job = next((item for item in _jobs.values() if item.external_run_id == run_id), None)
    if job is None:
        return {"alive": False}
    return {"alive": True, **job.public()}


@router.post("", status_code=202)
async def create_job(
    xml_semente: UploadFile = File(...),
    certificado: UploadFile = File(...),
    senha: str = Form(...),
    gatilho_mes: int = Form(8),
    janela_mes: int = Form(30),
    lacuna_parada: int = Form(80),
    max_numeracoes: int = Form(1000),
    intervalo_consulta_ms: int = Form(100),
    intervalo_download_segundos: int = Form(60),
    authorization: str | None = Header(None),
) -> dict[str, Any]:
    _cleanup_expired()
    if os.getenv("NFCE_ENABLE_SVRS_DISCOVERY", "true").lower() != "true":
        raise HTTPException(
            status_code=503,
            detail="Busca NFC-e aguardando habilitação do piloto autorizado.",
        )
    owner_id = _authenticate(authorization)
    with _jobs_lock:
        active_jobs = _live_jobs_locked()
        if any(item.owner_id == owner_id for item in active_jobs):
            raise HTTPException(status_code=409, detail="Você já possui uma busca NFC-e em andamento.")
        if len(active_jobs) >= MAX_QUEUED_JOBS:
            raise HTTPException(status_code=429, detail=WORKER_BUSY_DETAIL)
    if not (2 <= gatilho_mes <= janela_mes < lacuna_parada <= 5000):
        raise HTTPException(status_code=400, detail="Parâmetros de lacuna inválidos.")
    if not (1 <= max_numeracoes <= MAX_NUMERACOES):
        raise HTTPException(status_code=400, detail=f"max_numeracoes deve estar entre 1 e {MAX_NUMERACOES}.")
    if not (0 <= intervalo_consulta_ms <= 10000 and 0 <= intervalo_download_segundos <= 300):
        raise HTTPException(status_code=400, detail="Intervalos fora dos limites permitidos.")
    seed_bytes, pfx_bytes = await xml_semente.read(MAX_UPLOAD_BYTES + 1), await certificado.read(MAX_UPLOAD_BYTES + 1)
    try:
        parse_seed_xml(seed_bytes)  # falha cedo, antes de ocupar a fila
    except ValueError as exc:
        raise HTTPException(status_code=400, detail=str(exc)) from exc
    if not pfx_bytes or len(pfx_bytes) > MAX_UPLOAD_BYTES:
        raise HTTPException(status_code=400, detail="Certificado ausente ou maior que o limite.")
    job_id = secrets.token_urlsafe(24)
    directory = WORK_ROOT / job_id
    directory.mkdir(mode=0o700)
    job = Job(id=job_id, owner_id=owner_id, directory=directory)
    with _jobs_lock:
        _jobs[job_id] = job
    options = {
        "month_trigger": gatilho_mes,
        "month_window": janela_mes,
        "stop_gap": lacuna_parada,
        "max_numbers": max_numeracoes,
        "query_interval_ms": intervalo_consulta_ms,
        "download_interval_seconds": clamp_download_interval(intervalo_download_segundos),
    }
    _executor.submit(run_job, job, seed_bytes, pfx_bytes, senha, options)
    return job.public()


@router.get("/{job_id}")
def get_job(job_id: str, authorization: str | None = Header(None)) -> dict[str, Any]:
    _cleanup_expired()
    return _owned_job(job_id, _authenticate(authorization)).public()


@router.get("/{job_id}/download")
def download_job(job_id: str, authorization: str | None = Header(None)) -> FileResponse:
    job = _owned_job(job_id, _authenticate(authorization))
    if job.status != "completed" or not job.zip_path or not job.zip_path.exists():
        raise HTTPException(status_code=409, detail="Arquivo ainda não disponível.")
    return FileResponse(job.zip_path, media_type="application/zip", filename=job.zip_path.name)
