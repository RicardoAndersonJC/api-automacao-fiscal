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
import os
import re
import secrets
import shutil
import tempfile
import threading
import time
import zipfile
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Any
from urllib.parse import urlparse
from xml.etree import ElementTree as ET

import requests
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
_executor = ThreadPoolExecutor(max_workers=max(1, int(os.getenv("NFCE_WORKERS", "2"))))
# Concorrência limitada: acelera I/O sem disparar centenas de requisições contra a SVRS.
QUERY_CONCURRENCY = max(1, min(8, int(os.getenv("NFCE_QUERY_CONCURRENCY", "4"))))
DOWNLOAD_CONCURRENCY = 1  # SVRS: download serial para respeitar o intervalo entre XMLs
# Lote curto de propósito: cada XML espera 90–120s. 18 × 90s cabe num ciclo
# sem estourar o tempo do worker nem disparar o limite da SVRS.
MAX_PENDING_PER_RUN = max(1, min(24, int(os.getenv("NFCE_MAX_PENDING_PER_RUN", "18"))))
# Piso de 1 min 30 s e teto de 2 min entre downloads. Abaixo disso a SVRS
# devolve página sem XML e o lote inteiro parece "falha".
SVRS_INTERVAL_MIN_SECONDS = 90
SVRS_INTERVAL_MAX_SECONDS = 120
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
    """Mantém o espaço entre downloads da SVRS entre 1 min 30 s e 2 min."""
    try:
        value = int(seconds)
    except (TypeError, ValueError):
        value = SVRS_INTERVAL_MIN_SECONDS
    return max(SVRS_INTERVAL_MIN_SECONDS, min(SVRS_INTERVAL_MAX_SECONDS, value))


_RATE_LIMIT_HINTS = (
    "muitas consultas",
    "muitas requisi",
    "excesso de requis",
    "too many",
    "captcha",
    "recaptcha",
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
    """Classifica a página da SVRS: rate_limit, unavailable ou no_xml."""
    if status_code in {429, 503}:
        return "rate_limit"
    sample = html.unescape(text or "")[:8000].lower()
    if any(hint in sample for hint in _RATE_LIMIT_HINTS):
        return "rate_limit"
    if any(hint in sample for hint in _UNAVAILABLE_HINTS):
        return "unavailable"
    return "no_xml"


def download_failure_message(kind: str, status_code: int = 0) -> str:
    if kind == "rate_limit":
        return (
            "Limite da SVRS: muitas consultas em sequência. "
            "Esta NFC-e continua na fila. O lote pausa 1 min 30 s para não tomar bloqueio."
        )
    if kind == "unavailable":
        return (
            "NFC-e sem XML no portal da SVRS (cancelada ou indisponível). "
            "Não é falha de conexão."
        )
    if kind == "timeout":
        return (
            "A SVRS não respondeu a tempo. "
            "A chave continua na fila e será tentada de novo com intervalo de 1 min 30 s."
        )
    if kind == "http":
        code = f" HTTP {status_code}" if status_code else ""
        return (
            f"A SVRS retornou erro{code}. "
            "A chave continua na fila para o próximo lote."
        )
    return (
        "O portal da SVRS respondeu, mas não trouxe o XML desta chave. "
        "Nova tentativa no próximo lote."
    )


def extract_downloaded_xml(text: str) -> str | None:
    cleaned = html.unescape(text.replace(r'\"', '"').replace(r"\/", "/"))
    for opening, closing in (("<nfeProc", "</nfeProc>"), ("<NFe", "</NFe>")):
        start, end = cleaned.find(opening), cleaned.rfind(closing)
        if start >= 0 and end > start:
            candidate = cleaned[start : end + len(closing)].strip()
            try:
                ET.fromstring(candidate)
                return candidate
            except ET.ParseError:
                continue
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
    for attempt in range(attempts):
        try:
            response = requests.post(
                f"{supabase_url}/functions/v1/nfce-download",
                json=request_body,
                headers=_anon_headers(),
                timeout=timeout,
            )
            if response.ok:
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
            time.sleep((0.5 * (2 ** attempt)) + (secrets.randbelow(250) / 1000))
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


def _consult(session: requests.Session, cfg: dict[str, Any], number: int, aamm: str) -> tuple[str, str, str]:
    artificial = access_key(cfg, number, aamm)
    response = session.post(
        SVRS_CONSULTA_URL,
        data=soap_request(artificial).encode("utf-8"),
        headers={"Content-Type": f'application/soap+xml; charset=utf-8; action="{SOAP_ACTION}"'},
        timeout=REQUEST_TIMEOUT,
    )
    response.raise_for_status()
    status, reason, _ = extract_status(response.text)
    real_key = next(
        (key for key in re.findall(r"(?<!\d)\d{44}(?!\d)", response.text) if key != artificial),
        "",
    )
    return status, reason, real_key


def _new_svrs_session(cert_path: Path, key_path: Path, verify_path: str) -> requests.Session:
    """Cria uma Session independente para uso seguro por uma thread."""
    session = requests.Session()
    session.cert = (str(cert_path), str(key_path))
    session.verify = verify_path
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
    if kind == "rate_limit" or response.status_code in {429, 503}:
        return "rate_limit", download_failure_message("rate_limit", response.status_code)
    if kind == "unavailable":
        return "unavailable", download_failure_message("unavailable")
    return "http", download_failure_message("http", response.status_code)


def _download_one(
    cert_path: Path, key_path: Path, verify_path: str, item: dict[str, Any]
) -> tuple[dict[str, Any], str | None, str, str]:
    """Uma tentativa por chave. Rede/timeout ganha uma segunda chance no mesmo intervalo.

    Limite da SVRS não é retentado na hora: repetir na sequência piora o bloqueio.
    """
    session = _new_svrs_session(cert_path, key_path, verify_path)
    interval = clamp_download_interval(int(item.get("_download_interval_seconds", SVRS_INTERVAL_MIN_SECONDS)))
    try:
        for attempt in range(2):
            try:
                xml, kind, message = _download(session, item["chave_real"])
                if xml:
                    return item, xml, "", "ok"
                if kind == "rate_limit" or attempt == 1 or kind in {"unavailable", "no_xml"}:
                    return item, None, message, kind
            except requests.Timeout:
                if attempt == 1:
                    return item, None, download_failure_message("timeout"), "timeout"
            except requests.RequestException as exc:
                if attempt == 1:
                    text = str(exc)
                    if "429" in text or "503" in text:
                        return item, None, download_failure_message("rate_limit"), "rate_limit"
                    return item, None, download_failure_message("http"), "http"
            time.sleep(interval)
        return item, None, download_failure_message("no_xml"), "no_xml"
    finally:
        session.close()


def _download(session: requests.Session, key: str) -> tuple[str | None, str, str]:
    get_response = session.get(
        SVRS_DOWNLOAD_GET_URL,
        params={"OrigemSite": "2", "Ambiente": "1", "ChaveAcessoDfe": key},
        headers={"User-Agent": "Mozilla/5.0", "Accept": "text/html,application/xml;q=0.9,*/*;q=0.8"},
        timeout=REQUEST_TIMEOUT,
    )
    blocked = _portal_http_failure(get_response)
    if blocked:
        return None, blocked[0], blocked[1]
    hidden: dict[str, str] = {}
    for tag in re.findall(r"<input\b[^>]*>", get_response.text, re.I):
        if not re.search(r'\btype=["\']?hidden["\']?', tag, re.I):
            continue
        name = re.search(r'\bname=["\']([^"\']+)["\']', tag, re.I)
        value = re.search(r'\bvalue=["\']([^"\']*)["\']', tag, re.I)
        if name:
            hidden[name.group(1)] = value.group(1) if value else ""
    hidden.update({"sistema": "Nfce", "OrigemSite": "SiteSefaz", "Ambiente": "1", "ChaveAcessoDfe": key})
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
    blocked = _portal_http_failure(post_response)
    if blocked:
        return None, blocked[0], blocked[1]
    xml = extract_downloaded_xml(post_response.text)
    if xml:
        return xml, "ok", ""
    page = f"{get_response.text}\n{post_response.text}"
    kind = classify_portal_body(post_response.status_code, page)
    return None, kind, download_failure_message(kind, post_response.status_code)


def run_job(job: Job, seed_bytes: bytes, pfx_bytes: bytes, password: str, options: dict[str, Any]) -> None:
    cert_path: Path | None = None
    key_path: Path | None = None
    session: requests.Session | None = None
    try:
        _update(job, status="running", message="Validando XML e certificado", progress=1)
        cfg = parse_seed_xml(seed_bytes)
        if aamm_order(cfg["aamm"]) > aamm_order(current_aamm()):
            raise ValueError("A competência do XML semente está no futuro.")
        cert_path, key_path, cert_cnpj = _certificate_files(pfx_bytes, password, job.directory)
        if cert_cnpj and cert_cnpj != cfg["cnpj"]:
            raise ValueError("O CNPJ do certificado é diferente do emitente do XML.")

        verify_path = svrs_ca_bundle()
        session = _new_svrs_session(cert_path, key_path, verify_path)
        records: list[dict[str, Any]] = []
        pending_items = list(options.get("pending_items") or [])
        interval_seconds = clamp_download_interval(
            int(options.get("download_interval_seconds", SVRS_INTERVAL_MIN_SECONDS))
        )
        pending_only = bool(options.get("pending_only"))
        paused_for_svrs = False
        xml_dir = job.directory / "xml"
        xml_dir.mkdir(exist_ok=True)

        # Reprocessa primeiro a fila persistente enviada pela Edge Function.
        # Pendências NÃO contam como "encontradas" da varredura e NÃO avançam o cursor.
        # Lote limitado: a Edge reinicia a empresa até esgotar a fila.
        pending_saved = 0
        pending_failed = 0
        if pending_items:
            pending_queue = list(pending_items)[:MAX_PENDING_PER_RUN]
            pending_total = len(pending_queue)
            pending_remaining = max(0, len(pending_items) - pending_total)
            _update(
                job,
                message=(
                    f"Recuperando {pending_total} pendência(s)"
                    + (
                        f" ({pending_remaining} ficam para a próxima execução)"
                        if pending_remaining
                        else ""
                    )
                ),
                progress=2,
            )
            _callback(
                job,
                "progress",
                consulted=0,
                found=0,
                downloaded=0,
                pending_total=pending_total,
                pending_remaining=pending_remaining,
                mode="pending_recovery",
                message=(
                    f"Recuperando pendências: 0/{pending_total} · "
                    f"{pending_remaining} restantes na fila"
                ),
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

                item, xml, last_download_error, failure_kind = _download_one(
                    cert_path, key_path, verify_path, item
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
                else:
                    failure_reason = last_download_error or download_failure_message(failure_kind)
                    if failure_kind == "rate_limit":
                        paused_for_svrs = True
                    else:
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
                    if paused_for_svrs:
                        _update(
                            job,
                            message=(
                                "Pausa: a SVRS limitou as consultas. "
                                f"{pending_saved} salvas neste lote. "
                                "O restante continua na fila daqui a 1 min 30 s."
                            ),
                        )
                        break

                message = (
                    f"Recuperando pendências: {pending_index}/{pending_total} · "
                    f"{pending_saved} salvas · {pending_failed} falhas"
                    + (
                        f" · {pending_remaining} na fila"
                        if pending_remaining
                        else ""
                    )
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
                    pending_remaining=pending_remaining,
                    mode="pending_recovery",
                    message=message,
                )

                if pending_index < pending_total and interval_seconds:
                    _update(
                        job,
                        message=(
                            f"Aguardando {format_wait(interval_seconds)} · próxima NFC-e · "
                            f"{pending_index}/{pending_total}"
                        ),
                    )
                    time.sleep(interval_seconds)

            _callback(
                job,
                "progress",
                consulted=0,
                found=0,
                downloaded=pending_saved,
                pending_total=pending_total,
                pending_failed=pending_failed,
                pending_remaining=pending_remaining,
                mode="pending_recovery",
                message=(
                    (
                        f"Pausa por limite da SVRS · {pending_saved} salvas · "
                        "o restante segue no próximo lote"
                    )
                    if paused_for_svrs
                    else (
                        f"Pendências do lote: {pending_saved} salvas · "
                        f"{pending_failed} sem XML"
                        + (
                            f" · {pending_remaining} ficam para a próxima execução"
                            if pending_remaining or pending_only
                            else " · seguindo para varredura"
                        )
                    )
                ),
            )

            if pending_only or paused_for_svrs:
                start_aamm = str(options.get("start_aamm") or cfg["aamm"])
                start_nnf = int(
                    options.get("start_number")
                    if options.get("start_number") is not None
                    else cfg["number"]
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
                    cursor_aamm=start_aamm,
                    cursor_nnf=start_nnf,
                    message=(
                        (
                            f"Pausa por limite da SVRS · {pending_saved} salvas. "
                            "As demais NFC-e continuam na fila e seguem em 1 min 30 s."
                        )
                        if paused_for_svrs
                        else (
                            f"Lote de pendências: {pending_saved} salvas · "
                            f"{pending_failed} sem XML"
                            + (
                                f" · {pending_remaining} restantes na fila"
                                if pending_remaining
                                else ""
                            )
                        )
                    ),
                )
                _update(
                    job,
                    status="completed",
                    message=(
                        "Pausa por limite da SVRS"
                        if paused_for_svrs
                        else "Pendências do lote processadas"
                    ),
                    progress=100,
                    downloaded=pending_saved,
                )
                return

        found: list[dict[str, Any]] = []
        current_month = str(options.get("start_aamm") or cfg["aamm"])
        start_number = int(options.get("start_number") if options.get("start_number") is not None else cfg["number"])
        number = start_number + 1
        consecutive_217, gap_start, last_probe = 0, None, number - 1
        max_numbers = options["max_numbers"]
        last_progress_at = 0.0
        last_consulted_aamm = current_month
        last_consulted_nnf = start_number

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
        while len(records) < max_numbers:
            _update(
                job,
                message=f"Consultando {current_month} nNF {number}",
                current_number=number,
                current_competence=current_month,
                progress=min(65, 2 + int(len(records) / max_numbers * 63)),
            )
            status, reason, real_key = _consult(session, cfg, number, current_month)
            last_consulted_aamm = current_month
            last_consulted_nnf = number
            report_progress(f"Consultando {current_month} nNF {number}")
            record = {"AAMM": current_month, "nNF": number, "cStat": status, "xMotivo": reason, "chave_real": real_key}
            records.append(record)
            if status == "613" and real_key:
                found.append(record)
                consecutive_217, gap_start, last_probe = 0, None, number
                number += 1
                time.sleep(options["query_interval_ms"] / 1000)
                continue
            if status != "217":
                consecutive_217, gap_start = 0, None
                number += 1
                time.sleep(options["query_interval_ms"] / 1000)
                continue
            gap_start = number if gap_start is None else gap_start
            consecutive_217 += 1
            if consecutive_217 >= options["month_trigger"]:
                following = next_aamm(current_month)
                if aamm_order(following) <= aamm_order(current_aamm()):
                    probe_start = max(gap_start, last_probe + 1)
                    probe_end = probe_start + options["month_window"] - 1
                    switched = False
                    for probe in range(probe_start, probe_end + 1):
                        if len(records) >= max_numbers:
                            break
                        status2, reason2, real2 = _consult(session, cfg, probe, following)
                        probe_record = {"AAMM": following, "nNF": probe, "cStat": status2, "xMotivo": reason2, "chave_real": real2}
                        records.append(probe_record)
                        if status2 == "613" and real2:
                            found.append(probe_record)
                            last_consulted_aamm, last_consulted_nnf = following, probe
                            current_month, number = following, probe + 1
                            consecutive_217, gap_start, last_probe, switched = 0, None, probe, True
                            break
                        time.sleep(options["query_interval_ms"] / 1000)
                    last_probe = probe_end
                    if switched:
                        continue
            if consecutive_217 >= options["stop_gap"]:
                break
            number += 1
            time.sleep(options["query_interval_ms"] / 1000)

        _update(job, consulted=len(records), found=len(found), message=f"Baixando {len(found)} XML(s)", progress=68)
        _callback(
            job, "progress",
            consulted=len(records), found=len(found), downloaded=pending_saved,
            message=f"Baixando {len(found)} XML(s) da varredura",
            mode="download",
        )
        xml_dir = job.directory / "xml"
        xml_dir.mkdir(exist_ok=True)
        downloaded = pending_saved
        processed_downloads = 0
        # Download estritamente serial: nenhuma próxima requisição começa antes
        # de terminar o intervalo configurado.
        if found:
            for original_index, item in enumerate(found, 1):
                item["_download_interval_seconds"] = interval_seconds
                try:
                    item, xml, last_download_error, failure_kind = _download_one(
                        cert_path, key_path, verify_path, item
                    )
                except Exception as exc:
                    xml, last_download_error, failure_kind = None, str(exc), "http"

                processed_downloads += 1
                if xml:
                    full_xml = '<?xml version="1.0" encoding="UTF-8"?>\n' + xml
                    _callback(
                        job, "file", key=item["chave_real"], aamm=item["AAMM"],
                        number=item["nNF"], emitted_at=_xml_emission_date(xml),
                        advance_cursor=False,
                        consulted=len(records), found=len(found), item_index=original_index,
                        xml_base64=base64.b64encode(full_xml.encode("utf-8")).decode("ascii"),
                    )
                    (xml_dir / f'{item["chave_real"]}-procNFe.xml').write_text(
                        full_xml, encoding="utf-8"
                    )
                    item["download_status"] = "OK"
                    downloaded += 1
                else:
                    item["download_status"] = "LIMITE_SVRS" if failure_kind == "rate_limit" else "NAO_EXTRAIDO"
                    failure_reason = last_download_error or download_failure_message(failure_kind)
                    item["xMotivo"] = (
                        f'{item.get("xMotivo", "")} | download: {failure_reason[:300]}'
                    )
                    _callback(
                        job, "download_failed", key=item["chave_real"], aamm=item["AAMM"],
                        number=item["nNF"], error=failure_reason, error_kind=failure_kind,
                        consulted=len(records), found=len(found), item_index=original_index,
                    )
                    if failure_kind == "rate_limit":
                        paused_for_svrs = True
                        _update(
                            job,
                            message=(
                                "Pausa: a SVRS limitou as consultas. "
                                "As NFC-e restantes continuam na fila."
                            ),
                        )
                        break

                message = (
                    f"Baixando XMLs: {processed_downloads}/{len(found)} processados · "
                    f"{downloaded} salvos"
                )
                _update(
                    job, downloaded=downloaded, message=message,
                    progress=68 + int(processed_downloads / max(1, len(found)) * 27),
                )
                if processed_downloads == len(found) or processed_downloads % 10 == 0:
                    _callback(
                        job, "progress", consulted=len(records), found=len(found),
                        downloaded=downloaded, message=message,
                    )

                if processed_downloads < len(found) and interval_seconds:
                    _update(
                        job,
                        message=(
                            f"Aguardando {format_wait(interval_seconds)} para o próximo XML · "
                            f"{processed_downloads}/{len(found)} processados · "
                            f"{downloaded} salvos"
                        ),
                    )
                    time.sleep(interval_seconds)
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
        completion_message = "Processamento concluído"
        if paused_for_svrs:
            completion_message = (
                f"Pausa por limite da SVRS · {downloaded} XML salvos. "
                "O restante continua na fila e segue em 1 min 30 s."
            )
        elif pending_saved or pending_failed:
            completion_message = (
                f"Concluído · pendências {pending_saved} salvas/"
                f"{pending_failed} falhas · varredura {len(found)} encontradas/"
                f"{max(0, downloaded - pending_saved)} salvas"
            )
        _callback(
            job, "completed", consulted=len(records), found=len(found), downloaded=downloaded,
            cursor_aamm=last_consulted_aamm, cursor_nnf=last_consulted_nnf,
            pending_saved=pending_saved, pending_failed=pending_failed,
            pause_for_svrs=paused_for_svrs,
            message=completion_message,
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
    intervalo_download_segundos: int = Form(90),
    somente_pendentes: str = Form("false"),
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
        active_jobs = [item for item in _jobs.values() if item.status in {"queued", "running"}]
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
    job = Job(
        id=job_id, owner_id=f"run:{run_id}", directory=directory,
        callback_token=run_token, external_run_id=run_id,
    )
    with _jobs_lock:
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
    intervalo_download_segundos: int = Form(90),
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
        active_jobs = [item for item in _jobs.values() if item.status in {"queued", "running"}]
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
