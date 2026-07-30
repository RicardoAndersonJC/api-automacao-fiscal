"""Worker de ZIP único dos XMLs NFS-e com upload retomável.

Projetado para o web service Render existente: o endpoint apenas despacha uma
thread; concorrencia entre instancias e retomada sao controladas por leases no
Postgres. O ZIP usa ZIP64, arquivo temporário em disco e upload TUS em blocos,
sem acumular XMLs em RAM.
"""
from __future__ import annotations

import hmac
import html
import base64
import json
import os
import random
import re
import secrets
import shutil
import tempfile
import threading
import time
import uuid
import zipfile
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from typing import Any
from urllib.parse import quote, urljoin, urlparse

import requests
from lxml import etree
from fastapi import FastAPI, Header
from fastapi.responses import FileResponse, JSONResponse

_active: set[str] = set()
_active_lock = threading.Lock()
_lease_seconds = 300
_heartbeat_interval = 45.0
_transient_statuses = {408, 429, 500, 502, 503, 504}
_download_session_local = threading.local()
_zip_result_ttl_seconds = 2 * 60 * 60

_excel_columns = [
    "Arquivo", "Numero_NFSe", "Competencia", "Dh_Emissao_DPS",
    "Prestador_CNPJ", "Prestador_Razao", "Prestador_Mun_UF",
    "Tomador_CNPJ", "Tomador_CPF", "Tomador_Nome",
    "CTribNac", "Descricao_Servico", "Local_Prest", "Municipio_Incidencia",
    "V_Servico", "V_ISSQN", "tpRetISSQN", "ISS_Status",
    "PIS_Valor", "COFINS_Valor", "IRRF_Retido", "INSS_Retido_vRetCP",
    "CSLL_Retida", "V_Total_Retencoes", "V_Liquido", "tpRetPisCofins",
    "PIS_Retido_Derivado", "COFINS_Retido_Derivado",
    "Tem_Substituicao", "Chave_Substituida_chSubstda", "Erro",
]


def _repair_text(value: str) -> str:
    current = html.unescape(html.unescape(html.unescape(str(value or ""))))
    for _ in range(3):
        try:
            candidate = current.encode("cp1252").decode("utf-8")
        except (UnicodeEncodeError, UnicodeDecodeError):
            break
        if sum(candidate.count(ch) for ch in "ÃÂ") >= sum(current.count(ch) for ch in "ÃÂ"):
            break
        current = candidate
    return current.replace("ÿ", "Ó").replace("¿", "Ó").strip()


def _parse_excel_xml(path: Path, file_name: str) -> list[Any]:
    row: dict[str, Any] = {column: "" for column in _excel_columns}
    row["Arquivo"] = file_name
    try:
        root = etree.fromstring(path.read_bytes(), parser=etree.XMLParser(recover=False))

        def section(node: Any, tag: str) -> Any:
            if node is None:
                return None
            found = node.xpath(".//*[local-name()=$tag]", tag=tag)
            return found[0] if found else None

        def text(node: Any, tag: str) -> str:
            found = section(node, tag)
            return _repair_text("".join(found.itertext())) if found is not None else ""

        def digits(value: str) -> str:
            return re.sub(r"\D", "", value or "")

        def number(value: str) -> float | None:
            try:
                return float(value.replace(",", ".")) if value else None
            except ValueError:
                return None

        inf = section(root, "infNFSe")
        if inf is None:
            raise ValueError("Estrutura NFSe nao encontrada")
        inf_dps = section(inf, "infDPS")
        emit = section(inf, "emit")
        toma = section(inf_dps, "toma")
        serv = section(inf_dps, "serv")
        trib_fed = section(inf_dps, "tribFed")
        piscofins = section(trib_fed, "piscofins")
        trib_mun = section(inf_dps, "tribMun")
        subst = section(inf_dps, "subst") or section(inf, "subst")
        pis = number(text(piscofins, "vPis"))
        cofins = number(text(piscofins, "vCofins"))
        tp_pis_cofins = text(piscofins, "tpRetPisCofins")
        tp_iss = text(trib_mun, "tpRetISSQN")
        chave_substituida = digits(text(subst, "chSubstda"))
        prest_mun = text(section(emit, "enderNac"), "cMun")
        prest_uf = text(section(emit, "enderNac"), "UF")
        row.update({
            "Numero_NFSe": text(inf, "nNFSe"),
            "Competencia": text(inf_dps, "dCompet"),
            "Dh_Emissao_DPS": text(inf_dps, "dhEmi"),
            "Prestador_CNPJ": digits(text(emit, "CNPJ")),
            "Prestador_Razao": text(emit, "xNome"),
            "Prestador_Mun_UF": "/".join(filter(None, [prest_mun, prest_uf])),
            "Tomador_CNPJ": digits(text(toma, "CNPJ")),
            "Tomador_CPF": digits(text(toma, "CPF")),
            "Tomador_Nome": text(toma, "xNome"),
            "CTribNac": text(serv, "cTribNac"),
            "Descricao_Servico": text(serv, "xDescServ"),
            "Local_Prest": text(inf, "xLocPrestacao"),
            "Municipio_Incidencia": text(inf, "xLocIncid"),
            "V_Servico": number(text(section(inf_dps, "vServPrest"), "vServ")),
            "V_ISSQN": number(text(inf, "vISSQN")),
            "tpRetISSQN": tp_iss,
            "ISS_Status": "NÃO RETIDO" if tp_iss == "1" else "ISS RETIDO" if tp_iss else "",
            "PIS_Valor": pis,
            "COFINS_Valor": cofins,
            "IRRF_Retido": number(text(trib_fed, "vRetIRRF")),
            "INSS_Retido_vRetCP": number(text(trib_fed, "vRetCP")),
            "CSLL_Retida": number(text(trib_fed, "vRetCSLL")),
            "V_Total_Retencoes": number(text(inf, "vTotalRet")),
            "V_Liquido": number(text(inf, "vLiq")),
            "tpRetPisCofins": tp_pis_cofins,
            "PIS_Retido_Derivado": (pis or 0) if tp_pis_cofins in ("1", "3") else 0 if tp_pis_cofins else None,
            "COFINS_Retido_Derivado": (cofins or 0) if tp_pis_cofins in ("1", "4") else 0 if tp_pis_cofins else None,
            "Tem_Substituicao": "SIM" if chave_substituida else "NÃO",
            "Chave_Substituida_chSubstda": chave_substituida,
        })
    except Exception as exc:
        row["Erro"] = str(exc)[:500]
    return [row[column] if row[column] is not None else "" for column in _excel_columns]


def _log(stage: str, job_id: str, **fields: Any) -> None:
    """Structured logs without XML contents, credentials or signed URLs."""
    print(json.dumps({"event": "nfse_zip", "stage": stage, "job_id": job_id, **fields},
                     ensure_ascii=False, default=str), flush=True)


def _bounded_env_int(name: str, default: int, minimum: int, maximum: int) -> int:
    try:
        return max(minimum, min(int(os.environ.get(name, default)), maximum))
    except (TypeError, ValueError):
        return default


def _safe_archive_name(value: str, arquivo_id: str) -> str:
    parts = str(value or "").replace("\\", "/").split("/")
    safe_parts = []
    for part in parts:
        cleaned = re.sub(r"[^A-Za-z0-9._ -]", "_", part).replace("..", "_").strip(". ")
        if cleaned:
            safe_parts.append(cleaned[:160])
    if not safe_parts:
        safe_parts = ["_SEM_COMPETENCIA_", f"{arquivo_id}.xml"]
    elif len(safe_parts) == 1:
        safe_parts.insert(0, "_SEM_COMPETENCIA_")
    return "/".join(safe_parts)


def _settings() -> tuple[str, str, str]:
    url = os.environ.get("SUPABASE_URL", "").rstrip("/")
    key = os.environ.get("SUPABASE_SERVICE_ROLE_KEY", "")
    secret = os.environ.get("NFSE_ZIP_INTERNAL_SECRET", "")
    if not url or not key or not secret:
        raise RuntimeError(
            "Configure SUPABASE_URL, SUPABASE_SERVICE_ROLE_KEY e "
            "NFSE_ZIP_INTERNAL_SECRET"
        )
    return url, key, secret


def _headers(key: str) -> dict[str, str]:
    return {
        "Authorization": f"Bearer {key}",
        "apikey": key,
        "Content-Type": "application/json",
    }


def _new_session(pool_size: int = 8) -> requests.Session:
    session = requests.Session()
    adapter = requests.adapters.HTTPAdapter(
        pool_connections=pool_size,
        pool_maxsize=pool_size,
        max_retries=0,
        pool_block=True,
    )
    session.mount("https://", adapter)
    session.mount("http://", adapter)
    return session


def _download_session(pool_size: int) -> requests.Session:
    session = getattr(_download_session_local, "session", None)
    if session is None:
        session = _new_session(pool_size)
        _download_session_local.session = session
    return session


def _rpc(
    url: str,
    key: str,
    name: str,
    payload: dict[str, Any],
    session: requests.Session | None = None,
) -> Any:
    response = (session or requests).post(
        f"{url}/rest/v1/rpc/{name}",
        headers=_headers(key),
        json=payload,
        timeout=(10, 60),
    )
    response.raise_for_status()
    return response.json() if response.content else None


def _download_to_temp(
    url: str,
    key: str,
    item: dict[str, Any],
    target_dir: Path,
    pool_size: int,
) -> dict[str, Any]:
    storage_path = str(item["storage_path"])
    encoded = quote(storage_path, safe="/")
    target = target_dir / f"{int(item['seq']):020d}_{item['arquivo_id']}.xml"
    last_error: Exception | None = None
    for attempt in range(3):
        try:
            with _download_session(pool_size).get(
                f"{url}/storage/v1/object/fiscal-files/{encoded}",
                headers=_headers(key),
                stream=True,
                timeout=(15, 120),
            ) as response:
                if response.status_code in _transient_statuses and attempt < 2:
                    raise requests.HTTPError(
                        f"HTTP transitorio {response.status_code}", response=response
                    )
                response.raise_for_status()
                size = 0
                with target.open("wb") as output:
                    for chunk in response.iter_content(chunk_size=256 * 1024):
                        if chunk:
                            output.write(chunk)
                            size += len(chunk)
                return {"item": item, "path": target, "size": size, "error": None}
        except Exception as exc:
            last_error = exc
            target.unlink(missing_ok=True)
            status = getattr(getattr(exc, "response", None), "status_code", None)
            if attempt >= 2 or (status is not None and status not in _transient_statuses):
                break
            retry_after = getattr(getattr(exc, "response", None), "headers", {}).get("Retry-After")
            try:
                delay = min(float(retry_after), 30.0) if retry_after else 0.25 * (2**attempt)
            except (TypeError, ValueError):
                delay = 0.25 * (2**attempt)
            time.sleep(delay + random.uniform(0, max(0.05, delay * 0.2)))
    return {"item": item, "path": None, "size": 0, "error": str(last_error)[:1000]}


def _upload_zip(
    url: str,
    key: str,
    object_path: str,
    local_path: Path,
    session: requests.Session | None = None,
) -> None:
    # Supabase recomenda TUS para arquivos acima de 6 MB. O ZIP continua sendo
    # um único objeto; somente a transferência ocorre em blocos retomáveis.
    parsed = urlparse(url)
    project_ref = parsed.hostname.split(".")[0] if parsed.hostname else ""
    storage_origin = (
        f"{parsed.scheme}://{project_ref}.storage.supabase.co"
        if project_ref else url
    )
    endpoint = f"{storage_origin}/storage/v1/upload/resumable"
    headers = _headers(key)
    metadata = {
        "bucketName": "nfse-exports-private",
        "objectName": object_path,
        "contentType": "application/zip",
        "cacheControl": "3600",
    }
    encoded_metadata = ",".join(
        f"{name} {base64.b64encode(value.encode()).decode()}"
        for name, value in metadata.items()
    )
    headers.update({
        "Tus-Resumable": "1.0.0",
        "Upload-Length": str(local_path.stat().st_size),
        "Upload-Metadata": encoded_metadata,
        "x-upsert": "true",
    })
    headers.pop("Content-Type", None)
    client = session or requests.Session()
    created = client.post(endpoint, headers=headers, timeout=(15, 60))
    if created.status_code != 201:
        raise requests.HTTPError(
            f"TUS create HTTP {created.status_code}: {created.text[:500]}",
            response=created,
        )
    upload_url = urljoin(endpoint, created.headers["Location"])
    chunk_size = 6 * 1024 * 1024
    offset = 0
    with local_path.open("rb") as body:
        while offset < local_path.stat().st_size:
            body.seek(offset)
            chunk = body.read(chunk_size)
            patch_headers = {
                "Authorization": f"Bearer {key}",
                "apikey": key,
                "Tus-Resumable": "1.0.0",
                "Upload-Offset": str(offset),
                "Content-Type": "application/offset+octet-stream",
                "Content-Length": str(len(chunk)),
            }
            response = client.patch(
                upload_url,
                headers=patch_headers,
                data=chunk,
                timeout=(15, 180),
            )
            if response.status_code != 204:
                raise requests.HTTPError(
                    f"TUS patch HTTP {response.status_code}: {response.text[:500]}",
                    response=response,
                )
            offset = int(response.headers.get("Upload-Offset", offset + len(chunk)))


def _upload_excel(
    url: str,
    key: str,
    object_path: str,
    local_path: Path,
    session: requests.Session | None = None,
) -> None:
    encoded = quote(object_path, safe="/")
    headers = _headers(key)
    headers.update({
        "Content-Type": "application/vnd.openxmlformats-officedocument.spreadsheetml.sheet",
        "x-upsert": "true",
    })
    with local_path.open("rb") as body:
        response = (session or requests).post(
            f"{url}/storage/v1/object/nfse-exports-private/{encoded}",
            headers=headers,
            data=body,
            timeout=(15, 900),
        )
    response.raise_for_status()


def _first(value: Any) -> dict[str, Any] | None:
    if isinstance(value, list):
        return value[0] if value else None
    return value if isinstance(value, dict) else None


def _zip_result_dir() -> Path:
    path = Path(tempfile.gettempdir()) / "nfse_zip_results"
    path.mkdir(parents=True, exist_ok=True)
    return path


def _cleanup_zip_results() -> None:
    cutoff = time.time() - _zip_result_ttl_seconds
    for path in _zip_result_dir().glob("*.zip"):
        try:
            if path.stat().st_mtime < cutoff:
                path.unlink(missing_ok=True)
        except OSError:
            continue


def _publish_zip_download(zip_path: Path) -> tuple[str, int]:
    _cleanup_zip_results()
    token = secrets.token_urlsafe(32)
    target = _zip_result_dir() / f"{token}.zip"
    size = zip_path.stat().st_size
    shutil.move(str(zip_path), str(target))
    public_base = os.environ.get(
        "NFSE_ZIP_PUBLIC_URL", "https://api-automacao-fiscal.onrender.com"
    ).rstrip("/")
    return f"external:{public_base}/nfse/xml-zip/download/{token}", size


def process_nfse_xml_zip(job_id: str) -> None:
    worker_id = str(uuid.uuid4())
    temp_dir: Path | None = None
    url = key = ""
    heartbeat_stop = threading.Event()
    heartbeat_lost = threading.Event()
    heartbeat_error: list[str] = []
    heartbeat_thread: threading.Thread | None = None
    control_session: requests.Session | None = None
    try:
        url, key, _ = _settings()
        control_session = _new_session(4)
        job_started = time.monotonic()
        job = _first(
            _rpc(
                url,
                key,
                "claim_nfse_xml_zip_job",
                {
                    "p_job_id": job_id,
                    "p_worker_id": worker_id,
                    "p_lease_seconds": _lease_seconds,
                },
                control_session,
            )
        )
        if not job:
            return

        def keep_lease_alive() -> None:
            heartbeat_session = _new_session(2)
            try:
                while not heartbeat_stop.wait(_heartbeat_interval):
                    try:
                        ok = _rpc(url, key, "heartbeat_nfse_xml_zip_job", {
                            "p_job_id": job_id,
                            "p_worker_id": worker_id,
                            "p_lease_seconds": _lease_seconds,
                        }, heartbeat_session)
                        if ok is not True:
                            raise RuntimeError("Lease perdido durante a geracao")
                    except Exception as exc:
                        heartbeat_error.append(str(exc))
                        heartbeat_lost.set()
                        return
            finally:
                heartbeat_session.close()

        heartbeat_thread = threading.Thread(
            target=keep_lease_alive,
            name=f"nfse-zip-heartbeat-{job_id[:8]}",
            daemon=True,
        )
        heartbeat_thread.start()

        temp_dir = Path(tempfile.mkdtemp(prefix=f"nfse_zip_{job_id[:8]}_"))
        zip_paths: list[Path] = []
        download_dir = temp_dir / "downloads"
        download_dir.mkdir()
        download_concurrency = _bounded_env_int("NFSE_ZIP_DOWNLOAD_CONCURRENCY", 12, 1, 24)
        checkpoint_size = _bounded_env_int("NFSE_ZIP_CHECKPOINT_SIZE", 500, 250, 1000)
        compression_level = _bounded_env_int("NFSE_ZIP_COMPRESSION_LEVEL", 2, 0, 9)
        part_max_bytes = 5 * 1024 * 1024 * 1024
        _log("running", job_id, concurrency=download_concurrency, checkpoint_size=checkpoint_size)
        total_download_ms = 0
        total_checkpoint_ms = 0
        bytes_downloaded = 0
        part_uncompressed_bytes = 0
        part_entries = 0
        archive: zipfile.ZipFile | None = None

        def open_next_part() -> zipfile.ZipFile:
            part_path = (
                temp_dir / "nfse_xmls.zip"
                if not zip_paths
                else temp_dir / f"nfse_xmls_parte_{len(zip_paths) + 1:03d}.zip"
            )
            zip_paths.append(part_path)
            return zipfile.ZipFile(
                part_path,
                mode="w",
                compression=zipfile.ZIP_DEFLATED,
                allowZip64=True,
                compresslevel=compression_level,
            )

        try:
            archive = open_next_part()
            with ThreadPoolExecutor(
                max_workers=download_concurrency,
                thread_name_prefix="nfse-xml-download",
            ) as executor:
              while True:
                items = _rpc(
                    url,
                    key,
                    "claim_nfse_xml_zip_items",
                    {
                        "p_job_id": job_id,
                        "p_worker_id": worker_id,
                        # Claim e checkpoint usam o mesmo tamanho efetivo. Assim
                        # NFSE_ZIP_CHECKPOINT_SIZE=500 reduz de fato as viagens
                        # ao banco, sem uma pagina intermediaria fixa em 250.
                        "p_limit": checkpoint_size,
                    }, control_session,
                ) or []
                if not items:
                    break

                for start in range(0, len(items), checkpoint_size):
                    wave = items[start : start + checkpoint_size]
                    if heartbeat_lost.is_set():
                        raise RuntimeError(heartbeat_error[-1] if heartbeat_error else "Lease perdido")
                    download_started = time.monotonic()
                    downloaded = list(
                        executor.map(
                            lambda item: _download_to_temp(
                                url, key, item, download_dir, download_concurrency
                            ),
                            wave,
                        )
                    )
                    total_download_ms += int((time.monotonic() - download_started) * 1000)
                    results: list[dict[str, Any]] = []
                    for downloaded_item in downloaded:
                        item = downloaded_item["item"]
                        path = downloaded_item["path"]
                        if heartbeat_lost.is_set():
                            raise RuntimeError(
                                heartbeat_error[-1] if heartbeat_error else "Lease perdido"
                            )
                        if path is not None:
                            try:
                                item_size = int(downloaded_item["size"])
                                if (
                                    part_entries > 0
                                    and part_uncompressed_bytes + item_size > part_max_bytes
                                ):
                                    archive.close()
                                    archive = open_next_part()
                                    part_uncompressed_bytes = 0
                                    part_entries = 0
                                archive.write(
                                    path,
                                    arcname=_safe_archive_name(
                                        str(item["archive_name"]), str(item["arquivo_id"])
                                    ),
                                )
                                results.append({
                                    "arquivo_id": item["arquivo_id"],
                                    "ok": True,
                                    "size": downloaded_item["size"],
                                })
                                bytes_downloaded += item_size
                                part_uncompressed_bytes += item_size
                                part_entries += 1
                            finally:
                                path.unlink(missing_ok=True)
                        else:
                            results.append({
                                "arquivo_id": item["arquivo_id"],
                                "ok": False,
                                "error": downloaded_item["error"],
                            })
                    checkpoint_started = time.monotonic()
                    checkpoint = _rpc(
                        url,
                        key,
                        "checkpoint_nfse_xml_zip_items",
                        {
                            "p_job_id": job_id,
                            "p_worker_id": worker_id,
                            "p_results": results,
                        }, control_session,
                    )
                    total_checkpoint_ms += int((time.monotonic() - checkpoint_started) * 1000)
                    _log(
                        "checkpoint",
                        job_id,
                        processed=(checkpoint or {}).get("processados") if isinstance(checkpoint, dict) else None,
                        batch=len(results),
                        bytes_downloaded=bytes_downloaded,
                    )
        finally:
            if archive is not None:
                archive.close()

        if heartbeat_lost.is_set():
            raise RuntimeError(heartbeat_error[-1] if heartbeat_error else "Lease perdido")
        publish_started = time.monotonic()
        if len(zip_paths) != 1:
            raise RuntimeError("A geracao deveria produzir um unico ZIP")
        external_path, total_zip_bytes = _publish_zip_download(zip_paths[0])
        upload_ms = int((time.monotonic() - publish_started) * 1000)
        if heartbeat_lost.is_set():
            raise RuntimeError(heartbeat_error[-1] if heartbeat_error else "Lease perdido durante upload")
        _rpc(
            url,
            key,
            "finish_nfse_xml_zip_job_parts",
            {
                "p_job_id": job_id,
                "p_worker_id": worker_id,
                "p_result_paths": [external_path],
                "p_size": total_zip_bytes,
            }, control_session,
        )
        _log(
            "completed",
            job_id,
            duration_ms=int((time.monotonic() - job_started) * 1000),
            download_duration_ms=total_download_ms,
            checkpoint_duration_ms=total_checkpoint_ms,
            upload_duration_ms=upload_ms,
            bytes_downloaded=bytes_downloaded,
            zip_bytes=total_zip_bytes,
            zip_parts=len(zip_paths),
        )
    except Exception as exc:
        _log("failed", job_id, error=str(exc)[:500])
        if url and key:
            try:
                _rpc(
                    url,
                    key,
                    "fail_nfse_xml_zip_job",
                    {
                        "p_job_id": job_id,
                        "p_worker_id": worker_id,
                        "p_error": str(exc)[:1000],
                    }, control_session,
                )
            except Exception:
                pass
    finally:
        heartbeat_stop.set()
        if heartbeat_thread and heartbeat_thread is not threading.current_thread():
            heartbeat_thread.join(timeout=2)
        if temp_dir:
            shutil.rmtree(temp_dir, ignore_errors=True)
        if control_session:
            control_session.close()
        with _active_lock:
            _active.discard(job_id)


def process_nfse_excel(job_id: str) -> None:
    worker_id = str(uuid.uuid4())
    temp_dir: Path | None = None
    url = key = ""
    heartbeat_stop = threading.Event()
    heartbeat_lost = threading.Event()
    heartbeat_error: list[str] = []
    heartbeat_thread: threading.Thread | None = None
    control_session: requests.Session | None = None
    try:
        import xlsxwriter

        url, key, _ = _settings()
        control_session = _new_session(4)
        job_started = time.monotonic()
        job = _first(_rpc(url, key, "claim_nfse_xml_zip_job", {
            "p_job_id": job_id,
            "p_worker_id": worker_id,
            "p_lease_seconds": _lease_seconds,
        }, control_session))
        if not job or job.get("tipo") != "EXCEL":
            return

        def keep_lease_alive() -> None:
            heartbeat_session = _new_session(2)
            try:
                while not heartbeat_stop.wait(_heartbeat_interval):
                    try:
                        ok = _rpc(url, key, "heartbeat_nfse_xml_zip_job", {
                            "p_job_id": job_id,
                            "p_worker_id": worker_id,
                            "p_lease_seconds": _lease_seconds,
                        }, heartbeat_session)
                        if ok is not True:
                            raise RuntimeError("Lease perdido durante a geracao")
                    except Exception as exc:
                        heartbeat_error.append(str(exc))
                        heartbeat_lost.set()
                        return
            finally:
                heartbeat_session.close()

        heartbeat_thread = threading.Thread(
            target=keep_lease_alive,
            name=f"nfse-excel-heartbeat-{job_id[:8]}",
            daemon=True,
        )
        heartbeat_thread.start()

        temp_dir = Path(tempfile.mkdtemp(prefix=f"nfse_excel_{job_id[:8]}_"))
        excel_path = temp_dir / "nfse_relatorio_completo.xlsx"
        download_dir = temp_dir / "downloads"
        download_dir.mkdir()
        download_concurrency = _bounded_env_int("NFSE_EXCEL_DOWNLOAD_CONCURRENCY", 16, 1, 32)
        checkpoint_size = _bounded_env_int("NFSE_EXCEL_CHECKPOINT_SIZE", 500, 100, 1000)
        workbook = xlsxwriter.Workbook(str(excel_path), {"constant_memory": True})
        worksheet = workbook.add_worksheet("NFSe")
        header_format = workbook.add_format({
            "bold": True, "font_color": "#FFFFFF", "bg_color": "#1F4E78",
        })
        text_format = workbook.add_format({"num_format": "@"})
        for column, heading in enumerate(_excel_columns):
            worksheet.write(0, column, heading, header_format)
            worksheet.set_column(column, column, min(max(len(heading) + 2, 14), 42))

        row_index = 1
        bytes_downloaded = 0
        with ThreadPoolExecutor(
            max_workers=download_concurrency,
            thread_name_prefix="nfse-excel-download",
        ) as executor:
            while True:
                items = _rpc(url, key, "claim_nfse_xml_zip_items", {
                    "p_job_id": job_id,
                    "p_worker_id": worker_id,
                    "p_limit": checkpoint_size,
                }, control_session) or []
                if not items:
                    break
                downloaded = list(executor.map(
                    lambda item: _download_to_temp(
                        url, key, item, download_dir, download_concurrency
                    ),
                    items,
                ))
                results: list[dict[str, Any]] = []
                for downloaded_item in downloaded:
                    item = downloaded_item["item"]
                    path = downloaded_item["path"]
                    if heartbeat_lost.is_set():
                        raise RuntimeError(heartbeat_error[-1] if heartbeat_error else "Lease perdido")
                    if path is None:
                        values = [""] * len(_excel_columns)
                        values[0] = str(item.get("archive_name") or item["arquivo_id"])
                        values[-1] = str(downloaded_item["error"] or "Falha ao baixar")[:500]
                        results.append({
                            "arquivo_id": item["arquivo_id"], "ok": False,
                            "error": values[-1],
                        })
                    else:
                        try:
                            file_name = str(item.get("archive_name") or path.name)
                            values = _parse_excel_xml(path, file_name)
                            ok = not bool(values[-1])
                            results.append({
                                "arquivo_id": item["arquivo_id"], "ok": ok,
                                "size": downloaded_item["size"],
                                "error": None if ok else str(values[-1]),
                            })
                            bytes_downloaded += int(downloaded_item["size"])
                        finally:
                            path.unlink(missing_ok=True)
                    for column, value in enumerate(values):
                        if isinstance(value, (int, float)):
                            worksheet.write_number(row_index, column, value)
                        else:
                            safe = str(value or "")
                            if safe.startswith(("=", "+", "-", "@")):
                                safe = "'" + safe
                            worksheet.write(row_index, column, safe, text_format)
                    row_index += 1
                _rpc(url, key, "checkpoint_nfse_xml_zip_items", {
                    "p_job_id": job_id,
                    "p_worker_id": worker_id,
                    "p_results": results,
                }, control_session)
                _log("excel_checkpoint", job_id, batch=len(results), rows=row_index - 1)

        workbook.close()
        if heartbeat_lost.is_set():
            raise RuntimeError(heartbeat_error[-1] if heartbeat_error else "Lease perdido")
        object_path = (
            f"{job['organizacao_id']}/{job['usuario_id']}/{job_id}/"
            "nfse_relatorio_completo.xlsx"
        )
        _upload_excel(url, key, object_path, excel_path, control_session)
        _rpc(url, key, "finish_nfse_xml_zip_job", {
            "p_job_id": job_id,
            "p_worker_id": worker_id,
            "p_result_path": object_path,
            "p_size": excel_path.stat().st_size,
        }, control_session)
        _log(
            "excel_completed", job_id,
            duration_ms=int((time.monotonic() - job_started) * 1000),
            rows=row_index - 1,
            bytes_downloaded=bytes_downloaded,
            excel_bytes=excel_path.stat().st_size,
        )
    except Exception as exc:
        _log("excel_failed", job_id, error=str(exc)[:500])
        if url and key:
            try:
                _rpc(url, key, "defer_nfse_xml_zip_job", {
                    "p_job_id": job_id,
                    "p_worker_id": worker_id,
                    "p_error": str(exc)[:1000],
                }, control_session)
            except Exception:
                pass
    finally:
        heartbeat_stop.set()
        if heartbeat_thread and heartbeat_thread is not threading.current_thread():
            heartbeat_thread.join(timeout=2)
        if temp_dir:
            shutil.rmtree(temp_dir, ignore_errors=True)
        if control_session:
            control_session.close()
        with _active_lock:
            _active.discard(job_id)


def install_nfse_zip_routes(app: FastAPI) -> None:
    @app.get("/nfse/xml-zip/download/{token}")
    async def download_nfse_xml_zip(token: str):
        if not re.fullmatch(r"[A-Za-z0-9_-]{40,64}", token):
            return JSONResponse({"error": "Link invalido"}, status_code=404)
        _cleanup_zip_results()
        path = _zip_result_dir() / f"{token}.zip"
        if not path.is_file():
            return JSONResponse(
                {"error": "Arquivo expirado ou indisponivel"}, status_code=404
            )
        return FileResponse(
            path,
            media_type="application/zip",
            filename="nfse_xmls.zip",
            headers={"Cache-Control": "private, no-store"},
        )

    @app.post("/nfse/xml-zip/dispatch")
    @app.post("/nfe/xml-zip/dispatch")
    @app.post("/nfse/excel/dispatch")
    async def dispatch_nfse_xml_zip(
        payload: dict[str, Any],
        x_nfse_zip_secret: str | None = Header(default=None),
    ):
        try:
            _, _, expected = _settings()
        except RuntimeError as exc:
            return JSONResponse({"success": False, "error": str(exc)}, status_code=503)
        if not x_nfse_zip_secret or not hmac.compare_digest(
            x_nfse_zip_secret, expected
        ):
            return JSONResponse(
                {"success": False, "error": "Nao autorizado"}, status_code=401
            )
        job_id = str(payload.get("job_id") or "")
        try:
            uuid.UUID(job_id)
        except ValueError:
            return JSONResponse(
                {"success": False, "error": "job_id invalido"}, status_code=400
            )

        with _active_lock:
            if job_id in _active:
                return JSONResponse(
                    {"success": True, "accepted": True, "already_running": True},
                    status_code=202,
                )
            _active.add(job_id)
        is_excel = str(getattr(payload, "get", lambda *_: "")("tipo") or "") == "EXCEL"
        # O endpoint também identifica Excel pela rota enviada pelo Supabase.
        # Como o payload histórico contém apenas job_id, a rota específica
        # adiciona o tipo no Edge Function.
        target = process_nfse_excel if is_excel else process_nfse_xml_zip
        threading.Thread(
            target=target,
            args=(job_id,),
            name=f"nfse-zip-{job_id[:8]}",
            daemon=True,
        ).start()
        return JSONResponse(
            {"success": True, "accepted": True, "job_id": job_id},
            status_code=202,
        )
