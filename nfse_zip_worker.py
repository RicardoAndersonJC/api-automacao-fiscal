"""Worker de ZIP unico dos XMLs NFS-e.

Projetado para o web service Render existente: o endpoint apenas despacha uma
thread; concorrencia entre instancias e retomada sao controladas por leases no
Postgres. O ZIP usa ZIP64 e arquivo temporario em disco, sem acumular XMLs em
RAM.
"""
from __future__ import annotations

import hmac
import json
import os
import random
import re
import shutil
import tempfile
import threading
import time
import uuid
import zipfile
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from typing import Any
from urllib.parse import quote

import requests
from fastapi import FastAPI, Header
from fastapi.responses import JSONResponse

_active: set[str] = set()
_active_lock = threading.Lock()
_lease_seconds = 300
_heartbeat_interval = 45.0
_transient_statuses = {408, 429, 500, 502, 503, 504}
_download_session_local = threading.local()


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
    encoded = quote(object_path, safe="/")
    headers = _headers(key)
    headers.update({"Content-Type": "application/zip", "x-upsert": "true"})
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
        zip_path = temp_dir / "nfse_xmls.zip"
        download_dir = temp_dir / "downloads"
        download_dir.mkdir()
        download_concurrency = _bounded_env_int("NFSE_ZIP_DOWNLOAD_CONCURRENCY", 8, 1, 16)
        checkpoint_size = _bounded_env_int("NFSE_ZIP_CHECKPOINT_SIZE", 250, 250, 500)
        compression_level = _bounded_env_int("NFSE_ZIP_COMPRESSION_LEVEL", 2, 0, 9)
        _log("running", job_id, concurrency=download_concurrency, checkpoint_size=checkpoint_size)
        total_download_ms = 0
        total_checkpoint_ms = 0
        bytes_downloaded = 0
        with zipfile.ZipFile(
            zip_path,
            mode="w",
            compression=zipfile.ZIP_DEFLATED,
            allowZip64=True,
            compresslevel=compression_level,
        ) as archive, ThreadPoolExecutor(
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
                                bytes_downloaded += int(downloaded_item["size"])
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
        object_path = (
            f"{job['organizacao_id']}/{job['usuario_id']}/{job_id}/"
            "nfse_xmls.zip"
        )
        if heartbeat_lost.is_set():
            raise RuntimeError(heartbeat_error[-1] if heartbeat_error else "Lease perdido")
        upload_started = time.monotonic()
        _upload_zip(url, key, object_path, zip_path, control_session)
        upload_ms = int((time.monotonic() - upload_started) * 1000)
        if heartbeat_lost.is_set():
            raise RuntimeError(heartbeat_error[-1] if heartbeat_error else "Lease perdido durante upload")
        _rpc(
            url,
            key,
            "finish_nfse_xml_zip_job",
            {
                "p_job_id": job_id,
                "p_worker_id": worker_id,
                "p_result_path": object_path,
                "p_size": zip_path.stat().st_size,
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
            zip_bytes=zip_path.stat().st_size,
        )
    except Exception as exc:
        if url and key:
            try:
                _rpc(
                    url,
                    key,
                    "defer_nfse_xml_zip_job",
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


def install_nfse_zip_routes(app: FastAPI) -> None:
    @app.post("/nfse/xml-zip/dispatch")
    @app.post("/nfe/xml-zip/dispatch")
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
        threading.Thread(
            target=process_nfse_xml_zip,
            args=(job_id,),
            name=f"nfse-zip-{job_id[:8]}",
            daemon=True,
        ).start()
        return JSONResponse(
            {"success": True, "accepted": True, "job_id": job_id},
            status_code=202,
        )
