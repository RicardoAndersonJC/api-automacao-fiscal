"""Worker de ZIP unico dos XMLs NFS-e.

Projetado para o web service Render existente: o endpoint apenas despacha uma
thread; concorrencia entre instancias e retomada sao controladas por leases no
Postgres. O ZIP usa ZIP64 e arquivo temporario em disco, sem acumular XMLs em
RAM.
"""
from __future__ import annotations

import hmac
import os
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
_batch_size = 250
_lease_seconds = 300
_heartbeat_interval = 45.0
_transient_statuses = {408, 429, 500, 502, 503, 504}


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


def _rpc(url: str, key: str, name: str, payload: dict[str, Any]) -> Any:
    response = requests.post(
        f"{url}/rest/v1/rpc/{name}",
        headers=_headers(key),
        json=payload,
        timeout=(10, 60),
    )
    response.raise_for_status()
    return response.json() if response.content else None


def _download_to_temp(
    url: str, key: str, item: dict[str, Any], target_dir: Path
) -> dict[str, Any]:
    storage_path = str(item["storage_path"])
    encoded = quote(storage_path, safe="/")
    target = target_dir / f"{int(item['seq']):020d}_{item['arquivo_id']}.xml"
    last_error: Exception | None = None
    for attempt in range(3):
        try:
            with requests.get(
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
            time.sleep(0.25 * (2**attempt))
    return {"item": item, "path": None, "size": 0, "error": str(last_error)[:1000]}


def _upload_zip(
    url: str, key: str, object_path: str, local_path: Path
) -> None:
    encoded = quote(object_path, safe="/")
    headers = _headers(key)
    headers.update({"Content-Type": "application/zip", "x-upsert": "true"})
    with local_path.open("rb") as body:
        response = requests.post(
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
    try:
        url, key, _ = _settings()
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
            )
        )
        if not job:
            return

        def keep_lease_alive() -> None:
            while not heartbeat_stop.wait(_heartbeat_interval):
                try:
                    ok = _rpc(url, key, "heartbeat_nfse_xml_zip_job", {
                        "p_job_id": job_id,
                        "p_worker_id": worker_id,
                        "p_lease_seconds": _lease_seconds,
                    })
                    if ok is not True:
                        raise RuntimeError("Lease perdido durante a geracao")
                except Exception as exc:
                    heartbeat_error.append(str(exc))
                    heartbeat_lost.set()
                    return

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
        checkpoint_size = _bounded_env_int("NFSE_ZIP_CHECKPOINT_SIZE", 25, 10, 50)
        compression_level = _bounded_env_int("NFSE_ZIP_COMPRESSION_LEVEL", 2, 0, 9)
        with zipfile.ZipFile(
            zip_path,
            mode="w",
            compression=zipfile.ZIP_DEFLATED,
            allowZip64=True,
            compresslevel=compression_level,
        ) as archive:
            while True:
                items = _rpc(
                    url,
                    key,
                    "claim_nfse_xml_zip_items",
                    {
                        "p_job_id": job_id,
                        "p_worker_id": worker_id,
                        "p_limit": _batch_size,
                    },
                ) or []
                if not items:
                    break

                for start in range(0, len(items), checkpoint_size):
                    wave = items[start : start + checkpoint_size]
                    if heartbeat_lost.is_set():
                        raise RuntimeError(heartbeat_error[-1] if heartbeat_error else "Lease perdido")
                    with ThreadPoolExecutor(
                        max_workers=download_concurrency,
                        thread_name_prefix="nfse-xml-download",
                    ) as executor:
                        downloaded = list(
                            executor.map(
                                lambda item: _download_to_temp(url, key, item, download_dir),
                                wave,
                            )
                        )
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
                            finally:
                                path.unlink(missing_ok=True)
                        else:
                            results.append({
                                "arquivo_id": item["arquivo_id"],
                                "ok": False,
                                "error": downloaded_item["error"],
                            })
                    _rpc(
                        url,
                        key,
                        "checkpoint_nfse_xml_zip_items",
                        {
                            "p_job_id": job_id,
                            "p_worker_id": worker_id,
                            "p_results": results,
                        },
                    )
        object_path = (
            f"{job['organizacao_id']}/{job['usuario_id']}/{job_id}/"
            "nfse_xmls.zip"
        )
        if heartbeat_lost.is_set():
            raise RuntimeError(heartbeat_error[-1] if heartbeat_error else "Lease perdido")
        _upload_zip(url, key, object_path, zip_path)
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
            },
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
                    },
                )
            except Exception:
                pass
    finally:
        heartbeat_stop.set()
        if heartbeat_thread and heartbeat_thread is not threading.current_thread():
            heartbeat_thread.join(timeout=2)
        if temp_dir:
            shutil.rmtree(temp_dir, ignore_errors=True)
        with _active_lock:
            _active.discard(job_id)


def install_nfse_zip_routes(app: FastAPI) -> None:
    @app.post("/nfse/xml-zip/dispatch")
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
