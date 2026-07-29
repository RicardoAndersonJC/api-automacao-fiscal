"""DANFE completo de NF-e autorizada usando BrazilFiscalReport."""
from __future__ import annotations

import hmac
import os
import tempfile
from pathlib import Path
from xml.etree import ElementTree as ET

from fastapi import FastAPI, Header
from fastapi.responses import JSONResponse, Response


def _local(root: ET.Element, name: str) -> ET.Element | None:
    return next((node for node in root.iter() if node.tag.rsplit("}", 1)[-1] == name), None)


def _text(root: ET.Element, name: str) -> str:
    node = _local(root, name)
    return (node.text or "").strip() if node is not None else ""


def validate_authorized_nfe(xml_text: str, expected_key: str) -> None:
    if "<resNFe" in xml_text or ":resNFe" in xml_text:
        raise ValueError("Resumo resNFe nao pode gerar DANFE")
    try:
        root = ET.fromstring(xml_text)
    except ET.ParseError as exc:
        raise ValueError("XML da NF-e invalido") from exc
    if root.tag.rsplit("}", 1)[-1] != "nfeProc":
        raise ValueError("DANFE exige XML autorizado nfeProc")
    inf_nfe = _local(root, "infNFe")
    inf_prot = _local(root, "infProt")
    if inf_nfe is None or inf_prot is None:
        raise ValueError("NF-e ou protocolo ausente")
    key_id = (inf_nfe.attrib.get("Id") or "").removeprefix("NFe")
    protocol_key = _text(inf_prot, "chNFe")
    if not expected_key.isdigit() or len(expected_key) != 44:
        raise ValueError("Chave esperada invalida")
    if key_id != expected_key or protocol_key != expected_key:
        raise ValueError("Chave divergente entre arquivo, NF-e e protocolo")
    if _text(inf_nfe, "mod") != "55":
        raise ValueError("Somente NF-e modelo 55 gera DANFE")
    if _text(inf_prot, "cStat") not in {"100", "150"} or not _text(inf_prot, "nProt"):
        raise ValueError("NF-e sem protocolo de autorizacao valido")


def render_danfe(xml_text: str, expected_key: str) -> bytes:
    validate_authorized_nfe(xml_text, expected_key)
    try:
        from brazilfiscalreport.danfe import Danfe
    except ImportError as exc:
        raise RuntimeError("BrazilFiscalReport==1.0.1 nao instalado") from exc
    with tempfile.TemporaryDirectory(prefix="nfe_danfe_") as directory:
        output = Path(directory) / f"{expected_key}.pdf"
        Danfe(xml=xml_text).output(str(output))
        content = output.read_bytes()
    if len(content) < 100 or not content.startswith(b"%PDF-"):
        raise RuntimeError("Biblioteca retornou DANFE invalido")
    return content


def install_nfe_danfe_routes(app: FastAPI) -> None:
    @app.post("/nfe/danfe/render")
    async def render(
        payload: dict[str, str],
        x_nfe_danfe_secret: str | None = Header(default=None),
    ):
        expected = os.environ.get("NFE_DANFE_INTERNAL_SECRET", "")
        if not expected or not x_nfe_danfe_secret or not hmac.compare_digest(expected, x_nfe_danfe_secret):
            return JSONResponse({"success": False, "error": "Nao autorizado"}, status_code=401)
        try:
            content = render_danfe(str(payload.get("xml") or ""), str(payload.get("chave") or ""))
            return Response(content, media_type="application/pdf", headers={"Cache-Control": "no-store"})
        except ValueError as exc:
            return JSONResponse({"success": False, "error": str(exc)}, status_code=422)
        except Exception as exc:
            return JSONResponse({"success": False, "error": str(exc)}, status_code=500)
