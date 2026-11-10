"""Worker de NF-e modelo 55 de saída. Não compartilha rota nem estado com a NFC-e."""

from __future__ import annotations

import os
import re
import shutil
import tempfile
import threading
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from typing import Any
from urllib.parse import urlparse
import certifi
import requests
from cryptography import x509
from cryptography.hazmat.primitives import hashes
from cryptography.hazmat.primitives.serialization import Encoding, NoEncryption, PrivateFormat, pkcs12
from fastapi import APIRouter, File, Form, HTTPException, UploadFile

from nfe55_saida_discovery import (
    avancar,
    cfg_da_chave,
    chave_artificial,
    extrair_xml_portal,
    interpretar_consulta,
    ler_xml_semente,
    montar_soap,
    proximo_aamm,
    xml_modelo_55,
)

URL_CONSULTA = "https://nfe.svrs.rs.gov.br/ws/NfeConsulta/NfeConsulta4.asmx"
URL_PORTAL = "https://dfe-portal.svrs.rs.gov.br/NFeSSL/DownloadXMLDFe"
SOAP_ACTION = "http://www.portalfiscal.inf.br/nfe/wsdl/NFeConsultaProtocolo4/nfeConsultaNF"
MAX_NUMEROS = 10000
JANELA_MES_SEGUINTE = 3
ICP_BRASIL_CA_PATH = Path(__file__).with_name("icp-brasil-v10.pem")
ICP_BRASIL_CA_SHA256 = "6E0BFF069A26994C15DE2C4888CC54AF84882E5495B7FBF66BE9CCFFEC7489F6"

router = APIRouter(prefix="/nfe55/saida-jobs", tags=["NF-e saída"])
_executor = ThreadPoolExecutor(max_workers=1, thread_name_prefix="nfe55-saida")
_vaga = threading.BoundedSemaphore(1)


def _ambiente() -> tuple[str, str]:
    url = os.getenv("SUPABASE_URL", "https://vqhtbyiecsxxprikpnus.supabase.co").rstrip("/")
    chave = os.getenv(
        "SUPABASE_ANON_KEY",
        "eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9.eyJpc3MiOiJzdXBhYmFzZSIsInJlZiI6InZxaHRieWllY3N4eHByaWtwbnVzIiwicm9sZSI6ImFub24iLCJpYXQiOjE3NjYwNjU3OTUsImV4cCI6MjA4MTY0MTc5NX0.aOvciVxs4NjCpHEYZXQziJy-0PQpcy4h-E2CbMZWKJ8",
    )
    parsed = urlparse(url)
    if parsed.scheme != "https" or parsed.hostname != "vqhtbyiecsxxprikpnus.supabase.co" or not chave:
        raise HTTPException(status_code=503, detail="Ambiente da NF-e de saída incompleto.")
    return url, chave


def _validar_execucao(run_id: str, token: str) -> None:
    url, chave = _ambiente()
    try:
        resposta = requests.post(
            f"{url}/rest/v1/rpc/claim_nfe_saida_run",
            headers={"apikey": chave, "Authorization": f"Bearer {chave}", "Content-Type": "application/json"},
            json={"p_run_id": run_id, "p_token": token},
            timeout=10,
        )
    except requests.RequestException as exc:
        raise HTTPException(status_code=503, detail="Não foi possível validar a execução de NF-e de saída.") from exc
    if resposta.status_code != 200 or resposta.json() is not True:
        raise HTTPException(status_code=401, detail="Execução de NF-e de saída inválida ou já utilizada.")


def _callback(run_id: str, token: str, evento: str, **dados: Any) -> bool:
    url, chave = _ambiente()
    try:
        resposta = requests.post(
            f"{url}/functions/v1/nfe-saida-download",
            headers={"apikey": chave, "Authorization": f"Bearer {chave}", "Content-Type": "application/json"},
            json={"action": "callback", "event": evento, "run_id": run_id, "token": token, **dados},
            timeout=20,
        )
    except requests.RequestException:
        return False
    if not resposta.ok:
        return False
    corpo = resposta.json() if resposta.content else {}
    return bool(corpo.get("cancel"))


def _pfx(dados: bytes, senha: str, pasta: Path) -> tuple[Path, Path]:
    chave, cert, extras = pkcs12.load_key_and_certificates(dados, senha.encode("utf-8") if senha else None)
    if chave is None or cert is None:
        raise RuntimeError("Não foi possível ler o certificado A1.")
    cert_path = pasta / "cert.pem"
    key_path = pasta / "key.pem"
    material = cert.public_bytes(Encoding.PEM)
    for extra in extras or []:
        material += extra.public_bytes(Encoding.PEM)
    cert_path.write_bytes(material)
    key_path.write_bytes(chave.private_bytes(Encoding.PEM, PrivateFormat.TraditionalOpenSSL, NoEncryption()))
    return cert_path, key_path


def _ca_bundle() -> str:
    """Raízes públicas mais a ICP-Brasil v10. A SVRS não fecha a cadeia só com o certifi."""
    try:
        certificate = x509.load_pem_x509_certificate(ICP_BRASIL_CA_PATH.read_bytes())
    except (OSError, ValueError) as exc:
        raise RuntimeError("Cadeia ICP-Brasil v10 ausente ou inválida.") from exc
    fingerprint = certificate.fingerprint(hashes.SHA256()).hex().upper()
    if fingerprint != ICP_BRASIL_CA_SHA256:
        raise RuntimeError("Fingerprint da cadeia ICP-Brasil v10 não confere.")
    bundle_path = Path(tempfile.gettempdir()) / "nexus_nfe55_svrs_ca.pem"
    if not bundle_path.exists():
        public_roots = Path(certifi.where()).read_bytes()
        separator = b"" if public_roots.endswith(b"\n") else b"\n"
        bundle_path.write_bytes(public_roots + separator + ICP_BRASIL_CA_PATH.read_bytes())
    return str(bundle_path)


def _consultar(sessao: requests.Session, cfg: dict, nnf: int, aamm: str) -> str:
    chave = chave_artificial(cfg, nnf, aamm)
    resposta = sessao.post(
        URL_CONSULTA,
        data=montar_soap(chave).encode("utf-8"),
        headers={
            "Content-Type": f'application/soap+xml; charset=utf-8; action="{SOAP_ACTION}"',
            "Accept": "application/soap+xml, text/xml, */*",
        },
        timeout=(20, 75),
        verify=_ca_bundle(),
    )
    resposta.raise_for_status()
    return resposta.text


def _baixar(cert_path: Path, key_path: Path, chave: str) -> str:
    with requests.Session() as sessao:
        sessao.cert = (str(cert_path), str(key_path))
        pagina = sessao.get(URL_PORTAL, timeout=45, verify=_ca_bundle())
        pagina.raise_for_status()
        campos: dict[str, str] = {}
        for tag in re.findall(r"<input\b[^>]*>", pagina.text, flags=re.I):
            nome = re.search(r"\bname=[\"']([^\"']+)[\"']", tag, flags=re.I)
            if not nome:
                continue
            valor = re.search(r"\bvalue=[\"']([^\"']*)[\"']", tag, flags=re.I)
            campos[nome.group(1)] = valor.group(1) if valor else ""
        campos.update({"sistema": "Nfe", "OrigemSite": "0", "Ambiente": "1", "ChaveAcessoDfe": chave})
        resposta = sessao.post(
            URL_PORTAL,
            data=campos,
            timeout=45,
            verify=_ca_bundle(),
            headers={"Referer": URL_PORTAL, "Content-Type": "application/x-www-form-urlencoded"},
        )
        resposta.raise_for_status()
    xml = extrair_xml_portal(resposta.text)
    if not xml or not xml_modelo_55(xml, chave):
        raise RuntimeError("O portal não devolveu o XML modelo 55 desta chave.")
    return xml


def _executar(run_id: str, token: str, semente: bytes, pfx: bytes, senha: str, opcoes: dict[str, Any]) -> None:
    pasta = Path(tempfile.mkdtemp(prefix="nfe55_saida_"))
    try:
        cert_path, key_path = _pfx(pfx, senha, pasta)
        cfg = cfg_da_chave(opcoes["chave"]) if opcoes.get("chave") else ler_xml_semente(semente)
        if opcoes.get("cnpj") and opcoes["cnpj"] != cfg["CNPJ"]:
            raise RuntimeError("A semente não pertence ao CNPJ da empresa.")
        with requests.Session() as sessao:
            sessao.cert = (str(cert_path), str(key_path))
            if opcoes.get("somente_chave"):
                xml = _baixar(cert_path, key_path, cfg["chave_semente"])
                _callback(run_id, token, "xml", chave=cfg["chave_semente"], aamm=cfg["AAMM"], nnf=cfg["nNF_semente"], xml=xml)
                _callback(run_id, token, "done", mensagem="Chave baixada.", consultadas=0, encontradas=1, salvas=1)
                return
            aamm = cfg["AAMM"]
            nnf = int(cfg["nNF_semente"]) + 1
            consecutivos = 0
            consultadas = 0
            encontradas: list[str] = []
            lacunas: list[dict[str, Any]] = []
            limite = min(int(opcoes.get("max_numeracoes") or 300), MAX_NUMEROS)
            parada = max(1, min(int(opcoes.get("stop_217") or 15), 100))
            while consultadas < limite:
                if _callback(run_id, token, "progress", mensagem=f"Consultando {aamm} nNF {nnf}", aamm=aamm, nnf=nnf, consultadas=consultadas, encontradas=len(encontradas)):
                    _callback(run_id, token, "done", mensagem="Busca cancelada.", consultadas=consultadas, encontradas=len(encontradas))
                    return
                atual = _consultar(sessao, cfg, nnf, aamm)
                consultadas += 1
                passo = avancar(cfg, aamm, nnf, consecutivos, parada, atual)
                if passo.encerrar:
                    recuperada = ""
                    competencia = proximo_aamm(aamm)
                    inicio = nnf - parada + 1
                    for numero in range(inicio, inicio + parada + JANELA_MES_SEGUINTE):
                        texto = _consultar(sessao, cfg, numero, competencia)
                        consultadas += 1
                        _codigo, _motivo, real = interpretar_consulta(texto, cfg, numero, competencia)
                        if real:
                            recuperada = real
                            break
                    if recuperada:
                        encontradas.append(recuperada)
                        time.sleep(60)
                        xml = _baixar(cert_path, key_path, recuperada)
                        _callback(run_id, token, "xml", chave=recuperada, aamm=recuperada[2:6], nnf=int(recuperada[25:34]), xml=xml)
                        aamm = recuperada[2:6]
                        nnf = int(recuperada[25:34]) + 1
                        consecutivos = 0
                        continue
                    lacunas.append({"aamm": aamm, "nnf": nnf})
                    break
                aamm, nnf, consecutivos = passo.aamm, passo.nnf, passo.consecutivos_217
                if passo.encontrada:
                    encontradas.append(passo.encontrada)
                    time.sleep(60)
                    xml = _baixar(cert_path, key_path, passo.encontrada)
                    _callback(run_id, token, "xml", chave=passo.encontrada, aamm=passo.encontrada[2:6], nnf=int(passo.encontrada[25:34]), xml=xml)
                elif passo.lacuna:
                    lacunas.append({"aamm": aamm, "nnf": nnf - 1})
                time.sleep(0.7)
        _callback(
            run_id, token, "done", mensagem="Busca de NF-e de saída concluída.",
            consultadas=consultadas, encontradas=len(encontradas), salvas=len(encontradas),
            aamm=aamm, nnf=nnf, lacunas=lacunas[-200:],
        )
    except Exception as exc:
        _callback(run_id, token, "error", erro=str(exc)[:500])
    finally:
        shutil.rmtree(pasta, ignore_errors=True)
        _vaga.release()


@router.post("/internal", status_code=202)
async def iniciar(
    run_id: str = Form(...),
    run_token: str = Form(...),
    certificado: UploadFile = File(...),
    senha: str = Form(...),
    xml_semente: UploadFile | None = File(None),
    chave: str = Form(""),
    cnpj: str = Form(""),
    stop_217: int = Form(15),
    max_numeracoes: int = Form(300),
    somente_chave: str = Form("false"),
) -> dict[str, str]:
    _validar_execucao(run_id, run_token)
    if not _vaga.acquire(blocking=False):
        raise HTTPException(status_code=429, detail="Já existe uma busca de NF-e de saída em andamento.")
    try:
        semente = await xml_semente.read() if xml_semente else b""
        pfx = await certificado.read()
        if not pfx:
            raise HTTPException(status_code=400, detail="Certificado ausente.")
        if chave:
            cfg_da_chave(chave)
        elif semente:
            ler_xml_semente(semente)
        else:
            raise HTTPException(status_code=400, detail="Informe a chave ou o XML semente modelo 55.")
        _executor.submit(_executar, run_id, run_token, semente, pfx, senha, {
            "chave": re.sub(r"\D", "", chave),
            "cnpj": re.sub(r"\D", "", cnpj),
            "stop_217": stop_217,
            "max_numeracoes": max_numeracoes,
            "somente_chave": somente_chave.lower() == "true",
        })
    except HTTPException:
        _vaga.release()
        raise
    except Exception as exc:
        _vaga.release()
        raise HTTPException(status_code=400, detail=str(exc)) from exc
    return {"id": run_id}
