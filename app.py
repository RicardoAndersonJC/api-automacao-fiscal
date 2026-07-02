import base64
import gzip
import io
import json
import os
import re
import tempfile
import threading
import time
import zipfile
from concurrent.futures import ThreadPoolExecutor, as_completed
from urllib.parse import quote
from datetime import datetime
from typing import Any
from xml.etree import ElementTree as ET

import requests
from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.serialization import pkcs12
from fastapi import FastAPI, File, Form, Header, Request, Response, UploadFile
from fastapi.middleware.cors import CORSMiddleware
from fastapi.responses import JSONResponse, StreamingResponse
from lxml import etree
from signxml import XMLSigner, methods

NFE_NS = "http://www.portalfiscal.inf.br/nfe"
SOAP12_NS = "http://www.w3.org/2003/05/soap-envelope"
WSDL_DIST_NS = "http://www.portalfiscal.inf.br/nfe/wsdl/NFeDistribuicaoDFe"
WSDL_EVENTO_NS = "http://www.portalfiscal.inf.br/nfe/wsdl/RecepcaoEvento4"

TP_EVENTO_CIENCIA = "210210"
SCHEMA_RESUMO_PREFIX = "resNFe"
SCHEMA_COMPLETO_PREFIXES = ("procNFe", "NFe")
SCHEMA_EVENTO_PREFIXES = ("procEventoNFe", "resEvento")

ENDPOINT_DIST = {
    "homologacao": "https://hom1.nfe.fazenda.gov.br/NFeDistribuicaoDFe/NFeDistribuicaoDFe.asmx",
    "producao": "https://www1.nfe.fazenda.gov.br/NFeDistribuicaoDFe/NFeDistribuicaoDFe.asmx",
}

ENDPOINT_EVENTO = {
    "homologacao": "https://hom1.nfe.fazenda.gov.br/RecepcaoEvento4/RecepcaoEvento4.asmx",
    "producao": "https://www.nfe.fazenda.gov.br/NFeRecepcaoEvento4/NFeRecepcaoEvento4.asmx",
}

BASE_DIR = os.path.abspath("./dados")
os.makedirs(BASE_DIR, exist_ok=True)

app = FastAPI()
app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"],
    allow_credentials=False,
    allow_methods=["*"],
    allow_headers=["*"],
)


@app.middleware("http")
async def ensure_cors_headers(request: Request, call_next):
    origin = request.headers.get("origin") or "*"
    if request.method == "OPTIONS":
        response = Response(status_code=204)
    else:
        response = await call_next(request)
    response.headers["Access-Control-Allow-Origin"] = origin
    response.headers["Access-Control-Allow-Methods"] = "GET, POST, PUT, PATCH, DELETE, OPTIONS"
    response.headers["Access-Control-Allow-Headers"] = "authorization, content-type, apikey, x-client-info"
    response.headers["Access-Control-Max-Age"] = "86400"
    response.headers["Vary"] = "Origin"
    return response


def limpar_cnpj(cnpj: str) -> str:
    return re.sub(r"\D", "", cnpj or "")


def garantir_cnpj(cnpj: str) -> str:
    cnpj_limpo = limpar_cnpj(cnpj)
    if len(cnpj_limpo) != 14:
        raise ValueError(f"CNPJ invÃ¡lido: {cnpj}")
    return cnpj_limpo


def garantir_competencia(comp: str) -> str:
    comp = (comp or "").strip()
    if not re.fullmatch(r"\d{4}-\d{2}", comp):
        raise ValueError("CompetÃªncia invÃ¡lida. Use YYYY-MM.")
    return comp


def garantir_ambiente(ambiente: str) -> str:
    ambiente = (ambiente or "").strip().lower()
    if ambiente not in ENDPOINT_DIST:
        raise ValueError("Ambiente invÃ¡lido. Use homologacao ou producao.")
    return ambiente


def garantir_bool(valor: Any) -> bool:
    if isinstance(valor, bool):
        return valor
    return str(valor).strip().lower() in {"1", "true", "t", "sim", "yes", "on"}


def carregar_json(caminho: str, padrao: Any) -> Any:
    if not os.path.exists(caminho):
        return padrao
    with open(caminho, "r", encoding="utf-8") as f:
        return json.load(f)


def salvar_json(caminho: str, dados: Any) -> None:
    os.makedirs(os.path.dirname(caminho), exist_ok=True)
    with open(caminho, "w", encoding="utf-8") as f:
        json.dump(dados, f, ensure_ascii=False, indent=2)


def caminho_nsu(cnpj: str, ambiente: str) -> str:
    return os.path.join(BASE_DIR, "estado", f"nsu_{ambiente}_{cnpj}.json")


def caminho_manifestadas(cnpj: str, ambiente: str) -> str:
    return os.path.join(BASE_DIR, "estado", f"manifestadas_{ambiente}_{cnpj}.json")


def carregar_nsu(cnpj: str, ambiente: str) -> str:
    dados = carregar_json(caminho_nsu(cnpj, ambiente), {"ult_nsu": "000000000000000"})
    return str(dados.get("ult_nsu", "000000000000000")).zfill(15)


def salvar_nsu(cnpj: str, ambiente: str, nsu: str, competencia: str | None = None, total_documentos: int | None = None) -> None:
    atual = carregar_json(caminho_nsu(cnpj, ambiente), {})
    atual.update(
        {
            "ult_nsu": str(nsu).zfill(15),
            "last_competencia": competencia,
            "total_documentos": total_documentos or atual.get("total_documentos", 0),
            "updated_at": datetime.now().isoformat(),
            "ambiente": ambiente,
        }
    )
    salvar_json(caminho_nsu(cnpj, ambiente), atual)


def carregar_manifestadas(cnpj: str, ambiente: str) -> set[str]:
    return set(carregar_json(caminho_manifestadas(cnpj, ambiente), []))


def salvar_manifestadas(cnpj: str, ambiente: str, dados: set[str]) -> None:
    salvar_json(caminho_manifestadas(cnpj, ambiente), sorted(dados))


def extrair_competencia_de_data(texto_data: str | None) -> str | None:
    if not texto_data:
        return None
    texto = texto_data.strip()
    m = re.match(r"^(\d{4})-(\d{2})-\d{2}", texto)
    if m:
        return f"{m.group(1)}-{m.group(2)}"
    m = re.match(r"^(\d{2})/(\d{2})/(\d{4})", texto)
    if m:
        return f"{m.group(3)}-{m.group(2)}"
    m = re.match(r"^(\d{4})(\d{2})(\d{2})$", texto)
    if m:
        return f"{m.group(1)}-{m.group(2)}"
    return None


def mesmo_mes(texto_data: str | None, competencia: str) -> bool:
    return extrair_competencia_de_data(texto_data) == competencia


def normalizar_nome_arquivo(nome: str) -> str:
    nome = re.sub(r'[<>:"/\\|?*]+', "_", nome or "")
    nome = re.sub(r"\s+", " ", nome).strip()
    return nome or "arquivo.xml"


def montar_xml_dist(cnpj: str, ult_nsu: str, cuf: str, ambiente: str) -> str:
    tp_amb = "1" if ambiente == "producao" else "2"
    return f"""<distDFeInt xmlns="{NFE_NS}" versao="1.01">
    <tpAmb>{tp_amb}</tpAmb>
    <cUFAutor>{cuf}</cUFAutor>
    <CNPJ>{cnpj}</CNPJ>
    <distNSU>
        <ultNSU>{str(ult_nsu).zfill(15)}</ultNSU>
    </distNSU>
</distDFeInt>"""


def montar_envelope_dist(xml: str) -> str:
    return f"""<?xml version="1.0" encoding="utf-8"?>
<soap12:Envelope xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
                 xmlns:xsd="http://www.w3.org/2001/XMLSchema"
                 xmlns:soap12="{SOAP12_NS}">
  <soap12:Body>
    <nfeDistDFeInteresse xmlns="{WSDL_DIST_NS}">
      <nfeDadosMsg xmlns="{WSDL_DIST_NS}">
        {xml}
      </nfeDadosMsg>
    </nfeDistDFeInteresse>
  </soap12:Body>
</soap12:Envelope>"""


def montar_envelope_evento(xml: str) -> str:
    return f"""<?xml version="1.0" encoding="utf-8"?>
<soap12:Envelope xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
                 xmlns:xsd="http://www.w3.org/2001/XMLSchema"
                 xmlns:soap12="{SOAP12_NS}">
  <soap12:Body>
    <nfeRecepcaoEventoNF xmlns="{WSDL_EVENTO_NS}">
      <nfeDadosMsg xmlns="{WSDL_EVENTO_NS}">
        {xml}
      </nfeDadosMsg>
    </nfeRecepcaoEventoNF>
  </soap12:Body>
</soap12:Envelope>"""


def descompactar_doczip(texto_b64: str) -> str:
    return gzip.decompress(base64.b64decode(texto_b64)).decode("utf-8")


def extrair_ret_dist(xml_soap: str) -> ET.Element:
    root = ET.fromstring(xml_soap)
    ret = root.find(".//{http://www.portalfiscal.inf.br/nfe}retDistDFeInt")
    if ret is not None:
        return ret

    for elem in root.iter():
        if elem.text and "<retDistDFeInt" in elem.text:
            return ET.fromstring(elem.text.strip())

    raise RuntimeError("NÃ£o foi possÃ­vel localizar retDistDFeInt no retorno SOAP.")


def resumir_documento(xml_doc: str, schema: str) -> dict[str, Any]:
    try:
        root = ET.fromstring(xml_doc)
    except Exception:
        return {
            "tipo": "xml_invalido",
            "schema_categoria": "desconhecido",
            "chave": None,
            "emitente_cnpj": None,
            "destinatario_cnpj": None,
            "dh_emi": None,
            "valor": None,
            "modelo": None,
        }

    tag = root.tag.split("}")[-1]
    categoria = "outro"
    if schema.startswith(SCHEMA_RESUMO_PREFIX):
        categoria = "resumo"
    elif schema.startswith(SCHEMA_COMPLETO_PREFIXES):
        categoria = "completo"
    elif schema.startswith(SCHEMA_EVENTO_PREFIXES):
        categoria = "evento"

    if tag == "resNFe":
        return {
            "tipo": "resNFe",
            "schema_categoria": categoria,
            "chave": root.findtext(f"{{{NFE_NS}}}chNFe"),
            "emitente_cnpj": root.findtext(f"{{{NFE_NS}}}CNPJ"),
            "destinatario_cnpj": None,
            "dh_emi": root.findtext(f"{{{NFE_NS}}}dhEmi"),
            "valor": root.findtext(f"{{{NFE_NS}}}vNF"),
            "modelo": "55",
        }

    inf_nfe = root.find(f".//{{{NFE_NS}}}infNFe")
    if inf_nfe is not None:
        ide = inf_nfe.find(f"{{{NFE_NS}}}ide")
        emit = inf_nfe.find(f"{{{NFE_NS}}}emit")
        dest = inf_nfe.find(f"{{{NFE_NS}}}dest")
        total = inf_nfe.find(f".//{{{NFE_NS}}}ICMSTot")

        chave = None
        inf_id = inf_nfe.attrib.get("Id")
        if inf_id and inf_id.startswith("NFe"):
            chave = inf_id[3:]

        return {
            "tipo": "procNFe/NFe",
            "schema_categoria": categoria,
            "chave": chave,
            "emitente_cnpj": emit.findtext(f"{{{NFE_NS}}}CNPJ") if emit is not None else None,
            "destinatario_cnpj": (
                dest.findtext(f"{{{NFE_NS}}}CNPJ") or dest.findtext(f"{{{NFE_NS}}}CPF")
            ) if dest is not None else None,
            "dh_emi": ide.findtext(f"{{{NFE_NS}}}dhEmi") or ide.findtext(f"{{{NFE_NS}}}dEmi") if ide is not None else None,
            "valor": total.findtext(f"{{{NFE_NS}}}vNF") if total is not None else None,
            "modelo": ide.findtext(f"{{{NFE_NS}}}mod") if ide is not None else None,
        }

    if tag in {"procEventoNFe", "resEvento"}:
        return {
            "tipo": tag,
            "schema_categoria": categoria,
            "chave": root.findtext(f".//{{{NFE_NS}}}chNFe"),
            "emitente_cnpj": None,
            "destinatario_cnpj": root.findtext(f".//{{{NFE_NS}}}CNPJ"),
            "dh_emi": root.findtext(f".//{{{NFE_NS}}}dhEvento") or root.findtext(f".//{{{NFE_NS}}}dhRegEvento"),
            "valor": None,
            "modelo": None,
        }

    return {
        "tipo": tag,
        "schema_categoria": categoria,
        "chave": root.findtext(f".//{{{NFE_NS}}}chNFe"),
        "emitente_cnpj": root.findtext(f".//{{{NFE_NS}}}CNPJ"),
        "destinatario_cnpj": None,
        "dh_emi": root.findtext(f".//{{{NFE_NS}}}dhEmi"),
        "valor": root.findtext(f".//{{{NFE_NS}}}vNF"),
        "modelo": None,
    }


def extrair_certificado(caminho_pfx: str, senha: str) -> tuple[str, str, bytes, bytes]:
    with open(caminho_pfx, "rb") as f:
        pfx_data = f.read()

    private_key, certificate, additional_certificates = pkcs12.load_key_and_certificates(
        pfx_data,
        senha.encode("utf-8"),
    )

    if private_key is None or certificate is None:
        raise ValueError("NÃ£o foi possÃ­vel extrair certificado e chave do PFX.")

    cert_pem = certificate.public_bytes(serialization.Encoding.PEM)
    if additional_certificates:
        for cert in additional_certificates:
            cert_pem += cert.public_bytes(serialization.Encoding.PEM)

    key_pem = private_key.private_bytes(
        encoding=serialization.Encoding.PEM,
        format=serialization.PrivateFormat.TraditionalOpenSSL,
        encryption_algorithm=serialization.NoEncryption(),
    )

    cert_tmp = tempfile.NamedTemporaryFile(delete=False, suffix=".pem")
    key_tmp = tempfile.NamedTemporaryFile(delete=False, suffix=".pem")
    cert_tmp.write(cert_pem)
    cert_tmp.close()
    key_tmp.write(key_pem)
    key_tmp.close()
    return cert_tmp.name, key_tmp.name, cert_pem, key_pem


def assinar_xml(xml_str: str, cert_pem: bytes, key_pem: bytes) -> str:
    root = etree.fromstring(xml_str.encode("utf-8"))
    inf_evento = root.find(f".//{{{NFE_NS}}}infEvento")
    if inf_evento is None:
        raise ValueError("infEvento nÃ£o encontrado para assinatura.")

    evento = inf_evento.getparent()
    if evento is None:
        raise ValueError("evento nÃ£o encontrado para assinatura.")

    signer = XMLSigner(
        method=methods.enveloped,
        signature_algorithm="rsa-sha256",
        digest_algorithm="sha256",
        c14n_algorithm="http://www.w3.org/TR/2001/REC-xml-c14n-20010315",
    )
    signed_evento = signer.sign(
        evento,
        key=key_pem,
        cert=cert_pem,
        reference_uri=f"#{inf_evento.attrib['Id']}",
        id_attribute="Id",
    )
    root.remove(evento)
    root.append(signed_evento)
    return etree.tostring(root, encoding="utf-8").decode("utf-8")


def gerar_manifestacao(cnpj: str, chave: str, ambiente: str) -> str:
    tp_amb = "1" if ambiente == "producao" else "2"
    dh_evento = datetime.now().astimezone().isoformat(timespec="seconds")
    return f"""<envEvento xmlns="{NFE_NS}" versao="1.00">
  <idLote>{str(int(time.time() * 1000))[:15]}</idLote>
  <evento versao="1.00">
    <infEvento Id="ID{TP_EVENTO_CIENCIA}{chave}01">
      <cOrgao>91</cOrgao>
      <tpAmb>{tp_amb}</tpAmb>
      <CNPJ>{cnpj}</CNPJ>
      <chNFe>{chave}</chNFe>
      <dhEvento>{dh_evento}</dhEvento>
      <tpEvento>{TP_EVENTO_CIENCIA}</tpEvento>
      <nSeqEvento>1</nSeqEvento>
      <verEvento>1.00</verEvento>
      <detEvento versao="1.00">
        <descEvento>Ciencia da Operacao</descEvento>
      </detEvento>
    </infEvento>
  </evento>
</envEvento>"""


def manifestar(session: requests.Session, cert_pem: bytes, key_pem: bytes, cnpj: str, chave: str, ambiente: str) -> dict[str, Any]:
    try:
        xml = gerar_manifestacao(cnpj, chave, ambiente)
        xml_assinado = assinar_xml(xml, cert_pem, key_pem)
        envelope = montar_envelope_evento(xml_assinado)

        response = session.post(
            ENDPOINT_EVENTO[ambiente],
            data=envelope.encode("utf-8"),
            headers={"Content-Type": "application/soap+xml; charset=utf-8"},
            timeout=60,
        )
        response.raise_for_status()

        root = ET.fromstring(response.text)
        cstat = root.findtext(f".//{{{NFE_NS}}}cStat")
        xmotivo = root.findtext(f".//{{{NFE_NS}}}xMotivo")
        ok = cstat in {"128", "135", "136", "155"}
        return {"chave": chave, "ok": ok, "cStat": cstat, "xMotivo": xmotivo}
    except Exception as exc:
        return {"chave": chave, "ok": False, "cStat": None, "xMotivo": str(exc)}


def salvar_documento(cnpj: str, competencia: str, doc: dict[str, Any], resumo: dict[str, Any]) -> str | None:
    chave = resumo.get("chave")
    if not chave:
        return None

    pasta = os.path.join(BASE_DIR, cnpj, competencia)
    os.makedirs(pasta, exist_ok=True)

    categoria = resumo.get("schema_categoria") or "outro"
    nome = normalizar_nome_arquivo(f"{chave}_{categoria}.xml")
    caminho = os.path.join(pasta, nome)
    if not os.path.exists(caminho):
        with open(caminho, "w", encoding="utf-8") as f:
            f.write(doc["xml"])
    return caminho


def listar_arquivos_zip(cnpj: str, competencia: str) -> list[str]:
    pasta = os.path.join(BASE_DIR, cnpj, competencia)
    if not os.path.isdir(pasta):
        return []
    return sorted(
        [
            os.path.abspath(os.path.join(pasta, nome))
            for nome in os.listdir(pasta)
            if nome.lower().endswith(".xml")
        ]
    )


def processar_consulta(
    ambiente: str,
    caminho_pfx: str,
    senha: str,
    cnpj: str,
    cuf: str,
    max_lotes: int,
    competencia: str,
    somente_completas: bool,
    manifestar_ciencia: bool,
    start_nsu: str | None = None,
    filtrar_competencia: bool = True,
) -> dict[str, Any]:
    ambiente = garantir_ambiente(ambiente)
    cnpj = garantir_cnpj(cnpj)
    competencia = garantir_competencia(competencia)

    cert_path = None
    key_path = None
    session = None

    ult_nsu_inicial = str(start_nsu).zfill(15) if start_nsu else carregar_nsu(cnpj, ambiente)
    ult_nsu_atual = ult_nsu_inicial
    manifestadas = carregar_manifestadas(cnpj, ambiente)

    lotes_consultados = 0
    docs_recebidos = 0
    resumos = 0
    completos = 0
    eventos = 0
    manifestados = 0
    erros_manifestacao = 0
    ignorados_competencia = 0
    documentos: list[dict[str, Any]] = []
    manifestacoes: list[dict[str, Any]] = []
    salvos: list[str] = []
    cstat_final = None
    xmotivo_final = None
    max_nsu_final = None

    try:
        cert_path, key_path, cert_pem, key_pem = extrair_certificado(caminho_pfx, senha)
        session = requests.Session()
        session.cert = (cert_path, key_path)
        session.verify = True

        resumo_docs_para_manifestar: list[tuple[str, dict[str, Any]]] = []

        for _ in range(max_lotes):
            lotes_consultados += 1
            xml_req = montar_xml_dist(cnpj, ult_nsu_atual, cuf, ambiente)
            envelope = montar_envelope_dist(xml_req)

            response = session.post(
                ENDPOINT_DIST[ambiente],
                data=envelope.encode("utf-8"),
                headers={"Content-Type": "application/soap+xml; charset=utf-8"},
                timeout=60,
            )
            response.raise_for_status()

            ret = extrair_ret_dist(response.text)
            cstat_final = ret.findtext(f"{{{NFE_NS}}}cStat", default="")
            xmotivo_final = ret.findtext(f"{{{NFE_NS}}}xMotivo", default="")
            ult_nsu_resp = ret.findtext(f"{{{NFE_NS}}}ultNSU", default=ult_nsu_atual)
            max_nsu_final = ret.findtext(f"{{{NFE_NS}}}maxNSU", default=ult_nsu_resp)
            ult_nsu_atual = ult_nsu_resp

            lote = ret.find(f"{{{NFE_NS}}}loteDistDFeInt")
            doc_zips = lote.findall(f"{{{NFE_NS}}}docZip") if lote is not None else []
            docs_recebidos += len(doc_zips)

            for doc_zip in doc_zips:
                try:
                    xml_doc = descompactar_doczip(doc_zip.text or "")
                except Exception:
                    documentos.append(
                        {
                            "nsu": doc_zip.attrib.get("NSU"),
                            "tipo": "erro",
                            "chave": None,
                            "competencia": None,
                            "acao": "ignorado",
                            "motivo": "Falha ao descompactar docZip",
                        }
                    )
                    continue

                schema = doc_zip.attrib.get("schema", "")
                resumo = resumir_documento(xml_doc, schema)
                categoria = resumo.get("schema_categoria")
                chave = resumo.get("chave")
                comp_doc = extrair_competencia_de_data(resumo.get("dh_emi"))

                if resumo.get("modelo") not in (None, "55"):
                    documentos.append(
                        {
                            "nsu": doc_zip.attrib.get("NSU"),
                            "tipo": categoria,
                            "chave": chave,
                            "competencia": comp_doc,
                            "acao": "ignorado",
                            "motivo": "Modelo diferente de 55",
                        }
                    )
                    continue

                if filtrar_competencia and not mesmo_mes(resumo.get("dh_emi"), competencia):
                    ignorados_competencia += 1
                    documentos.append(
                        {
                            "nsu": doc_zip.attrib.get("NSU"),
                            "tipo": categoria,
                            "chave": chave,
                            "competencia": comp_doc,
                            "acao": "ignorado",
                            "motivo": "CompetÃªncia diferente da selecionada",
                        }
                    )
                    continue

                doc_info = {"xml": xml_doc, "schema": schema}

                if categoria == "resumo":
                    resumos += 1
                    documentos.append(
                        {
                            "nsu": doc_zip.attrib.get("NSU"),
                            "tipo": categoria,
                            "chave": chave,
                            "competencia": comp_doc,
                            "acao": "resumo_encontrado",
                            "motivo": None,
                        }
                    )
                    if manifestar_ciencia and chave and chave not in manifestadas:
                        resumo_docs_para_manifestar.append((chave, {"nsu": doc_zip.attrib.get("NSU"), "competencia": comp_doc}))
                    elif not somente_completas:
                        competencia_destino = comp_doc or competencia
                        caminho = salvar_documento(cnpj, competencia_destino, doc_info, resumo)
                        if caminho:
                            salvos.append(caminho)
                    continue

                if categoria == "completo":
                    completos += 1
                    competencia_destino = comp_doc or competencia
                    caminho = salvar_documento(cnpj, competencia_destino, doc_info, resumo)
                    if caminho:
                        salvos.append(caminho)
                    documentos.append(
                        {
                            "nsu": doc_zip.attrib.get("NSU"),
                            "tipo": categoria,
                            "chave": chave,
                            "competencia": comp_doc,
                            "acao": "salvo",
                            "motivo": None,
                        }
                    )
                    continue

                if categoria == "evento":
                    eventos += 1
                if not somente_completas:
                    competencia_destino = comp_doc or competencia
                    caminho = salvar_documento(cnpj, competencia_destino, doc_info, resumo)
                    if caminho:
                        salvos.append(caminho)
                documentos.append(
                    {
                        "nsu": doc_zip.attrib.get("NSU"),
                        "tipo": categoria,
                        "chave": chave,
                        "competencia": comp_doc,
                        "acao": "ignorado" if somente_completas else "salvo",
                        "motivo": None if not somente_completas else "NÃ£o Ã© XML completo",
                    }
                )

            salvar_nsu(cnpj, ambiente, ult_nsu_atual, competencia=competencia, total_documentos=docs_recebidos)

            if cstat_final == "137" or ult_nsu_atual == max_nsu_final:
                break

        if manifestar_ciencia and resumo_docs_para_manifestar:
            for chave, meta in resumo_docs_para_manifestar:
                ret = manifestar(session, cert_pem, key_pem, cnpj, chave, ambiente)
                manifestacoes.append(ret)
                if ret.get("ok"):
                    manifestados += 1
                    manifestadas.add(chave)
                    documentos.append(
                        {
                            "nsu": meta.get("nsu"),
                            "tipo": "manifestacao",
                            "chave": chave,
                            "competencia": meta.get("competencia"),
                            "acao": "manifestado",
                            "motivo": ret.get("xMotivo"),
                        }
                    )
                else:
                    erros_manifestacao += 1
                    documentos.append(
                        {
                            "nsu": meta.get("nsu"),
                            "tipo": "manifestacao",
                            "chave": chave,
                            "competencia": meta.get("competencia"),
                            "acao": "erro_manifestacao",
                            "motivo": ret.get("xMotivo"),
                        }
                    )

            if manifestados > 0:
                time.sleep(8)
                for _ in range(2):
                    lotes_consultados += 1
                    xml_req = montar_xml_dist(cnpj, ult_nsu_atual, cuf, ambiente)
                    envelope = montar_envelope_dist(xml_req)

                    response = session.post(
                        ENDPOINT_DIST[ambiente],
                        data=envelope.encode("utf-8"),
                        headers={"Content-Type": "application/soap+xml; charset=utf-8"},
                        timeout=60,
                    )
                    response.raise_for_status()

                    ret = extrair_ret_dist(response.text)
                    cstat_final = ret.findtext(f"{{{NFE_NS}}}cStat", default="")
                    xmotivo_final = ret.findtext(f"{{{NFE_NS}}}xMotivo", default="")
                    ult_nsu_resp = ret.findtext(f"{{{NFE_NS}}}ultNSU", default=ult_nsu_atual)
                    max_nsu_final = ret.findtext(f"{{{NFE_NS}}}maxNSU", default=ult_nsu_resp)
                    ult_nsu_atual = ult_nsu_resp

                    lote = ret.find(f"{{{NFE_NS}}}loteDistDFeInt")
                    doc_zips = lote.findall(f"{{{NFE_NS}}}docZip") if lote is not None else []
                    docs_recebidos += len(doc_zips)

                    novos_completos = 0
                    for doc_zip in doc_zips:
                        xml_doc = descompactar_doczip(doc_zip.text or "")
                        schema = doc_zip.attrib.get("schema", "")
                        resumo = resumir_documento(xml_doc, schema)
                        categoria = resumo.get("schema_categoria")
                        chave = resumo.get("chave")
                        comp_doc = extrair_competencia_de_data(resumo.get("dh_emi"))

                        if categoria != "completo":
                            continue
                        if filtrar_competencia and not mesmo_mes(resumo.get("dh_emi"), competencia):
                            continue

                        doc_info = {"xml": xml_doc, "schema": schema}
                        competencia_destino = comp_doc or competencia
                        caminho = salvar_documento(cnpj, competencia_destino, doc_info, resumo)
                        if caminho and caminho not in salvos:
                            salvos.append(caminho)
                            completos += 1
                            novos_completos += 1
                            documentos.append(
                                {
                                    "nsu": doc_zip.attrib.get("NSU"),
                                    "tipo": categoria,
                                    "chave": chave,
                                    "competencia": comp_doc,
                                    "acao": "salvo_pos_manifestacao",
                                    "motivo": None,
                                }
                            )

                    salvar_nsu(cnpj, ambiente, ult_nsu_atual, competencia=competencia, total_documentos=docs_recebidos)
                    if novos_completos == 0 or cstat_final == "137" or ult_nsu_atual == max_nsu_final:
                        break

        salvar_manifestadas(cnpj, ambiente, manifestadas)

        arquivos = listar_arquivos_zip(cnpj, competencia) if filtrar_competencia else salvos
        return {
            "success": True,
            "cStat": cstat_final,
            "xMotivo": xmotivo_final,
            "ult_nsu_inicial": ult_nsu_inicial,
            "ult_nsu_final": ult_nsu_atual,
            "max_nsu": max_nsu_final,
            "lotes_consultados": lotes_consultados,
            "docs_recebidos": docs_recebidos,
            "resumos": resumos,
            "completos": completos,
            "eventos": eventos,
            "manifestados": manifestados,
            "erros_manifestacao": erros_manifestacao,
            "ignorados_competencia": ignorados_competencia,
            "salvos": len(arquivos),
            "arquivos": arquivos,
            "manifestacoes": manifestacoes,
            "documentos": documentos,
        }
    finally:
        if session is not None:
            session.close()
        for path in (cert_path, key_path, caminho_pfx):
            try:
                if path and os.path.exists(path) and path != caminho_pfx:
                    os.remove(path)
            except Exception:
                pass



# ============================================================================
# NFS-e Nacional ZIP worker
# ============================================================================

NFSE_ZIP_BUCKET = "fiscal-files"
NFSE_ZIP_PREFIX = "nfse-zips"
NFSE_ZIP_PAGE_SIZE = 1000
NFSE_ZIP_MAX_FILES = 200000
NFSE_ZIP_WORKERS = int(os.getenv("NFSE_ZIP_WORKERS", "32"))
NFSE_ZIP_PROGRESS_EVERY = int(os.getenv("NFSE_ZIP_PROGRESS_EVERY", "100"))


def nfse_now_iso() -> str:
    return datetime.utcnow().isoformat() + "Z"


def nfse_supabase_config() -> tuple[str, str]:
    url = (os.getenv("SUPABASE_URL") or "").rstrip("/")
    service_key = os.getenv("SUPABASE_SERVICE_ROLE_KEY") or os.getenv("SUPABASE_SERVICE_KEY") or ""
    if not url or not service_key:
        raise RuntimeError("Configure SUPABASE_URL e SUPABASE_SERVICE_ROLE_KEY na API.")
    return url, service_key


def nfse_supabase_headers(content_type: str | None = "application/json") -> dict[str, str]:
    _, service_key = nfse_supabase_config()
    headers = {
        "apikey": service_key,
        "Authorization": f"Bearer {service_key}",
    }
    if content_type:
        headers["Content-Type"] = content_type
    return headers


def nfse_rest_request(method: str, path: str, **kwargs) -> requests.Response:
    url, _ = nfse_supabase_config()
    resp = requests.request(method, f"{url}{path}", timeout=kwargs.pop("timeout", 60), **kwargs)
    if resp.status_code >= 400:
        raise RuntimeError(f"Supabase {method} {path} retornou {resp.status_code}: {resp.text[:500]}")
    return resp


def nfse_update_execucao(execucao_id: str, updates: dict[str, Any]) -> None:
    headers = nfse_supabase_headers()
    headers["Prefer"] = "return=minimal"
    nfse_rest_request(
        "PATCH",
        "/rest/v1/execucoes",
        params={"id": f"eq.{execucao_id}"},
        headers=headers,
        json=updates,
    )


def nfse_get_execucao(execucao_id: str) -> dict[str, Any] | None:
    resp = nfse_rest_request(
        "GET",
        "/rest/v1/execucoes",
        params={"select": "status,progresso,parametros", "id": f"eq.{execucao_id}", "limit": "1"},
        headers=nfse_supabase_headers(None),
    )
    data = resp.json()
    return data[0] if data else None


def nfse_auth_user_id(authorization: str | None) -> str:
    token = (authorization or "").replace("Bearer", "", 1).strip()
    if not token:
        raise PermissionError("Autenticacao necessaria.")
    url, service_key = nfse_supabase_config()
    resp = requests.get(
        f"{url}/auth/v1/user",
        headers={"apikey": service_key, "Authorization": f"Bearer {token}"},
        timeout=30,
    )
    if resp.status_code >= 400:
        raise PermissionError("Usuario invalido ou sessao expirada.")
    user_id = (resp.json() or {}).get("id")
    if not user_id:
        raise PermissionError("Usuario invalido.")
    return user_id


def nfse_require_org_access(authorization: str | None, org_id: str) -> str:
    user_id = nfse_auth_user_id(authorization)
    headers = nfse_supabase_headers()

    try:
        resp = nfse_rest_request(
            "POST",
            "/rest/v1/rpc/user_can_access_org",
            headers=headers,
            json={"p_org_id": org_id, "_user_id": user_id},
        )
        if resp.json() is True:
            return user_id
    except Exception:
        pass

    try:
        resp = nfse_rest_request(
            "POST",
            "/rest/v1/rpc/is_global_admin",
            headers=headers,
            json={"_user_id": user_id},
        )
        if resp.json() is True:
            return user_id
    except Exception:
        pass

    resp = nfse_rest_request(
        "GET",
        "/rest/v1/usuarios_organizacoes",
        headers=nfse_supabase_headers(None),
        params={
            "select": "id",
            "user_id": f"eq.{user_id}",
            "organizacao_id": f"eq.{org_id}",
            "status": "eq.aprovado",
            "limit": "1",
        },
    )
    if resp.json():
        return user_id
    raise PermissionError("Sem permissao para esta organizacao.")


def nfse_only_digits(value: Any) -> str:
    return re.sub(r"\D", "", str(value or ""))


def nfse_get_competencia_from_date(value: Any) -> str | None:
    text = str(value or "").strip()
    match = re.match(r"^(\d{4})-(\d{2})", text)
    if match:
        return f"{match.group(1)}-{match.group(2)}"
    match = re.match(r"^(\d{2})/(\d{2})/(\d{4})", text)
    if match:
        return f"{match.group(3)}-{match.group(2)}"
    match = re.match(r"^(\d{4})(\d{2})(\d{2})$", text)
    if match:
        return f"{match.group(1)}-{match.group(2)}"
    return None


def nfse_get_competencia_from_path(storage_path: str | None) -> str | None:
    parts = (storage_path or "").split("/")
    competencia = parts[2] if len(parts) >= 3 else ""
    return competencia if competencia and competencia != "_SEM_COMPETENCIA_" else None


def nfse_get_arquivo_competencia(row: dict[str, Any]) -> str:
    metadata = row.get("metadata") or {}
    if not isinstance(metadata, dict):
        metadata = {}
    return (
        nfse_get_competencia_from_date(metadata.get("dataEmissao"))
        or nfse_get_competencia_from_date(metadata.get("dataEvento"))
        or nfse_get_competencia_from_date(metadata.get("dhEvento"))
        or nfse_get_competencia_from_date(metadata.get("dhProc"))
        or nfse_get_competencia_from_date(metadata.get("competencia"))
        or str(metadata.get("competencia") or "")
        or nfse_get_competencia_from_path(row.get("storage_path"))
        or "_SEM_COMPETENCIA_"
    )


def nfse_is_evento(row: dict[str, Any]) -> bool:
    metadata = row.get("metadata") or {}
    if not isinstance(metadata, dict):
        metadata = {}
    values = [
        metadata.get("tipoDoc"), metadata.get("tipoDocumento"), metadata.get("TipoDocumento"),
        metadata.get("tipo_documento"), metadata.get("tpEvento"), metadata.get("descEvento"),
        metadata.get("status"), metadata.get("situacao"), metadata.get("cancelada"),
        metadata.get("cStat"), metadata.get("xMotivo"), row.get("nome"), row.get("storage_path"),
    ]
    text = " ".join(str(v) for v in values if v).upper()
    return "EVENTO" in text or "CANCEL" in text or "PEDREGEVENTO" in text or bool(metadata.get("tpEvento"))


def nfse_matches_filters(row: dict[str, Any], filters: dict[str, Any]) -> bool:
    metadata = row.get("metadata") or {}
    if not isinstance(metadata, dict):
        metadata = {}

    if filters.get("competencia") and nfse_get_arquivo_competencia(row) != filters.get("competencia"):
        return False

    tipo_doc = str(filters.get("tipo_doc") or "").upper()
    if tipo_doc:
        is_evento = nfse_is_evento(row)
        if tipo_doc == "EVENTO" and not is_evento:
            return False
        if tipo_doc == "NFSE" and is_evento:
            return False

    search = str(filters.get("search") or "").strip().lower()
    if search and search not in str(row.get("nome") or "").lower():
        return False

    emit_filter = nfse_only_digits(filters.get("emit_cnpj"))
    if emit_filter and emit_filter not in nfse_only_digits(metadata.get("emit_cnpj")):
        return False

    dest_filter = nfse_only_digits(filters.get("dest_cnpj"))
    if dest_filter:
        dest_doc = nfse_only_digits(metadata.get("toma_cnpj") or metadata.get("toma_cpf"))
        if dest_filter not in dest_doc:
            return False

    if "municipios" in filters and filters.get("municipios") is not None:
        municipios = filters.get("municipios") or []
        if not municipios:
            return False
        codes: list[str] = []
        for raw in (metadata.get("mun_incid_cod"), metadata.get("mun_prest_cod")):
            code = nfse_only_digits(raw)
            if not code:
                continue
            codes.append(code)
            if len(code) == 7:
                codes.append(code[:6])
        if not codes:
            return "__sem__" in municipios
        if not any(code in municipios for code in codes):
            return False

    return True


def nfse_collect_rows(org_id: str, filters: dict[str, Any]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    offset = 0
    while True:
        params = {
            "select": "id,nome,storage_path,empresa_id,metadata",
            "organizacao_id": f"eq.{org_id}",
            "tipo": "eq.XML",
            "storage_path": "like.xml-nfse/%",
            "order": "created_at.desc",
            "limit": str(NFSE_ZIP_PAGE_SIZE),
            "offset": str(offset),
        }
        if filters.get("empresa_id"):
            params["empresa_id"] = f"eq.{filters.get('empresa_id')}"
        resp = nfse_rest_request("GET", "/rest/v1/arquivos", headers=nfse_supabase_headers(None), params=params, timeout=90)
        batch = resp.json() or []
        rows.extend(row for row in batch if nfse_matches_filters(row, filters))
        if len(batch) < NFSE_ZIP_PAGE_SIZE or len(rows) > NFSE_ZIP_MAX_FILES:
            break
        offset += NFSE_ZIP_PAGE_SIZE
    return rows


def nfse_fetch_empresas(empresa_ids: list[str]) -> dict[str, dict[str, Any]]:
    result: dict[str, dict[str, Any]] = {}
    ids = [eid for eid in empresa_ids if eid]
    for i in range(0, len(ids), 100):
        chunk = ids[i:i + 100]
        if not chunk:
            continue
        resp = nfse_rest_request(
            "GET",
            "/rest/v1/empresas",
            headers=nfse_supabase_headers(None),
            params={"select": "id,nome,apelido,cnpj", "id": f"in.({','.join(chunk)})"},
        )
        for empresa in resp.json() or []:
            result[empresa.get("id")] = empresa
    return result


def nfse_sanitize_zip_segment(value: Any) -> str:
    text = re.sub(r"[<>:\"\\|?*\x00-\x1F]", "_", str(value or ""))
    text = re.sub(r"\s+", " ", text).strip()
    return (text[:120] or "Sem Nome")


def nfse_unique_path(base_path: str, used: set[str]) -> str:
    if base_path not in used:
        used.add(base_path)
        return base_path
    folder, name = base_path.rsplit("/", 1) if "/" in base_path else ("", base_path)
    stem, ext = os.path.splitext(name)
    prefix = f"{folder}/" if folder else ""
    counter = 1
    while True:
        candidate = f"{prefix}{stem}_{counter}{ext}"
        if candidate not in used:
            used.add(candidate)
            return candidate
        counter += 1


def nfse_zip_arcname(row: dict[str, Any], empresas: dict[str, dict[str, Any]], used: set[str]) -> str:
    empresa = empresas.get(row.get("empresa_id") or "") or {}
    empresa_base = nfse_sanitize_zip_segment(empresa.get("apelido") or empresa.get("nome") or "Sem Empresa")
    empresa_doc = nfse_only_digits(empresa.get("cnpj")) or str(row.get("empresa_id") or "")[:8]
    empresa_nome = nfse_sanitize_zip_segment(f"{empresa_base} - {empresa_doc}" if empresa_doc else empresa_base)
    competencia = nfse_sanitize_zip_segment(nfse_get_arquivo_competencia(row))
    file_name = nfse_sanitize_zip_segment(row.get("nome") or os.path.basename(row.get("storage_path") or "") or f"{row.get('id')}.xml")
    return nfse_unique_path(f"{empresa_nome}/{competencia}/{file_name}", used)


def nfse_download_storage_object(row: dict[str, Any]) -> tuple[dict[str, Any], bytes | None, str | None]:
    storage_path = row.get("storage_path") or ""
    url, _ = nfse_supabase_config()
    object_url = f"{url}/storage/v1/object/{NFSE_ZIP_BUCKET}/{quote(storage_path, safe='/')}"
    try:
        resp = requests.get(object_url, headers=nfse_supabase_headers(None), timeout=90)
        if resp.status_code >= 400:
            return row, None, f"HTTP {resp.status_code}"
        return row, resp.content, None
    except Exception as exc:
        return row, None, str(exc)


def nfse_upload_zip(zip_path: str, storage_path: str) -> None:
    url, _ = nfse_supabase_config()
    object_url = f"{url}/storage/v1/object/{NFSE_ZIP_BUCKET}/{quote(storage_path, safe='/')}"
    headers = nfse_supabase_headers("application/zip")
    headers["x-upsert"] = "true"
    with open(zip_path, "rb") as f:
        resp = requests.post(object_url, headers=headers, data=f, timeout=600)
    if resp.status_code >= 400:
        raise RuntimeError(f"Falha ao subir ZIP: HTTP {resp.status_code}: {resp.text[:500]}")


def nfse_zip_worker(execucao_id: str, organizacao_id: str, filters: dict[str, Any]) -> None:
    zip_path = ""
    try:
        nfse_update_execucao(execucao_id, {
            "status": "processando",
            "progresso": 0,
            "parametros": {
                "filters": filters,
                "totalArquivos": 0,
                "processados": 0,
                "zip_ok": 0,
                "erros": 0,
                "part_paths": [],
                "updatedAt": nfse_now_iso(),
            },
        })

        rows = nfse_collect_rows(organizacao_id, filters)
        total = len(rows)
        if total <= 0:
            raise RuntimeError("Nenhum XML encontrado para os filtros selecionados")
        if total > NFSE_ZIP_MAX_FILES:
            raise RuntimeError(f"Limite de {NFSE_ZIP_MAX_FILES} XMLs por ZIP excedido")

        empresas = nfse_fetch_empresas(list({str(row.get("empresa_id")) for row in rows if row.get("empresa_id")}))
        params = {
            "filters": filters,
            "totalArquivos": total,
            "processados": 0,
            "zip_ok": 0,
            "erros": 0,
            "part_paths": [],
            "updatedAt": nfse_now_iso(),
        }
        nfse_update_execucao(execucao_id, {"status": "processando", "parametros": params})

        tmp = tempfile.NamedTemporaryFile(prefix=f"nfse_zip_{execucao_id}_", suffix=".zip", delete=False)
        zip_path = tmp.name
        tmp.close()

        used_names: set[str] = set()
        processed = 0
        zip_ok = 0
        errors = 0

        with zipfile.ZipFile(zip_path, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=6) as zf:
            with ThreadPoolExecutor(max_workers=NFSE_ZIP_WORKERS) as executor:
                futures = [executor.submit(nfse_download_storage_object, row) for row in rows]
                for future in as_completed(futures):
                    row, content, error = future.result()
                    processed += 1
                    if content:
                        arcname = nfse_zip_arcname(row, empresas, used_names)
                        zf.writestr(arcname, content)
                        zip_ok += 1
                    else:
                        errors += 1

                    if processed == total or processed % NFSE_ZIP_PROGRESS_EVERY == 0:
                        params.update({
                            "processados": processed,
                            "zip_ok": zip_ok,
                            "erros": errors,
                            "updatedAt": nfse_now_iso(),
                        })
                        progresso = min(95, round((processed / total) * 95)) if total else 0
                        nfse_update_execucao(execucao_id, {"progresso": progresso, "parametros": params})

        if zip_ok <= 0:
            raise RuntimeError("Nenhum XML pode ser adicionado ao ZIP")

        part_path = f"{NFSE_ZIP_PREFIX}/{execucao_id}_nfse_xmls.zip"
        nfse_upload_zip(zip_path, part_path)
        params.update({
            "processados": total,
            "zip_ok": zip_ok,
            "erros": errors,
            "part_paths": [part_path],
            "updatedAt": nfse_now_iso(),
            "error": None,
        })
        nfse_update_execucao(execucao_id, {
            "status": "concluido",
            "progresso": 100,
            "finalizado_em": nfse_now_iso(),
            "parametros": params,
        })
    except Exception as exc:
        current = nfse_get_execucao(execucao_id) or {}
        params = current.get("parametros") or {}
        if not isinstance(params, dict):
            params = {}
        params.update({"error": str(exc), "updatedAt": nfse_now_iso()})
        try:
            nfse_update_execucao(execucao_id, {
                "status": "erro",
                "finalizado_em": nfse_now_iso(),
                "parametros": params,
            })
        except Exception:
            pass
    finally:
        if zip_path:
            try:
                os.remove(zip_path)
            except Exception:
                pass


@app.get("/nfse/zip/ping")
def nfse_zip_ping() -> dict[str, bool]:
    return {"ok": True}


@app.post("/nfse/zip/start")
async def nfse_zip_start(payload: dict[str, Any], authorization: str | None = Header(None)):
    try:
        execucao_id = str(payload.get("execucao_id") or "").strip()
        organizacao_id = str(payload.get("organizacao_id") or "").strip()
        filters = payload.get("filters") or {}
        if not isinstance(filters, dict):
            filters = {}
        if not execucao_id:
            return JSONResponse({"success": False, "error": "execucao_id obrigatorio"}, status_code=400)
        if not organizacao_id:
            return JSONResponse({"success": False, "error": "organizacao_id obrigatorio"}, status_code=400)

        nfse_require_org_access(authorization, organizacao_id)
        thread = threading.Thread(target=nfse_zip_worker, args=(execucao_id, organizacao_id, filters), daemon=True)
        thread.start()
        return JSONResponse({"success": True, "background": True, "execucao_id": execucao_id})
    except PermissionError as exc:
        return JSONResponse({"success": False, "error": str(exc)}, status_code=403)
    except Exception as exc:
        return JSONResponse({"success": False, "error": str(exc)}, status_code=500)


@app.get("/health")
def health() -> dict[str, bool]:
    return {"ok": True}


@app.post("/baixar-nfe")
async def baixar_nfe(
    ambiente: str = Form("producao"),
    senha: str = Form(...),
    cnpj: str = Form(...),
    cuf: str = Form("27"),
    competencia: str = Form(...),
    max_lotes: int = Form(10),
    somente_completas: str = Form("true"),
    manifestar_ciencia: str = Form("false"),
    start_nsu: str | None = Form(None),
    certificado: UploadFile = File(...),
):
    cert_path = None
    try:
        cert_path = os.path.join(tempfile.gettempdir(), certificado.filename or "certificado_nfe_tmp.pfx")
        with open(cert_path, "wb") as f:
            f.write(await certificado.read())

        resultado = processar_consulta(
            ambiente=ambiente,
            caminho_pfx=cert_path,
            senha=senha,
            cnpj=cnpj,
            cuf=cuf,
            max_lotes=int(max_lotes),
            competencia=competencia,
            somente_completas=garantir_bool(somente_completas),
            manifestar_ciencia=garantir_bool(manifestar_ciencia),
            start_nsu=start_nsu,
            filtrar_competencia=True,
        )
        return JSONResponse(resultado)
    except Exception as exc:
        return JSONResponse({"success": False, "error": str(exc)}, status_code=500)
    finally:
        try:
            if cert_path and os.path.exists(cert_path):
                os.remove(cert_path)
        except Exception:
            pass


@app.post("/baixar-zip")
async def baixar_zip(payload: dict[str, Any]):
    arquivos = payload.get("arquivos") or []
    arquivos_validos = [os.path.abspath(str(path)) for path in arquivos if os.path.exists(str(path))]

    if not arquivos_validos:
        return JSONResponse({"success": False, "error": "Nenhum arquivo vÃ¡lido para compactar."}, status_code=400)

    buf = io.BytesIO()
    with zipfile.ZipFile(buf, "w", zipfile.ZIP_DEFLATED) as zf:
        for path in arquivos_validos:
            zf.write(path, arcname=os.path.basename(path))
    buf.seek(0)

    return StreamingResponse(
        buf,
        media_type="application/zip",
        headers={"Content-Disposition": 'attachment; filename="nfe_entrada.zip"'},
    )


# ============================================================================
# NEW: Endpoint que retorna os XMLs como conteÃºdo base64 (em vez de paths
# locais), para integraÃ§Ã£o com Supabase Edge Functions / Lovable Cloud.
# Mesma lÃ³gica de processamento; sÃ³ muda a forma de devolver os arquivos.
# ============================================================================

@app.post("/baixar-nfe-json")
async def baixar_nfe_json(
    ambiente: str = Form("producao"),
    senha: str = Form(...),
    cnpj: str = Form(...),
    cuf: str = Form("27"),
    competencia: str = Form(...),
    max_lotes: int = Form(10),
    somente_completas: str = Form("true"),
    manifestar_ciencia: str = Form("false"),
    start_nsu: str | None = Form(None),
    filtrar_competencia: str = Form("false"),
    certificado: UploadFile = File(...),
):
    """
    Igual ao /baixar-nfe, porÃ©m retorna os XMLs jÃ¡ lidos como base64 dentro
    do JSON, para que o cliente (edge function) possa subi-los ao Storage
    sem precisar acessar o disco local da API.

    Resposta:
    {
      "success": bool,
      "cStat": str, "xMotivo": str,
      "ult_nsu_inicial", "ult_nsu_final", "max_nsu",
      "lotes_consultados", "docs_recebidos",
      "resumos", "completos", "eventos",
      "manifestados", "erros_manifestacao", "ignorados_competencia",
      "salvos": int,
      "arquivos": [
         {
           "nome": "<chave>_<categoria>.xml",
           "categoria": "completo" | "resumo" | "evento" | "outro",
           "chave": "<44 dÃ­gitos>" | null,
           "competencia": "YYYY-MM" | null,
           "tamanho_bytes": int,
           "xml_base64": "<base64 do XML utf-8>"
         }, ...
      ],
      "manifestacoes": [...], "documentos": [...]
    }
    """
    cert_path = None
    try:
        cert_path = os.path.join(
            tempfile.gettempdir(),
            certificado.filename or "certificado_nfe_tmp.pfx",
        )
        with open(cert_path, "wb") as f:
            f.write(await certificado.read())

        resultado = processar_consulta(
            ambiente=ambiente,
            caminho_pfx=cert_path,
            senha=senha,
            cnpj=cnpj,
            cuf=cuf,
            max_lotes=int(max_lotes),
            competencia=competencia,
            somente_completas=garantir_bool(somente_completas),
            manifestar_ciencia=garantir_bool(manifestar_ciencia),
            start_nsu=start_nsu,
            filtrar_competencia=garantir_bool(filtrar_competencia),
        )

        # Substitui a lista de paths por uma lista enriquecida com base64.
        arquivos_base64 = []
        for caminho in resultado.get("arquivos", []) or []:
            try:
                if not caminho or not os.path.exists(caminho):
                    continue
                with open(caminho, "rb") as f:
                    raw = f.read()
                nome = os.path.basename(caminho)

                # Categoria heurÃ­stica pelo sufixo do nome
                # (salvar_documento usa "{chave}_{categoria}.xml")
                categoria = "outro"
                m = re.match(r"^(\d{44})_(\w+)\.xml$", nome, re.IGNORECASE)
                chave = None
                if m:
                    chave = m.group(1)
                    categoria = m.group(2).lower()

                # Tenta extrair competÃªncia do XML
                competencia_doc = None
                try:
                    xml_text = raw.decode("utf-8", errors="ignore")
                    schema_guess = "procNFe" if categoria == "completo" else (
                        "resNFe" if categoria == "resumo" else (
                            "procEventoNFe" if categoria == "evento" else ""
                        )
                    )
                    res = resumir_documento(xml_text, schema_guess)
                    competencia_doc = extrair_competencia_de_data(res.get("dh_emi"))
                    if not chave:
                        chave = res.get("chave")
                except Exception:
                    pass

                arquivos_base64.append({
                    "nome": nome,
                    "categoria": categoria,
                    "chave": chave,
                    "competencia": competencia_doc or competencia,
                    "tamanho_bytes": len(raw),
                    "xml_base64": base64.b64encode(raw).decode("ascii"),
                })
            except Exception as exc:
                # NÃ£o derruba a resposta inteira por causa de 1 arquivo
                arquivos_base64.append({
                    "nome": os.path.basename(caminho or ""),
                    "categoria": "erro",
                    "chave": None,
                    "competencia": None,
                    "tamanho_bytes": 0,
                    "xml_base64": "",
                    "erro": str(exc),
                })

        resultado["arquivos"] = arquivos_base64
        resultado["salvos"] = len([a for a in arquivos_base64 if a.get("xml_base64")])
        return JSONResponse(resultado)
    except Exception as exc:
        return JSONResponse(
            {"success": False, "error": str(exc)},
            status_code=500,
        )
    finally:
        try:
            if cert_path and os.path.exists(cert_path):
                os.remove(cert_path)
        except Exception:
            pass
