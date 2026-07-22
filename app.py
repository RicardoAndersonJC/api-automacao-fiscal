import base64
import gzip
import io
import json
import os
import re
import tempfile
import time
import zipfile
from datetime import date, datetime
from typing import Any
from xml.etree import ElementTree as ET

import requests
from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.serialization import pkcs12
from fastapi import FastAPI, File, Form, UploadFile
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
    allow_credentials=True,
    allow_methods=["*"],
    allow_headers=["*"],
)


def limpar_cnpj(cnpj: str) -> str:
    return re.sub(r"\D", "", cnpj or "")


def garantir_cnpj(cnpj: str) -> str:
    cnpj_limpo = limpar_cnpj(cnpj)
    if len(cnpj_limpo) != 14:
        raise ValueError(f"CNPJ inválido: {cnpj}")
    return cnpj_limpo


def garantir_competencia(comp: str) -> str:
    comp = (comp or "").strip()
    if not re.fullmatch(r"\d{4}-\d{2}", comp):
        raise ValueError("Competência inválida. Use YYYY-MM.")
    return comp


def garantir_data_iso(valor: str, campo: str) -> date:
    try:
        return date.fromisoformat((valor or "").strip())
    except ValueError as exc:
        raise ValueError(f"{campo} invalida. Use YYYY-MM-DD.") from exc


def garantir_periodo_recuperacao(data_inicio: str, data_fim: str) -> tuple[date, date]:
    inicio = garantir_data_iso(data_inicio, "data_inicio")
    fim = garantir_data_iso(data_fim, "data_fim")
    if inicio > fim:
        raise ValueError("data_inicio deve ser anterior ou igual a data_fim.")
    if (fim - inicio).days > 89:
        raise ValueError("A recuperacao pode abranger no maximo 90 dias, inclusive.")
    if fim > date.today():
        raise ValueError("data_fim nao pode estar no futuro.")
    return inicio, fim


def garantir_ambiente(ambiente: str) -> str:
    ambiente = (ambiente or "").strip().lower()
    if ambiente not in ENDPOINT_DIST:
        raise ValueError("Ambiente inválido. Use homologacao ou producao.")
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


def caminho_staging_recuperacao(cnpj: str, recovery_id: str) -> str:
    safe_id = re.sub(r"[^a-zA-Z0-9_-]", "", recovery_id or "")
    if len(safe_id) < 8:
        raise ValueError("recovery_id invalido.")
    return os.path.join(BASE_DIR, "estado", f"recovery_{cnpj}_{safe_id}.json")


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


def extrair_data_documento(texto_data: str | None) -> date | None:
    if not texto_data:
        return None
    texto = texto_data.strip()
    for pattern, order in (
        (r"^(\d{4})-(\d{2})-(\d{2})", (1, 2, 3)),
        (r"^(\d{2})/(\d{2})/(\d{4})", (3, 2, 1)),
        (r"^(\d{4})(\d{2})(\d{2})$", (1, 2, 3)),
    ):
        match = re.match(pattern, texto)
        if match:
            try:
                return date(*(int(match.group(i)) for i in order))
            except ValueError:
                return None
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

    raise RuntimeError("Não foi possível localizar retDistDFeInt no retorno SOAP.")


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
        raise ValueError("Não foi possível extrair certificado e chave do PFX.")

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
        raise ValueError("infEvento não encontrado para assinatura.")

    evento = inf_evento.getparent()
    if evento is None:
        raise ValueError("evento não encontrado para assinatura.")

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
    competencia: str | None,
    somente_completas: bool,
    manifestar_ciencia: bool,
    start_nsu: str | None = None,
    modo_recuperacao: bool = False,
    data_inicio: str | None = None,
    data_fim: str | None = None,
    persistir_nsu: bool = True,
    recovery_id: str | None = None,
) -> dict[str, Any]:
    ambiente = garantir_ambiente(ambiente)
    cnpj = garantir_cnpj(cnpj)
    periodo_inicio: date | None = None
    periodo_fim: date | None = None
    if modo_recuperacao:
        periodo_inicio, periodo_fim = garantir_periodo_recuperacao(data_inicio or "", data_fim or "")
        if not recovery_id:
            raise ValueError("recovery_id e obrigatorio no modo de recuperacao.")
        competencia = None
        persistir_nsu = False
    else:
        competencia = garantir_competencia(competencia or "")

    cert_path = None
    key_path = None
    session = None

    ult_nsu_inicial = (
        str(start_nsu).zfill(15)
        if start_nsu is not None
        else carregar_nsu(cnpj, ambiente)
    )
    if not re.fullmatch(r"\d{15}", ult_nsu_inicial):
        raise ValueError("start_nsu invalido. Use 15 digitos.")
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
    staging_path = caminho_staging_recuperacao(cnpj, recovery_id) if modo_recuperacao and recovery_id else None
    staged_paths = set(carregar_json(staging_path, [])) if staging_path else set()

    def registrar_salvo(caminho: str) -> None:
        if caminho not in salvos:
            salvos.append(caminho)
        if staging_path and caminho not in staged_paths:
            staged_paths.add(caminho)
            salvar_json(staging_path, sorted(staged_paths))
    ignorados_fora_janela = 0
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

                data_doc = extrair_data_documento(resumo.get("dh_emi"))
                competencia_destino = comp_doc or "_SEM_COMPETENCIA_"
                fora_do_escopo = (
                    modo_recuperacao
                    and data_doc is not None
                    and periodo_inicio is not None
                    and periodo_fim is not None
                    and not (periodo_inicio <= data_doc <= periodo_fim)
                ) or (
                    not modo_recuperacao
                    and not mesmo_mes(resumo.get("dh_emi"), competencia)
                )
                if fora_do_escopo:
                    if modo_recuperacao:
                        ignorados_fora_janela += 1
                    else:
                        ignorados_competencia += 1
                    documentos.append(
                        {
                            "nsu": doc_zip.attrib.get("NSU"),
                            "tipo": categoria,
                            "chave": chave,
                            "competencia": comp_doc,
                            "acao": "ignorado",
                            "motivo": "Documento fora do periodo da recuperacao" if modo_recuperacao else "Competência diferente da selecionada",
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
                        caminho = salvar_documento(cnpj, competencia_destino, doc_info, resumo)
                        if caminho:
                            registrar_salvo(caminho)
                    continue

                if categoria == "completo":
                    completos += 1
                    caminho = salvar_documento(cnpj, competencia_destino, doc_info, resumo)
                    if caminho:
                        registrar_salvo(caminho)
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
                    caminho = salvar_documento(cnpj, competencia_destino, doc_info, resumo)
                    if caminho:
                        registrar_salvo(caminho)
                documentos.append(
                    {
                        "nsu": doc_zip.attrib.get("NSU"),
                        "tipo": categoria,
                        "chave": chave,
                        "competencia": comp_doc,
                        "acao": "ignorado" if somente_completas else "salvo",
                        "motivo": None if not somente_completas else "Não é XML completo",
                    }
                )

            if persistir_nsu:
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

                        data_doc = extrair_data_documento(resumo.get("dh_emi"))
                        dentro_do_escopo = (
                            periodo_inicio is not None
                            and periodo_fim is not None
                            and (data_doc is None or periodo_inicio <= data_doc <= periodo_fim)
                        ) if modo_recuperacao else mesmo_mes(resumo.get("dh_emi"), competencia)
                        if categoria != "completo" or not dentro_do_escopo:
                            continue

                        doc_info = {"xml": xml_doc, "schema": schema}
                        caminho = salvar_documento(cnpj, comp_doc or "_SEM_COMPETENCIA_", doc_info, resumo)
                        if caminho and caminho not in salvos:
                            registrar_salvo(caminho)
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

                    if persistir_nsu:
                        salvar_nsu(cnpj, ambiente, ult_nsu_atual, competencia=competencia, total_documentos=docs_recebidos)
                    if novos_completos == 0 or cstat_final == "137" or ult_nsu_atual == max_nsu_final:
                        break

        if persistir_nsu:
            salvar_manifestadas(cnpj, ambiente, manifestadas)

        arquivos = (
            sorted(staged_paths) if modo_recuperacao and cstat_final == "656"
            else list(dict.fromkeys(salvos))
        )
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
            "ignorados_fora_janela": ignorados_fora_janela,
            "modo_recuperacao": modo_recuperacao,
            "data_inicio": data_inicio if modo_recuperacao else None,
            "data_fim": data_fim if modo_recuperacao else None,
            "parcial": bool(max_nsu_final and ult_nsu_atual != max_nsu_final and cstat_final not in {"137", "656"}),
            "proximo_nsu": ult_nsu_atual,
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


@app.get("/health")
def health() -> dict[str, bool]:
    return {"ok": True}


def serializar_arquivo_xml(caminho: str) -> dict[str, Any]:
    caminho_abs = os.path.abspath(caminho)
    base_abs = os.path.abspath(BASE_DIR)
    if os.path.commonpath([caminho_abs, base_abs]) != base_abs:
        raise ValueError("Arquivo fora do diretorio fiscal permitido.")
    nome = os.path.basename(caminho_abs)
    match = re.match(r"^(\d{44})_([a-zA-Z0-9_-]+)\.xml$", nome)
    competencia = os.path.basename(os.path.dirname(caminho_abs))
    with open(caminho_abs, "rb") as arquivo:
        conteudo = arquivo.read()
    return {
        "nome": nome,
        "categoria": match.group(2) if match else "outro",
        "chave": match.group(1) if match else None,
        "competencia": competencia,
        "tamanho_bytes": len(conteudo),
        "xml_base64": base64.b64encode(conteudo).decode("ascii"),
    }


@app.post("/baixar-nfe")
@app.post("/baixar-nfe-json")
async def baixar_nfe(
    ambiente: str = Form("producao"),
    senha: str = Form(...),
    cnpj: str = Form(...),
    cuf: str = Form("27"),
    competencia: str | None = Form(None),
    max_lotes: int = Form(10),
    somente_completas: str = Form("true"),
    manifestar_ciencia: str = Form("false"),
    start_nsu: str | None = Form(None),
    modo_recuperacao: str = Form("false"),
    data_inicio: str | None = Form(None),
    data_fim: str | None = Form(None),
    persistir_nsu: str = Form("true"),
    recovery_id: str | None = Form(None),
    certificado: UploadFile = File(...),
):
    cert_path = None
    try:
        with tempfile.NamedTemporaryFile(prefix="cert_nfe_", suffix=".pfx", delete=False) as f:
            cert_path = f.name
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
            modo_recuperacao=garantir_bool(modo_recuperacao),
            data_inicio=data_inicio,
            data_fim=data_fim,
            persistir_nsu=garantir_bool(persistir_nsu),
            recovery_id=recovery_id,
        )
        resultado["arquivos"] = [serializar_arquivo_xml(path) for path in resultado.get("arquivos", [])]
        return JSONResponse(resultado)
    except ValueError as exc:
        return JSONResponse({"success": False, "error": str(exc)}, status_code=400)
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
        return JSONResponse({"success": False, "error": "Nenhum arquivo válido para compactar."}, status_code=400)

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
