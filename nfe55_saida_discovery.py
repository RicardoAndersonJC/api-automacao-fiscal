"""Descoberta de NF-e modelo 55, isolada da NFC-e.

A varredura segue o XML ou a chave semente. cStat 100 só vale quando a
resposta confirma a chave consultada. cStat 613 aceita a chave real de outro
mês e troca a competência. A parada ocorre depois de N retornos 217 seguidos
sem documento no mês atual nem na janela do mês seguinte.
"""

from __future__ import annotations

import json
import re
from dataclasses import dataclass
from xml.etree import ElementTree as ET

MODELO = "55"
PESOS_DV = (2, 3, 4, 5, 6, 7, 8, 9)


def somente_digitos(valor: str) -> str:
    return re.sub(r"\D", "", valor or "")


def modulo11_dv(chave43: str) -> str:
    if len(chave43) != 43 or not chave43.isdigit():
        raise ValueError("A base da chave precisa ter 43 dígitos.")
    soma = 0
    for indice, digito in enumerate(reversed(chave43)):
        soma += int(digito) * PESOS_DV[indice % len(PESOS_DV)]
    resto = soma % 11
    dv = 11 - resto
    return "0" if dv >= 10 else str(dv)


def proximo_aamm(aamm: str) -> str:
    if not re.fullmatch(r"\d{4}", aamm):
        raise ValueError("AAMM inválido.")
    ano = 2000 + int(aamm[:2])
    mes = int(aamm[2:4]) + 1
    if mes == 13:
        mes = 1
        ano += 1
    if not 1 <= mes <= 12:
        raise ValueError("Mês inválido.")
    return f"{ano % 100:02d}{mes:02d}"


def _tag(elem: ET.Element) -> str:
    return elem.tag.split("}", 1)[-1]


def chave_artificial(cfg: dict, nnf: int, aamm: str | None = None) -> str:
    competencia = aamm or cfg["AAMM"]
    base = (
        f"{cfg['cUF']}{competencia}{cfg['CNPJ']}{cfg['modelo']}"
        f"{cfg['serie']}{nnf:09d}{cfg['tpEmis']}00000001"
    )
    return base + modulo11_dv(base)


def cfg_da_chave(chave: str) -> dict:
    chave = somente_digitos(chave)
    if len(chave) != 44:
        raise ValueError("A chave de acesso deve conter exatamente 44 dígitos.")
    if chave[20:22] != MODELO:
        raise ValueError(f"A chave informada é do modelo {chave[20:22]}; esta busca é de NF-e modelo 55.")
    if modulo11_dv(chave[:43]) != chave[43]:
        raise ValueError("Chave com dígito verificador inválido.")
    return {
        "cUF": chave[0:2],
        "AAMM": chave[2:6],
        "CNPJ": chave[6:20],
        "modelo": MODELO,
        "serie": chave[22:25],
        "nNF_semente": int(chave[25:34]),
        "tpEmis": chave[34:35],
        "chave_semente": chave,
    }


def ler_xml_semente(conteudo: bytes) -> dict:
    raiz = ET.fromstring(conteudo)
    inf = next((item for item in raiz.iter() if _tag(item) == "infNFe"), None)
    emit = next((item for item in raiz.iter() if _tag(item) == "emit"), None)
    if inf is None or emit is None:
        raise ValueError("O XML não contém infNFe e emitente.")

    def texto(parent: ET.Element, nome: str) -> str:
        for item in parent.iter():
            if _tag(item) == nome and (item.text or "").strip():
                return item.text.strip()
        return ""

    modelo = texto(inf, "mod").zfill(2)
    if modelo != MODELO:
        raise ValueError("Selecione um XML de NF-e modelo 55.")
    chave = inf.attrib.get("Id", "").removeprefix("NFe")
    if len(somente_digitos(chave)) != 44:
        raise ValueError("Não foi possível ler a chave do XML semente.")
    cfg = cfg_da_chave(chave)
    cnpj_emit = somente_digitos(texto(emit, "CNPJ"))
    if cnpj_emit and cnpj_emit != cfg["CNPJ"]:
        raise ValueError("O CNPJ do emitente não confere com a chave.")
    numero = int(texto(inf, "nNF") or cfg["nNF_semente"])
    cfg["nNF_semente"] = numero
    cfg["xNome"] = texto(emit, "xNome") or "EMPRESA"
    return cfg


def chave_corresponde(chave: str, cfg: dict, nnf: int, aamm: str, aceitar_mes_diferente: bool = False) -> bool:
    chave = somente_digitos(chave)
    if len(chave) != 44 or modulo11_dv(chave[:43]) != chave[-1]:
        return False
    return (
        chave[:2] == cfg["cUF"]
        and (aceitar_mes_diferente or chave[2:6] == aamm)
        and chave[6:20] == cfg["CNPJ"]
        and chave[20:22] == cfg["modelo"]
        and chave[22:25] == cfg["serie"]
        and int(chave[25:34]) == nnf
    )


def chaves_protocolo(texto: str) -> list[str]:
    try:
        raiz = ET.fromstring(texto)
    except ET.ParseError:
        return []
    return list(dict.fromkeys(
        somente_digitos(item.text or "")
        for item in raiz.iter()
        if _tag(item) == "chNFe" and item.text
    ))


def interpretar_consulta(texto: str, cfg: dict, nnf: int, aamm: str) -> tuple[str, str, str]:
    """Retorna cStat, motivo e chave real confirmada."""
    cstat = re.search(r"<cStat>(\d+)</cStat>", texto or "")
    motivo = re.search(r"<xMotivo>(.*?)</xMotivo>", texto or "", flags=re.S)
    codigo = cstat.group(1) if cstat else ""
    descricao = re.sub(r"\s+", " ", motivo.group(1)).strip() if motivo else ""
    artificial = chave_artificial(cfg, nnf, aamm)
    if codigo == "100":
        if artificial in chaves_protocolo(texto) and chave_corresponde(artificial, cfg, nnf, aamm):
            return codigo, descricao, artificial
        return codigo, descricao, ""
    if codigo == "613":
        for candidata in re.findall(r"(?<!\d)\d{44}(?!\d)", texto or ""):
            if candidata != artificial and chave_corresponde(candidata, cfg, nnf, aamm, aceitar_mes_diferente=True):
                return codigo, descricao, candidata
    return codigo, descricao, ""


@dataclass
class Passo:
    aamm: str
    nnf: int
    consecutivos_217: int
    encerrar: bool
    encontrada: str
    lacuna: bool


def avancar(cfg: dict, aamm: str, nnf: int, consecutivos: int, stop_217: int, atual: str, seguinte: str | None = None) -> Passo:
    codigo, _motivo, real = interpretar_consulta(atual, cfg, nnf, aamm)
    if real:
        return Passo(real[2:6], nnf + 1, 0, False, real, False)
    if codigo == "217":
        if seguinte:
            codigo_seguinte, _motivo_seguinte, real_seguinte = interpretar_consulta(seguinte, cfg, nnf, proximo_aamm(aamm))
            if real_seguinte:
                return Passo(real_seguinte[2:6], nnf + 1, 0, False, real_seguinte, False)
            if codigo_seguinte == "217":
                consecutivos += 1
            else:
                consecutivos = 0
        else:
            consecutivos += 1
        encerrar = consecutivos >= stop_217
        return Passo(aamm, nnf + 1, consecutivos, encerrar, "", True)
    return Passo(aamm, nnf + 1, 0, False, "", False)


def montar_soap(chave: str) -> str:
    consulta = (
        '<consSitNFe versao="4.00" xmlns="http://www.portalfiscal.inf.br/nfe">'
        f"<tpAmb>1</tpAmb><xServ>CONSULTAR</xServ><chNFe>{chave}</chNFe></consSitNFe>"
    )
    return (
        '<?xml version="1.0" encoding="utf-8"?>'
        '<soap12:Envelope xmlns:soap12="http://www.w3.org/2003/05/soap-envelope">'
        '<soap12:Body><nfeDadosMsg xmlns="http://www.portalfiscal.inf.br/nfe/wsdl/NFeConsultaProtocolo4">'
        f"{consulta}</nfeDadosMsg></soap12:Body></soap12:Envelope>"
    )


def extrair_xml_portal(texto: str) -> str | None:
    posicao = texto.find("stringJson")
    if posicao >= 0:
        achado = re.search(r"""["']xml["']\s*:\s*""", texto[posicao:])
        if achado:
            trecho = texto[posicao + achado.end():].lstrip()
            if trecho.startswith('"'):
                try:
                    valor, _ = json.JSONDecoder().raw_decode(trecho)
                    inicio, fim = valor.find("<nfeProc"), valor.rfind("</nfeProc>")
                    if inicio >= 0 and fim > inicio:
                        xml = valor[inicio:fim + len("</nfeProc>")]
                        ET.fromstring(xml)
                        return xml
                except (ValueError, ET.ParseError):
                    pass
    inicio, fim = texto.find("<nfeProc"), texto.rfind("</nfeProc>")
    if inicio >= 0 and fim > inicio:
        xml = texto[inicio:fim + len("</nfeProc>")]
        try:
            ET.fromstring(xml)
            return xml
        except ET.ParseError:
            return None
    return None


def xml_modelo_55(xml: str, chave: str) -> bool:
    try:
        raiz = ET.fromstring(xml)
    except ET.ParseError:
        return False
    inf = next((item for item in raiz.iter() if _tag(item) == "infNFe"), None)
    if inf is None:
        return False
    modelo = next(((item.text or "").strip() for item in inf.iter() if _tag(item) == "mod"), "")
    return inf.attrib.get("Id", "").removeprefix("NFe") == chave and modelo == MODELO
