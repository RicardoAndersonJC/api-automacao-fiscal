"""Worker de NF-e modelo 55 de saída. Não compartilha rota nem estado com a NFC-e."""

from __future__ import annotations

import html
import os
import re
import shutil
import tempfile
import threading
import time
import unicodedata
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timedelta, timezone
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
    avancar_sobre_recuperadas,
    cfg_da_chave,
    chave_artificial,
    chaves_para_recuperar,
    numeros_sem_chave,
    extrair_xml_portal,
    interpretar_consulta,
    ler_xml_semente,
    montar_soap,
    proximo_aamm,
    xml_modelo_55,
)
import nfe55_saida_transport as saida_rede

URL_CONSULTA = "https://nfe.svrs.rs.gov.br/ws/NfeConsulta/NfeConsulta4.asmx"
URL_PORTAL = "https://dfe-portal.svrs.rs.gov.br/NFeSSL/DownloadXMLDFe"
ORIGEM_PORTAL = "https://dfe-portal.svrs.rs.gov.br"
# Mesmos cabeçalhos de navegador do fluxo capturado no Chrome (código base da saída).
CABECALHOS_NAVEGADOR = {
    "User-Agent": (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
        "(KHTML, like Gecko) Chrome/153.0.0.0 Safari/537.36"
    ),
    "Accept": (
        "text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,"
        "image/apng,*/*;q=0.8,application/signed-exchange;v=b3;q=0.7"
    ),
    "Accept-Language": "pt-BR,pt;q=0.9,en-US;q=0.8,en;q=0.7",
    "Cache-Control": "no-cache",
    "Pragma": "no-cache",
    "Upgrade-Insecure-Requests": "1",
}
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


def _transporte():
    """Saída própria da NF-e de saída. Limite da SVRS não troca o proxy."""
    return saida_rede.transporte_compartilhado()


def _abrir_sessao(cert_path: Path, key_path: Path) -> requests.Session:
    sessao = requests.Session()
    sessao.cert = (str(cert_path), str(key_path))
    sessao.verify = _ca_bundle()
    _transporte().apply(sessao)
    return sessao


def _esperar_limite() -> None:
    time.sleep(saida_rede.cooldown_segundos())


def _enviar_rota(sessao: requests.Session, transporte: Any, metodo: str, url: str, **kwargs: Any) -> requests.Response:
    """429 repete na mesma sessão. Falha de conexão só troca se houver outra rota."""
    kwargs["verify"] = _ca_bundle()

    def chamar() -> requests.Response:
        return getattr(sessao, metodo)(url, **kwargs)

    try:
        resposta = chamar()
    except requests.exceptions.ProxyError:
        if not transporte.note_infrastructure_failure():
            raise
        transporte.apply(sessao)
        resposta = chamar()
    if resposta.status_code != 429:
        if resposta.ok:
            transporte.note_success()
        resposta.raise_for_status()
        return resposta
    transporte.note_remote_limit()
    _esperar_limite()
    resposta = chamar()
    if resposta.status_code == 429:
        transporte.note_remote_limit()
    elif resposta.ok:
        transporte.note_success()
    resposta.raise_for_status()
    return resposta


def _enviar(sessao: requests.Session, metodo: str, url: str, **kwargs: Any) -> requests.Response:
    return _enviar_rota(sessao, _transporte(), metodo, url, **kwargs)


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
    resposta = _enviar(
        sessao,
        "post",
        URL_CONSULTA,
        data=montar_soap(chave).encode("utf-8"),
        headers={
            "Content-Type": f'application/soap+xml; charset=utf-8; action="{SOAP_ACTION}"',
            "Accept": "application/soap+xml, text/xml, */*",
        },
        timeout=(20, 75),
    )
    return resposta.text


def _tamanho_lote() -> int:
    return saida_rede.tamanho_lote()


def _rotas_proxy() -> list[Any]:
    """NFE55_PROXY_* ou, se vazias, os mesmos proxies da NFC-e. Sem duas rotas, o download segue um a um."""
    return saida_rede.rotas_configuradas()


def _lote_ativo(rotas: list[Any]) -> bool:
    return len(rotas) >= 2


def _ponto_de_partida(cfg: dict[str, Any], opcoes: dict[str, Any]) -> tuple[str, int]:
    """A semente começa no número seguinte. Um cursor já avançado continua de lá."""
    aamm = str(cfg["AAMM"])
    semente = int(cfg["nNF_semente"])
    cursor_aamm = str(opcoes.get("cursor_aamm") or "")
    try:
        cursor_nnf = int(opcoes.get("cursor_nnf") or 0)
    except (TypeError, ValueError):
        cursor_nnf = 0
    if len(cursor_aamm) == 4 and cursor_nnf > 0 and (cursor_aamm, cursor_nnf) != (aamm, semente):
        return cursor_aamm, cursor_nnf
    return aamm, semente + 1


def _ondas_por_execucao() -> int:
    """Os mesmos IPs são recusados no lote seguinte; por padrão, uma onda por execução."""
    try:
        valor = int(os.environ.get("NFE55_ONDAS_POR_EXECUCAO") or 1)
    except ValueError:
        valor = 1
    return max(1, min(valor, 10))


def _dispara_lote(pendentes: int, rotas: int) -> bool:
    if rotas < 2:
        return False
    return pendentes >= min(_tamanho_lote(), rotas)


def _faixa_proxy(transporte: Any) -> str:
    host = urlparse(transporte.current().proxy_url or "").hostname or "direct"
    return f"proxy-ip:{host}"


def _limitador() -> Any:
    return saida_rede.limitador_compartilhado()


def _abrir_sessao_rota(cert_path: Path, key_path: Path, transporte: Any) -> requests.Session:
    sessao = requests.Session()
    sessao.cert = (str(cert_path), str(key_path))
    sessao.verify = _ca_bundle()
    transporte.apply(sessao)
    return sessao


# Bloqueio por IP do portal de download: "IP não autorizado devido múltiplas consultas".
_DICAS_BLOQUEIO_IP = ("ip nao autorizado",)
_DICAS_LIMITE = (
    "muitas consultas", "muitas requisi", "excesso de requis", "too many", "bloqueio",
    "bloqueado", "tente novamente mais tarde", "limite de acesso", "acesso temporariamente",
)
_DICAS_INDISPONIVEL = (
    "cancelad", "inexistente", "não encontr", "nao encontr", "documento inválido",
    "documento invalido", "denegad", "chave de acesso inválida", "chave de acesso invalida",
)
_DICAS_ACESSO = ("/erro/forbidden", "acesso negado", "access denied")


_FUSO_SVRS = timezone(timedelta(hours=-3))
_BLOQUEADO_ATE_RE = re.compile(
    r"bloquead[oa]\s+at[ée]\s+(\d{2})/(\d{2})/(\d{4})\s+(\d{2}):(\d{2})", re.IGNORECASE,
)
BLOQUEIO_MAXIMO = timedelta(hours=24)


def bloqueado_ate_svrs(texto: str) -> datetime | None:
    """Fim do bloqueio "Acesso ao Download do XML bloqueado até dd/mm/aaaa hh:mm" (Brasília), em UTC."""
    achado = _BLOQUEADO_ATE_RE.search(html.unescape(texto or ""))
    if not achado:
        return None
    dia, mes, ano, hora, minuto = (int(parte) for parte in achado.groups())
    try:
        return datetime(ano, mes, dia, hora, minuto, tzinfo=_FUSO_SVRS).astimezone(timezone.utc)
    except ValueError:
        return None


def texto_bloqueio(ate: datetime) -> str:
    return ate.astimezone(_FUSO_SVRS).strftime("%d/%m/%Y %H:%M")


class Bloqueio:
    """Maior horário de bloqueio visto numa execução (as threads do lote registram aqui)."""

    def __init__(self) -> None:
        self._trava = threading.Lock()
        self.ate: datetime | None = None

    def registrar(self, ate: datetime | None) -> None:
        if ate is None:
            return
        agora = datetime.now(timezone.utc)
        ate = min(ate, agora + BLOQUEIO_MAXIMO)
        if ate <= agora:
            return
        with self._trava:
            if self.ate is None or ate > self.ate:
                self.ate = ate


class PortalSemXml(RuntimeError):
    def __init__(self, categoria: str, dica: str = "", bloqueado_ate: datetime | None = None) -> None:
        super().__init__(f"O portal não devolveu o XML modelo 55 desta chave ({categoria}).")
        self.categoria = categoria
        self.dica = dica
        self.bloqueado_ate = bloqueado_ate


def classificar_pagina(status: int, url: str, texto: str) -> tuple[str, str]:
    """Mesma leitura da página que a NFC-e faz, sem compartilhar código."""
    amostra = html.unescape(texto or "")[:8000].lower()
    sem_acento = unicodedata.normalize("NFKD", amostra).encode("ascii", "ignore").decode("ascii")
    for dica in _DICAS_BLOQUEIO_IP:
        if dica in sem_acento:
            return "limite", "ip bloqueado"
    if status in {401, 403} or "/erro/forbidden" in (url or "").lower():
        return "acesso", "forbidden"
    for categoria, dicas in (("acesso", _DICAS_ACESSO), ("limite", _DICAS_LIMITE), ("indisponivel", _DICAS_INDISPONIVEL)):
        for dica in dicas:
            if dica in amostra:
                return categoria, dica
    if status == 429:
        return "limite", "http 429"
    return "sem_xml", ""


def _categoria_download(exc: Exception) -> str:
    if isinstance(exc, PortalSemXml):
        return exc.categoria
    if isinstance(exc, requests.exceptions.ProxyError):
        return "proxy"
    if isinstance(exc, requests.Timeout):
        return "timeout"
    if isinstance(exc, requests.HTTPError) and getattr(exc.response, "status_code", None) == 429:
        return "limite"
    if isinstance(exc, RuntimeError) and "não devolveu o XML" in str(exc):
        return "sem_xml"
    return "http"


MOTIVO_DOWNLOAD = {
    "proxy": "Falha no proxy ao baixar o XML desta chave.",
    "timeout": "Tempo esgotado no portal ao baixar o XML desta chave.",
    "limite": "Limite da SVRS (429) ao baixar o XML desta chave.",
    "sem_xml": "O portal não devolveu o XML desta chave.",
    "indisponivel": "Portal informou nota indisponível (cancelada, denegada ou inexistente).",
    "acesso": "Portal recusou o acesso do certificado a esta chave.",
    "http": "Erro HTTP do portal ao baixar o XML desta chave.",
}


def _motivo_download(categoria: str) -> str:
    return MOTIVO_DOWNLOAD.get(categoria, MOTIVO_DOWNLOAD["sem_xml"])


def _baixar(cert_path: Path, key_path: Path, chave: str, transporte: Any = None) -> str:
    dono = _transporte() if transporte is None else transporte
    with _abrir_sessao_rota(cert_path, key_path, dono) as sessao:
        pagina = _enviar_rota(sessao, dono, "get", URL_PORTAL, timeout=45, headers=dict(CABECALHOS_NAVEGADOR))
        campos: dict[str, str] = {}
        for tag in re.findall(r"<input\b[^>]*>", pagina.text, flags=re.I):
            nome = re.search(r"\bname=[\"']([^\"']+)[\"']", tag, flags=re.I)
            if not nome:
                continue
            valor = re.search(r"\bvalue=[\"']([^\"']*)[\"']", tag, flags=re.I)
            campos[nome.group(1)] = valor.group(1) if valor else ""
        campos.update({"sistema": "Nfe", "OrigemSite": "0", "Ambiente": "1", "ChaveAcessoDfe": chave})
        resposta = _enviar_rota(
            sessao,
            dono,
            "post",
            URL_PORTAL,
            data=campos,
            timeout=45,
            headers={
                **CABECALHOS_NAVEGADOR,
                "Content-Type": "application/x-www-form-urlencoded",
                "Origin": ORIGEM_PORTAL,
                "Referer": str(getattr(pagina, "url", "") or URL_PORTAL),
            },
        )
    xml = extrair_xml_portal(resposta.text)
    if not xml or not xml_modelo_55(xml, chave):
        categoria, dica = classificar_pagina(resposta.status_code, str(resposta.url or ""), resposta.text)
        ate = bloqueado_ate_svrs(resposta.text) if categoria == "limite" else None
        # Só categoria, dica e horário do bloqueio: nunca o corpo da página nem a chave completa.
        print(
            f"[nfe55-saida] download sem XML http={resposta.status_code} categoria={categoria} "
            f"dica={dica!r} bloqueado_ate={texto_bloqueio(ate) if ate else '-'} "
            f"tamanho={len(resposta.text or '')} chave=...{chave[-6:]}",
            flush=True,
        )
        raise PortalSemXml(categoria, dica, ate)
    return xml


def _baixar_na_faixa(
    cert_path: Path,
    key_path: Path,
    chave: str,
    transporte: Any,
    limitador: Any,
    avisar_espera: Any = None,
    bloqueio: Bloqueio | None = None,
) -> tuple[str, str]:
    faixa = _faixa_proxy(transporte)
    slot, sonda = limitador.begin_download(notify_wait=avisar_espera, lane=faixa)
    if slot == "skip":
        return "", "limite"
    sucesso = False
    try:
        xml = _baixar(cert_path, key_path, chave, transporte)
        sucesso = bool(xml)
        return xml, ""
    except requests.HTTPError as exc:
        if _categoria_download(exc) == "limite":
            limitador.note_remote_limit()
        return "", _categoria_download(exc)
    except (requests.RequestException, RuntimeError) as exc:
        if _categoria_download(exc) == "limite":
            limitador.note_remote_limit()
            if bloqueio is not None and isinstance(exc, PortalSemXml):
                bloqueio.registrar(exc.bloqueado_ate)
        return "", _categoria_download(exc)
    finally:
        limitador.finish_download_probe(sonda, succeeded=sucesso)


def _descarregar_lote(
    cert_path: Path,
    key_path: Path,
    chaves: list[str],
    rotas: list[Any],
    avisar_espera: Any = None,
    ao_concluir: Any = None,
    bloqueio: Bloqueio | None = None,
    sondar: bool = False,
) -> list[tuple[str, str, str]]:
    """Uma chave por IP. O intervalo de 1 min vale ao reutilizar a mesma faixa.

    Com sondar, a primeira chave vai sozinha: se a SVRS responder limite, o lote para ali
    e as outras chaves não gastam tentativas (o bloqueio é por certificado, não por IP).
    """
    quantidade = min(len(chaves), len(rotas), _tamanho_lote())
    if quantidade < 1:
        return []
    pedaco = chaves[:quantidade]
    gestores = [saida_rede.GestorSaida([rota], enabled=True) for rota in rotas[:quantidade]]
    limitador = _limitador()
    resultados: dict[int, tuple[str, str, str]] = {}

    def um(indice: int, chave: str, gestor: Any) -> tuple[int, str, str, str]:
        xml, erro = _baixar_na_faixa(cert_path, key_path, chave, gestor, limitador, avisar_espera, bloqueio)
        return indice, chave, xml, erro

    def registrar(indice: int, chave: str, xml: str, erro: str) -> None:
        resultados[indice] = (chave, xml, erro)
        if ao_concluir:
            ao_concluir(chave, xml, erro)

    inicio = 0
    if sondar and quantidade > 1:
        registrar(*um(0, pedaco[0], gestores[0]))
        if resultados[0][2] == "limite":
            return [resultados[0]]
        inicio = 1
    restantes = list(range(inicio, quantidade))
    if restantes:
        with ThreadPoolExecutor(max_workers=len(restantes), thread_name_prefix="nfe55-saida-proxy") as pool:
            futuros = [pool.submit(um, indice, pedaco[indice], gestores[indice]) for indice in restantes]
            for futuro in as_completed(futuros):
                registrar(*futuro.result())
    return [resultados[indice] for indice in sorted(resultados)]


def _inteiro_env(nome: str, padrao: int, minimo: int, maximo: int) -> int:
    try:
        valor = int(os.environ.get(nome) or padrao)
    except ValueError:
        valor = padrao
    return max(minimo, min(valor, maximo))


TENTATIVAS_POR_CHAVE = 3
INTERVALO_MINIMO = 5
INTERVALO_MAXIMO = 180


class RitmoCertificado:
    """Ritmo do código base: um download por vez por certificado.

    O intervalo conta desde o último download que deu certo (tentativa recusada não zera o relógio),
    sobe um passo a cada recusa e desce um passo após 3 sucessos de primeira (entre 5 s e 180 s).
    """

    def __init__(self, intervalo: float, passo: float, clock: Any = None, sleep: Any = None) -> None:
        self.intervalo = float(max(INTERVALO_MINIMO, min(intervalo, INTERVALO_MAXIMO)))
        self.passo = float(max(1, passo))
        self.ultimo_sucesso: float | None = None
        self.seguidos = 0
        self._clock = clock or time.monotonic
        self._sleep = sleep or time.sleep

    def restante(self) -> float:
        if self.ultimo_sucesso is None:
            return 0.0
        return max(0.0, self.intervalo - (self._clock() - self.ultimo_sucesso))

    def espera_repeticao(self) -> float:
        # Sem sucesso de referência, repete após só um passo (como o base).
        return self.restante() if self.ultimo_sucesso is not None else self.passo

    def dormir(self, segundos: float) -> None:
        if segundos > 0:
            self._sleep(segundos)

    def sucesso(self, primeira: bool) -> None:
        self.ultimo_sucesso = self._clock()
        if not primeira:
            self.seguidos = 0
            return
        self.seguidos += 1
        if self.seguidos >= 3:
            self.intervalo = max(INTERVALO_MINIMO, self.intervalo - self.passo)
            self.seguidos = 0

    def recusa(self) -> None:
        self.seguidos = 0
        self.intervalo = min(INTERVALO_MAXIMO, self.intervalo + self.passo)


_ritmos: dict[str, RitmoCertificado] = {}
_ritmos_trava = threading.Lock()


def _ritmo_do_certificado(cnpj: str) -> RitmoCertificado:
    """O ritmo fica guardado por CNPJ e vale entre execuções do mesmo certificado."""
    with _ritmos_trava:
        ritmo = _ritmos.get(cnpj)
        if ritmo is None:
            ritmo = RitmoCertificado(
                _inteiro_env("NFE55_INTERVALO_DOWNLOAD", 55, INTERVALO_MINIMO, INTERVALO_MAXIMO),
                _inteiro_env("NFE55_PASSO_AJUSTE", 5, 1, 60),
            )
            _ritmos[cnpj] = ritmo
        return ritmo


def _paralelo_por_certificado() -> int:
    """Downloads simultâneos do mesmo certificado, cada um em um IP diferente (padrão 10)."""
    return _inteiro_env("NFE55_PARALELO_POR_CERTIFICADO", 10, 1, 100)


def _descarregar_em_ritmo(
    cert_path: Path,
    key_path: Path,
    chaves: list[str],
    rotas: list[Any],
    ritmo: RitmoCertificado,
    ao_concluir: Any = None,
    bloqueio: Bloqueio | None = None,
    avisar: Any = None,
    paralelo: int | None = None,
) -> None:
    """Blocos de até `paralelo` chaves do mesmo certificado, cada uma em um IP do rodízio.

    Entre um bloco e o seguinte vale o ritmo do certificado (55 s desde o último sucesso, +5/-5 s).
    A chave recusada volta no bloco seguinte por outro IP, até 3 tentativas; nota indisponível ou
    acesso negado não repetem. Bloqueio com horário da SVRS encerra na hora.
    avisar(texto, posicao) devolve True para cancelar.
    """
    limitador = _limitador()
    largura = max(1, min(paralelo or _paralelo_por_certificado(), len(rotas) or 1))
    proxima_rota = 0
    tentativas: dict[str, int] = {}
    pendentes = list(chaves)
    concluidas = 0
    bloco = 0

    def gestor_seguinte() -> Any:
        nonlocal proxima_rota
        if not rotas:
            return _transporte()
        gestor = saida_rede.GestorSaida([rotas[proxima_rota % len(rotas)]], enabled=True)
        proxima_rota += 1
        return gestor

    while pendentes:
        espera = ritmo.restante() if bloco else 0.0
        if espera > 0:
            if avisar and avisar(
                f"aguardando {int(round(espera))} s (ritmo do certificado {int(ritmo.intervalo)} s, {largura} por bloco)",
                concluidas + 1,
            ):
                return
            ritmo.dormir(espera)
        # O primeiro bloco é a sonda: 1 chave só; com o certificado bloqueado, gasta 1 tentativa e não 10.
        tamanho = 1 if bloco == 0 else largura
        bloco += 1
        atual, pendentes = pendentes[:tamanho], pendentes[tamanho:]
        trabalhos = [(chave, gestor_seguinte()) for chave in atual]
        resultados: dict[str, tuple[str, str]] = {}
        if len(trabalhos) == 1:
            chave, gestor = trabalhos[0]
            resultados[chave] = _baixar_na_faixa(cert_path, key_path, chave, gestor, limitador, None, bloqueio)
        else:
            with ThreadPoolExecutor(max_workers=len(trabalhos), thread_name_prefix="nfe55-saida-cert") as pool:
                futuros = {
                    pool.submit(_baixar_na_faixa, cert_path, key_path, chave, gestor, limitador, None, bloqueio): chave
                    for chave, gestor in trabalhos
                }
                for futuro in as_completed(futuros):
                    resultados[futuros[futuro]] = futuro.result()
        sucesso_de_primeira = False
        houve_sucesso = False
        houve_recusa = False
        repetir: list[str] = []
        parar = bool(bloqueio is not None and bloqueio.ate)
        for chave in atual:
            xml, erro = resultados[chave]
            tentativas[chave] = tentativas.get(chave, 0) + 1
            if xml:
                houve_sucesso = True
                sucesso_de_primeira = sucesso_de_primeira or tentativas[chave] == 1
            else:
                houve_recusa = houve_recusa or erro not in {"indisponivel", "acesso"}
                final = (
                    parar
                    or erro in {"indisponivel", "acesso"}
                    or tentativas[chave] >= TENTATIVAS_POR_CHAVE
                )
                if not final:
                    repetir.append(chave)
                    continue
            concluidas += 1
            if ao_concluir:
                ao_concluir(chave, xml, erro)
        if houve_sucesso:
            ritmo.sucesso(primeira=sucesso_de_primeira and not houve_recusa)
        if houve_recusa:
            ritmo.recusa()
        if parar:
            return
        esgotadas_por_limite = [
            chave for chave in atual
            if not resultados[chave][0] and resultados[chave][1] == "limite" and tentativas[chave] >= TENTATIVAS_POR_CHAVE
        ]
        if esgotadas_por_limite and not houve_sucesso:
            # Bloco inteiro recusado por limite na última tentativa: os IPs estão recusando.
            return
        # As recusadas voltam na frente, por outro IP, no próximo bloco.
        pendentes = repetir + pendentes


def _executar(run_id: str, token: str, semente: bytes, pfx: bytes, senha: str, opcoes: dict[str, Any]) -> None:
    pasta = Path(tempfile.mkdtemp(prefix="nfe55_saida_"))
    aamm, nnf, consultadas = "", 0, 0
    lacunas: list[dict[str, Any]] = []
    try:
        cert_path, key_path = _pfx(pfx, senha, pasta)
        cfg = cfg_da_chave(opcoes["chave"]) if opcoes.get("chave") else ler_xml_semente(semente)
        if opcoes.get("cnpj") and opcoes["cnpj"] != cfg["CNPJ"]:
            raise RuntimeError("A semente não pertence ao CNPJ da empresa.")
        rotas = _rotas_proxy()
        lote = _lote_ativo(rotas)
        with _abrir_sessao(cert_path, key_path) as sessao:
            if opcoes.get("somente_chave"):
                chave_unica = cfg["chave_semente"]
                if lote:
                    baixados = _descarregar_lote(cert_path, key_path, [chave_unica], rotas)
                    xml = baixados[0][1] if baixados else ""
                    if not xml:
                        raise RuntimeError("O portal não devolveu o XML modelo 55 desta chave.")
                else:
                    xml = _baixar(cert_path, key_path, chave_unica)
                _callback(run_id, token, "xml", chave=chave_unica, aamm=cfg["AAMM"], nnf=cfg["nNF_semente"], xml=xml)
                _callback(run_id, token, "done", mensagem="Chave baixada.", consultadas=0, encontradas=1, salvas=1)
                return
            aamm, nnf = _ponto_de_partida(cfg, opcoes)
            consecutivos = 0
            consultadas = 0
            encontradas: list[str] = []
            fila: list[str] = []
            salvas = 0
            falhas = 0
            onda_inicio = 1
            ondas = 0
            downloads_parados = ""
            bloqueio = Bloqueio()
            ritmo = _ritmo_do_certificado(cfg["CNPJ"])
            limite = min(int(opcoes.get("max_numeracoes") or 300), MAX_NUMEROS)
            parada = max(1, min(int(opcoes.get("stop_217") or 15), 100))

            def avisar_espera() -> None:
                _callback(
                    run_id, token, "progress",
                    mensagem=f"Aguardando intervalo de 1 min para reutilizar o lote de {len(rotas)} IPs · {salvas} salvas",
                    aamm=aamm, nnf=nnf, consultadas=consultadas, encontradas=len(encontradas),
                )

            def publicar(chave: str, xml: str) -> None:
                nonlocal salvas
                if not xml:
                    return
                _callback(run_id, token, "xml", chave=chave, aamm=chave[2:6], nnf=int(chave[25:34]), xml=xml)
                salvas += 1

            def esvaziar(final: bool = False, origem: str = "Baixando") -> bool:
                nonlocal onda_inicio, falhas, ondas, downloads_parados
                if not lote:
                    return False
                if downloads_parados:
                    fila.clear()
                    return False
                while fila:
                    capacidade = min(_tamanho_lote(), len(rotas))
                    if not final and not _dispara_lote(len(fila), len(rotas)):
                        break
                    pedaco = fila[:capacidade]
                    del fila[:capacidade]
                    fim = onda_inicio + len(pedaco) - 1
                    mensagem = (
                        f"{origem} lote {onda_inicio}-{fim} · {_paralelo_por_certificado()} por vez, ritmo do certificado "
                        f"{int(ritmo.intervalo)} s · {len(rotas)} IP(s) em rodízio"
                    )
                    if _callback(run_id, token, "progress", mensagem=mensagem, aamm=aamm, nnf=nnf, consultadas=consultadas, encontradas=len(encontradas)):
                        _callback(run_id, token, "done", mensagem="Busca cancelada.", consultadas=consultadas, encontradas=len(encontradas))
                        return True
                    feitos = 0
                    baixados_na_onda = 0
                    sem_xml_na_onda = 0
                    houve_limite = False
                    cancelado = False

                    def avisar(texto: str, posicao: int) -> bool:
                        nonlocal cancelado
                        cancelado = _callback(
                            run_id, token, "progress",
                            mensagem=f"{origem} {posicao}/{len(pedaco)} · {salvas} salvas · {sem_xml_na_onda} sem XML · {texto}",
                            aamm=aamm, nnf=nnf, consultadas=consultadas, encontradas=len(encontradas),
                        )
                        return cancelado

                    def ao_concluir(chave: str, xml: str, erro: str) -> None:
                        nonlocal feitos, houve_limite, falhas, baixados_na_onda, sem_xml_na_onda
                        feitos += 1
                        if xml:
                            baixados_na_onda += 1
                            publicar(chave, xml)
                        else:
                            falhas += 1
                            sem_xml_na_onda += 1
                            houve_limite = houve_limite or erro == "limite"
                            motivo = _motivo_download(erro)
                            if erro == "limite" and bloqueio.ate:
                                motivo = f"Download bloqueado pela SVRS até {texto_bloqueio(bloqueio.ate)}."
                            _callback(
                                run_id, token, "download_falhou", chave=chave,
                                aamm=chave[2:6], nnf=int(chave[25:34]),
                                erro=motivo,
                            )
                        nonlocal cancelado
                        cancelado = _callback(
                            run_id, token, "progress",
                            mensagem=(
                                f"{origem} {feitos}/{len(pedaco)} · {salvas} salvas · {sem_xml_na_onda} sem XML"
                                f" · ritmo do certificado {int(ritmo.intervalo)} s"
                            ),
                            aamm=aamm, nnf=nnf, consultadas=consultadas, encontradas=len(encontradas),
                        ) or cancelado

                    _descarregar_em_ritmo(
                        cert_path, key_path, pedaco, rotas, ritmo, ao_concluir, bloqueio=bloqueio,
                        avisar=avisar,
                    )
                    if cancelado:
                        _callback(run_id, token, "done", mensagem="Busca cancelada.", consultadas=consultadas, encontradas=len(encontradas), salvas=salvas)
                        return True
                    onda_inicio = fim + 1
                    ondas += 1
                    if houve_limite and bloqueio.ate:
                        downloads_parados = f"Download bloqueado pela SVRS até {texto_bloqueio(bloqueio.ate)}."
                    elif houve_limite:
                        downloads_parados = "Limite da SVRS (429) no download."
                    elif not baixados_na_onda:
                        downloads_parados = "O portal não devolveu XML neste lote."
                    elif ondas >= _ondas_por_execucao():
                        downloads_parados = "Lote de download desta execução concluído."
                    if downloads_parados:
                        # As chaves que ficaram já estão nas lacunas com a chave real.
                        fila.clear()
                        break
                return False

            def guardar(chave: str, origem: str = "Baixando") -> bool:
                nonlocal downloads_parados, falhas
                if downloads_parados:
                    return False
                if not lote:
                    time.sleep(60)
                    try:
                        publicar(chave, _baixar(cert_path, key_path, chave))
                    except (requests.RequestException, RuntimeError) as exc:
                        falhas += 1
                        downloads_parados = _motivo_download(_categoria_download(exc))
                        _callback(
                            run_id, token, "download_falhou", chave=chave,
                            aamm=chave[2:6], nnf=int(chave[25:34]), erro=downloads_parados,
                        )
                    return False
                fila.append(chave)
                return esvaziar(False, origem)

            if lote:
                aviso = f"Lote de {len(rotas)} proxies pronto"
            elif saida_rede.proxy_configurado():
                aviso = f"Lote de proxies indisponível ({len(rotas)} rota(s)); download 1 a 1"
            else:
                aviso = ""
            if aviso and _callback(run_id, token, "progress", mensagem=aviso, aamm=aamm, nnf=nnf, consultadas=0, encontradas=0):
                _callback(run_id, token, "done", mensagem="Busca cancelada.", consultadas=0, encontradas=0)
                return
            chaves_faltantes = chaves_para_recuperar(cfg, opcoes.get("lacunas_abertas"))
            vaga_recuperacao = max(1, min(_tamanho_lote(), len(rotas))) if lote else 1
            for aamm_antigo, nnf_antigo in numeros_sem_chave(cfg, opcoes.get("lacunas_abertas")):
                if len(chaves_faltantes) >= vaga_recuperacao:
                    break
                # Pendência antiga sem chave real: a consulta devolve a chave verdadeira.
                _codigo, _motivo, real = interpretar_consulta(
                    _consultar(sessao, cfg, nnf_antigo, aamm_antigo), cfg, nnf_antigo, aamm_antigo,
                )
                if real and real not in chaves_faltantes:
                    chaves_faltantes.append(real)
                    _callback(
                        run_id, token, "descoberta", chave=real, aamm=aamm_antigo, nnf=nnf_antigo,
                        erro="Chave localizada; XML aguardando download",
                    )
                time.sleep(0.7)
            chaves_faltantes = chaves_faltantes[:vaga_recuperacao]
            if chaves_faltantes:
                if _callback(run_id, token, "progress", mensagem=f"Recuperando {len(chaves_faltantes)} nota(s) faltante(s) antes das novas", aamm=aamm, nnf=nnf, consultadas=0, encontradas=len(chaves_faltantes)):
                    _callback(run_id, token, "done", mensagem="Busca cancelada.", consultadas=0, encontradas=len(chaves_faltantes))
                    return
                for chave_faltante in chaves_faltantes:
                    encontradas.append(chave_faltante)
                    if guardar(chave_faltante, "Recuperando faltantes"):
                        return
                if esvaziar(True, "Recuperando faltantes"):
                    return
                aamm, nnf = avancar_sobre_recuperadas(
                    aamm, nnf, {(chave[2:6], int(chave[25:34])) for chave in chaves_faltantes},
                )
            while consultadas < limite:
                if _callback(run_id, token, "progress", mensagem=f"Consultando {aamm} nNF {nnf}", aamm=aamm, nnf=nnf, consultadas=consultadas, encontradas=len(encontradas)):
                    _callback(run_id, token, "done", mensagem="Busca cancelada.", consultadas=consultadas, encontradas=len(encontradas))
                    return
                atual = _consultar(sessao, cfg, nnf, aamm)
                consultadas += 1
                passo = avancar(cfg, aamm, nnf, consecutivos, parada, atual)
                if passo.encerrar:
                    if esvaziar(True):
                        return
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
                        _callback(
                            run_id, token, "descoberta", chave=recuperada,
                            aamm=recuperada[2:6], nnf=int(recuperada[25:34]),
                            erro="Chave localizada; XML aguardando download",
                        )
                        if guardar(recuperada) or esvaziar(True):
                            return
                        aamm = recuperada[2:6]
                        nnf = int(recuperada[25:34]) + 1
                        consecutivos = 0
                        continue
                    # Fim da numeração: os números vazios do fim não são lacunas e o
                    # cursor volta ao primeiro deles, para a próxima volta reconsultar.
                    lacunas[:] = [
                        item for item in lacunas
                        if not (item["aamm"] == aamm and item["nnf"] >= inicio)
                    ]
                    nnf = inicio
                    break
                aamm, nnf, consecutivos = passo.aamm, passo.nnf, passo.consecutivos_217
                if passo.encontrada:
                    encontradas.append(passo.encontrada)
                    _callback(
                        run_id, token, "descoberta", chave=passo.encontrada,
                        aamm=passo.encontrada[2:6], nnf=int(passo.encontrada[25:34]),
                        erro="Chave localizada; XML aguardando download",
                    )
                    if guardar(passo.encontrada):
                        return
                elif passo.lacuna:
                    lacunas.append({"aamm": aamm, "nnf": nnf - 1, "erro": "Numeração ainda não localizada na consulta"})
                time.sleep(0.7)
            if esvaziar(True):
                return
        mensagem = f"Busca de NF-e de saída concluída. {salvas} XML(s) salvos."
        if falhas:
            mensagem += f" {falhas} download(s) ficaram sem XML."
        if downloads_parados:
            pendentes = max(0, len(encontradas) - salvas - falhas)
            mensagem += f" {downloads_parados} {pendentes} chave(s) guardadas para a próxima vez."
        extra = {"svrs_bloqueado_ate": bloqueio.ate.isoformat()} if bloqueio.ate else {}
        _callback(
            run_id, token, "done", mensagem=mensagem,
            consultadas=consultadas, encontradas=len(encontradas), salvas=salvas,
            aamm=aamm, nnf=nnf, lacunas=lacunas[-200:], **extra,
        )
    except Exception as exc:
        erro = "Falha de proxy no download." if isinstance(exc, requests.exceptions.ProxyError) else str(exc)[:500]
        # Guarda onde a consulta parou; as chaves já localizadas estão nas lacunas.
        cursor = {"aamm": aamm, "nnf": nnf, "consultadas": consultadas, "lacunas": lacunas[-200:]} if aamm and nnf else {}
        _callback(run_id, token, "error", erro=erro, **cursor)
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
    cursor_aamm: str = Form(""),
    cursor_nnf: int = Form(0),
    lacunas_abertas: str = Form("[]"),
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
            "cursor_aamm": re.sub(r"\D", "", cursor_aamm)[:4],
            "cursor_nnf": cursor_nnf,
            "lacunas_abertas": lacunas_abertas,
        })
    except HTTPException:
        _vaga.release()
        raise
    except Exception as exc:
        _vaga.release()
        raise HTTPException(status_code=400, detail=str(exc)) from exc
    return {"id": run_id}
