"""Worker de NF-e modelo 55 de saída. Não compartilha rota nem estado com a NFC-e."""

from __future__ import annotations

import os
import re
import shutil
import tempfile
import threading
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
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


def _transporte():
    """Mesma saída da NFC-e. Limite da SVRS não troca o proxy."""
    from nfce_download_worker import shared_outbound_transport

    return shared_outbound_transport()


def _abrir_sessao(cert_path: Path, key_path: Path) -> requests.Session:
    sessao = requests.Session()
    sessao.cert = (str(cert_path), str(key_path))
    sessao.verify = _ca_bundle()
    _transporte().apply(sessao)
    return sessao


def _esperar_limite() -> None:
    from nfce_download_worker import sefaz_cooldown_seconds

    time.sleep(sefaz_cooldown_seconds())


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
    try:
        tamanho = int(os.getenv("NFCE_PROXY_BATCH_SIZE", "100"))
    except (TypeError, ValueError):
        tamanho = 100
    return max(1, min(100, tamanho))


def _rotas_proxy() -> list[Any]:
    """Mesmo pool da NFC-e. Sem duas rotas, o download segue um a um."""
    from nfce_download_worker import OutboundRoute, webshare_pilot_routes

    tamanho = _tamanho_lote()
    chave = os.getenv("NFCE_PROXY_PILOT_WEBSHARE_API_KEY", "").strip()
    rotas: list[Any] = []
    if chave:
        rotas = webshare_pilot_routes(
            chave,
            os.getenv("NFCE_PROXY_PILOT_WEBSHARE_PLAN_ID", "").strip(),
            tamanho,
        )
    if rotas:
        return rotas[:tamanho]
    vistas: set[str] = set()
    for slot in range(1, tamanho + 1):
        sufixo = "" if slot == 1 else f"_{slot}"
        url = os.getenv(f"NFCE_PROXY_PILOT_URL{sufixo}", "").strip()
        if not url or url in vistas:
            continue
        vistas.add(url)
        usuario = os.getenv(f"NFCE_PROXY_PILOT_USERNAME{sufixo}") or os.getenv("NFCE_PROXY_PILOT_USERNAME", "")
        senha = os.getenv(f"NFCE_PROXY_PILOT_PASSWORD{sufixo}") or os.getenv("NFCE_PROXY_PILOT_PASSWORD", "")
        rotas.append(OutboundRoute(f"outbound-{slot}", url, usuario, senha))
        if len(rotas) == tamanho:
            break
    return rotas[:tamanho]


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


def _dispara_lote(pendentes: int, rotas: int) -> bool:
    if rotas < 2:
        return False
    return pendentes >= min(_tamanho_lote(), rotas)


def _faixa_proxy(transporte: Any) -> str:
    host = urlparse(transporte.current().proxy_url or "").hostname or "direct"
    return f"proxy-ip:{host}"


def _limitador() -> Any:
    from nfce_download_worker import clamp_download_interval, shared_rate_limiter

    return shared_rate_limiter(0.1, clamp_download_interval(60))


def _abrir_sessao_rota(cert_path: Path, key_path: Path, transporte: Any) -> requests.Session:
    sessao = requests.Session()
    sessao.cert = (str(cert_path), str(key_path))
    sessao.verify = _ca_bundle()
    transporte.apply(sessao)
    return sessao


def _categoria_download(exc: Exception) -> str:
    if isinstance(exc, requests.exceptions.ProxyError):
        return "proxy"
    if isinstance(exc, requests.Timeout):
        return "timeout"
    if isinstance(exc, requests.HTTPError) and getattr(exc.response, "status_code", None) == 429:
        return "limite"
    if isinstance(exc, RuntimeError) and "não devolveu o XML" in str(exc):
        return "sem_xml"
    return "http"


def _baixar(cert_path: Path, key_path: Path, chave: str, transporte: Any = None) -> str:
    dono = _transporte() if transporte is None else transporte
    with _abrir_sessao_rota(cert_path, key_path, dono) as sessao:
        pagina = _enviar_rota(sessao, dono, "get", URL_PORTAL, timeout=45)
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
            headers={"Referer": URL_PORTAL, "Content-Type": "application/x-www-form-urlencoded"},
        )
    xml = extrair_xml_portal(resposta.text)
    if not xml or not xml_modelo_55(xml, chave):
        raise RuntimeError("O portal não devolveu o XML modelo 55 desta chave.")
    return xml


def _baixar_na_faixa(
    cert_path: Path,
    key_path: Path,
    chave: str,
    transporte: Any,
    limitador: Any,
    avisar_espera: Any = None,
) -> tuple[str, str]:
    faixa = _faixa_proxy(transporte)
    slot = limitador.begin_download(notify_wait=avisar_espera, lane=faixa)
    if slot == "skip":
        return "", "limite"
    try:
        xml = _baixar(cert_path, key_path, chave, transporte)
    except requests.HTTPError as exc:
        if _categoria_download(exc) == "limite":
            limitador.note_remote_limit()
        return "", _categoria_download(exc)
    except (requests.RequestException, RuntimeError) as exc:
        return "", _categoria_download(exc)
    limitador.note_download_ok()
    return xml, ""


def _descarregar_lote(
    cert_path: Path,
    key_path: Path,
    chaves: list[str],
    rotas: list[Any],
    avisar_espera: Any = None,
    ao_concluir: Any = None,
) -> list[tuple[str, str, str]]:
    """Uma chave por IP. O intervalo de 1 min vale ao reutilizar a mesma faixa."""
    from nfce_download_worker import OutboundTransportManager

    quantidade = min(len(chaves), len(rotas), _tamanho_lote())
    if quantidade < 1:
        return []
    pedaco = chaves[:quantidade]
    gestores = [OutboundTransportManager([rota], enabled=True) for rota in rotas[:quantidade]]
    limitador = _limitador()
    resultados: dict[int, tuple[str, str, str]] = {}

    def um(indice: int, chave: str, gestor: Any) -> tuple[int, str, str, str]:
        xml, erro = _baixar_na_faixa(cert_path, key_path, chave, gestor, limitador, avisar_espera)
        return indice, chave, xml, erro

    with ThreadPoolExecutor(max_workers=quantidade, thread_name_prefix="nfe55-saida-proxy") as pool:
        futuros = [pool.submit(um, indice, chave, gestor) for indice, (chave, gestor) in enumerate(zip(pedaco, gestores))]
        for futuro in as_completed(futuros):
            indice, chave, xml, erro = futuro.result()
            resultados[indice] = (chave, xml, erro)
            if ao_concluir:
                ao_concluir(chave, xml, erro)
    return [resultados[indice] for indice in range(quantidade)]


def _executar(run_id: str, token: str, semente: bytes, pfx: bytes, senha: str, opcoes: dict[str, Any]) -> None:
    pasta = Path(tempfile.mkdtemp(prefix="nfe55_saida_"))
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
            lacunas: list[dict[str, Any]] = []
            fila: list[str] = []
            salvas = 0
            falhas = 0
            onda_inicio = 1
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

            def esvaziar(final: bool = False) -> bool:
                nonlocal onda_inicio, falhas
                if not lote:
                    return False
                while fila:
                    capacidade = min(_tamanho_lote(), len(rotas))
                    if not final and not _dispara_lote(len(fila), len(rotas)):
                        break
                    pedaco = fila[:capacidade]
                    del fila[:capacidade]
                    fim = onda_inicio + len(pedaco) - 1
                    faixa = f"/{capacidade}" if len(pedaco) == capacidade else ""
                    mensagem = f"Baixando lote {onda_inicio}-{fim}{faixa} · {len(pedaco)} proxy(s) em paralelo"
                    if _callback(run_id, token, "progress", mensagem=mensagem, aamm=aamm, nnf=nnf, consultadas=consultadas, encontradas=len(encontradas)):
                        _callback(run_id, token, "done", mensagem="Busca cancelada.", consultadas=consultadas, encontradas=len(encontradas))
                        return True
                    feitos = 0
                    houve_limite = False

                    def ao_concluir(chave: str, xml: str, erro: str) -> None:
                        nonlocal feitos, houve_limite, falhas
                        feitos += 1
                        if xml:
                            publicar(chave, xml)
                        else:
                            falhas += 1
                            houve_limite = houve_limite or erro == "limite"
                        _callback(
                            run_id, token, "progress",
                            mensagem=f"Baixando {feitos}/{len(pedaco)} · {salvas} salvas · {len(pedaco)} proxy(s) em paralelo",
                            aamm=aamm, nnf=nnf, consultadas=consultadas, encontradas=len(encontradas),
                        )

                    _descarregar_lote(
                        cert_path, key_path, pedaco, rotas, avisar_espera if onda_inicio > 1 else None, ao_concluir,
                    )
                    onda_inicio = fim + 1
                    if houve_limite:
                        _callback(
                            run_id, token, "done",
                            mensagem="Limite da SVRS no download. A busca para neste ponto.",
                            consultadas=consultadas, encontradas=len(encontradas), salvas=salvas,
                            aamm=aamm, nnf=nnf, lacunas=lacunas[-200:],
                        )
                        return True
                return False

            def guardar(chave: str) -> bool:
                if not lote:
                    time.sleep(60)
                    publicar(chave, _baixar(cert_path, key_path, chave))
                    return False
                fila.append(chave)
                return esvaziar(False)

            if lote:
                aviso = f"Lote de {len(rotas)} proxies pronto"
            elif os.getenv("NFCE_PROXY_PILOT_WEBSHARE_API_KEY", "").strip() or os.getenv("NFCE_PROXY_PILOT_URL", "").strip():
                aviso = f"Lote de proxies indisponível ({len(rotas)} rota(s)); download 1 a 1"
            else:
                aviso = ""
            if aviso and _callback(run_id, token, "progress", mensagem=aviso, aamm=aamm, nnf=nnf, consultadas=0, encontradas=0):
                _callback(run_id, token, "done", mensagem="Busca cancelada.", consultadas=0, encontradas=0)
                return
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
                        if guardar(recuperada) or esvaziar(True):
                            return
                        aamm = recuperada[2:6]
                        nnf = int(recuperada[25:34]) + 1
                        consecutivos = 0
                        continue
                    lacunas.append({"aamm": aamm, "nnf": nnf})
                    break
                aamm, nnf, consecutivos = passo.aamm, passo.nnf, passo.consecutivos_217
                if passo.encontrada:
                    encontradas.append(passo.encontrada)
                    if guardar(passo.encontrada):
                        return
                elif passo.lacuna:
                    lacunas.append({"aamm": aamm, "nnf": nnf - 1})
                time.sleep(0.7)
            if esvaziar(True):
                return
        mensagem = "Busca de NF-e de saída concluída."
        if falhas:
            mensagem += f" {falhas} download(s) ficaram sem XML."
        _callback(
            run_id, token, "done", mensagem=mensagem,
            consultadas=consultadas, encontradas=len(encontradas), salvas=salvas,
            aamm=aamm, nnf=nnf, lacunas=lacunas[-200:],
        )
    except Exception as exc:
        erro = "Falha de proxy no download." if isinstance(exc, requests.exceptions.ProxyError) else str(exc)[:500]
        _callback(run_id, token, "error", erro=erro)
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
        })
    except HTTPException:
        _vaga.release()
        raise
    except Exception as exc:
        _vaga.release()
        raise HTTPException(status_code=400, detail=str(exc)) from exc
    return {"id": run_id}
