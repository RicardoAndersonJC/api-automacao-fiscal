"""Saída de rede e limitador próprios da NF-e de saída (modelo 55).

Não importa nada da NFC-e. Estado, proxies e cooldown ficam só neste processo da saída:
um 429 da NF-e de saída não pausa a NFC-e, e vice-versa.

Variáveis de ambiente (todas com prefixo NFE55_):
- NFE55_PROXY_WEBSHARE_API_KEY / NFE55_PROXY_WEBSHARE_PLAN_ID: lista de proxies do Webshare.
- NFE55_PROXY_URL[_n], NFE55_PROXY_USERNAME[_n], NFE55_PROXY_PASSWORD[_n]: proxies fixos.
- NFE55_PROXY_BATCH_SIZE: tamanho do lote (1 a 100, padrão 100).
- NFE55_COOLDOWN_SECONDS: espera após limite da SVRS (padrão 60, mínimo 1).
Se nenhuma NFE55_PROXY_* estiver preenchida, usa os mesmos valores da NFC-e
(NFCE_PROXY_PILOT_*, NFCE_PROXY_BATCH_SIZE e SEFAZ_COOLDOWN_SECONDS). Só a configuração
é reaproveitada; o estado (limitador, saúde das rotas) continua separado.
Sem proxy configurado, a saída usa a conexão direta do processo.
"""

from __future__ import annotations

import ipaddress
import json
import logging
import os
import threading
import time
from collections import deque
from dataclasses import dataclass
from typing import Any
from urllib.parse import quote, urlparse

import requests

_logger = logging.getLogger("nfe55_saida_transport")

COOLDOWN_PADRAO = 60
INTERVALO_MIN = 60
INTERVALO_MAX = 120
LOTE_MAX = 100


_NOMES_PROPRIOS = {
    "webshare_key": "NFE55_PROXY_WEBSHARE_API_KEY",
    "webshare_plan": "NFE55_PROXY_WEBSHARE_PLAN_ID",
    "url": "NFE55_PROXY_URL",
    "username": "NFE55_PROXY_USERNAME",
    "password": "NFE55_PROXY_PASSWORD",
    "batch": "NFE55_PROXY_BATCH_SIZE",
}
_NOMES_NFCE = {
    "webshare_key": "NFCE_PROXY_PILOT_WEBSHARE_API_KEY",
    "webshare_plan": "NFCE_PROXY_PILOT_WEBSHARE_PLAN_ID",
    "url": "NFCE_PROXY_PILOT_URL",
    "username": "NFCE_PROXY_PILOT_USERNAME",
    "password": "NFCE_PROXY_PILOT_PASSWORD",
    "batch": "NFCE_PROXY_BATCH_SIZE",
}


def _texto(env: Any, nome: str) -> str:
    return str(env.get(nome) or "").strip()


def nomes_proxy(environ: dict[str, str] | None = None) -> dict[str, str]:
    """Variáveis NFE55_PROXY_* quando alguma estiver preenchida; senão, as mesmas da NFC-e."""
    env = environ if environ is not None else os.environ
    if _texto(env, _NOMES_PROPRIOS["webshare_key"]) or _texto(env, _NOMES_PROPRIOS["url"]):
        return _NOMES_PROPRIOS
    return _NOMES_NFCE


def cooldown_segundos() -> float:
    bruto = os.getenv("NFE55_COOLDOWN_SECONDS") or os.getenv("SEFAZ_COOLDOWN_SECONDS") or str(COOLDOWN_PADRAO)
    try:
        valor = float(bruto)
    except (TypeError, ValueError):
        valor = float(COOLDOWN_PADRAO)
    return max(1.0, valor)


def intervalo_download(segundos: int) -> int:
    """Espaço entre downloads na mesma faixa, entre 1 e 2 min."""
    try:
        valor = int(segundos)
    except (TypeError, ValueError):
        valor = INTERVALO_MIN
    return max(INTERVALO_MIN, min(INTERVALO_MAX, valor))


def tamanho_lote() -> int:
    bruto = os.getenv("NFE55_PROXY_BATCH_SIZE") or os.getenv(nomes_proxy()["batch"]) or str(LOTE_MAX)
    try:
        tamanho = int(bruto)
    except (TypeError, ValueError):
        tamanho = LOTE_MAX
    return max(1, min(LOTE_MAX, tamanho))


@dataclass
class Rota:
    outbound_id: str
    proxy_url: str | None = None
    username: str = ""
    password: str = ""
    health: str = "healthy"
    unhealthy_until: float = 0.0


class GestorSaida:
    """Falha de proxy pode trocar de rota. Limite da SVRS não troca."""

    def __init__(self, rotas: list[Rota], enabled: bool = False, cooldown: float | None = None, clock: Any = None) -> None:
        self.routes = rotas or [Rota("direct", None)]
        self.enabled = enabled and any(rota.proxy_url for rota in self.routes)
        self.cooldown_seconds = float(cooldown) if cooldown is not None else cooldown_segundos()
        self._clock = clock or time.monotonic
        self._lock = threading.Lock()
        self.index = 0

    def current(self) -> Rota:
        with self._lock:
            self._refresh_locked(float(self._clock()))
            return self.routes[self.index]

    def _refresh_locked(self, agora: float) -> None:
        for rota in self.routes:
            if rota.health == "unhealthy" and agora >= rota.unhealthy_until:
                rota.health = "healthy"
        if self.routes[self.index].health == "healthy":
            return
        for passo in range(1, len(self.routes) + 1):
            candidato = (self.index + passo) % len(self.routes)
            if self.routes[candidato].health == "healthy":
                self.index = candidato
                return

    @staticmethod
    def _url_autenticada(rota: Rota) -> str:
        bruto = str(rota.proxy_url or "")
        if not rota.username:
            return bruto
        parsed = urlparse(bruto)
        porta = f":{parsed.port}" if parsed.port else ""
        usuario = quote(rota.username, safe="")
        senha = quote(rota.password, safe="")
        return f"{parsed.scheme or 'http'}://{usuario}:{senha}@{parsed.hostname or ''}{porta}"

    def apply(self, sessao: requests.Session) -> None:
        """Define o proxy da sessão. Não altera sessao.verify."""
        sessao.proxies.clear()
        if not self.enabled:
            return
        rota = self.current()
        if rota.proxy_url:
            url = self._url_autenticada(rota)
            sessao.proxies.update({"http": url, "https": url})

    def note_infrastructure_failure(self) -> bool:
        with self._lock:
            agora = float(self._clock())
            atual = self.routes[self.index]
            atual.health = "unhealthy"
            atual.unhealthy_until = agora + self.cooldown_seconds
            origem = self.index
            for passo in range(1, len(self.routes) + 1):
                candidato = (origem + passo) % len(self.routes)
                if candidato != origem and self.routes[candidato].health == "healthy":
                    self.index = candidato
                    return True
            return False

    def note_remote_limit(self) -> None:
        return None

    def note_success(self) -> None:
        with self._lock:
            self.routes[self.index].health = "healthy"
            self.routes[self.index].unhealthy_until = 0.0


def rotas_webshare(api_key: str, plan_id: str, limite: int = LOTE_MAX) -> list[Rota]:
    rotas: list[Rota] = []
    vistos: set[str] = set()
    try:
        for pagina in range(1, 1 + (limite + 24) // 25 + 3):
            params: dict[str, Any] = {"mode": "direct", "page": pagina, "page_size": 25, "valid": "true"}
            if plan_id:
                params["plan_id"] = plan_id
            resposta = requests.get(
                "https://proxy.webshare.io/api/v2/proxy/list/",
                params=params, headers={"Authorization": f"Token {api_key}"},
                timeout=(3, 5), allow_redirects=False,
            )
            if resposta.status_code != 200:
                _logger.warning(json.dumps({"event": "nfe55_webshare_list_failed", "status": resposta.status_code, "page": pagina}))
                return rotas
            dados = resposta.json()
            for proxy in dados["results"]:
                try:
                    endereco = str(ipaddress.IPv4Address(proxy["proxy_address"]))
                    porta = int(proxy["port"])
                except (ValueError, TypeError, KeyError):
                    continue
                if not proxy.get("valid") or endereco in vistos or not 1 <= porta <= 65535:
                    continue
                vistos.add(endereco)
                rotas.append(Rota(f"nfe55-{len(rotas) + 1}", f"http://{endereco}:{porta}", str(proxy["username"]), str(proxy["password"])))
                if len(rotas) == limite:
                    return rotas
            if not dados.get("next"):
                break
    except (requests.RequestException, ValueError, TypeError, KeyError) as exc:
        _logger.warning(json.dumps({"event": "nfe55_webshare_list_error", "error": type(exc).__name__, "routes_so_far": len(rotas)}))
    return rotas


def rotas_configuradas(environ: dict[str, str] | None = None, buscar_webshare: Any = None) -> list[Rota]:
    """Webshare primeiro; sem ele, <prefixo>_URL, <prefixo>_URL_2, ..."""
    env = environ if environ is not None else os.environ
    nomes = nomes_proxy(env)
    tamanho = tamanho_lote()
    chave = _texto(env, nomes["webshare_key"])
    if chave:
        rotas = (buscar_webshare or rotas_webshare)(chave, _texto(env, nomes["webshare_plan"]), tamanho)
        if rotas:
            return rotas[:tamanho]
    rotas = []
    vistas: set[str] = set()
    for slot in range(1, tamanho + 1):
        sufixo = "" if slot == 1 else f"_{slot}"
        url = _texto(env, f"{nomes['url']}{sufixo}")
        if not url or url in vistas:
            continue
        vistas.add(url)
        usuario = env.get(f"{nomes['username']}{sufixo}") or env.get(nomes["username"], "")
        senha = env.get(f"{nomes['password']}{sufixo}") or env.get(nomes["password"], "")
        rotas.append(Rota(f"nfe55-{slot}", url, str(usuario), str(senha)))
        if len(rotas) == tamanho:
            break
    return rotas


def proxy_configurado(environ: dict[str, str] | None = None) -> bool:
    env = environ if environ is not None else os.environ
    nomes = nomes_proxy(env)
    return bool(_texto(env, nomes["webshare_key"]) or _texto(env, nomes["url"]))


class LimitadorSaida:
    """Relógio da NF-e de saída. Cada faixa (IP) tem o próprio intervalo; o cooldown do portal é único.

    Estados do download: available, cooldown, half_open. Depois do cooldown sai só uma sonda.
    """

    def __init__(self, intervalo: float = INTERVALO_MIN, cooldown: float | None = None, clock: Any = None, sleep: Any = None) -> None:
        self.download_seconds = max(0.0, float(intervalo))
        self.cooldown_seconds = float(cooldown) if cooldown is not None else cooldown_segundos()
        self._clock = clock or time.monotonic
        self._sleep = sleep or time.sleep
        self._lock = threading.Lock()
        self._cond = threading.Condition(self._lock)
        self._filas: dict[str, deque] = {}
        self._proximo: dict[str, float] = {}
        self._estado = "available"
        self._cooldown_ate = 0.0
        self._sonda: object | None = None

    def estado(self) -> str:
        with self._lock:
            self._rolar_locked(float(self._clock()))
            return self._estado

    def _rolar_locked(self, agora: float) -> None:
        if self._estado == "cooldown" and agora >= self._cooldown_ate:
            self._estado = "half_open"

    def _entrar_cooldown_locked(self, agora: float) -> None:
        self._estado = "cooldown"
        self._cooldown_ate = agora + self.cooldown_seconds
        self._sonda = None
        self._cond.notify_all()

    def note_remote_limit(self) -> None:
        with self._lock:
            self._entrar_cooldown_locked(float(self._clock()))

    def finish_download_probe(self, sonda: object | None, *, succeeded: bool) -> None:
        if sonda is None:
            return
        with self._lock:
            if sonda is not self._sonda:
                return
            if succeeded:
                self._estado = "available"
                self._sonda = None
                self._cond.notify_all()
            else:
                self._entrar_cooldown_locked(float(self._clock()))

    def begin_download(self, notify_wait: Any = None, lane: str = "download") -> tuple[str, object | None]:
        """("call", sonda) quando pode baixar; ("skip", None) se outra sonda half_open já saiu."""
        ticket = object()
        ultimo_aviso = float(self._clock()) - 30.0
        with self._cond:
            self._filas.setdefault(lane, deque()).append(ticket)
        try:
            while True:
                with self._cond:
                    agora = float(self._clock())
                    fila = self._filas.get(lane) or deque()
                    na_frente = bool(fila) and fila[0] is ticket
                    espera = 0.0
                    if na_frente:
                        self._rolar_locked(agora)
                        if self._estado == "cooldown":
                            espera = max(0.0, self._cooldown_ate - agora)
                        elif self._sonda is not None:
                            return "skip", None
                        else:
                            espera = max(0.0, self._proximo.get(lane, 0.0) - agora)
                            if espera == 0:
                                self._proximo[lane] = agora + self.download_seconds
                                if self._estado == "half_open":
                                    self._sonda = object()
                                return "call", self._sonda
                if notify_wait and agora - ultimo_aviso >= 30.0:
                    notify_wait()
                    ultimo_aviso = float(self._clock())
                if na_frente and espera > 0:
                    self._sleep(min(espera, 30.0) if notify_wait else espera)
                else:
                    with self._cond:
                        fila = self._filas.get(lane) or deque()
                        if not fila or fila[0] is not ticket:
                            self._cond.wait(timeout=30.0)
        finally:
            with self._cond:
                fila = self._filas.get(lane)
                if fila is not None and ticket in fila:
                    fila.remove(ticket)
                if fila is not None and not fila:
                    self._filas.pop(lane, None)
                self._cond.notify_all()


_transporte: GestorSaida | None = None
_transporte_guard = threading.Lock()
_limitador: LimitadorSaida | None = None
_limitador_guard = threading.Lock()


def transporte_compartilhado() -> GestorSaida:
    """Saída principal da NF-e de saída (consulta SOAP e download 1 a 1)."""
    global _transporte
    with _transporte_guard:
        if _transporte is None:
            rotas = rotas_configuradas()
            _transporte = GestorSaida(rotas, enabled=bool(rotas)) if rotas else GestorSaida([Rota("direct", None)])
        return _transporte


def limitador_compartilhado() -> LimitadorSaida:
    global _limitador
    with _limitador_guard:
        if _limitador is None:
            _limitador = LimitadorSaida(intervalo_download(INTERVALO_MIN))
        return _limitador


def reiniciar_estado() -> None:
    """Uso em testes."""
    global _transporte, _limitador
    with _transporte_guard:
        _transporte = None
    with _limitador_guard:
        _limitador = None
