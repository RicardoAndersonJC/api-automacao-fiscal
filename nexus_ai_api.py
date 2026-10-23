"""Install the Nexus AI foundation into the existing FastAPI application."""
from __future__ import annotations

import asyncio
import json
import logging
import os
import time
from datetime import date, datetime, timezone
from decimal import Decimal,InvalidOperation,ROUND_UP
from dataclasses import dataclass, field
from typing import Callable, Literal
from urllib.parse import urlparse
from uuid import UUID, uuid4

import httpx
from fastapi import APIRouter, FastAPI, Header, HTTPException, Query, Request, Response
from fastapi.exceptions import RequestValidationError
from fastapi.routing import APIRoute
from pydantic import BaseModel, ConfigDict, Field, model_validator

try:
    from .nexus_ai_core import (
        ADMIN_CATALOG, CLIENT_CATALOG, AuthContext, CoreError, Limits,
        Orchestrator, Tool, ToolRegistry, redact,
    )
except ImportError:  # Flat module layout in the existing Render API.
    from nexus_ai_core import (
        ADMIN_CATALOG, CLIENT_CATALOG, AuthContext, CoreError, Limits,
        Orchestrator, Tool, ToolRegistry, redact,
    )


@dataclass(frozen=True)
class Settings:
    enabled: bool = False
    supabase_url: str = ""
    publishable_key: str = field(default="", repr=False)
    service_key: str = field(default="", repr=False)
    model: str = ""
    provider_key: str = field(default="", repr=False)
    operations_enabled: bool = False
    read_tools_enabled: bool = False
    knowledge_enabled: bool = False
    local_first: bool = True
    admin_only: bool = True
    local_supabase: bool = False
    allowed_origins: tuple[str,...] = ()
    input_price_per_million: Decimal | None = None
    output_price_per_million: Decimal | None = None

    @classmethod
    def from_env(cls):
        return cls(
            enabled=os.getenv("NEXUS_AI_ENABLED", "false").lower() == "true",
            supabase_url=os.getenv("SUPABASE_URL", "").rstrip("/"),
            publishable_key=os.getenv("SUPABASE_ANON_KEY", ""),
            service_key=os.getenv("SUPABASE_SERVICE_ROLE_KEY", ""),
            model=os.getenv("NEXUS_AI_MODEL", ""),
            provider_key=os.getenv("OPENAI_API_KEY", ""),
            operations_enabled=os.getenv("NEXUS_AI_OPERATIONS_ENABLED", "false").lower() == "true",
            read_tools_enabled=os.getenv("NEXUS_AI_READ_TOOLS_ENABLED", "false").lower() == "true",
            knowledge_enabled=os.getenv("NEXUS_AI_KNOWLEDGE_ENABLED", "false").lower() == "true",
            local_first=os.getenv('NEXUS_AI_LOCAL_FIRST','true').lower()=='true',
            admin_only=os.getenv('NEXUS_AI_ADMIN_ONLY','true').strip().lower()!='false',
            allowed_origins=tuple(origin.strip().rstrip('/') for origin in os.getenv('NEXUS_AI_ALLOWED_ORIGINS','').split(',') if origin.strip()),
            input_price_per_million=price_from_env('NEXUS_AI_INPUT_PRICE_USD_PER_MILLION'),
            output_price_per_million=price_from_env('NEXUS_AI_OUTPUT_PRICE_USD_PER_MILLION'),
        )

    def require_enabled(self):
        parsed = urlparse(self.supabase_url)
        scheme_allowed = parsed.scheme == 'https' or (
            self.local_supabase and parsed.scheme == 'http' and parsed.hostname == '127.0.0.1')
        if (not self.enabled or not scheme_allowed or not parsed.hostname
                or parsed.username or parsed.password or parsed.query or parsed.fragment
                or parsed.path not in ("", "/")
                or not all((self.publishable_key, self.service_key))):
            raise HTTPException(503, "ai_unavailable")


def price_from_env(name):
    try:
        value=Decimal(os.getenv(name,''))
        return value if value.is_finite() and Decimal(0)<=value<=Decimal(10000) else None
    except InvalidOperation:return None


def estimate_cost(settings,input_tokens,output_tokens):
    if settings.input_price_per_million is None or settings.output_price_per_million is None:
        raise HTTPException(503,'pricing_unavailable')
    return ((Decimal(input_tokens or 0)*settings.input_price_per_million+
        Decimal(output_tokens or 0)*settings.output_price_per_million)/Decimal(1000000)).quantize(Decimal('0.000001'),rounding=ROUND_UP)


class Filters(BaseModel):
    model_config = ConfigDict(extra='forbid')
    date_from: date = Field(default_factory=lambda: datetime.now(timezone.utc).date().replace(day=1))
    date_to: date = Field(default_factory=lambda: datetime.now(timezone.utc).date())
    empresa_id: UUID | None = None
    period_basis: Literal['imported_at','emitted_at']='imported_at'

    @model_validator(mode='after')
    def bounded_period(self):
        if self.date_to < self.date_from or (self.date_to-self.date_from).days > 365:
            raise ValueError('invalid_period')
        return self


class ChatRequest(BaseModel):
    model_config = ConfigDict(extra="forbid", strict=True)
    audience: Literal["client", "admin"] = "client"
    agent: str = Field(min_length=1, max_length=40)
    message: str = Field(min_length=1, max_length=4000)
    conversation_id: UUID | None = Field(default=None, strict=False)
    filters: Filters = Field(default_factory=Filters)


class DisabledAction(BaseModel):
    model_config=ConfigDict(extra='forbid')
    audience: Literal['client','admin']='client'
    operation: Literal['request_job_retry','request_xml_download','reprocess_pending']
    target_id: UUID


class PrivateValidationRoute(APIRoute):
    def get_route_handler(self):
        handler = super().get_route_handler()
        async def validated(request):
            try:
                return await handler(request)
            except RequestValidationError:
                raise HTTPException(422, "invalid_request") from None
        return validated


class BodyLimit:
    """Bound chunked and length-delimited AI requests before JSON parsing."""
    def __init__(self, app, maximum=20000,allowed_origins=()):
        self.app, self.maximum, self.allowed_origins = app, maximum,allowed_origins

    async def __call__(self, scope, receive, send):
        path = scope.get("path", "")
        if scope["type"] != "http" or not (path == "/ai" or path.startswith("/ai/")):
            return await self.app(scope, receive, send)
        correlation_id = str(uuid4())
        scope.setdefault("state", {})["nexus_ai_correlation"] = correlation_id
        started = time.monotonic()
        original_send = send
        origin=dict(scope.get('headers',[])).get(b'origin',b'').decode('latin1')
        async def send(message):
            if message["type"] == "http.response.start":
                headers = [(key, value) for key, value in message.get("headers", [])
                           if key.lower() not in (b"x-correlation-id", b"cache-control")
                           and not key.lower().startswith(b'access-control-')]
                message = dict(message, headers=headers + [
                    (b"x-correlation-id", correlation_id.encode()), (b"cache-control", b"no-store")])
                if origin and origin in self.allowed_origins:
                    message['headers'] += [(b'access-control-allow-origin',origin.encode()),
                        (b'vary',b'Origin'),(b'access-control-expose-headers',b'X-Correlation-ID')]
                logging.getLogger("nexus.ai").info(json.dumps({
                    "event": "ai_request", "correlation_id": correlation_id,
                    "status": message["status"], "elapsed_ms": round((time.monotonic()-started)*1000),
                }))
            await original_send(message)
        if origin and origin not in self.allowed_origins:
            await send({'type':'http.response.start','status':403,'headers':[(b'content-type',b'application/json')]})
            await send({'type':'http.response.body','body':b'{"detail":"origin_denied"}'})
            return
        if scope['method']=='OPTIONS':
            await send({'type':'http.response.start','status':204,'headers':[
                (b'access-control-allow-methods',b'GET, POST, DELETE, OPTIONS'),
                (b'access-control-allow-headers',b'Authorization, Content-Type, X-Organization-ID')]})
            await send({'type':'http.response.body','body':b''});return
        body_buffer = bytearray()
        deadline, message_count = started + 10, 0
        while True:
            try:
                remaining = deadline - time.monotonic()
                message_count += 1
                if remaining <= 0 or message_count > 1024:
                    raise asyncio.TimeoutError
                message = await asyncio.wait_for(receive(), remaining)
            except asyncio.TimeoutError:
                await send({"type": "http.response.start", "status": 408, "headers": []})
                await send({"type": "http.response.body", "body": b""})
                return
            if message["type"] == "http.disconnect":
                return
            body = message.get("body", b"")
            if len(body_buffer) + len(body) > self.maximum:
                await send({"type": "http.response.start", "status": 413,
                            "headers": [(b"content-type", b"application/json")]})
                await send({"type": "http.response.body", "body": b'{"detail":"input_limit"}'})
                return
            body_buffer.extend(body)
            if not message.get("more_body", False):
                break
        delivered = False
        async def replay():
            nonlocal delivered
            if not delivered:
                delivered = True
                return {"type": "http.request", "body": bytes(body_buffer), "more_body": False}
            return await receive()
        await self.app(scope, replay, send)


class Session:
    def __init__(self, settings, client, token, org_id):
        self.settings, self.client, self.token = settings, client, token
        self.org_id, self.user_id = str(org_id), None

    async def request(self, method, path, *, server=False, payload=None, params=None):
        key = self.settings.service_key if server else self.settings.publishable_key
        bearer = key if server else self.token
        try:
            async with self.client.stream(
                method, self.settings.supabase_url + path,
                headers={"apikey": key, "Authorization": "Bearer " + bearer},
                json=payload, params=params, timeout=8, follow_redirects=False,
            ) as response:
                content = bytearray()
                async for chunk in response.aiter_bytes():
                    content.extend(chunk)
                    if len(content) > 256000:
                        raise HTTPException(503, "data_limit")
                if response.status_code >= 300:
                    if response.status_code == 401:
                        raise HTTPException(401, "invalid_session")
                    if response.status_code == 403:
                        raise HTTPException(403, "forbidden")
                    if response.status_code == 429:
                        raise HTTPException(429, "usage_limit")
                    try:
                        code = json.loads(content).get("code")
                    except (ValueError, AttributeError):
                        code = None
                    mapped = {"54000": (429, "usage_limit"), "42501": (403, "forbidden"),
                              "P0002": (404, "conversation_not_found")}.get(code)
                    if mapped:
                        raise HTTPException(*mapped)
                    raise HTTPException(503, "data_unavailable")
                return json.loads(content) if content else None
        except httpx.TimeoutException:
            raise HTTPException(504, "data_timeout") from None
        except (httpx.HTTPError, ValueError):
            raise HTTPException(503, "data_unavailable") from None

    async def rpc(self, name, payload, *, server=False):
        return await self.request("POST", "/rest/v1/rpc/" + name, payload=payload, server=server)

    async def authenticate(self, audience):
        user = await self.request("GET", "/auth/v1/user")
        try:
            self.user_id = str(UUID(user["id"]))
        except (ValueError, TypeError, KeyError):
            raise HTTPException(401, "invalid_session") from None
        return await self.context(audience)

    async def context(self, audience):
        value = await self.rpc("nexus_ai_context", {"p_org_id": self.org_id, "p_audience": audience})
        if (type(value) is not dict or value.get("user_id") != self.user_id
                or value.get("org_id") != self.org_id
                or type(value.get("internal_admin")) is not bool
                or type(value.get("permissions")) is not list
                or any(type(p) is not str for p in value["permissions"])):
            raise HTTPException(403, "invalid_scope")
        context = AuthContext(self.user_id, self.org_id, frozenset(value["permissions"]),
                              value["internal_admin"])
        if ("ai:" + audience not in context.permissions
                or ((audience == "admin" or self.settings.admin_only) and not context.internal_admin)):
            raise HTTPException(403, "forbidden")
        return context

    async def history(self, conversation_id, audience):
        conversations = await self.request("GET", "/rest/v1/ai_conversations", params={
            "select": "id,audience,capability", "id": "eq." + str(conversation_id),
            "org_id": "eq." + self.org_id, "user_id": "eq." + self.user_id,
            "audience": "eq." + audience, "limit": "1",
        })
        if not conversations:
            raise HTTPException(404, "conversation_not_found")
        self.conversation_capability=conversations[0].get('capability')
        return await self.request("GET", "/rest/v1/ai_messages", params={
            "select": "id,role,content,created_at,references:references_data", "conversation_id": "eq." + str(conversation_id),
            "order": "created_at.desc,id.desc", "limit": "20",
        })


class SessionAudit:
    def __init__(self, session, audience, execution_id):
        self.session, self.audience, self.execution_id = session, audience, execution_id

    async def record(self, event):
        await self.session.rpc("nexus_ai_audit", {
            "p_org_id": event.org_id, "p_user_id": event.user_id,
            "p_operation": "provider" if event.operation == "orchestrator" else "tool",
            "p_outcome": "succeeded" if event.outcome == "ok" else "failed",
            "p_audience": self.audience,
            "p_execution_id": self.execution_id,
        }, server=True)


def default_provider(settings):
    try:
        from .nexus_ai_provider import OpenAIAgentsProvider
    except ImportError:
        from nexus_ai_provider import OpenAIAgentsProvider
    return OpenAIAgentsProvider(model=settings.model, api_key=settings.provider_key)


async def finalize(coroutine):
    # Two sequential persistence RPCs each have an eight-second request deadline.
    task = asyncio.create_task(asyncio.wait_for(coroutine, 20))
    cancellation = None
    try:
        while not task.done():
            try:
                await asyncio.shield(task)
            except asyncio.CancelledError as exc:
                cancellation = exc
        task.result()
    except asyncio.TimeoutError:
        raise HTTPException(503, "persistence_timeout") from None
    if cancellation:
        raise cancellation


def install_nexus_ai_routes(app: FastAPI, *, settings: Settings | None = None,
                            provider_factory: Callable = default_provider,
                            transport=None) -> None:
    settings = settings or Settings.from_env()
    router = APIRouter(prefix="/ai", tags=["Nexus AI"], route_class=PrivateValidationRoute)
    app.add_middleware(BodyLimit,allowed_origins=settings.allowed_origins)

    def credentials(authorization):
        settings.require_enabled()
        if not authorization or not authorization.startswith("Bearer "):
            raise HTTPException(401, "authentication_required")
        token = authorization[7:]
        if not token or len(token) > 8192 or token == settings.service_key:
            raise HTTPException(401, "invalid_session")
        return token

    @router.get("/agents")
    async def agents(audience: Literal["client", "admin"] = "client",
                     authorization: str | None = Header(default=None),
                     x_organization_id: UUID = Header()):
        token = credentials(authorization)
        async with httpx.AsyncClient(transport=transport, trust_env=False) as client:
            session = Session(settings, client, token, x_organization_id)
            context = await session.authenticate(audience)
            active = ['operational'] if (settings.operations_enabled and audience == 'admin'
                                         and 'read_operations' in context.permissions) else []
            if settings.read_tools_enabled:
                catalog = ADMIN_CATALOG if audience == 'admin' else CLIENT_CATALOG
                active = [name for name, agent in catalog.items() if agent.tools <= context.permissions]
            return {"agents": active, "status": "ready" if active else "foundation_only", "writes_enabled": False,
                    'admin_only':settings.admin_only}

    @router.get("/conversations")
    async def conversations(audience: Literal["client", "admin"] = "client",
                            limit: int = Query(default=20, ge=1, le=50),
                            offset: int = Query(default=0, ge=0, le=10000),
                            authorization: str | None = Header(default=None),
                            x_organization_id: UUID = Header()):
        token = credentials(authorization)
        async with httpx.AsyncClient(transport=transport, trust_env=False) as client:
            session = Session(settings, client, token, x_organization_id)
            await session.authenticate(audience)
            return await session.request("GET", "/rest/v1/ai_conversations", params={
                "select": "id,audience,created_at,capability", "user_id": "eq." + session.user_id,
                "org_id": "eq." + session.org_id, "audience": "eq." + audience,
                "order": "created_at.desc,id.desc", "limit": str(limit), "offset": str(offset),
            })

    @router.get('/companies')
    async def companies(audience: Literal['client','admin']='client',authorization: str | None=Header(default=None),
                        x_organization_id: UUID=Header()):
        token=credentials(authorization)
        async with httpx.AsyncClient(transport=transport,trust_env=False) as client:
            session=Session(settings,client,token,x_organization_id)
            await session.authenticate(audience)
            return await session.rpc('nexus_ai_companies',{'p_user_id':session.user_id,'p_org_id':session.org_id,
                'p_audience':audience},server=True)

    @router.get("/conversations/{conversation_id}")
    async def conversation(conversation_id: UUID, audience: Literal["client", "admin"] = "client",
                           authorization: str | None = Header(default=None),
                           x_organization_id: UUID = Header()):
        token = credentials(authorization)
        async with httpx.AsyncClient(transport=transport, trust_env=False) as client:
            session = Session(settings, client, token, x_organization_id)
            await session.authenticate(audience)
            messages=await session.history(conversation_id,audience)
            return {"id": str(conversation_id), "messages": messages,'capability':session.conversation_capability}

    @router.get('/metrics')
    async def metrics(authorization: str | None=Header(default=None),x_organization_id: UUID=Header()):
        token=credentials(authorization)
        async with httpx.AsyncClient(transport=transport,trust_env=False) as client:
            session=Session(settings,client,token,x_organization_id)
            context=await session.authenticate('admin')
            if not context.permissions.intersection({'read_performance','read_operations'}):
                raise HTTPException(403,'forbidden')
            return await session.rpc('nexus_ai_metrics',{'p_user_id':session.user_id,'p_org_id':session.org_id},server=True)

    @router.get("/usage")
    async def usage(audience: Literal["client", "admin"] = "client",
                    limit: int = Query(default=20, ge=1, le=50),
                    offset: int = Query(default=0, ge=0, le=10000),
                    authorization: str | None = Header(default=None),
                    x_organization_id: UUID = Header()):
        token = credentials(authorization)
        async with httpx.AsyncClient(transport=transport, trust_env=False) as client:
            session = Session(settings, client, token, x_organization_id)
            await session.authenticate(audience)
            entries = await session.request("GET", "/rest/v1/ai_usage", params={
                "select": "execution_id,reserved_tokens,charged_tokens,input_tokens,output_tokens,created_at,finished_at,reserved_cost_usd,estimated_cost_usd",
                "user_id": "eq." + session.user_id, "org_id": "eq." + session.org_id,
                "audience": "eq." + audience, "order": "created_at.desc,execution_id.desc",
                "limit": str(limit), "offset": str(offset),
            })
            for entry in entries:
                for field in ('reserved_cost_usd','estimated_cost_usd'):
                    if field in entry:entry[field]=format(Decimal(str(entry[field])),'.6f')
                if entry.get('finished_at') is None and entry.get('input_tokens')==0 and entry.get('output_tokens')==0:
                    entry['input_tokens']=entry['output_tokens']=None
            return {"entries": entries, "estimated_cost": None}

    @router.delete('/conversations/{conversation_id}',status_code=204)
    async def archive(conversation_id: UUID, audience: Literal['client','admin']='client',
                      authorization: str | None=Header(default=None),x_organization_id: UUID=Header()):
        token=credentials(authorization)
        async with httpx.AsyncClient(transport=transport,trust_env=False) as client:
            session=Session(settings,client,token,x_organization_id)
            await session.authenticate(audience)
            await session.rpc('nexus_ai_archive_conversation',{'p_user_id':session.user_id,'p_org_id':session.org_id,
                'p_audience':audience,'p_conversation_id':str(conversation_id)},server=True)
            return Response(status_code=204)

    @router.post("/chat")
    async def chat(payload: ChatRequest, request: Request, response: Response,
                   authorization: str | None = Header(default=None),
                   x_organization_id: UUID = Header()):
        token = credentials(authorization)
        correlation_id = request.state.nexus_ai_correlation
        response.headers["X-Correlation-ID"] = correlation_id
        response.headers["Cache-Control"] = "no-store"
        catalog = ADMIN_CATALOG if payload.audience == "admin" else CLIENT_CATALOG
        if payload.agent not in catalog:
            raise HTTPException(422, "unknown_agent")
        async with httpx.AsyncClient(transport=transport, trust_env=False) as client:
            session = Session(settings, client, token, x_organization_id)
            context = await session.authenticate(payload.audience)
            history = await session.history(payload.conversation_id, payload.audience) if payload.conversation_id else []
            prompt = json.dumps(redact({"history": list(reversed(history)), "message": payload.message}), ensure_ascii=True)
            if len(prompt.encode()) > 24000:
                raise HTTPException(413, "history_limit")
            priced=settings.read_tools_enabled or settings.operations_enabled
            local_gate=None
            if priced and settings.local_first:
                try:
                    from .nexus_ai_local_first import LocalFirstProvider
                except ImportError:
                    from nexus_ai_local_first import LocalFirstProvider
                async def before_fallback():
                    if settings.local_supabase and not settings.provider_key:
                        raise CoreError('local_model_disabled')
                    # Pilot access is rechecked immediately before reserving a paid call.
                    if settings.admin_only:
                        try:
                            await session.context(payload.audience)
                        except HTTPException:
                            raise CoreError('forbidden') from None
                    if settings.input_price_per_million is None or settings.output_price_per_million is None:
                        raise CoreError('pricing_unavailable')
                    amount=(Decimal(32768)*max(settings.input_price_per_million,settings.output_price_per_million)
                        /Decimal(1000000)).quantize(Decimal('0.000001'),rounding=ROUND_UP)
                    try:
                        await session.rpc('nexus_ai_reserve_fallback',{'p_user_id':session.user_id,
                            'p_execution_id':execution_id,'p_reserved_cost_usd':str(amount),
                            'p_company_scope':(getattr(provider,'evidence',None) or {}).get('company_scope',[])},server=True)
                    except HTTPException as exc:
                        raise CoreError('usage_limit' if exc.status_code==429 else 'forbidden' if exc.status_code==403 else 'fallback_unavailable') from None
                local_gate=LocalFirstProvider(lambda:provider_factory(settings),before_fallback)
                provider=local_gate
            else:
                try:
                    provider = provider_factory(settings)
                except Exception:
                    raise HTTPException(503, "provider_unavailable") from None
            reserved_cost=Decimal(0)
            if priced and local_gate is None:
                if settings.input_price_per_million is None or settings.output_price_per_million is None:
                    raise HTTPException(503,'pricing_unavailable')
                reserved_cost=(Decimal(32768)*max(settings.input_price_per_million,settings.output_price_per_million)
                    /Decimal(1000000)).quantize(Decimal('0.000001'),rounding=ROUND_UP)
            reservation = await session.rpc("nexus_ai_begin", {
                "p_org_id": session.org_id, "p_user_id": session.user_id,
                "p_audience": payload.audience,
                "p_conversation_id": str(payload.conversation_id) if payload.conversation_id else None,
                "p_reserved_tokens": 1 if local_gate else 32768,
                "p_correlation_id": correlation_id,
                "p_capability": next(iter(catalog[payload.agent].tools)) if priced else None,
                "p_reserved_cost_usd":str(reserved_cost),
            }, server=True)
            try:
                execution_id = str(UUID(reservation["execution_id"]))
                conversation_id = str(UUID(reservation["conversation_id"]))
            except (TypeError, KeyError, ValueError):
                raise HTTPException(503, "invalid_reservation") from None

            async def authorizer(candidate, permission):
                try:
                    fresh = await session.context(payload.audience)
                except HTTPException as exc:
                    if exc.status_code in (401, 403):
                        return False
                    raise
                return fresh == candidate and permission in fresh.permissions

            registry = ToolRegistry([], authorizer=authorizer,
                                    audit=SessionAudit(session, payload.audience, execution_id),
                                    limits=Limits(max_input_bytes=24000, total_timeout=30, audit_timeout=9))
            if settings.read_tools_enabled or (settings.operations_enabled and payload.audience=='admin'
                    and payload.agent=='operational'):
                try:
                    from .nexus_ai_tools import SnapshotProvider
                except ImportError:
                    from nexus_ai_tools import SnapshotProvider
                provider = SnapshotProvider(provider, session, context, registry, catalog[payload.agent], payload.filters,
                    knowledge_enabled=settings.knowledge_enabled, question=payload.message)
                capability = next(iter(catalog[payload.agent].tools))
                registry = ToolRegistry([Tool(capability, capability, provider.read_snapshot)],
                    authorizer=authorizer, audit=SessionAudit(session, payload.audience, execution_id),
                    limits=registry.limits)
                provider.registry = registry
            succeeded, answer = False, ""
            owner=asyncio.current_task()
            async def monitor_disconnect():
                while True:
                    if await request.is_disconnected():
                        owner.cancel();return
                    await asyncio.sleep(0.2)
            monitor=asyncio.create_task(monitor_disconnect())
            try:
                answer = await Orchestrator(provider, registry).run(context, payload.audience, payload.agent, prompt)
                if not await authorizer(context, "ai:" + payload.audience):
                    raise HTTPException(403, "forbidden")
                succeeded = True
            except CoreError as exc:
                status = 429 if str(exc)=='usage_limit' else 403 if str(exc) == "forbidden" else (
                    504 if str(exc) in ("total_timeout", "tool_timeout") else 503)
                raise HTTPException(status, str(exc)) from None
            finally:
                monitor.cancel()
                # Unknown usage on failure retains the entire database reservation.
                async def persist():
                    await asyncio.gather(monitor,return_exceptions=True)
                    await session.rpc('nexus_ai_record_usage',{
                        'p_user_id':session.user_id,'p_execution_id':execution_id,
                        'p_input_tokens':getattr(provider,'input_tokens',None) or 0,
                        'p_output_tokens':getattr(provider,'output_tokens',None) or 0,
                        'p_estimated_cost_usd':str(estimate_cost(settings,getattr(provider,'input_tokens',None),
                            getattr(provider,'output_tokens',None))) if priced and (local_gate is None or local_gate.used_model) else '0'},server=True)
                    await session.rpc("nexus_ai_finish", {
                        "p_execution_id": execution_id, "p_user_id": session.user_id,
                        "p_user_message": redact(payload.message) if succeeded else "",
                        "p_assistant_message": answer if succeeded else "",
                        "p_input_tokens": getattr(provider, "input_tokens", None) or 0,
                        "p_output_tokens": getattr(provider, "output_tokens", None) or 0,
                        "p_succeeded": succeeded,
                        "p_company_scope": (getattr(provider, 'evidence', None) or {}).get('company_scope') if succeeded else None,
                        "p_references": getattr(provider,'references',[]) if succeeded else [],
                        "p_estimated_cost_usd":str(estimate_cost(settings,getattr(provider,'input_tokens',None),
                            getattr(provider,'output_tokens',None))) if priced and (local_gate is None or local_gate.used_model) else '0',
                    }, server=True)
                await finalize(persist())
            return {"conversation_id": conversation_id, "message": answer,
                    'resolution':'local' if local_gate and not local_gate.used_model else 'model',
                    "references": getattr(provider, 'references', []), "correlation_id": correlation_id,
                    "evidence": {k:v for k,v in (getattr(provider,'evidence',None) or {}).items()
                        if k not in ('org_id','company_scope')} if settings.read_tools_enabled else None,
                    "usage": {"input_tokens": provider.input_tokens,
                              "output_tokens": provider.output_tokens}, "writes_enabled": False}

    @router.post('/actions/preview')
    @router.post('/actions/confirm')
    async def disabled_action(payload: DisabledAction, authorization: str | None=Header(default=None),
                              x_organization_id: UUID=Header()):
        token=credentials(authorization)
        async with httpx.AsyncClient(transport=transport,trust_env=False) as client:
            session=Session(settings,client,token,x_organization_id)
            await session.authenticate(payload.audience)
            raise HTTPException(409,'writes_disabled')

    app.include_router(router)
