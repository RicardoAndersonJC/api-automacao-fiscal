"""Local read-only foundation. Trusted auth, data and audit adapters are required.

No JWT verification, persistence, SDK or network implementation is provided here.
Handlers must enforce organization scope in their data source and be cooperative
async functions; Python callbacks are trusted code, not a security sandbox.
"""

import asyncio
import inspect
import json
import math
import re
from dataclasses import dataclass
from types import MappingProxyType
from typing import Awaitable, Callable, Mapping, Protocol


class CoreError(Exception):
    """Public errors contain codes only, never adapter exceptions or payloads."""


@dataclass(frozen=True)
class AuthContext:
    """Construct only from a verified server identity, never from model input."""

    user_id: str
    org_id: str
    permissions: frozenset[str]
    internal_admin: bool

    def __post_init__(self):
        if not all(type(v) is str and v.strip() for v in (self.user_id, self.org_id)):
            raise ValueError("invalid_identity")
        if type(self.internal_admin) is not bool:
            raise ValueError("invalid_admin_flag")
        permissions = frozenset(self.permissions)
        if any(type(v) is not str or not v for v in permissions):
            raise ValueError("invalid_permissions")
        object.__setattr__(self, "permissions", permissions)


@dataclass(frozen=True)
class Agent:
    name: str
    audience: str
    tools: frozenset[str]


ADMIN_CATALOG = MappingProxyType({name: Agent(name, "admin", frozenset({tool}))
    for name, tool in (
        ("operational", "read_operations"),
        ("fiscal_diagnostic", "read_diagnostics"),
        ("worker_monitor", "read_workers"),
        ("security_audit", "read_security"),
        ("performance", "read_performance"))})
CLIENT_CATALOG = MappingProxyType({name: Agent(name, "client", frozenset({tool}))
    for name, tool in (
        ("fiscal", "read_fiscal"), ("nfe", "read_nfe"),
        ("nfce", "read_nfce"), ("nfse", "read_nfse"),
        ("reports", "read_reports"), ("financial_analysis", "read_financial"))})
TOOL_NAMES = frozenset(tool for catalog in (ADMIN_CATALOG, CLIENT_CATALOG)
                       for agent in catalog.values() for tool in agent.tools)


@dataclass(frozen=True)
class Limits:
    max_calls: int = 8
    max_page_size: int = 100
    max_offset: int = 10000
    max_output_bytes: int = 32000
    max_input_bytes: int = 16000
    tool_timeout: float = 5.0
    total_timeout: float = 30.0
    audit_timeout: float = 2.0

    def __post_init__(self):
        for name in ("max_calls", "max_page_size", "max_offset",
                     "max_output_bytes", "max_input_bytes"):
            if type(getattr(self, name)) is not int or getattr(self, name) <= 0:
                raise ValueError("invalid_limit")
        for name in ("tool_timeout", "total_timeout", "audit_timeout"):
            value = getattr(self, name)
            if type(value) not in (int, float) or not math.isfinite(value) or value <= 0:
                raise ValueError("invalid_timeout")


@dataclass(frozen=True)
class ToolSchema:
    """Closed schema: identity, SQL, shell and arbitrary filters are impossible."""

    def validate(self, args: Mapping, limits: Limits) -> Mapping:
        if type(args) is not dict or set(args) != {"org_id", "limit", "offset"}:
            raise CoreError("invalid_arguments")
        if type(args["org_id"]) is not str or not args["org_id"]:
            raise CoreError("invalid_arguments")
        for key, low, high in (("limit", 1, limits.max_page_size),
                               ("offset", 0, limits.max_offset)):
            if type(args[key]) is not int or not low <= args[key] <= high:
                raise CoreError("invalid_pagination")
        return MappingProxyType(dict(args))


Authorizer = Callable[[AuthContext, str], Awaitable[bool]]
Handler = Callable[[AuthContext, Mapping], Awaitable[object]]


@dataclass(frozen=True)
class Tool:
    name: str
    permission: str
    handler: Handler
    read_only: bool = True
    schema: ToolSchema = ToolSchema()
    description: str = 'Read an authorized organization snapshot; no fiscal mutations.'
    risk: str = 'read_only'
    confirmation_policy: str = 'not_required_for_read_only'


@dataclass(frozen=True)
class AuditEvent:
    user_id: str
    org_id: str
    operation: str
    outcome: str


class AuditSink(Protocol):
    async def record(self, event: AuditEvent) -> None: ...


_SECRET_KEY = re.compile(r"secret|token|password|passwd|authorization|api.?key|"
                         r"certificate|private.?key|certificado|senha|credential", re.I)
_SECRET_TEXT = re.compile(
    r"-----BEGIN [^-]+-----[\s\S]*?-----END [^-]+-----|"
    r"\b(?:Bearer|Basic)\s+\S+|\beyJ[\w-]+\.[\w-]+\.[\w-]+|"
    r"\b(?:sk|sb_secret|sb_publishable)[-_][\w-]+|"
    r"\b(?:token|secret|password|senha|api[_-]?key)[\"']?\s*[:=]\s*"
    r"(?:\"(?:\\.|[^\"\\])*\"|'(?:\\.|[^'\\])*'|\S+)|"
    r"https?://\S+", re.I)


def redact(value, depth=0):
    if depth > 20:
        raise CoreError("invalid_output")
    if type(value) is dict:
        if any(type(key) is not str for key in value):
            raise CoreError("invalid_output")
        return {_SECRET_TEXT.sub("[REDACTED]", key):
                "[REDACTED]" if _SECRET_KEY.search(key) else redact(item, depth + 1)
                for key, item in value.items()}
    if type(value) in (list, tuple):
        return [redact(item, depth + 1) for item in value]
    if type(value) is str:
        return _SECRET_TEXT.sub("[REDACTED]", value)
    if value is None or type(value) in (bool, int):
        return value
    if type(value) is float and math.isfinite(value):
        return value
    raise CoreError("invalid_output")


def bounded(value, maximum):
    clean = redact(value)
    if len(json.dumps(clean, ensure_ascii=True, allow_nan=False).encode()) > maximum:
        raise CoreError("output_limit")
    return clean


async def audited(sink, context, operation, timeout, work):
    outcome = "failed"
    try:
        result = await work()
        outcome = "ok"
        return result
    finally:
        # No arguments, results, prompts or exception messages enter audit logs.
        task = asyncio.create_task(asyncio.wait_for(sink.record(AuditEvent(
            context.user_id, context.org_id, operation, outcome)), timeout))
        cancellation = None
        try:
            # Finish the bounded audit even when the caller cancels repeatedly.
            while not task.done():
                try:
                    await asyncio.shield(task)
                except asyncio.CancelledError as exc:
                    cancellation = exc
            task.result()
        except Exception:
            raise CoreError("audit_unavailable") from None
        if cancellation is not None:
            raise cancellation


async def authorize(context, permission, authorizer):
    if permission not in context.permissions:
        raise CoreError("forbidden")
    if await authorizer(context, permission) is not True:
        raise CoreError("forbidden")


class ToolRegistry:
    def __init__(self, tools, *, authorizer: Authorizer, audit: AuditSink,
                 limits: Limits = Limits()):
        entries = {}
        for tool in tools:
            if (tool.name not in TOOL_NAMES or tool.name in entries
                    or tool.read_only is not True or tool.permission != tool.name
                    or type(tool.schema) is not ToolSchema
                    or not inspect.iscoroutinefunction(tool.handler)):
                raise ValueError("invalid_tool")
            entries[tool.name] = tool
        self._tools = MappingProxyType(entries)
        self.authorizer, self.audit, self.limits = authorizer, audit, limits

    async def execute(self, context, agent, name, arguments):
        async def work():
            async def invoke():
                catalog = ADMIN_CATALOG if agent.audience == "admin" else CLIENT_CATALOG
                if catalog.get(agent.name) != agent:
                    raise CoreError("unknown_agent")
                if agent.audience == "admin" and not context.internal_admin:
                    raise CoreError("forbidden")
                if name not in self._tools or name not in agent.tools:
                    raise CoreError("unknown_tool")
                tool = self._tools[name]
                args = tool.schema.validate(arguments, self.limits)
                if args["org_id"] != context.org_id:
                    raise CoreError("org_mismatch")
                await authorize(context, tool.permission, self.authorizer)
                result = await tool.handler(context, args)
                if type(result) in (list, tuple) and len(result) > args["limit"]:
                    raise CoreError("pagination_output_limit")
                return bounded(result, self.limits.max_output_bytes)
            try:
                return await asyncio.wait_for(invoke(), self.limits.tool_timeout)
            except asyncio.TimeoutError:
                raise CoreError("tool_timeout") from None
            except CoreError:
                raise
            except Exception:
                raise CoreError("tool_failed") from None
        operation = name if type(name) is str and name in TOOL_NAMES else "unknown_tool"
        return await audited(self.audit, context, operation,
                             self.limits.audit_timeout, work)


@dataclass(frozen=True)
class ToolCall:
    name: str
    arguments: dict


@dataclass(frozen=True)
class ProviderReply:
    text: str = ""
    calls: tuple[ToolCall, ...] = ()


class Provider(Protocol):
    async def respond(self, *, agent: Agent, prompt: str,
                      observations: tuple[str, ...]) -> ProviderReply: ...


class Orchestrator:
    def __init__(self, provider: Provider, registry: ToolRegistry):
        self.provider, self.registry = provider, registry

    async def run(self, context: AuthContext, audience: str, agent_name: str,
                  prompt: str) -> str:
        limits = self.registry.limits

        async def work():
            async def dialogue():
                catalog = {"admin": ADMIN_CATALOG, "client": CLIENT_CATALOG}.get(audience)
                if catalog is None or agent_name not in catalog:
                    raise CoreError("unknown_agent")
                agent = catalog[agent_name]
                if audience == "admin" and not context.internal_admin:
                    raise CoreError("forbidden")
                await authorize(context, "ai:" + audience, self.registry.authorizer)
                if type(prompt) is not str or len(prompt.encode()) > limits.max_input_bytes:
                    raise CoreError("input_limit")
                observations, count = (), 0
                while True:
                    try:
                        reply = await self.provider.respond(
                            agent=agent, prompt=redact(prompt), observations=observations)
                    except CoreError:
                        raise
                    except Exception:
                        raise CoreError("provider_failed") from None
                    if (type(reply) is not ProviderReply or type(reply.text) is not str
                            or type(reply.calls) is not tuple):
                        raise CoreError("invalid_provider_reply")
                    if not reply.calls:
                        return bounded(reply.text, limits.max_output_bytes)
                    if count + len(reply.calls) > limits.max_calls:
                        raise CoreError("call_limit")
                    for call in reply.calls:
                        if type(call) is not ToolCall or type(call.name) is not str:
                            raise CoreError("invalid_provider_reply")
                        count += 1
                        result = await self.registry.execute(context, agent, call.name,
                                                             call.arguments)
                        observations += (json.dumps(result, ensure_ascii=True),)
                        bounded(observations, limits.max_output_bytes)
            try:
                return await asyncio.wait_for(dialogue(), limits.total_timeout)
            except asyncio.TimeoutError:
                raise CoreError("total_timeout") from None
            except CoreError:
                raise
            except Exception:
                raise CoreError("execution_failed") from None
        return await audited(self.registry.audit, context, "orchestrator",
                             limits.audit_timeout, work)
