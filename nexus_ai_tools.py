"""Authorized operational evidence; no fiscal mutations or arbitrary queries."""
import json
from uuid import UUID

try:
    from .nexus_ai_core import CoreError,bounded
except ImportError:
    from nexus_ai_core import CoreError,bounded


class EvidenceProvider:
    """Per-request evidence and provider usage; authorization lives in SQL tools."""
    def __init__(self, provider, session, context, registry, agent):
        self.provider, self.session, self.context = provider, session, context
        self.registry, self.agent = registry, agent
        self.evidence = None
        self.references = []

    @property
    def input_tokens(self):
        return self.provider.input_tokens

    @property
    def output_tokens(self):
        return self.provider.output_tokens



class SnapshotProvider(EvidenceProvider):
    def __init__(self, provider, session, context, registry, agent, filters, *, knowledge_enabled=False, question=''):
        super().__init__(provider, session, context, registry, agent)
        self.filters = filters
        self.capability = next(iter(agent.tools))
        self.knowledge_enabled,self.question=knowledge_enabled,question
        self.knowledge=[]

    async def read_snapshot(self, context, arguments):
        value = await self.session.rpc('nexus_ai_snapshot', {
            'p_user_id': context.user_id, 'p_org_id': context.org_id,
            'p_audience': self.agent.audience, 'p_capability': self.capability,
            'p_date_from': self.filters.date_from.isoformat(),
            'p_date_to': self.filters.date_to.isoformat(),
            'p_empresa_id': str(self.filters.empresa_id) if self.filters.empresa_id else None,
            'p_limit': arguments['limit'], 'p_offset': arguments['offset'],
            'p_period_basis':self.filters.period_basis,
        }, server=True)
        source = ('fiscal_documents' if self.agent.audience == 'client' else
                  'ai_tool_executions' if self.capability == 'read_security' else 'execucoes')
        allowed = {'source','scope','org_id','period_basis','date_from','date_to','total_count',
                   'total_value','missing_values','by_module','by_status','rows','company_scope','pending_count','pending_rows','by_month','by_supplier','undated_documents','pending_period_basis','missing_supplier_documents'}
        if (type(value) is not dict or set(value)-allowed or value.get('source') != source
                or value.get('org_id') != context.org_id
                or value.get('date_from') != self.filters.date_from.isoformat()
                or value.get('date_to') != self.filters.date_to.isoformat()
                or type(value.get('total_count')) is not int or value['total_count'] < 0
                or type(value.get('rows')) is not list or len(value['rows']) > arguments['limit']):
            raise CoreError('invalid_evidence')
        pending=value.get('pending_rows',[])
        if type(pending) is not list or len(pending)>arguments['limit']:
            raise CoreError('invalid_evidence')
        for row in value['rows']+pending:
            try:
                UUID(row['id'])
                if source == 'fiscal_documents':
                    UUID(row['empresa_id'])
                if self.filters.empresa_id and str(row.get('empresa_id')) != str(self.filters.empresa_id):
                    raise ValueError
            except (KeyError, ValueError, TypeError, AttributeError):
                raise CoreError('invalid_evidence') from None
        return value

    async def respond(self, *, agent, prompt, observations):
        if self.evidence is None:
            self.evidence = await self.registry.execute(self.context, self.agent, self.capability,
                {'org_id': self.context.org_id, 'limit': 25, 'offset': 0})
            self.references = [{'source': self.evidence['source'], 'id': row['id']}
                               for row in self.evidence['rows']]
            self.references += [{'source':'nfce_download_pending','id':row['id']}
                                for row in self.evidence.get('pending_rows',[])]
            if self.knowledge_enabled:
                self.knowledge=await self.session.rpc('nexus_ai_search_knowledge',{
                    'p_user_id':self.context.user_id,'p_org_id':self.context.org_id,
                    'p_audience':self.agent.audience,'p_query':self.question[:500],
                    'p_empresa_id':str(self.filters.empresa_id) if self.filters.empresa_id else None},server=True)
                if type(self.knowledge) is not list or len(self.knowledge)>3:
                    raise CoreError('invalid_knowledge')
                self.knowledge=bounded(self.knowledge,16000)
                for chunk in self.knowledge:
                    try:
                        UUID(chunk['id'])
                        UUID(chunk['document_id'])
                        if set(chunk)!={'id','document_id','title','visibility','org_id','empresa_id','content'}:
                            raise ValueError
                        if type(chunk['content']) is not str or len(chunk['content'].encode())>4000:
                            raise ValueError
                        if chunk['visibility']!='organization' and chunk['org_id'] is not None:
                            raise ValueError
                        if (chunk['visibility']=='internal' and self.agent.audience!='admin'
                            or chunk['visibility']=='organization' and chunk['org_id']!=self.context.org_id
                            or chunk['visibility'] not in ('general','internal','organization')):
                            raise ValueError
                    except (KeyError,TypeError,ValueError):
                        raise CoreError('invalid_knowledge') from None
                    self.references.append({'source':'ai_knowledge_chunks','id':chunk['id']})
                    if chunk.get('empresa_id'):
                        self.evidence.setdefault('company_scope',[]).append(chunk['empresa_id'])
                from_audit=self.registry.audit
                try:
                    from .nexus_ai_core import AuditEvent
                except ImportError:
                    from nexus_ai_core import AuditEvent
                await from_audit.record(AuditEvent(self.context.user_id,self.context.org_id,'read_knowledge','ok'))
        return await self.provider.respond(agent=agent, prompt=prompt,
            observations=(json.dumps({k:v for k,v in self.evidence.items() if k not in ('org_id','company_scope')}, ensure_ascii=True),
                json.dumps([{k:v for k,v in chunk.items() if k not in ('org_id','empresa_id')} for chunk in self.knowledge],ensure_ascii=True)) + observations)
