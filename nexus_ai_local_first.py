"""Conservative full-match intents; never let an LLM decide whether to spend."""
import json
import re
import unicodedata

try:
    from .nexus_ai_core import ProviderReply
except ImportError:
    from nexus_ai_core import ProviderReply


def normalize(text):
    return re.sub(r'\s+',' ',''.join(c for c in unicodedata.normalize('NFD',text.lower())
        if not unicodedata.combining(c))).strip(' .?!')


def local_answer(question,evidence,knowledge,agent_name=None):
    question=normalize(question)
    question={
        'preciso de um relatorio':'relatorio', 'quero um relatorio':'relatorio',
        'pode gerar um relatorio':'relatorio', 'quais as pendencias':'pendencias',
        'quais sao as pendencias':'pendencias', 'qual o valor total':'valor total',
        'qual e o valor total':'valor total',
    }.get(question,question)
    if question in ('oi','ola','bom dia','boa tarde','boa noite'):
        return 'Ola! Qual consulta deseja fazer? Por exemplo: "Quantas NF-e?", "Preciso de um relatorio" ou "Quais as pendencias?".'
    if re.match(r'^(emita|cancele|reprocesse|execute|rode|baixe)\b',question):
        return 'Operacoes fiscais de escrita permanecem bloqueadas. Nenhuma acao foi executada.'
    fiscal=evidence.get('source')=='fiscal_documents'
    if evidence.get('total_count')==0 and not evidence.get('pending_count') and not knowledge:
        return 'Nao ha registros autorizados no periodo selecionado. Nao ha evidencia suficiente para esta consulta; ajuste os filtros se necessario.'
    summary=re.fullmatch(r'(resumo|resumo fiscal|totais|total|valor total|quantos documentos|quantas notas|quantas nf-?e|quantas nfc-?e|quantas nfs-?e)( no periodo selecionado)?',question)
    if summary and fiscal:
        requested=re.search(r'\b(nf-?e|nfc-?e|nfs-?e)\b',question)
        if requested and requested.group(1).replace('-','')!=agent_name:
            if agent_name in ('fiscal','reports','financial_analysis') and isinstance(evidence.get('by_module'),list):
                module=requested.group(1).replace('-','')
                row=next((item for item in evidence['by_module'] if item.get('module')==module),None)
                evidence={**evidence,'total_count':row['total_count'] if row else 0,
                    'total_value':row.get('total_value') if row else None,
                    'missing_values':row.get('missing_values',0) if row else 0}
            else:
                return 'Selecione o agente do documento solicitado para consultar o total autorizado desse modulo.'
        value=evidence.get('total_value')
        value='R$ '+str(value).replace('.',',') if value is not None else 'nao informado'
        basis='importacao (UTC)' if evidence.get('period_basis')=='imported_at' else 'emissao'
        return (f"{evidence['total_count']} documentos armazenados autorizados; bruto conhecido: {value}; "
            f"{evidence.get('missing_values',0)} sem valor. Periodo por {basis}: "
            f"{evidence['date_from']} a {evidence['date_to']}. Valores brutos nao representam receita, lucro ou imposto devido.")
    if fiscal and re.fullmatch(r'(pendencias|pendencias nfce|pendencias nfc-e|quais nfce estao pendentes|quais nfc-e estao pendentes)',question):
        if agent_name not in ('nfce','fiscal','reports','financial_analysis') or 'pending_count' not in evidence:
            return 'Selecione o agente NFC-e ou Fiscal para consultar pendencias autorizadas.'
        return f"{evidence['pending_count']} pendencias de download por entrada na fila (UTC). Pendencia nao comprova emissao."
    if fiscal and re.fullmatch(r'(relatorio|gere um relatorio|relatorio mensal|notas por mes|documentos por mes)',question):
        rows=evidence.get('by_month',[])
        return 'Documentos armazenados por mes no periodo selecionado:\n'+('\n'.join(
            f"{row['competencia']}: {row['total_count']} documentos; bruto conhecido: {row.get('total_value') or 'nao informado'}."
            for row in rows) or 'Sem agregados mensais disponiveis.')
    if fiscal and re.fullmatch(r'(fornecedores|relatorio por fornecedor|valores por fornecedor)',question):
        return 'Fornecedores com identificador conhecido no periodo selecionado:\n'+('\n'.join(
            f"{row.get('supplier') or 'Nao informado'}: {row['total_count']} documentos; bruto conhecido: {row.get('total_value') or 'nao informado'}."
            for row in evidence.get('by_supplier',[])) or 'Sem fornecedores identificados disponiveis.')
    if evidence.get('source')=='execucoes' and re.fullmatch(r'(resumo|status|status dos jobs|jobs|falhas|resumo operacional)',question):
        return f"{evidence['total_count']} execucoes autorizadas no periodo selecionado.\n"+'\n'.join(
            f"{row['status']}: {row['total_count']}" for row in evidence.get('by_status',[]))+ '\nEstados nao estabelecem causas de falha nem disponibilidade dos servicos.'
    return None


class LocalFirstProvider:
    def __init__(self,factory,before_fallback):
        self.factory,self.before_fallback=factory,before_fallback
        self.delegate=None
        self.used_model=False

    @property
    def input_tokens(self):return self.delegate.input_tokens if self.delegate else 0

    @property
    def output_tokens(self):return self.delegate.output_tokens if self.delegate else 0

    async def respond(self,*,agent,prompt,observations):
        evidence=json.loads(observations[0]) if observations else {}
        knowledge=json.loads(observations[1]) if len(observations)>1 else []
        question=json.loads(prompt)['message']
        answer=local_answer(question,evidence,knowledge,agent.name)
        if answer is not None:
            return ProviderReply(answer)
        await self.before_fallback()
        self.delegate=self.factory()
        self.used_model=True
        return await self.delegate.respond(agent=agent,prompt=prompt,observations=observations)
