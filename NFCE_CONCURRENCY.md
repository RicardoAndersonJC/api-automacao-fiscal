# Filas NFC-e por organizacao

O worker usa duas threads por padrao (`NFCE_WORKERS=2`). Duas organizacoes
podem ter jobs ativos ao mesmo tempo; a admissao do endpoint interno continua
limitada a um job ativo por organizacao. Mais jobs aguardam uma thread livre.

As sessoes HTTP, os certificados e os diretorios continuam separados por job.
O limitador de consultas e downloads da SVRS e compartilhado entre as threads,
preservando os intervalos configurados e a pausa global por limite remoto.
Uma tentativa de download nao pode encurtar o intervalo reservado pelo processo.

No Render, altere `NFCE_WORKERS` para `2` se houver um valor explicito `1`.
Mantenha um unico processo Gunicorn (`--workers 1`) e uma unica instancia da API:
a fila e os limitadores ficam em memoria e nao coordenam multiplos processos.

Os logs `nfce_job_started` identificam `organizacao_id`, `run_id` e `workers`.
Para validar, inicie uma empresa em cada uma de duas organizacoes e confirme
que os dois jobs iniciam antes de o primeiro concluir. Os downloads continuam
respeitando o intervalo compartilhado de acesso ao portal.

Para voltar ao processamento sequencial, configure `NFCE_WORKERS=1` e reinicie.
