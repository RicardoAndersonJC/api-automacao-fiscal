# Download de XML NFC-e (SVRS)

## Arquitetura

- A tela `/xml-nfce` envia XML semente, PFX e senha diretamente para a API Python.
- O worker processa em fila (`NFCE_WORKERS=1` por padrão), mantém somente estado temporário e entrega um ZIP.
- Nenhum XML, resposta de consulta, senha ou certificado é gravado no banco do Nexu.
- A API valida a sessão Supabase e a permissão `downloads_xml` no início; o polling não consulta o banco durante os cinco minutos de cache da autorização.
- PFX e PEM não entram no ZIP. Os PEMs são apagados no `finally`; o diretório do job expira em seis horas.

## Deploy da API

Os arquivos prontos ficam no repositório `C:\Users\Acer\Music\API\api-automacao-fiscal`:

- `app.py`
- `nfce_download_worker.py`
- `test_nfce_download_worker.py`
- `.gitignore`

Use apenas um processo do Gunicorn para que criação, polling e download enxerguem a mesma fila em memória. O worker interno já limita a concorrência pesada:

```text
gunicorn app:app -k uvicorn.workers.UvicornWorker --workers 1
```

Variáveis:

```text
NFCE_ENABLE_SVRS_DISCOVERY=true
NFCE_WORKERS=1
NFCE_MAX_QUEUED_JOBS=10
NFCE_JOB_TTL_SECONDS=21600
NFCE_MAX_NUMERACOES=10000
```

`SUPABASE_URL` e `SUPABASE_ANON_KEY` podem sobrescrever os valores públicos já configurados no módulo.

## Ativação controlada

1. Confirme `/health` após a publicação.
2. Valide login e permissão com uma empresa de piloto autorizada.
3. Comece com `max_numeracoes` baixo e intervalo de download conservador.
4. Para rollback imediato, defina `NFCE_ENABLE_SVRS_DISCOVERY=false` e reinicie.

O método recebido usa respostas 217/613 do serviço de consulta para descobrir chaves. O serviço oficial é documentado para consulta de chave conhecida; por isso a ativação não é automática.

## Verificação local

```text
python -B -m unittest test_nfce_download_worker.py -v
npm run build
```

Não adicione PFX, P12, PEM ou KEY ao Git.
