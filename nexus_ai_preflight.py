"""Offline deployment checks. Never prints configuration values or calls a service."""
import argparse
import json
from decimal import Decimal
from urllib.parse import urlsplit

try:
    from .nexus_ai_api import Settings
except ImportError:
    from nexus_ai_api import Settings


def safe_origin(value, production):
    try:
        uri=urlsplit(value)
        local=uri.hostname in ('localhost','127.0.0.1','::1')
        return bool(uri.hostname and not any(c.isspace() or c=='\\' for c in value)
            and not uri.username and not uri.password and not uri.query
            and not uri.fragment and uri.path in ('','/') and '*' not in uri.netloc
            and (uri.scheme=='https' and (not production or not local)
                 or not production and local and uri.scheme=='http') and uri.port != 0)
    except ValueError:
        return False


def check(settings, frontend_url, *, production=False, admin_pilot=False):
    checks={
        'supabase_https':safe_origin(settings.supabase_url,True),
        'server_credentials_present':all((settings.publishable_key,settings.service_key,settings.provider_key)),
        'public_private_keys_distinct':bool(settings.publishable_key and settings.service_key
            and settings.publishable_key!=settings.service_key and settings.provider_key!=settings.service_key
            and settings.provider_key!=settings.publishable_key),
        'model_selected':bool(settings.model.strip()),
        'read_tools_selected':settings.read_tools_enabled,
        'origins_explicit':bool(settings.allowed_origins) and all(safe_origin(o,production) for o in settings.allowed_origins),
        'frontend_origin_allowed':safe_origin(frontend_url,production) and frontend_url.rstrip('/') in settings.allowed_origins,
        'prices_configured':all(isinstance(p,Decimal) and p.is_finite() and Decimal(0)<=p<=Decimal(10000)
            for p in (settings.input_price_per_million,settings.output_price_per_million)),
    }
    if admin_pilot:
        checks['admin_only_required']=settings.admin_only is True
    return {'ready_for_environment_validation':all(checks.values()),'checks':checks,
        'ai_enabled':settings.enabled,'writes_enabled':False,'network_requests':0,
        'remaining_gates':['database_schema_and_acl','independent_review','approved_model_quality_eval','deployment_authorization']}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--frontend-origin',required=True)
    parser.add_argument('--production',action='store_true')
    parser.add_argument('--admin-pilot',action='store_true',help='Require admin-only access for the pilot.')
    args=parser.parse_args()
    report=check(Settings.from_env(),args.frontend_origin,production=args.production,admin_pilot=args.admin_pilot)
    print(json.dumps(report,sort_keys=True))
    return 0 if report['ready_for_environment_validation'] else 1


if __name__=='__main__':
    raise SystemExit(main())
