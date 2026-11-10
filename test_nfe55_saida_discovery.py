import unittest

from nfe55_saida_discovery import (
    avancar,
    cfg_da_chave,
    chave_artificial,
    extrair_xml_portal,
    interpretar_consulta,
    ler_xml_semente,
    modulo11_dv,
    proximo_aamm,
)


def chave_valida(**troca: str) -> str:
    cfg = {
        "cUF": "27",
        "AAMM": "2608",
        "CNPJ": "12345678000199",
        "modelo": "55",
        "serie": "001",
        "tpEmis": "1",
    }
    cfg.update(troca)
    return chave_artificial(cfg, 123, cfg["AAMM"])


class Nfe55DiscoveryTest(unittest.TestCase):
    def test_rejeita_modelo_65(self):
        cfg = {
            "cUF": "27", "AAMM": "2608", "CNPJ": "12345678000199",
            "modelo": "65", "serie": "001", "tpEmis": "1",
        }
        chave = chave_artificial(cfg, 10, "2608")
        with self.assertRaisesRegex(ValueError, "modelo 65"):
            cfg_da_chave(chave)

    def test_rejeita_dv_invalido(self):
        chave = chave_valida()
        quebrada = chave[:-1] + ("0" if chave[-1] != "0" else "1")
        with self.assertRaisesRegex(ValueError, "verificador"):
            cfg_da_chave(quebrada)

    def test_cstat_100_exige_a_chave_consultada(self):
        cfg = cfg_da_chave(chave_valida())
        outra = chave_artificial(cfg, 124, "2608")
        texto = f"<retConsSitNFe><cStat>100</cStat><xMotivo>Autorizado</xMotivo><chNFe>{outra}</chNFe></retConsSitNFe>"
        codigo, _motivo, real = interpretar_consulta(texto, cfg, 123, "2608")
        self.assertEqual(codigo, "100")
        self.assertEqual(real, "")

    def test_cstat_613_troca_o_mes(self):
        cfg = cfg_da_chave(chave_valida())
        real = chave_artificial(cfg, 123, "2609")
        texto = f"<retConsSitNFe><cStat>613</cStat><xMotivo>Chave</xMotivo><chNFe>{real}</chNFe></retConsSitNFe>"
        passo = avancar(cfg, "2608", 123, 4, 15, texto)
        self.assertEqual(passo.encontrada, real)
        self.assertEqual(passo.aamm, "2609")
        self.assertEqual(passo.consecutivos_217, 0)

    def test_217_no_mes_atual_e_no_seguinte_encerra_a_lacuna(self):
        cfg = cfg_da_chave(chave_valida())
        atual = "<retConsSitNFe><cStat>217</cStat><xMotivo>Inexistente</xMotivo></retConsSitNFe>"
        passo = avancar(cfg, "2608", 123, 14, 15, atual, atual)
        self.assertTrue(passo.encerrar)
        self.assertTrue(passo.lacuna)
        self.assertEqual(passo.nnf, 124)

    def test_100_no_mes_seguinte_continua(self):
        cfg = cfg_da_chave(chave_valida())
        atual = "<retConsSitNFe><cStat>217</cStat><xMotivo>Inexistente</xMotivo></retConsSitNFe>"
        real = chave_artificial(cfg, 123, "2609")
        seguinte = f"<retConsSitNFe><cStat>100</cStat><chNFe>{real}</chNFe></retConsSitNFe>"
        passo = avancar(cfg, "2608", 123, 14, 15, atual, seguinte)
        self.assertEqual(passo.encontrada, real)
        self.assertFalse(passo.encerrar)

    def test_xml_semente_modelo_55(self):
        chave = chave_valida()
        xml = (
            '<nfeProc xmlns="http://www.portalfiscal.inf.br/nfe"><NFe>'
            f'<infNFe Id="NFe{chave}"><ide><cUF>27</cUF><mod>55</mod><serie>1</serie>'
            '<nNF>123</nNF><tpEmis>1</tpEmis></ide><emit><CNPJ>12345678000199</CNPJ>'
            '<xNome>Empresa</xNome></emit></infNFe></NFe></nfeProc>'
        ).encode()
        cfg = ler_xml_semente(xml)
        self.assertEqual(cfg["chave_semente"], chave)
        self.assertEqual(cfg["nNF_semente"], 123)

    def test_extrai_xml_do_portal(self):
        bruto = '{"stringJson":{"xml":"<nfeProc><infNFe Id=\\"NFe1\\"></infNFe></nfeProc>"}}'
        self.assertIn("<nfeProc>", extrair_xml_portal(bruto) or "")

    def test_proximo_mes_vira_o_ano(self):
        self.assertEqual(proximo_aamm("2612"), "2701")
        self.assertEqual(len(modulo11_dv("1" * 43)), 1)


if __name__ == "__main__":
    unittest.main()
