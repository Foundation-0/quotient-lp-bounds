"""Deterministic unit and adversarial `must_fail` tests for the Quotient-LP Synthesizer."""
from __future__ import annotations

import copy
import json
from fractions import Fraction
from pathlib import Path
import unittest

from verify import build_all_certificates, synthesize_1lipschitz_quotient_lp
from verify_independent import (
    loads_exact_json,
    verify_certificate_bundle_file,
    verify_quotient_lp_certificate,
)


class TestQuotientLpSynthesizer(unittest.TestCase):
    def test_01_regenerated_bundle_matches_stored_certificate_and_independent_verifier(self) -> None:
        cert_path = Path(__file__).resolve().parent.parent / "certificate.json"
        self.assertTrue(cert_path.is_file())
        regenerated = json.dumps(build_all_certificates(), indent=2, sort_keys=True) + "\n"
        self.assertEqual(cert_path.read_text(encoding="utf-8"), regenerated)

        res = verify_certificate_bundle_file(cert_path)
        self.assertTrue(res["valid"], msg=str(res))
        self.assertEqual(res["instances_verified"], 3)

    def test_02_strict_json_rejects_floats_bools_and_duplicate_keys(self) -> None:
        with self.assertRaises(ValueError):
            loads_exact_json('{"x": 1.5}')
        with self.assertRaises(ValueError):
            loads_exact_json('{"x": 1, "x": 2}')

        bundle = build_all_certificates()
        bad_bool = copy.deepcopy(bundle["instances"][0])
        bad_bool["primal_h"][0] = True
        self.assertFalse(verify_quotient_lp_certificate(bad_bool)["valid"])

    def test_03_must_fail_lipschitz_drop_and_duality_gap_and_deficit_drop(self) -> None:
        bundle = build_all_certificates()

        # 1. Corrupt primal_h to introduce a 2-step drop (`12 -> 10` style consistency breach)
        inst_lip = copy.deepcopy(bundle["instances"][0])
        # Restore raw un-repaired cap on an inconsistent state
        inst_lip["primal_h"] = list(inst_lip["upper_caps"])
        r_lip = verify_quotient_lp_certificate(inst_lip)
        self.assertFalse(r_lip["valid"])
        self.assertIn("lipschitz_violation", r_lip["reason"])

        # 2. Corrupt dual flow y_e to create a strong-duality / flow-conservation mismatch
        inst_dual = copy.deepcopy(bundle["instances"][1])
        inst_dual["dual_edge_y"][0] = "999/2"
        r_dual = verify_quotient_lp_certificate(inst_dual)
        self.assertFalse(r_dual["valid"])

        # 3. Corrupt zero-self-loop deficit so a non-self-loop edge decreases phi (`d_phi > 0`)
        inst_def = copy.deepcopy(bundle["instances"][0])
        inst_def["zero_self_loop_deficit"]["abstract_deficit_edges"].append(
            {"phi_u": 2, "phi_v": 5, "quotient_self_loop": False, "concrete_cost": 1}
        )
        r_def = verify_quotient_lp_certificate(inst_def)
        self.assertFalse(r_def["valid"])
        self.assertIn("non_self_loop_deficit_decreased", r_def["reason"])

    def test_04_must_fail_claimed_objectives_and_deficit_malformed_or_negative_fields(self) -> None:
        base = build_all_certificates()["instances"][0]

        # Tampered claimed primal/dual objectives
        bad_primal = copy.deepcopy(base)
        bad_primal["primal_objective"] = "999999"
        self.assertFalse(verify_quotient_lp_certificate(bad_primal)["valid"])

        bad_dual = copy.deepcopy(base)
        bad_dual["dual_objective"] = "999999"
        self.assertFalse(verify_quotient_lp_certificate(bad_dual)["valid"])

        missing_obj = copy.deepcopy(base)
        del missing_obj["primal_objective"]
        self.assertFalse(verify_quotient_lp_certificate(missing_obj)["valid"])

        # Negative phi_values
        neg_phi = copy.deepcopy(base)
        neg_phi["zero_self_loop_deficit"]["phi_values"][0] = -1
        self.assertFalse(verify_quotient_lp_certificate(neg_phi)["valid"])

        # Empty or non-list abstract_deficit_edges
        empty_edges = copy.deepcopy(base)
        empty_edges["zero_self_loop_deficit"]["abstract_deficit_edges"] = []
        self.assertFalse(verify_quotient_lp_certificate(empty_edges)["valid"])

        bad_edges_type = copy.deepcopy(base)
        bad_edges_type["zero_self_loop_deficit"]["abstract_deficit_edges"] = "not-a-list"
        self.assertFalse(verify_quotient_lp_certificate(bad_edges_type)["valid"])

        # Negative concrete_cost and malformed float-string concrete_cost (no unhandled exception)
        neg_cost = copy.deepcopy(base)
        neg_cost["zero_self_loop_deficit"]["abstract_deficit_edges"][0]["concrete_cost"] = -5
        self.assertFalse(verify_quotient_lp_certificate(neg_cost)["valid"])

        float_cost = copy.deepcopy(base)
        float_cost["zero_self_loop_deficit"]["abstract_deficit_edges"][0]["concrete_cost"] = "1.5"
        self.assertFalse(verify_quotient_lp_certificate(float_cost)["valid"])

        # Non-dict zero_self_loop_deficit (no unhandled AttributeError)
        bad_spec_type = copy.deepcopy(base)
        bad_spec_type["zero_self_loop_deficit"] = [1, 2, 3]
        self.assertFalse(verify_quotient_lp_certificate(bad_spec_type)["valid"])

    def test_05_deep_zero_weight_chain_iterative_arborescence_no_recursion_error(self) -> None:
        n = 2000
        edges = [(u, u - 1, Fraction(0, 1)) for u in range(1, n)]
        cert = synthesize_1lipschitz_quotient_lp(
            name="deep_zero_weight_chain_2000",
            num_vertices=n,
            goals=[0],
            edges=edges,
        )
        res = verify_quotient_lp_certificate(cert)
        self.assertTrue(res["valid"], msg=str(res))


if __name__ == "__main__":
    unittest.main()
