"""Deterministic unit and adversarial `must_fail` tests for the Quotient-LP Synthesizer."""
from __future__ import annotations

import copy
import json
from pathlib import Path
import unittest

from verify import build_all_certificates
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


if __name__ == "__main__":
    unittest.main()
