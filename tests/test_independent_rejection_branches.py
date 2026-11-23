"""Exhaustive rejection-branch and guard-subcondition regression suite for verify_independent.py (Issues #2, #7).

Covers every rejection branch in `verify_quotient_lp_certificate` (42/42) and
`verify_certificate_bundle_file` (5/5), all nine Issue #7 guard sub-conditions,
plus `loads_exact_json` and `parse_q` boundaries, matching exact rejection reason
prefixes so deleting or weakening any single check cannot be silently masked by a
later check.

Uses unittest assertion methods only (zero bare `assert` statements), so
`python3 -O` executes every check identically.
"""
from __future__ import annotations

import copy
import json
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from verify_independent import (
    loads_exact_json,
    parse_q,
    verify_certificate_bundle_file,
    verify_quotient_lp_certificate,
)


def _minimal_valid_cert(
    *,
    with_caps: bool = False,
    with_deficit: bool = False,
    fractional_obj: bool = False,
) -> dict:
    """Self-contained minimal valid 2-vertex certificate (`1 -> 0`) with zero shared code."""
    w = "3/2" if fractional_obj else "2"
    h1 = "3/2" if fractional_obj else "2"
    cert: dict = {
        "name": "minimal_2v",
        "num_vertices": 2,
        "goals": [0],
        "weights_mu": [0, 1],
        "primal_h": [0, h1],
        "edges": [[1, 0, w]],
        "dual_edge_y": [1],
        "primal_objective": h1,
        "dual_objective": h1,
    }
    if with_caps:
        # Tight cap on vertex 1 (`cap[1] == 1 < w == 2`) with dual cap z[1] == 1.
        cert["primal_h"] = [0, "1"]
        cert["upper_caps"] = ["0", "1"]
        cert["dual_cap_z"] = ["0", "1"]
        cert["dual_edge_y"] = ["0"]
        cert["primal_objective"] = "1"
        cert["dual_objective"] = "1"
    if with_deficit:
        cert["zero_self_loop_deficit"] = {
            "phi_values": ["0", "2", "1"],
            "goal_phi_indices": [0],
            "abstract_deficit_edges": [
                {"phi_u": 1, "phi_v": 2, "quotient_self_loop": True, "concrete_cost": "1"},
                {"phi_u": 2, "phi_v": 1, "quotient_self_loop": False, "concrete_cost": "0"},
                {"phi_u": 0, "phi_v": 0, "quotient_self_loop": False, "concrete_cost": "0"},
            ],
        }
    return cert


class TestIndependentRejectionBranches(unittest.TestCase):
    def _assert_rejected(self, cert: object, expected_prefix: str, label: str = "") -> None:
        res = verify_quotient_lp_certificate(cert)  # type: ignore[arg-type]
        self.assertFalse(res["valid"], msg=f"{label}: expected rejection {expected_prefix!r}, got {res}")
        self.assertTrue(
            res["reason"].startswith(expected_prefix),
            msg=f"{label}: expected reason starting with {expected_prefix!r}, got {res['reason']!r}",
        )

    def test_01_minimal_valid_certificates_and_tight_boundaries_pass(self) -> None:
        for kwargs in (
            {},
            {"fractional_obj": True},
            {"with_caps": True},
            {"with_deficit": True},
            {"with_caps": True, "with_deficit": True},
        ):
            with self.subTest(**kwargs):
                cert = _minimal_valid_cert(**kwargs)
                res = verify_quotient_lp_certificate(cert)
                self.assertTrue(res["valid"], msg=str(res))
                self.assertEqual(res["reason"], "ok")
                self.assertEqual(res["num_vertices"], 2)
                self.assertEqual(res["num_edges"], 1)
                self.assertEqual(res["primal_objective"], cert["primal_objective"])
                self.assertEqual(res["dual_objective"], cert["dual_objective"])

        # Tight equality on goal == n-1, edge weight == 0, dual_y == 0, mu == 0, default concrete_cost.
        cert_zero = {
            "name": "zero_boundary",
            "num_vertices": 2,
            "goals": [1],
            "weights_mu": [0, 0],
            "primal_h": [0, 0],
            "edges": [[0, 1, 0]],
            "dual_edge_y": [0],
            "primal_objective": 0,
            "dual_objective": 0,
            "zero_self_loop_deficit": {
                "phi_values": [0, 1],
                "goal_phi_indices": [0],
                "abstract_deficit_edges": [
                    {"phi_u": 1, "phi_v": 0, "quotient_self_loop": True},
                ],
            },
        }
        res_zero = verify_quotient_lp_certificate(cert_zero)
        self.assertTrue(res_zero["valid"], msg=str(res_zero))
        self.assertEqual(res_zero["primal_objective"], "0")
        self.assertEqual(res_zero["dual_objective"], "0")

    def test_02_exact_json_and_parse_q_strictness(self) -> None:
        for bad_json in ('{"x": 1.5}', '{"x": NaN}', '{"x": Infinity}', '{"x": -Infinity}', '{"a": 1, "a": 2}'):
            with self.subTest(bad_json=bad_json), self.assertRaises(ValueError):
                loads_exact_json(bad_json)
        self.assertEqual(loads_exact_json('{"a": 1, "b": "3/2"}'), {"a": 1, "b": "3/2"})

        self.assertEqual(parse_q(0), 0)
        self.assertEqual(parse_q(-5), -5)
        self.assertEqual(parse_q(" 3/4 "), parse_q("6/8"))
        self.assertEqual(parse_q(" -7 "), -7)
        for bad_dec in ("", "   ", "1.5", "1e3", "1E3"):
            with self.subTest(bad_dec=bad_dec), self.assertRaisesRegex(
                ValueError, "Decimal/scientific notation forbidden"
            ):
                parse_q(bad_dec)
        for bad_q in (True, False, "1/2/3", "1/0", "1/-2", "abc", None, 1.5, [1]):
            with self.subTest(bad_q=bad_q), self.assertRaises(ValueError):
                parse_q(bad_q)

    def test_03_top_level_shape_goals_and_primal_weight_checks(self) -> None:
        # 1. cert_not_dict
        for bad in ("not-a-dict", [1, 2], None, 42):
            self._assert_rejected(bad, "cert_not_dict")

        # 2. invalid_num_vertices
        for bad_n in (True, False, 0, -1, "2", None):
            c = _minimal_valid_cert()
            c["num_vertices"] = bad_n
            self._assert_rejected(c, "invalid_num_vertices", f"n={bad_n!r}")

        # 3. empty_or_invalid_goals
        for bad_goals in ([], "0", None, {0: 1}):
            c = _minimal_valid_cert()
            c["goals"] = bad_goals
            self._assert_rejected(c, "empty_or_invalid_goals", f"goals={bad_goals!r}")

        # 4. goal_out_of_range
        for bad_g in (True, False, -1, 2, "0"):
            c = _minimal_valid_cert()
            c["goals"] = [bad_g]
            self._assert_rejected(c, "goal_out_of_range", f"g={bad_g!r}")

        # 5. weights_mu_length_mismatch
        for bad_mu in ([0], [0, 1, 2], "bad", None):
            c = _minimal_valid_cert()
            c["weights_mu"] = bad_mu
            self._assert_rejected(c, "weights_mu_length_mismatch", f"mu={bad_mu!r}")

        # 6. primal_h_length_mismatch
        for bad_h in ([0], [0, 2, 3], "bad", None):
            c = _minimal_valid_cert()
            c["primal_h"] = bad_h
            self._assert_rejected(c, "primal_h_length_mismatch", f"h={bad_h!r}")

        # 7. rational_parse_error (both weights_mu and primal_h)
        c = _minimal_valid_cert()
        c["weights_mu"][1] = "1.5"
        self._assert_rejected(c, "rational_parse_error:", "mu float str")
        c = _minimal_valid_cert()
        c["primal_h"][1] = True
        self._assert_rejected(c, "rational_parse_error:", "h bool")

        # 8. negative_mu_at_u
        c = _minimal_valid_cert()
        c["weights_mu"][0] = "-1/2"
        self._assert_rejected(c, "negative_mu_at_0")

        # 9. negative_h_at_u
        c = _minimal_valid_cert()
        c["primal_h"][1] = "-1"
        self._assert_rejected(c, "negative_h_at_1")

        # 10. nonzero_goal_h_at_u
        c = _minimal_valid_cert()
        c["primal_h"][0] = "1/10"
        self._assert_rejected(c, "nonzero_goal_h_at_0")

    def test_04_upper_cap_and_dual_cap_checks(self) -> None:
        # 11. upper_caps_length_mismatch
        for bad_caps in (["0"], ["0", "1", "2"], "bad"):
            c = _minimal_valid_cert(with_caps=True)
            c["upper_caps"] = bad_caps
            self._assert_rejected(c, "upper_caps_length_mismatch", f"caps={bad_caps!r}")

        # 12. dual_cap_z_length_mismatch
        for bad_z in (["0"], ["0", "1", "2"], "bad", None):
            c = _minimal_valid_cert(with_caps=True)
            c["dual_cap_z"] = bad_z
            self._assert_rejected(c, "dual_cap_z_length_mismatch", f"z={bad_z!r}")

        # 13. cap_parse_error (both upper_caps and dual_cap_z)
        c = _minimal_valid_cert(with_caps=True)
        c["upper_caps"][1] = "1.5"
        self._assert_rejected(c, "cap_parse_error:", "upper_caps parse")
        c = _minimal_valid_cert(with_caps=True)
        c["dual_cap_z"][1] = True
        self._assert_rejected(c, "cap_parse_error:", "dual_cap_z parse")

        # 14. primal_exceeds_cap_at_u
        c = _minimal_valid_cert(with_caps=True)
        c["upper_caps"][1] = "1/2"
        self._assert_rejected(c, "primal_exceeds_cap_at_1")

        # 15. negative_dual_z_at_u
        c = _minimal_valid_cert(with_caps=True)
        c["dual_cap_z"][0] = "-1/4"
        self._assert_rejected(c, "negative_dual_z_at_0")

    def test_05_edge_lipschitz_flow_duality_and_claimed_objective_checks(self) -> None:
        # 16. edges_or_dual_y_length_mismatch
        for edges_val, y_val in (([], [1]), ([[1, 0, 2]], []), ("bad", [1]), ([[1, 0, 2]], "bad")):
            c = _minimal_valid_cert()
            c["edges"] = edges_val
            c["dual_edge_y"] = y_val
            self._assert_rejected(c, "edges_or_dual_y_length_mismatch")

        # 17. malformed_edge_idx
        for bad_edge in ([1, 0], [1, 0, 2, 3], "bad"):
            c = _minimal_valid_cert()
            c["edges"][0] = bad_edge
            self._assert_rejected(c, "malformed_edge_0")

        # 18. non_int_edge_endpoint_idx
        for bad_edge in ([True, 0, 2], [1, False, 2], ["1", 0, 2], [1, "0", 2]):
            c = _minimal_valid_cert()
            c["edges"][0] = bad_edge
            self._assert_rejected(c, "non_int_edge_endpoint_0")

        # 19. edge_endpoint_out_of_range_idx
        for bad_edge in ([-1, 0, 2], [2, 0, 2], [1, -1, 2], [1, 2, 2]):
            c = _minimal_valid_cert()
            c["edges"][0] = bad_edge
            self._assert_rejected(c, "edge_endpoint_out_of_range_0")

        # 20. edge_rational_error_idx (both weight and dual_y)
        c = _minimal_valid_cert()
        c["edges"][0][2] = "2.5"
        self._assert_rejected(c, "edge_rational_error_0:", "edge weight parse")
        c = _minimal_valid_cert()
        c["dual_edge_y"][0] = False
        self._assert_rejected(c, "edge_rational_error_0:", "dual_y parse")

        # 21. negative_edge_weight_idx
        c = _minimal_valid_cert()
        c["edges"][0][2] = "-1"
        self._assert_rejected(c, "negative_edge_weight_0")

        # 22. negative_dual_y_idx
        c = _minimal_valid_cert()
        c["dual_edge_y"][0] = "-1/2"
        self._assert_rejected(c, "negative_dual_y_0")

        # 23. lipschitz_violation_edge_idx
        c = _minimal_valid_cert()
        c["primal_h"][1] = "5/2"
        self._assert_rejected(c, "lipschitz_violation_edge_0:1->0")

        # 24. dual_flow_conservation_failed_at_u (primal feasible, dual flow deficient at vertex 1)
        c = _minimal_valid_cert()
        c["dual_edge_y"][0] = "1/2"
        self._assert_rejected(c, "dual_flow_conservation_failed_at_1")

        # 24b. inflow subtraction matters: 3-vertex chain `2 -> 1 -> 0` where net_out[1] = y_{1->0} - y_{2->1} < mu[1]
        c_chain = {
            "name": "chain_inflow",
            "num_vertices": 3,
            "goals": [0],
            "weights_mu": [0, 1, 1],
            "primal_h": [0, 1, 2],
            "edges": [[2, 1, 1], [1, 0, 1]],
            "dual_edge_y": [1, 1],  # net_out[2]=1 >= 1, net_out[1]=1-1=0 < 1
            "primal_objective": 3,
            "dual_objective": 2,
        }
        self._assert_rejected(c_chain, "dual_flow_conservation_failed_at_1")

        # 25. strong_duality_gap_nonzero (primal & dual both feasible, claimed objectives match own computed sides!)
        # If strong_duality_gap_nonzero is deleted, claimed_primal and claimed_dual would still match and pass!
        c = _minimal_valid_cert()
        c["dual_edge_y"][0] = "2"  # dual_obj = 4 != primal_obj = 2; net_out[1] = 2 >= mu[1] = 1
        c["primal_objective"] = "2"
        c["dual_objective"] = "4"
        self._assert_rejected(c, "strong_duality_gap_nonzero:2!=4")

        # 26. missing_claimed_objectives (both missing primal and missing dual)
        for key in ("primal_objective", "dual_objective"):
            c = _minimal_valid_cert()
            del c[key]
            self._assert_rejected(c, "missing_claimed_objectives", f"missing {key}")

        # 27. claimed_objective_parse_error (both primal and dual)
        for key in ("primal_objective", "dual_objective"):
            c = _minimal_valid_cert()
            c[key] = "2.0"
            self._assert_rejected(c, "claimed_objective_parse_error:", f"parse {key}")

        # 28. claimed_primal_objective_mismatch
        c = _minimal_valid_cert()
        c["primal_objective"] = "3"
        self._assert_rejected(c, "claimed_primal_objective_mismatch:2!=3")

        # 29. claimed_dual_objective_mismatch
        c = _minimal_valid_cert()
        c["dual_objective"] = "3"
        self._assert_rejected(c, "claimed_dual_objective_mismatch:2!=3")

    def test_06_zero_self_loop_deficit_checks(self) -> None:
        # 30. invalid_deficit_spec_type
        for bad_spec in ([1, 2], "bad", 7):
            c = _minimal_valid_cert(with_deficit=True)
            c["zero_self_loop_deficit"] = bad_spec
            self._assert_rejected(c, "invalid_deficit_spec_type")

        # 31. invalid_deficit_phi_values
        for bad_phi in ([], "bad", None):
            c = _minimal_valid_cert(with_deficit=True)
            c["zero_self_loop_deficit"]["phi_values"] = bad_phi
            self._assert_rejected(c, "invalid_deficit_phi_values")

        # 32. empty_or_invalid_deficit_edges
        for bad_edges in ([], "bad", None):
            c = _minimal_valid_cert(with_deficit=True)
            c["zero_self_loop_deficit"]["abstract_deficit_edges"] = bad_edges
            self._assert_rejected(c, "empty_or_invalid_deficit_edges")

        # 33. deficit_phi_parse_error
        c = _minimal_valid_cert(with_deficit=True)
        c["zero_self_loop_deficit"]["phi_values"][1] = "2.5"
        self._assert_rejected(c, "deficit_phi_parse_error:")

        # 34. negative_deficit_phi
        c = _minimal_valid_cert(with_deficit=True)
        c["zero_self_loop_deficit"]["phi_values"][2] = "-1/3"
        self._assert_rejected(c, "negative_deficit_phi")

        # 35. empty_or_invalid_goal_phi_indices
        for bad_gi in ([], "bad", None):
            c = _minimal_valid_cert(with_deficit=True)
            c["zero_self_loop_deficit"]["goal_phi_indices"] = bad_gi
            self._assert_rejected(c, "empty_or_invalid_goal_phi_indices")

        # 36. nonzero_or_invalid_goal_phi (all 5 disjuncts)
        for bad_idx in (True, "0", -1, 3, 1):
            c = _minimal_valid_cert(with_deficit=True)
            c["zero_self_loop_deficit"]["goal_phi_indices"] = [bad_idx]
            self._assert_rejected(c, "nonzero_or_invalid_goal_phi", f"gi={bad_idx!r}")

        # 37. malformed_deficit_edge_idx
        c = _minimal_valid_cert(with_deficit=True)
        c["zero_self_loop_deficit"]["abstract_deficit_edges"][0] = "not-a-dict"
        self._assert_rejected(c, "malformed_deficit_edge_0")

        # 38. invalid_deficit_edge_fields_idx (all 9 disjuncts)
        bad_edge_variants = [
            {"phi_u": True, "phi_v": 0, "quotient_self_loop": True, "concrete_cost": 1},
            {"phi_u": 1, "phi_v": False, "quotient_self_loop": True, "concrete_cost": 1},
            {"phi_u": "1", "phi_v": 0, "quotient_self_loop": True, "concrete_cost": 1},
            {"phi_u": 1, "phi_v": "0", "quotient_self_loop": True, "concrete_cost": 1},
            {"phi_u": -1, "phi_v": 0, "quotient_self_loop": True, "concrete_cost": 1},
            {"phi_u": 3, "phi_v": 0, "quotient_self_loop": True, "concrete_cost": 1},
            {"phi_u": 1, "phi_v": -1, "quotient_self_loop": True, "concrete_cost": 1},
            {"phi_u": 1, "phi_v": 3, "quotient_self_loop": True, "concrete_cost": 1},
            {"phi_u": 1, "phi_v": 0, "quotient_self_loop": 1, "concrete_cost": 1},
        ]
        for variant in bad_edge_variants:
            c = _minimal_valid_cert(with_deficit=True)
            c["zero_self_loop_deficit"]["abstract_deficit_edges"][0] = variant
            self._assert_rejected(c, "invalid_deficit_edge_fields_0", str(variant))

        # 39. deficit_edge_cost_parse_error_idx
        c = _minimal_valid_cert(with_deficit=True)
        c["zero_self_loop_deficit"]["abstract_deficit_edges"][0]["concrete_cost"] = "1.5"
        self._assert_rejected(c, "deficit_edge_cost_parse_error_0:")

        # 40. negative_deficit_edge_cost_idx
        c = _minimal_valid_cert(with_deficit=True)
        c["zero_self_loop_deficit"]["abstract_deficit_edges"][0]["concrete_cost"] = "-1"
        self._assert_rejected(c, "negative_deficit_edge_cost_0")

        # 41. self_loop_deficit_drop_exceeds_cost_idx (d_phi = 2 - 1 = 1 > cost = 1/2)
        c = _minimal_valid_cert(with_deficit=True)
        c["zero_self_loop_deficit"]["abstract_deficit_edges"][0]["concrete_cost"] = "1/2"
        self._assert_rejected(c, "self_loop_deficit_drop_exceeds_cost_0")

        # 42. non_self_loop_deficit_decreased_idx (d_phi = 2 - 1 = 1 > 0 on non-self-loop)
        c = _minimal_valid_cert(with_deficit=True)
        c["zero_self_loop_deficit"]["abstract_deficit_edges"][1] = {
            "phi_u": 1,
            "phi_v": 2,
            "quotient_self_loop": False,
            "concrete_cost": "10",
        }
        self._assert_rejected(c, "non_self_loop_deficit_decreased_1")

    def test_07_bundle_file_rejection_branches(self) -> None:
        valid_inst = _minimal_valid_cert(with_caps=True, with_deficit=True)
        dup_inst = copy.deepcopy(valid_inst)
        bad_inst = copy.deepcopy(valid_inst)
        bad_inst["name"] = "broken_inst"
        bad_inst["primal_objective"] = "999"

        cases = [
            ([1, 2, 3], "missing_instances_list"),
            ({}, "missing_instances_list"),
            ({"instances": []}, "empty_instances_list"),
            ({"instances": "not-a-list"}, "empty_instances_list"),
            ({"instances": ["not-a-dict"]}, "instance_0_not_dict"),
            ({"instances": [{"name": ""}]}, "invalid_or_duplicate_instance_name_at_0"),
            ({"instances": [{"name": 123}]}, "invalid_or_duplicate_instance_name_at_0"),
            ({"instances": [valid_inst, dup_inst]}, "invalid_or_duplicate_instance_name_at_1"),
            ({"instances": [bad_inst]}, "instance_broken_inst_failed:claimed_primal_objective_mismatch:"),
        ]
        with tempfile.TemporaryDirectory() as td:
            for idx, (payload, expected_prefix) in enumerate(cases):
                p = Path(td) / f"bundle_{idx}.json"
                p.write_text(json.dumps(payload), encoding="utf-8")
                res = verify_certificate_bundle_file(p)
                self.assertFalse(res["valid"], msg=f"case {idx}: {res}")
                self.assertTrue(
                    res["reason"].startswith(expected_prefix),
                    msg=f"case {idx}: expected {expected_prefix!r}, got {res['reason']!r}",
                )

            p_ok = Path(td) / "bundle_ok.json"
            p_ok.write_text(json.dumps({"instances": [valid_inst]}), encoding="utf-8")
            res_ok = verify_certificate_bundle_file(p_ok)
            self.assertTrue(res_ok["valid"], msg=str(res_ok))
            self.assertEqual(res_ok["instances_verified"], 1)

    def test_08_main_cli_exits_zero_on_valid_and_nonzero_on_invalid_bundle(self) -> None:
        proc_ok = subprocess.run(
            [sys.executable, "-I", "-O", "-B", str(ROOT / "verify_independent.py")],
            cwd=ROOT,
            text=True,
            capture_output=True,
            check=False,
        )
        self.assertEqual(proc_ok.returncode, 0, msg=proc_ok.stderr)
        self.assertTrue(json.loads(proc_ok.stdout)["valid"])

        with tempfile.TemporaryDirectory() as td:
            work = Path(td) / "repo"
            work.mkdir()
            shutil.copy2(ROOT / "verify_independent.py", work / "verify_independent.py")
            (work / "certificate.json").write_text('{"instances": []}\n', encoding="utf-8")
            proc_bad = subprocess.run(
                [sys.executable, "-I", "-O", "-B", str(work / "verify_independent.py")],
                cwd=work,
                text=True,
                capture_output=True,
                check=False,
            )
            self.assertEqual(proc_bad.returncode, 1, msg=proc_bad.stdout + proc_bad.stderr)
            parsed = json.loads(proc_bad.stdout)
            self.assertFalse(parsed["valid"])
            self.assertEqual(parsed["reason"], "empty_instances_list")

    def test_09_issue7_guard_subconditions_and_boundary_accepts(self) -> None:
        # Row 1: n <= 0 -> n <= 1 (valid 1-vertex certificate must be accepted).
        cert_one = {
            "name": "single_vertex",
            "num_vertices": 1,
            "goals": [0],
            "weights_mu": [0],
            "primal_h": [0],
            "edges": [],
            "dual_edge_y": [],
            "primal_objective": 0,
            "dual_objective": 0,
        }
        res_one = verify_quotient_lp_certificate(cert_one)
        self.assertTrue(res_one["valid"], msg=str(res_one))
        self.assertEqual(res_one["reason"], "ok")
        self.assertEqual(res_one["num_vertices"], 1)
        self.assertEqual(res_one["num_edges"], 0)
        self.assertEqual(res_one["primal_objective"], "0")
        self.assertEqual(res_one["dual_objective"], "0")

        # Row 2: den <= 0 -> den <= 1 (explicit "1/1" rational denominator must be accepted).
        self.assertEqual(parse_q("1/1"), 1)
        cert_unit_den = {
            "name": "unit_denominator",
            "num_vertices": 2,
            "goals": [0],
            "weights_mu": [0, 1],
            "primal_h": [0, "1/1"],
            "edges": [[1, 0, "1/1"]],
            "dual_edge_y": ["1/1"],
            "primal_objective": "1/1",
            "dual_objective": "1/1",
        }
        res_unit = verify_quotient_lp_certificate(cert_unit_den)
        self.assertTrue(res_unit["valid"], msg=str(res_unit))
        self.assertEqual(res_unit["reason"], "ok")
        self.assertEqual(res_unit["primal_objective"], "1")
        self.assertEqual(res_unit["dual_objective"], "1")

        # Row 3: isinstance(gi, bool) removed in goal_phi_indices check
        # (`phi_values = [0, 0]` ensures phi[True] == 0 does not mask removal).
        for bad_bool_gi in (True, False):
            c_bool = _minimal_valid_cert(with_deficit=True)
            c_bool["zero_self_loop_deficit"] = {
                "phi_values": [0, 0],
                "goal_phi_indices": [bad_bool_gi],
                "abstract_deficit_edges": [
                    {"phi_u": 0, "phi_v": 1, "quotient_self_loop": False, "concrete_cost": 0},
                ],
            }
            self._assert_rejected(c_bool, "nonzero_or_invalid_goal_phi", f"bool gi={bad_bool_gi!r}")

        # Rows 4 & 5: gi < 0 removed and gi < -1 in goal_phi_indices check
        # (`phi_values = [0, 2, 0]` ensures phi[-1] == 0 does not mask removal/weakening).
        c_neg = _minimal_valid_cert(with_deficit=True)
        c_neg["zero_self_loop_deficit"] = {
            "phi_values": [0, 2, 0],
            "goal_phi_indices": [-1],
            "abstract_deficit_edges": [
                {"phi_u": 1, "phi_v": 2, "quotient_self_loop": True, "concrete_cost": 2},
            ],
        }
        self._assert_rejected(c_neg, "nonzero_or_invalid_goal_phi", "gi=-1 with phi[-1]==0")

        # Shared 2-vertex zero-weight base so length-matched strings cannot be masked by later checks.
        base_zero = {
            "name": "zero_2v",
            "num_vertices": 2,
            "goals": [0],
            "weights_mu": [0, 0],
            "primal_h": [0, 0],
            "edges": [],
            "dual_edge_y": [],
            "primal_objective": 0,
            "dual_objective": 0,
        }
        res_base = verify_quotient_lp_certificate(base_zero)
        self.assertTrue(res_base["valid"], msg=str(res_base))

        # Row 6: not isinstance(caps_raw, list) removed (`len("00") == 2` and every char parses to 0).
        c_caps_str = copy.deepcopy(base_zero)
        c_caps_str["upper_caps"] = "00"
        c_caps_str["dual_cap_z"] = [0, 0]
        self._assert_rejected(c_caps_str, "upper_caps_length_mismatch", "upper_caps='00'")

        # Row 7: not isinstance(edges_raw, list) removed (`len("") == len([]) == 0`).
        c_edges_str = copy.deepcopy(base_zero)
        c_edges_str["edges"] = ""
        c_edges_str["dual_edge_y"] = []
        self._assert_rejected(c_edges_str, "edges_or_dual_y_length_mismatch", "edges=''")

        # Row 8: not isinstance(y_raw, list) removed (`len([]) == len("") == 0`).
        c_y_str = copy.deepcopy(base_zero)
        c_y_str["edges"] = []
        c_y_str["dual_edge_y"] = ""
        self._assert_rejected(c_y_str, "edges_or_dual_y_length_mismatch", "dual_edge_y=''")

        # Same-length string guards on weights_mu, primal_h, dual_cap_z, and phi_values.
        for field, expected in (
            ("weights_mu", "weights_mu_length_mismatch"),
            ("primal_h", "primal_h_length_mismatch"),
        ):
            c_str = copy.deepcopy(base_zero)
            c_str[field] = "00"
            self._assert_rejected(c_str, expected, f"{field}='00'")
        c_z_str = copy.deepcopy(base_zero)
        c_z_str["upper_caps"] = [0, 0]
        c_z_str["dual_cap_z"] = "00"
        self._assert_rejected(c_z_str, "dual_cap_z_length_mismatch", "dual_cap_z='00'")
        c_phi_str = copy.deepcopy(base_zero)
        c_phi_str["zero_self_loop_deficit"] = {
            "phi_values": "00",
            "goal_phi_indices": [0],
            "abstract_deficit_edges": [
                {"phi_u": 0, "phi_v": 1, "quotient_self_loop": False, "concrete_cost": 0},
            ],
        }
        self._assert_rejected(c_phi_str, "invalid_deficit_phi_values", "phi_values='00'")

        # Row 9: not isinstance(data, dict) removed (`"instances" in ["instances"]` is True;
        # without the dict guard, `data["instances"]` raises TypeError instead of returning a reason).
        with tempfile.TemporaryDirectory() as td:
            p_list = Path(td) / "list_with_instances_str.json"
            p_list.write_text('["instances"]\n', encoding="utf-8")
            res_list = verify_certificate_bundle_file(p_list)
            self.assertFalse(res_list["valid"], msg=str(res_list))
            self.assertEqual(res_list["reason"], "missing_instances_list")


if __name__ == "__main__":
    unittest.main()
