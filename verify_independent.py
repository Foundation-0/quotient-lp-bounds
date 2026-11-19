"""Independent zero-import verifier for Certified Quotient-LP + Monotone Deficit certificates.

Contains zero shared imports from the synthesizer (`verify.py` / `soko_mcp`), uses only
Python standard library `fractions.Fraction`, `json`, `hashlib`, and `pathlib`, and fails
closed on floats, booleans-as-integers, duplicate JSON keys, primal consistency violations,
dual flow conservation mismatches, or strong-duality gaps (`mde guard --code-audit` clean).
"""
from __future__ import annotations

from fractions import Fraction
import json
from pathlib import Path
from typing import Any, Dict, List, Tuple


def _reject_float_const(tok: str) -> Any:
    raise ValueError(f"Forbidden JSON constant in exact certificate: {tok}")


def _reject_float_num(tok: str) -> Any:
    raise ValueError(f"Forbidden float literal in exact certificate: {tok}")


def _reject_dup_keys(pairs: List[Tuple[str, Any]]) -> Dict[str, Any]:
    out: Dict[str, Any] = {}
    for k, v in pairs:
        if k in out:
            raise ValueError(f"Duplicate JSON key in exact certificate: {k!r}")
        out[k] = v
    return out


def loads_exact_json(raw: str) -> Any:
    """Parse JSON strictly without float literals, NaN/Infinity, or duplicate keys."""
    return json.loads(
        raw,
        parse_float=_reject_float_num,
        parse_constant=_reject_float_const,
        object_pairs_hook=_reject_dup_keys,
    )


def parse_q(val: Any) -> Fraction:
    """Parse an exact integer or `'p/q'` rational string without floats or bools."""
    if isinstance(val, bool):
        raise ValueError("Boolean is not a valid rational value")
    if isinstance(val, int):
        return Fraction(val, 1)
    if isinstance(val, str):
        s = val.strip()
        if not s or "." in s or "e" in s or "E" in s:
            raise ValueError(f"Decimal/scientific notation forbidden in exact rational: {val!r}")
        if "/" in s:
            parts = s.split("/")
            if len(parts) != 2:
                raise ValueError(f"Malformed rational string: {val!r}")
            num = int(parts[0])
            den = int(parts[1])
            if den <= 0:
                raise ValueError(f"Non-positive denominator in rational string: {val!r}")
            return Fraction(num, den)
        return Fraction(int(s), 1)
    raise ValueError(f"Unsupported rational representation: {type(val).__name__}")


def verify_quotient_lp_certificate(cert: Dict[str, Any]) -> Dict[str, Any]:
    """Independently verify an exact rational 1-Lipschitz Quotient LP + Farkas Dual certificate.

    Primal problem over V = {0 .. n-1}:
      maximize   sum_{u in V} mu[u] * h[u]
      subject to h[g] == 0                    for all g in goals
                 0 <= h[u] <= cap[u]          for all u in V (where cap[u] is optional)
                 h[u] - h[v] <= w_e           for all e = (u, v, w_e) in edges

    Dual problem (flow conservation at every non-goal vertex u):
      minimize   sum_{e} w_e * y_e + sum_{u: capped} cap[u] * z_u
      subject to y_e >= 0, z_u >= 0
                 sum_{e out of u} y_e - sum_{e into u} y_e + z_u >= mu[u]   (for u not in goals)
    """
    if not isinstance(cert, dict):
        return {"valid": False, "reason": "cert_not_dict"}

    n = cert.get("num_vertices")
    if isinstance(n, bool) or not isinstance(n, int) or n <= 0:
        return {"valid": False, "reason": "invalid_num_vertices"}

    goals_raw = cert.get("goals", [])
    if not isinstance(goals_raw, list) or not goals_raw:
        return {"valid": False, "reason": "empty_or_invalid_goals"}
    goals = set()
    for g in goals_raw:
        if isinstance(g, bool) or not isinstance(g, int) or g < 0 or g >= n:
            return {"valid": False, "reason": "goal_out_of_range"}
        goals.add(g)

    mu_raw = cert.get("weights_mu", [])
    h_raw = cert.get("primal_h", [])
    if not isinstance(mu_raw, list) or len(mu_raw) != n:
        return {"valid": False, "reason": "weights_mu_length_mismatch"}
    if not isinstance(h_raw, list) or len(h_raw) != n:
        return {"valid": False, "reason": "primal_h_length_mismatch"}

    try:
        mu = [parse_q(x) for x in mu_raw]
        h = [parse_q(x) for x in h_raw]
    except ValueError as exc:
        return {"valid": False, "reason": f"rational_parse_error:{exc}"}

    for u in range(n):
        if mu[u] < 0:
            return {"valid": False, "reason": f"negative_mu_at_{u}"}
        if h[u] < 0:
            return {"valid": False, "reason": f"negative_h_at_{u}"}
        if u in goals and h[u] != 0:
            return {"valid": False, "reason": f"nonzero_goal_h_at_{u}"}

    caps_raw = cert.get("upper_caps")
    has_caps = caps_raw is not None
    caps: List[Fraction] = []
    z_dual: List[Fraction] = [Fraction(0, 1)] * n
    if has_caps:
        z_raw = cert.get("dual_cap_z", [])
        if not isinstance(caps_raw, list) or len(caps_raw) != n:
            return {"valid": False, "reason": "upper_caps_length_mismatch"}
        if not isinstance(z_raw, list) or len(z_raw) != n:
            return {"valid": False, "reason": "dual_cap_z_length_mismatch"}
        try:
            caps = [parse_q(x) for x in caps_raw]
            z_dual = [parse_q(x) for x in z_raw]
        except ValueError as exc:
            return {"valid": False, "reason": f"cap_parse_error:{exc}"}
        for u in range(n):
            if h[u] > caps[u]:
                return {"valid": False, "reason": f"primal_exceeds_cap_at_{u}"}
            if z_dual[u] < 0:
                return {"valid": False, "reason": f"negative_dual_z_at_{u}"}

    edges_raw = cert.get("edges", [])
    y_raw = cert.get("dual_edge_y", [])
    if not isinstance(edges_raw, list) or not isinstance(y_raw, list) or len(edges_raw) != len(y_raw):
        return {"valid": False, "reason": "edges_or_dual_y_length_mismatch"}

    net_out = [Fraction(0, 1) for _ in range(n)]
    dual_edge_obj = Fraction(0, 1)

    for idx, (e_item, y_item) in enumerate(zip(edges_raw, y_raw)):
        if not isinstance(e_item, list) or len(e_item) != 3:
            return {"valid": False, "reason": f"malformed_edge_{idx}"}
        u, v, w_raw = e_item
        if isinstance(u, bool) or isinstance(v, bool) or not isinstance(u, int) or not isinstance(v, int):
            return {"valid": False, "reason": f"non_int_edge_endpoint_{idx}"}
        if u < 0 or u >= n or v < 0 or v >= n:
            return {"valid": False, "reason": f"edge_endpoint_out_of_range_{idx}"}
        try:
            w = parse_q(w_raw)
            ye = parse_q(y_item)
        except ValueError as exc:
            return {"valid": False, "reason": f"edge_rational_error_{idx}:{exc}"}
        if w < 0:
            return {"valid": False, "reason": f"negative_edge_weight_{idx}"}
        if ye < 0:
            return {"valid": False, "reason": f"negative_dual_y_{idx}"}
        if h[u] - h[v] > w:
            return {"valid": False, "reason": f"lipschitz_violation_edge_{idx}:{u}->{v}"}
        net_out[u] += ye
        net_out[v] -= ye
        dual_edge_obj += w * ye

    for u in range(n):
        if u in goals:
            continue
        lhs = net_out[u] + z_dual[u]
        if lhs < mu[u]:
            return {"valid": False, "reason": f"dual_flow_conservation_failed_at_{u}"}

    primal_obj = sum((mu[u] * h[u] for u in range(n)), Fraction(0, 1))
    dual_cap_obj = sum((caps[u] * z_dual[u] for u in range(n)), Fraction(0, 1)) if has_caps else Fraction(0, 1)
    dual_obj = dual_edge_obj + dual_cap_obj

    if primal_obj != dual_obj:
        return {
            "valid": False,
            "reason": f"strong_duality_gap_nonzero:{primal_obj}!={dual_obj}",
        }

    if "primal_objective" not in cert or "dual_objective" not in cert:
        return {"valid": False, "reason": "missing_claimed_objectives"}
    try:
        claimed_primal = parse_q(cert["primal_objective"])
        claimed_dual = parse_q(cert["dual_objective"])
    except ValueError as exc:
        return {"valid": False, "reason": f"claimed_objective_parse_error:{exc}"}
    if primal_obj != claimed_primal:
        return {
            "valid": False,
            "reason": f"claimed_primal_objective_mismatch:{primal_obj}!={claimed_primal}",
        }
    if dual_obj != claimed_dual:
        return {
            "valid": False,
            "reason": f"claimed_dual_objective_mismatch:{dual_obj}!={claimed_dual}",
        }

    # Optional zero-self-loop monotone deficit check (`Mcproof.Spec.zeroSelfLoop_deficit_composition`)
    deficit_spec = cert.get("zero_self_loop_deficit")
    if deficit_spec is not None:
        if not isinstance(deficit_spec, dict):
            return {"valid": False, "reason": "invalid_deficit_spec_type"}
        phi_raw = deficit_spec.get("phi_values")
        abs_edges = deficit_spec.get("abstract_deficit_edges")
        if not isinstance(phi_raw, list) or not phi_raw:
            return {"valid": False, "reason": "invalid_deficit_phi_values"}
        if not isinstance(abs_edges, list) or not abs_edges:
            return {"valid": False, "reason": "empty_or_invalid_deficit_edges"}
        try:
            phi = [parse_q(x) for x in phi_raw]
        except ValueError as exc:
            return {"valid": False, "reason": f"deficit_phi_parse_error:{exc}"}
        if any(p < 0 for p in phi):
            return {"valid": False, "reason": "negative_deficit_phi"}
        m_phi = len(phi)
        goal_phi_indices = deficit_spec.get("goal_phi_indices")
        if not isinstance(goal_phi_indices, list) or not goal_phi_indices:
            return {"valid": False, "reason": "empty_or_invalid_goal_phi_indices"}
        for gi in goal_phi_indices:
            if isinstance(gi, bool) or not isinstance(gi, int) or gi < 0 or gi >= m_phi or phi[gi] != 0:
                return {"valid": False, "reason": "nonzero_or_invalid_goal_phi"}
        for a_idx, ae in enumerate(abs_edges):
            if not isinstance(ae, dict):
                return {"valid": False, "reason": f"malformed_deficit_edge_{a_idx}"}
            pu = ae.get("phi_u")
            pv = ae.get("phi_v")
            is_self = ae.get("quotient_self_loop")
            cost_raw = ae.get("concrete_cost", 1)
            if (
                isinstance(pu, bool)
                or isinstance(pv, bool)
                or not isinstance(pu, int)
                or not isinstance(pv, int)
                or pu < 0
                or pu >= m_phi
                or pv < 0
                or pv >= m_phi
                or not isinstance(is_self, bool)
            ):
                return {"valid": False, "reason": f"invalid_deficit_edge_fields_{a_idx}"}
            try:
                cost = parse_q(cost_raw)
            except ValueError as exc:
                return {"valid": False, "reason": f"deficit_edge_cost_parse_error_{a_idx}:{exc}"}
            if cost < 0:
                return {"valid": False, "reason": f"negative_deficit_edge_cost_{a_idx}"}
            d_phi = phi[pu] - phi[pv]
            if is_self:
                if d_phi > cost:
                    return {"valid": False, "reason": f"self_loop_deficit_drop_exceeds_cost_{a_idx}"}
            else:
                if d_phi > 0:
                    return {"valid": False, "reason": f"non_self_loop_deficit_decreased_{a_idx}"}

    return {
        "valid": True,
        "reason": "ok",
        "num_vertices": n,
        "num_edges": len(edges_raw),
        "primal_objective": f"{primal_obj.numerator}/{primal_obj.denominator}" if primal_obj.denominator != 1 else str(primal_obj.numerator),
        "dual_objective": f"{dual_obj.numerator}/{dual_obj.denominator}" if dual_obj.denominator != 1 else str(dual_obj.numerator),
    }


def verify_certificate_bundle_file(path: Path) -> Dict[str, Any]:
    data = loads_exact_json(path.read_text(encoding="utf-8"))
    if not isinstance(data, dict) or "instances" not in data:
        return {"valid": False, "reason": "missing_instances_list"}
    instances = data["instances"]
    if not isinstance(instances, list) or not instances:
        return {"valid": False, "reason": "empty_instances_list"}
    results = []
    seen_names = set()
    for idx, inst in enumerate(instances):
        if not isinstance(inst, dict):
            return {"valid": False, "reason": f"instance_{idx}_not_dict"}
        name = inst.get("name")
        if not isinstance(name, str) or not name or name in seen_names:
            return {"valid": False, "reason": f"invalid_or_duplicate_instance_name_at_{idx}"}
        seen_names.add(name)
        res = verify_quotient_lp_certificate(inst)
        if not res["valid"]:
            return {"valid": False, "reason": f"instance_{name}_failed:{res['reason']}"}
        results.append({"name": name, **res})
    return {"valid": True, "instances_verified": len(results), "results": results}


def main() -> int:
    cert_path = Path(__file__).resolve().parent / "certificate.json"
    res = verify_certificate_bundle_file(cert_path)
    print(json.dumps(res, indent=2))
    if not res["valid"]:
        raise SystemExit(1)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
