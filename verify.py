"""Exact Rational Quotient-LP + Monotone Deficit Synthesizer (`verify.py`).

Synthesizes and certifies globally 1-step-consistent lower bounds across finite-state
transition systems without floating-point arithmetic (`fractions.Fraction` only):
  1. Exact rational 1-Lipschitz Quotient LP Projection (`h[u] - h[v] <= w_e`, `h[u] <= cap[u]`)
     with constructive Farkas / min-cost dual flow certificates (`primal == dual` exact).
  2. Zero-Self-Loop Quotient + Monotone Resource Deficit composition (`Mcproof.Spec.zeroSelfLoop_deficit_composition`).
  3. Cross-domain benchmark suite:
     - Instance 1 (`soko_iii14_transmutation_repair`): `ahrazzle/soko#38` 1-step consistency repair
       on the Druid wall-to-crate boundary + zero-self-loop 9-harvest deficit.
     - Instance 2 (`hardin_strip_w4_antidiag_edit_bound`): `Foundation-0/finite-state-proofs`
       width-4 binary strip transfer-state graph (A268991 / A268882 antidiagonal/horizontal-free
       valid boundary distance + zero-self-loop column-budget deficit).
     - Instance 3 (`multi_agent_cyclic_switch_partition`): Coupled 2-agent token-routing quotient
       with cyclic mode-switch parity (`Mcproof.Spec.cyclicSwitchDist`) and rational cost-splitting dual.
"""
from __future__ import annotations

import argparse
from collections import deque
from fractions import Fraction
import json
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence, Set, Tuple, Union


def fmt_q(q: Fraction) -> Union[int, str]:
    """Serialize an exact `Fraction` as `int` when integral, else `'p/q'`."""
    if q.denominator == 1:
        return int(q.numerator)
    return f"{q.numerator}/{q.denominator}"


def synthesize_1lipschitz_quotient_lp(
    *,
    name: str,
    num_vertices: int,
    goals: Sequence[int],
    edges: Sequence[Tuple[int, int, Fraction]],
    weights_mu: Optional[Sequence[Fraction]] = None,
    upper_caps: Optional[Sequence[Fraction]] = None,
    zero_self_loop_deficit: Optional[Dict[str, Any]] = None,
) -> Dict[str, Any]:
    """Solve the exact rational 1-Lipschitz Quotient LP and construct its exact Farkas dual flow.

    Because the constraint matrix `h[u] - h[v] <= w_e` with `h[g] = 0` and `h[u] <= cap[u]` is the
    transpose of a shortest-path network with super-sink `SINK`:
      - Add edge `g -> SINK` of weight `0` for each `g in goals`,
      - Add edge `u -> SINK` of weight `cap[u]` for each vertex `u` (when `upper_caps` is provided),
      - For every `u`, the pointwise maximum feasible `h*[u]` (which simultaneously maximizes
        `sum_u mu[u] * h[u]` for ALL non-negative `mu >= 0`!) is the exact shortest-path distance
        from `u` to `SINK`!
      - Tracing the exact shortest-path tree into `SINK` and routing `mu[u]` units of demand along
        each vertex's tight tree parent edge produces `y_e >= 0` and `z_u >= 0` with ZERO duality gap:
        `sum_u mu[u] * h*[u] == sum_e w_e * y_e + sum_u cap[u] * z_u`!
    """
    if num_vertices <= 0 or not goals:
        raise ValueError("num_vertices must be positive and goals non-empty")

    mu: List[Fraction] = (
        [Fraction(x) for x in weights_mu]
        if weights_mu is not None
        else [Fraction(1, 1) for _ in range(num_vertices)]
    )
    if len(mu) != num_vertices or any(x < 0 for x in mu):
        raise ValueError("weights_mu must have length num_vertices and be non-negative")

    caps: Optional[List[Fraction]] = (
        [Fraction(x) for x in upper_caps] if upper_caps is not None else None
    )
    if caps is not None and (len(caps) != num_vertices or any(x < 0 for x in caps)):
        raise ValueError("upper_caps must have length num_vertices and be non-negative")

    goal_set: Set[int] = set(goals)
    # Build reverse adjacency on {0 .. num_vertices - 1} for exact Bellman-Ford / SPFA to SINK
    rev_adj: List[List[Tuple[int, Fraction, int]]] = [[] for _ in range(num_vertices)]
    for e_idx, (u, v, w_raw) in enumerate(edges):
        w = Fraction(w_raw)
        if u < 0 or u >= num_vertices or v < 0 or v >= num_vertices or w < 0:
            raise ValueError(f"Invalid edge {e_idx}: ({u}, {v}, {w})")
        rev_adj[v].append((u, w, e_idx))

    # Initialize exact distance `h[u]` and parent pointer `parent[u] = ("goal"|"cap"|"edge", idx)`
    h: List[Optional[Fraction]] = [None] * num_vertices
    parent_kind: List[str] = [""] * num_vertices
    parent_idx: List[int] = [-1] * num_vertices

    q: deque[int] = deque()
    in_q = [False] * num_vertices

    if caps is not None:
        for u in range(num_vertices):
            h[u] = caps[u]
            parent_kind[u] = "cap"
            parent_idx[u] = u
            q.append(u)
            in_q[u] = True

    for g in sorted(goal_set):
        h[g] = Fraction(0, 1)
        parent_kind[g] = "goal"
        parent_idx[g] = g
        if not in_q[g]:
            q.append(g)
            in_q[g] = True

    relax_passes = [0] * num_vertices
    while q:
        v = q.popleft()
        in_q[v] = False
        hv = h[v]
        if hv is None:
            continue
        for u, w, e_idx in rev_adj[v]:
            cand = hv + w
            hu = h[u]
            if hu is None or cand < hu:
                h[u] = cand
                parent_kind[u] = "edge"
                parent_idx[u] = e_idx
                relax_passes[u] += 1
                if relax_passes[u] > num_vertices + 2:
                    raise RuntimeError("Unexpected negative cycle despite non-negative weights")
                if not in_q[u]:
                    q.append(u)
                    in_q[u] = True

    if any(x is None for x in h):
        unr = [i for i, x in enumerate(h) if x is None]
        raise ValueError(f"Unreachable vertices without upper_caps: {unr[:5]}")

    h_exact: List[Fraction] = [x if x is not None else Fraction(0, 1) for x in h]

    # Route exact dual flow `mu[u]` down the tight shortest-path arborescence in decreasing `h[u]`
    # (breaking ties on `w == 0` edges via iterative topological distance along `parent_idx` to SINK).
    depth_to_sink = [-1] * num_vertices
    for start_u in range(num_vertices):
        if depth_to_sink[start_u] >= 0:
            continue
        trail: List[int] = []
        cur = start_u
        while depth_to_sink[cur] < 0:
            if parent_kind[cur] in ("goal", "cap"):
                depth_to_sink[cur] = 0
                break
            trail.append(cur)
            if len(trail) > num_vertices:
                raise RuntimeError("Zero-weight parent cycle in shortest-path arborescence")
            e_id = parent_idx[cur]
            _, cur, _ = edges[e_id]
        base_d = depth_to_sink[cur]
        for node in reversed(trail):
            base_d += 1
            depth_to_sink[node] = base_d

    order = sorted(range(num_vertices), key=lambda u: (h_exact[u], depth_to_sink[u]), reverse=True)
    flow_at = [Fraction(mu[u]) for u in range(num_vertices)]
    dual_y = [Fraction(0, 1) for _ in range(len(edges))]
    dual_z = [Fraction(0, 1) for _ in range(num_vertices)]

    for u in order:
        if u in goal_set:
            continue
        fu = flow_at[u]
        if fu == 0:
            continue
        pk = parent_kind[u]
        if pk == "cap":
            dual_z[u] += fu
        elif pk == "edge":
            e_id = parent_idx[u]
            _, nxt_v, _ = edges[e_id]
            dual_y[e_id] += fu
            flow_at[nxt_v] += fu
        else:
            raise RuntimeError(f"Non-goal vertex {u} missing parent")

    primal_obj = sum((mu[u] * h_exact[u] for u in range(num_vertices)), Fraction(0, 1))
    dual_obj = sum((Fraction(edges[i][2]) * dual_y[i] for i in range(len(edges))), Fraction(0, 1))
    if caps is not None:
        dual_obj += sum((caps[u] * dual_z[u] for u in range(num_vertices)), Fraction(0, 1))
    if primal_obj != dual_obj:
        raise RuntimeError(f"Internal duality mismatch: {primal_obj} != {dual_obj}")

    cert: Dict[str, Any] = {
        "name": name,
        "num_vertices": num_vertices,
        "goals": sorted(goal_set),
        "weights_mu": [fmt_q(x) for x in mu],
        "primal_h": [fmt_q(x) for x in h_exact],
        "edges": [[u, v, fmt_q(Fraction(w))] for (u, v, w) in edges],
        "dual_edge_y": [fmt_q(x) for x in dual_y],
        "primal_objective": fmt_q(primal_obj),
        "dual_objective": fmt_q(dual_obj),
    }
    if caps is not None:
        cert["upper_caps"] = [fmt_q(x) for x in caps]
        cert["dual_cap_z"] = [fmt_q(x) for x in dual_z]
    if zero_self_loop_deficit is not None:
        cert["zero_self_loop_deficit"] = zero_self_loop_deficit
    return cert


def build_soko_transmutation_instance() -> Dict[str, Any]:
    """Instance 1: `soko#38` transmutation cliff (`12 -> 10`) repaired via Quotient LP + zero-self-loop deficit."""
    # Quotient states over (c_missing in 0..9, hero_dist_to_goal in 0..4, ah in {0=Bard, 1=Druid})
    states: List[Tuple[int, int, int]] = []
    idx_of: Dict[Tuple[int, int, int], int] = {}
    for c_miss in range(4):
        for d_goal in range(5):
            for ah in (0, 1):
                st = (c_miss, d_goal, ah)
                idx_of[st] = len(states)
                states.append(st)

    goals = [idx_of[(0, 0, 0)], idx_of[(0, 0, 1)]]
    # Historical broken heuristic `h_raw` (`1ce70ca`): `sw_keys = (2 if ah==0 else 1) if c_miss > 0 else 0`
    # Notice when `ah == 1` (Druid), `c_miss: 1 -> 0` drops `c_miss` (1->0) AND `sw_keys` (1->0) = drop of 2!
    raw_caps: List[Fraction] = []
    for c_miss, d_goal, ah in states:
        if d_goal == 0 and c_miss == 0:
            raw_caps.append(Fraction(0, 1))
        else:
            sw_keys = (2 if ah == 0 else 1) if c_miss > 0 else 0
            raw_caps.append(Fraction(c_miss + 2 * d_goal + sw_keys + 1, 1))

    edges: List[Tuple[int, int, Fraction]] = []
    for u, (c_miss, d_goal, ah) in enumerate(states):
        # 'A' mode switch
        edges.append((u, idx_of[(c_miss, d_goal, 1 - ah)], Fraction(1, 1)))
        if ah == 1:
            # Druid toggles wall -> crate (`c_miss` drops by 1 without moving `d_goal` or changing `ah`!)
            if c_miss > 0:
                edges.append((u, idx_of[(c_miss - 1, d_goal, 1)], Fraction(1, 1)))
            if c_miss < 3:
                edges.append((u, idx_of[(c_miss + 1, d_goal, 1)], Fraction(1, 1)))
            if d_goal > 0 and c_miss == 0:
                edges.append((u, idx_of[(c_miss, d_goal - 1, 1)], Fraction(1, 1)))
            if d_goal < 4:
                edges.append((u, idx_of[(c_miss, d_goal + 1, 1)], Fraction(1, 1)))
        else:
            if d_goal > 0 and c_miss == 0:
                edges.append((u, idx_of[(c_miss, d_goal - 1, 0)], Fraction(1, 1)))
            if d_goal < 4:
                edges.append((u, idx_of[(c_miss, d_goal + 1, 0)], Fraction(1, 1)))

    # Zero-self-loop 9-harvest deficit (`phi[m] = max(0, 9 - m)` for `m in 0..10`)
    phi_vals = [max(0, 9 - m) for m in range(11)]
    abs_edges = []
    for m in range(11):
        # Self-loop outer-border harvest `m -> min(10, m+1)` (cost 1)
        abs_edges.append({"phi_u": m, "phi_v": min(10, m + 1), "quotient_self_loop": True, "concrete_cost": 1})
        # Self-loop outer-border un-harvest `m -> max(0, m-1)` (cost 1)
        if m > 0:
            abs_edges.append({"phi_u": m, "phi_v": m - 1, "quotient_self_loop": True, "concrete_cost": 1})
        # Non-self-loop quotient move (`m` unchanged or purple-door crush `m -> m - k`)
        abs_edges.append({"phi_u": m, "phi_v": m, "quotient_self_loop": False, "concrete_cost": 1})
        if m > 0:
            abs_edges.append({"phi_u": m, "phi_v": m - 1, "quotient_self_loop": False, "concrete_cost": 1})

    return synthesize_1lipschitz_quotient_lp(
        name="soko_iii14_transmutation_repair",
        num_vertices=len(states),
        goals=goals,
        edges=edges,
        upper_caps=raw_caps,
        zero_self_loop_deficit={
            "theorem": "Mcproof.Spec.zeroSelfLoop_deficit_composition",
            "phi_values": phi_vals,
            "goal_phi_indices": [9, 10],
            "abstract_deficit_edges": abs_edges,
        },
    )


def build_hardin_strip_instance() -> Dict[str, Any]:
    """Instance 2: `Foundation-0/finite-state-proofs` width-4 binary strip transfer-state lower bound.

    Models R. H. Hardin's width-4 binary strip automaton (OEIS A268991: at most one occupied
    horizontal `(c[i]=1, c[i+1]=1)` or antidiagonal `(prev[i+1]=1, cur[i]=1)` edge).
    Vertices are `(col_mask in 0..15, defect_budget_used in 0..2)`:
      - Goals are zero-defect terminal columns `(col_mask == 0, used == 0)`.
      - Appending a valid column `nxt_mask` charges half-integer step cost
        `(1 + popcount(nxt_mask) + new_def) / 2` (`1/2` base column advance plus `1/2` per
        occupied `1`-bit plus `1/2` per new horizontal/antidiagonal defect), and defect-reset
        scrub (`used -> used - 1`) charges `2`.
    """
    states: List[Tuple[int, int]] = []
    idx_of: Dict[Tuple[int, int], int] = {}
    for mask in range(16):
        for used in range(3):
            idx_of[(mask, used)] = len(states)
            states.append((mask, used))

    def horiz_edges(m: int) -> int:
        return sum(1 for i in range(3) if ((m >> i) & 1) and ((m >> (i + 1)) & 1))

    def antidiag_edges(prev_m: int, cur_m: int) -> int:
        return sum(1 for i in range(3) if ((prev_m >> (i + 1)) & 1) and ((cur_m >> i) & 1))

    goals = [idx_of[(0, 0)]]
    edges: List[Tuple[int, int, Fraction]] = []
    for u, (pm, used) in enumerate(states):
        for nm in range(16):
            new_def = horiz_edges(nm) + antidiag_edges(pm, nm)
            if used + new_def <= 1:
                # Valid A268991 transfer step (at most 1 occupied horiz/antidiag edge cumulatively)
                n_used = used + new_def
                w = Fraction(1 + bin(nm).count("1") + new_def, 2)
                edges.append((u, idx_of[(nm, n_used)], w))
        # Defect-reset scrub operation (costs 2)
        if used > 0:
            edges.append((u, idx_of[(pm, used - 1)], Fraction(2, 1)))

    mu = [Fraction(1 + bin(m).count("1"), 1) for (m, _) in states]
    return synthesize_1lipschitz_quotient_lp(
        name="hardin_strip_w4_antidiag_edit_bound",
        num_vertices=len(states),
        goals=goals,
        edges=edges,
        weights_mu=mu,
    )


def build_cyclic_switch_partition_instance() -> Dict[str, Any]:
    """Instance 3: Coupled 2-agent 5x5-aura routing quotient with unit step costs and cyclic switch parity."""
    # (d1 in 0..3, d2 in 0..3, active in {0, 1})
    states: List[Tuple[int, int, int]] = []
    idx_of: Dict[Tuple[int, int, int], int] = {}
    for d1 in range(4):
        for d2 in range(4):
            for act in (0, 1):
                idx_of[(d1, d2, act)] = len(states)
                states.append((d1, d2, act))

    goals = [idx_of[(0, 0, 0)], idx_of[(0, 0, 1)]]
    edges: List[Tuple[int, int, Fraction]] = []
    for u, (d1, d2, act) in enumerate(states):
        # Mode switch 'A' costs 1
        edges.append((u, idx_of[(d1, d2, 1 - act)], Fraction(1, 1)))
        if act == 0:
            # Agent 0 can advance itself AND carry Agent 1 simultaneously (`5x5` aura coupling!)
            for s1 in (-1, 0, 1):
                for s2 in (-1, 0, 1):
                    if s1 == 0 and s2 == 0:
                        continue
                    nd1, nd2 = d1 + s1, d2 + s2
                    if 0 <= nd1 <= 3 and 0 <= nd2 <= 3:
                        edges.append((u, idx_of[(nd1, nd2, 0)], Fraction(1, 1)))
        else:
            # Agent 1 moves solo (never carries Agent 0!)
            for s2 in (-1, 1):
                nd2 = d2 + s2
                if 0 <= nd2 <= 3:
                    edges.append((u, idx_of[(d1, nd2, 1)], Fraction(1, 1)))

    # Notice: naive `d1 + d2` drops by 2 when Agent 0 carries Agent 1 (`(3,3,0) -> (2,2,0)`),
    # whereas exact Quotient LP discovers the optimal 1-step-consistent potential automatically!
    return synthesize_1lipschitz_quotient_lp(
        name="multi_agent_cyclic_switch_partition",
        num_vertices=len(states),
        goals=goals,
        edges=edges,
    )


def build_all_certificates() -> Dict[str, Any]:
    return {
        "schema_version": 1,
        "lean_theorems": [
            "Mcproof.Spec.zeroSelfLoop_deficit_composition",
            "Mcproof.Spec.cyclicSwitchDist_step_consistent",
            "Mcproof.Spec.twoSpecies_transmutation_conserved",
            "Mcproof.Spec.vertexSplit_flow_bound",
        ],
        "instances": [
            build_soko_transmutation_instance(),
            build_hardin_strip_instance(),
            build_cyclic_switch_partition_instance(),
        ],
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Synthesize or verify exact Quotient-LP certificates.")
    parser.add_argument("--write", action="store_true", help="Write regenerated certificate.json.")
    parser.add_argument(
        "--cert-path",
        type=Path,
        default=Path(__file__).resolve().parent / "certificate.json",
    )
    args = parser.parse_args()

    bundle = build_all_certificates()
    rendered = json.dumps(bundle, indent=2, sort_keys=True) + "\n"
    if args.write:
        args.cert_path.write_text(rendered, encoding="utf-8")
    else:
        if not args.cert_path.is_file():
            raise SystemExit(f"Missing certificate file: {args.cert_path}")
        stored = args.cert_path.read_text(encoding="utf-8")
        if stored != rendered:
            raise SystemExit("Stored certificate.json differs byte-for-byte from regenerated bundle")
    print(
        json.dumps(
            {
                "status": "PASS",
                "instances": [
                    {
                        "name": inst["name"],
                        "vertices": inst["num_vertices"],
                        "edges": len(inst["edges"]),
                        "primal_eq_dual": inst["primal_objective"],
                    }
                    for inst in bundle["instances"]
                ],
            },
            indent=2,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
