"""Rounding direction for cost partitions: floor keeps shares valid, old potentials go stale.

Three statements are checked on the three instances in certificate.json, for D = 10, 100, 10000:

  A. Flooring each share of an operator cost to the grid 1/D keeps the sum of shares at or below the
     operator cost.
  B. Potentials computed before rounding are rejected by the repository's independent checker on the
     rounded costs. Potentials recomputed with the repository's synthesizer on the rounded costs are
     accepted.
  C. At every vertex, recomputing on the rounded costs lowers a share's potential by at most
     (edges on a shortest path after rounding) / D.

Three more statements cover signed shares, as made by a reduced-cost tower (tests 09 to 11):

  D. Flooring the potentials of a layer after the fact can leave a negative residual cost.
  E. Flooring signed shares can create a negative cycle among the shares.
  F. Flooring each layer's input costs before solving the layer keeps every residual non-negative
     and the summed potentials consistent. Costs already on the grid need no rounding at all.

Each statement has a control that must fail. Plain assertions are written as unittest methods, so
`python3 -O` does not strip them.
"""
from __future__ import annotations

import copy
import heapq
import json
import math
import sys
from fractions import Fraction
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from verify import fmt_q, synthesize_1lipschitz_quotient_lp
from verify_independent import verify_quotient_lp_certificate

CERT_PATH = Path(__file__).resolve().parent.parent / "certificate.json"
GRIDS = (10, 100, 10000)
SHARES = 3


def floor_grid(x: Fraction, d: int) -> Fraction:
    return Fraction(math.floor(x * d), d)


def ceil_grid(x: Fraction, d: int) -> Fraction:
    return Fraction(-math.floor(-x * d), d)


def load_instances() -> list:
    cert = json.loads(CERT_PATH.read_text(encoding="utf-8"))
    out = []
    for inst in cert["instances"]:
        edges = [(u, v, Fraction(str(w))) for u, v, w in inst["edges"]]
        out.append((inst["name"], inst["num_vertices"], inst["goals"], edges))
    return out


def split_costs(kind: str, costs: list) -> list:
    """Return SHARES lists of shares, one list per share, each edge cost split exactly."""
    out = [[] for _ in range(SHARES)]
    for i, c in enumerate(costs):
        if kind == "thirds":
            a = [Fraction(1, 3)] * 3
        else:
            cuts = sorted(((3 * i) % 8, (5 * i + 1) % 8))
            a = [Fraction(cuts[0], 7), Fraction(cuts[1] - cuts[0], 7), Fraction(7 - cuts[1], 7)]
        for k in range(SHARES):
            out[k].append(c * a[k])
        if sum(out[k][-1] for k in range(SHARES)) != c:
            raise AssertionError("split does not sum to the cost")
    return out


def over_budget_edges(costs: list, shares: list) -> list:
    """Edges where the shares are negative or sum to more than the operator cost."""
    bad = []
    for e, c in enumerate(costs):
        if any(s[e] < 0 for s in shares) or sum(s[e] for s in shares) > c:
            bad.append(e)
    return bad


def dist_and_hops(n: int, goals: list, edges: list, cost: list):
    """Distance to the goal set and fewest edges among shortest paths. Own code, no repo imports."""
    if any(c < 0 for c in cost):
        raise AssertionError("negative edge cost")
    radj = [[] for _ in range(n)]
    for e, (u, v, _) in enumerate(edges):
        radj[v].append((u, e))
    best = [None] * n
    pq = []
    for g in goals:
        best[g] = (Fraction(0), 0)
        heapq.heappush(pq, (Fraction(0), 0, g))
    while pq:
        d, h, v = heapq.heappop(pq)
        if best[v] != (d, h):
            continue
        for u, e in radj[v]:
            cand = (d + cost[e], h + 1)
            if best[u] is None or cand < best[u]:
                best[u] = cand
                heapq.heappush(pq, (cand[0], cand[1], u))
    if any(b is None for b in best):
        raise AssertionError("unreachable vertex")
    return [b[0] for b in best], [b[1] for b in best]


def share_cert(name: str, n: int, goals: list, edges: list, cost: list) -> dict:
    return synthesize_1lipschitz_quotient_lp(
        name=name, num_vertices=n, goals=goals,
        edges=[(u, v, cost[e]) for e, (u, v, _) in enumerate(edges)],
    )


def with_costs(cert: dict, cost: list) -> dict:
    """Copy of a certificate whose edge costs are replaced; potentials and duals stay as they were."""
    out = copy.deepcopy(cert)
    out["edges"] = [[u, v, fmt_q(cost[e])] for e, (u, v, _) in enumerate(cert["edges"])]
    return out


def potentials(cert: dict) -> list:
    return [Fraction(str(x)) for x in cert["primal_h"]]


def loss_bound_violations(pre: list, post: list, hops: list, d: int, scale: Fraction) -> int:
    """Vertices where the loss exceeds scale * hops / d."""
    return sum(1 for v in range(len(pre)) if pre[v] - post[v] > scale * Fraction(hops[v], d))


# ---- signed shares: a reduced-cost tower (tests 09 to 11) -------------------------------------------

def quotient_potential(n: int, goals: list, edges: list, cost: list, pi: list) -> list:
    """Distance to the goal classes in the quotient graph. Crossing edges only, minimum cost per pair."""
    best = {}
    for e, (u, v, _) in enumerate(edges):
        a, b = pi[u], pi[v]
        if a != b and ((a, b) not in best or cost[e] < best[(a, b)]):
            best[(a, b)] = cost[e]
    pairs = sorted(best)
    qn = max(pi) + 1
    qgoals = sorted({pi[g] for g in goals})
    return dist_and_hops(qn, qgoals, [(a, b, None) for a, b in pairs], [best[p] for p in pairs])[0]


def peel(n: int, goals: list, edges: list, quotients: list, rule: str, d: int) -> dict:
    """Peel the quotients in order. Each layer solves its quotient on the residual cost, then subtracts
    its share (h(pi u) - h(pi v)) from every edge. rule is one of
      exact       : potentials as solved,
      floor_pot   : potentials floored to the grid after solving,
      floor_input : the layer's input costs floored before solving, shares taken from the potentials.
    Returns the potentials per layer, the summed potential, the final residual, and the first negative
    residual found (edge index, value) or None."""
    resid = [e[2] for e in edges]
    total = [Fraction(0)] * n
    layers = []
    for pi in quotients:
        inp = [floor_grid(x, d) for x in resid] if rule == "floor_input" else resid
        h = quotient_potential(n, goals, edges, inp, pi)
        if rule == "floor_pot":
            h = [floor_grid(x, d) for x in h]
        layers.append(h)
        nxt = [resid[e] + h[pi[v]] - h[pi[u]] for e, (u, v, _) in enumerate(edges)]
        bad = [(e, x) for e, x in enumerate(nxt) if x < 0]
        if bad:
            return {"layers": layers, "total": None, "resid": nxt, "first_negative": bad[0]}
        resid = nxt
        total = [total[s] + h[pi[s]] for s in range(n)]
    return {"layers": layers, "total": total, "resid": resid, "first_negative": None}


def consistent(n: int, goals: list, edges: list, h: list) -> bool:
    return all(h[u] - h[v] <= w for u, v, w in edges) and all(h[g] == 0 for g in goals)


def has_negative_cycle(n: int, edges: list, cost: list) -> bool:
    """Bellman-Ford from a virtual source: still improving after n rounds means a negative cycle."""
    dist = [Fraction(0)] * n
    for _ in range(n + 1):
        changed = False
        for e, (u, v, _) in enumerate(edges):
            if dist[v] + cost[e] < dist[u]:
                dist[u] = dist[v] + cost[e]
                changed = True
        if not changed:
            return False
    return True


def small_graphs(count: int, denom: int = 6):
    """Deterministic small graphs on 5 vertices, goal 0, costs in multiples of 1/denom. Every vertex reaches the goal."""
    state = 12345
    def nxt(m: int) -> int:
        nonlocal state
        state = (state * 1103515245 + 12345) % (2 ** 31)
        return (state >> 8) % m
    for _ in range(count):
        edges = []
        for v in range(1, 5):
            edges.append((v, nxt(v), Fraction(1 + nxt(11), denom)))
        for _ in range(5):
            u, v = 1 + nxt(4), nxt(5)
            if u != v:
                edges.append((u, v, Fraction(1 + nxt(11), denom)))
        yield edges


class TestFloorRounding(unittest.TestCase):
    def runs(self):
        for name, n, goals, edges in load_instances():
            costs = [e[2] for e in edges]
            for kind in ("thirds", "sevenths"):
                for d in GRIDS:
                    yield name, n, goals, edges, costs, kind, d

    def test_01_floored_shares_stay_within_operator_cost(self) -> None:
        count = 0
        for name, n, goals, edges, costs, kind, d in self.runs():
            shares = split_costs(kind, costs)
            self.assertEqual(over_budget_edges(costs, shares), [])
            floored = [[floor_grid(x, d) for x in s] for s in shares]
            self.assertEqual(over_budget_edges(costs, floored), [], msg=f"{name} {kind} D={d}")
            count += 1
        self.assertEqual(count, 18)

    def test_02_stale_potentials_rejected_and_recomputed_accepted(self) -> None:
        for name, n, goals, edges, costs, kind, d in self.runs():
            shares = split_costs(kind, costs)
            floored = [[floor_grid(x, d) for x in s] for s in shares]
            rejected = 0
            for k in range(SHARES):
                pre = share_cert(name, n, goals, edges, shares[k])
                self.assertTrue(verify_quotient_lp_certificate(pre)["valid"])
                stale = verify_quotient_lp_certificate(with_costs(pre, floored[k]))
                if not stale["valid"]:
                    self.assertTrue(stale["reason"].startswith("lipschitz_violation_edge_"), msg=str(stale))
                    rejected += 1
                post = share_cert(name, n, goals, edges, floored[k])
                res = verify_quotient_lp_certificate(post)
                self.assertTrue(res["valid"], msg=f"{name} {kind} D={d} share {k}: {res}")
                # the synthesizer agrees with separate exact Dijkstra code
                self.assertEqual(potentials(post), dist_and_hops(n, goals, edges, floored[k])[0])
            self.assertGreater(rejected, 0, msg=f"no stale share rejected: {name} {kind} D={d}")

    def test_03_loss_is_at_most_hops_over_d(self) -> None:
        worst = Fraction(0)
        for name, n, goals, edges, costs, kind, d in self.runs():
            shares = split_costs(kind, costs)
            for k in range(SHARES):
                fl = [floor_grid(x, d) for x in shares[k]]
                pre, _ = dist_and_hops(n, goals, edges, shares[k])
                post, hops = dist_and_hops(n, goals, edges, fl)
                self.assertTrue(all(pre[v] >= post[v] for v in range(n)))
                self.assertEqual(loss_bound_violations(pre, post, hops, d, Fraction(1)), 0,
                                 msg=f"{name} {kind} D={d} share {k}")
                for v in range(n):
                    if hops[v]:
                        worst = max(worst, (pre[v] - post[v]) * d / hops[v])
        # The largest ratio over the 18 runs, quoted in PROOF.md 4.3. It is below 1, as the proof says.
        self.assertEqual(worst, Fraction(6, 7))

    def test_04_must_fail_ceiling_breaks_the_share_budget(self) -> None:
        name, n, goals, edges = load_instances()[0]
        costs = [e[2] for e in edges]
        shares = split_costs("thirds", costs)
        ceiled = [[ceil_grid(x, 10) for x in s] for s in shares]
        self.assertGreater(len(over_budget_edges(costs, ceiled)), 0)

    def test_05_must_fail_stale_potentials_on_the_smallest_graph(self) -> None:
        # One edge 1 -> 0 of cost 1/2, grid step 1. The floored cost is 0, the old potential at 1 is 1/2.
        edges = [(1, 0, Fraction(1, 2))]
        pre = synthesize_1lipschitz_quotient_lp(name="one_edge", num_vertices=2, goals=[0], edges=edges)
        self.assertTrue(verify_quotient_lp_certificate(pre)["valid"])
        self.assertEqual(potentials(pre), [0, Fraction(1, 2)])
        stale = verify_quotient_lp_certificate(with_costs(pre, [floor_grid(Fraction(1, 2), 1)]))
        self.assertFalse(stale["valid"])
        self.assertEqual(stale["reason"], "lipschitz_violation_edge_0:1->0")
        post = synthesize_1lipschitz_quotient_lp(
            name="one_edge", num_vertices=2, goals=[0], edges=[(1, 0, Fraction(0))])
        self.assertTrue(verify_quotient_lp_certificate(post)["valid"])
        self.assertEqual(potentials(post), [0, 0])

    def test_06_must_fail_potential_raised_by_one_millionth(self) -> None:
        name, n, goals, edges = load_instances()[0]
        costs = [e[2] for e in edges]
        shares = split_costs("thirds", costs)
        fl = [floor_grid(x, 10) for x in shares[0]]
        post = share_cert(name, n, goals, edges, fl)
        self.assertTrue(verify_quotient_lp_certificate(post)["valid"])
        h = potentials(post)
        tight = [(u, v) for e, (u, v, _) in enumerate(edges) if u not in goals and h[u] - h[v] == fl[e]]
        self.assertTrue(tight)
        u = tight[0][0]
        bad = copy.deepcopy(post)
        bad["primal_h"][u] = fmt_q(h[u] + Fraction(1, 10 ** 6))
        res = verify_quotient_lp_certificate(bad)
        self.assertFalse(res["valid"])
        self.assertTrue(res["reason"].startswith("lipschitz_violation_edge_"), msg=str(res))

    def test_07_must_fail_share_raised_by_one_billionth(self) -> None:
        name, n, goals, edges = load_instances()[0]
        costs = [e[2] for e in edges]
        shares = split_costs("thirds", costs)
        self.assertEqual(over_budget_edges(costs, shares), [])
        shares[1][3] += Fraction(1, 10 ** 9)
        self.assertEqual(over_budget_edges(costs, shares), [3])
        # A negative share is flagged even though it lowers the sum.
        shares = split_costs("thirds", costs)
        shares[0][5] = -Fraction(1, 10 ** 9)
        self.assertEqual(over_budget_edges(costs, shares), [5])

    def test_08_must_fail_loss_bound_with_half_the_hops(self) -> None:
        # Shows the loss check is not vacuous: half the allowance is exceeded on a real run.
        name, n, goals, edges = load_instances()[0]
        costs = [e[2] for e in edges]
        shares = split_costs("sevenths", costs)
        seen = 0
        for k in range(SHARES):
            fl = [floor_grid(x, 10) for x in shares[k]]
            pre, _ = dist_and_hops(n, goals, edges, shares[k])
            post, hops = dist_and_hops(n, goals, edges, fl)
            seen += loss_bound_violations(pre, post, hops, 10, Fraction(1, 2))
        self.assertGreater(seen, 0)


    def test_09_signed_shares_floor_of_potentials_leaves_a_negative_residual(self) -> None:
        # Chain 2 -> 1 -> 0, each edge costs 1/2, D = 1, one layer on the identity quotient.
        edges = [(2, 1, Fraction(1, 2)), (1, 0, Fraction(1, 2))]
        ident = [list(range(3))]
        exact = peel(3, [0], edges, ident, "exact", 1)
        self.assertEqual(exact["layers"][0], [0, Fraction(1, 2), Fraction(1)])
        self.assertIsNone(exact["first_negative"])
        self.assertEqual(exact["resid"], [0, 0])
        # Floored potentials are [0, 0, 1]. Edge 2 -> 1 gets residual 1/2 + 0 - 1 = -1/2.
        bad = peel(3, [0], edges, ident, "floor_pot", 1)
        self.assertEqual(bad["layers"][0], [0, 0, 1])
        self.assertEqual(bad["first_negative"], (0, Fraction(-1, 2)))
        # Must-fail control: the check is not always firing. Flooring the input costs first is safe here.
        safe = peel(3, [0], edges, ident, "floor_input", 1)
        self.assertIsNone(safe["first_negative"])
        self.assertTrue(consistent(3, [0], edges, safe["total"]))
        # Must-fail control on the consistency check itself: the floored potentials break edge 2 -> 1.
        self.assertFalse(consistent(3, [0], edges, [0, 0, 1]))

    def test_10_signed_shares_floor_of_shares_creates_a_negative_cycle(self) -> None:
        # States 1 and 2 form a 2-cycle of cost 1 each way. Exits to the goal 0 cost 3/2 and 1.
        edges = [(1, 2, Fraction(1)), (2, 1, Fraction(1)), (1, 0, Fraction(3, 2)), (2, 0, Fraction(1))]
        costs = [e[2] for e in edges]
        ident = [list(range(3))]
        h = peel(3, [0], edges, ident, "exact", 1)["layers"][0]
        self.assertEqual(h, [0, Fraction(3, 2), Fraction(1)])
        shares = [h[u] - h[v] for u, v, _ in edges]
        self.assertEqual(shares, [Fraction(1, 2), Fraction(-1, 2), Fraction(3, 2), Fraction(1)])
        self.assertFalse(has_negative_cycle(3, edges, shares))
        floored = [floor_grid(x, 1) for x in shares]
        self.assertEqual(floored, [0, -1, 1, 1])
        # The budget still looks fine: every floored share is at most the unfloored one, so the
        # remaining cost is non-negative. The damage is the cycle 1 -> 2 -> 1 of total share -1.
        self.assertTrue(all(c - f >= 0 for c, f in zip(costs, floored)))
        self.assertTrue(has_negative_cycle(3, edges, floored))
        # Must-fail control on the cycle check: it must reject a share vector with a known negative cycle
        # and accept the same graph with the cycle made zero.
        self.assertTrue(has_negative_cycle(3, edges, [Fraction(0), Fraction(-1), Fraction(1), Fraction(1)]))
        self.assertFalse(has_negative_cycle(3, edges, [Fraction(0), Fraction(0), Fraction(1), Fraction(1)]))
        # The safe rule gives shares with no negative cycle.
        safe = peel(3, [0], edges, ident, "floor_input", 1)
        self.assertIsNone(safe["first_negative"])
        safe_shares = [safe["layers"][0][u] - safe["layers"][0][v] for u, v, _ in edges]
        self.assertEqual(safe_shares, [0, 0, 1, 1])
        self.assertFalse(has_negative_cycle(3, edges, safe_shares))

    def test_11_safe_rule_floor_each_layers_input_on_small_graphs(self) -> None:
        merged = [0, 1, 1, 2, 2]
        coarse = [0, 1, 2, 2, 2]
        orders = [[list(range(5)), merged], [merged, list(range(5))], [merged, coarse], [coarse, merged]]
        unsafe_failures = 0
        for edges in small_graphs(40):
            for d in (1, 2, 4):
                for qs in orders:
                    safe = peel(5, [0], edges, qs, "floor_input", d)
                    self.assertIsNone(safe["first_negative"], msg=f"{edges} D={d}")
                    self.assertTrue(consistent(5, [0], edges, safe["total"]), msg=f"{edges} D={d}")
                    # every layer's potentials sit on the grid
                    for h in safe["layers"]:
                        self.assertTrue(all((x * d).denominator == 1 for x in h))
                    # Must-fail control: the same case under the unsafe rule.
                    if peel(5, [0], edges, qs, "floor_pot", d)["first_negative"] is not None:
                        unsafe_failures += 1
        self.assertGreater(unsafe_failures, 0)
        # Costs already on the grid need no rounding at all: all three rules agree.
        ongrid_cases = 0
        for edges in small_graphs(40, denom=4):
            for d in (4, 8):
                for qs in orders:
                    self.assertTrue(all((w * d).denominator == 1 for _, _, w in edges))
                    ongrid_cases += 1
                    exact = peel(5, [0], edges, qs, "exact", d)
                    self.assertIsNone(exact["first_negative"])
                    for rule in ("floor_input", "floor_pot"):
                        same = peel(5, [0], edges, qs, rule, d)
                        self.assertEqual(same["layers"], exact["layers"], msg=f"{rule} {edges} D={d}")
                        self.assertEqual(same["resid"], exact["resid"])
        self.assertEqual(ongrid_cases, 320)
        # Must-fail control: the same graphs on a coarser grid are off the grid and the rules then differ.
        differ = 0
        for edges in small_graphs(40, denom=4):
            for qs in orders:
                if peel(5, [0], edges, qs, "floor_pot", 1)["layers"] != peel(5, [0], edges, qs, "exact", 1)["layers"]:
                    differ += 1
        self.assertGreater(differ, 0)
        # Must-fail control on the consistency check: raise one summed potential and it must be rejected.
        edges = next(small_graphs(1))
        total = peel(5, [0], edges, orders[0], "floor_input", 2)["total"]
        self.assertTrue(consistent(5, [0], edges, total))
        tampered = list(total)
        u, v, w = edges[0]
        tampered[u] = tampered[v] + w + Fraction(1, 2)
        self.assertFalse(consistent(5, [0], edges, tampered))
        # Must-fail control on the goal clause: a raised goal potential loosens every edge into the goal,
        # so only the goal check can reject it.
        tampered = list(total)
        tampered[0] += 1
        self.assertTrue(all(tampered[a] - tampered[b] <= c for a, b, c in edges))
        self.assertFalse(consistent(5, [0], edges, tampered))


if __name__ == "__main__":
    unittest.main()
