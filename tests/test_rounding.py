"""Rounding direction for cost partitions: floor keeps shares valid, old potentials go stale.

Three statements are checked on the three instances in certificate.json, for D = 10, 100, 10000:

  A. Flooring each share of an operator cost to the grid 1/D keeps the sum of shares at or below the
     operator cost.
  B. Potentials computed before rounding are rejected by the repository's independent checker on the
     rounded costs. Potentials recomputed with the repository's synthesizer on the rounded costs are
     accepted.
  C. At every vertex, recomputing on the rounded costs lowers a share's potential by at most
     (edges on a shortest path after rounding) / D.

Each statement has a control that must fail. Plain assertions are written as unittest methods, so
`python3 -O` does not strip them.
"""
from __future__ import annotations

import copy
import heapq
import json
import math
from fractions import Fraction
from pathlib import Path
import unittest

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


if __name__ == "__main__":
    unittest.main()
