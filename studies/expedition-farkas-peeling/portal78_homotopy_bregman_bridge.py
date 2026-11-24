#!/usr/bin/env python3
"""Exact-Rational Maslov-Doob Homotopy (Portal 7) & Nonlinear Bregman Two-Loop Pythagoras (Portal 8).

100% zero-float (`fractions.Fraction` only, stdlib only) computational proof & instrument
uniting `continuum-bridge`'s live discoveries (#36/#37) with `session-cartographer`'s
Session 1 Portals 7 & 8 (#38, S1:F[400-401, 412-415, 450-451]):

  PART I — Exact Q[q] Maslov-Doob Homotopy & All-Beta Rigidity Theorem (Portal 7):
    Set q := exp(-beta) in Q intersect (0, 1) on integer edge costs c(u, v) in Z_{>= 0}.
    Define the exact rational Cole-Hopf transfer matrix (K_q)_{uv} = q^{c(u, v)} in Q
    (and summed over multi-edges if present).
    1. Exact Doob h-Transform = 1-Cochain Farkas Peeling:
       Under ANY 1-cochain gauge shift c'(u, v) = c(u, v) + h(pi(v)) - h(pi(u)),
         K_q' = D_h^{-1} K_q D_h   where (D_h)_{uu} = q^{h(pi(u))} in Q.
       Verified identically over Q across q in {1/2, 1/4, 1/8, 1/16} on the 32-state
       coupled 2-agent system: exact similarity K_q' == D_h^{-1} K_q D_h, exact preservation
       of Tr((K_q)^k) for k = 1..4 (spectral/cycle-holonomy invariance), and exact convergence
       of the peeled matrix entries K_q' -> indicator of zero-reduced-cost optimal edges as q -> 0+!
    2. Polynomial Characterization & Accidental Single-q Lumpability Counterexample:
       The block-sum polynomial from u in X to fiber Y is P_{u -> Y}(q) = sum_{v in Y} q^{c(u, v)}.
       - All-beta commutation holds iff P_{u1 -> Y}(q) == P_{u2 -> Y}(q) identically in Q[q]
         (identical outgoing edge-cost multisets!).
       - Tropical commutation (q -> 0+) checks only equality of minimum degree (min cost).
       - Accidental single-q lumpability occurs at an isolated rational root q* in (0, 1):
         explicit 4-state witness with P_{u1 -> Y}(q) = q and P_{u2 -> Y}(q) = 2 q^2 gives
         EXACT zero linear defect delta_q == 0 at q = 1/2, strictly POSITIVE defect at ALL
         other q (e.g. q = 1/3, 1/4, 2/3), and strictly POSITIVE tropical defect delta^trop = 1!

  PART II — Exact Nonlinear Bregman Dually-Flat Two-Loop Pythagoras & Fisher-Rao Boundary (Portal 8):
    Replaces Euclidean l2 in `two_loop_omitted_variable.py` (SEAM-07) with the genuinely
    NON-QUADRATIC, NON-EUCLIDEAN cubic Legendre generator on Q_{>0}^m:
      F(q) = (1/3) sum_i q_i^3,    grad F(q)_i = q_i^2,    H_F(q) = diag(2 q_i),
      D_F(p || q) = (1/3) sum_i (p_i - q_i)^2 (p_i + 2 q_i) in Q_{>= 0}.
    On the curved exponential/natural-parameter manifold E_Phi = {q > 0 : q^{odot 2} = Phi theta}:
    1. Exact Global Nonlinear Bregman Pythagoras (ZERO linear approximation!):
       If q* in E_Phi satisfies the exact Latch optimality condition Phi^T (p - q*) = 0, then
       for EVERY q_adapt in E_Phi (including any curved shift silencing an outside anchor a_1):
         D_F(p || q_adapt) == D_F(p || q*) + D_F(q* || q_adapt)  >  D_F(p || q*)  EXACTLY IN Q!
       And for a curved specification expansion Phi' = [Phi, Psi_rev] with projection q_rev in E_{Phi'}
       satisfying (Phi')^T (p - q_rev) = 0:
         D_F(p || q_rev)   == D_F(p || q*) - D_F(q_rev || q*)   <  D_F(p || q*)  EXACTLY IN Q!
    2. Exact Fisher-Rao Metric Phase Boundary on Tangent Perturbations:
       With exact rational Fisher metric G_F = Phi^T H_F(q*)^{-1} Phi = Phi^T diag(1/(2 q*_i)) Phi,
       the minimum-Fisher-norm anchor-silencing tangent shift dq = H_F(q*)^{-1} Phi G_F^{-1} Phi^T H_F(q*)^{-1} a_1 * (e_1 / ||a_1||_{Phi,G}^2)
       reproduces the exact local Fisher-Rao phase boundary 0 < rho_{Phi,G} / kappa_perp < 2
       for Falsifier #6 on curved manifolds!

Run:
  python3 -O -B -W error studies/expedition-farkas-peeling/portal78_homotopy_bregman_bridge.py
  python3 -O -B -W error studies/expedition-farkas-peeling/portal78_homotopy_bregman_bridge.py --json
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import json
import sys
from pathlib import Path as _Path
_HERE = str(_Path(__file__).resolve().parent)
if _HERE not in sys.path:
    sys.path.insert(0, _HERE)
from typing import Any, Dict, List, Optional, Sequence, Tuple

from tropical_quotient_sheaf_bridge import (
    build_coupled_2agent_system,
    hs_norm_sq,
    linear_markov_commutation_defect_sq,
    mat_mul,
    mat_t,
    peel_quotient_tower,
    trace,
)

Mat = List[List[Fraction]]
Vec = List[Fraction]

# --- Self-contained exact rational vector & Gauss-Jordan inverse helpers ---
def dot(u: Vec, v: Vec) -> Fraction:
    return sum((a * b for a, b in zip(u, v)), Fraction(0))


def norm2(u: Vec) -> Fraction:
    return dot(u, u)


def vec_add(u: Vec, v: Vec) -> Vec:
    return [a + b for a, b in zip(u, v)]


def vec_sub(u: Vec, v: Vec) -> Vec:
    return [a - b for a, b in zip(u, v)]


def vec_scale(c: Fraction, u: Vec) -> Vec:
    return [c * a for a in u]


def mat_vec(A: Mat, x: Vec) -> Vec:
    return [dot(row, x) for row in A]


def mat_inv_exact(A: Mat) -> Mat:
    """Exact Gauss-Jordan inverse over Q for full-rank square matrix A."""
    n = len(A)
    aug = [A[i][:] + [Fraction(1) if i == j else Fraction(0) for j in range(n)] for i in range(n)]
    for col in range(n):
        piv = None
        for r in range(col, n):
            if aug[r][col] != 0:
                piv = r
                break
        if piv is None:
            raise ValueError("SINGULAR_GRAM_MATRIX")
        aug[col], aug[piv] = aug[piv], aug[col]
        pv = aug[col][col]
        for c in range(2 * n):
            aug[col][c] /= pv
        for r in range(n):
            if r != col and aug[r][col] != 0:
                fac = aug[r][col]
                for c in range(2 * n):
                    aug[r][c] -= fac * aug[col][c]
    return [row[n:] for row in aug]



# ===========================================================================
# PART I: Exact Q[q] Maslov-Doob Homotopy & All-Beta Rigidity (Portal 7)
# ===========================================================================

def build_cole_hopf_matrix(
    num_states: int,
    edges: Sequence[Tuple[int, int, Fraction]],
    q: Fraction,
) -> Mat:
    """Build exact rational Cole-Hopf matrix (K_q)_{uv} = sum_{e=(u,v)} q^{c(e)} for integer c(e) >= 0."""
    K = [[Fraction(0) for _ in range(num_states)] for _ in range(num_states)]
    for u, v, w in edges:
        if w.denominator != 1 or w < 0:
            raise ValueError(f"REQUIRE_NONNEG_INTEGER_COST: got {w}")
        K[u][v] += q ** int(w)
    return K


def doob_similarity_transform(K: Mat, h_vals: Sequence[Fraction], q: Fraction) -> Mat:
    """Exact Doob h-transform K'_q = D_h^{-1} K_q D_h with (D_h)_{uu} = q^{h(u)}."""
    n = len(K)
    d = []
    for h in h_vals:
        if h.denominator != 1 or h < 0:
            raise ValueError(f"REQUIRE_NONNEG_INTEGER_POTENTIAL: got {h}")
        d.append(q ** int(h))
    return [[(K[u][v] * d[v]) / d[u] for v in range(n)] for u in range(n)]


def run_portal7_maslov_doob() -> Dict[str, Any]:
    # --- 1A: Exact Doob h-Transform == 1-Cochain Farkas Peeling on 32-state Coupled System ---
    n_st, goals, edges, pi_x, pi_y = build_coupled_2agent_system(asymmetric=False)
    states = [(x, y, m) for x in range(4) for y in range(4) for m in (0, 1)]
    pi_imb = [2 * (1 if y > x else 0) + m for (x, y, m) in states]
    tower = peel_quotient_tower(
        n_st, goals, edges, [("pi_x", pi_x), ("pi_y", pi_y), ("pi_imbalance", pi_imb)]
    )
    H = tower["H_total"]
    # Build exact reduced-cost edges c_red(u, v) = c(u, v) + H[v] - H[u] >= 0
    red_edges = [(u, v, w + H[v] - H[u]) for (u, v, w) in edges]

    homotopy_rows = []
    for q in (Fraction(1, 2), Fraction(1, 4), Fraction(1, 8), Fraction(1, 16)):
        K_orig = build_cole_hopf_matrix(n_st, edges, q)
        K_red = build_cole_hopf_matrix(n_st, red_edges, q)
        K_doob = doob_similarity_transform(K_orig, H, q)
        if K_red != K_doob:
            raise RuntimeError(f"Doob h-transform identity failed at q={q}")

        # Verify exact spectral/cycle-holonomy preservation: Tr(K_orig^k) == Tr(K_red^k) for k=1..4
        P_o, P_r = K_orig, K_red
        traces_match = True
        tr_list = []
        for k in range(1, 5):
            to, tr = trace(P_o), trace(P_r)
            if to != tr:
                traces_match = False
            tr_list.append(str(to))
            if k < 4:
                P_o = mat_mul(P_o, K_orig)
                P_r = mat_mul(P_r, K_red)
        if not traces_match:
            raise RuntimeError(f"Cycle-holonomy trace invariance failed at q={q}")

        # Check convergence of K_red to the exact indicator matrix of zero-reduced-cost optimal edges
        # Entry (u,v) of K_red equals 1 if c_red == 0, else <= q^1 -> max deviation from {0,1} <= q!
        max_nonopt_entry = max(
            (K_red[u][v] for (u, v, c_r) in red_edges if c_r > 0),
            default=Fraction(0),
        )
        if max_nonopt_entry > q:
            raise RuntimeError(f"Tropical convergence bound violated at q={q}")
        homotopy_rows.append({
            "q": str(q),
            "exact_doob_similarity_K_red_eq_Dinv_K_D": True,
            "cycle_traces_k1_to_k4_match": traces_match,
            "tr_K2": tr_list[1],
            "max_suboptimal_entry_in_K_red": str(max_nonopt_entry),
        })

    # --- 1B: Accidental Single-q Lumpability vs All-Beta Multiset Rigidity ---
    # 4-state system: goal 0; fiber {1, 2} (quotient state 1); sink/auxiliary state 3 (quotient state 2).
    # Wait: even simpler! 3 quotient blocks: goal=0, fiber X={1, 2}, target Y={0, 3} with pi = [0, 1, 1, 0]!
    # Vertex 1 has ONE edge of cost 1 into fiber 0: (1 -> 0, cost 1)  => P_{1 -> 0}(q) = q
    # Vertex 2 has TWO edges of cost 2 into fiber 0: (2 -> 0, cost 2) and (2 -> 3, cost 2) => P_{2 -> 0}(q) = 2 q^2
    # Goal fiber {0, 3}: 0 -> 0 (cost 1), 3 -> 3 (cost 1) (identical cost-1 self-loops!).
    # Polynomial difference: P_{1->0}(q) - P_{2->0}(q) = q - 2 q^2 = q(1 - 2q) == 0 IFF q = 1/2!
    acc_edges = [
        (0, 0, Fraction(1)),
        (3, 3, Fraction(1)),
        (1, 0, Fraction(1)),
        (2, 0, Fraction(2)),
        (2, 3, Fraction(2)),
    ]
    acc_pi = [0, 1, 1, 0]
    acc_q_sweep = []
    for q_test in (Fraction(1, 4), Fraction(1, 3), Fraction(1, 2), Fraction(2, 3), Fraction(3, 4)):
        Kq = build_cole_hopf_matrix(4, acc_edges, q_test)
        # Check exact lumpability defect ||(I - Pi) K_q Pi||_HS^2 (remember Pi projects onto fiber-constant cols;
        # Wait: standard right-action lumpability is K_q Pi == Pi K_q Pi <=> ||(I - Pi) K_q Pi||_HS^2 == 0!)
        # Let's check: (K_q Pi)_{u, w} = (1/|Y|) sum_{v in Y} (K_q)_{uv} = (1/|Y|) P_{u -> Y}(q)!
        # So (I - Pi) K_q Pi == 0 IFF P_{u -> Y}(q) is constant on every fiber u in X!
        def_sq = linear_markov_commutation_defect_sq(Kq, acc_pi)
        acc_q_sweep.append({
            "q": str(q_test),
            "P1_minus_P2": str(q_test - 2 * q_test * q_test),
            "commutation_defect_hs2": str(def_sq),
            "exact_lumpable_at_q": (def_sq == 0),
        })
        if (q_test == Fraction(1, 2)) != (def_sq == 0):
            raise RuntimeError(f"Accidental single-q lumpability check failed at q={q_test}: def_sq={def_sq}")

    # Verify tropical defect on the SAME system is strictly positive (delta^trop = 1 at state 2!)
    acc_trop = peel_quotient_tower(4, [0, 3], acc_edges, [("acc_pi", acc_pi)])
    if acc_trop["layers"][0]["max_tropical_defect"] != "1":
        raise RuntimeError(f"Expected tropical defect 1, got {acc_trop['layers'][0]['max_tropical_defect']}")

    # --- 1B-2: Row-Normalized Boltzmann Markov Witness (5-state, accidental single-q at q = 1/2!) ---
    # Fiber X = {1, 2}, target fiber Y = {0, 3}, sink/exit fiber Z = {4}, pi = [0, 1, 1, 0, 2].
    # State 1: (1->0, cost 1) [weight q], (1->4, cost 1) [weight q]  => row sum = 2q, P_q(1->Y) = 1/2!
    # State 2: (2->0, cost 2) [weight q^2], (2->3, cost 2) [weight q^2], (2->4, cost 1) [weight q]
    #   => row sum = 2q^2 + q, P_q(2->Y) = 2q^2 / (2q^2 + q) = 2q / (2q + 1)!
    # Check: P_q(1->Y) - P_q(2->Y) = 1/2 - 2q/(2q+1) = (1 - 2q) / (2(2q+1)) == 0 IFF q = 1/2!!
    # So EVEN AFTER ROW NORMALIZATION into a stochastic Boltzmann kernel P_q, lumpability holds
    # EXCLUSIVELY at q = 1/2, fails at all other q, AND fails tropical commutation (delta^trop = 1)!
    boltz_edges = [
        (0, 0, Fraction(1)),
        (3, 3, Fraction(1)),
        (4, 0, Fraction(3)),
        (1, 0, Fraction(1)),
        (1, 4, Fraction(1)),
        (2, 0, Fraction(2)),
        (2, 3, Fraction(2)),
        (2, 4, Fraction(1)),
    ]
    boltz_pi = [0, 1, 1, 0, 2]
    boltz_sweep = []
    for q_test in (Fraction(1, 4), Fraction(1, 3), Fraction(1, 2), Fraction(2, 3), Fraction(3, 4)):
        Kq = build_cole_hopf_matrix(5, boltz_edges, q_test)
        # Row-normalize Kq into exact rational stochastic Boltzmann transition matrix P_q
        Pq = []
        for row in Kq:
            rs = sum(row, Fraction(0))
            Pq.append([v / rs for v in row])
        def_sq_b = linear_markov_commutation_defect_sq(Pq, boltz_pi)
        gap_b = (Fraction(1) - 2 * q_test) / (2 * (2 * q_test + Fraction(1)))
        boltz_sweep.append({
            "q": str(q_test),
            "P1_minus_P2": str(gap_b),
            "commutation_defect_hs2": str(def_sq_b),
            "exact_lumpable_at_q": (def_sq_b == 0),
        })
        if (q_test == Fraction(1, 2)) != (def_sq_b == 0):
            raise RuntimeError(f"Row-normalized Boltzmann witness failed at q={q_test}")
    boltz_trop = peel_quotient_tower(5, [0, 3], boltz_edges, [("boltz_pi", boltz_pi)])
    if boltz_trop["layers"][0]["max_tropical_defect"] != "1":
        raise RuntimeError(
            f"Row-normalized Boltzmann tropical defect mismatch: {boltz_trop['layers'][0]['max_tropical_defect']}"
        )

    # --- 1C: All-Beta Rigid Positive Control (Identical Outgoing Cost Multisets) ---
    # Vertex 1: (1->0, cost 1), (1->3, cost 2); Vertex 2: (2->0, cost 2), (2->3, cost 1).
    # Different individual edges, IDENTICAL outgoing cost multiset {{1, 2}} into fiber {0, 3}!
    rigid_edges = [
        (0, 0, Fraction(1)),
        (3, 3, Fraction(1)),
        (1, 0, Fraction(1)),
        (1, 3, Fraction(2)),
        (2, 0, Fraction(2)),
        (2, 3, Fraction(1)),
    ]
    rigid_all_zero = True
    for q_test in (Fraction(1, 16), Fraction(1, 4), Fraction(1, 3), Fraction(1, 2), Fraction(2, 3)):
        if linear_markov_commutation_defect_sq(build_cole_hopf_matrix(4, rigid_edges, q_test), acc_pi) != 0:
            rigid_all_zero = False
    rigid_trop = peel_quotient_tower(4, [0, 3], rigid_edges, [("acc_pi", acc_pi)])
    if not (rigid_all_zero and rigid_trop["exact_micro_optimal"] and rigid_trop["layers"][0]["max_tropical_defect"] == "0"):
        raise RuntimeError("All-beta multiset-rigid positive control failed!")

    return {
        "doob_h_transform_equals_farkas_peeling_32states": homotopy_rows,
        "accidental_single_q_lumpability_witness": {
            "polynomial_gap": "P_{1->0}(q) - P_{2->0}(q) = q(1 - 2q)",
            "q_sweep": acc_q_sweep,
            "tropical_defect_at_q_to_0": acc_trop["layers"][0]["max_tropical_defect"],
            "exact_only_at_q_half": True,
        },
        "row_normalized_boltzmann_single_q_witness": {
            "normalized_gap": "P_q(1->Y) - P_q(2->Y) = (1 - 2q)/(2(2q + 1))",
            "q_sweep": boltz_sweep,
            "tropical_defect_at_q_to_0": boltz_trop["layers"][0]["max_tropical_defect"],
            "exact_only_at_q_half": True,
        },
        "all_beta_multiset_rigid_control": {
            "zero_defect_at_all_tested_q": rigid_all_zero,
            "tropical_defect": rigid_trop["layers"][0]["max_tropical_defect"],
            "exact_micro_optimal": rigid_trop["exact_micro_optimal"],
        },
    }


# ===========================================================================
# PART II: Exact Nonlinear Cubic-Bregman Two-Loop Pythagoras & Fisher-Rao
#          Phase Boundary (Portal 8, Zero Float!)
# ===========================================================================

def cubic_bregman_div(p: Vec, q: Vec) -> Fraction:
    """Exact Bregman divergence for strictly convex cubic generator F(x) = (1/3) sum x_i^3 on Q_{>0}^m.

    D_F(p || q) = F(p) - F(q) - <grad F(q), p - q> = (1/3) sum_i (p_i - q_i)^2 (p_i + 2 q_i).
    """
    if any(x <= 0 for x in p) or any(x <= 0 for x in q):
        raise ValueError("BREGMAN_DOMAIN_REQUIRES_STRICTLY_POSITIVE_Q")
    return Fraction(1, 3) * sum(
        ((pi - qi) * (pi - qi) * (pi + 2 * qi) for pi, qi in zip(p, q)),
        Fraction(0),
    )


def cubic_grad_F(q: Vec) -> Vec:
    """Exact natural parameter eta = grad F(q) = q^{odot 2} in Q_{>0}^m."""
    return [qi * qi for qi in q]


def run_portal8_nonlinear_bregman() -> Dict[str, Any]:
    # Construct an EXACT rational curved dual-flat family E_Phi = {q > 0 : q^{odot 2} = Phi theta} in Q_{>0}^4!
    # Basis columns of Phi (4 x 2):
    #   phi_0 = [1, 1, 1, 1]^T
    #   phi_1 = [1, 1, -1, -1]^T
    # Notice any vector of the form [a^2, a^2, b^2, b^2]^T lies EXACTLY in Col(Phi) with
    #   theta_0 = (a^2 + b^2)/2, theta_1 = (a^2 - b^2)/2!
    # So q(a, b) = [a, a, b, b]^T (for ANY rational a, b > 0) lies EXACTLY on the curved manifold E_Phi!
    Phi: Mat = [
        [Fraction(1), Fraction(1)],
        [Fraction(1), Fraction(1)],
        [Fraction(1), Fraction(-1)],
        [Fraction(1), Fraction(-1)],
    ]
    Phi_T = mat_t(Phi)

    # Latch optimum q* = [2, 2, 3, 3] in E_Phi (eta* = [4, 4, 9, 9] = Phi [13/2, -5/2]^T)
    q_star: Vec = [Fraction(2), Fraction(2), Fraction(3), Fraction(3)]
    # True distribution p = q* + r* where r* in ker(Phi^T), i.e. r* = [1, -1, 1, -1] (exact Latch optimality Phi^T (p - q*) = 0!)
    # Check positivity: p = [3, 1, 4, 2] > 0 strictly!
    r_star: Vec = [Fraction(1), Fraction(-1), Fraction(1), Fraction(-1)]
    p: Vec = vec_add(q_star, r_star)
    if mat_vec(Phi_T, vec_sub(p, q_star)) != [Fraction(0), Fraction(0)]:
        raise RuntimeError("Latch optimality Phi^T(p - q*) == 0 failed!")

    # Outside anchor a_1 = [1, 0, 0, 0]^T:
    #   At Latch optimum q*, anchor reading is e_1 = <a_1, p - q*> = 3 - 2 = 1 != 0 (FAILS anchor!).
    #   Forcing q_adapt in E_Phi to silence a_1 (<a_1, p - q_adapt> = 0) sets first coordinate a = 3:
    #   e.g. q_adapt = [3, 3, 3, 3] in E_Phi (still on the curved manifold E_Phi: eta_adapt = [9, 9, 9, 9] = Phi [9, 0]^T)!
    a_1: Vec = [Fraction(1), Fraction(0), Fraction(0), Fraction(0)]
    q_adapt: Vec = [Fraction(3), Fraction(3), Fraction(3), Fraction(3)]
    if dot(a_1, vec_sub(p, q_adapt)) != Fraction(0):
        raise RuntimeError("q_adapt did not silence anchor a_1!")

    # Exact Global Nonlinear Bregman Pythagoras (NO linear approximation!):
    d_p_qstar = cubic_bregman_div(p, q_star)
    d_p_qadapt = cubic_bregman_div(p, q_adapt)
    d_qstar_qadapt = cubic_bregman_div(q_star, q_adapt)
    if d_p_qadapt != d_p_qstar + d_qstar_qadapt or d_qstar_qadapt <= 0:
        raise RuntimeError(
            f"Nonlinear Bregman Pythagoras failed: {d_p_qadapt} != {d_p_qstar} + {d_qstar_qadapt}"
        )

    # Curved Specification Expansion: add omitted column psi = [1, -1, 0, 0]^T -> Phi' = [Phi, psi]
    # Now q_rev = [3, 1, 3, 3] lies EXACTLY on the expanded curved manifold E_{Phi'}!
    # Check: grad F(q_rev) = [9, 1, 9, 9] = 7*[1,1,1,1] + (-2)*[1,1,-1,-1] + 4*[1,-1,0,0] in Col(Phi')!
    # AND exact Latch optimality on expanded spec: (Phi')^T (p - q_rev) = 0 (since p - q_rev = [0, 0, 1, -1] perp Phi')!
    Phi_rev: Mat = [
        [Fraction(1), Fraction(1), Fraction(1)],
        [Fraction(1), Fraction(1), Fraction(-1)],
        [Fraction(1), Fraction(-1), Fraction(0)],
        [Fraction(1), Fraction(-1), Fraction(0)],
    ]
    q_rev: Vec = [Fraction(3), Fraction(1), Fraction(3), Fraction(3)]
    if mat_vec(mat_t(Phi_rev), vec_sub(p, q_rev)) != [Fraction(0), Fraction(0), Fraction(0)]:
        raise RuntimeError("Expanded spec optimality (Phi')^T(p - q_rev) == 0 failed!")
    # Verify grad F(q_rev) in Col(Phi_rev) explicitly:
    theta_rev = [Fraction(7), Fraction(-2), Fraction(4)]
    if mat_vec(Phi_rev, theta_rev) != cubic_grad_F(q_rev):
        raise RuntimeError("q_rev not on curved manifold E_{Phi'}!")

    # Exact Nonlinear Bregman Contraction: D_F(p || q_rev) == D_F(p || q*) - D_F(q_rev || q*)!
    d_p_qrev = cubic_bregman_div(p, q_rev)
    d_qrev_qstar = cubic_bregman_div(q_rev, q_star)
    if d_p_qrev != d_p_qstar - d_qrev_qstar or d_qrev_qstar <= 0:
        raise RuntimeError(
            f"Nonlinear Bregman contraction failed: {d_p_qrev} != {d_p_qstar} - {d_qrev_qstar}"
        )

    # Full spec expansion (adding [0, 0, 1, -1]) hits q_full = p with D_F(p || p) == 0!
    d_p_p = cubic_bregman_div(p, p)

    # --- 2B: Exact Fisher-Rao Tangent Phase Boundary on Non-Uniform Curvature H_F(q*) = diag(2 q*_i) ---
    # Tangent space of E_Phi at q* is spanned by J = H_F(q*)^{-1} Phi = diag(1/(2 q*_i)) Phi.
    # Notice q* = [2, 2, 3, 3] has NON-UNIFORM Hessian H_F = diag(4, 4, 6, 6) != c * I!
    # Exact Fisher metric on tangent coordinates d_theta: G_F = Phi^T H_F^{-1} Phi.
    # Minimum-Fisher-norm shift d_theta silencing a_1 (<a_1, J d_theta> = e_1) is:
    #   d_theta = (e_1 / (a_1^T J G_F^{-1} J^T a_1)) * G_F^{-1} J^T a_1,
    #   dq      = J d_theta = (e_1 / ||a_1||_{Phi,G}^2) * P_{Phi,G} a_1,
    # where P_{Phi,G} = J G_F^{-1} J^T = H_F^{-1} Phi (Phi^T H_F^{-1} Phi)^{-1} Phi^T H_F^{-1} (Fisher-metric projection!).
    H_inv_diag = [Fraction(1) / (2 * qi) for qi in q_star]  # [1/4, 1/4, 1/6, 1/6]
    J: Mat = [[H_inv_diag[r] * Phi[r][c] for c in range(2)] for r in range(4)]
    G_F = mat_mul(Phi_T, J)  # Phi^T H_F^{-1} Phi
    G_F_inv = mat_inv_exact(G_F)
    # Fisher-metric operator M_G = J G_F^{-1} J^T
    M_G = mat_mul(mat_mul(J, G_F_inv), mat_t(J))

    # Pick anchor a_1 = [1, 0, 1, 0] (couples BOTH differently-curved blocks q*=2 and q*=3!)
    a1_f: Vec = [Fraction(1), Fraction(0), Fraction(1), Fraction(0)]
    e1_f = dot(a1_f, r_star)  # 1 + 1 = 2
    p1_G = mat_vec(M_G, a1_f)
    denom_G = dot(a1_f, p1_G)  # a_1^T M_G a_1 > 0
    dq_G = vec_scale(e1_f / denom_G, p1_G)
    if dot(a1_f, dq_G) != e1_f:
        raise RuntimeError("Fisher-Rao tangent shift did not silence a_1!")
    # Check exact Fisher-norm quadratic expansion: dq^T H_F dq == e1_f^2 / denom_G
    H_F_dq = [2 * q_star[i] * dq_G[i] for i in range(4)]
    fisher_quad_inflation = dot(dq_G, H_F_dq)
    if fisher_quad_inflation != (e1_f * e1_f) / denom_G:
        raise RuntimeError("Fisher-Rao quadratic inflation identity failed!")

    # Verify non-Euclidean Fisher phase boundary on fresh anchor family a_2(alpha) = alpha * [1, 1, 0, 0] + [0, 0, 1, -1]:
    # Notice e_2 = <a_2, r*> = 2, kappa_perp = e_2 / e_1 = 1, and rho_{Phi,G} = <a_2, p1_G> / denom_G!
    # Also compute naive Euclidean ratio to prove non-uniform curvature shifts the boundary!
    fisher_sweep = []
    for alpha in (Fraction(-1), Fraction(0), Fraction(1), Fraction(2), Fraction(3), Fraction(5), Fraction(6)):
        a2_f = vec_add(vec_scale(alpha, [Fraction(1), Fraction(1), Fraction(0), Fraction(0)]), [Fraction(0), Fraction(0), Fraction(1), Fraction(-1)])
        e2_f = dot(a2_f, r_star)
        e2_after = e2_f - dot(a2_f, dq_G)
        rho_G = dot(a2_f, p1_G) / denom_G
        kappa_p = e2_f / e1_f
        ratio_G = rho_G / kappa_p
        if e2_after != e2_f * (Fraction(1) - ratio_G):
            raise RuntimeError("Fisher-Rao phase formula mismatch!")
        fires = (e2_after * e2_after < e2_f * e2_f)
        if fires != (Fraction(0) < ratio_G < Fraction(2)):
            raise RuntimeError("Fisher-Rao phase iff violated!")
        fisher_sweep.append({
            "alpha": str(alpha),
            "fisher_ratio_rhoG_over_kappa": str(ratio_G),
            "err_sq_before": str(e2_f * e2_f),
            "err_sq_after_fisher_adapt": str(e2_after * e2_after),
            "falsifier6_fires": fires,
        })

    # --- 2C: Genuinely Curved Nonlinear Cone E_cone = {q in Q_{>0}^3 : q_3^2 = q_1^2 + q_2^2} ---
    # Phi_cone = [[1, 0], [0, 1], [1, 1]] => eta = [a^2, b^2, a^2+b^2] => q = [a, b, sqrt(a^2+b^2)]
    # is STRICTLY CURVED in q-space (NOT affine in q)! Pythagorean triples give exact rational points!
    Phi_cone: Mat = [
        [Fraction(1), Fraction(0)],
        [Fraction(0), Fraction(1)],
        [Fraction(1), Fraction(1)],
    ]
    q_star_c: Vec = [Fraction(3), Fraction(4), Fraction(5)]
    q_adapt_c: Vec = [Fraction(5), Fraction(12), Fraction(13)]
    # r* in ker(Phi_cone^T) = span([1, 1, -1]); pick p = q_star_c + [1, 1, -1] = [4, 5, 4] > 0!
    p_c: Vec = [Fraction(4), Fraction(5), Fraction(4)]
    if mat_vec(mat_t(Phi_cone), vec_sub(p_c, q_star_c)) != [Fraction(0), Fraction(0)]:
        raise RuntimeError("Curved cone Latch optimality failed!")
    d_c_star = cubic_bregman_div(p_c, q_star_c)
    d_c_adapt = cubic_bregman_div(p_c, q_adapt_c)
    d_c_between = cubic_bregman_div(q_star_c, q_adapt_c)
    if d_c_adapt != d_c_star + d_c_between or d_c_between <= 0:
        raise RuntimeError("Curved cone global Bregman Pythagoras failed!")

    return {
        "cubic_bregman_global_pythagoras": {
            "D_F_p_qstar": str(d_p_qstar),
            "D_F_p_qadapt": str(d_p_qadapt),
            "D_F_qstar_qadapt": str(d_qstar_qadapt),
            "exact_inflation_identity_holds": (d_p_qadapt == d_p_qstar + d_qstar_qadapt),
            "D_F_p_qrev_partial": str(d_p_qrev),
            "D_F_qrev_qstar": str(d_qrev_qstar),
            "exact_contraction_identity_holds": (d_p_qrev == d_p_qstar - d_qrev_qstar),
            "D_F_p_full_rev": str(d_p_p),
            "strict_global_ordering": (d_p_p < d_p_qrev < d_p_qstar < d_p_qadapt),
        },
        "genuinely_curved_pythagorean_cone_pythagoras": {
            "q_star": [str(x) for x in q_star_c],
            "q_adapt": [str(x) for x in q_adapt_c],
            "p": [str(x) for x in p_c],
            "D_F_p_qstar": str(d_c_star),
            "D_F_qstar_qadapt": str(d_c_between),
            "D_F_p_qadapt": str(d_c_adapt),
            "exact_curved_identity_holds": (d_c_adapt == d_c_star + d_c_between),
        },
        "fisher_rao_curved_tangent_boundary": {
            "nonuniform_hessian_diag": [str(2 * qi) for qi in q_star],
            "fisher_inflation_dq_HF_dq": str(fisher_quad_inflation),
            "sweep": fisher_sweep,
        },
    }


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true", help="Emit JSON report")
    args = parser.parse_args(argv)
    rep = {
        "portal_7_maslov_doob_homotopy": run_portal7_maslov_doob(),
        "portal_8_nonlinear_bregman_pythagoras": run_portal8_nonlinear_bregman(),
    }
    if args.json:
        print(json.dumps(rep, indent=2))
    else:
        print("=== portal78_homotopy_bregman_bridge.py: ALL CHECKS PASSED (ZERO FLOAT) ===")
        p7 = rep["portal_7_maslov_doob_homotopy"]
        print("P7.1 Doob h-transform == 1-cochain Farkas peeling on 32-state coupled system:")
        for row in p7["doob_h_transform_equals_farkas_peeling_32states"]:
            print(f"     q={row['q']:>4s}: K_red == D_h^-1 K D_h ({row['exact_doob_similarity_K_red_eq_Dinv_K_D']}), Tr(K^1..4) match={row['cycle_traces_k1_to_k4_match']}, max_subopt={row['max_suboptimal_entry_in_K_red']}")
        acc = p7["accidental_single_q_lumpability_witness"]
        print(f"P7.2 Accidental single-q lumpability ({acc['polynomial_gap']}; tropical defect={acc['tropical_defect_at_q_to_0']}):")
        for row in acc["q_sweep"]:
            print(f"     q={row['q']:>3s}: gap={row['P1_minus_P2']:>6s}, defect_hs2={row['commutation_defect_hs2']:>8s}, lumpable={row['exact_lumpable_at_q']}")
        boltz = p7["row_normalized_boltzmann_single_q_witness"]
        print(f"P7.2b Row-normalized Boltzmann Markov witness ({boltz['normalized_gap']}; tropical defect={boltz['tropical_defect_at_q_to_0']}):")
        for row in boltz["q_sweep"]:
            print(f"     q={row['q']:>3s}: gap={row['P1_minus_P2']:>8s}, defect_hs2={row['commutation_defect_hs2']:>12s}, lumpable={row['exact_lumpable_at_q']}")
        rg = p7["all_beta_multiset_rigid_control"]
        print(f"P7.3 All-beta multiset-rigid control: zero_all_q={rg['zero_defect_at_all_tested_q']}, tropical_defect={rg['tropical_defect']}, exact_opt={rg['exact_micro_optimal']}")
        p8 = rep["portal_8_nonlinear_bregman_pythagoras"]
        bp = p8["cubic_bregman_global_pythagoras"]
        print(
            f"P8.1 Exact Nonlinear Cubic-Bregman Pythagoras: "
            f"D(p||full)={bp['D_F_p_full_rev']} < D(p||rev)={bp['D_F_p_qrev_partial']} (= {bp['D_F_p_qstar']} - {bp['D_F_qrev_qstar']}) < "
            f"D(p||q*)={bp['D_F_p_qstar']} < D(p||adapt)={bp['D_F_p_qadapt']} (= {bp['D_F_p_qstar']} + {bp['D_F_qstar_qadapt']})"
        )
        cc = p8["genuinely_curved_pythagorean_cone_pythagoras"]
        print(
            f"P8.1b Genuinely curved Pythagorean cone ({cc['q_star']} -> {cc['q_adapt']}, p={cc['p']}): "
            f"D(p||adapt)={cc['D_F_p_qadapt']} == D(p||q*)={cc['D_F_p_qstar']} + D(q*||adapt)={cc['D_F_qstar_qadapt']} ({cc['exact_curved_identity_holds']})"
        )
        fr = p8["fisher_rao_curved_tangent_boundary"]
        print(f"P8.2 Fisher-Rao curved tangent phase boundary (H_F diag={fr['nonuniform_hessian_diag']}, inflation={fr['fisher_inflation_dq_HF_dq']}):")
        for row in fr["sweep"]:
            print(f"     alpha={row['alpha']:>2s} | fisher_ratio={row['fisher_ratio_rhoG_over_kappa']:>5s} | before^2={row['err_sq_before']:>2s} -> after^2={row['err_sq_after_fisher_adapt']:>6s} | Falsifier#6={row['falsifier6_fires']}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
