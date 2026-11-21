# Iterative Multi-Quotient Farkas Peeling Tower & Exact `Q[q]` Maslov–Doob Homotopy

**Status:** Independently **`VERIFIED`** (`AUDIT-004` `N2` Part A / `N1` Parts B–C; `AUDIT-008R` `N1`) — 100% zero-float exact rational (`fractions.Fraction`, pure Python 3 stdlib, zero external dependencies).

## Summary of Exact Results

1. **Iterative Multi-Quotient Farkas Residual Peeling Tower ([`tropical_quotient_sheaf_bridge.py`](./tropical_quotient_sheaf_bridge.py), `AUDIT-004` `N2`):**
   - Solves exact-rational 1-Lipschitz quotient LPs sequentially with independent Farkas dual flow certificates (`primal == dual`), updating concrete edge costs via the exact 1-cochain gauge shift:
     $$c^{(j)}(s, s') = c^{(j-1)}(s, s') + h_j^*(\pi_j(s')) - h_j^*(\pi_j(s)) \ge 0.$$
   - **Cohomological Optimality Theorem:** $d^*_G(s) - H^{(K)}(s) = d^*_{(S, E, c^{(K)})}(s)$ identically; for $c > 0$ with all states co-reachable to $S_{\text{goal}}$, $H^{(K)} = d^*_G$ everywhere **iff** the tropical commutation defect $\delta_{\mathrm{emg}}^{\mathrm{trop}}(s) = \min_{(s,s')} c^{(K)}(s,s') = 0$ on all non-goal states.
   - **Strict dominance over `zeroSelfLoop_deficit_composition`:** On a coupled 32-state 2-resource benchmark (exact sum `124`), single quotient $\pi_x$ gives `64`, $\pi_x$ + best `zeroSelfLoop_deficit` stays stuck at **`64`** (`+0`), **2-layer Peeling ($\pi_x \to \pi_y$) reaches `112` (`+48`)**, and **3-layer Peeling (+ 4-state imbalance quotient $\pi_{\mathrm{imb}}$) reaches `124` (100% exact micro-optimal, $\delta_{\mathrm{emg}}^{\mathrm{trop}} \equiv 0$)**.
   - **Order Non-Commutativity & Max Composition:** On an asymmetric coupled cost table, $H_{xy} = 88$, $H_{yx} = 76$, and pointwise $\max(H_{xy}, H_{yx}) = 203/2$ (remains globally 1-Lipschitz; exact `217/2`).
   - **Bidirectional Linear-vs-Tropical Separation:** Exact rational witnesses prove Markov lumpability ($\delta^{\mathrm{lin}} = 0$) and tropical Bellman commutation ($\delta^{\mathrm{trop}} = 0$) are inequivalent in both directions (`dir1: trop=0, lin_hs2=1/4`; `dir2: lin=0, trop=2`).
2. **Exact $\mathbb{Q}[q]$ Maslov–Doob Homotopy & Nonlinear Bregman Pythagoras ([`portal78_homotopy_bregman_bridge.py`](./portal78_homotopy_bregman_bridge.py), `AUDIT-008R`):**
   - Setting $q = e^{-\beta} \in \mathbb{Q} \cap (0, 1)$, 1-cochain Farkas peeling $c \mapsto c + d^0(H)$ is **identically** the Doob $h$-transform similarity $K_q' = D_h^{-1} K_q D_h$ across $q \in \{1/2, 1/4, 1/8, 1/16\}$ on the 32-state coupled system (`Tr(K^1..4)` exact match, suboptimal entries decay as $q^2$).
   - **Accidental single-$q$ lumpability witnesses** vanishing exclusively at $q = 1/2$ (while tropical defect $= 1$): both unnormalized $P_{1\to 0}(q) - P_{2\to 0}(q) = q(1 - 2q)$ and a 5-state **row-normalized stochastic Boltzmann Markov kernel** with gap $\frac{1-2q}{2(2q+1)}$, contrasted with an all-$\beta$ multiset-rigid positive control (`0` defect at all $q$ and tropical defect `0`).
   - **Nonlinear Cubic-Bregman Pythagoras & Fisher–Rao Boundary:** Exact zero-float global Bregman Pythagoras on curved manifolds (including the strictly curved Pythagorean cone `[3,4,5] -> [5,12,13]`, `p = [4,5,4]`: `3865/3 == 37/3 + 1276`) and non-uniform Fisher–Rao curvature $H_F = \operatorname{diag}(4,4,6,6)$.

## Reproduction

```bash
python3 -I -O -B -W error studies/expedition-farkas-peeling/tropical_quotient_sheaf_bridge.py
python3 -I -O -B -W error studies/expedition-farkas-peeling/portal78_homotopy_bregman_bridge.py
```
