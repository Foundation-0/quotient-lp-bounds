# Mathematical Proofs for Quotient-LP and Monotone Deficit Synthesis

This document records the exact mathematical invariants verified by `verify.py` and `verify_independent.py` and bound to the 6-kernel Lean 4 theorems in `Mcproof.Spec`.

## 1. Quotient Homomorphism Soundness

Let $G = (S, E, c, S_{\text{goal}})$ be a concrete state transition system with non-negative rational step costs $c : E \to \mathbb{Q}_{\ge 0}$, and let $Q = (V_Q, E_Q, w_Q, Q_{\text{goal}})$ be a finite quotient graph equipped with a map $\pi : S \to V_Q$ such that:

1. For every $g \in S_{\text{goal}}$, $\pi(g) \in Q_{\text{goal}}$.
2. For every concrete transition $(s, s') \in E$, either $\pi(s) = \pi(s')$ (a quotient self-loop) or $(\pi(s), \pi(s')) \in E_Q$ with $w_Q(\pi(s), \pi(s')) \le c(s, s')$.

Any function $h : V_Q \to \mathbb{Q}_{\ge 0}$ satisfying $h(q) = 0$ for all $q \in Q_{\text{goal}}$ and the edge Lipschitz inequality $h(u) - h(v) \le w_Q(u, v)$ for all $(u, v) \in E_Q$ lifts to a globally consistent lower bound $H(s) = h(\pi(s))$ on $G$:

$$H(s) - H(s') = h(\pi(s)) - h(\pi(s')) \le c(s, s').$$

## 2. Exact Strong Duality of Optimal 1-Lipschitz Repair

Given importance weights $\mu \in \mathbb{Q}_{\ge 0}^{V_Q}$ and optional seed upper bounds $\bar{h} \in \mathbb{Q}_{\ge 0}^{V_Q}$, the repair linear program maximizes $\sum_{u \in V_Q} \mu_u h_u$ subject to $h_g = 0$ ($g \in Q_{\text{goal}}$), $0 \le h_u \le \bar{h}_u$, and $h_u - h_v \le w_e$ for every $e = (u, v) \in E_Q$.

Its linear programming dual introduces edge flows $y_e \ge 0$ and cap multipliers $z_u \ge 0$, minimizing $\sum_{e \in E_Q} w_e y_e + \sum_{u \in V_Q} \bar{h}_u z_u$ subject to net flow conservation at every non-goal vertex $u \notin Q_{\text{goal}}$:

$$\sum_{e \in \delta^+(u)} y_e - \sum_{e \in \delta^-(u)} y_e + z_u \ge \mu_u.$$

For any feasible pair $(h, (y, z))$, weak duality follows directly from non-negativity:

$$\sum_{u \notin Q_{\text{goal}}} \mu_u h_u \le \sum_{u \in V_Q} h_u \left(\sum_{e \in \delta^+(u)} y_e - \sum_{e \in \delta^-(u)} y_e + z_u\right) = \sum_{e=(u,v) \in E_Q} (h_u - h_v) y_e + \sum_{u \in V_Q} h_u z_u \le \sum_{e \in E_Q} w_e y_e + \sum_{u \in V_Q} \bar{h}_u z_u.$$

`verify.py` constructs $(h^*, y^*, z^*)$ from the shortest-path arborescence into the zero-cost goal sink and routes $\mu_u$ along tight parent edges ($h^*_u - h^*_v = w_e$ or $h^*_u = \bar{h}_u$), achieving exact equality $\sum_u \mu_u h^*_u = \sum_e w_e y^*_e + \sum_u \bar{h}_u z^*_u$ in `fractions.Fraction`. `verify_independent.py` checks primal feasibility, dual feasibility, and zero duality gap independently.

## 3. Zero-Self-Loop Monotone Deficit Composition

Suppose $\phi : S \to \mathbb{Q}_{\ge 0}$ vanishes on $S_{\text{goal}}$ and satisfies:

- On quotient self-loops ($\pi(s) = \pi(s')$): $\phi(s) - \phi(s') \le c(s, s')$.
- On quotient transitions ($\pi(s) \ne \pi(s')$): $\phi(s) - \phi(s') \le 0$.

Then for $H_{\text{sum}}(s) = h(\pi(s)) + \phi(s)$:

- If $\pi(s) = \pi(s')$, $H_{\text{sum}}(s) - H_{\text{sum}}(s') = 0 + (\phi(s) - \phi(s')) \le c(s, s')$.
- If $\pi(s) \ne \pi(s')$, $H_{\text{sum}}(s) - H_{\text{sum}}(s') \le w_Q(\pi(s), \pi(s')) + 0 \le c(s, s')$.

This matches `Mcproof.Spec.zeroSelfLoop_deficit_composition` and avoids solving a linear program on $S$ when $\phi$ tracks monotone irreversible or boundary-isolated resource creation.

## 4. Rounding Direction for Cost Partitions

A cost partition splits each operator cost $c(e)$ into $K$ shares $c_1(e), \dots, c_K(e) \ge 0$ with $\sum_i c_i(e) \le c(e)$. Each share has its own potential $h_i$, the exact distance to the goal set under $c_i$. The summed bound $\sum_i h_i(v)$ is then a lower bound on the true distance.

To store shares on a grid of step $1/D$, replace each share by $\lfloor D \cdot c_i(e) \rfloor / D$. Three statements follow.

All are checked by `tests/test_rounding.py` on the three instances in `certificate.json` at $D = 10, 100, 10000$.

**4.1 Floored shares stay valid.** Let $c'_i(e) = \lfloor D \cdot c_i(e) \rfloor / D$. Since $\lfloor x \rfloor \le x$, we have $0 \le c'_i(e) \le c_i(e)$. Summing, $\sum_i c'_i(e) \le \sum_i c_i(e) \le c(e)$. The ceiling fails here: with $c(e) = 1$, $K = 3$, equal thirds and $D = 10$, each share becomes $4/10$ and the sum is $12/10 > 1$.

**4.2 Potentials computed before rounding go stale.** Take one edge $1 \to 0$ with goal $0$, cost $1/2$ and $D = 1$. The potential before rounding is $h(1) = 1/2$. The floored cost is $0$, so the edge inequality $h(1) - h(0) \le 0$ fails: $1/2 > 0$. This is the smallest case, with two vertices and one edge.

In the test file it is test 05, and `verify_independent.py` rejects it with `lipschitz_violation_edge_0:1->0`. Recomputing on the floored cost gives $h(1) = 0$, which the checker accepts. In general, floored costs are no larger, so distances can only fall, and the old potential is too high wherever a distance fell.

**4.3 The loss is bounded by edges over $D$.** Fix a share, write $d$ and $d'$ for distances under $c_i$ and $c'_i$, and let $P$ be a shortest path from $v$ under $c'_i$ with $|P|$ edges. For every edge, $c_i(e) - c'_i(e) < 1/D$ because flooring removes less than one grid step. Then
$$d(v) \le c_i(P) \le c'_i(P) + |P|/D = d'(v) + |P|/D.$$
So $d(v) - d'(v) \le |P|/D$, strictly less when $|P| > 0$. The bound holds for every shortest path $P$ after rounding, in particular the one with fewest edges, which is what the test uses. Over the 18 runs the largest observed ratio of loss to $|P|/D$ is $6/7$ (about $0.857$), and test 03 asserts that value.

**Controls that must fail.** Each is a test that goes red if the guarded behavior is changed:

- Ceiling in place of floor: the share-budget check finds edges over the cost (test 04).
- Stale potentials on the one-edge graph: the repository checker rejects them (test 05).
- A potential raised by $10^{-6}$ at a vertex with a tight edge: the checker reports a Lipschitz violation (test 06).
- A share raised by $10^{-9}$ on an unrounded partition: the budget check flags exactly that edge (test 07).
- The loss bound with half the hops is exceeded on a real run, so the loss check is not vacuous (test 08).

What this does not show: the share-sum rule in 4.1 is checked by code in the test file, because `verify_independent.py` verifies one potential at a time and has no notion of a partition.
