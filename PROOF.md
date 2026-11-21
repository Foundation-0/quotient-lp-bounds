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

A cost partition splits each operator cost $c(e)$ into $K$ shares $c_1(e), \dots, c_K(e)$ with $\sum_i c_i(e) \le c(e)$. Each share has its own potential $h_i$, the exact distance to the goal set under $c_i$. The summed bound $\sum_i h_i(v)$ is then a lower bound on the true distance.

**Hypothesis for 4.1 to 4.3.** Every share is non-negative: $c_i(e) \ge 0$. The proofs use it. Section 4.4 treats shares of either sign.

To store shares on a grid of step $1/D$, replace each share by $\lfloor D \cdot c_i(e) \rfloor / D$. Three statements follow for non-negative shares. They are checked by `tests/test_rounding.py` on the three instances in `certificate.json` at $D = 10, 100, 10000$.

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

### 4.4 Signed shares

A reduced-cost tower peels one quotient at a time. Write $c_0 = c$. Layer $j$ has a quotient map $\pi_j$. It solves for the distance $h_j$ to the goal classes on the quotient graph under the residual cost $c_{j-1}$. Each quotient edge takes the least cost among the concrete edges that map to it.

The layer then sets $s_j(e) = h_j(\pi_j(u)) - h_j(\pi_j(v))$ for $e = (u, v)$ and passes on $c_j = c_{j-1} - s_j$. In the planning literature this is saturated cost partitioning in its state-dependent form, where each transition gets its own share (Keller et al., IJCAI 2016, Definition 4). Seipp, Keller and Helmert, JAIR 2020, Definition 13 gives the same tower when each transition is its own label.

Foundation-0/quotient-lp-bounds draft pull request 5 builds such a tower with exact fractions. The tower and its instance are that draft's work. The examples below are ours, found while checking it.

The shares $s_j$ are signed. An edge that leads away from the goal in the quotient has $h_j(\pi_j(u)) < h_j(\pi_j(v))$, so its share is negative and the residual cost grows. The shares sum to $c(e) - c_K(e)$, which is at most $c(e)$ when the final residual is non-negative.

**Example A, flooring potentials after the fact is unsafe.** Take the chain $2 \to 1 \to 0$ with goal $0$, both edges of cost $1/2$, $D = 1$ and the identity quotient. The exact potentials are $(0, 1/2, 1)$ for states $0, 1, 2$. Flooring them gives $(0, 0, 1)$.

The residual of edge $2 \to 1$ is $1/2 + 0 - 1 = -1/2$. A negative residual would start the next layer from a negative cost. The summed bound is also inconsistent: $1 - 0 > 1/2$ on that edge.

**Example B, flooring shares can create a negative cycle.** Take states $1, 2$ and goal $0$. Edges $1 \to 2$ and $2 \to 1$ cost $1$, edge $1 \to 0$ costs $3/2$ and edge $2 \to 0$ costs $1$. One layer on the identity quotient gives potentials $(0, 3/2, 1)$.

The shares are $1/2$ on $1 \to 2$, $-1/2$ on $2 \to 1$, $3/2$ on $1 \to 0$ and $1$ on $2 \to 0$. Flooring each share at $D = 1$ gives $0$ and $-1$ around the 2-cycle, so the cycle has total share $-1$.

The residual costs stay non-negative, so a check that only asks whether the shares sum to at most the cost passes. The check in 4.1 also rejects negative shares, so it would catch this. But the shares now contain a negative cycle, and the distance under them is not defined.

**The safe rule.** Before solving layer $j$, replace its input costs by $\lfloor D \cdot c_{j-1}(e) \rfloor / D$. Solve on those costs and take the shares from the resulting potentials. Pass on the exact residual $c_j = c_{j-1} - s_j$.

Operator costs are non-negative, so $c_0 \ge 0$. Assume $c_{j-1} \ge 0$. Flooring is monotone, so the quotient weight is the floor of the least concrete residual. The potential $h_j$ is a distance under floored costs, so on crossing edges $s_j(e) \le \lfloor D \cdot c_{j-1}(e) \rfloor / D \le c_{j-1}(e)$. On self-loops of the quotient $s_j = 0$. So $c_j \ge 0$.

Summing the shares telescopes to $H(u) - H(v) \le c(e)$ for $H = \sum_j h_j \circ \pi_j$. Every $h_j$ lies on the grid $1/D$. In Example A the rule gives $h = (0, 0, 0)$. In Example B it gives shares $0$ and $0$ around the cycle.

The proof gives no bound on how much value the rule loses against the exact tower. The bound in 4.3 is for one share on the original costs only.

**Costs already on the grid need no rounding.** If every input cost is a multiple of $1/D$, every distance is a sum of such costs. Then every potential, every share and every residual is again a multiple of $1/D$. Flooring changes nothing, and all three rules give the same tower.

**Controls that must fail for 4.4.** Tests 09 to 11 check Example A, Example B and the safe rule on 40 small graphs at $D = 1, 2, 4$ in four quotient orders. The on-grid statement is checked on 320 further cases.

- Flooring potentials is rejected on Example A and on some of the small graphs (tests 09 and 11).
- Flooring shares is rejected on Example B by the negative-cycle check (test 10).
- The negative-cycle check fires on a corrupted share vector and stays quiet on a repaired one (test 10).
- A summed potential raised by $1/2$ above an edge limit is rejected by the consistency check. So is a raised goal potential (test 11).
- The same graphs on a coarser grid are off the grid, and there the rules differ (test 11).

What this does not show: the share-sum rule in 4.1 is checked by code in the test file, because `verify_independent.py` verifies one potential at a time and has no notion of a partition.
