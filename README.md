# Certified Quotient-LP and Monotone Deficit Synthesizer

Exact rational synthesis and two-checker verification of globally 1-step-consistent lower bounds on discrete state transition systems.

## Purpose

When a concrete state graph $G = (S, E, c, S_{\text{goal}})$ is too large to enumerate directly, search engines project states onto a smaller quotient graph $Q = (V_Q, E_Q, w_Q, Q_{\text{goal}})$ via $\pi : S \to V_Q$.

Adding auxiliary resource counts or combining heuristics often breaks 1-step consistency ($h(u) - h(v) > c(u, v)$), causing deduplicated A* search to prune optimal routes or overstate unwitnessed lower bounds.

This package provides two exact rational (`fractions.Fraction`, zero `float`) mechanisms backed by machine-checked Lean 4 theorems (`Mcproof.Spec`):

1. **Optimal 1-Lipschitz Quotient LP Repair (`verify.py`)**: Given any quotient graph $Q$ and optional heuristic upper cap $h_0 : V_Q \to \mathbb{Q}_{\ge 0}$, computes the pointwise-maximum consistent potential $h^* \le h_0$ together with a non-negative Farkas dual flow certificate $(y_e, z_u) \ge 0$ proving zero strong-duality gap ($\sum_u \mu_u h^*_u = \sum_e w_e y_e + \sum_u h_0(u) z_u$).
2. **Zero-Self-Loop Monotone Deficit Composition (`Mcproof.Spec.zeroSelfLoop_deficit_composition`)**: Verifies that an auxiliary deficit $\phi$ decreases by at most $c(e)$ on quotient self-loops ($\pi(u) = \pi(v)$) and never decreases on non-self-loop quotient transitions, guaranteeing global 1-step consistency of $h(s) = d_Q(\pi(s)) + \phi(s)$ across $S$ without enumerating $S$.

## Benchmark Instances (`certificate.json`)

| Instance | Domain | Vertices | Edges | Certified Objective (`primal == dual`) |
| :--- | :--- | ---: | ---: | ---: |
| `soko_iii14_transmutation_repair` | `ahrazzle/soko` Druid wall-to-crate boundary + 9-harvest deficit | `40` | `110` | `155` |
| `hardin_strip_w4_antidiag_edit_bound` | `Foundation-0/finite-state-proofs` width-4 OEIS A268991 transfer graph | `48` | `256` | `717/2` |
| `multi_agent_cyclic_switch_partition` | Coupled 2-agent aura routing + cyclic mode-switch parity | `32` | `140` | `80` |

## Reproduce and Verify

Python 3.10+ standard library only (`0` external dependencies, `0` floats):

```sh
python3 -O -B verify.py
python3 -O -B -m unittest discover -s tests -p 'test_*.py' -v
```

`verify_independent.py` shares zero imports with `verify.py`. It parses `certificate.json` through a strict float-rejecting JSON loader and checks non-negativity, goal zeroing, edge Lipschitz inequalities, dual flow conservation, exact strong duality, and zero-self-loop deficit monotonicity.

## Rounding Direction

Flooring each share of a cost partition to a grid of step 1/D keeps non-negative shares within the operator cost. Potentials computed before rounding go stale wherever a distance falls, so they must be recomputed on the rounded costs. The loss per share at a vertex is at most the edges on its shortest path after rounding, divided by D. The proof and controls are in `PROOF.md` section 4, and `tests/test_rounding.py` checks them on the three instances.

These three statements assume non-negative shares. A reduced-cost tower, as in Foundation-0/quotient-lp-bounds draft pull request 5, produces shares of either sign. There, flooring potentials after the fact leaves negative residual costs, and flooring shares can create a negative cycle.

The safe rule is to floor each layer's input costs before solving that layer. Costs already on the 1/D grid need no rounding. `PROOF.md` section 4.4 gives two small exact examples and the argument. Tests 09 to 11 check them on small cases. The loss bound of 4.3 is not shown for the tower.

## What Is Not Proved

- Quotient LP certificates prove 1-Lipschitz consistency and LP optimality on the supplied quotient graph $Q$. Soundness on a concrete domain $S$ additionally requires verifying that every concrete transition $s \to s'$ maps to an edge (or self-loop) in $Q$.
- On infinite families of strip widths, each width $w$ requires its own finite transfer-graph certificate.
