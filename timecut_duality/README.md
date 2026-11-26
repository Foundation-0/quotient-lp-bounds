# Clean-Room Adjacent-Rectangle Time-Cut LP Duality and Pure-`Init` Lean 4.36.0 Package

Self-contained exact rational (`fractions.Fraction`, zero `float`, zero `/` division, zero `//` floor division, zero `**` power operator, zero `math.log`) Python 3.10+ verifier and zero-dependency `Lean 4.36.0` formalization of adjacent-rectangle time-cut linear programming duality, dual balanced-core dominance, integral binary laminar interval-tree dynamic programming, and crossing-advantage witnesses.

## Mathematical Problem and Summary of Certified Results

Given an ordered discrete horizon $\{0, 1, \dots, N - 1\}$ ($N \ge 2$), an **adjacent rectangle** is a Cartesian product $R_{a,b,c} = [a, b) \times [b, c)$ with integer endpoints $0 \le a < b < c \le N$ and cut charge $c(R_{a,b,c}) = \min(b - a, c - b)$.

- **Primal Time-Cut Packing LP ($P_N$):** Maximize $\sum_{a < b < c} c(R_{a,b,c})\, x_{a,b,c}$ over $x_{a,b,c} \ge 0$ subject to unit pair-congestion $\sum_{a \le i < b \le j < c} x_{a,b,c} \le 1$ for every ordered pair $0 \le i < j < N$.
- **Dual Time-Cut Covering LP ($D_N$):** Minimize $\sum_{0 \le i < j < N} y_{i,j}$ over $y_{i,j} \ge 0$ subject to $\sum_{(i,j) \in [a,b) \times [b,c)} y_{i,j} \ge \min(b - a, c - b)$ for every $0 \le a < b < c \le N$.
- **Integral Binary Laminar Interval-Tree Baseline ($T_N$):** Over integral binary recursive partition trees (`IntervalTree` on $N$ contiguous leaves), Bellman dynamic programming gives $T_0 = T_1 = 0$ and $T_n = \max_{1 \le k < n} (T_k + T_{n-k} + \min(k, n - k))$. Note that `CleanRoomTimeCutDuality.lean` formalizes $T_N$ as an upper bound over integral binary `IntervalTree`s of size $\le 20$ (`universal_laminar_tree_upper_bound`), rather than general fractional laminar-supported LP solutions.

### Four Verification Pillars (`verify_timecut_duality.py`)

1. **Exact-$\mathbb{Q}$ Simplex, Strong Duality, and Sharp Threshold $N_{\min} = 18$ (`p1_timecut_lp_and_threshold`):**
   - **Lean 4.36.0 + Python exact-$\mathbb{Q}$:** Universal finite-Fubini weak duality (`universal_weak_duality`), **dual-side** balanced-core dominance (`balanced_core_inRect_le`, `balanced_core_charge_eq`, `balanced_core_dualMass_le`, and for $N = 18$ `dual18_covers_every_valid_rect18`: any nonnegative dual covering balanced cores $[b - h, b) \times [b, b + h)$ covers all valid general adjacent rectangles), universal binary `IntervalTree` upper bound `treeScore t <= laminarTreeOpt (treeSize t)` for `treeSize t <= 20` (`universal_laminar_tree_upper_bound`), 18-leaf attainment `T_{18} = 35` (`witnessTree18_attains_35`, alongside table lookups `T_{17} = 33`, `T_{18} = 35`, `T_{19} = 37`), universal $N = 18$ primal/dual optimality $P_{18} = D_{18} = 107/3 > 35 = T_{18}$ (`cleanRoomPrimal18_pair_congestion`, `cleanRoomPrimal18_beats_every_laminar_tree`, `dual18_covers_every_valid_rect18`, `n18_universal_optimum_upper_bound`), and the $N = 19$ half-integral primal lower-bound witness `cleanRoomPrimal19` achieving $76/2 = 38 \ge T_{19} + 1$ over every 19-leaf binary `IntervalTree` (`cleanRoomPrimal19_pair_congestion`, `cleanRoomPrimal19_integer_gap_over_every_tree`).
   - **Python exact-$\mathbb{Q}$ only (not formalized in Lean):** Primal-side balanced-core symmetry reduction inside the exact-$\mathbb{Q}$ Bland-rule simplex solver; LP optima and exhaustive $\binom{N+1}{3}$ general-rectangle dual coverage across all $2 \le N \le 20$ for $N \ne 18$; sharpness of $N_{\min} = 18$ ($P_N = T_N$ for $2 \le N \le 17$); exact dyadic ceiling $P_{2^d} = T_{2^d} = d \cdot 2^{d-1}$ at $N \in \{2, 4, 8, 16\}$; the matching $N = 19$ dual upper bound $D_{19} = 38$; $P_{20} = D_{20} = 122/3 > 40 = T_{20}$ (gap $+2/3$); and explicit binary-tree attainment of `laminarTreeOpt N` for $N \ne 18$.
2. **Banked CNF Bit-Length Envelope and 5-Clause Port Gadget (`p2_banked_cnf_envelope_and_port_gadget`):**
   - **Lean 4.36.0 + Python:** Diophantine decimal-identifier inequalities $10^3 < 2^{10} < 10^4$, $9 \cdot 10^6 < 2^{24}$, and $2^{24} < 2 \cdot 10^{24}$ (`eight_bank_diophantine_sublinearity`), and exhaustive $\{0, 1\}^6$ verification that the 5-clause degree-$\ge 3$ port gadget has $2(a + b + c)$ satisfying extensions for every port assignment $(a, b, c)$ (`five_clause_gadget_exact_multiplicity`, including `0` extensions at $(0, 0, 0)$).
   - **Python exact-$\mathbb{Q}$ only (not formalized in Lean):** Full $k \in \{8, 12, 16, 20, 24\}$ 8-bank ASCII-to-raw bit-length ratio envelope $[48, 304]$ (tightening below $150$ at $k = 24$, whereas naive 2-bank variable reservation exceeds $10^{16}$ per row), simultaneous $\bmod\,2$ and $\bmod\,3$ Tseitin charge mismatches on the canonical $t = 2^k - 3$ vertex count ($2^k \equiv 4 \pmod 6 \implies t \equiv 1 \pmod{2, 3}$ for $4 \mid k$), and strict single-clause-deletion irredundancy of all `5` gadget clauses at $(0, 0, 0)$.
3. **Zero-Dependency `Lean 4.36.0` Package Binding (`p3_lean4_package`):**
   - Binds all `5` files in `timecut_duality/lean/` by raw-bytes SHA-256 (refusing symlinks and forbidding `lakefile.lean`), enforces `lake-manifest.json` `"packages": []` and strict TOML parsing of `lakefile.toml` (blocking all spaced/quoted `require` forms), runs a character-literal-safe (`'"'`, `'\"'`, `'\''`, `"\\"`) R13b static gate, and supports cold `env -i` `lean`/`lake` `4.36.0` version-checked `lake build` + standalone `leanchecker` module kernel replay (`CleanRoomTimeCutDuality`, `AxiomAudit`) + live `lake env lean AxiomAudit.lean` axiom audit (`0` `Classical.choice`, `0` `bv_decide`, `0` `native_decide`, `0` `sorryAx`).
4. **Crossing Geometry and Characteristic-2 vs. $\mathbb{Q}$ Obstructions (`p4_crossing_c1p_and_char2_rank_obstructions` — Python exact-$\mathbb{Q}$ / $\mathbb{F}_2$ only):**
   - **Python only (not formalized in Lean):** Every active interval $[a, c)$ in the $N = 18$ optimal packing satisfies the 1D Consecutive-Ones Property (`C1P`), yet laminar nesting breaks across **`71` strictly crossing active interval pairs**; characteristic-$2$ vs. $\mathbb{Q}$ rank drop $\operatorname{rank}_{\mathbb{F}_2}(J_3 - I_3) = 2 < 3 = \operatorname{rank}_{\mathbb{Q}}(J_3 - I_3)$; and $18$-cell grid cycle separation $\gcd(3, 6) = 3 \ne 1 = \gcd(2, 9)$.

## Pure-`Init` `Lean 4.36.0` Theorem Catalog (`30` Theorems)

All `30` theorems in `lean/CleanRoomTimeCutDuality.lean` compile on `leanprover/lean4:v4.36.0` using `Init` only (`0` external imports) and are audited in `lean/AxiomAudit.lean`:

- **Grid Sums & Finite Fubini Weak Duality (`8`):** `gridSum_zero`, `gridSum_add`, `gridSum_mul_left`, `gridSum_mul_right`, `gridSum_mono`, `fubini_rect_pair_exchange`, `scale_primal_le_weighted_dual`, `universal_weak_duality`.
- **Boolean Arithmetic & Dual Balanced-Core Dominance (`6`):** `ble_false_gt`, `and4_ble_mp`, `and4_ble_mpr`, `balanced_core_inRect_le`, `balanced_core_charge_eq`, `balanced_core_dualMass_le`.
- **Binary Laminar Interval-Tree DP Upper Bound & $N = 18$ Witness (`4`):** `treeSize_pos`, `laminar_bellman_subadditive_le20`, `universal_laminar_tree_upper_bound`, `witnessTree18_attains_35`.
- **Universal $N = 18$ ($107/3$) Primal & Dual Optimality (`8`):** `cleanRoomPrimal18_pair_congestion`, `cleanRoomPrimal18_beats_every_laminar_tree`, `dual18_total_mass_eq_107`, `dual18_covers_all_81_balanced_cores`, `checkBalancedAtCenter_sound`, `checkAllBalanced18_sound`, `dual18_covers_every_valid_rect18`, `n18_universal_optimum_upper_bound`.
- **$N = 19$ Primal Integer-Gap Witness, Diophantine Scaling Inequalities & 5-Clause Gadget (`4`):** `cleanRoomPrimal19_pair_congestion`, `cleanRoomPrimal19_integer_gap_over_every_tree`, `eight_bank_diophantine_sublinearity`, `five_clause_gadget_exact_multiplicity`.

## Recorded Digest Manifest (`timecut_duality_certificate.json`)

| Artifact / Digest Field | SHA-256 |
| :--- | :--- |
| `payload_sha256` | `9e791e49e4cf52c79486e137541e002f4e7ab9ae8f150064457991b9d2d55118` |
| `certificate_sha256` | `253ad3c6755031964b3051a47b183bfeb30538a0b531d5cc7c3dbefd2bd84296` |
| `lean/AxiomAudit.lean` | `67bf4fd74ead82790d2072b68f81b7e5a801a2bc1fed70c336d8d29ee26ddf04` |
| `lean/CleanRoomTimeCutDuality.lean` | `63b1d4995dffd148c3973719b29f4f0cff72b137f4cc9744f4fd29558499cb05` |
| `lean/lake-manifest.json` | `6b8f8f994fad868af7aebe620a2431332757369d66d84988a6b592b1c1b08edc` |
| `lean/lakefile.toml` | `73f9d0f11938a8bcd6c303c9f6c5f2f4f3b35f326c3030c5939587ca965f2e09` |
| `lean/lean-toolchain` | `582a63f8f9c5128067b688778c1051cf1464c3ca9d57b9325025c051c29b774a` |

## Reproduce and Verify

Python 3.10+ standard library only (`0` external packages; tamper/validation failures exit fail-closed with `RC=2` and structured JSON on `stderr`):

```sh
python3 -I -B timecut_duality/verify_timecut_duality.py --check
python3 -I -O -B timecut_duality/verify_timecut_duality.py --check
python3 -I -B timecut_duality/test_timecut_duality_r5.py
```

When `leanprover/lean4:v4.36.0` (`lean`, `lake`, `leanchecker`) is installed locally, run cold isolated compilation, standalone `leanchecker` kernel replay, and live `#print axioms` verification across all `5` package files (copied in-memory to an ephemeral temporary directory so `.lake/` is never written into the repository):

```sh
python3 -I -B timecut_duality/verify_timecut_duality.py --live-lean
```

Additional CLI modes: `--write` (regenerate canonical `timecut_duality_certificate.json`), `--json` (emit canonical JSON to stdout), `--cert-path <path>`, and `--lean-dir <dir>`.

## What Is Not Proved

- Exact LP optima $P_N$ and integral binary `IntervalTree` DP optima $T_N$ are solved and certified on the finite horizon range $2 \le N \le 20$; equivalence between fractional laminar-supported LPs and integral binary `IntervalTree`s, as well as asymptotic crossing-ratio behavior as $N \to \infty$, is not proved here.
- This package certifies unconditional combinatorial LP duality, banked CNF bit-length envelopes, and finite gadget/rank obstructions; it does not claim unconditional circuit or Turing time lower bounds for 3-SAT.
