# Technical Report: Exact-$\mathbb{Q}$ Farkas & Delsarte Dual-Certificate Verification and Monotonic Wall-Clock Benchmark

- **Study Bundle:** `studies/exact_farkas_delsarte_bench/`
- **Execution Regime:** Pure Python 3 stdlib (exact arithmetic strictly via `int`, `fractions.Fraction`, `math.gcd`, `math.isqrt`; stdlib CLI/IO/AST/policy modules `argparse`, `ast`, `collections.deque`, `errno.{EISDIR,ENXIO}`, `hashlib`, `json`, `os`, `pathlib.Path`, `re`, `stat`, `sys`, `time.perf_counter_ns`, `typing`, `unicodedata`), single-thread CPU-only (`CUDA_VISIBLE_DEVICES=""`, `OPENBLAS_NUM_THREADS=1`, `OMP_NUM_THREADS=1`), monotonic wall-clock `time.perf_counter_ns` (not `process_time_ns`), `energy_power_status = UNCONTROLLED_LAPTOP_NOT_CLAIMED` (zero power or energy telemetry claimed or reported).
- **Canonical Self-Bound & Pinned Artifacts:**
  - Deterministic certificate: `exact_farkas_delsarte_certificate.json` (`payload_sha256 = 2b619307fd3cc0b12636921152f9d2ee4b0d5102bbefeef776b57aa8fef92cd3`, `certificate_sha256 = 29b99332981c2ad709a7d778e42b60cc82c1f73cc8697788239e4db129335673`).
  - Live integer-nanosecond benchmark receipt: `wallclock_benchmark_receipt.json` (`payload_sha256 = 9e6aab8c060200595a2dfd2c8bbe9a000f65bb9db9f2652e1f101893115c6a9d`, `benchmark_sha256 = ddb8d4f75ecd3eda8cffb4329a8b0a778a7a6985dd3094e98692dab2cfcdc6f9`).

---

## 1. Hardened Pure-$\mathbb{Z}/\mathbb{Q}$ AST Purity & Strict JSON Binding

`verify_exact_farkas_delsarte.py` runs an internal closed-allowlist AST self-audit (`verify_ast_purity`) over non-symlink source bytes (`read_regular_bytes_nofollow(Path(__file__))`) during every `--write` and `--check`:
- Counts all visited AST nodes (`visited_nodes > 0`), wraps malformed-source `SyntaxError`/`ValueError` fail-closed (`AST_SYNTAX_ERROR`), and rejects `ast.Div` (`/` and `/=`), `ast.FloorDiv` (`//` and `//=`), `ast.Mod` (`%` and `%=`), `ast.FormattedValue.format_spec` (`f"{1:.3f}"`), `float`/`complex` literals, bare `Name` bindings for `float`/`complex`/`format`/`divmod`/`round`/`open`/`memoryview`/`eval`/`exec`/`getattr`/`__import__`/`__builtins__`, negative or non-constant exponents in `ast.Pow` (`**` and `**=`) and 2-argument positional `pow(...)`, reflection/formatting/dunder attributes (`.real`, `.imag`, `.conjugate`, `cast`, `literal_eval`, `__class__`, `__base__`, `__bases__`, `__mro__` outside the exact `_is_float_or_complex` `GeneratorExp`, `__subclasses__`, `__globals__`, `__format__`, `__truediv__`, `__floordiv__`, `__mod__`, `__pow__`, `__float__`, `__complex__`, `__getattribute__`, `__getattr__`, `__dict__`, `from_float`, `from_decimal`, `fromhex`, `as_integer_ratio`, `format`, `format_map`, `modules`, `time`, `perf_counter`, `sleep`), unallowlisted imports/from-imports/wildcards/relative imports/import aliases (closed allowlists `ALLOWED_IMPORT_MODULES`, `ALLOWED_FROM_IMPORTS`, `ALLOWED_MODULE_ATTRS`), unguarded `json.loads(...)` lacking `ast.Name`-bound `parse_float=` and `parse_constant=`, local value-position aliasing or rebinding of `Fraction`/`pow`/`type`/`math`/`sys`/`time`/`json`/`os`, 1-argument or string/starred `Fraction(...)`, and bare `assert`s.
- Strict JSON loading (`load_strict_json` + `read_regular_bytes_nofollow` / `write_regular_bytes_nofollow`) enforces `O_NOFOLLOW | O_NONBLOCK` + `ENXIO`/`EISDIR`/`fstat(S_ISREG)` symlink/FIFO/directory refusal, `1 MiB` (`MAX_FILE_BYTES`) streaming byte cap, pre-`json.loads` raw nesting depth cap (`_check_json_raw_depth` + iterative `check_json_tree_clean`, `MAX_JSON_DEPTH = 32`), `MAX_INT_DIGITS = 1024` integer and rational digit bounds, `object_pairs_hook` duplicate-key rejection, zero floats/NaN/Inf, host path leak rejection, and NUL/control-char-stripped linear-time power/energy telemetry rejection (`RAPL`/`NVML`/`nvidia-smi`/`j/tok`/`W/tok`/`energy: 12`/SI units). Callers (`check_certificate_artifact` and `check_benchmark_artifact`) additionally enforce closed top-level and nested key allowlists, `--require-pinned` SHA-256 verification across CLI modes (rejected fail-closed on live `--benchmark`), and exact raw-bytes SHA-256 parity against canonical serialization.

---

## 2. Certified Mathematical Families (`exact_farkas_delsarte_certificate.json`)

### 2.1 Family 1 — Exact-$\mathbb{Q}$ Delsarte Krawtchouk Coding LP (`(n, d) = (2m, m)`)

For binary codes with $n = 2m$ and $d = m$, the exact Krawtchouk dual polynomial $F(i) = 1 + K_1(i) + \frac{1}{m} K_2(i) = \frac{2}{m}(m - i)(2m - i)$ yields dual multipliers $y_1 = 1, y_2 = 1/m, y_{k \ge 3} = 0$ matching the primal Plotkin/Hadamard/Reed–Muller distance distribution $A_m^* = 4m - 2, A_{2m}^* = 1$ with `0/1` duality gap, full active-support rank `2/2` (checked exact Bareiss divisibility), and exact `1/1` (`100%`) gain retention under row/column permutations:

| Instance `(n, d)` | Singleton | Hamming | Exact Delsarte Bound (`1 + dual_obj`) | Tightening vs. Hamming | Dual Nonzeros `(y_1, y_2)` | Active Rank | Obfuscated Perm Retention |
| :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| `(8, 4)` ($H_8$) | `32` | `28` | **`16/1`** | `12/1` | `(1/1, 1/4)` | `2/2` | — |
| `(12, 6)` ($H_{12}$) | `128` | `51` | **`24/1`** | `27/1` | `(1/1, 1/6)` | `2/2` | — |
| `(16, 8)` (`RM(1,4)`) | `512` | `94` | **`32/1`** | `62/1` | `(1/1, 1/8)` | `2/2` | **`1/1` (`100%`)** (`154016/154116`) |
| `(20, 10)` ($H_{20}$) | `2,048` | `169` | **`40/1`** | `129/1` | `(1/1, 1/10)` | `2/2` | **`1/1` (`100%`)** (`154020/154120`) |

### 2.2 Family 2 — Structured `N = 48` 1-Lipschitz Quotient LP + Farkas Dual Flow

On the $6 \times 4 \times 2$ cyclic mode-switch quotient graph (`N = 48` vertices, `240` directed edges, `288` LP rows):
- **Original instance:** `primal_obj = dual_obj = 535/4`, gap `0/1`, verified identically by dense `verify_lp_primal_dual_q` (`active_support_rank = 48/48`) and sparse `O(|E| + N)` `verify_quotient_lp_sparse_q`.
- **Seeded vertex/edge permutation obfuscation (`seeds 154048/154049`, re-synthesized from scratch):** `primal_obj = dual_obj = 535/4`, `active_support_rank = 48/48`, exact bound retention **`1/1` (`100%`)**.

### 2.3 Family 3 — Zero-Logarithm Farkas Infeasibility Obstruction

- On the 4-node Zu Chongzhi `355/113` interval cone ($[355/113, 4], [2, 3], [2, 3], [355/113, 4]$), exact integer Farkas ray $y = (0, 1, 1, 0, 1, 0, 0, 1) \in \mathbb{Z}_{\ge 0}^8$ satisfies $A^\top y = 0$ and $b^\top y = \mathbf{-32/113 < 0}$, certifying global infeasibility with zero logarithms or floating-point arithmetic.
- Both 3-node local sub-cones are certified explicitly feasible: `{0, 1, 2}` via $(355/113, -16/113)$ and `{1, 2, 3}` via $(307/113, 16/113)$, paired with exact BigInt `53-TET` Holder comma $3^{53} - 2^{84} = 40{,}432{,}553{,}845{,}953{,}101{,}497{,}907 > 0$.

---

## 3. Monotonic Wall-Clock Benchmark & Honest Small-Control Slowdown (`wallclock_benchmark_receipt.json`)

Measured via integer `time.perf_counter_ns()` with untimed 1-iteration warm-ups for both linear solvers (`dim = 12, 16, 20`), both `N = 48` verifiers (`verify_quotient_lp_sparse_q` and `verify_lp_primal_dual_q`; the `48x48` active-basis solvers run directly across 5 repeats), and both `N = 6` control paths, with exact cross-checked solutions ($x_j = j + 1$ and $x = h^*$), zero-residual verification, and exact nanosecond accounting (`measured_components_sum_ns = 497,382,822 ns` + `unmeasured_setup_and_verify_ns = 64,974,476 ns` == `total_benchmark_ns = 562,357,298 ns` = **`0.562 s << 300 s`**):

### 3.1 Dense Structured Integer Linear Systems (`5` Timed Repeats After Warm-Up)

| Dimension | Fraction-Free Elimination (`ms`) | Naive Dense `Fraction` (`ms`) | `O(n^2)` Residual Verify (`ms`) | Elimination vs. Naive (`Q` / approx) | Verify vs. Naive (`Q` / approx) |
| :---: | :---: | :---: | :---: | :---: | :---: |
| `12 x 12` | `1.72` | `5.40` | `1.09` | `1800626/572147` (**`3.15x`**) | `1800626/362483` (**`4.97x`**) |
| `16 x 16` | `3.91` | `14.60` | `1.99` | `14595812/3905353` (**`3.74x`**) | `7297906/994481` (**`7.34x`**) |
| `20 x 20` | `7.28` | `30.16` | `2.99` | `6031753/1455162` (**`4.15x`**) | `30158765/2987584` (**`10.09x`**) |

### 3.2 Structured `N = 48` Quotient-LP (`240` Edges, `288` Rows, `5` Repeats)

| Routine | Total Time (`ms`) | Exact Rational Ratio vs. Naive Solve |
| :--- | :---: | :---: |
| `active_basis_naive_fraction` (`48x48` dense `Fraction` pivoting) | `188.14` | `1/1` (`1.00x`, baseline) |
| `dense_lp_verify` (`O(M N)` dense matrix product) | `142.51` | `188142319/142507786` (`1.32x`) |
| `active_basis_fangcheng` (`48x48` checked fraction-free elimination) | `51.35` | `188142319/51345192` (**`3.66x`**) |
| **`sparse_farkas_verify` (`O(|E| + N)` exact-$\mathbb{Q}$ flow check)** | **`5.54`** | **`188142319/5543223` (`33.94x` vs. naive; `25.71x` vs. dense verify; `9.26x` vs. elimination)** |

### 3.3 Honest Small-Instance Tractable Slowdown Control (`N = 6`, `30` Edges, `50` Repeats)

- **Uncertified direct SPFA distance evaluation (including reverse adjacency build inside timed loop):** `1.83 ms` (`1,831,768 ns`).
- **Full certified dense LP + Farkas dual + active-rank pipeline:** `38.89 ms` (`38,894,480 ns`).
- **Measured Slowdown Ratio:** **`4861810/228971` (`≈ 21.23x` slower, `slowdown_observed = true`)**.
- **Scope Caveat:** On trivial small graphs, full dense matrix assembly and rank certification add substantial constant-factor overhead compared to uncertified distance evaluation; exact-$\mathbb{Q}$ verification wins decisively once sparsity (`33.94x`) and integer elimination (`3.66x`–`4.15x`) replace dense rational pivoting on structured instances.

---

## 4. Adversarial Refusal & Mutation Verification Summary

- **Refusal Suite (`test_exact_farkas_delsarte_r5.py`):** Kills sign-flipped duals (`-1/10^9`), `1/10^9` primal/dual/gap violations (both `"max_le"` and `"min_ge"` + sparse Quotient-LP + Farkas), ragged Farkas matrices, negative/duplicate `active_cols`/`active_rows`, out-of-range sparse goal/edge vertices, non-`Fraction` float injection across all inputs, inexact Bareiss division, non-canonical `parse_q_str` and `1024`-digit integer/rational limits, exact `1/1` permutation retention, all `136` AST impurity controls (`135` source snippets + non-string rejection), `93` forbidden energy-claim payloads (`0` false positives on `54` clean values + linear-time CPU-timed ReDoS stress guard), pre-`json.loads` and iterative JSON depth caps (`32` pass / `33`, `500`, & `5000` fail), `O_NOFOLLOW | O_NONBLOCK` symlink/unread-FIFO/open-FIFO/directory/device/`1 MiB` read/write refusal, duplicate JSON keys, closed nested allowlists, pinned SHA mismatches across all CLI modes, exact nanosecond accounting tampers, and `rc == 2` I/O failures.
- **Exhaustive Mutation & `BoolOp` Coverage (External Verifier Runs):** `288 / 288 = 100.0%` killed (`0` survived, `null_mutant = passed`, `truncated = False`) on both default and `--guards require_ok`, plus `66 / 66 = 100.0%` whole-file AST `BoolOp` kill rate.
- **CI Integration:** `tests/test_exact_farkas_delsarte_bench.py` runs automatically under `.github/workflows/verify.yml` with `--require-pinned` without modifying any existing repository file or `SHA256SUMS`.
