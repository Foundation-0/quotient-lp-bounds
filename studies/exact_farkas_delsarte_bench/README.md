# Exact-$\mathbb{Q}$ Farkas & Delsarte Dual-Certificate Verifier and Wall-Clock Benchmark

Pure Python 3 stdlib, zero-float, zero-`ast.Div` verification and monotonic wall-clock (`time.perf_counter_ns`, single-thread CPU-only) benchmarking study extending `quotient-lp-bounds` across three exact-$\mathbb{Q}$ primal–dual LP and Farkas families:

1. **Delsarte Krawtchouk Coding LP (`(n, d) = (2m, m)` for `n in {8, 12, 16, 20}`):** Certifies exact Plotkin/Hadamard/Reed–Muller bounds (`16/1`, `24/1`, `32/1`, `40/1`) via exact dual weights $y_1 = 1, y_2 = 1/m$, zero duality gap (`0/1`), full active-support rank `2/2` via checked-divisibility fraction-free integer Gaussian elimination (`fangcheng_rank_z` / `exact_div_z`), and exact `1/1` (`100%`) tightening-gain retention under seeded row/column permutation obfuscation.
2. **Structured 1-Lipschitz Quotient LP + Farkas Flow (`N = 48` vertices, `240` directed edges, `288` LP rows):** Synthesizes exact shortest-path potential $h^*$ and Farkas dual flow $(y^*, z^*)$ (`primal = dual = 535/4`, gap `0/1`, active basis rank `48/48`) verified identically by both dense `O(M N)` and sparse `O(|E| + N)` checkers, retaining exact `1/1` (`100%`) under seeded vertex/edge permutation obfuscation.
3. **Zero-Logarithm Farkas Infeasibility Obstruction (`355/113` 4-Node Cone & `53-TET` Holder Comma):** Certifies global infeasibility of the 4-node interval cone $[355/113, 4], [2, 3], [2, 3], [355/113, 4]$ via exact integer Farkas ray $y \in \mathbb{Z}_{\ge 0}^8$ ($A^\top y = 0, b^\top y = -32/113 < 0$) while certifying both 3-node local sub-cones feasible, paired with exact BigInt Holder comma $3^{53} - 2^{84} = 40{,}432{,}553{,}845{,}953{,}101{,}497{,}907 > 0$.

## Key Security, Purity, & Benchmarking Highlights

- **Closed-Allowlist Pure-$\mathbb{Z}/\mathbb{Q}$ AST Self-Audit:** Reads its own source via `O_NOFOLLOW | O_NONBLOCK` + `fstat(S_ISREG)`, counts visited AST nodes, wraps malformed-source `SyntaxError`/`ValueError` fail-closed (`AST_SYNTAX_ERROR`), and rejects `ast.Div` (`/` and `/=`), `ast.FloorDiv` (`//` and `//=`), `ast.Mod` (`%` and `%=`), `ast.FormattedValue.format_spec`, `float`/`complex` literals and bare `Name` bindings (`float`, `complex`, `format`, `divmod`, `round`, `open`, `eval`, `exec`, `getattr`, `__import__`, `__builtins__`), negative or non-constant exponents in `ast.Pow` (`**` and `**=`) and 2-argument positional `pow(...)`, reflection/formatting/dunder attributes (`.real`, `.imag`, `.conjugate`, `__class__`, `__base__`, `__subclasses__`, `__globals__`, `__format__`, `__truediv__`, `__floordiv__`, `__mod__`, `__pow__`, `__float__`, `__complex__`, `__getattribute__`, `__getattr__`, `__dict__`, `from_float`, `from_decimal`, `fromhex`, `as_integer_ratio`, `format`, `modules`, `time`, `perf_counter`, `sleep`), unallowlisted imports/from-imports/relative imports/wildcards/aliases, unguarded `json.loads(...)` lacking `parse_float=`, local value-position aliasing or rebinding of `Fraction`/`pow`/`type`/`math`/`sys`/`time`/`json`/`os`, 1-arg or string/starred `Fraction(...)`, and bare `assert`s.
- **Strict Non-Symlink JSON, Closed Allowlists, Depth/Digit/Size Caps, & Pinned Raw-Bytes Binding:** `load_strict_json` enforces `O_NOFOLLOW | O_NONBLOCK` + `fstat(S_ISREG)` refusal on symlinks/directories/FIFOs, `1 MiB` streaming byte cap, pre-`json.loads` raw nesting depth cap (`MAX_JSON_DEPTH = 32`), `MAX_INT_DIGITS = 1024` integer/rational digit cap, `object_pairs_hook` duplicate-key rejection, zero floats/NaN/Inf, host path leak rejection, and linear-time NUL/control-char-stripped power/energy telemetry rejection (`energy_power_status = "UNCONTROLLED_LAPTOP_NOT_CLAIMED"`). Callers (`check_certificate_artifact`, `check_benchmark_artifact`) enforce closed top-level and nested key allowlists, exact nanosecond accounting (`total_benchmark_ns == measured_components_sum_ns + unmeasured_setup_and_verify_ns`), `--require-pinned` SHA-256 verification, and exact raw-bytes SHA-256 parity.
- **Honest Monotonic Wall-Clock Results (`wallclock_benchmark_receipt.json`, `time.perf_counter_ns`, `0.562 s << 300 s` budget; `0.497 s` measured loops + `0.065 s` warm-up/setup/residual verification):**
  - On dense integer basis systems (`dim = 12, 16, 20`, 1 untimed warm-up + 5 repeats), checked-divisibility fraction-free integer elimination beats naive dense `Fraction` pivoting by **`3.15x` -> `3.74x` -> `4.15x`** and exact `O(n^2)` residual verification reaches **`10.09x`** at `dim = 20`.
  - On the `N = 48` structured Quotient-LP (`240` edges, 5 repeats), sparse `O(|E| + N)` exact-$\mathbb{Q}$ Farkas verification (`5.54 ms`) beats naive dense `Fraction` basis solving (`188.14 ms`) by **`33.94x`**, dense `O(M N)` matrix checking (`142.51 ms`) by **`25.71x`**, and checked fraction-free elimination (`51.35 ms`) by **`9.26x`**.
  - On the trivial small tractable control (`N = 6`, `30` edges, `50` repeats, apples-to-apples adjacency build inside both timed loops), full dense LP + active-rank certificate synthesis incurs an honest **`21.23x`** slowdown (`38.89 ms` vs. `1.83 ms` direct SPFA evaluation).

## Quick Verification (3-Mode Isolated `-I` Parity)

```bash
for flags in "-I -B" "-I -O -B" "-I -B -W error"; do
  OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 CUDA_VISIBLE_DEVICES="" python3 ${flags} \
    studies/exact_farkas_delsarte_bench/verify_exact_farkas_delsarte.py \
    --check studies/exact_farkas_delsarte_bench/exact_farkas_delsarte_certificate.json --require-pinned
  OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 CUDA_VISIBLE_DEVICES="" python3 ${flags} \
    studies/exact_farkas_delsarte_bench/verify_exact_farkas_delsarte.py \
    --check-bench studies/exact_farkas_delsarte_bench/wallclock_benchmark_receipt.json --require-pinned
  OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 CUDA_VISIBLE_DEVICES="" python3 ${flags} \
    tests/test_exact_farkas_delsarte_bench.py -v
done
```
