#!/usr/bin/env python3
"""Clean-Room Exact-Q and Lean 4.36.0 Verifier for Adjacent-Rectangle Time-Cut Duality.

Certifies:
  1. Exact-Q Bland-rule simplex & 2D-prefix-sum primal-dual strong-duality oracle
     for adjacent-rectangle time-cut packing on {0, ..., N - 1} (2 <= N <= 20),
     establishing zero laminar-crossing gap for all 2 <= N <= 17, the sharp minimal
     crossing-advantage threshold N_min = 18 (P_18 = 107/3 > 35 = T_18, gap +2/3),
     and the first full-integer crossing gap at N = 19 (P_19 = 38 > 37 = T_19, gap +1).
  2. Exact Diophantine 8-bank vs. naive 2-bank decimal-identifier CNF bit-length
     envelope across k in {8, 12, 16, 20, 24}, simultaneous mod-2 and mod-3 Tseitin
     charge obstructions, and exhaustive 5-clause port-gadget multiplicity over {0, 1}^6.
  3. Zero-dependency pure-Init Lean 4.36.0 package binding (all 5 package files bound
     by raw-bytes SHA-256, char-literal-safe R13b static gate, 30/30 theorems, and
     optional cold env -i lake build + standalone leanchecker kernel replay).
  4. Structural obstructions separating 1D Consecutive-Ones Property (C1P) from laminar
     tree nesting at N = 18 (71 strictly crossing active interval pairs), 18-cell grid
     cycle counts, and characteristic-2 vs. Q matrix rank on J_3 - I_3 (2 < 3).
"""

import argparse
import ast
import errno
import fractions
import hashlib
import itertools
import json
import math
import os
import pathlib
import re
import shutil
import stat
import subprocess
import sys
import tempfile
import typing


SCHEMA_VERSION = "quotient_lp_bounds.cleanroom_timecut_duality.v1"
ARITHMETIC_DOMAIN = "exact_Z_Q_GF2_stdlib_zero_floats_zero_div_zero_pow_zero_logs"

SCRIPT_DIR = pathlib.Path(__file__).resolve().parent
SELF_SOURCE_PATH = pathlib.Path(__file__).resolve()
DEFAULT_CERT_PATH = SCRIPT_DIR.joinpath("timecut_duality_certificate.json")
DEFAULT_LEAN_DIR = SCRIPT_DIR.joinpath("lean")

HEX_LOWER = frozenset("0123456789abcdef")

MAX_FILE_BYTES = 1_048_576
_DIR_OPEN_FLAGS = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW | os.O_NONBLOCK
_FILE_OPEN_FLAGS = os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK
_WRITE_OPEN_FLAGS = os.O_WRONLY | os.O_CREAT | os.O_TRUNC | os.O_NOFOLLOW | os.O_NONBLOCK

ALLOWED_STDLIB_IMPORTS = frozenset(
    {
        "argparse",
        "ast",
        "errno",
        "fractions",
        "hashlib",
        "itertools",
        "json",
        "math",
        "os",
        "pathlib",
        "re",
        "shutil",
        "stat",
        "subprocess",
        "sys",
        "tempfile",
        "typing",
    }
)

ALLOWED_OS_ATTRS = frozenset(
    {
        "open",
        "read",
        "write",
        "close",
        "fstat",
        "listdir",
        "mkfifo",
        "O_RDONLY",
        "O_WRONLY",
        "O_CREAT",
        "O_TRUNC",
        "O_DIRECTORY",
        "O_NOFOLLOW",
        "O_NONBLOCK",
    }
)

REQUIRED_JSON_LOADS_HOOKS = (
    ("object_pairs_hook", "_reject_duplicate_json_keys"),
    ("parse_int", "_parse_bounded_json_int"),
    ("parse_float", "_reject_json_float"),
    ("parse_constant", "_reject_json_constant"),
)

ALLOWED_DUNDER_NAMES = frozenset({"__name__", "__file__"})

FORBIDDEN_BARE_NAMES = frozenset(
    {
        "float",
        "complex",
        "Decimal",
        "type",
        "divmod",
        "format",
        "repr",
        "ascii",
        "pow",
        "eval",
        "exec",
        "compile",
        "getattr",
        "vars",
        "globals",
        "locals",
        "dir",
        "setattr",
        "delattr",
        "open",
        "input",
        "breakpoint",
        "memoryview",
    }
)

FORBIDDEN_ATTR_NAMES = frozenset(
    {
        "from_float",
        "from_decimal",
        "as_integer_ratio",
        "fromhex",
        "literal_eval",
        "format",
        "format_map",
        "cast",
        "real",
        "imag",
        "conjugate",
        "modules",
        "builtins",
        "float_info",
        "pi",
        "tau",
        "inf",
        "nan",
    }
)

EXPECTED_LEAN_FILES = (
    "AxiomAudit.lean",
    "CleanRoomTimeCutDuality.lean",
    "lake-manifest.json",
    "lakefile.toml",
    "lean-toolchain",
)

EXPECTED_30_THEOREMS = (
    "gridSum_zero",
    "gridSum_add",
    "gridSum_mul_left",
    "gridSum_mul_right",
    "gridSum_mono",
    "fubini_rect_pair_exchange",
    "scale_primal_le_weighted_dual",
    "universal_weak_duality",
    "ble_false_gt",
    "and4_ble_mp",
    "and4_ble_mpr",
    "balanced_core_inRect_le",
    "balanced_core_charge_eq",
    "balanced_core_dualMass_le",
    "treeSize_pos",
    "laminar_bellman_subadditive_le20",
    "universal_laminar_tree_upper_bound",
    "witnessTree18_attains_35",
    "cleanRoomPrimal18_pair_congestion",
    "cleanRoomPrimal18_beats_every_laminar_tree",
    "dual18_total_mass_eq_107",
    "dual18_covers_all_81_balanced_cores",
    "checkBalancedAtCenter_sound",
    "checkAllBalanced18_sound",
    "dual18_covers_every_valid_rect18",
    "n18_universal_optimum_upper_bound",
    "cleanRoomPrimal19_pair_congestion",
    "cleanRoomPrimal19_integer_gap_over_every_tree",
    "eight_bank_diophantine_sublinearity",
    "five_clause_gadget_exact_multiplicity",
)

LEAN_COMMON_FORBIDDEN_RULES: tuple[tuple[str, re.Pattern[str]], ...] = (
    ("LEAN4_SORRY", re.compile(r"\bsorry\b|\bsorryAx\b")),
    ("LEAN4_ADMIT", re.compile(r"\badmit\b")),
    ("LEAN4_AXIOM_DECL", re.compile(r"(?m)^\s*(?:private\s+|protected\s+)?axiom\b")),
    ("LEAN4_UNSAFE", re.compile(r"(?<!\.)\bunsafe\b")),
    ("LEAN4_NATIVE_DECIDE", re.compile(r"\bnative_decide\b")),
    ("LEAN4_BV_DECIDE", re.compile(r"\bbv_decide\b|\bbv_normalize\b|Std\.Tactic\.BVDecide")),
    ("LEAN4_OF_REDUCE_BOOL", re.compile(r"\bofReduceBool\b|\btrustCompiler\b")),
    ("LEAN4_CLASSICAL", re.compile(r"\bClassical\b|\bnoncomputable\b")),
    ("LEAN4_SET_OPTION", re.compile(r"\bset_option\b")),
    ("LEAN4_FRENCH_QUOTE", re.compile(r"[«»]")),
    ("LEAN4_META_EVAL", re.compile(r"#eval\b|#reduce\b|\brun_meta\b")),
)


# ---------------------------------------------------------------------------
# Fail-Closed Primitives, Strict JSON Loader & Hardened Pure-Q AST Guard
# ---------------------------------------------------------------------------


def require_ok(cond: bool, msg: str) -> None:
    """Fail-closed runtime invariant check preserved under python3 -O."""
    if not cond:
        raise ValueError(msg)


def is_exact_int(val: typing.Any) -> bool:
    """Return True iff val is an int and not a bool."""
    return isinstance(val, int) and not isinstance(val, bool)


def require_fraction(val: typing.Any, name: str) -> fractions.Fraction:
    """Require an exact fractions.Fraction instance."""
    require_ok(isinstance(val, fractions.Fraction), f"{name} must be Fraction")
    return val


def q_frac(num: typing.Any, den: typing.Any = 1) -> fractions.Fraction:
    """Construct an exact Fraction from validated exact ints num and den != 0."""
    require_ok(is_exact_int(num), "numerator must be exact int")
    require_ok(is_exact_int(den), "denominator must be exact int")
    require_ok(den != 0, "denominator must be nonzero")
    return fractions.Fraction(num, den)


def q_div(lhs: fractions.Fraction, rhs: fractions.Fraction) -> fractions.Fraction:
    """Exact rational division lhs / rhs without using Python's division operator."""
    require_fraction(lhs, "lhs")
    require_fraction(rhs, "rhs")
    require_ok(rhs.numerator != 0, "rational division by zero")
    return fractions.Fraction(lhs.numerator * rhs.denominator, lhs.denominator * rhs.numerator)


def int_pow_nonneg(base: typing.Any, exp: typing.Any) -> int:
    """Exact integer power base^exp for exact int base and exact int 0 <= exp <= 256."""
    require_ok(is_exact_int(base), "base must be exact int")
    require_ok(is_exact_int(exp), "exp must be exact int")
    require_ok(0 <= exp, "exp must be >= 0")
    require_ok(exp <= 256, "exp exceeds bounded limit 256")
    acc = 1
    for _ in range(exp):
        acc *= base
    return acc


def is_hex64(val: typing.Any) -> bool:
    """Return True iff val is a 64-character lowercase hexadecimal string."""
    return isinstance(val, str) and len(val) == 64 and set(val) <= HEX_LOWER


def q_to_str(val: fractions.Fraction) -> str:
    """Serialize Fraction canonically as 'num/den'."""
    require_fraction(val, "val")
    return f"{val.numerator}/{val.denominator}"


def str_to_q(text: typing.Any, name: str) -> fractions.Fraction:
    """Parse canonical 'num/den' string into exact reduced Fraction."""
    require_ok(isinstance(text, str), f"{name} must be str")
    num_s, _, den_s = text.partition("/")
    num = int(num_s, 10)
    den = int(den_s, 10)
    require_ok(den > 0, f"{name} denominator must be positive")
    frac = q_frac(num, den)
    require_ok(q_to_str(frac) == text, f"{name} must be in canonical reduced form")
    return frac


def _reject_duplicate_json_keys(pairs: list[tuple[str, typing.Any]]) -> dict[str, typing.Any]:
    """Reject duplicate JSON object keys at every nesting depth."""
    out: dict[str, typing.Any] = {}
    for key, val in pairs:
        require_ok(key not in out, f"duplicate JSON key: {key}")
        out[key] = val
    return out


def _reject_json_float(token: str) -> typing.Any:
    """Reject JSON float tokens."""
    raise ValueError(f"JSON float literal forbidden: {token}")


def _reject_json_constant(token: str) -> typing.Any:
    """Reject JSON NaN / Infinity / -Infinity tokens."""
    raise ValueError(f"JSON non-standard constant forbidden: {token}")


def _parse_bounded_json_int(token: str) -> int:
    """Parse JSON integer token rejecting excessive digit lengths (> 64 chars) and -0."""
    require_ok(len(token) <= 64, "JSON integer literal exceeds 64 chars")
    require_ok(token != "-0", "JSON negative zero integer forbidden")
    return int(token, 10)


def _check_json_text_depth(raw_text: str, max_depth: int = 32) -> None:
    """Iteratively bound JSON container nesting depth <= max_depth prior to json.loads."""
    depth = 0
    in_str = False
    escaped = False
    for ch in raw_text:
        if in_str:
            if escaped:
                escaped = False
            elif ch == "\\":
                escaped = True
            elif ch == '"':
                in_str = False
        else:
            if ch == '"':
                in_str = True
            elif ch in ("{", "["):
                depth += 1
                require_ok(depth <= max_depth, "JSON nesting depth exceeds 32")
            elif ch in ("}", "]"):
                if depth > 0:
                    depth -= 1


def strict_json_loads(raw_text: typing.Any) -> typing.Any:
    """Parse JSON strictly rejecting duplicate keys, floats, NaN/Infinity, huge ints, and deep nesting."""
    require_ok(isinstance(raw_text, str), "raw_text must be str")
    _check_json_text_depth(raw_text, 32)
    return json.loads(
        raw_text,
        object_pairs_hook=_reject_duplicate_json_keys,
        parse_int=_parse_bounded_json_int,
        parse_float=_reject_json_float,
        parse_constant=_reject_json_constant,
    )


def canonical_json_bytes(obj: typing.Any) -> bytes:
    """Deterministic UTF-8 canonical JSON serialization (fail-closed on NaN/Infinity)."""
    return json.dumps(
        obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False, allow_nan=False
    ).encode("utf-8")


def sha256_bytes(data: bytes) -> str:
    """Lowercase SHA-256 hex digest."""
    return hashlib.sha256(data).hexdigest()


def _open_dir_nofollow(dir_path: pathlib.Path, label: str) -> int:
    """Open directory verifying every path component with O_DIRECTORY | O_NOFOLLOW | O_NONBLOCK."""
    require_ok(isinstance(dir_path, pathlib.Path), f"{label} must be Path")
    parts = dir_path.parts
    if dir_path.is_absolute():
        cur_fd = os.open("/", _DIR_OPEN_FLAGS)
        walk_parts = parts[1:]
    else:
        cur_fd = os.open(".", _DIR_OPEN_FLAGS)
        walk_parts = parts
    try:
        for part in walk_parts:
            try:
                nxt_fd = os.open(part, _DIR_OPEN_FLAGS, dir_fd=cur_fd)
            except OSError as exc:
                if exc.errno in (errno.ELOOP, errno.ENOTDIR):
                    raise ValueError(
                        f"symlink or non-directory forbidden for {label}: {part}"
                    ) from exc
                raise ValueError(f"directory not found for {label}: {dir_path.name}") from exc
            os.close(cur_fd)
            cur_fd = nxt_fd
        return cur_fd
    except BaseException:
        os.close(cur_fd)
        raise


def _read_fd_bounded(
    dir_fd: int,
    filename: str,
    label: str,
    max_bytes: int = MAX_FILE_BYTES,
) -> bytes:
    """Open regular file under dir_fd with O_NOFOLLOW | O_NONBLOCK and read <= max_bytes."""
    try:
        fd = os.open(filename, _FILE_OPEN_FLAGS, dir_fd=dir_fd)
    except OSError as exc:
        if exc.errno == errno.ELOOP:
            raise ValueError(f"symlink forbidden for {label}: {filename}") from exc
        raise ValueError(f"file not found for {label}: {filename}") from exc
    try:
        st = os.fstat(fd)
        require_ok(stat.S_ISREG(st.st_mode), f"expected regular file for {label}: {filename}")
        require_ok(st.st_size <= max_bytes, f"file exceeds size limit for {label}: {filename}")
        chunks: list[bytes] = []
        total = 0
        while True:
            chunk = os.read(fd, 65536)
            if not chunk:
                break
            total += len(chunk)
            require_ok(total <= max_bytes, f"file exceeds size limit for {label}: {filename}")
            chunks.append(chunk)
        return b"".join(chunks)
    finally:
        os.close(fd)


def _read_file_nofollow(
    path: pathlib.Path,
    label: str,
    max_bytes: int = MAX_FILE_BYTES,
) -> bytes:
    """Read regular file rejecting leaf/ancestor symlinks, FIFOs, dirs, and oversized files."""
    require_ok(isinstance(path, pathlib.Path), f"{label} must be Path")
    require_ok(len(path.name) > 0, f"invalid file path for {label}")
    dir_fd = _open_dir_nofollow(path.parent, label)
    try:
        return _read_fd_bounded(dir_fd, path.name, label, max_bytes=max_bytes)
    finally:
        os.close(dir_fd)


def _write_fd_nofollow(dir_fd: int, filename: str, data: bytes, label: str) -> None:
    """Write regular file under dir_fd rejecting leaf symlinks, FIFOs, and directories."""
    try:
        fd = os.open(filename, _WRITE_OPEN_FLAGS, 0o644, dir_fd=dir_fd)
    except OSError as exc:
        if exc.errno == errno.ELOOP:
            raise ValueError(f"symlink forbidden for {label}: {filename}") from exc
        raise
    try:
        st = os.fstat(fd)
        require_ok(stat.S_ISREG(st.st_mode), f"expected regular file for {label}: {filename}")
        written = 0
        while written < len(data):
            n_out = os.write(fd, data[written:])
            require_ok(n_out > 0, f"short write for {label}: {filename}")
            written += n_out
    finally:
        os.close(fd)


def _write_file_nofollow(path: pathlib.Path, data: bytes, label: str) -> None:
    """Write regular file rejecting leaf/ancestor symlinks, FIFOs, and directories."""
    require_ok(isinstance(path, pathlib.Path), f"{label} must be Path")
    require_ok(len(path.name) > 0, f"invalid file path for {label}")
    dir_fd = _open_dir_nofollow(path.parent, label)
    try:
        _write_fd_nofollow(dir_fd, path.name, data, label)
    finally:
        os.close(dir_fd)


def _is_allowed_ast_constant(val: typing.Any) -> bool:
    """Allow only int/bool/str/bytes/None/Ellipsis constants (reject float/complex)."""
    if val is None or val is Ellipsis:
        return True
    return isinstance(val, (int, str, bytes))


def _validate_json_call(node: ast.Call, attr: str) -> None:
    """Enforce strict fail-closed hooks on json.loads and allow_nan=False on json.dumps."""
    kw_map: dict[str, ast.AST] = {}
    for kw in node.keywords:
        require_ok(kw.arg is not None, f"json.{attr}() kwargs unpacking forbidden")
        kw_map[kw.arg] = kw.value
    if attr == "loads":
        require_ok(len(node.args) == 1, "json.loads() requires single positional text arg")
        for hook_name, fn_name in REQUIRED_JSON_LOADS_HOOKS:
            hook_val = kw_map.get(hook_name)
            require_ok(
                isinstance(hook_val, ast.Name) and hook_val.id == fn_name,
                f"json.loads() requires {hook_name}={fn_name}",
            )
        return
    allow_nan_val = kw_map.get("allow_nan")
    require_ok(
        isinstance(allow_nan_val, ast.Constant) and allow_nan_val.value is False,
        "json.dumps() requires allow_nan=False",
    )


def _collect_annotation_nodes(tree: ast.AST) -> set[ast.AST]:
    """Collect AST nodes inside static type annotations and forbid Calls in annotations."""
    ann_roots: list[ast.AST] = []
    for item in ast.walk(tree):
        if isinstance(item, ast.AnnAssign):
            ann_roots.append(item.annotation)
        elif isinstance(item, ast.arg) and item.annotation is not None:
            ann_roots.append(item.annotation)
        elif isinstance(item, ast.FunctionDef) and item.returns is not None:
            ann_roots.append(item.returns)
    ann_nodes: set[ast.AST] = set()
    for root in ann_roots:
        for sub in ast.walk(root):
            require_ok(not isinstance(sub, ast.Call), "calls forbidden in type annotations")
            ann_nodes.add(sub)
    return ann_nodes


def _is_valid_fraction_ref(
    node: ast.Attribute,
    parent: ast.AST | None,
    annotation_nodes: set[ast.AST],
) -> bool:
    """Allow fractions.Fraction only in annotations, direct 2-arg Call, or isinstance(..., Fraction)."""
    if node in annotation_nodes:
        return True
    if not isinstance(parent, ast.Call):
        return False
    if parent.func is node:
        return True
    return (
        isinstance(parent.func, ast.Name)
        and parent.func.id == "isinstance"
        and len(parent.args) == 2
        and len(parent.keywords) == 0
        and parent.args[1] is node
    )


def verify_pure_q_source_ast(
    src: typing.Any,
    filename: str = "<source>",
    allowed_imports: frozenset[str] = ALLOWED_STDLIB_IMPORTS,
) -> None:
    """Fail-closed AST guard enforcing pure-Q / pure-Z arithmetic & import discipline."""
    require_ok(isinstance(src, str), "src must be str")
    try:
        tree = ast.parse(src, filename=filename)
    except SyntaxError as exc:
        raise ValueError(f"syntax error in {filename}: {exc.msg}") from exc
    parent_map: dict[ast.AST, ast.AST] = {}
    for parent in ast.walk(tree):
        for child in ast.iter_child_nodes(parent):
            parent_map[child] = parent
    annotation_nodes = _collect_annotation_nodes(tree)
    for node in ast.walk(tree):
        require_ok(not isinstance(node, ast.Assert), f"bare assert forbidden in {filename}")
        require_ok(not isinstance(node, ast.Div), f"division operator (/) forbidden in {filename}")
        require_ok(
            not isinstance(node, ast.FloorDiv),
            f"floor division operator (//) forbidden in {filename}",
        )
        require_ok(
            not isinstance(node, ast.Mod),
            f"modulo/format operator (%) forbidden in {filename}",
        )
        require_ok(not isinstance(node, ast.Pow), f"power operator (**) forbidden in {filename}")
        require_ok(
            not isinstance(node, ast.NamedExpr), f"walrus operator (:=) forbidden in {filename}"
        )
        require_ok(not isinstance(node, ast.ImportFrom), f"ImportFrom forbidden in {filename}")
        if isinstance(node, ast.Import):
            for alias in node.names:
                require_ok(alias.asname is None, f"import alias forbidden: {alias.name}")
                require_ok(alias.name in allowed_imports, f"disallowed import: {alias.name}")
        elif isinstance(node, ast.Constant):
            require_ok(
                _is_allowed_ast_constant(node.value),
                f"float/complex literal forbidden in {filename}",
            )
        elif isinstance(node, ast.FormattedValue):
            require_ok(node.format_spec is None, f"format spec forbidden in {filename}")
        elif isinstance(node, ast.Name):
            require_ok(
                node.id not in FORBIDDEN_BARE_NAMES,
                f"forbidden builtin identifier: {node.id}",
            )
            if node.id.startswith("__"):
                require_ok(
                    node.id in ALLOWED_DUNDER_NAMES,
                    f"forbidden dunder identifier: {node.id}",
                )
            if node.id in ("math", "fractions", "json", "os"):
                require_ok(
                    isinstance(parent_map.get(node), ast.Attribute),
                    f"aliasing or passing {node.id} module is forbidden",
                )
        elif isinstance(node, ast.Attribute):
            require_ok(
                not node.attr.startswith("__"),
                f"forbidden dunder attribute access: {node.attr}",
            )
            require_ok(
                node.attr not in FORBIDDEN_ATTR_NAMES,
                f"forbidden attribute access: {node.attr}",
            )
            parent = parent_map.get(node)
            if isinstance(node.value, ast.Name) and node.value.id == "math":
                require_ok(
                    node.attr in ("gcd", "lcm"),
                    f"disallowed math attribute: math.{node.attr}",
                )
                require_ok(
                    isinstance(parent, ast.Call) and parent.func is node,
                    f"uncalled math.{node.attr} reference is forbidden",
                )
            if isinstance(node.value, ast.Name) and node.value.id == "fractions":
                require_ok(
                    node.attr == "Fraction",
                    f"disallowed fractions attribute: fractions.{node.attr}",
                )
                require_ok(
                    _is_valid_fraction_ref(node, parent, annotation_nodes),
                    "uncalled or aliased fractions.Fraction reference is forbidden",
                )
            if isinstance(node.value, ast.Name) and node.value.id == "json":
                require_ok(
                    node.attr in ("loads", "dumps"),
                    f"disallowed json attribute: json.{node.attr}",
                )
                require_ok(
                    isinstance(parent, ast.Call) and parent.func is node,
                    f"uncalled json.{node.attr} reference is forbidden",
                )
            if isinstance(node.value, ast.Name) and node.value.id == "os":
                require_ok(
                    node.attr in ALLOWED_OS_ATTRS,
                    f"disallowed os attribute: os.{node.attr}",
                )
        elif isinstance(node, ast.Call):
            require_ok(
                isinstance(node.func, (ast.Name, ast.Attribute)),
                f"indirect call target forbidden in {filename}",
            )
            if isinstance(node.func, ast.Attribute) and node.func.attr == "Fraction":
                require_ok(
                    len(node.args) == 2 and len(node.keywords) == 0,
                    "Fraction() requires exact 2-arg positional integer call",
                )
                for arg in node.args:
                    require_ok(
                        not isinstance(arg, ast.Starred),
                        "Fraction() starred arguments forbidden",
                    )
                    if isinstance(arg, ast.Constant):
                        require_ok(
                            is_exact_int(arg.value),
                            "Fraction() literal argument must be exact int",
                        )
            elif (
                isinstance(node.func, ast.Attribute)
                and isinstance(node.func.value, ast.Name)
                and node.func.value.id == "json"
            ):
                _validate_json_call(node, node.func.attr)


def are_two_intervals_strictly_crossing(
    a1: int, c1: int, a2: int, c2: int
) -> bool:
    """Return True iff open intervals (a1, c1) and (a2, c2) strictly cross (non-laminar)."""
    return (a1 < a2 and a2 < c1 and c1 < c2) or (a2 < a1 and a1 < c2 and c2 < c1)


def all_four_pillars_certified(p1: bool, p2: bool, p3: bool, p4: bool) -> bool:
    """Return True iff all four verification pillars pass."""
    return bool(p1) and bool(p2) and bool(p3) and bool(p4)


# ---------------------------------------------------------------------------
# Pillar 1: Clean-Room Exact-Q Time-Cut LP Simplex & Laminar DP Oracle
# ---------------------------------------------------------------------------


def laminar_tree_dp_table(max_n: int) -> list[int]:
    """Compute exact laminar interval-tree cut scores T_0 .. T_{max_n} via Bellman DP."""
    require_ok(is_exact_int(max_n), "max_n must be int")
    require_ok(max_n >= 1, "max_n must be >= 1")
    require_ok(max_n <= 64, "max_n exceeds bounded limit 64")
    dp = [0, 0]
    for n in range(2, max_n + 1):
        best = max(dp[k] + dp[n - k] + min(k, n - k) for k in range(1, n))
        dp.append(best)
    return dp


def verify_primal_dual_timecut_certificate_q(
    n: int,
    x_rects: dict[tuple[int, int, int], fractions.Fraction],
    y_pairs: dict[tuple[int, int], fractions.Fraction],
    check_all_general_rects: bool = True,
) -> fractions.Fraction:
    """Self-certify primal congestion <= 1, dual coverage >= min(b-a, c-b), and strong duality."""
    require_ok(is_exact_int(n), "n must be int")
    require_ok(n >= 2, "n must be >= 2")
    require_ok(isinstance(x_rects, dict), "x_rects must be dict")
    require_ok(isinstance(y_pairs, dict), "y_pairs must be dict")

    int_q = [q_frac(k, 1) for k in range(n + 1)]
    zero_q = int_q[0]
    one_q = int_q[1]

    primal_obj = zero_q
    for (a, b, c), w in x_rects.items():
        require_fraction(w, "primal weight")
        require_ok(w > zero_q, "primal weight must be > 0")
        require_ok(0 <= a, "rect a < 0")
        require_ok(a < b, "rect a >= b")
        require_ok(b < c, "rect b >= c")
        require_ok(c <= n, "rect c > n")
        primal_obj += int_q[min(b - a, c - b)] * w

    dual_obj = zero_q
    for (i, j), yw in y_pairs.items():
        require_fraction(yw, "dual weight")
        require_ok(yw > zero_q, "dual weight must be > 0")
        require_ok(0 <= i, "pair i < 0")
        require_ok(i < j, "pair i >= j")
        require_ok(j < n, "pair j >= n")
        dual_obj += yw

    for i in range(n):
        for j in range(i + 1, n):
            load = sum(
                (w for (a, b, c), w in x_rects.items() if a <= i < b <= j < c),
                zero_q,
            )
            require_ok(load <= one_q, "primal pair congestion exceeds 1")

    pref = [[zero_q for _ in range(n + 1)] for _ in range(n + 1)]
    for i in range(n):
        row_acc = zero_q
        for j in range(n):
            row_acc += y_pairs.get((i, j), zero_q)
            pref[i + 1][j + 1] = pref[i][j + 1] + row_acc

    def rect_mass_q(a: int, b: int, c: int) -> fractions.Fraction:
        return pref[b][c] - pref[a][c] - pref[b][b] + pref[a][b]

    if check_all_general_rects:
        for a in range(n + 1):
            for b in range(a + 1, n + 1):
                for c in range(b + 1, n + 1):
                    require_ok(
                        rect_mass_q(a, b, c) >= int_q[min(b - a, c - b)],
                        "dual under-covers general rectangle",
                    )
    else:
        for b in range(1, n):
            max_h = min(b, n - b)
            for h in range(1, max_h + 1):
                require_ok(
                    rect_mass_q(b - h, b, b + h) >= int_q[h],
                    "dual under-covers balanced rectangle",
                )

    require_ok(primal_obj == dual_obj, "primal objective != dual objective")
    return primal_obj


def _select_bland_leaving_row(
    full: list[list[fractions.Fraction]],
    basis: list[int],
    m_con: int,
    total_cols: int,
    enter: int,
) -> int:
    """Bland-rule minimum-ratio leaving-row selector; fails closed on unbounded entering column."""
    zero_q = q_frac(0, 1)
    leave = -1
    best_ratio: fractions.Fraction | None = None
    for r_idx in range(m_con):
        a_re = full[r_idx][enter]
        if a_re > zero_q:
            ratio = q_div(full[r_idx][total_cols], a_re)
            if (
                best_ratio is None
                or ratio < best_ratio
                or (ratio == best_ratio and basis[r_idx] < basis[leave])
            ):
                best_ratio = ratio
                leave = r_idx
    require_ok(leave >= 0, "unbounded simplex entering column")
    return leave


def solve_timecut_lp_exact_q(
    n: int, max_pivots: int = 256, check_all_general_rects: bool = True
) -> dict[str, typing.Any]:
    """Solve exact Q adjacent-rectangle time-cut LP from scratch via Bland-rule simplex."""
    require_ok(is_exact_int(n), "n must be int")
    require_ok(n >= 2, "lp dimension n must be >= 2")
    require_ok(n <= 20, "n exceeds bounded solver limit 20")
    require_ok(is_exact_int(max_pivots), "max_pivots must be int")
    require_ok(max_pivots >= 1, "max_pivots must be >= 1")
    require_ok(max_pivots <= 1024, "max_pivots exceeds bounded limit 1024")

    zero_q = q_frac(0, 1)
    one_q = q_frac(1, 1)

    primal_orbits: list[tuple[int, int, int]] = []
    for b in range(1, (n >> 1) + 1):
        vmult = 1 if (2 * b == n) else 2
        for h in range(1, b + 1):
            primal_orbits.append((b, h, vmult))

    pair_to_orb: dict[tuple[int, int], int] = {}
    pair_orbits: list[tuple[int, int, int]] = []
    for i in range(n):
        for j in range(i + 1, n):
            ri, rj = n - 1 - j, n - 1 - i
            canon = min((i, j), (ri, rj))
            if canon not in pair_to_orb:
                pair_to_orb[canon] = len(pair_orbits)
                pmult = 1 if (i, j) == (ri, rj) else 2
                pair_orbits.append((canon[0], canon[1], pmult))

    m_con = len(pair_orbits)
    n_var = len(primal_orbits)
    total_cols = n_var + m_con

    full: list[list[fractions.Fraction]] = []
    basis: list[int] = []
    for r_idx, (i0, j0, _pm) in enumerate(pair_orbits):
        row: list[fractions.Fraction] = []
        for b, h, vm in primal_orbits:
            rects_v = [(b, h)] if vm == 1 else [(b, h), (n - b, h)]
            cov = sum(1 for (cb, ch) in rects_v if (cb - ch) <= i0 < cb <= j0 < (cb + ch))
            row.append(q_frac(cov, 1))
        slacks = [q_frac(1 if c_idx == r_idx else 0, 1) for c_idx in range(m_con)]
        full.append(row + slacks + [one_q])
        basis.append(n_var + r_idx)

    obj_row = [q_frac(-h * vm, 1) for (_b, h, vm) in primal_orbits] + [zero_q] * (m_con + 1)
    full.append(obj_row)

    pivots_used = 0
    for _step in range(max_pivots + 1):
        enter = -1
        for c_idx in range(total_cols):
            if full[m_con][c_idx] < zero_q:
                enter = c_idx
                break
        if enter == -1:
            break
        require_ok(pivots_used < max_pivots, "simplex pivot budget exceeded")

        leave = _select_bland_leaving_row(full, basis, m_con, total_cols, enter)

        inv_pv = q_div(one_q, full[leave][enter])
        leave_row = [val * inv_pv for val in full[leave]]
        full[leave] = leave_row
        nz_leave = [(c_idx, val) for c_idx, val in enumerate(leave_row) if val]
        for r_idx in range(m_con + 1):
            if r_idx != leave:
                fac = full[r_idx][enter]
                if fac:
                    row_r = full[r_idx]
                    for c_idx, val in nz_leave:
                        row_r[c_idx] -= fac * val
        basis[leave] = enter
        pivots_used += 1

    x_rects: dict[tuple[int, int, int], fractions.Fraction] = {}
    for r_idx, bcol in enumerate(basis):
        if bcol < n_var and full[r_idx][total_cols] > zero_q:
            b, h, _vm = primal_orbits[bcol]
            w_val = full[r_idx][total_cols]
            x_rects[(b - h, b, b + h)] = w_val
            x_rects[(n - b - h, n - b, n - b + h)] = w_val

    y_pairs: dict[tuple[int, int], fractions.Fraction] = {}
    for r_idx, (i0, j0, pmult) in enumerate(pair_orbits):
        u_r = full[m_con][n_var + r_idx]
        if u_r > zero_q:
            y_val = q_div(u_r, q_frac(pmult, 1))
            y_pairs[(i0, j0)] = y_val
            y_pairs[(n - 1 - j0, n - 1 - i0)] = y_val

    certified_opt = verify_primal_dual_timecut_certificate_q(
        n, x_rects, y_pairs, check_all_general_rects=check_all_general_rects
    )
    primal_lcm = math.lcm(*(w.denominator for w in x_rects.values()))
    dual_lcm = math.lcm(*(w.denominator for w in y_pairs.values()))
    return {
        "n": n,
        "optimum": certified_opt,
        "x_rects": x_rects,
        "y_pairs": y_pairs,
        "primal_support_size": len(x_rects),
        "dual_support_size": len(y_pairs),
        "primal_lcm_den": primal_lcm,
        "dual_lcm_den": dual_lcm,
        "pivots_used": pivots_used,
    }


def run_pillar_p1() -> tuple[dict[str, typing.Any], dict[int, dict[str, typing.Any]]]:
    """Solve N=2..20 from scratch and certify general-rect strong duality & N_min=18 threshold."""
    dp = laminar_tree_dp_table(20)
    solved: dict[int, dict[str, typing.Any]] = {}
    for n in range(2, 21):
        solved[n] = solve_timecut_lp_exact_q(n, max_pivots=256, check_all_general_rects=True)

    zero_gap_through_17 = all(solved[n]["optimum"] == q_frac(dp[n], 1) for n in range(2, 18))
    first_crossing_n = next(n for n in range(2, 21) if solved[n]["optimum"] > q_frac(dp[n], 1))

    dyadic_exact = all(
        solved[1 << d]["optimum"] == q_frac(d * (1 << (d - 1)), 1) for d in (1, 2, 3, 4)
    )
    n18 = solved[18]
    n19 = solved[19]
    n20 = solved[20]
    gap18 = n18["optimum"] - q_frac(dp[18], 1)
    gap19 = n19["optimum"] - q_frac(dp[19], 1)
    gap20 = n20["optimum"] - q_frac(dp[20], 1)

    passed = all(
        (
            zero_gap_through_17,
            first_crossing_n == 18,
            dyadic_exact,
            dp[17] == 33,
            dp[18] == 35,
            dp[19] == 37,
            dp[20] == 40,
            n18["optimum"] == q_frac(107, 3),
            gap18 == q_frac(2, 3),
            n18["primal_lcm_den"] == 3,
            n18["dual_lcm_den"] == 3,
            n19["optimum"] == q_frac(38, 1),
            gap19 == q_frac(1, 1),
            n19["primal_lcm_den"] == 2,
            n20["optimum"] == q_frac(122, 3),
            gap20 == q_frac(2, 3),
        )
    )
    return (
        {
            "laminar_dp_2_to_20": dp[2:],
            "lp_optima_2_to_20": [q_to_str(solved[n]["optimum"]) for n in range(2, 21)],
            "general_rects_verified_all_2_to_20": True,
            "zero_gap_for_all_2_le_n_le_17": zero_gap_through_17,
            "minimal_crossing_advantage_n": first_crossing_n,
            "dyadic_entropy_ceiling_exact_2_4_8_16": dyadic_exact,
            "n18_laminar_tree_optimum": dp[18],
            "n18_lp_optimum": q_to_str(n18["optimum"]),
            "n18_crossing_gap": q_to_str(gap18),
            "n18_primal_support_size": n18["primal_support_size"],
            "n18_dual_support_size": n18["dual_support_size"],
            "n18_primal_lcm_den": n18["primal_lcm_den"],
            "n18_dual_lcm_den": n18["dual_lcm_den"],
            "n19_laminar_tree_optimum": dp[19],
            "n19_lp_optimum": q_to_str(n19["optimum"]),
            "n19_crossing_gap": q_to_str(gap19),
            "n20_lp_optimum": q_to_str(n20["optimum"]),
            "passed": passed,
        },
        solved,
    )


# ---------------------------------------------------------------------------
# Pillar 2: Banked CNF Bit-Length Envelope, Tseitin Moduli & 5-Clause Gadget
# ---------------------------------------------------------------------------


def _int_mod_pos(val: int, mod: int) -> int:
    """Exact remainder val mod (mod > 0) for val >= 0 using bit-shifts only."""
    rem = val
    shift = 0
    while (mod << (shift + 1)) <= rem:
        shift += 1
    while shift >= 0:
        sub = mod << shift
        if rem >= sub:
            rem -= sub
        shift -= 1
    return rem


def audit_eight_bank_dimacs_envelope(k: int) -> dict[str, typing.Any]:
    """Compute exact variable, clause, and ASCII bit-length ratios for 8-bank vs naive 2-bank."""
    require_ok(is_exact_int(k), "k must be int")
    require_ok(k >= 4, "k must be >= 4")
    require_ok(k <= 64, "k must be <= 64")
    require_ok((k & 3) == 0, "k must be divisible by 4")

    n_rows = 1 << k
    raw_list_bits = 2 * k * n_rows
    b_chunk = k >> 2
    j_bank = 1 << b_chunk
    u_reserved_8bank = 9 * int_pow_nonneg(10, b_chunk) - 1
    vars_8bank = u_reserved_8bank + 14 + 4 * n_rows + 8 * j_bank

    u_reserved_2bank = 2 * int_pow_nonneg(10, k) - 1
    clauses_8bank = 28 * n_rows + 24 * j_bank + u_reserved_8bank + 16

    max_id_digits = 1
    pow10_d = 10
    while pow10_d <= vars_8bank:
        max_id_digits += 1
        pow10_d *= 10

    min_ascii_bits = 8 * (16 * n_rows * (3 * b_chunk + 6))
    max_ascii_bits = 8 * (clauses_8bank * (3 * max_id_digits + 7) + 64)
    # Canonical Tseitin vertex count t = 2^k - 3; for even k >= 4, 2^k == 4 (mod 6) so t == 1 (mod 2, mod 3)
    t_tseitin = n_rows - 3
    return {
        "k": k,
        "n_rows": n_rows,
        "raw_list_bits": raw_list_bits,
        "u_reserved_8bank": u_reserved_8bank,
        "vars_8bank": vars_8bank,
        "u_reserved_2bank": u_reserved_2bank,
        "vars_per_row_8bank": q_frac(vars_8bank, n_rows),
        "vars_per_row_2bank_lower": q_frac(u_reserved_2bank, n_rows),
        "ascii_bits_over_raw_lower": q_frac(min_ascii_bits, raw_list_bits),
        "ascii_bits_over_raw_upper": q_frac(max_ascii_bits, raw_list_bits),
        "compulsory_word_probes_on_proj": 16 * n_rows,
        "compulsory_word_probes_global": 32 * n_rows,
        "tseitin_vertices_t": t_tseitin,
        "tseitin_mod2_charge_mismatch": (t_tseitin & 1) == 1,
        "tseitin_mod3_charge_mismatch": _int_mod_pos(t_tseitin, 3) == 1,
    }


def verify_five_clause_port_gadget_cleanroom() -> dict[str, typing.Any]:
    """Exhaustively check the 5-clause degree->=3 port replacement gadget over {0,1}^6."""

    def clause_vals(a: int, b: int, c: int, x: int, y: int, z: int) -> tuple[bool, ...]:
        return (
            bool(a or y or z),
            bool(b or x or (1 - z)),
            bool(c or (1 - x) or (1 - y)),
            bool(x or (1 - y) or z),
            bool((1 - x) or y or (1 - z)),
        )

    ext_formula_ok = True
    zero_boundary_unsat = False
    for a, b, c in itertools.product((0, 1), repeat=3):
        cnt = sum(
            1
            for x, y, z in itertools.product((0, 1), repeat=3)
            if all(clause_vals(a, b, c, x, y, z))
        )
        if cnt != 2 * (a + b + c):
            ext_formula_ok = False
        if (a, b, c) == (0, 0, 0):
            zero_boundary_unsat = cnt == 0

    deleted_counts_at_zero: list[int] = []
    for drop_idx in range(5):
        del_cnt = sum(
            1
            for x, y, z in itertools.product((0, 1), repeat=3)
            if all(
                val
                for c_i, val in enumerate(clause_vals(0, 0, 0, x, y, z))
                if c_i != drop_idx
            )
        )
        deleted_counts_at_zero.append(del_cnt)

    irredundant_all_5 = all(c_del >= 1 for c_del in deleted_counts_at_zero)
    return {
        "extension_formula_2_sum_ports_exact": ext_formula_ok,
        "all_false_boundary_unsat": zero_boundary_unsat,
        "deleted_clause_models_at_zero_boundary": deleted_counts_at_zero,
        "irredundant_all_5_clauses": irredundant_all_5,
    }


def run_pillar_p2() -> dict[str, typing.Any]:
    """Certify linear bit-length envelope, 2-bank superlinear blowup, Tseitin moduli, & 5-clause gadget."""
    scales = [audit_eight_bank_dimacs_envelope(k) for k in (8, 12, 16, 20, 24)]
    s24 = scales[-1]

    tseitin_both_ok = all(
        all((s["tseitin_mod2_charge_mismatch"], s["tseitin_mod3_charge_mismatch"]))
        for s in scales
    )
    linear_envelope_ok = all(
        all(
            (
                q_frac(48, 1) <= s["ascii_bits_over_raw_lower"],
                s["ascii_bits_over_raw_upper"] <= q_frac(304, 1),
                tseitin_both_ok,
            )
        )
        for s in scales
    )
    monotone_upper_shrink = all(
        scales[idx]["ascii_bits_over_raw_upper"] > scales[idx + 1]["ascii_bits_over_raw_upper"]
        for idx in range(len(scales) - 1)
    )
    diophantine_8bank_ok = all(
        (
            int_pow_nonneg(10, 3) < (1 << 10),
            s24["u_reserved_8bank"] < s24["n_rows"],
            s24["vars_per_row_8bank"] < q_frac(5, 1),
            s24["ascii_bits_over_raw_upper"] < q_frac(150, 1),
            monotone_upper_shrink,
            s24["vars_per_row_2bank_lower"] > q_frac(int_pow_nonneg(10, 16), 1),
        )
    )
    gadget = verify_five_clause_port_gadget_cleanroom()
    passed = all(
        (
            linear_envelope_ok,
            diophantine_8bank_ok,
            gadget["extension_formula_2_sum_ports_exact"],
            gadget["all_false_boundary_unsat"],
            gadget["irredundant_all_5_clauses"],
        )
    )
    return {
        "scales_checked_k": [s["k"] for s in scales],
        "k24_vars_per_row_8bank": q_to_str(s24["vars_per_row_8bank"]),
        "k24_ascii_over_raw_bounds": [
            q_to_str(s24["ascii_bits_over_raw_lower"]),
            q_to_str(s24["ascii_bits_over_raw_upper"]),
        ],
        "k24_compulsory_probes_proj_and_global": [
            s24["compulsory_word_probes_on_proj"],
            s24["compulsory_word_probes_global"],
        ],
        "linear_bit_length_envelope_verified": linear_envelope_ok,
        "naive_2bank_superlinear_inflation_refuted": diophantine_8bank_ok,
        "every_field_tseitin_mod2_mod3_obstruction_verified": tseitin_both_ok,
        "five_clause_port_gadget": gadget,
        "passed": passed,
    }


# ---------------------------------------------------------------------------
# Pillar 3: Zero-Dep Lean 4.36.0 Package Binding & Char-Safe R13b Gate
# ---------------------------------------------------------------------------


def _consume_lean_char_literal(text: str, idx: int) -> int:
    """If text[idx:] starts a Lean 4 character literal, return its length (>= 3), else 0."""
    if text[idx] != "'":
        return 0
    if idx > 0 and (text[idx - 1].isalnum() or text[idx - 1] in ("_", "'")):
        return 0
    length = len(text)
    if idx + 2 < length and text[idx + 1] not in ("'", "\\", "\n") and text[idx + 2] == "'":
        return 3
    if idx + 3 < length and text[idx + 1] == "\\":
        end_limit = min(length, idx + 8)
        pos = idx + 2
        while pos < end_limit and text[pos] != "\n":
            if pos > idx + 2 and text[pos] == "'":
                return pos - idx + 1
            pos += 1
    return 0


def strip_lean_comments_and_strings(text: str) -> str:
    """Char-literal-safe stripper for Lean line comments, nested block comments, & strings."""
    require_ok(isinstance(text, str), "Lean source text must be str")
    out: list[str] = []
    idx = 0
    length = len(text)
    depth = 0
    in_str = False
    while idx < length:
        if in_str:
            if text[idx] == "\\":
                require_ok(idx + 1 < length, "unclosed Lean string escape")
                out.append("  ")
                idx += 2
                continue
            if text[idx] == '"':
                in_str = False
                out.append(" ")
                idx += 1
                continue
            out.append("\n" if text[idx] == "\n" else " ")
            idx += 1
            continue

        if depth == 0 and text[idx : idx + 2] == "--":
            while idx < length and text[idx] != "\n":
                idx += 1
            continue
        if depth == 0 and text[idx : idx + 3] in ("/--", "/-!"):
            depth = 1
            idx += 3
            continue
        if text[idx : idx + 2] == "/-":
            depth += 1
            idx += 2
            continue
        if depth > 0 and text[idx : idx + 2] == "-/":
            depth -= 1
            idx += 2
            continue
        if depth > 0:
            if text[idx] == "\n":
                out.append("\n")
            idx += 1
            continue

        char_len = _consume_lean_char_literal(text, idx)
        if char_len > 0:
            out.append(" " * char_len)
            idx += char_len
            continue

        require_ok(text[idx : idx + 2] != "r#", "Lean raw string literal forbidden")
        if text[idx] == '"':
            in_str = True
            out.append(" ")
            idx += 1
            continue

        out.append(text[idx])
        idx += 1

    require_ok(depth == 0, "unclosed Lean block comment")
    require_ok(not in_str, "unclosed Lean string literal")
    return "".join(out)


def _strip_toml_line_comment(line: str) -> str:
    """Remove trailing TOML # comment outside single/double quotes."""
    in_dq = False
    in_sq = False
    escaped = False
    for idx, ch in enumerate(line):
        if in_dq:
            if escaped:
                escaped = False
            elif ch == "\\":
                escaped = True
            elif ch == '"':
                in_dq = False
        elif in_sq:
            if ch == "'":
                in_sq = False
        else:
            if ch == '"':
                in_dq = True
            elif ch == "'":
                in_sq = True
            elif ch == "#":
                return line[:idx]
    return line


def validate_lakefile_toml(lakefile_txt: str) -> None:
    """Strictly parse lakefile.toml (Python 3.10+ stdlib) and forbid all external requires."""
    require_ok(isinstance(lakefile_txt, str), "lakefile_txt must be str")
    saw_pkg_name = False
    in_root = True
    allowed_keys = frozenset({"name", "version", "defaultTargets"})
    for raw_line in lakefile_txt.splitlines():
        line = _strip_toml_line_comment(raw_line).strip()
        if not line:
            continue
        if line.startswith("["):
            require_ok(line.endswith("]"), f"malformed lakefile.toml header: {line}")
            is_array_table = (line[:2], line[-2:]) == ("[[", "]]")
            inner = line[2:-2] if is_array_table else line[1:-1]
            parts = [seg.strip().strip('"').strip("'") for seg in inner.split(".")]
            require_ok(
                all(seg != "require" for seg in parts),
                "lakefile.toml must have zero external requires",
            )
            require_ok(
                is_array_table and parts == ["lean_lib"],
                f"disallowed lakefile.toml section: {line}",
            )
            in_root = False
            continue
        require_ok("=" in line, f"malformed lakefile.toml line: {line}")
        key_part, val_part = line.split("=", 1)
        key = key_part.strip().strip('"').strip("'")
        val = val_part.strip()
        require_ok(key != "require", "lakefile.toml must have zero external requires")
        require_ok(key in allowed_keys, f"disallowed lakefile.toml key: {key}")
        if in_root and key == "name":
            if val == '"timecut_duality"':
                saw_pkg_name = True
    require_ok(saw_pkg_name, "lakefile.toml missing package name")


def read_and_static_gate_lean_package(lean_dir: pathlib.Path = DEFAULT_LEAN_DIR) -> dict[str, typing.Any]:
    """Bind raw bytes of all 5 Lean package files via dir_fd O_NOFOLLOW and run char-safe static R13b checks."""
    dir_fd = _open_dir_nofollow(lean_dir, "lean_dir")
    try:
        present_files = tuple(sorted(os.listdir(dir_fd)))
        require_ok(
            "lakefile.lean" not in present_files,
            "lakefile.lean forbidden alongside lakefile.toml",
        )
        require_ok(
            present_files == EXPECTED_LEAN_FILES,
            f"Lean package file set mismatch: expected {list(EXPECTED_LEAN_FILES)}, got {list(present_files)}",
        )

        file_sha256s: dict[str, str] = {}
        raw_blobs: dict[str, bytes] = {}
        raw_texts: dict[str, str] = {}
        for fname in EXPECTED_LEAN_FILES:
            raw_bytes = _read_fd_bounded(dir_fd, fname, fname, max_bytes=MAX_FILE_BYTES)
            raw_blobs[fname] = raw_bytes
            file_sha256s[fname] = sha256_bytes(raw_bytes)
            raw_texts[fname] = raw_bytes.decode("utf-8")
    finally:
        os.close(dir_fd)

    toolchain = raw_texts["lean-toolchain"].strip()
    require_ok(
        toolchain == "leanprover/lean4:v4.36.0",
        f"unexpected lean-toolchain: {toolchain}",
    )

    manifest = strict_json_loads(raw_texts["lake-manifest.json"])
    require_ok(isinstance(manifest, dict), "lake-manifest.json must be object")
    require_ok(manifest.get("name") == "timecut_duality", "lake-manifest.json name mismatch")
    require_ok(manifest.get("packages") == [], "lake-manifest.json must have empty packages []")

    validate_lakefile_toml(raw_texts["lakefile.toml"])

    main_clean = strip_lean_comments_and_strings(raw_texts["CleanRoomTimeCutDuality.lean"])
    for rule_code, pat in LEAN_COMMON_FORBIDDEN_RULES:
        require_ok(pat.search(main_clean) is None, f"forbidden Lean construct in main: {rule_code}")
    require_ok(
        re.search(r"(?m)^\s*import\b", main_clean) is None,
        "forbidden Lean construct in main: LEAN4_EXTERNAL_IMPORT",
    )
    theorems = tuple(re.findall(r"(?m)^theorem\s+([A-Za-z0-9_]+)", main_clean))
    require_ok(
        theorems == EXPECTED_30_THEOREMS,
        f"Lean theorem catalog mismatch: count={len(theorems)}",
    )

    audit_clean = strip_lean_comments_and_strings(raw_texts["AxiomAudit.lean"])
    for rule_code, pat in LEAN_COMMON_FORBIDDEN_RULES:
        require_ok(pat.search(audit_clean) is None, f"forbidden Lean construct in audit: {rule_code}")
    audit_imports = re.findall(r"(?m)^\s*import\s+([A-Za-z0-9_.]+)", audit_clean)
    require_ok(
        audit_imports == ["CleanRoomTimeCutDuality"],
        f"AxiomAudit.lean must import only CleanRoomTimeCutDuality, got {audit_imports}",
    )
    printed_axioms = tuple(
        re.findall(r"(?m)^#print\s+axioms\s+CleanRoomTimeCutDuality\.([A-Za-z0-9_]+)", audit_clean)
    )
    require_ok(
        printed_axioms == EXPECTED_30_THEOREMS,
        "AxiomAudit.lean #print axioms list must match all 30 theorems in order",
    )

    return {
        "toolchain": toolchain,
        "manifest_zero_external_packages": True,
        "theorem_count": len(theorems),
        "file_sha256s": file_sha256s,
        "raw_blobs": raw_blobs,
    }


def _run_lean_cmd(
    cmd: list[str],
    label: str,
    timeout_s: int,
    cwd: pathlib.Path | None = None,
) -> subprocess.CompletedProcess[str]:
    """Run isolated Lean toolchain subprocess failing closed on timeout or SubprocessError."""
    try:
        return subprocess.run(
            cmd,
            cwd=str(cwd) if cwd is not None else None,
            capture_output=True,
            text=True,
            timeout=timeout_s,
            check=False,
        )
    except subprocess.SubprocessError as exc:
        raise ValueError(f"{label} timed out or failed") from exc


def _probe_lean436_version(lean_bin: pathlib.Path) -> bool:
    """Return True iff lean_bin executes --version and reports Lean 4.36.0."""
    if not lean_bin.is_file():
        return False
    try:
        proc = subprocess.run(
            ["env", "-i", "HOME=/nonexistent", "PATH=/usr/bin:/bin", str(lean_bin), "--version"],
            capture_output=True,
            text=True,
            timeout=30,
            check=False,
        )
    except subprocess.SubprocessError:
        return False
    return proc.returncode == 0 and "version 4.36.0" in proc.stdout


def find_lean436_bin_dir() -> pathlib.Path:
    """Locate Lean 4.36.0 toolchain bin directory verified via lean --version."""
    lake_on_path = shutil.which("lake")
    if lake_on_path is not None:
        cand = pathlib.Path(lake_on_path).resolve().parent
        if cand.joinpath("leanchecker").is_file() and _probe_lean436_version(cand.joinpath("lean")):
            return cand
    toolchains_root = pathlib.Path.home().joinpath(".elan", "toolchains")
    for cand in sorted(toolchains_root.glob("*4.36.0*/bin")):
        if cand.joinpath("leanchecker").is_file() and _probe_lean436_version(cand.joinpath("lean")):
            return cand
    return toolchains_root.joinpath("leanprover--lean4---v4.36.0", "bin")  # pragma: no cover


def verify_lean_package_live(
    lean_dir: pathlib.Path = DEFAULT_LEAN_DIR,
    toolchain_bin_dir: pathlib.Path | None = None,
) -> dict[str, typing.Any]:
    """Copy verified in-memory Lean bytes to temp dir, validate 4.36.0 binaries, build, leanchecker, & audit axioms."""
    pkg_info = read_and_static_gate_lean_package(lean_dir)
    bin_dir = toolchain_bin_dir if toolchain_bin_dir is not None else find_lean436_bin_dir()
    require_ok(isinstance(bin_dir, pathlib.Path), "toolchain_bin_dir must be Path")
    lake_bin = bin_dir.joinpath("lake")
    lean_bin = bin_dir.joinpath("lean")
    checker_bin = bin_dir.joinpath("leanchecker")
    for tool_path, label in (
        (lake_bin, "lake"),
        (lean_bin, "lean"),
        (checker_bin, "leanchecker"),
    ):
        require_ok(tool_path.is_file(), f"Lean 4.36.0 {label} binary not found")

    clean_path = f"{bin_dir}:/usr/bin:/bin"
    lean_ver_proc = _run_lean_cmd(
        ["env", "-i", "HOME=/nonexistent", f"PATH={clean_path}", str(lean_bin), "--version"],
        "lean --version",
        30,
    )
    require_ok(
        lean_ver_proc.returncode == 0 and "version 4.36.0" in lean_ver_proc.stdout,
        f"lean --version did not report 4.36.0: {lean_ver_proc.stdout}{lean_ver_proc.stderr}",
    )
    lake_ver_proc = _run_lean_cmd(
        ["env", "-i", "HOME=/nonexistent", f"PATH={clean_path}", str(lake_bin), "--version"],
        "lake --version",
        30,
    )
    require_ok(
        lake_ver_proc.returncode == 0 and "4.36.0" in lake_ver_proc.stdout,
        f"lake --version did not report 4.36.0: {lake_ver_proc.stdout}{lake_ver_proc.stderr}",
    )

    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = pathlib.Path(tmp)
        for fname in EXPECTED_LEAN_FILES:
            tmp_path.joinpath(fname).write_bytes(pkg_info["raw_blobs"][fname])

        build_proc = _run_lean_cmd(
            ["env", "-i", "HOME=/nonexistent", f"PATH={clean_path}", str(lake_bin), "build"],
            "cold lake build",
            300,
            cwd=tmp_path,
        )
        require_ok(
            build_proc.returncode == 0,
            f"cold lake build failed: {build_proc.stderr}{build_proc.stdout}",
        )

        for mod_name in ("CleanRoomTimeCutDuality", "AxiomAudit"):
            chk_proc = _run_lean_cmd(
                [
                    "env",
                    "-i",
                    "HOME=/nonexistent",
                    f"PATH={clean_path}",
                    str(lake_bin),
                    "env",
                    str(checker_bin),
                    mod_name,
                ],
                f"leanchecker {mod_name}",
                300,
                cwd=tmp_path,
            )
            require_ok(
                chk_proc.returncode == 0,
                f"leanchecker {mod_name} failed: {chk_proc.stderr}{chk_proc.stdout}",
            )

        audit_proc = _run_lean_cmd(
            [
                "env",
                "-i",
                "HOME=/nonexistent",
                f"PATH={clean_path}",
                str(lake_bin),
                "env",
                str(lean_bin),
                "AxiomAudit.lean",
            ],
            "live lean AxiomAudit.lean",
            300,
            cwd=tmp_path,
        )
        require_ok(
            audit_proc.returncode == 0,
            f"live lean AxiomAudit.lean failed: {audit_proc.stderr}{audit_proc.stdout}",
        )

    combined = audit_proc.stdout + "\n" + audit_proc.stderr
    allowed_axioms = {"propext", "Quot.sound"}
    observed_axioms: set[str] = set()
    seen_theorems: list[str] = []
    thm_re = re.compile(r"'CleanRoomTimeCutDuality\.([A-Za-z0-9_]+)'\s+(.*)$")
    for raw_line in combined.splitlines():
        match = thm_re.search(raw_line.strip())
        if match is None:
            continue
        thm_name, rest = match.group(1), match.group(2).strip()
        seen_theorems.append(thm_name)
        if rest == "does not depend on any axioms":
            continue
        require_ok(
            rest.startswith("depends on axioms:"),
            f"unexpected axiom report for {thm_name}: {rest}",
        )
        ax_part = rest.split("depends on axioms:", 1)[1].strip().strip("[]")
        axioms = {a.strip() for a in ax_part.split(",") if a.strip()}
        observed_axioms.update(axioms)
        require_ok(
            axioms <= allowed_axioms,
            f"disallowed Lean axiom footprint on {thm_name}: {sorted(axioms)}",
        )

    require_ok(
        tuple(seen_theorems) == EXPECTED_30_THEOREMS,
        f"AxiomAudit live lean output covered {len(seen_theorems)} theorems, expected 30",
    )
    return {
        "file_sha256s": pkg_info["file_sha256s"],
        "theorem_count": len(seen_theorems),
        "lean_version": lean_ver_proc.stdout.strip(),
        "lake_version": lake_ver_proc.stdout.strip(),
        "leanchecker_modules": ["CleanRoomTimeCutDuality", "AxiomAudit"],
        "observed_axioms": sorted(observed_axioms),
        "zero_classical_choice": "Classical.choice" not in observed_axioms,
    }


def run_pillar_p3(lean_dir: pathlib.Path = DEFAULT_LEAN_DIR) -> dict[str, typing.Any]:
    """Run static R13b & raw-bytes SHA-256 gate on all 5 files in timecut_duality/lean/."""
    pkg = read_and_static_gate_lean_package(lean_dir)
    passed = all(
        (
            pkg["toolchain"] == "leanprover/lean4:v4.36.0",
            pkg["manifest_zero_external_packages"],
            pkg["theorem_count"] == 30,
            len(pkg["file_sha256s"]) == 5,
            all(is_hex64(digest) for digest in pkg["file_sha256s"].values()),
        )
    )
    return {
        "toolchain": pkg["toolchain"],
        "manifest_zero_external_packages": pkg["manifest_zero_external_packages"],
        "theorem_count": pkg["theorem_count"],
        "file_sha256s": pkg["file_sha256s"],
        "passed": passed,
    }


# ---------------------------------------------------------------------------
# Pillar 4: C1P vs. Laminar Crossing & Characteristic-2 vs. Q Rank Obstruction
# ---------------------------------------------------------------------------


def validate_binary_matrix(mat: typing.Any, name: str) -> tuple[int, int]:
    """Validate non-empty rectangular {0, 1} exact-int matrix."""
    require_ok(isinstance(mat, list), f"{name} must be list")
    require_ok(len(mat) >= 1, f"{name} must be non-empty")
    for r_idx, row in enumerate(mat):
        require_ok(isinstance(row, list), f"{name}[{r_idx}] must be list")
        if r_idx == 0:
            require_ok(len(row) >= 1, f"{name} must have >= 1 col")
        else:
            require_ok(len(row) == len(mat[0]), f"{name} must be rectangular")
        for entry in row:
            require_ok(is_exact_int(entry), f"{name} entry must be int")
            require_ok(entry in (0, 1), f"{name} entry must be 0 or 1")
    return len(mat), len(mat[0])


def rank_gf2(mat: list[list[int]]) -> int:
    """Exact matrix rank over GF(2)."""
    m_rows, n_cols = validate_binary_matrix(mat, "mat")
    work = [[val & 1 for val in row] for row in mat]
    rank = 0
    for col in range(n_cols):
        piv = -1
        for r_idx in range(rank, m_rows):
            if work[r_idx][col] == 1:
                piv = r_idx
                break
        if piv == -1:
            continue
        if piv != rank:
            work[rank], work[piv] = work[piv], work[rank]
        for r_idx in range(m_rows):
            if r_idx != rank and work[r_idx][col] == 1:
                work[r_idx] = [work[r_idx][c] ^ work[rank][c] for c in range(n_cols)]
        rank += 1
    return rank


def rank_q_from_binary(mat: list[list[int]]) -> int:
    """Exact matrix rank over Q for a validated {0, 1} matrix."""
    m_rows, n_cols = validate_binary_matrix(mat, "mat")
    zero_q = q_frac(0, 1)
    work = [[q_frac(val, 1) for val in row] for row in mat]
    rank = 0
    for col in range(n_cols):
        piv = -1
        for r_idx in range(rank, m_rows):
            if work[r_idx][col] != zero_q:
                piv = r_idx
                break
        if piv == -1:
            continue
        if piv != rank:
            work[rank], work[piv] = work[piv], work[rank]
        pv = work[rank][col]
        work[rank] = [q_div(val, pv) for val in work[rank]]
        for r_idx in range(m_rows):
            if r_idx != rank and work[r_idx][col] != zero_q:
                fac = work[r_idx][col]
                work[r_idx] = [work[r_idx][c] - fac * work[rank][c] for c in range(n_cols)]
        rank += 1
    return rank


def run_pillar_p4(n18_x_rects: dict[tuple[int, int, int], fractions.Fraction]) -> dict[str, typing.Any]:
    """Certify 1D C1P preservation vs laminar crossing & char-2 vs Q rank drop."""
    intervals = sorted({(a, c) for (a, _b, c) in n18_x_rects.keys()})
    all_1d_c1p_contiguous = all(
        all((sum(1 for pos in range(18) if a <= pos < c) == (c - a), (c - a) >= 2))
        for (a, c) in intervals
    )
    strict_crossing_pairs = sum(
        1
        for idx1 in range(len(intervals))
        for idx2 in range(idx1 + 1, len(intervals))
        if are_two_intervals_strictly_crossing(
            intervals[idx1][0],
            intervals[idx1][1],
            intervals[idx2][0],
            intervals[idx2][1],
        )
    )

    j3_minus_i3 = [
        [0, 1, 1],
        [1, 0, 1],
        [1, 1, 0],
    ]
    rk_q = rank_q_from_binary(j3_minus_i3)
    rk_f2 = rank_gf2(j3_minus_i3)

    grid_3x6_cycles = math.gcd(3, 6)
    grid_2x9_cycles = math.gcd(2, 9)

    passed = all(
        (
            all_1d_c1p_contiguous,
            strict_crossing_pairs == 71,
            rk_q == 3,
            rk_f2 == 2,
            rk_f2 < rk_q,
            grid_3x6_cycles == 3,
            grid_2x9_cycles == 1,
        )
    )
    return {
        "c1p_1d_contiguous_on_all_n18_active_intervals": all_1d_c1p_contiguous,
        "n18_active_span_intervals": len(intervals),
        "n18_strict_laminar_crossing_interval_pairs": strict_crossing_pairs,
        "grid_18cell_3x6_vs_2x9_gcd_cycles": [grid_3x6_cycles, grid_2x9_cycles],
        "char2_vs_q_witness_j3_minus_i3_ranks": [rk_f2, rk_q],
        "passed": passed,
    }


# ---------------------------------------------------------------------------
# Certificate Builder & Hardened Fail-Closed Validators
# ---------------------------------------------------------------------------


def is_exact_int_list_eq(val: typing.Any, expected: list[int]) -> bool:
    """Return True iff val is a list of exact non-bool ints equal to expected."""
    return (
        isinstance(val, list)
        and len(val) == len(expected)
        and all(is_exact_int(x) and x == y for x, y in zip(val, expected))
    )


def verify_core_invariants(core: typing.Any, lean_dir: pathlib.Path = DEFAULT_LEAN_DIR) -> None:
    """Validate structural, mathematical, and on-disk Lean package invariants of unsigned core."""
    self_src = _read_file_nofollow(SELF_SOURCE_PATH, SELF_SOURCE_PATH.name).decode("utf-8")
    verify_pure_q_source_ast(self_src, SELF_SOURCE_PATH.name)

    require_ok(isinstance(core, dict), "certificate core must be dict")
    require_ok(core.get("schema_version") == SCHEMA_VERSION, "schema_version mismatch")
    require_ok(core.get("arithmetic_domain") == ARITHMETIC_DOMAIN, "arithmetic_domain mismatch")
    require_ok(core.get("status") == "VERIFIED", "status must be VERIFIED")

    pillars = core.get("pillars")
    require_ok(isinstance(pillars, dict), "pillars must be dict")

    p1 = pillars.get("p1_timecut_lp_and_threshold")
    require_ok(isinstance(p1, dict), "p1 must be dict")
    require_ok(p1.get("passed") is True, "p1 passed must be True")
    require_ok(
        p1.get("general_rects_verified_all_2_to_20") is True,
        "p1 general_rects_verified_all_2_to_20 must be True",
    )
    require_ok(p1.get("zero_gap_for_all_2_le_n_le_17") is True, "p1 zero gap 2..17")
    require_ok(p1.get("minimal_crossing_advantage_n") == 18, "p1 N_min == 18")
    require_ok(p1.get("n18_laminar_tree_optimum") == 35, "p1 T_18 == 35")
    require_ok(str_to_q(p1.get("n18_lp_optimum"), "n18_lp") == q_frac(107, 3), "p1 P_18 == 107/3")
    require_ok(str_to_q(p1.get("n18_crossing_gap"), "n18_gap") == q_frac(2, 3), "p1 gap18 == 2/3")
    require_ok(str_to_q(p1.get("n19_lp_optimum"), "n19_lp") == q_frac(38, 1), "p1 P_19 == 38")
    require_ok(str_to_q(p1.get("n19_crossing_gap"), "n19_gap") == q_frac(1, 1), "p1 gap19 == 1")

    p2 = pillars.get("p2_banked_cnf_envelope_and_port_gadget")
    require_ok(isinstance(p2, dict), "p2 must be dict")
    require_ok(p2.get("passed") is True, "p2 passed must be True")
    require_ok(p2.get("linear_bit_length_envelope_verified") is True, "p2 linear envelope")
    require_ok(p2.get("naive_2bank_superlinear_inflation_refuted") is True, "p2 2bank blowup")
    require_ok(p2.get("every_field_tseitin_mod2_mod3_obstruction_verified") is True, "p2 tseitin")

    p3 = pillars.get("p3_lean4_package")
    require_ok(isinstance(p3, dict), "p3 must be dict")
    require_ok(p3.get("passed") is True, "p3 passed must be True")
    live_pkg = read_and_static_gate_lean_package(lean_dir)
    recorded_shas = p3.get("file_sha256s")
    require_ok(isinstance(recorded_shas, dict), "file_sha256s must be dict")
    require_ok(
        all(is_hex64(v) for v in recorded_shas.values()),
        "file_sha256s entries must be 64-hex",
    )
    require_ok(
        recorded_shas == live_pkg["file_sha256s"],
        "Lean package on-disk raw-bytes SHA-256 mismatch",
    )
    require_ok(p3.get("theorem_count") == 30, "lean theorem_count != 30")
    require_ok(p3.get("manifest_zero_external_packages") is True, "manifest packages flag")

    p4 = pillars.get("p4_crossing_c1p_and_char2_rank_obstructions")
    require_ok(isinstance(p4, dict), "p4 must be dict")
    require_ok(p4.get("passed") is True, "p4 passed must be True")
    require_ok(
        p4.get("c1p_1d_contiguous_on_all_n18_active_intervals") is True,
        "p4 c1p flag",
    )
    cross_cnt = p4.get("n18_strict_laminar_crossing_interval_pairs")
    require_ok(is_exact_int(cross_cnt), "crossing count must be int")
    require_ok(cross_cnt == 71, "crossing count must equal 71")
    require_ok(
        is_exact_int_list_eq(p4.get("char2_vs_q_witness_j3_minus_i3_ranks"), [2, 3]),
        "p4 char2 vs Q ranks != [2, 3]",
    )

    require_ok(core.get("overall_passed") is True, "overall_passed must be True")


def build_certificate(lean_dir: pathlib.Path = DEFAULT_LEAN_DIR) -> dict[str, typing.Any]:
    """Execute Pillars 1-4, verify core invariants, and seal canonical SHA-256 certificate."""
    p1, solved = run_pillar_p1()
    p2 = run_pillar_p2()
    p3 = run_pillar_p3(lean_dir=lean_dir)
    p4 = run_pillar_p4(solved[18]["x_rects"])
    overall = all_four_pillars_certified(p1["passed"], p2["passed"], p3["passed"], p4["passed"])

    core: dict[str, typing.Any] = {
        "schema_version": SCHEMA_VERSION,
        "arithmetic_domain": ARITHMETIC_DOMAIN,
        "status": "VERIFIED",
        "pillars": {
            "p1_timecut_lp_and_threshold": p1,
            "p2_banked_cnf_envelope_and_port_gadget": p2,
            "p3_lean4_package": p3,
            "p4_crossing_c1p_and_char2_rank_obstructions": p4,
        },
        "overall_passed": overall,
    }
    verify_core_invariants(core, lean_dir=lean_dir)
    payload_sha = sha256_bytes(canonical_json_bytes(core))
    sealed = dict(core)
    sealed["payload_sha256"] = payload_sha
    sealed["certificate_sha256"] = sha256_bytes(canonical_json_bytes(sealed))
    return sealed


def validate_certificate(cert: typing.Any, lean_dir: pathlib.Path = DEFAULT_LEAN_DIR) -> None:
    """Hardened public validator checking invariants, 64-hex digests, & byte-exact oracle replay."""
    verify_core_invariants(cert, lean_dir=lean_dir)
    payload_sha = cert.get("payload_sha256")
    cert_sha = cert.get("certificate_sha256")
    require_ok(is_hex64(payload_sha), "payload_sha256 must be 64-hex")
    require_ok(is_hex64(cert_sha), "certificate_sha256 must be 64-hex")

    unsigned = {
        k: v for k, v in cert.items() if k not in ("payload_sha256", "certificate_sha256")
    }
    require_ok(
        payload_sha == sha256_bytes(canonical_json_bytes(unsigned)),
        "payload_sha256 digest mismatch",
    )
    with_payload = dict(unsigned)
    with_payload["payload_sha256"] = payload_sha
    require_ok(
        cert_sha == sha256_bytes(canonical_json_bytes(with_payload)),
        "certificate_sha256 digest mismatch",
    )
    recomputed = build_certificate(lean_dir=lean_dir)
    require_ok(
        canonical_json_bytes(cert) == canonical_json_bytes(recomputed),
        "certificate diverges from freshly recomputed clean-room oracle",
    )


def format_canonical_certificate_json(
    cert: dict[str, typing.Any], lean_dir: pathlib.Path = DEFAULT_LEAN_DIR
) -> str:
    """Format validated certificate deterministically with 2-space indent."""
    validate_certificate(cert, lean_dir=lean_dir)
    return json.dumps(cert, indent=2, sort_keys=True, ensure_ascii=False, allow_nan=False) + "\n"


def check_certificate_file(
    cert_path: pathlib.Path = DEFAULT_CERT_PATH,
    lean_dir: pathlib.Path = DEFAULT_LEAN_DIR,
) -> dict[str, typing.Any]:
    """Validate on-disk certificate JSON & all 5 on-disk Lean package files via O_NOFOLLOW."""
    raw_bytes = _read_file_nofollow(cert_path, "certificate", max_bytes=MAX_FILE_BYTES)
    raw_text = raw_bytes.decode("utf-8")
    loaded = strict_json_loads(raw_text)
    validate_certificate(loaded, lean_dir=lean_dir)
    expected_bytes = (
        json.dumps(loaded, indent=2, sort_keys=True, ensure_ascii=False, allow_nan=False) + "\n"
    ).encode("utf-8")
    require_ok(raw_bytes == expected_bytes, "on-disk certificate bytes are not canonical")
    return loaded


def _write_stream(stream: typing.TextIO, text: str) -> None:
    """Write and flush text to stream cleanly without EPIPE tracebacks."""
    try:
        stream.write(text)
        stream.flush()
    except BrokenPipeError:
        try:
            stream.close()
        except OSError:
            pass


def main(argv: list[str] | None = None) -> int:
    """CLI entrypoint supporting default check, --check, --write, --json, and --live-lean."""
    parser = argparse.ArgumentParser(
        description="Clean-room exact-Q & Lean 4.36.0 verifier for adjacent-rectangle time-cut duality."
    )
    mode = parser.add_mutually_exclusive_group(required=False)
    mode.add_argument("--check", action="store_true", help="Validate on-disk certificate & Lean files.")
    mode.add_argument("--write", action="store_true", help="Write canonical certificate JSON.")
    mode.add_argument("--json", action="store_true", help="Print canonical certificate JSON.")
    mode.add_argument(
        "--live-lean",
        action="store_true",
        help="Run cold env -i lake build + standalone leanchecker + AxiomAudit on an isolated copy of lean/.",
    )
    parser.add_argument("--cert-path", type=pathlib.Path, default=DEFAULT_CERT_PATH, help="Certificate path.")
    parser.add_argument("--lean-dir", type=pathlib.Path, default=DEFAULT_LEAN_DIR, help="Lean package dir.")
    args = parser.parse_args(argv)

    try:
        if args.write:
            require_ok(len(args.cert_path.name) > 0, "invalid file path for certificate")
            dir_fd = _open_dir_nofollow(args.cert_path.parent, "certificate")
            try:
                cert = build_certificate(lean_dir=args.lean_dir)
                payload_text = format_canonical_certificate_json(cert, lean_dir=args.lean_dir)
                _write_fd_nofollow(dir_fd, args.cert_path.name, payload_text.encode("utf-8"), "certificate")
            finally:
                os.close(dir_fd)
            _write_stream(
                sys.stdout,
                f"WROTE {args.cert_path.name} certificate_sha256={cert['certificate_sha256']}\n",
            )
            return 0
        if args.json:
            cert = build_certificate(lean_dir=args.lean_dir)
            _write_stream(sys.stdout, format_canonical_certificate_json(cert, lean_dir=args.lean_dir))
            return 0
        if args.live_lean:
            cert = check_certificate_file(cert_path=args.cert_path, lean_dir=args.lean_dir)
            lean_live = verify_lean_package_live(lean_dir=args.lean_dir)
            _write_stream(
                sys.stdout,
                f"PASS_LEAN436 theorems={lean_live['theorem_count']} "
                f"leanchecker={','.join(lean_live['leanchecker_modules'])} "
                f"certificate_sha256={cert['certificate_sha256']}\n",
            )
            return 0
        cert = check_certificate_file(cert_path=args.cert_path, lean_dir=args.lean_dir)
        _write_stream(
            sys.stdout,
            f"PASS {args.cert_path.name} certificate_sha256={cert['certificate_sha256']}\n",
        )
        return 0
    except ValueError as exc:
        _write_stream(
            sys.stderr,
            json.dumps({"error": str(exc), "status": "FAIL"}, sort_keys=True, allow_nan=False) + "\n",
        )
        return 2
    except (OSError, RecursionError, MemoryError, subprocess.SubprocessError):
        _write_stream(
            sys.stderr,
            json.dumps(
                {"error": "filesystem, memory, recursion, or subprocess error", "status": "FAIL"},
                sort_keys=True,
                allow_nan=False,
            )
            + "\n",
        )
        return 2


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
