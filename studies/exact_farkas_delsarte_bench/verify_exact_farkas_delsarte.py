"""Exact-Q Farkas & Delsarte Dual-Certificate Verifier and Wall-Clock Benchmark.

Pure Python 3 stdlib, zero-float, zero-ast.Div verifier and monotonic wall-clock CPU benchmark unifying:
  1. Exact-Q Delsarte Krawtchouk coding LP bounds for (n, d) in {(8,4), (12,6), (16,8), (20,10)}
     with full-rank active basis certification and seeded row/column permutation obfuscation.
  2. Exact-Q 1-Lipschitz Quotient LP + Farkas dual flow synthesis on a structured N=48 cyclic
     mode-switch quotient plus seeded vertex/edge permutation obfuscation.
  3. Zero-logarithm exact Farkas infeasibility certificate for the 4-node 355/113 interval cone
     paired with feasible local 3-node sub-cones and BigInt 53-TET Holder comma inequality.
  4. Reproducible monotonic wall-clock benchmark (integer time.perf_counter_ns, <= 300 s, CPU-only)
     comparing sparse O(|E|+N) Farkas certificate verification, dense LP verification, fraction-free
     integer elimination, and naive dense Fraction pivoting, plus a small tractable slowdown control.
"""
from __future__ import annotations

import argparse
import ast
from collections import deque
from errno import EISDIR, ENXIO
from fractions import Fraction
import hashlib
import json
from math import gcd, isqrt
import os
from pathlib import Path
import re
import stat
import sys
import time
from typing import Any, Dict, List, Optional, Sequence, Tuple
import unicodedata


SCHEMA_CERT = "exact_farkas_delsarte_certificate_v1"
SCHEMA_BENCH = "exact_farkas_delsarte_wallclock_benchmark_v1"
ENERGY_POLICY_EXPECTED = "UNCONTROLLED_LAPTOP_NOT_CLAIMED"
CLOCK_SOURCE_EXPECTED = "time.perf_counter_ns"
WALLCLOCK_BUDGET_NS = 300 * 1000 * 1000 * 1000
MAX_JSON_DEPTH = 32
MAX_FILE_BYTES = 1024 * 1024
MAX_INT_DIGITS = 1024
_READ_NOFOLLOW_FLAGS = os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK
_WRITE_NOFOLLOW_FLAGS = os.O_WRONLY | os.O_CREAT | os.O_TRUNC | os.O_NOFOLLOW | os.O_NONBLOCK

PINNED_CERTIFICATE_SHA256 = "29b99332981c2ad709a7d778e42b60cc82c1f73cc8697788239e4db129335673"
PINNED_BENCHMARK_SHA256 = "ddb8d4f75ecd3eda8cffb4329a8b0a778a7a6985dd3094e98692dab2cfcdc6f9"

CERT_ALLOWED_KEYS = frozenset({"schema", "payload", "payload_sha256", "certificate_sha256"})
BENCH_ALLOWED_KEYS = frozenset({"schema", "payload", "payload_sha256", "benchmark_sha256"})
BENCH_PAYLOAD_KEYS = frozenset({
    "schema",
    "energy_power_status",
    "clock_source",
    "wallclock_budget_ns",
    "measured_components_sum_ns",
    "unmeasured_setup_and_verify_ns",
    "total_benchmark_ns",
    "within_wallclock_budget",
    "repeats",
    "linear_basis_scaling",
    "quotient_lp_n48_comparison",
    "tractable_small_control_slowdown",
})
BENCH_SCALING_ROW_KEYS = frozenset({
    "dim",
    "repeats",
    "fangcheng_total_ns",
    "naive_dense_fraction_total_ns",
    "exact_residual_verify_total_ns",
    "fangcheng_vs_naive_speedup_q",
    "verify_vs_naive_speedup_q",
    "verify_vs_fangcheng_speedup_q",
})
BENCH_Q48_KEYS = frozenset({
    "num_vertices",
    "num_edges",
    "repeats",
    "sparse_farkas_verify_total_ns",
    "dense_lp_verify_total_ns",
    "active_basis_fangcheng_total_ns",
    "active_basis_naive_fraction_total_ns",
    "fangcheng_vs_naive_speedup_q",
    "sparse_verify_vs_naive_speedup_q",
    "sparse_verify_vs_fangcheng_speedup_q",
    "sparse_verify_vs_dense_verify_speedup_q",
})
BENCH_CTRL_KEYS = frozenset({
    "num_vertices",
    "num_edges",
    "repeats",
    "direct_spfa_eval_total_ns",
    "full_certified_pipeline_total_ns",
    "certified_over_direct_slowdown_q",
    "slowdown_observed",
})
EXPECTED_SCALING_DIMS = (12, 16, 20)

ALLOWED_IMPORT_MODULES = frozenset({
    "argparse", "ast", "hashlib", "json", "os", "re", "stat", "sys", "time", "unicodedata",
})
ALLOWED_FROM_IMPORTS: Dict[str, frozenset[str]] = {
    "__future__": frozenset({"annotations"}),
    "collections": frozenset({"deque"}),
    "errno": frozenset({"EISDIR", "ENXIO"}),
    "fractions": frozenset({"Fraction"}),
    "math": frozenset({"gcd", "isqrt"}),
    "pathlib": frozenset({"Path"}),
    "time": frozenset({"perf_counter_ns"}),
    "typing": frozenset({"Any", "Dict", "List", "Optional", "Sequence", "Tuple"}),
}
ALLOWED_MODULE_ATTRS: Dict[str, frozenset[str]] = {
    "math": frozenset({"gcd", "isqrt"}),
    "sys": frozenset({"stderr"}),
    "time": frozenset({"perf_counter_ns"}),
    "json": frozenset({"dumps", "loads"}),
    "os": frozenset({
        "O_RDONLY", "O_WRONLY", "O_CREAT", "O_TRUNC", "O_NOFOLLOW", "O_NONBLOCK",
        "open", "fstat", "read", "write", "close",
    }),
}
FORBIDDEN_NAMES = frozenset({
    "float", "complex", "format", "divmod", "round", "open", "memoryview",
    "eval", "exec", "__import__", "getattr", "setattr", "delattr",
    "compile", "globals", "locals", "vars", "builtins", "__builtins__",
})
FORBIDDEN_ATTR_NAMES = frozenset({
    "from_float", "from_decimal", "fromhex", "as_integer_ratio", "format", "format_map",
    "real", "imag", "conjugate", "cast", "literal_eval",
    "__truediv__", "__rtruediv__", "__itruediv__",
    "__floordiv__", "__rfloordiv__", "__ifloordiv__",
    "__mod__", "__rmod__", "__imod__",
    "__pow__", "__rpow__", "__ipow__",
    "__float__", "__complex__", "__format__",
    "__getattribute__", "__getattr__", "__dict__",
    "__class__", "__base__", "__bases__", "__mro__", "__subclasses__", "__globals__",
    "modules", "time", "perf_counter", "process_time", "process_time_ns",
    "monotonic", "monotonic_ns", "thread_time", "thread_time_ns", "sleep",
})
RESTRICTED_SYMBOL_NAMES = frozenset({"Fraction", "pow", "type", "math", "sys", "time", "json", "os"})
FORBIDDEN_PATH_TOKENS = ("/" + "home" + "/", "/" + "users" + "/", "/" + "root" + "/", "c:/users/", "c:\\users\\")
ALLOWLISTED_POLICY_KEYS = frozenset({"energy_power_status"})

_CANON_Q_RE = re.compile(r"\A(?:0|-?[1-9][0-9]*)(?:/[1-9][0-9]*)?\Z")
_PFX = r"(?:p|n|u|\u03bc|m|k|g|t|pico|nano|micro|milli|kilo|mega|giga|tera)"
_UNIT = r"(?:watt[\s_\-\u2013\u2014]{0,2}hours?|watthours?|wattages?|watts?|joules?|whrs?|wh|ws|w|j|tdp)"
_MULTI_UNIT = (
    r"(?:watt[\s_\-\u2013\u2014]{0,2}hours?|watthours?|wattages?|watts?|joules?|whrs?|wh|ws|kwh|mwh|tdp|energy|power"
    r"|(?:p|n|u|\u03bc|m|k|g|t|pico|nano|micro|milli|kilo|mega|giga|tera)[\s_\-\u2013\u2014]{0,2}(?:watts?|joules?|w|j))"
)
_UNIT_SEP = r"[\s_\-\u2013\u2014\u00d7\u00b7\u2219\[\(]{0,3}"
_NUM = r"(?<![0-9])\d+(?:[.,]\d+){0,3}(?:e[+-]?\d+)?"
_UPPER_BARE_WJ_PREFIX_RE = re.compile(r"(?<![A-Za-z0-9])(?:[WJ](?:[\s]{0,3}[:=][\s]{0,3}|[\s]{1,3})\d|W[\s]{0,3}/[\s]{0,3}tok)")
_ENERGY_VALUE_RE = re.compile(
    "(?:"
    rf"{_NUM}{_UNIT_SEP}(?:{_PFX}{_UNIT_SEP})?{_UNIT}(?![a-z0-9])(?!/\s|/o(?![a-z0-9]))(?!\s*=)"
    rf"|(?<![a-z0-9]){_MULTI_UNIT}(?:[\s]{{0,3}}[:=][\s]{{0,3}}|[\s]{{1,3}}){_NUM}(?![a-z0-9_-])"
    rf"|(?<![a-z0-9])(?:{_PFX})?(?:watt(?:s|ages?|hours?)?|joules?)(?![a-z0-9])"
    rf"|(?<![a-z0-9_])(?:kwh|mwh|whrs?)(?![a-z0-9_])"
    r"|\A[\s\[\(\-\u2013\u2014]{0,3}(?:(?:p|n|u|\u03bc|m|k|g|t)?(?:w|j|wh|ws)|tdp)[\s\]\)\?!.,\-\u2013\u2014]{0,3}\Z"
    r"|(?<![a-z0-9])(?:energy|power|joules?|watts?|kwh|mwh|whrs?|wh|ws|[pnu\u03bcmkgt]?j|[pnu\u03bcmkgt]w)[\s_-]{0,3}(?:per|/)[\s_-]{0,3}tok(?:en)?s?(?![a-z0-9])"
    r"|(?<![a-z0-9])w(?:/|[\s_-]{1,3}per[\s_-]{1,3})tok(?:en)?s?(?![a-z0-9])"
    r"|(?<![a-z0-9])tok(?:en)?s?[\s_-]{0,3}(?:per|/)[\s_-]{0,3}(?:energy|power|joules?|watts?|kwh|mwh|whrs?|wh|ws|[pnu\u03bcmkgt]?[jw])(?![a-z0-9])"
    r"|(?:rapl|nvml|nvidia[\s_-]{0,2}smi)"
    r"|(?<![a-z0-9])(?:less|lower|reduced|fewer)[\s_-]{1,3}(?:in[\s_-]{1,3})?(?:energy|power)(?![a-z0-9])"
    r"|(?<![a-z0-9])(?:energy|power)[\s_-]{1,3}(?:use|usage|reduction|savings?|dropped|consumption|draw|budget|cap|limit)(?![a-z0-9])"
    ")"
)
_ENERGY_KEY_RE = re.compile(
    r"(?:(?:^|[^a-z0-9])(?:power|watt|watts|wattage|wattages|joule|joules|energy|kwh|mwh|whr|wh|ws|tdp|mj|uj|mw|kw|gw|tw)(?:[^a-z0-9]|$)"
    r"|(?:rapl|nvml)"
    r"|(?:^|[^a-z0-9])(?:pkg|gpu|cpu|sys|avg|peak|max|min|total|board)[^a-z0-9]{1,3}(?:w|j)(?:[^a-z0-9]|$))"
)
_CAMEL_SPLIT_RE = re.compile(r"([a-z0-9])([A-Z])")


class CertVerifyError(ValueError):
    """Fail-closed verification error."""


def require_ok(cond: bool, msg: str) -> None:
    """Fail-closed guard (never disabled by Python -O)."""
    if cond is not True:
        raise CertVerifyError(msg)


def _is_float_or_complex(obj: Any) -> bool:
    return any(cls.__name__ in ("float", "complex") for cls in type(obj).__mro__)


def q_int(val: int) -> Fraction:
    """Convert strict Python int (not bool/float) to Fraction."""
    require_ok(type(val) is int, "EXPECTED_STRICT_INT")
    return Fraction(val, 1)


def q_make(num: int, den: int) -> Fraction:
    """Construct exact Fraction from two strict Python ints."""
    require_ok(type(num) is int and type(den) is int, "EXPECTED_INT_PAIR")
    require_ok(den != 0, "ZERO_DENOMINATOR")
    return Fraction(num, den)


def q_div(a: Fraction, b: Fraction) -> Fraction:
    """Exact rational division without Python ast.Div '/'."""
    require_ok(isinstance(a, Fraction) and isinstance(b, Fraction), "EXPECTED_FRACTION")
    require_ok(b.numerator != 0, "ZERO_DIVISION")
    return Fraction(a.numerator * b.denominator, a.denominator * b.numerator)


def exact_div_z(num: int, den: int) -> int:
    """Exact integer division failing closed on non-int, zero divisor, or nonzero remainder (no // or divmod)."""
    require_ok(type(num) is int and type(den) is int, "EXACT_DIV_BAD_ARGS")
    require_ok(den != 0, "EXACT_DIV_ZERO")
    if num == 0:
        return 0
    if den == 1:
        return num
    if den == -1:
        return -num
    q_frac = Fraction(num, den)
    require_ok(q_frac.denominator == 1, "BAREISS_INEXACT_DIVISION")
    return q_frac.numerator


def _floor_div_nonneg_z(num: int, den: int) -> int:
    """Exact floor division for num >= 0, den > 0 without // or divmod."""
    require_ok(type(num) is int and type(den) is int and num >= 0 and den > 0, "BAD_FLOOR_DIV_ARGS")
    q = 0
    rem = num
    shift = max(0, num.bit_length() - den.bit_length())
    while shift >= 0:
        d_shifted = den << shift
        if rem >= d_shifted:
            rem -= d_shifted
            q |= 1 << shift
        shift -= 1
    return q


def _mod_nonneg_z(num: int, den: int) -> int:
    """Exact remainder for num >= 0, den > 0 without ast.Mod or divmod."""
    return num - _floor_div_nonneg_z(num, den) * den


def fmt_q(q: Fraction) -> str:
    """Canonical rational string 'p/q'."""
    require_ok(isinstance(q, Fraction), "FMT_EXPECTED_FRACTION")
    return f"{q.numerator}/{q.denominator}"


def parse_q_str(text: str) -> Fraction:
    """Strictly parse canonical ASCII 'p/q' (reduced, positive den) or 'p' into Fraction(int, int)."""
    require_ok(type(text) is str and _CANON_Q_RE.fullmatch(text) is not None, "BAD_Q_STR")
    parts = text.split("/")
    num_s = parts[0]
    num_digits = num_s[1:] if num_s.startswith("-") else num_s
    den_s = "1" if len(parts) == 1 else parts[1]
    require_ok(len(num_digits) <= MAX_INT_DIGITS and len(den_s) <= MAX_INT_DIGITS, "BAD_Q_DIGIT_LIMIT")
    num = int(num_s)
    den = int(den_s)
    require_ok(gcd(abs(num), den) == 1, "BAD_Q_NONCANONICAL")
    return q_make(num, den)


def exact_binom(n: int, k: int) -> int:
    """Exact integer binomial coefficient C(n, k) without math.comb."""
    require_ok(type(n) is int and type(k) is int and n >= 0, "BAD_BINOM_ARGS")
    if k < 0 or k > n:
        return 0
    r = k if k <= n - k else n - k
    out = 1
    for i in range(1, r + 1):
        out = exact_div_z(out * (n - r + i), i)
    return out


def lcm_int(a: int, b: int) -> int:
    """Positive least common multiple of two nonzero integers."""
    require_ok(a != 0 and b != 0, "LCM_ZERO")
    aa = abs(a)
    bb = abs(b)
    return exact_div_z(aa, gcd(aa, bb)) * bb


def canonical_json_bytes(obj: Any) -> bytes:
    """Deterministic UTF-8 canonical JSON serialization."""
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), allow_nan=False, ensure_ascii=True).encode("utf-8")


def formatted_json_bytes(obj: Any) -> bytes:
    """Deterministic UTF-8 pretty JSON serialization for raw-bytes binding."""
    return (json.dumps(obj, indent=2, sort_keys=True, allow_nan=False, ensure_ascii=True) + "\n").encode("utf-8")


def sha256_bytes(data: bytes) -> str:
    """Hex SHA-256 of raw bytes."""
    return hashlib.sha256(data).hexdigest()


def sha256_json(obj: Any) -> str:
    """Hex SHA-256 of canonical JSON."""
    return sha256_bytes(canonical_json_bytes(obj))


def _strip_policy_marks(text: str) -> str:
    norm = unicodedata.normalize("NFKD", unicodedata.normalize("NFKC", text))
    out: List[str] = []
    for ch in norm:
        if ch in ("\t", "\n", "\r"):
            out.append(" ")
        elif unicodedata.category(ch) not in ("Cf", "Mn", "Cc"):
            out.append(ch)
    return "".join(out)


def _has_non_ascii_letter(text: str) -> bool:
    return any(ord(ch) > 127 and ch.isalpha() and ch not in ("\u03bc", "\u00b5") for ch in text)


def is_forbidden_energy_value(text: str) -> bool:
    """Check whether string value carries a forbidden power/energy telemetry claim."""
    require_ok(type(text) is str, "BAD_POLICY_STR")
    cleaned = _strip_policy_marks(text)
    if _UPPER_BARE_WJ_PREFIX_RE.search(cleaned):
        return True
    norm = cleaned.casefold()
    if _has_non_ascii_letter(norm):
        return True
    return bool(_ENERGY_VALUE_RE.search(norm))


def is_forbidden_energy_key(key: str) -> bool:
    """Check whether dict key carries a forbidden power/energy telemetry field name."""
    require_ok(type(key) is str, "BAD_POLICY_KEY")
    if key in ALLOWLISTED_POLICY_KEYS:
        return False
    split_key = _CAMEL_SPLIT_RE.sub(r"\1 \2", key).replace("_", " ")
    cleaned = _strip_policy_marks(split_key)
    norm = cleaned.casefold()
    if _has_non_ascii_letter(norm):
        return True
    return bool(_ENERGY_KEY_RE.search(norm)) or bool(_ENERGY_VALUE_RE.search(norm))


def _is_nonneg_int_const(node: ast.AST) -> bool:
    return isinstance(node, ast.Constant) and type(node.value) is int and node.value >= 0


def _mark_annotation_fractions(ann: Optional[ast.AST], allowed_ids: set[int]) -> None:
    if ann is not None:
        for sub in ast.walk(ann):
            if isinstance(sub, ast.Name) and sub.id == "Fraction":
                allowed_ids.add(id(sub))


def _is_single_arg_type_call(node: ast.AST) -> bool:
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "type"
        and len(node.args) == 1
        and len(node.keywords) == 0
    )


def _collect_allowed_restricted_name_ids(tree: ast.AST) -> Tuple[set[int], set[int]]:
    allowed_ids: set[int] = set()
    allowed_mro_ids: set[int] = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.FunctionDef):
            _mark_annotation_fractions(node.returns, allowed_ids)
        elif isinstance(node, ast.arg):
            _mark_annotation_fractions(node.annotation, allowed_ids)
        elif isinstance(node, ast.AnnAssign):
            _mark_annotation_fractions(node.annotation, allowed_ids)
        elif isinstance(node, ast.Compare):
            if len(node.ops) == 1 and isinstance(node.ops[0], ast.Is) and _is_single_arg_type_call(node.left):
                allowed_ids.add(id(node.left.func))  # type: ignore[attr-defined]
        elif isinstance(node, ast.GeneratorExp):
            if (
                len(node.generators) == 1
                and not node.generators[0].ifs
                and isinstance(node.generators[0].target, ast.Name)
                and isinstance(node.generators[0].iter, ast.Attribute)
                and node.generators[0].iter.attr == "__mro__"
                and _is_single_arg_type_call(node.generators[0].iter.value)
                and isinstance(node.elt, ast.Compare)
                and len(node.elt.ops) == 1
                and isinstance(node.elt.ops[0], ast.In)
                and len(node.elt.comparators) == 1
                and isinstance(node.elt.left, ast.Attribute)
                and isinstance(node.elt.left.value, ast.Name)
                and node.elt.left.value.id == node.generators[0].target.id
                and node.elt.left.attr == "__name__"
                and isinstance(node.elt.comparators[0], ast.Tuple)
                and all(isinstance(e, ast.Constant) and type(e.value) is str for e in node.elt.comparators[0].elts)
            ):
                allowed_mro_ids.add(id(node.generators[0].iter))
                allowed_ids.add(id(node.generators[0].iter.value.func))  # type: ignore[attr-defined]
        elif isinstance(node, ast.Attribute):
            if isinstance(node.value, ast.Name) and node.value.id in ("Fraction", "math", "sys", "time", "json", "os"):
                allowed_ids.add(id(node.value))
        elif isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
            if node.func.id in ("Fraction", "pow"):
                allowed_ids.add(id(node.func))
            elif node.func.id == "isinstance" and len(node.args) == 2:
                if isinstance(node.args[1], ast.Name) and node.args[1].id == "Fraction":
                    allowed_ids.add(id(node.args[1]))
    return allowed_ids, allowed_mro_ids


def verify_ast_purity(source_text: str) -> Dict[str, int]:
    """Closed-allowlist pure-Z/Q AST guard banning /, //, %, floats, format specs, neg Pow, reflection, and unallowed imports."""
    require_ok(type(source_text) is str, "AST_SOURCE_NOT_STR")
    try:
        tree = ast.parse(source_text)
    except (SyntaxError, ValueError) as exc:
        raise CertVerifyError("AST_SYNTAX_ERROR") from exc
    require_ok(len(tree.body) > 0, "AST_EMPTY_SOURCE")
    allowed_restricted_ids, allowed_mro_ids = _collect_allowed_restricted_name_ids(tree)
    visited_nodes = 0
    for node in ast.walk(tree):
        visited_nodes += 1
        require_ok(not isinstance(node, ast.Div), "AST_FORBIDDEN_DIV")
        require_ok(not isinstance(node, ast.FloorDiv), "AST_FORBIDDEN_FLOORDIV")
        require_ok(not isinstance(node, ast.Mod), "AST_FORBIDDEN_MOD")
        require_ok(not isinstance(node, ast.Assert), "AST_FORBIDDEN_BARE_ASSERT")
        if isinstance(node, ast.FormattedValue):
            require_ok(node.format_spec is None, "AST_FORBIDDEN_FORMAT_SPEC")
        elif isinstance(node, ast.Constant):
            require_ok(not _is_float_or_complex(node.value), "AST_FORBIDDEN_FLOAT_LITERAL")
        elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            require_ok(node.name not in RESTRICTED_SYMBOL_NAMES, "AST_FORBIDDEN_SYMBOL_ALIAS")
        elif isinstance(node, ast.Name):
            require_ok(node.id not in FORBIDDEN_NAMES, "AST_FORBIDDEN_NAME")
            if node.id in RESTRICTED_SYMBOL_NAMES:
                require_ok(id(node) in allowed_restricted_ids, "AST_FORBIDDEN_SYMBOL_ALIAS")
        elif isinstance(node, ast.BinOp) and isinstance(node.op, ast.Pow):
            require_ok(_is_nonneg_int_const(node.right), "AST_FORBIDDEN_NEG_POW")
        elif isinstance(node, ast.AugAssign) and isinstance(node.op, ast.Pow):
            require_ok(_is_nonneg_int_const(node.value), "AST_FORBIDDEN_NEG_POW")
        elif isinstance(node, ast.Import):
            for alias in node.names:
                require_ok(alias.name in ALLOWED_IMPORT_MODULES, "AST_FORBIDDEN_IMPORT")
                require_ok(alias.asname is None, "AST_FORBIDDEN_IMPORT_ALIAS")
        elif isinstance(node, ast.ImportFrom):
            require_ok(node.level == 0 and node.module is not None, "AST_RELATIVE_IMPORT")
            allowed_names = ALLOWED_FROM_IMPORTS.get(node.module)
            require_ok(allowed_names is not None, "AST_FORBIDDEN_IMPORT")
            for alias in node.names:
                require_ok(alias.name in allowed_names and alias.asname is None, "AST_FORBIDDEN_IMPORT")
        elif isinstance(node, ast.Attribute):
            if isinstance(node.value, ast.Name) and node.value.id in ALLOWED_MODULE_ATTRS:
                require_ok(node.attr in ALLOWED_MODULE_ATTRS[node.value.id], "AST_FORBIDDEN_MODULE_ATTR")
            if node.attr != "__mro__" or id(node) not in allowed_mro_ids:
                require_ok(node.attr not in FORBIDDEN_ATTR_NAMES, "AST_FORBIDDEN_ATTR")
        elif isinstance(node, ast.Call):
            if isinstance(node.func, ast.Attribute) and isinstance(node.func.value, ast.Name):
                if node.func.value.id == "json" and node.func.attr == "loads":
                    kw_map = {kw.arg: kw.value for kw in node.keywords if kw.arg is not None}
                    require_ok(
                        isinstance(kw_map.get("parse_float"), ast.Name)
                        and isinstance(kw_map.get("parse_constant"), ast.Name),
                        "AST_UNSAFE_JSON_LOADS",
                    )
            elif isinstance(node.func, ast.Name):
                fname = node.func.id
                if fname == "pow":
                    require_ok(
                        len(node.keywords) == 0 and len(node.args) == 2 and _is_nonneg_int_const(node.args[1]),
                        "AST_FORBIDDEN_NEG_POW",
                    )
                if fname == "Fraction":
                    require_ok(len(node.keywords) == 0, "AST_FORBIDDEN_FRACTION_KWARGS")
                    for arg in node.args:
                        is_bad_str = isinstance(arg, ast.Constant) and type(arg.value) is str
                        require_ok(
                            not is_bad_str and not isinstance(arg, (ast.JoinedStr, ast.Starred)),
                            "AST_FORBIDDEN_FRACTION_STR",
                        )
                    require_ok(len(node.args) == 2, "AST_FORBIDDEN_FRACTION_ARITY")
    return {
        "visited_nodes": visited_nodes,
        "ast_div": 0,
        "float_or_complex_literals": 0,
        "forbidden_names": 0,
        "forbidden_math_sys_time": 0,
        "negative_pow": 0,
        "fraction_str_or_from_float": 0,
        "bare_asserts": 0,
    }


def check_json_tree_clean(obj: Any, max_depth: int = MAX_JSON_DEPTH) -> None:
    """Iteratively reject floats, host path leaks, energy claims, and excessive nesting depth."""
    stack: List[Tuple[Any, Optional[str], int]] = [(obj, None, 0)]
    while stack:
        cur, parent_key, depth = stack.pop()
        require_ok(depth <= max_depth, "JSON_MAX_DEPTH_EXCEEDED")
        if _is_float_or_complex(cur):
            raise CertVerifyError("JSON_FORBIDDEN_FLOAT")
        if isinstance(cur, str):
            low = cur.lower()
            for tok in FORBIDDEN_PATH_TOKENS:
                require_ok(tok not in low, "JSON_PATH_LEAK")
            require_ok(not is_forbidden_energy_value(cur), "JSON_ENERGY_CLAIM_VALUE")
            if parent_key in ALLOWLISTED_POLICY_KEYS:
                require_ok(cur == ENERGY_POLICY_EXPECTED, "JSON_ALLOWLIST_SMUGGLE")
        elif isinstance(cur, dict):
            for k, v in cur.items():
                require_ok(type(k) is str, "JSON_KEY_NOT_STR")
                low_k = k.lower()
                for tok in FORBIDDEN_PATH_TOKENS:
                    require_ok(tok not in low_k, "JSON_PATH_LEAK")
                require_ok(not is_forbidden_energy_key(k), "JSON_ENERGY_CLAIM_KEY")
                if k in ALLOWLISTED_POLICY_KEYS:
                    require_ok(type(v) is str, "JSON_ALLOWLIST_SMUGGLE")
                stack.append((v, k, depth + 1))
        elif isinstance(cur, (list, tuple)):
            for item in cur:
                stack.append((item, parent_key, depth + 1))


def _no_dup_pairs(pairs: List[Tuple[str, Any]]) -> Dict[str, Any]:
    out: Dict[str, Any] = {}
    for k, v in pairs:
        require_ok(k not in out, "JSON_DUP_KEY")
        out[k] = v
    return out


def read_regular_bytes_nofollow(path: Path, max_bytes: int = MAX_FILE_BYTES) -> bytes:
    """Read a regular non-symlink file via O_NOFOLLOW|O_NONBLOCK + fstat(S_ISREG) with strict byte cap."""
    require_ok(isinstance(path, Path), "JSON_MISSING")
    require_ok(not path.is_symlink(), "SYMLINK_FORBIDDEN")
    try:
        fd = os.open(str(path), _READ_NOFOLLOW_FLAGS)
    except FileNotFoundError as exc:
        raise CertVerifyError("JSON_MISSING") from exc
    except OSError as exc:
        raise CertVerifyError("JSON_READ_ERROR") from exc
    try:
        require_ok(stat.S_ISREG(os.fstat(fd).st_mode), "NOT_REGULAR_FILE")
        chunks: List[bytes] = []
        total = 0
        while True:
            chunk = os.read(fd, 65536)
            if not chunk:
                break
            total += len(chunk)
            require_ok(total <= max_bytes, "FILE_TOO_LARGE")
            chunks.append(chunk)
        return b"".join(chunks)
    except CertVerifyError:
        raise
    except OSError as exc:
        raise CertVerifyError("JSON_READ_ERROR") from exc
    finally:
        os.close(fd)


def write_regular_bytes_nofollow(path: Path, data: bytes) -> None:
    """Write bytes refusing symlink targets and non-regular destinations via O_NOFOLLOW|O_NONBLOCK."""
    require_ok(not path.is_symlink(), "SYMLINK_FORBIDDEN")
    try:
        fd = os.open(str(path), _WRITE_NOFOLLOW_FLAGS, 0o644)
    except OSError as exc:
        if exc.errno in (ENXIO, EISDIR):
            raise CertVerifyError("NOT_REGULAR_FILE") from exc
        raise CertVerifyError("JSON_WRITE_ERROR") from exc
    try:
        require_ok(stat.S_ISREG(os.fstat(fd).st_mode), "NOT_REGULAR_FILE")
        written = 0
        total = len(data)
        while written < total:
            n = os.write(fd, data[written:])
            require_ok(n > 0, "IO_SHORT_WRITE")
            written += n
    except CertVerifyError:
        raise
    except OSError as exc:
        raise CertVerifyError("JSON_WRITE_ERROR") from exc
    finally:
        os.close(fd)


def _check_json_raw_depth(text: str, max_depth: int = MAX_JSON_DEPTH) -> None:
    """Reject JSON nesting deeper than max_depth before json.loads() runs."""
    depth = 0
    in_str = False
    esc = False
    for ch in text:
        if in_str:
            if esc:
                esc = False
            elif ch == "\\":
                esc = True
            elif ch == '"':
                in_str = False
        elif ch == '"':
            in_str = True
        elif ch in ("{", "["):
            depth += 1
            require_ok(depth <= max_depth, "JSON_MAX_DEPTH_EXCEEDED")
        elif ch in ("}", "]"):
            if depth > 0:
                depth -= 1


def _parse_strict_json_int(tok: str) -> int:
    digits = tok[1:] if tok.startswith("-") else tok
    require_ok(len(digits) <= MAX_INT_DIGITS, "JSON_INT_DIGIT_LIMIT")
    return int(tok)


def load_strict_json(path: Path, max_bytes: int = MAX_FILE_BYTES) -> Tuple[Dict[str, Any], bytes]:
    """Load regular non-symlink JSON rejecting duplicates, floats, NaN/Inf, >1024-digit ints, >32 depth, leaks, and energy claims."""
    def _reject_const(tok: str) -> Any:
        raise CertVerifyError(f"JSON_BAD_CONST:{tok}")

    def _reject_float(tok: str) -> Any:
        raise CertVerifyError(f"JSON_FORBIDDEN_FLOAT:{tok}")

    raw_bytes = read_regular_bytes_nofollow(path, max_bytes=max_bytes)
    try:
        text = raw_bytes.decode("utf-8")
        _check_json_raw_depth(text, MAX_JSON_DEPTH)
        data = json.loads(
            text,
            object_pairs_hook=_no_dup_pairs,
            parse_constant=_reject_const,
            parse_float=_reject_float,
            parse_int=_parse_strict_json_int,
        )
    except CertVerifyError:
        raise
    except (UnicodeDecodeError, ValueError, RecursionError) as exc:
        raise CertVerifyError("JSON_PARSE_ERROR") from exc
    require_ok(isinstance(data, dict), "JSON_ROOT_NOT_DICT")
    check_json_tree_clean(data)
    return data, raw_bytes


def _dot_q(u: Sequence[Fraction], v: Sequence[Fraction]) -> Fraction:
    """Exact inner product of equal-length Fraction vectors."""
    require_ok(len(u) == len(v), "DOT_LEN_MISMATCH")
    acc = Fraction(0, 1)
    for a, b in zip(u, v):
        require_ok(isinstance(a, Fraction) and isinstance(b, Fraction), "NON_EXACT_VALUE")
        acc += a * b
    return acc


def _clear_matrix_denoms_z(rows: Sequence[Sequence[Fraction]]) -> List[List[int]]:
    """Scale each Fraction row by the LCM of its denominators into exact integers."""
    out: List[List[int]] = []
    for row in rows:
        row_lcm = 1
        for val in row:
            require_ok(isinstance(val, Fraction), "NON_EXACT_VALUE")
            row_lcm = lcm_int(row_lcm, val.denominator)
        out.append([val.numerator * exact_div_z(row_lcm, val.denominator) for val in row])
    return out


def fangcheng_rank_z(rows: Sequence[Sequence[int]]) -> int:
    """Exact fraction-free integer Gaussian rank with checked Bareiss divisibility."""
    m = len(rows)
    if m == 0:
        return 0
    n = len(rows[0])
    mat: List[List[int]] = []
    for row in rows:
        require_ok(len(row) == n, "RANK_RAGGED_MATRIX")
        for v in row:
            require_ok(type(v) is int, "RANK_NON_INT")
        mat.append(list(row))
    rank = 0
    prev_pivot = 1
    for col in range(n):
        pivot_row = -1
        for r in range(rank, m):
            if mat[r][col] != 0:
                pivot_row = r
                break
        if pivot_row == -1:
            continue
        if pivot_row != rank:
            mat[rank], mat[pivot_row] = mat[pivot_row], mat[rank]
        pivot = mat[rank][col]
        for r in range(rank + 1, m):
            factor = mat[r][col]
            for c in range(col + 1, n):
                mat[r][c] = exact_div_z(pivot * mat[r][c] - factor * mat[rank][c], prev_pivot)
            mat[r][col] = 0
        prev_pivot = pivot
        rank += 1
        if rank == m:
            break
    return rank


def fangcheng_solve_z(a_rows: Sequence[Sequence[int]], b_vec: Sequence[int]) -> List[Fraction]:
    """Exact fraction-free integer elimination solving A x = b over Q with checked Bareiss divisibility."""
    n = len(a_rows)
    require_ok(n > 0 and len(b_vec) == n, "BAD_SOLVE_DIMS")
    aug: List[List[int]] = []
    for i in range(n):
        require_ok(len(a_rows[i]) == n, "NON_SQUARE_SYSTEM")
        require_ok(type(b_vec[i]) is int, "SOLVE_NON_INT")
        for v in a_rows[i]:
            require_ok(type(v) is int, "SOLVE_NON_INT")
        aug.append(list(a_rows[i]) + [b_vec[i]])
    prev_pivot = 1
    for k in range(n):
        pivot_row = -1
        for r in range(k, n):
            if aug[r][k] != 0:
                pivot_row = r
                break
        require_ok(pivot_row != -1, "SINGULAR_SYSTEM")
        if pivot_row != k:
            aug[k], aug[pivot_row] = aug[pivot_row], aug[k]
        pivot = aug[k][k]
        for r in range(k + 1, n):
            factor = aug[r][k]
            for c in range(k + 1, n + 1):
                aug[r][c] = exact_div_z(pivot * aug[r][c] - factor * aug[k][c], prev_pivot)
            aug[r][k] = 0
        prev_pivot = pivot
    sol: List[Fraction] = [Fraction(0, 1) for _ in range(n)]
    for i in range(n - 1, -1, -1):
        rhs = Fraction(aug[i][n], 1)
        for j in range(i + 1, n):
            rhs -= Fraction(aug[i][j], 1) * sol[j]
        sol[i] = q_div(rhs, Fraction(aug[i][i], 1))
    return sol


def naive_dense_fraction_solve_q(
    a_rows: Sequence[Sequence[Fraction]],
    b_vec: Sequence[Fraction],
) -> List[Fraction]:
    """Naive dense Fraction Gaussian elimination baseline (no ast.Div) for timing comparison."""
    n = len(a_rows)
    require_ok(n > 0 and len(b_vec) == n, "BAD_SOLVE_DIMS")
    aug = [list(a_rows[i]) + [b_vec[i]] for i in range(n)]
    for k in range(n):
        pivot_row = -1
        for r in range(k, n):
            if aug[r][k] != 0:
                pivot_row = r
                break
        require_ok(pivot_row != -1, "SINGULAR_SYSTEM")
        if pivot_row != k:
            aug[k], aug[pivot_row] = aug[pivot_row], aug[k]
        piv = aug[k][k]
        for r in range(k + 1, n):
            mult = q_div(aug[r][k], piv)
            for c in range(k + 1, n + 1):
                aug[r][c] = aug[r][c] - mult * aug[k][c]
            aug[r][k] = Fraction(0, 1)
    sol = [Fraction(0, 1) for _ in range(n)]
    for i in range(n - 1, -1, -1):
        rhs = aug[i][n]
        for j in range(i + 1, n):
            rhs -= aug[i][j] * sol[j]
        sol[i] = q_div(rhs, aug[i][i])
    return sol


def verify_linear_residual_q(
    a_rows: Sequence[Sequence[int]],
    b_vec: Sequence[int],
    x_vec: Sequence[Fraction],
) -> bool:
    """Exact O(n^2) verification of A x == b in pure Q returning True on pass."""
    n = len(a_rows)
    require_ok(len(b_vec) == n and len(x_vec) == n, "RESIDUAL_DIM_MISMATCH")
    for i in range(n):
        require_ok(len(a_rows[i]) == n, "RESIDUAL_ROW_WIDTH_MISMATCH")
        require_ok(type(b_vec[i]) is int, "NON_EXACT_VALUE")
        lhs = Fraction(0, 1)
        for j in range(n):
            require_ok(type(a_rows[i][j]) is int and isinstance(x_vec[j], Fraction), "NON_EXACT_VALUE")
            lhs += Fraction(a_rows[i][j], 1) * x_vec[j]
        require_ok(lhs == Fraction(b_vec[i], 1), "LINEAR_RESIDUAL_NONZERO")
    return True


def verify_quotient_lp_sparse_q(
    num_vertices: int,
    goals: Sequence[int],
    edges: Sequence[Tuple[int, int, Fraction]],
    mu: Sequence[Fraction],
    caps: Sequence[Fraction],
    h_vec: Sequence[Fraction],
    dual_y: Sequence[Fraction],
    dual_z: Sequence[Fraction],
) -> Dict[str, Any]:
    """Fail-closed sparse O(|E| + N) exact-Q verifier for 1-Lipschitz Quotient LP + Farkas flow."""
    require_ok(type(num_vertices) is int and num_vertices > 0, "SPARSE_DIM_MISMATCH")
    require_ok(len(mu) == num_vertices and len(caps) == num_vertices, "SPARSE_DIM_MISMATCH")
    require_ok(len(h_vec) == num_vertices and len(dual_y) == len(edges) and len(dual_z) == num_vertices, "SPARSE_CERT_DIM_MISMATCH")
    for g in goals:
        require_ok(type(g) is int and 0 <= g < num_vertices, "SPARSE_BAD_GOAL")
    goal_set = set(goals)
    for u in range(num_vertices):
        require_ok(isinstance(mu[u], Fraction) and isinstance(caps[u], Fraction), "NON_EXACT_VALUE")
        require_ok(isinstance(h_vec[u], Fraction) and isinstance(dual_z[u], Fraction), "NON_EXACT_VALUE")
        require_ok(h_vec[u] >= 0, "PRIMAL_NEGATIVE_VAR")
        require_ok(dual_z[u] >= 0, "DUAL_SIGN_VIOLATION")
        cap_u = Fraction(0, 1) if u in goal_set else caps[u]
        require_ok(h_vec[u] <= cap_u, "PRIMAL_INFEASIBLE")
    net_flow = list(dual_z)
    dual_obj = Fraction(0, 1)
    for u in range(num_vertices):
        if u not in goal_set:
            dual_obj += caps[u] * dual_z[u]
    for e_idx, (u, v, w) in enumerate(edges):
        require_ok(type(u) is int and 0 <= u < num_vertices, "SPARSE_BAD_EDGE_VERTEX")
        require_ok(type(v) is int and 0 <= v < num_vertices, "SPARSE_BAD_EDGE_VERTEX")
        ye = dual_y[e_idx]
        require_ok(isinstance(w, Fraction) and isinstance(ye, Fraction), "NON_EXACT_VALUE")
        require_ok(ye >= 0, "DUAL_SIGN_VIOLATION")
        require_ok(h_vec[u] - h_vec[v] <= w, "PRIMAL_INFEASIBLE")
        net_flow[u] += ye
        net_flow[v] -= ye
        dual_obj += w * ye
    primal_obj = Fraction(0, 1)
    for u in range(num_vertices):
        require_ok(net_flow[u] >= mu[u], "DUAL_INFEASIBLE")
        primal_obj += mu[u] * h_vec[u]
    require_ok(primal_obj == dual_obj, "DUALITY_GAP_NONZERO")
    return {
        "num_vertices": num_vertices,
        "num_edges": len(edges),
        "primal_obj": fmt_q(primal_obj),
        "dual_obj": fmt_q(dual_obj),
        "duality_gap": "0/1",
    }


def verify_lp_primal_dual_q(
    a_mat: Sequence[Sequence[Fraction]],
    b_vec: Sequence[Fraction],
    c_vec: Sequence[Fraction],
    x_vec: Sequence[Fraction],
    y_vec: Sequence[Fraction],
    sense: str,
    active_rows: Optional[Sequence[int]] = None,
    active_cols: Optional[Sequence[int]] = None,
) -> Dict[str, Any]:
    """Fail-closed exact-Q primal/dual LP certificate verifier with active-support rank check."""
    require_ok(sense in ("max_le", "min_ge"), "BAD_LP_SENSE")
    m = len(a_mat)
    n = len(c_vec)
    require_ok(m > 0 and n > 0, "EMPTY_LP")
    require_ok(len(b_vec) == m and len(x_vec) == n and len(y_vec) == m, "LP_DIM_MISMATCH")
    for val in x_vec:
        require_ok(isinstance(val, Fraction), "NON_EXACT_VALUE")
        require_ok(val >= 0, "PRIMAL_NEGATIVE_VAR")
    for val in y_vec:
        require_ok(isinstance(val, Fraction), "NON_EXACT_VALUE")
        require_ok(val >= 0, "DUAL_SIGN_VIOLATION")

    ax_vals: List[Fraction] = []
    for i in range(m):
        row = a_mat[i]
        require_ok(len(row) == n, "LP_ROW_WIDTH_MISMATCH")
        val = _dot_q(row, x_vec)
        if sense == "max_le":
            require_ok(val <= b_vec[i], "PRIMAL_INFEASIBLE")
        else:
            require_ok(val >= b_vec[i], "PRIMAL_INFEASIBLE")
        ax_vals.append(val)

    for j in range(n):
        aty = Fraction(0, 1)
        for i in range(m):
            aty += a_mat[i][j] * y_vec[i]
        if sense == "max_le":
            require_ok(aty >= c_vec[j], "DUAL_INFEASIBLE")
        else:
            require_ok(aty <= c_vec[j], "DUAL_INFEASIBLE")

    primal_obj = _dot_q(c_vec, x_vec)
    dual_obj = _dot_q(b_vec, y_vec)
    require_ok(primal_obj == dual_obj, "DUALITY_GAP_NONZERO")

    active_rank = 0
    if active_rows is not None:
        require_ok(len(active_rows) > 0, "EMPTY_ACTIVE_SUPPORT")
        require_ok(len(set(active_rows)) == len(active_rows), "DUP_ACTIVE_ROW")
        if active_cols is None:
            cols = list(range(n))
        else:
            cols = list(active_cols)
            require_ok(len(cols) > 0, "EMPTY_ACTIVE_COLS")
            require_ok(len(set(cols)) == len(cols), "DUP_ACTIVE_COL")
            for c_idx in cols:
                require_ok(type(c_idx) is int and 0 <= c_idx < n, "BAD_ACTIVE_COL")
        sub_q: List[List[Fraction]] = []
        for r_idx in active_rows:
            require_ok(type(r_idx) is int and 0 <= r_idx < m, "BAD_ACTIVE_ROW")
            require_ok(ax_vals[r_idx] == b_vec[r_idx], "INACTIVE_ROW_IN_SUPPORT")
            sub_q.append([a_mat[r_idx][c_idx] for c_idx in cols])
        active_rank = fangcheng_rank_z(_clear_matrix_denoms_z(sub_q))
        require_ok(active_rank == len(active_rows), "RANK_DEFICIENT_ACTIVE_SUPPORT")

    return {
        "sense": sense,
        "num_rows": m,
        "num_cols": n,
        "primal_obj": fmt_q(primal_obj),
        "dual_obj": fmt_q(dual_obj),
        "duality_gap": "0/1",
        "active_support_rank": active_rank,
    }


def verify_farkas_infeasibility_q(
    a_mat: Sequence[Sequence[Fraction]],
    b_vec: Sequence[Fraction],
    y_vec: Sequence[Fraction],
) -> Dict[str, Any]:
    """Certify Ax <= b (x free) is infeasible via y >= 0, A^T y == 0, b^T y < 0."""
    m = len(a_mat)
    require_ok(m > 0 and len(b_vec) == m and len(y_vec) == m, "FARKAS_DIM_MISMATCH")
    n = len(a_mat[0])
    require_ok(n > 0, "FARKAS_EMPTY_COLS")
    for i in range(m):
        require_ok(len(a_mat[i]) == n, "FARKAS_ROW_WIDTH_MISMATCH")
        require_ok(isinstance(b_vec[i], Fraction), "NON_EXACT_VALUE")
        for entry in a_mat[i]:
            require_ok(isinstance(entry, Fraction), "NON_EXACT_VALUE")
    for val in y_vec:
        require_ok(isinstance(val, Fraction), "NON_EXACT_VALUE")
        require_ok(val >= 0, "FARKAS_DUAL_NEGATIVE")
    for j in range(n):
        col_dot = Fraction(0, 1)
        for i in range(m):
            col_dot += a_mat[i][j] * y_vec[i]
        require_ok(col_dot == 0, "FARKAS_ATY_NONZERO")
    bty = _dot_q(b_vec, y_vec)
    require_ok(bty < 0, "FARKAS_BTY_NOT_NEGATIVE")
    return {
        "num_rows": m,
        "num_cols": n,
        "b_dot_y": fmt_q(bty),
        "infeasible_certified": True,
    }


def verify_retention_gate_q(gain_perm: Fraction, gain_orig: Fraction) -> Fraction:
    """Certify exact 1/1 rational gain retention under pure permutation obfuscation."""
    require_ok(isinstance(gain_orig, Fraction) and gain_orig > 0, "RETENTION_NONPOSITIVE_ORIG")
    retention = q_div(gain_perm, gain_orig)
    require_ok(retention == Fraction(1, 1), "OBFUSCATION_RETENTION_MISMATCH")
    return retention


def verify_local_subcone_q(
    lows: Sequence[Fraction],
    highs: Sequence[Fraction],
    idxs: Sequence[int],
    alpha0: Fraction,
    alpha1: Fraction,
) -> List[str]:
    """Certify affine witness (alpha0, alpha1) lies inside every indexed interval box."""
    vals: List[str] = []
    for k in idxs:
        val = alpha0 + Fraction(k, 1) * alpha1
        require_ok(lows[k] <= val <= highs[k], "LOCAL_SUBCONE_INFEASIBLE")
        vals.append(fmt_q(val))
    return vals


def seeded_perm(length: int, seed: int) -> List[int]:
    """Pure-integer deterministic LCG Fisher-Yates permutation (zero floats/random)."""
    perm = list(range(length))
    state = (seed * 1103515245 + 12345) & 0x7FFFFFFF
    for i in range(length - 1, 0, -1):
        state = (state * 1103515245 + 12345) & 0x7FFFFFFF
        j = _mod_nonneg_z(state, i + 1)
        perm[i], perm[j] = perm[j], perm[i]
    return perm


def permute_lp(
    a_mat: Sequence[Sequence[Fraction]],
    b_vec: Sequence[Fraction],
    c_vec: Sequence[Fraction],
    x_vec: Sequence[Fraction],
    y_vec: Sequence[Fraction],
    row_perm: Sequence[int],
    col_perm: Sequence[int],
) -> Tuple[List[List[Fraction]], List[Fraction], List[Fraction], List[Fraction], List[Fraction]]:
    """Apply exact row/column permutation obfuscation (P_r A P_c, P_r b, P_c^T c)."""
    p_a = [[a_mat[r][c] for c in col_perm] for r in row_perm]
    p_b = [b_vec[r] for r in row_perm]
    p_c = [c_vec[c] for c in col_perm]
    p_x = [x_vec[c] for c in col_perm]
    p_y = [y_vec[r] for r in row_perm]
    return p_a, p_b, p_c, p_x, p_y


def krawtchouk_int(n: int, k: int, i: int) -> int:
    """Exact integer binary Krawtchouk polynomial K_k(i; n)."""
    total = 0
    for j in range(k + 1):
        term = exact_binom(i, j) * exact_binom(n - i, k - j)
        total = total - term if (j & 1) == 1 else total + term
    return total


def build_delsarte_plotkin_lp(
    m_half: int,
) -> Tuple[List[List[Fraction]], List[Fraction], List[Fraction], List[Fraction], List[Fraction], List[int], List[int]]:
    """Construct exact Delsarte LP for binary (n=2m, d=m) Plotkin/Hadamard/RM family."""
    n = 2 * m_half
    d = m_half
    cols = list(range(d, n + 1))
    a_mat: List[List[Fraction]] = []
    b_vec: List[Fraction] = []
    for k in range(1, n + 1):
        a_mat.append([Fraction(-krawtchouk_int(n, k, i), 1) for i in cols])
        b_vec.append(Fraction(exact_binom(n, k), 1))
    c_vec = [Fraction(1, 1) for _ in cols]
    x_vec = [Fraction(0, 1) for _ in cols]
    x_vec[0] = Fraction(4 * m_half - 2, 1)
    x_vec[-1] = Fraction(1, 1)
    y_vec = [Fraction(0, 1) for _ in range(n)]
    y_vec[0] = Fraction(1, 1)
    y_vec[1] = Fraction(1, m_half)
    active_rows = [0, 1]
    active_cols = [0, len(cols) - 1]
    return a_mat, b_vec, c_vec, x_vec, y_vec, active_rows, active_cols


def hamming_sphere_packing_bound(n: int, d: int) -> int:
    """Exact integer Hamming sphere-packing upper bound floor(2^n / sum_{j<=t} C(n, j))."""
    t = (d - 1) >> 1
    vol = sum(exact_binom(n, j) for j in range(t + 1))
    return _floor_div_nonneg_z(1 << n, vol)


def run_family1_delsarte() -> Dict[str, Any]:
    """Certify exact-Q Delsarte bounds for n in {8,12,16,20} + row/col obfuscation retention."""
    cases: List[Dict[str, Any]] = []
    for m_half in (4, 6, 8, 10):
        n = 2 * m_half
        d = m_half
        a_mat, b_vec, c_vec, x_vec, y_vec, act_r, act_c = build_delsarte_plotkin_lp(m_half)
        cert = verify_lp_primal_dual_q(
            a_mat, b_vec, c_vec, x_vec, y_vec, "max_le", active_rows=act_r, active_cols=act_c
        )
        m_bound = 1 + parse_q_str(cert["dual_obj"])
        singleton = 1 << (n - d + 1)
        hamming = hamming_sphere_packing_bound(n, d)
        entry: Dict[str, Any] = {
            "n": n,
            "d": d,
            "singleton_bound": singleton,
            "hamming_bound": hamming,
            "delsarte_exact_bound": fmt_q(m_bound),
            "tightening_over_hamming": fmt_q(Fraction(hamming, 1) - m_bound),
            "lp_check": cert,
            "dual_poly_nonzero": {"y_1": fmt_q(y_vec[0]), "y_2": fmt_q(y_vec[1])},
        }
        if m_half in (8, 10):
            r_perm = seeded_perm(len(a_mat), 154000 + n)
            c_perm = seeded_perm(len(c_vec), 154100 + n)
            p_a, p_b, p_c, p_x, p_y = permute_lp(a_mat, b_vec, c_vec, x_vec, y_vec, r_perm, c_perm)
            inv_r = [0] * len(r_perm)
            for idx, orig in enumerate(r_perm):
                inv_r[orig] = idx
            inv_c = [0] * len(c_perm)
            for idx, orig in enumerate(c_perm):
                inv_c[orig] = idx
            p_act_r = [inv_r[r] for r in act_r]
            p_act_c = [inv_c[c] for c in act_c]
            p_cert = verify_lp_primal_dual_q(
                p_a, p_b, p_c, p_x, p_y, "max_le", active_rows=p_act_r, active_cols=p_act_c
            )
            p_bound = 1 + parse_q_str(p_cert["dual_obj"])
            gain_orig = Fraction(hamming, 1) - m_bound
            gain_perm = Fraction(hamming, 1) - p_bound
            retention = verify_retention_gate_q(gain_perm, gain_orig)
            entry["obfuscated_permutation_check"] = {
                "seed_rows": 154000 + n,
                "seed_cols": 154100 + n,
                "delsarte_exact_bound": fmt_q(p_bound),
                "gain_retention": fmt_q(retention),
                "active_support_rank": p_cert["active_support_rank"],
            }
        cases.append(entry)
    return {
        "family": "F1_DELSARTE_KRAWTCHOUK_PLOTKIN_RM",
        "cases": cases,
        "all_zero_duality_gap": True,
        "obfuscation_retention_min": "1/1",
    }


def synthesize_quotient_lp_exact(
    num_vertices: int,
    goals: Sequence[int],
    edges: Sequence[Tuple[int, int, Fraction]],
    mu: Sequence[Fraction],
    caps: Sequence[Fraction],
) -> Tuple[List[List[Fraction]], List[Fraction], List[Fraction], List[Fraction], List[Fraction], List[int]]:
    """Synthesize exact-Q 1-Lipschitz Quotient LP primal h* and Farkas dual flow (y*, z*)."""
    rev_adj: List[List[Tuple[int, Fraction, int]]] = [[] for _ in range(num_vertices)]
    for e_idx, (u, v, w) in enumerate(edges):
        rev_adj[v].append((u, w, e_idx))

    h: List[Fraction] = list(caps)
    p_kind: List[str] = ["cap"] * num_vertices
    p_idx: List[int] = list(range(num_vertices))
    goal_set = set(goals)
    q: deque[int] = deque(range(num_vertices))
    in_q = [True] * num_vertices
    for g in goals:
        h[g] = Fraction(0, 1)
        p_kind[g] = "goal"
        p_idx[g] = g

    while q:
        v = q.popleft()
        in_q[v] = False
        hv = h[v]
        for u, w, e_idx in rev_adj[v]:
            cand = hv + w
            if cand < h[u]:
                h[u] = cand
                p_kind[u] = "edge"
                p_idx[u] = e_idx
                if not in_q[u]:
                    q.append(u)
                    in_q[u] = True

    order = sorted(range(num_vertices), key=lambda u: h[u], reverse=True)
    flow_at = list(mu)
    dual_y = [Fraction(0, 1) for _ in range(len(edges))]
    dual_z = [Fraction(0, 1) for _ in range(num_vertices)]
    for u in order:
        if p_kind[u] == "goal":
            continue
        fu = flow_at[u]
        if p_kind[u] == "cap":
            dual_z[u] += fu
        else:
            e_id = p_idx[u]
            _, nxt_v, _ = edges[e_id]
            dual_y[e_id] += fu
            flow_at[nxt_v] += fu

    a_mat: List[List[Fraction]] = []
    b_vec: List[Fraction] = []
    for u, v, w in edges:
        row = [Fraction(0, 1) for _ in range(num_vertices)]
        row[u] = Fraction(1, 1)
        row[v] = Fraction(-1, 1)
        a_mat.append(row)
        b_vec.append(w)
    for u in range(num_vertices):
        row = [Fraction(0, 1) for _ in range(num_vertices)]
        row[u] = Fraction(1, 1)
        a_mat.append(row)
        b_vec.append(Fraction(0, 1) if u in goal_set else caps[u])

    active_rows: List[int] = []
    for u in range(num_vertices):
        if p_kind[u] == "edge":
            active_rows.append(p_idx[u])
        else:
            active_rows.append(len(edges) + u)
    for g in goals:
        dual_z[g] = flow_at[g]

    y_all = dual_y + dual_z
    return a_mat, b_vec, list(mu), h, y_all, active_rows


def build_cyclic_quotient_graph(
    nx: int,
    ny: int,
    modes: int,
) -> Tuple[int, List[int], List[Tuple[int, int, Fraction]], List[Fraction], List[Fraction]]:
    """Build structured cyclic mode-switch quotient graph."""
    num_v = nx * ny * modes
    edges: List[Tuple[int, int, Fraction]] = []

    def vid(x: int, y: int, md: int) -> int:
        return (x * ny + y) * modes + md

    for x in range(nx):
        for y in range(ny):
            for md in range(modes):
                u = vid(x, y, md)
                edges.append((u, vid(_mod_nonneg_z(x + 1, nx), y, md), Fraction(5, 4)))
                edges.append((u, vid(_mod_nonneg_z(x - 1 + nx, nx), y, md), Fraction(3, 2)))
                edges.append((u, vid(x, _mod_nonneg_z(y + 1, ny), md), Fraction(7, 4)))
                edges.append((u, vid(x, _mod_nonneg_z(y - 1 + ny, ny), md), Fraction(1, 1)))
                edges.append((u, vid(x, y, _mod_nonneg_z(md + 1, modes)), Fraction(3, 4)))
    goals = [0, vid(nx - 1, ny - 1, modes - 1)]
    mu = [Fraction(1 + _mod_nonneg_z(u, 3), 2) for u in range(num_v)]
    caps = [Fraction(20, 1) for _ in range(num_v)]
    return num_v, goals, edges, mu, caps


def run_family2_quotient_lp() -> Dict[str, Any]:
    """Certify N=48 structured cyclic Quotient-LP + seeded vertex/edge obfuscation control."""
    num_v, goals, edges, mu, caps = build_cyclic_quotient_graph(6, 4, 2)
    a_mat, b_vec, c_vec, h_vec, y_vec, act_rows = synthesize_quotient_lp_exact(
        num_v, goals, edges, mu, caps
    )
    cert_orig = verify_lp_primal_dual_q(
        a_mat, b_vec, c_vec, h_vec, y_vec, "max_le", active_rows=act_rows
    )
    sparse_orig = verify_quotient_lp_sparse_q(
        num_v, goals, edges, mu, caps, h_vec, y_vec[:len(edges)], y_vec[len(edges):]
    )
    v_perm = seeded_perm(num_v, 154048)
    inv_v = [0] * num_v
    for new_u, old_u in enumerate(v_perm):
        inv_v[old_u] = new_u
    e_perm = seeded_perm(len(edges), 154049)
    p_edges = [(inv_v[edges[ei][0]], inv_v[edges[ei][1]], edges[ei][2]) for ei in e_perm]
    p_goals = sorted(inv_v[g] for g in goals)
    p_mu = [mu[v_perm[new_u]] for new_u in range(num_v)]
    p_caps = [caps[v_perm[new_u]] for new_u in range(num_v)]
    pa, pb, pc, ph, py, pact = synthesize_quotient_lp_exact(
        num_v, p_goals, p_edges, p_mu, p_caps
    )
    cert_perm = verify_lp_primal_dual_q(pa, pb, pc, ph, py, "max_le", active_rows=pact)
    obj_orig = parse_q_str(cert_orig["dual_obj"])
    obj_perm = parse_q_str(cert_perm["dual_obj"])
    retention = verify_retention_gate_q(obj_perm, obj_orig)
    return {
        "family": "F2_QUOTIENT_LP_1LIPSCHITZ_FARKAS_FLOW",
        "num_vertices": num_v,
        "num_edges": len(edges),
        "orig_check": cert_orig,
        "sparse_check": sparse_orig,
        "obfuscated_check": {
            "seed_vertices": 154048,
            "seed_edges": 154049,
            "primal_obj": cert_perm["primal_obj"],
            "dual_obj": cert_perm["dual_obj"],
            "active_support_rank": cert_perm["active_support_rank"],
            "bound_retention": fmt_q(retention),
        },
    }


def run_family3_zero_log_farkas() -> Dict[str, Any]:
    """Certify zero-log Farkas infeasibility on 4-node 355/113 cone + local feasibility + Holder comma."""
    lows = [Fraction(355, 113), Fraction(2, 1), Fraction(2, 1), Fraction(355, 113)]
    highs = [Fraction(4, 1), Fraction(3, 1), Fraction(3, 1), Fraction(4, 1)]
    a_mat: List[List[Fraction]] = []
    b_vec: List[Fraction] = []
    for k in range(4):
        a_mat.append([Fraction(1, 1), Fraction(k, 1)])
        b_vec.append(highs[k])
    for k in range(4):
        a_mat.append([Fraction(-1, 1), Fraction(-k, 1)])
        b_vec.append(-lows[k])
    y_global = [
        Fraction(0, 1), Fraction(1, 1), Fraction(1, 1), Fraction(0, 1),
        Fraction(1, 1), Fraction(0, 1), Fraction(0, 1), Fraction(1, 1),
    ]
    farkas_cert = verify_farkas_infeasibility_q(a_mat, b_vec, y_global)

    local_witnesses = [
        ("subcone_012", (0, 1, 2), Fraction(355, 113), Fraction(-16, 113)),
        ("subcone_123", (1, 2, 3), Fraction(307, 113), Fraction(16, 113)),
    ]
    local_out: Dict[str, Any] = {}
    for label, idxs, a0, a1 in local_witnesses:
        vals = verify_local_subcone_q(lows, highs, idxs, a0, a1)
        local_out[label] = {"alpha0": fmt_q(a0), "alpha1": fmt_q(a1), "values": vals}

    holder_lhs = 3 ** 53
    holder_rhs = 1 << 84
    holder_gap = holder_lhs - holder_rhs
    return {
        "family": "F3_ZERO_LOG_FARKAS_INFEASIBILITY_OBSTRUCTION",
        "zu_chongzhi_global_farkas": farkas_cert,
        "local_3node_feasible_witnesses": local_out,
        "holder_comma_53tet": {
            "three_pow_53": str(holder_lhs),
            "two_pow_84": str(holder_rhs),
            "positive_gap": str(holder_gap),
        },
    }


def build_structured_integer_system(dim: int) -> Tuple[List[List[int]], List[int]]:
    """Build well-conditioned diagonally dominant integer basis system of dimension dim."""
    a_rows: List[List[int]] = []
    b_vec: List[int] = []
    for i in range(dim):
        row: List[int] = []
        rhs = 0
        for j in range(dim):
            val = (dim * dim + 3 * i + 1) if i == j else _mod_nonneg_z((i + 2) * (j + 1), 7) - 3
            row.append(val)
            rhs += val * (j + 1)
        a_rows.append(row)
        b_vec.append(rhs)
    return a_rows, b_vec


def build_deterministic_certificate() -> Dict[str, Any]:
    """Build 100% deterministic pure-Z/Q certificate with hardened AST self-audit."""
    source_text = read_regular_bytes_nofollow(Path(__file__)).decode("utf-8")
    ast_purity = verify_ast_purity(source_text)
    ast_summary = {k: v for k, v in ast_purity.items() if k != "visited_nodes"}
    payload: Dict[str, Any] = {
        "schema": SCHEMA_CERT,
        "energy_power_status": ENERGY_POLICY_EXPECTED,
        "ast_purity_self_audit": ast_summary,
        "family1_delsarte": run_family1_delsarte(),
        "family2_quotient_lp": run_family2_quotient_lp(),
        "family3_zero_log_farkas": run_family3_zero_log_farkas(),
        "exact_math_guard_check": {"isqrt_10000": isqrt(10000), "gcd_355_113": gcd(355, 113)},
    }
    check_json_tree_clean(payload)
    payload_sha = sha256_json(payload)
    cert: Dict[str, Any] = {
        "schema": SCHEMA_CERT,
        "payload": payload,
        "payload_sha256": payload_sha,
    }
    cert["certificate_sha256"] = sha256_json(cert)
    return cert


def check_certificate_artifact(cert_path: Path, require_pinned: bool = False) -> Dict[str, Any]:
    """Fail-closed live recomputation, key-allowlist, optional pin, and raw-bytes SHA-256 verification."""
    disk, raw_bytes = load_strict_json(cert_path)
    require_ok(frozenset(disk.keys()) == CERT_ALLOWED_KEYS, "CERT_KEYS_MISMATCH")
    require_ok(disk["schema"] == SCHEMA_CERT, "CERT_SCHEMA_MISMATCH")
    require_ok(isinstance(disk["payload"], dict), "CERT_PAYLOAD_NOT_DICT")
    payload = disk["payload"]
    require_ok(payload.get("energy_power_status") == ENERGY_POLICY_EXPECTED, "CERT_ENERGY_STATUS_BAD")
    require_ok(disk["payload_sha256"] == sha256_json(payload), "CERT_PAYLOAD_SHA_MISMATCH")
    body = {"schema": disk["schema"], "payload": payload, "payload_sha256": disk["payload_sha256"]}
    require_ok(disk["certificate_sha256"] == sha256_json(body), "CERT_SHA_MISMATCH")
    fresh = build_deterministic_certificate()
    require_ok(fresh["certificate_sha256"] == disk["certificate_sha256"], "CERT_LIVE_RECOMPUTE_MISMATCH")
    if require_pinned:
        require_ok(disk["certificate_sha256"] == PINNED_CERTIFICATE_SHA256, "CERT_PIN_MISMATCH")
    require_ok(sha256_bytes(raw_bytes) == sha256_bytes(formatted_json_bytes(fresh)), "CERT_RAW_BYTES_MISMATCH")
    return fresh


def _verify_bench_solutions(
    a_rows: Sequence[Sequence[int]],
    b_vec: Sequence[int],
    sol_fc: Sequence[Fraction],
    sol_naive: Sequence[Fraction],
    expected: Sequence[Fraction],
) -> None:
    """Verify exact equality and zero residual for both benchmarked linear solvers."""
    require_ok(list(sol_fc) == list(expected), "BENCH_SOL_FC_MISMATCH")
    require_ok(list(sol_naive) == list(expected), "BENCH_SOL_NAIVE_MISMATCH")
    verify_linear_residual_q(a_rows, b_vec, sol_fc)
    verify_linear_residual_q(a_rows, b_vec, sol_naive)


def _verify_small_ctrl_equal(dist: Sequence[Fraction], certified_h: Sequence[Fraction]) -> None:
    """Verify uncertified direct SPFA distance vector matches certified LP primal vector."""
    require_ok(list(dist) == list(certified_h), "BENCH_SMALL_CTRL_MISMATCH")


def _direct_spfa_eval(
    num_vertices: int,
    goals: Sequence[int],
    edges: Sequence[Tuple[int, int, Fraction]],
    caps: Sequence[Fraction],
) -> List[Fraction]:
    """Uncertified direct SPFA evaluation building reverse adjacency inside the timed path."""
    rev_adj: List[List[Tuple[int, Fraction]]] = [[] for _ in range(num_vertices)]
    for u, v, w in edges:
        rev_adj[v].append((u, w))
    dist = list(caps)
    dq: deque[int] = deque(goals)
    for g in goals:
        dist[g] = Fraction(0, 1)
    while dq:
        vv = dq.popleft()
        dv = dist[vv]
        for uu, ww in rev_adj[vv]:
            cand = dv + ww
            if cand < dist[uu]:
                dist[uu] = cand
                dq.append(uu)
    return dist


def run_wallclock_benchmark(repeats: int = 5) -> Dict[str, Any]:
    """Run live monotonic wall-clock benchmark (pure-int perf_counter_ns, <= 300 s, small slowdown control)."""
    require_ok(type(repeats) is int and repeats >= 2, "BAD_REPEATS")
    t_total_start = time.perf_counter_ns()
    measured_sum_ns = 0

    linear_scaling: List[Dict[str, Any]] = []
    for dim in EXPECTED_SCALING_DIMS:
        a_int, b_int = build_structured_integer_system(dim)
        a_q = [[Fraction(v, 1) for v in row] for row in a_int]
        b_q = [Fraction(v, 1) for v in b_int]
        expected_sol = [Fraction(j + 1, 1) for j in range(dim)]

        # Untimed 1-iteration warm-up before timed repeats
        warm_fc = fangcheng_solve_z(a_int, b_int)
        warm_nv = naive_dense_fraction_solve_q(a_q, b_q)
        _verify_bench_solutions(a_int, b_int, warm_fc, warm_nv, expected_sol)

        t0 = time.perf_counter_ns()
        sol_fc: List[Fraction] = []
        for _ in range(repeats):
            sol_fc = fangcheng_solve_z(a_int, b_int)
        t_fc_ns = max(1, time.perf_counter_ns() - t0)

        t1 = time.perf_counter_ns()
        sol_naive: List[Fraction] = []
        for _ in range(repeats):
            sol_naive = naive_dense_fraction_solve_q(a_q, b_q)
        t_naive_ns = max(1, time.perf_counter_ns() - t1)

        t2 = time.perf_counter_ns()
        for _ in range(repeats):
            verify_linear_residual_q(a_int, b_int, sol_fc)
        t_verify_ns = max(1, time.perf_counter_ns() - t2)

        _verify_bench_solutions(a_int, b_int, sol_fc, sol_naive, expected_sol)
        measured_sum_ns += t_fc_ns + t_naive_ns + t_verify_ns
        linear_scaling.append({
            "dim": dim,
            "repeats": repeats,
            "fangcheng_total_ns": t_fc_ns,
            "naive_dense_fraction_total_ns": t_naive_ns,
            "exact_residual_verify_total_ns": t_verify_ns,
            "fangcheng_vs_naive_speedup_q": fmt_q(Fraction(t_naive_ns, t_fc_ns)),
            "verify_vs_naive_speedup_q": fmt_q(Fraction(t_naive_ns, t_verify_ns)),
            "verify_vs_fangcheng_speedup_q": fmt_q(Fraction(t_fc_ns, t_verify_ns)),
        })

    num_v, goals, edges, mu, caps = build_cyclic_quotient_graph(6, 4, 2)
    q_a, q_b, q_c, q_h, q_y, q_act = synthesize_quotient_lp_exact(num_v, goals, edges, mu, caps)
    q_dual_y = q_y[:len(edges)]
    q_dual_z = q_y[len(edges):]
    q_sub_q = [q_a[r] for r in q_act]
    q_sub_b_q = [q_b[r] for r in q_act]
    q_sub_b_int: List[int] = []
    q_sub_int_rhs_aligned: List[List[int]] = []
    for r in q_act:
        row_lcm = 1
        for val in q_a[r]:
            row_lcm = lcm_int(row_lcm, val.denominator)
        row_lcm = lcm_int(row_lcm, q_b[r].denominator)
        q_sub_b_int.append(q_b[r].numerator * exact_div_z(row_lcm, q_b[r].denominator))
        q_sub_int_rhs_aligned.append([val.numerator * exact_div_z(row_lcm, val.denominator) for val in q_a[r]])

    # Untimed warm-up for N=48 Quotient-LP
    verify_quotient_lp_sparse_q(num_v, goals, edges, mu, caps, q_h, q_dual_y, q_dual_z)
    verify_lp_primal_dual_q(q_a, q_b, q_c, q_h, q_y, "max_le")

    t_qsp0 = time.perf_counter_ns()
    for _ in range(repeats):
        verify_quotient_lp_sparse_q(num_v, goals, edges, mu, caps, q_h, q_dual_y, q_dual_z)
    t_q_sparse_ns = max(1, time.perf_counter_ns() - t_qsp0)

    t_qv0 = time.perf_counter_ns()
    for _ in range(repeats):
        verify_lp_primal_dual_q(q_a, q_b, q_c, q_h, q_y, "max_le")
    t_q_dense_verify_ns = max(1, time.perf_counter_ns() - t_qv0)

    t_qfc0 = time.perf_counter_ns()
    sol_q_fc: List[Fraction] = []
    for _ in range(repeats):
        sol_q_fc = fangcheng_solve_z(q_sub_int_rhs_aligned, q_sub_b_int)
    t_q_fc_ns = max(1, time.perf_counter_ns() - t_qfc0)

    t_qn0 = time.perf_counter_ns()
    sol_q_naive: List[Fraction] = []
    for _ in range(repeats):
        sol_q_naive = naive_dense_fraction_solve_q(q_sub_q, q_sub_b_q)
    t_q_naive_ns = max(1, time.perf_counter_ns() - t_qn0)

    _verify_bench_solutions(q_sub_int_rhs_aligned, q_sub_b_int, sol_q_fc, sol_q_naive, q_h)
    measured_sum_ns += t_q_sparse_ns + t_q_dense_verify_ns + t_q_fc_ns + t_q_naive_ns

    s_nv, s_goals, s_edges, s_mu, s_caps = build_cyclic_quotient_graph(3, 1, 2)
    ctrl_reps = repeats * 10
    warm_dist = _direct_spfa_eval(s_nv, s_goals, s_edges, s_caps)
    sa_w, sb_w, sc_w, sh_w, sy_w, sact_w = synthesize_quotient_lp_exact(s_nv, s_goals, s_edges, s_mu, s_caps)
    verify_lp_primal_dual_q(sa_w, sb_w, sc_w, sh_w, sy_w, "max_le", active_rows=sact_w)
    _verify_small_ctrl_equal(warm_dist, sh_w)

    t_dir0 = time.perf_counter_ns()
    dist: List[Fraction] = []
    for _ in range(ctrl_reps):
        dist = _direct_spfa_eval(s_nv, s_goals, s_edges, s_caps)
    t_direct_small_ns = max(1, time.perf_counter_ns() - t_dir0)

    t_cert0 = time.perf_counter_ns()
    sh: List[Fraction] = []
    for _ in range(ctrl_reps):
        sa, sb, sc, sh, sy, sact = synthesize_quotient_lp_exact(s_nv, s_goals, s_edges, s_mu, s_caps)
        verify_lp_primal_dual_q(sa, sb, sc, sh, sy, "max_le", active_rows=sact)
    t_certified_small_ns = max(1, time.perf_counter_ns() - t_cert0)

    _verify_small_ctrl_equal(dist, sh)
    measured_sum_ns += t_direct_small_ns + t_certified_small_ns

    t_total_ns = max(measured_sum_ns, time.perf_counter_ns() - t_total_start)
    require_ok(t_total_ns <= WALLCLOCK_BUDGET_NS, "BENCH_TIME_OVER_BUDGET")
    unmeasured_ns = t_total_ns - measured_sum_ns

    payload: Dict[str, Any] = {
        "schema": SCHEMA_BENCH,
        "energy_power_status": ENERGY_POLICY_EXPECTED,
        "clock_source": CLOCK_SOURCE_EXPECTED,
        "wallclock_budget_ns": WALLCLOCK_BUDGET_NS,
        "measured_components_sum_ns": measured_sum_ns,
        "unmeasured_setup_and_verify_ns": unmeasured_ns,
        "total_benchmark_ns": t_total_ns,
        "within_wallclock_budget": True,
        "repeats": repeats,
        "linear_basis_scaling": linear_scaling,
        "quotient_lp_n48_comparison": {
            "num_vertices": num_v,
            "num_edges": len(edges),
            "repeats": repeats,
            "sparse_farkas_verify_total_ns": t_q_sparse_ns,
            "dense_lp_verify_total_ns": t_q_dense_verify_ns,
            "active_basis_fangcheng_total_ns": t_q_fc_ns,
            "active_basis_naive_fraction_total_ns": t_q_naive_ns,
            "fangcheng_vs_naive_speedup_q": fmt_q(Fraction(t_q_naive_ns, t_q_fc_ns)),
            "sparse_verify_vs_naive_speedup_q": fmt_q(Fraction(t_q_naive_ns, t_q_sparse_ns)),
            "sparse_verify_vs_fangcheng_speedup_q": fmt_q(Fraction(t_q_fc_ns, t_q_sparse_ns)),
            "sparse_verify_vs_dense_verify_speedup_q": fmt_q(Fraction(t_q_dense_verify_ns, t_q_sparse_ns)),
        },
        "tractable_small_control_slowdown": {
            "num_vertices": s_nv,
            "num_edges": len(s_edges),
            "repeats": ctrl_reps,
            "direct_spfa_eval_total_ns": t_direct_small_ns,
            "full_certified_pipeline_total_ns": t_certified_small_ns,
            "certified_over_direct_slowdown_q": fmt_q(Fraction(t_certified_small_ns, t_direct_small_ns)),
            "slowdown_observed": t_certified_small_ns > t_direct_small_ns,
        },
    }
    check_json_tree_clean(payload)
    payload_sha = sha256_json(payload)
    bench: Dict[str, Any] = {
        "schema": SCHEMA_BENCH,
        "payload": payload,
        "payload_sha256": payload_sha,
    }
    bench["benchmark_sha256"] = sha256_json(bench)
    return bench


def _require_pos_int(val: Any, code: str) -> int:
    require_ok(type(val) is int and val > 0, code)
    return val


def _require_nonneg_int(val: Any, code: str) -> int:
    require_ok(type(val) is int and val >= 0, code)
    return val


def check_benchmark_artifact(bench_path: Path, require_pinned: bool = False) -> Dict[str, Any]:
    """Fail-closed validation of benchmark receipt (closed allowlists, exact accounting, optional pin, ratios)."""
    disk, raw_bytes = load_strict_json(bench_path)
    require_ok(frozenset(disk.keys()) == BENCH_ALLOWED_KEYS, "BENCH_KEYS_MISMATCH")
    require_ok(disk["schema"] == SCHEMA_BENCH, "BENCH_SCHEMA_MISMATCH")
    require_ok(isinstance(disk["payload"], dict), "BENCH_PAYLOAD_NOT_DICT")
    payload = disk["payload"]
    require_ok(frozenset(payload.keys()) == BENCH_PAYLOAD_KEYS, "BENCH_PAYLOAD_KEYS_MISMATCH")
    require_ok(payload["schema"] == SCHEMA_BENCH, "BENCH_PAYLOAD_SCHEMA_MISMATCH")
    require_ok(payload["clock_source"] == CLOCK_SOURCE_EXPECTED, "BENCH_CLOCK_SOURCE_BAD")
    require_ok(payload["wallclock_budget_ns"] == WALLCLOCK_BUDGET_NS, "BENCH_BUDGET_CONST_MISMATCH")
    require_ok(disk["payload_sha256"] == sha256_json(payload), "BENCH_PAYLOAD_SHA_MISMATCH")
    body = {"schema": disk["schema"], "payload": payload, "payload_sha256": disk["payload_sha256"]}
    require_ok(disk["benchmark_sha256"] == sha256_json(body), "BENCH_SHA_MISMATCH")
    if require_pinned:
        require_ok(disk["benchmark_sha256"] == PINNED_BENCHMARK_SHA256, "BENCH_PIN_MISMATCH")
    require_ok(sha256_bytes(raw_bytes) == sha256_bytes(formatted_json_bytes(disk)), "BENCH_RAW_BYTES_MISMATCH")

    repeats = payload["repeats"]
    require_ok(type(repeats) is int and repeats >= 2, "BENCH_REPEATS_BAD")
    total_ns = _require_pos_int(payload["total_benchmark_ns"], "BENCH_TIME_BAD")
    require_ok(total_ns <= WALLCLOCK_BUDGET_NS, "BENCH_TIME_OVER_BUDGET")
    require_ok(payload["within_wallclock_budget"] is True, "BENCH_BUDGET_FLAG_FALSE")
    measured_sum_ns = _require_pos_int(payload["measured_components_sum_ns"], "BENCH_MEASURED_SUM_BAD")
    overhead_ns = _require_nonneg_int(payload["unmeasured_setup_and_verify_ns"], "BENCH_OVERHEAD_BAD")

    scaling = payload["linear_basis_scaling"]
    require_ok(isinstance(scaling, list) and len(scaling) == len(EXPECTED_SCALING_DIMS), "BENCH_SCALING_BAD")
    actual_component_sum = 0
    for idx, row in enumerate(scaling):
        require_ok(isinstance(row, dict), "BENCH_SCALING_ROW_BAD")
        require_ok(frozenset(row.keys()) == BENCH_SCALING_ROW_KEYS, "BENCH_SCALING_ROW_KEYS_MISMATCH")
        require_ok(type(row["dim"]) is int and row["dim"] == EXPECTED_SCALING_DIMS[idx], "BENCH_SCALING_DIM_MISMATCH")
        require_ok(type(row["repeats"]) is int and row["repeats"] == repeats, "BENCH_SCALING_REPEATS_MISMATCH")
        fc_ns = _require_pos_int(row["fangcheng_total_ns"], "BENCH_SCALING_NS_BAD")
        nv_ns = _require_pos_int(row["naive_dense_fraction_total_ns"], "BENCH_SCALING_NS_BAD")
        vf_ns = _require_pos_int(row["exact_residual_verify_total_ns"], "BENCH_SCALING_NS_BAD")
        require_ok(parse_q_str(row["fangcheng_vs_naive_speedup_q"]) == Fraction(nv_ns, fc_ns), "BENCH_RATIO_MISMATCH")
        require_ok(parse_q_str(row["verify_vs_naive_speedup_q"]) == Fraction(nv_ns, vf_ns), "BENCH_RATIO_MISMATCH")
        require_ok(parse_q_str(row["verify_vs_fangcheng_speedup_q"]) == Fraction(fc_ns, vf_ns), "BENCH_RATIO_MISMATCH")
        actual_component_sum += fc_ns + nv_ns + vf_ns

    q48 = payload["quotient_lp_n48_comparison"]
    require_ok(isinstance(q48, dict), "BENCH_Q48_MISSING")
    require_ok(frozenset(q48.keys()) == BENCH_Q48_KEYS, "BENCH_Q48_KEYS_MISMATCH")
    require_ok(type(q48["num_vertices"]) is int and q48["num_vertices"] == 48, "BENCH_Q48_META_MISMATCH")
    require_ok(type(q48["num_edges"]) is int and q48["num_edges"] == 240, "BENCH_Q48_META_MISMATCH")
    require_ok(type(q48["repeats"]) is int and q48["repeats"] == repeats, "BENCH_Q48_META_MISMATCH")
    sp_ns = _require_pos_int(q48["sparse_farkas_verify_total_ns"], "BENCH_Q48_NS_BAD")
    dn_ns = _require_pos_int(q48["dense_lp_verify_total_ns"], "BENCH_Q48_NS_BAD")
    qfc_ns = _require_pos_int(q48["active_basis_fangcheng_total_ns"], "BENCH_Q48_NS_BAD")
    qnv_ns = _require_pos_int(q48["active_basis_naive_fraction_total_ns"], "BENCH_Q48_NS_BAD")
    require_ok(parse_q_str(q48["fangcheng_vs_naive_speedup_q"]) == Fraction(qnv_ns, qfc_ns), "BENCH_Q48_RATIO_MISMATCH")
    require_ok(parse_q_str(q48["sparse_verify_vs_naive_speedup_q"]) == Fraction(qnv_ns, sp_ns), "BENCH_Q48_RATIO_MISMATCH")
    require_ok(parse_q_str(q48["sparse_verify_vs_fangcheng_speedup_q"]) == Fraction(qfc_ns, sp_ns), "BENCH_Q48_RATIO_MISMATCH")
    require_ok(parse_q_str(q48["sparse_verify_vs_dense_verify_speedup_q"]) == Fraction(dn_ns, sp_ns), "BENCH_Q48_RATIO_MISMATCH")
    actual_component_sum += sp_ns + dn_ns + qfc_ns + qnv_ns

    ctrl = payload["tractable_small_control_slowdown"]
    require_ok(isinstance(ctrl, dict), "BENCH_CTRL_MISSING")
    require_ok(frozenset(ctrl.keys()) == BENCH_CTRL_KEYS, "BENCH_CTRL_KEYS_MISMATCH")
    require_ok(type(ctrl["num_vertices"]) is int and ctrl["num_vertices"] == 6, "BENCH_CTRL_META_MISMATCH")
    require_ok(type(ctrl["num_edges"]) is int and ctrl["num_edges"] == 30, "BENCH_CTRL_META_MISMATCH")
    require_ok(type(ctrl["repeats"]) is int and ctrl["repeats"] == repeats * 10, "BENCH_CTRL_META_MISMATCH")
    dir_ns = _require_pos_int(ctrl["direct_spfa_eval_total_ns"], "BENCH_CTRL_NS_BAD")
    crt_ns = _require_pos_int(ctrl["full_certified_pipeline_total_ns"], "BENCH_CTRL_NS_BAD")
    require_ok(parse_q_str(ctrl["certified_over_direct_slowdown_q"]) == Fraction(crt_ns, dir_ns), "BENCH_CTRL_RATIO_MISMATCH")
    require_ok(ctrl["slowdown_observed"] is (crt_ns > dir_ns), "BENCH_CTRL_FLAG_MISMATCH")
    actual_component_sum += dir_ns + crt_ns

    require_ok(measured_sum_ns == actual_component_sum, "BENCH_COMPONENT_SUM_MISMATCH")
    require_ok(total_ns == measured_sum_ns + overhead_ns, "BENCH_TOTAL_ACCOUNTING_MISMATCH")
    return disk


def parse_args(argv: Optional[Sequence[str]] = None) -> argparse.Namespace:
    """Parse CLI arguments."""
    parser = argparse.ArgumentParser(description="Exact-Q Farkas/Delsarte verifier and wall-clock benchmark.")
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--write", type=Path, help="Write deterministic certificate JSON.")
    group.add_argument("--check", type=Path, help="Verify deterministic certificate JSON.")
    group.add_argument("--benchmark", type=Path, help="Run live CPU wall-clock benchmark and write JSON.")
    group.add_argument("--check-bench", type=Path, help="Verify wall-clock benchmark JSON receipt.")
    parser.add_argument("--repeats", type=int, default=5, help="Benchmark repeat count (>= 2, default: 5).")
    parser.add_argument(
        "--require-pinned",
        action="store_true",
        help="Require PINNED_CERTIFICATE_SHA256 / PINNED_BENCHMARK_SHA256 (rejected on --benchmark).",
    )
    return parser.parse_args(argv)


def main(argv: Optional[Sequence[str]] = None) -> int:
    """CLI entrypoint returning 0 on PASS, 2 on fail-closed verification or I/O error."""
    args = parse_args(argv)
    try:
        if args.write is not None:
            cert = build_deterministic_certificate()
            if args.require_pinned:
                require_ok(cert["certificate_sha256"] == PINNED_CERTIFICATE_SHA256, "CERT_PIN_MISMATCH")
            write_regular_bytes_nofollow(args.write, formatted_json_bytes(cert))
            print(json.dumps({"status": "WROTE_CERT", "certificate_sha256": cert["certificate_sha256"]}))
            return 0
        if args.check is not None:
            cert = check_certificate_artifact(args.check, require_pinned=args.require_pinned)
            print(json.dumps({"status": "PASS_CERT", "certificate_sha256": cert["certificate_sha256"]}))
            return 0
        if args.benchmark is not None:
            require_ok(not args.require_pinned, "BENCH_LIVE_CANNOT_REQUIRE_PINNED")
            bench = run_wallclock_benchmark(repeats=args.repeats)
            write_regular_bytes_nofollow(args.benchmark, formatted_json_bytes(bench))
            print(json.dumps({"status": "WROTE_BENCH", "benchmark_sha256": bench["benchmark_sha256"]}))
            return 0
        if args.check_bench is not None:
            bench = check_benchmark_artifact(args.check_bench, require_pinned=args.require_pinned)
            print(json.dumps({"status": "PASS_BENCH", "benchmark_sha256": bench["benchmark_sha256"]}))
            return 0
        cert = build_deterministic_certificate()
        if args.require_pinned:
            require_ok(cert["certificate_sha256"] == PINNED_CERTIFICATE_SHA256, "CERT_PIN_MISMATCH")
        print(json.dumps(cert, indent=2, sort_keys=True))
        return 0
    except (CertVerifyError, OSError) as exc:
        print(f"FAIL_CLOSED: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
