#!/usr/bin/env python3
"""Must-fail R5 verification suite for Clean-Room Time-Cut Duality & Lean 4.36.0 Package.

Enforces:
  - Hardened AST pure-Q / pure-Z guard (zero float/complex, zero /, zero **, zero ImportFrom,
    zero Fraction.from_float / Fraction(str), zero bare asserts) + negative controls for every rule.
  - Strict JSON loader rejecting duplicate keys at any depth, float literals, and NaN/Infinity.
  - Raw-bytes SHA-256 binding on all 5 files in timecut_duality/lean/ (1-byte tamper refusal on
    CleanRoomTimeCutDuality.lean, AxiomAudit.lean, lake-manifest.json, lakefile.toml, lean-toolchain).
  - Char-literal-safe ('\"', '"', '\'', '\\', x'+y') Lean comment/string stripper negative controls.
  - Complete truth-table and boundary coverage of simplex, primal-dual validator, banked CNF
    envelope, 5-clause port gadget, and GF(2)/Q matrix rank checks.
"""

import copy
import fractions
import io
import os
import pathlib
import shutil
import stat
import subprocess
import sys
import tempfile
import unittest
import unittest.mock


SCRIPT_DIR = pathlib.Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import verify_timecut_duality

vtd = verify_timecut_duality


VERIFIER_PATH = SCRIPT_DIR.joinpath("verify_timecut_duality.py")
TEST_PATH = pathlib.Path(__file__).resolve()

TEST_ALLOWED_IMPORTS = vtd.ALLOWED_STDLIB_IMPORTS | frozenset(
    {"copy", "io", "unittest", "unittest.mock", "verify_timecut_duality"}
)


def resign_cert(cert: dict) -> dict:
    """Recompute payload_sha256 and certificate_sha256 on a modified certificate dict."""
    unsigned = {
        k: v for k, v in cert.items() if k not in ("payload_sha256", "certificate_sha256")
    }
    cert["payload_sha256"] = vtd.sha256_bytes(vtd.canonical_json_bytes(unsigned))
    with_p = dict(unsigned)
    with_p["payload_sha256"] = cert["payload_sha256"]
    cert["certificate_sha256"] = vtd.sha256_bytes(vtd.canonical_json_bytes(with_p))
    return cert


class TestTimeCutStaticAstAndJsonGuards(unittest.TestCase):
    """Hardened AST pure-Q guard, strict JSON loader, and on-disk hygiene checks."""

    def test_ast_guard_passes_sources_and_rejects_all_forbidden_constructs(self) -> None:
        vtd.verify_pure_q_source_ast(VERIFIER_PATH.read_text(encoding="utf-8"), VERIFIER_PATH.name)
        vtd.verify_pure_q_source_ast(
            TEST_PATH.read_text(encoding="utf-8"),
            TEST_PATH.name,
            allowed_imports=TEST_ALLOWED_IMPORTS,
        )

        with self.assertRaisesRegex(ValueError, "src must be str"):
            vtd.verify_pure_q_source_ast(123)

        # Positive controls covering non-Fraction attribute assign, annotated assign, and 2-arg int/var Fraction
        vtd.verify_pure_q_source_ast(
            "import fractions\n"
            "import math\n"
            "def h(x: fractions.Fraction) -> fractions.Fraction:\n"
            "    return x\n"
            "a: int = 1\n"
            "b: fractions.Fraction | None = None\n"
            "f1 = fractions.Fraction(1, 2)\n"
            "f2 = fractions.Fraction(a, 2)\n"
            "ok = isinstance(f1, fractions.Fraction)\n"
            "g = math.gcd(4, 6)\n",
            "<good>",
        )

        bad_snippets = (
            ("def (\n", "syntax error in <bad>"),
            ("assert True\n", "bare assert forbidden"),
            ("x = 1 / 2\n", "division operator"),
            ("x = 4\nx /= 2\n", "division operator"),
            ("x = 1 // 2\n", "floor division operator"),
            ("x = 4\nx //= 2\n", "floor division operator"),
            ("x = 2 ** -1\n", "power operator"),
            ("x = 2 ** (0 - 1)\n", "power operator"),
            ("k = 3\nx = 2 ** k\n", "power operator"),
            ("x = 2\nx **= 3\n", "power operator"),
            ("x = (y := 1)\n", "walrus operator"),
            ("from fractions import Fraction\n", "ImportFrom forbidden"),
            ("import math as m\n", "import alias forbidden"),
            ("import decimal\n", "disallowed import: decimal"),
            ("import unittest\n", "disallowed import: unittest"),
            ("x = 0.5\n", "float/complex literal forbidden"),
            ("x = 1j\n", "float/complex literal forbidden"),
            ("x = f'{1:.3f}'\n", "format spec forbidden"),
            ("x = float(1)\n", "forbidden builtin identifier: float"),
            ("f = float\n", "forbidden builtin identifier: float"),
            ("x = [float][0]\n", "forbidden builtin identifier: float"),
            ("x = [float][0]('0.5')\n", "indirect call target forbidden"),
            ("x = complex(1)\n", "forbidden builtin identifier: complex"),
            ("x = pow(2, -1)\n", "forbidden builtin identifier: pow"),
            ("x = eval('1')\n", "forbidden builtin identifier: eval"),
            ("x = getattr(1, 'real')\n", "forbidden builtin identifier: getattr"),
            ("x = vars()\n", "forbidden builtin identifier: vars"),
            ("x = __builtins__\n", "forbidden dunder identifier: __builtins__"),
            ("x = __import__('math')\n", "forbidden dunder identifier: __import__"),
            ("x: int(1) = 1\n", "calls forbidden in type annotations"),
            ("import math\nm = math\nx = m.sqrt(2)\n", "aliasing or passing math module"),
            ("import fractions\nfr = fractions\n", "aliasing or passing fractions module"),
            ("import math\nx = math.log(2)\n", "disallowed math attribute: math.log"),
            ("import math\nx = math.pi\n", "forbidden attribute access: pi"),
            ("import math\nx = [math.gcd][0]\n", "uncalled math.gcd reference"),
            ("import math\nx = id(math.gcd)\n", "uncalled math.gcd reference"),
            ("import fractions\nx = fractions.Fraction.from_float(1)\n", "from_float"),
            ("import fractions\nx = fractions.Fraction.from_decimal(1)\n", "from_decimal"),
            ("import fractions\nx = fractions.gcd\n", "disallowed fractions attribute"),
            ("import fractions\nx = fractions.Fraction('1/2')\n", "exact 2-arg positional"),
            ("import fractions\nx = fractions.Fraction('1', 2)\n", "literal argument must be exact int"),
            ("import fractions\nx = fractions.Fraction(True, 2)\n", "literal argument must be exact int"),
            ("import fractions\np = (1, 2)\nx = fractions.Fraction(*p, 1)\n", "starred arguments forbidden"),
            ("import fractions\nx = fractions.Fraction(3)\n", "exact 2-arg positional"),
            (
                "import fractions\nx = fractions.Fraction(1, denominator=2)\n",
                "exact 2-arg positional",
            ),
            ("import fractions\nF = fractions.Fraction\n", "uncalled or aliased fractions.Fraction"),
            (
                "import fractions\nF: object = fractions.Fraction\nx = F('0.5')\n",
                "uncalled or aliased fractions.Fraction",
            ),
            (
                "import fractions\nx = (F := fractions.Fraction)('0.5')\n",
                "indirect call target forbidden",
            ),
            (
                "import fractions\nx = [fractions.Fraction][0]\n",
                "uncalled or aliased fractions.Fraction",
            ),
            (
                "import fractions\nx = [fractions.Fraction][0]('0.5')\n",
                "indirect call target forbidden",
            ),
            (
                "import fractions\nx = (fractions.Fraction,)[0]\n",
                "uncalled or aliased fractions.Fraction",
            ),
            (
                "import fractions\nx = id(fractions.Fraction)\n",
                "uncalled or aliased fractions.Fraction",
            ),
            (
                "import fractions\nx = issubclass(int, fractions.Fraction)\n",
                "uncalled or aliased fractions.Fraction",
            ),
            (
                "import fractions\nx = isinstance(fractions.Fraction)\n",
                "uncalled or aliased fractions.Fraction",
            ),
            (
                "import fractions\nx = isinstance(1, fractions.Fraction, 2)\n",
                "uncalled or aliased fractions.Fraction",
            ),
            (
                "import fractions\nx = isinstance(1, fractions.Fraction, k=1)\n",
                "uncalled or aliased fractions.Fraction",
            ),
            (
                "import fractions\nx = isinstance(fractions.Fraction, object)\n",
                "uncalled or aliased fractions.Fraction",
            ),
            (
                "import fractions\nx = (a.isinstance)(1, fractions.Fraction)\n",
                "uncalled or aliased fractions.Fraction",
            ),
            ("x = (1).real\n", "forbidden attribute access: real"),
            ("x = (1).imag\n", "forbidden attribute access: imag"),
            ("x = (1).conjugate()\n", "forbidden attribute access: conjugate"),
            ("x = (1).as_integer_ratio()\n", "forbidden attribute access: as_integer_ratio"),
            ("x = '%.2f' % (1,)\n", "modulo/format operator"),
            ("x = 5\nx %= 2\n", "modulo/format operator"),
            ("x = '{:.2f}'.format(1)\n", "forbidden attribute access: format"),
            ("x = '{a:.2f}'.format_map({'a': 1})\n", "forbidden attribute access: format_map"),
            ("import ast\nx = ast.literal_eval('0.5')\n", "forbidden attribute access: literal_eval"),
            ("x = type(1)\n", "forbidden builtin identifier: type"),
            ("import fractions\nx = type(fractions.Fraction(1, 1))('1.5')\n", "indirect call target forbidden"),
            ("x = f()('1.5')\n", "indirect call target forbidden"),
            ("x = [f][0]('1.5')\n", "indirect call target forbidden"),
            ("import json\nj = json\n", "aliasing or passing json module"),
            ("import json\nx = json.JSONDecoder\n", "disallowed json attribute: json.JSONDecoder"),
            ("import json\nx = [json.loads][0]\n", "uncalled json.loads reference"),
            ("import json\nx = id(json.loads)\n", "uncalled json.loads reference"),
            ("import json\nx = json.loads('1.5')\n", "json.loads\\(\\) requires object_pairs_hook"),
            (
                "import json\nx = json.loads('1.5', parse_float=None)\n",
                "json.loads\\(\\) requires object_pairs_hook",
            ),
            (
                "import json\nx = json.loads('1.5', None)\n",
                "requires single positional text arg",
            ),
            (
                "import json\nkw = {}\nx = json.loads('1.5', **kw)\n",
                "kwargs unpacking forbidden",
            ),
            (
                "import json\n"
                "x = json.loads('1.5', object_pairs_hook=_reject_duplicate_json_keys, "
                "parse_int=_parse_bounded_json_int, parse_float=bad_fn, "
                "parse_constant=_reject_json_constant)\n",
                "requires parse_float=_reject_json_float",
            ),
            ("import json\nx = json.dumps({'a': 1})\n", "requires allow_nan=False"),
            ("import json\nx = json.dumps({'a': 1}, allow_nan=True)\n", "requires allow_nan=False"),
            ("import json\nkw = {}\nx = json.dumps({'a': 1}, **kw)\n", "kwargs unpacking forbidden"),
            ("import os\no = os\n", "aliasing or passing os module"),
            ("import os\nx = os.system('true')\n", "disallowed os attribute: os.system"),
            ("x = (1).__getattribute__('__truediv__')\n", "forbidden dunder attribute access"),
            ("x = (1).__getattribute__('__truediv__')(2)\n", "indirect call target forbidden"),
            ("x = (1).__float__()\n", "forbidden dunder attribute access"),
            ("x = (1).__complex__()\n", "forbidden dunder attribute access"),
            ("x = (1).__truediv__(2)\n", "forbidden dunder attribute access"),
            ("x = (2).__pow__(-1)\n", "forbidden dunder attribute access"),
            ("import sys\nx = sys.modules\n", "forbidden attribute access: modules"),
            ("import sys\nx = sys.__builtins__\n", "forbidden dunder attribute access"),
        )
        for code, pat in bad_snippets:
            with self.assertRaisesRegex(ValueError, pat):
                vtd.verify_pure_q_source_ast(code, "<bad>")

        # canonical_json_bytes must reject runtime NaN via allow_nan=False (tested in isolated subprocess)
        nan_probe = subprocess.run(
            [
                "/usr/bin/python3",
                "-I",
                "-B",
                "-c",
                "import json, sys; sys.path.insert(0, sys.argv[1]); "
                "import verify_timecut_duality as v; v.canonical_json_bytes({'x': json.loads('NaN')})",
                str(SCRIPT_DIR),
            ],
            capture_output=True,
            text=True,
            timeout=20,
            check=False,
        )
        self.assertNotEqual(nan_probe.returncode, 0)
        self.assertIn("ValueError", nan_probe.stderr)

    def test_strict_json_loads_rejects_duplicates_floats_and_nan(self) -> None:
        self.assertEqual(vtd.strict_json_loads('{"a": 1, "b": [0, -5]}'), {"a": 1, "b": [0, -5]})
        self.assertEqual(
            vtd.strict_json_loads('{"s": "[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[\\"\\\\"}'),
            {"s": '[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[["\\'},
        )
        self.assertEqual(
            vtd.strict_json_loads('{"x": ' + ("9" * 64) + "}"), {"x": int("9" * 64, 10)}
        )
        with self.assertRaisesRegex(ValueError, "raw_text must be str"):
            vtd.strict_json_loads(b"{}")
        with self.assertRaisesRegex(ValueError, "exceeds 64 chars"):
            vtd.strict_json_loads('{"x": ' + ("9" * 65) + "}")
        with self.assertRaisesRegex(ValueError, "exceeds 64 chars"):
            vtd.strict_json_loads('{"x": ' + ("9" * 4400) + "}")
        with self.assertRaisesRegex(ValueError, "negative zero integer forbidden"):
            vtd.strict_json_loads('{"x": -0}')
        with self.assertRaisesRegex(ValueError, "duplicate JSON key: a"):
            vtd.strict_json_loads('{"a": 1, "a": 2}')
        with self.assertRaisesRegex(ValueError, "duplicate JSON key: k"):
            vtd.strict_json_loads('{"nested": {"k": 1, "k": 2}}')
        with self.assertRaisesRegex(ValueError, "JSON float literal forbidden"):
            vtd.strict_json_loads('{"x": 1.25}')
        with self.assertRaisesRegex(ValueError, "JSON float literal forbidden"):
            vtd.strict_json_loads('{"x": 1e3}')
        with self.assertRaisesRegex(ValueError, "JSON non-standard constant forbidden"):
            vtd.strict_json_loads('{"x": NaN}')
        with self.assertRaisesRegex(ValueError, "JSON non-standard constant forbidden"):
            vtd.strict_json_loads('{"x": Infinity}')
        d32 = ("[" * 32) + "1" + ("]" * 32)
        self.assertIsInstance(vtd.strict_json_loads(d32), list)
        d33 = ("[" * 33) + "1" + ("]" * 33)
        with self.assertRaisesRegex(ValueError, "nesting depth exceeds 32"):
            vtd.strict_json_loads(d33)
        d5000 = ("[" * 5000) + "1" + ("]" * 5000)
        with self.assertRaisesRegex(ValueError, "nesting depth exceeds 32"):
            vtd.strict_json_loads(d5000)
        # Unmatched closing brace handled without negative depth
        with self.assertRaises(ValueError):
            vtd.strict_json_loads("}")

    def test_committed_files_clean_and_valid(self) -> None:
        checked = vtd.check_certificate_file(vtd.DEFAULT_CERT_PATH, vtd.DEFAULT_LEAN_DIR)
        self.assertTrue(checked["overall_passed"])

        slash = chr(47)
        at_sign = chr(64)
        forbidden = (
            slash + "ho" + "me" + slash,
            slash + "Us" + "ers" + slash,
            slash + "ro" + "ot" + slash,
            at_sign,
        )
        all_paths = [
            VERIFIER_PATH,
            TEST_PATH,
            vtd.DEFAULT_CERT_PATH,
            *(vtd.DEFAULT_LEAN_DIR.joinpath(name) for name in vtd.EXPECTED_LEAN_FILES),
        ]
        for path in all_paths:
            txt = path.read_text(encoding="utf-8")
            for tok in forbidden:
                self.assertNotIn(tok, txt, f"Forbidden token {tok!r} in {path.name}")


class TestTimeCutPrimitivesAndPredicates(unittest.TestCase):
    """Complete truth-table and exact arithmetic helper coverage."""

    def test_exact_arithmetic_and_boolean_predicates(self) -> None:
        vtd.require_ok(True, "ok")
        with self.assertRaisesRegex(ValueError, "boom"):
            vtd.require_ok(False, "boom")

        self.assertTrue(vtd.is_exact_int(0))
        self.assertTrue(vtd.is_exact_int(-5))
        self.assertFalse(vtd.is_exact_int(True))
        self.assertFalse(vtd.is_exact_int(False))
        self.assertFalse(vtd.is_exact_int("3"))

        f34 = vtd.q_frac(3, 4)
        self.assertEqual(vtd.require_fraction(f34, "x"), f34)
        for bad in (1, True, "3/4", None):
            with self.assertRaisesRegex(ValueError, "must be Fraction"):
                vtd.require_fraction(bad, "x")

        self.assertEqual(vtd.q_frac(6, -8), vtd.q_frac(-3, 4))
        self.assertEqual(vtd.q_frac(5), fractions.Fraction(5, 1))
        with self.assertRaisesRegex(ValueError, "numerator must be exact int"):
            vtd.q_frac(True, 2)
        with self.assertRaisesRegex(ValueError, "denominator must be exact int"):
            vtd.q_frac(1, False)
        with self.assertRaisesRegex(ValueError, "denominator must be nonzero"):
            vtd.q_frac(1, 0)

        self.assertEqual(vtd.q_div(vtd.q_frac(3, 5), vtd.q_frac(9, 10)), vtd.q_frac(2, 3))
        with self.assertRaisesRegex(ValueError, "lhs must be Fraction"):
            vtd.q_div(1, f34)  # type: ignore[arg-type]
        with self.assertRaisesRegex(ValueError, "rhs must be Fraction"):
            vtd.q_div(f34, 1)  # type: ignore[arg-type]
        with self.assertRaisesRegex(ValueError, "rational division by zero"):
            vtd.q_div(f34, vtd.q_frac(0, 1))

        self.assertEqual(vtd.int_pow_nonneg(10, 0), 1)
        self.assertEqual(vtd.int_pow_nonneg(3, 4), 81)
        self.assertEqual(vtd.int_pow_nonneg(1, 256), 1)
        self.assertEqual(vtd.int_pow_nonneg(2, 10), 1024)
        with self.assertRaisesRegex(ValueError, "base must be exact int"):
            vtd.int_pow_nonneg(True, 2)
        with self.assertRaisesRegex(ValueError, "exp must be exact int"):
            vtd.int_pow_nonneg(2, True)
        with self.assertRaisesRegex(ValueError, "exp must be >= 0"):
            vtd.int_pow_nonneg(2, -1)
        with self.assertRaisesRegex(ValueError, "exceeds bounded limit 256"):
            vtd.int_pow_nonneg(2, 257)

        self.assertTrue(vtd.is_hex64("0123456789abcdef" * 4))
        self.assertFalse(vtd.is_hex64(99))
        self.assertFalse(vtd.is_hex64("a" * 63))
        self.assertFalse(vtd.is_hex64("a" * 65))
        self.assertFalse(vtd.is_hex64("A" + "a" * 63))
        self.assertFalse(vtd.is_hex64("g" + "a" * 63))

        self.assertEqual(vtd.q_to_str(vtd.q_frac(-4, 6)), "-2/3")
        with self.assertRaisesRegex(ValueError, "must be Fraction"):
            vtd.q_to_str(2)  # type: ignore[arg-type]
        self.assertEqual(vtd.str_to_q("107/3", "v"), vtd.q_frac(107, 3))
        for bad_den in ("1/0", "1/-3"):
            with self.assertRaisesRegex(ValueError, "denominator must be positive"):
                vtd.str_to_q(bad_den, "v")
        for bad_s in (
            12,
            "5",
            "1/2/3",
            "/2",
            "1/",
            "a/2",
            "1/b",
            "2/4",
            " 5/3 ",
            "5_0/3",
            "+5/3",
            "05/3",
        ):
            with self.assertRaises(ValueError):
                vtd.str_to_q(bad_s, "v")

        self.assertTrue(vtd.are_two_intervals_strictly_crossing(0, 4, 2, 6))
        self.assertTrue(vtd.are_two_intervals_strictly_crossing(2, 6, 0, 4))
        self.assertFalse(vtd.are_two_intervals_strictly_crossing(0, 6, 2, 4))
        self.assertFalse(vtd.are_two_intervals_strictly_crossing(2, 4, 0, 6))
        self.assertFalse(vtd.are_two_intervals_strictly_crossing(0, 4, 4, 8))
        self.assertFalse(vtd.are_two_intervals_strictly_crossing(4, 8, 0, 4))
        self.assertFalse(vtd.are_two_intervals_strictly_crossing(0, 4, 0, 6))
        self.assertFalse(vtd.are_two_intervals_strictly_crossing(0, 6, 2, 6))

        self.assertTrue(vtd.all_four_pillars_certified(True, True, True, True))
        self.assertFalse(vtd.all_four_pillars_certified(False, True, True, True))
        self.assertFalse(vtd.all_four_pillars_certified(True, False, True, True))
        self.assertFalse(vtd.all_four_pillars_certified(True, True, False, True))
        self.assertFalse(vtd.all_four_pillars_certified(True, True, True, False))

        self.assertTrue(vtd.is_exact_int_list_eq([2, 3], [2, 3]))
        self.assertFalse(vtd.is_exact_int_list_eq((2, 3), [2, 3]))
        self.assertFalse(vtd.is_exact_int_list_eq([2], [2, 3]))
        self.assertFalse(vtd.is_exact_int_list_eq([2, 3, 4], [2, 3]))
        self.assertFalse(vtd.is_exact_int_list_eq([2, True], [2, 1]))
        self.assertFalse(vtd.is_exact_int_list_eq([2, 4], [2, 3]))


class TestTimeCutSimplexDualityAndDomains(unittest.TestCase):
    """Boundary and guard coverage for laminar DP, simplex, primal-dual validator, P2, & P4."""

    def test_laminar_dp_and_simplex_guards(self) -> None:
        self.assertEqual(vtd.laminar_tree_dp_table(1), [0, 0])
        self.assertEqual(len(vtd.laminar_tree_dp_table(64)), 65)
        with self.assertRaisesRegex(ValueError, "max_n must be int"):
            vtd.laminar_tree_dp_table(True)  # type: ignore[arg-type]
        with self.assertRaisesRegex(ValueError, ">= 1"):
            vtd.laminar_tree_dp_table(0)
        with self.assertRaisesRegex(ValueError, "exceeds bounded limit 64"):
            vtd.laminar_tree_dp_table(65)

        r2_min = vtd.solve_timecut_lp_exact_q(2, max_pivots=1, check_all_general_rects=True)
        self.assertEqual(r2_min["optimum"], vtd.q_frac(1, 1))
        r2_max = vtd.solve_timecut_lp_exact_q(2, max_pivots=1024)
        self.assertEqual(r2_max["optimum"], vtd.q_frac(1, 1))

        with self.assertRaisesRegex(ValueError, "n must be int"):
            vtd.solve_timecut_lp_exact_q(True)  # type: ignore[arg-type]
        with self.assertRaisesRegex(ValueError, "lp dimension n must be >= 2"):
            vtd.solve_timecut_lp_exact_q(1)
        with self.assertRaisesRegex(ValueError, "exceeds bounded solver limit 20"):
            vtd.solve_timecut_lp_exact_q(21)
        with self.assertRaisesRegex(ValueError, "max_pivots must be int"):
            vtd.solve_timecut_lp_exact_q(2, max_pivots=True)  # type: ignore[arg-type]
        with self.assertRaisesRegex(ValueError, "max_pivots must be >= 1"):
            vtd.solve_timecut_lp_exact_q(2, max_pivots=0)
        with self.assertRaisesRegex(ValueError, "exceeds bounded limit 1024"):
            vtd.solve_timecut_lp_exact_q(2, max_pivots=1025)
        with self.assertRaisesRegex(ValueError, "pivot budget exceeded"):
            vtd.solve_timecut_lp_exact_q(4, max_pivots=1)

        # Bland leaving-row selector: leave == 0 boundary, tie-breaking, and unbounded column refusal
        q0, q1, q2 = vtd.q_frac(0, 1), vtd.q_frac(1, 1), vtd.q_frac(2, 1)
        self.assertEqual(
            vtd._select_bland_leaving_row([[q1, q1], [q1, q2]], [5, 3], 2, 1, 0), 0
        )
        self.assertEqual(
            vtd._select_bland_leaving_row([[q1, q2], [q1, q1]], [3, 5], 2, 1, 0), 1
        )
        self.assertEqual(
            vtd._select_bland_leaving_row([[q1, q1], [q1, q1]], [5, 3], 2, 1, 0), 1
        )
        self.assertEqual(
            vtd._select_bland_leaving_row([[q1, q1], [q1, q1]], [3, 5], 2, 1, 0), 0
        )
        with self.assertRaisesRegex(ValueError, "unbounded simplex entering column"):
            vtd._select_bland_leaving_row([[q0, q1], [vtd.q_frac(-1, 1), q1]], [3, 4], 2, 1, 0)

    def test_primal_dual_validator_guards(self) -> None:
        f1 = vtd.q_frac(1, 1)
        xr_ok = {(0, 1, 2): f1}
        yp_ok = {(0, 1): f1}
        self.assertEqual(
            vtd.verify_primal_dual_timecut_certificate_q(2, xr_ok, yp_ok, True), f1
        )
        self.assertEqual(
            vtd.verify_primal_dual_timecut_certificate_q(2, xr_ok, yp_ok, False), f1
        )

        with self.assertRaisesRegex(ValueError, "n must be int"):
            vtd.verify_primal_dual_timecut_certificate_q(True, xr_ok, yp_ok)  # type: ignore[arg-type]
        with self.assertRaisesRegex(ValueError, "n must be >= 2"):
            vtd.verify_primal_dual_timecut_certificate_q(1, xr_ok, yp_ok)
        with self.assertRaisesRegex(ValueError, "x_rects must be dict"):
            vtd.verify_primal_dual_timecut_certificate_q(2, [], yp_ok)  # type: ignore[arg-type]
        with self.assertRaisesRegex(ValueError, "y_pairs must be dict"):
            vtd.verify_primal_dual_timecut_certificate_q(2, xr_ok, [])  # type: ignore[arg-type]

        for bad_xr, pat in (
            ({(0, 1, 2): vtd.q_frac(0, 1)}, "primal weight must be > 0"),
            ({(-1, 1, 2): f1}, "rect a < 0"),
            ({(1, 1, 2): f1}, "rect a >= b"),
            ({(0, 2, 2): f1}, "rect b >= c"),
            ({(0, 1, 3): f1}, "rect c > n"),
            ({(0, 1, 2): vtd.q_frac(3, 2)}, "congestion exceeds 1"),
        ):
            with self.assertRaisesRegex(ValueError, pat):
                vtd.verify_primal_dual_timecut_certificate_q(2, bad_xr, yp_ok)

        for bad_yp, pat in (
            ({(0, 1): vtd.q_frac(0, 1)}, "dual weight must be > 0"),
            ({(-1, 1): f1}, "pair i < 0"),
            ({(1, 1): f1}, "pair i >= j"),
            ({(0, 2): f1}, "pair j >= n"),
            ({(0, 1): vtd.q_frac(1, 2)}, "under-covers general"),
            ({(0, 1): vtd.q_frac(2, 1)}, "primal objective != dual objective"),
        ):
            with self.assertRaisesRegex(ValueError, pat):
                vtd.verify_primal_dual_timecut_certificate_q(2, xr_ok, bad_yp, True)

        with self.assertRaisesRegex(ValueError, "under-covers balanced"):
            vtd.verify_primal_dual_timecut_certificate_q(
                2, xr_ok, {(0, 1): vtd.q_frac(1, 2)}, False
            )

        s3 = vtd.solve_timecut_lp_exact_q(3, check_all_general_rects=True)
        self.assertEqual(s3["optimum"], vtd.q_frac(2, 1))

    def test_p2_and_p4_domain_guards(self) -> None:
        self.assertEqual(vtd._int_mod_pos(0, 3), 0)
        self.assertEqual(vtd._int_mod_pos(3, 3), 0)
        self.assertEqual(vtd._int_mod_pos(6, 3), 0)
        self.assertEqual(vtd._int_mod_pos(7, 3), 1)
        self.assertEqual(vtd._int_mod_pos(13, 3), 1)
        self.assertEqual(vtd._int_mod_pos(14, 3), 2)

        e4 = vtd.audit_eight_bank_dimacs_envelope(4)
        self.assertEqual(e4["n_rows"], 16)
        e64 = vtd.audit_eight_bank_dimacs_envelope(64)
        self.assertTrue(e64["tseitin_mod3_charge_mismatch"])

        with self.assertRaisesRegex(ValueError, "k must be int"):
            vtd.audit_eight_bank_dimacs_envelope(True)  # type: ignore[arg-type]
        with self.assertRaisesRegex(ValueError, "k must be >= 4"):
            vtd.audit_eight_bank_dimacs_envelope(0)
        with self.assertRaisesRegex(ValueError, "k must be <= 64"):
            vtd.audit_eight_bank_dimacs_envelope(68)
        with self.assertRaisesRegex(ValueError, "divisible by 4"):
            vtd.audit_eight_bank_dimacs_envelope(5)
        with self.assertRaisesRegex(ValueError, "divisible by 4"):
            vtd.audit_eight_bank_dimacs_envelope(6)

        self.assertEqual(vtd.rank_gf2([[1]]), 1)
        self.assertEqual(vtd.rank_gf2([[0]]), 0)
        self.assertEqual(vtd.rank_gf2([[0, 1], [1, 0]]), 2)
        self.assertEqual(vtd.rank_gf2([[1, 1], [0, 1]]), 2)
        self.assertEqual(vtd.rank_gf2([[1, 1], [1, 1]]), 1)
        self.assertEqual(vtd.rank_q_from_binary([[1]]), 1)
        self.assertEqual(vtd.rank_q_from_binary([[0]]), 0)
        self.assertEqual(vtd.rank_q_from_binary([[0, 1], [1, 0]]), 2)
        self.assertEqual(vtd.rank_q_from_binary([[1, 1], [0, 1]]), 2)
        self.assertEqual(vtd.rank_q_from_binary([[1, 1], [1, 1]]), 1)

        for bad_m, pat in (
            (([1],), "^mat must be list$"),
            ([], "non-empty"),
            (["bad"], "mat\\[0\\] must be list"),
            ([[]], ">= 1 col"),
            ([[1], "bad"], "mat\\[1\\] must be list"),
            ([[1, 0], [1]], "rectangular"),
            ([[True]], "entry must be int"),
            ([[2]], "entry must be 0 or 1"),
            ([[-1]], "entry must be 0 or 1"),
        ):
            with self.assertRaisesRegex(ValueError, pat):
                vtd.validate_binary_matrix(bad_m, "mat")


class TestTimeCutLeanPackageTamperAndCli(unittest.TestCase):
    """Char-safe Lean lexer, 5-file raw-bytes tamper refusal, live-lean mock, & CLI."""

    def test_char_safe_lean_stripper_and_char_literal_edge_cases(self) -> None:
        with self.assertRaisesRegex(ValueError, "Lean source text must be str"):
            vtd.strip_lean_comments_and_strings(123)  # type: ignore[arg-type]
        with self.assertRaisesRegex(ValueError, "unclosed Lean block comment"):
            vtd.strip_lean_comments_and_strings("/- nested /- unclosed -/")
        with self.assertRaisesRegex(ValueError, "unclosed Lean string literal"):
            vtd.strip_lean_comments_and_strings('def s := "unclosed')
        with self.assertRaisesRegex(ValueError, "unclosed Lean string escape"):
            vtd.strip_lean_comments_and_strings('def s := "trail\\')
        with self.assertRaisesRegex(ValueError, "Lean raw string literal forbidden"):
            vtd.strip_lean_comments_and_strings('def s := r#"raw"#')

        clean_s = vtd.strip_lean_comments_and_strings(
            '-- sorry bv_decide\n/- Classical.choice\n/- nested sorry -/ -/\ndef msg := "sorry \\" bv_decide"\n'
        )
        self.assertNotIn("sorry", clean_s)
        self.assertNotIn("bv_decide", clean_s)
        self.assertEqual(clean_s.count("\n"), 4)

        # CRITICAL: char literals, 3-char doc comments (/--/ " -/), f!'\"', «a»'\"', & "\\" MUST NOT hide sorry!
        for tricky_prefix in (
            "def q : Char := '\"'\n",
            "def q : Char := '\\\"'\n",
            "def q : Char := '\\''\n",
            "def q : Char := '\\x41'\n",
            "def q : Char := '\\u0041'\n",
            'def s : String := "\\\\"\n',
            '/--/ " -/\n',
            '/-!/ " -/\n',
            "def x := f!'\\\"'\n",
            "def x := «a»'\\\"'\n",
        ):
            stripped = vtd.strip_lean_comments_and_strings(
                tricky_prefix + "theorem bad : True := by sorry\n"
            )
            self.assertIn("sorry", stripped)

        # Identifier primes x'+'y, x_'+'y, x''+'y must remain intact (not treated as '+' char lit)
        for ident_expr in ("x'+'y", "x_'+'y", "x''+'y", "x'+y'"):
            self.assertEqual(vtd.strip_lean_comments_and_strings(ident_expr), ident_expr)

        # Non-char-literal single quotes at end, multi-char unescaped, short escape, or newline
        self.assertEqual(vtd._consume_lean_char_literal("abc", 0), 0)
        self.assertEqual(vtd._consume_lean_char_literal("'ab'", 0), 0)
        self.assertEqual(vtd._consume_lean_char_literal("'\\", 0), 0)
        self.assertEqual(vtd._consume_lean_char_literal("'\n'", 0), 0)
        self.assertEqual(vtd._consume_lean_char_literal("'\\x\n'", 0), 0)
        self.assertEqual(vtd._consume_lean_char_literal("'\\u000000'", 0), 0)

    def test_lean_package_static_r13b_and_one_byte_tamper_refusal(self) -> None:
        with self.assertRaisesRegex(ValueError, "lean_dir must be Path"):
            vtd.read_and_static_gate_lean_package("bad")  # type: ignore[arg-type]

        with tempfile.TemporaryDirectory() as tmp:
            missing_dir = pathlib.Path(tmp).joinpath("missing")
            with self.assertRaisesRegex(ValueError, "directory not found for lean_dir"):
                vtd.read_and_static_gate_lean_package(missing_dir)

            pkg_copy = pathlib.Path(tmp).joinpath("lean_pkg")
            shutil.copytree(vtd.DEFAULT_LEAN_DIR, pkg_copy)
            cert_copy = pathlib.Path(tmp).joinpath("cert.json")
            shutil.copy2(vtd.DEFAULT_CERT_PATH, cert_copy)

            # 1-byte tamper of EVERY single one of the 5 Lean package files must fail --check!
            for fname in vtd.EXPECTED_LEAN_FILES:
                tamper_dir = pathlib.Path(tmp).joinpath(f"tamper_{fname}")
                shutil.copytree(vtd.DEFAULT_LEAN_DIR, tamper_dir)
                target = tamper_dir.joinpath(fname)
                orig = target.read_bytes()
                if fname.endswith(".lean"):
                    # Even appending a harmless space inside a comment changes raw SHA-256!
                    target.write_bytes(orig + b"\n-- comment byte\n")
                elif fname == "lake-manifest.json":
                    target.write_bytes(orig.replace(b'"packages": []', b'"packages": [ ]'))
                elif fname == "lakefile.toml":
                    target.write_bytes(orig + b"\n")
                else:
                    target.write_bytes(orig + b" ")
                with self.assertRaises(ValueError):
                    vtd.check_certificate_file(cert_copy, tamper_dir)

            # Extra file (e.g. lakefile.lean, .lake, or Stray.lean) in lean_dir must fail closed
            lakefile_lean = pkg_copy.joinpath("lakefile.lean")
            lakefile_lean.write_text("-- forbidden\n", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "lakefile.lean forbidden alongside lakefile.toml"):
                vtd.read_and_static_gate_lean_package(pkg_copy)
            lakefile_lean.unlink()

            stray = pkg_copy.joinpath("Stray.lean")
            stray.write_text("-- stray\n", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "file set mismatch"):
                vtd.read_and_static_gate_lean_package(pkg_copy)
            stray.unlink()

            # Subdirectory replacing expected regular file
            pkg_copy.joinpath("lean-toolchain").unlink()
            pkg_copy.joinpath("lean-toolchain").mkdir()
            with self.assertRaisesRegex(ValueError, "expected regular file"):
                vtd.read_and_static_gate_lean_package(pkg_copy)
            pkg_copy.joinpath("lean-toolchain").rmdir()
            shutil.copy2(
                vtd.DEFAULT_LEAN_DIR.joinpath("lean-toolchain"),
                pkg_copy.joinpath("lean-toolchain"),
            )

            # Specific static checks on toolchain, manifest, lakefile, main, and AxiomAudit
            pkg_copy.joinpath("lean-toolchain").write_text(
                "leanprover/lean4:v4.19.0\n", encoding="utf-8"
            )
            with self.assertRaisesRegex(ValueError, "unexpected lean-toolchain"):
                vtd.read_and_static_gate_lean_package(pkg_copy)
            shutil.copy2(
                vtd.DEFAULT_LEAN_DIR.joinpath("lean-toolchain"),
                pkg_copy.joinpath("lean-toolchain"),
            )

            for bad_manifest, pat in (
                ("[]", "must be object"),
                ('{"name": "wrong", "packages": []}', "name mismatch"),
                ('{"name": "timecut_duality", "packages": [{"name": "dep"}]}', "empty packages"),
            ):
                pkg_copy.joinpath("lake-manifest.json").write_text(bad_manifest, encoding="utf-8")
                with self.assertRaisesRegex(ValueError, pat):
                    vtd.read_and_static_gate_lean_package(pkg_copy)
            shutil.copy2(
                vtd.DEFAULT_LEAN_DIR.joinpath("lake-manifest.json"),
                pkg_copy.joinpath("lake-manifest.json"),
            )

            orig_toml = vtd.DEFAULT_LEAN_DIR.joinpath("lakefile.toml").read_text(encoding="utf-8")
            # Symlink refusal on lean_dir and on individual package files
            sym_lean_dir = pathlib.Path(tmp).joinpath("sym_lean_dir")
            sym_lean_dir.symlink_to(pkg_copy)
            with self.assertRaisesRegex(ValueError, "symlink or non-directory forbidden for lean_dir"):
                vtd.read_and_static_gate_lean_package(sym_lean_dir)
            sym_lean_dir.unlink()

            real_tc = pathlib.Path(tmp).joinpath("real_tc")
            real_tc.write_text("leanprover/lean4:v4.36.0\n", encoding="utf-8")
            pkg_copy.joinpath("lean-toolchain").unlink()
            pkg_copy.joinpath("lean-toolchain").symlink_to(real_tc)
            with self.assertRaisesRegex(ValueError, "symlink forbidden for lean-toolchain"):
                vtd.read_and_static_gate_lean_package(pkg_copy)
            pkg_copy.joinpath("lean-toolchain").unlink()
            shutil.copy2(
                vtd.DEFAULT_LEAN_DIR.joinpath("lean-toolchain"),
                pkg_copy.joinpath("lean-toolchain"),
            )

            # Pure-stdlib TOML parser coverage (comments, quotes, spaced [[ require ]], bad sections/keys)
            with self.assertRaisesRegex(ValueError, "lakefile_txt must be str"):
                vtd.validate_lakefile_toml(123)  # type: ignore[arg-type]
            vtd.validate_lakefile_toml(
                orig_toml + '\n# [[ require ]] ignored in comment\n# "esc \\" # ok" \'sq # ok\'\n'
            )
            self.assertEqual(vtd._strip_toml_line_comment('a = "x \\" # y" # tail'), 'a = "x \\" # y" ')
            self.assertEqual(vtd._strip_toml_line_comment("a = 'x # y' # tail"), "a = 'x # y' ")

            for bad_toml, pat in (
                ('name = "other"\n', "missing package name"),
                ('[[lean_lib]]\nname = "timecut_duality"\n', "missing package name"),
                (orig_toml + "\n[[require]]\n", "zero external requires"),
                (orig_toml + "\n[[ require ]]\n", "zero external requires"),
                (orig_toml + '\n[[ "require" ]]\n', "zero external requires"),
                (orig_toml + "\n[ require ]\n", "zero external requires"),
                (orig_toml + "\nrequire = []\n", "zero external requires"),
                (orig_toml + "\n[lean_lib]\n", "disallowed lakefile.toml section"),
                (orig_toml + "\n[[lean_lib]\n", "disallowed lakefile.toml section"),
                (orig_toml + "\n[lean_lib]]\n", "disallowed lakefile.toml section"),
                (orig_toml + "\n[[other]]\n", "disallowed lakefile.toml section"),
                (orig_toml + "\n[unclosed\n", "malformed lakefile.toml header"),
                (orig_toml + "\nmalformed_line\n", "malformed lakefile.toml line"),
                (orig_toml + "\nextraKey = 1\n", "disallowed lakefile.toml key"),
            ):
                pkg_copy.joinpath("lakefile.toml").write_text(bad_toml, encoding="utf-8")
                with self.assertRaisesRegex(ValueError, pat):
                    vtd.read_and_static_gate_lean_package(pkg_copy)
            shutil.copy2(
                vtd.DEFAULT_LEAN_DIR.joinpath("lakefile.toml"),
                pkg_copy.joinpath("lakefile.toml"),
            )

            base_main = vtd.DEFAULT_LEAN_DIR.joinpath("CleanRoomTimeCutDuality.lean").read_text(
                encoding="utf-8"
            )
            for snippet, rule_code in (
                ("def q := '\"'\ntheorem t : True := by sorry\n", "LEAN4_SORRY"),
                ("theorem t : True := by admit\n", "LEAN4_ADMIT"),
                ("axiom badAx : False\n", "LEAN4_AXIOM_DECL"),
                ("unsafe def u : Nat := 0\n", "LEAN4_UNSAFE"),
                ("theorem t : 1 = 1 := by native_decide\n", "LEAN4_NATIVE_DECIDE"),
                ("theorem t : 1 = 1 := by bv_decide\n", "LEAN4_BV_DECIDE"),
                ("def x := Lean.ofReduceBool\n", "LEAN4_OF_REDUCE_BOOL"),
                ("open Classical\n", "LEAN4_CLASSICAL"),
                ("set_option maxRecDepth 9999\n", "LEAN4_SET_OPTION"),
                ("def «ident» : Nat := 0\n", "LEAN4_FRENCH_QUOTE"),
                ("#eval 1 + 1\n", "LEAN4_META_EVAL"),
                ("import Std\n", "LEAN4_EXTERNAL_IMPORT"),
                ("theorem extra_t : 1 = 1 := rfl\n", "theorem catalog mismatch"),
            ):
                pkg_copy.joinpath("CleanRoomTimeCutDuality.lean").write_text(
                    snippet + base_main, encoding="utf-8"
                )
                with self.assertRaisesRegex(ValueError, rule_code):
                    vtd.read_and_static_gate_lean_package(pkg_copy)
            shutil.copy2(
                vtd.DEFAULT_LEAN_DIR.joinpath("CleanRoomTimeCutDuality.lean"),
                pkg_copy.joinpath("CleanRoomTimeCutDuality.lean"),
            )

            base_audit = vtd.DEFAULT_LEAN_DIR.joinpath("AxiomAudit.lean").read_text(
                encoding="utf-8"
            )
            pkg_copy.joinpath("AxiomAudit.lean").write_text(
                base_audit + "\ntheorem bad : True := by sorry\n", encoding="utf-8"
            )
            with self.assertRaisesRegex(ValueError, "LEAN4_SORRY"):
                vtd.read_and_static_gate_lean_package(pkg_copy)
            pkg_copy.joinpath("AxiomAudit.lean").write_text(
                "import Std\n" + base_audit, encoding="utf-8"
            )
            with self.assertRaisesRegex(ValueError, "import only CleanRoomTimeCutDuality"):
                vtd.read_and_static_gate_lean_package(pkg_copy)
            pkg_copy.joinpath("AxiomAudit.lean").write_text(
                "\n".join(base_audit.splitlines()[:-1]) + "\n", encoding="utf-8"
            )
            with self.assertRaisesRegex(ValueError, "must match all 30 theorems"):
                vtd.read_and_static_gate_lean_package(pkg_copy)

    def test_verify_lean_package_live_and_mocked_failure_paths(self) -> None:
        with self.assertRaisesRegex(ValueError, "toolchain_bin_dir must be Path"):
            vtd.verify_lean_package_live(vtd.DEFAULT_LEAN_DIR, toolchain_bin_dir="bad")  # type: ignore[arg-type]

        with tempfile.TemporaryDirectory() as tmp:
            empty_bin = pathlib.Path(tmp).joinpath("empty_bin")
            empty_bin.mkdir()
            with self.assertRaisesRegex(ValueError, "lake binary not found"):
                vtd.verify_lean_package_live(vtd.DEFAULT_LEAN_DIR, toolchain_bin_dir=empty_bin)

            bin_dir = pathlib.Path(tmp).joinpath("leanprover--lean4---v4.36.0", "bin")
            bin_dir.mkdir(parents=True)
            for tname in ("lake", "lean", "leanchecker"):
                bin_dir.joinpath(tname).write_text("#!/bin/sh\n", encoding="utf-8")

            ok_lean_ver = subprocess.CompletedProcess(
                args=[], returncode=0, stdout="Lean (version 4.36.0, Release)\n", stderr=""
            )
            bad_lean_ver_str = subprocess.CompletedProcess(
                args=[], returncode=0, stdout="Lean (version 4.19.0, Release)\n", stderr=""
            )
            bad_lean_ver_rc = subprocess.CompletedProcess(
                args=[], returncode=1, stdout="Lean (version 4.36.0, Release)\n", stderr="err"
            )
            ok_lake_ver = subprocess.CompletedProcess(
                args=[], returncode=0, stdout="Lake version 5.0.0 (Lean version 4.36.0)\n", stderr=""
            )
            bad_lake_ver_str = subprocess.CompletedProcess(
                args=[], returncode=0, stdout="Lake version 4.0.0 (Lean version 4.19.0)\n", stderr=""
            )
            bad_lake_ver_rc = subprocess.CompletedProcess(
                args=[], returncode=1, stdout="Lake version 5.0.0 (Lean version 4.36.0)\n", stderr="err"
            )

            with unittest.mock.patch(
                "subprocess.run", side_effect=RuntimeError("must not exec missing lean")
            ):
                self.assertFalse(vtd._probe_lean436_version(empty_bin.joinpath("lean")))
            with unittest.mock.patch("subprocess.run", return_value=ok_lean_ver):
                self.assertTrue(vtd._probe_lean436_version(bin_dir.joinpath("lean")))
            with unittest.mock.patch("subprocess.run", return_value=bad_lean_ver_str):
                self.assertFalse(vtd._probe_lean436_version(bin_dir.joinpath("lean")))
            with unittest.mock.patch("subprocess.run", return_value=bad_lean_ver_rc):
                self.assertFalse(vtd._probe_lean436_version(bin_dir.joinpath("lean")))

            with unittest.mock.patch(
                "shutil.which", return_value=str(bin_dir.joinpath("lake"))
            ), unittest.mock.patch("subprocess.run", return_value=ok_lean_ver):
                self.assertEqual(vtd.find_lean436_bin_dir(), bin_dir)

            # Fallback through ~/.elan/toolchains/*4.36.0*/bin with missing leanchecker, wrong ver, & good ver
            fake_home = pathlib.Path(tmp).joinpath("fake_home")
            elan_bad1 = fake_home.joinpath(".elan", "toolchains", "a-4.36.0-nochk", "bin")
            elan_bad1.mkdir(parents=True)
            elan_bad1.joinpath("lean").write_text("#!/bin/sh\n", encoding="utf-8")
            elan_bad2 = fake_home.joinpath(".elan", "toolchains", "b-4.36.0-wrongver", "bin")
            elan_bad2.mkdir(parents=True)
            for tname in ("lake", "lean", "leanchecker"):
                elan_bad2.joinpath(tname).write_text("#!/bin/sh\n", encoding="utf-8")
            elan_good = fake_home.joinpath(".elan", "toolchains", "c-4.36.0-good", "bin")
            elan_good.mkdir(parents=True)
            for tname in ("lake", "lean", "leanchecker"):
                elan_good.joinpath(tname).write_text("#!/bin/sh\n", encoding="utf-8")

            def _ver_by_path(cmd, **kwargs):
                if "b-4.36.0-wrongver" in cmd[-2]:
                    return bad_lean_ver_str
                return ok_lean_ver

            with unittest.mock.patch("shutil.which", return_value=str(elan_bad1.joinpath("lake"))), \
                unittest.mock.patch("pathlib.Path.home", return_value=fake_home), \
                unittest.mock.patch("subprocess.run", side_effect=_ver_by_path):
                self.assertEqual(vtd.find_lean436_bin_dir(), elan_good)

            with unittest.mock.patch("shutil.which", return_value=str(elan_bad2.joinpath("lake"))), \
                unittest.mock.patch("pathlib.Path.home", return_value=fake_home), \
                unittest.mock.patch("subprocess.run", side_effect=_ver_by_path):
                self.assertEqual(vtd.find_lean436_bin_dir(), elan_good)

            ok_lines = "\n".join(
                (
                    f"info: AxiomAudit.lean:{idx + 8}:0: 'CleanRoomTimeCutDuality.{t}' "
                    + (
                        "does not depend on any axioms"
                        if (idx & 1) == 0
                        else "depends on axioms: [propext, Quot.sound]"
                    )
                )
                for idx, t in enumerate(vtd.EXPECTED_30_THEOREMS)
            )
            ok_build = subprocess.CompletedProcess(args=[], returncode=0, stdout="", stderr="")
            ok_chk = subprocess.CompletedProcess(args=[], returncode=0, stdout="", stderr="")
            ok_audit = subprocess.CompletedProcess(args=[], returncode=0, stdout=ok_lines, stderr="")

            copied_seen: list[list[str]] = []

            def spy_run(cmd, **kwargs):
                if cmd[-1] == "--version":
                    return ok_lean_ver if cmd[-2].endswith("lean") else ok_lake_ver
                cwd_p = pathlib.Path(kwargs["cwd"])
                copied_seen.append(sorted(p.name for p in cwd_p.iterdir()))
                if cmd[-1] == "build":
                    return ok_build
                if cmd[-1] == "AxiomAudit.lean":
                    return ok_audit
                return ok_chk

            with unittest.mock.patch("subprocess.run", side_effect=spy_run):
                live_res = vtd.verify_lean_package_live(vtd.DEFAULT_LEAN_DIR, toolchain_bin_dir=bin_dir)
            self.assertEqual(live_res["theorem_count"], 30)
            self.assertTrue(live_res["zero_classical_choice"])
            self.assertEqual(live_res["observed_axioms"], ["Quot.sound", "propext"])
            self.assertIn("4.36.0", live_res["lean_version"])
            self.assertIn("lake-manifest.json", copied_seen[0])
            self.assertEqual(tuple(copied_seen[0]), vtd.EXPECTED_LEAN_FILES)

            # Binary version failures, build failure, leanchecker failure, live lean audit failure,
            # disallowed axiom, unexpected line, and short theorem count
            for seq, pat in (
                ([bad_lean_ver_str], "lean --version did not report 4.36.0"),
                ([bad_lean_ver_rc], "lean --version did not report 4.36.0"),
                ([ok_lean_ver, bad_lake_ver_str], "lake --version did not report 4.36.0"),
                ([ok_lean_ver, bad_lake_ver_rc], "lake --version did not report 4.36.0"),
            ):
                with unittest.mock.patch("subprocess.run", side_effect=seq):
                    with self.assertRaisesRegex(ValueError, pat):
                        vtd.verify_lean_package_live(vtd.DEFAULT_LEAN_DIR, toolchain_bin_dir=bin_dir)

            fail_proc = subprocess.CompletedProcess(args=[], returncode=1, stdout="", stderr="err")
            with unittest.mock.patch(
                "subprocess.run", side_effect=[ok_lean_ver, ok_lake_ver, fail_proc]
            ):
                with self.assertRaisesRegex(ValueError, "cold lake build failed"):
                    vtd.verify_lean_package_live(vtd.DEFAULT_LEAN_DIR, toolchain_bin_dir=bin_dir)

            with unittest.mock.patch(
                "subprocess.run", side_effect=[ok_lean_ver, ok_lake_ver, ok_build, fail_proc]
            ):
                with self.assertRaisesRegex(ValueError, "leanchecker CleanRoomTimeCutDuality failed"):
                    vtd.verify_lean_package_live(vtd.DEFAULT_LEAN_DIR, toolchain_bin_dir=bin_dir)

            with unittest.mock.patch(
                "subprocess.run",
                side_effect=[ok_lean_ver, ok_lake_ver, ok_build, ok_chk, ok_chk, fail_proc],
            ):
                with self.assertRaisesRegex(ValueError, "live lean AxiomAudit.lean failed"):
                    vtd.verify_lean_package_live(vtd.DEFAULT_LEAN_DIR, toolchain_bin_dir=bin_dir)

            bad_ax_audit = subprocess.CompletedProcess(
                args=[],
                returncode=0,
                stdout=(
                    "info: 'CleanRoomTimeCutDuality.gridSum_zero' "
                    "depends on axioms: [propext, Classical.choice]\n"
                ),
                stderr="",
            )
            with unittest.mock.patch(
                "subprocess.run",
                side_effect=[ok_lean_ver, ok_lake_ver, ok_build, ok_chk, ok_chk, bad_ax_audit],
            ):
                with self.assertRaisesRegex(ValueError, "disallowed Lean axiom footprint"):
                    vtd.verify_lean_package_live(vtd.DEFAULT_LEAN_DIR, toolchain_bin_dir=bin_dir)

            weird_audit = subprocess.CompletedProcess(
                args=[],
                returncode=0,
                stdout="info: 'CleanRoomTimeCutDuality.gridSum_zero' weird status\n",
                stderr="",
            )
            with unittest.mock.patch(
                "subprocess.run",
                side_effect=[ok_lean_ver, ok_lake_ver, ok_build, ok_chk, ok_chk, weird_audit],
            ):
                with self.assertRaisesRegex(ValueError, "unexpected axiom report"):
                    vtd.verify_lean_package_live(vtd.DEFAULT_LEAN_DIR, toolchain_bin_dir=bin_dir)

            with unittest.mock.patch("subprocess.run", side_effect=subprocess.TimeoutExpired("lean", 30)):
                self.assertFalse(vtd._probe_lean436_version(bin_dir.joinpath("lean")))

            with unittest.mock.patch(
                "subprocess.run",
                side_effect=[
                    ok_lean_ver,
                    ok_lake_ver,
                    ok_build,
                    subprocess.TimeoutExpired("leanchecker", 300),
                ],
            ):
                with self.assertRaisesRegex(ValueError, "leanchecker CleanRoomTimeCutDuality timed out"):
                    vtd.verify_lean_package_live(vtd.DEFAULT_LEAN_DIR, toolchain_bin_dir=bin_dir)

            short_audit = subprocess.CompletedProcess(
                args=[],
                returncode=0,
                stdout="info: 'CleanRoomTimeCutDuality.gridSum_zero' does not depend on any axioms\n",
                stderr="",
            )
            with unittest.mock.patch(
                "subprocess.run",
                side_effect=[ok_lean_ver, ok_lake_ver, ok_build, ok_chk, ok_chk, short_audit],
            ):
                with self.assertRaisesRegex(ValueError, "covered 1 theorems, expected 30"):
                    vtd.verify_lean_package_live(vtd.DEFAULT_LEAN_DIR, toolchain_bin_dir=bin_dir)

    def test_verify_core_invariants_rehashed_forgery_and_cli(self) -> None:
        base = vtd.strict_json_loads(vtd.DEFAULT_CERT_PATH.read_text(encoding="utf-8"))
        vtd.verify_core_invariants(base)

        with self.assertRaisesRegex(ValueError, "core must be dict"):
            vtd.verify_core_invariants([])

        def set_field(mapping: dict, key: str, val: object) -> None:
            mapping[key] = val

        def assert_tamper(tamper_fn, pat: str) -> None:
            bad = copy.deepcopy(base)
            tamper_fn(bad)
            with self.assertRaisesRegex(ValueError, pat):
                vtd.verify_core_invariants(bad)

        assert_tamper(lambda c: set_field(c, "schema_version", "v0"), "schema_version")
        assert_tamper(lambda c: set_field(c, "arithmetic_domain", "bad"), "arithmetic_domain")
        assert_tamper(lambda c: set_field(c, "status", "FAILED"), "status must be VERIFIED")
        assert_tamper(lambda c: set_field(c, "pillars", "bad"), "pillars must be dict")

        # P1 guards
        assert_tamper(
            lambda c: set_field(c["pillars"], "p1_timecut_lp_and_threshold", "bad"), "p1 must be dict"
        )
        assert_tamper(
            lambda c: set_field(c["pillars"]["p1_timecut_lp_and_threshold"], "passed", False),
            "p1 passed",
        )
        assert_tamper(
            lambda c: set_field(
                c["pillars"]["p1_timecut_lp_and_threshold"],
                "general_rects_verified_all_2_to_20",
                False,
            ),
            "general_rects_verified_all_2_to_20",
        )
        assert_tamper(
            lambda c: set_field(
                c["pillars"]["p1_timecut_lp_and_threshold"],
                "zero_gap_for_all_2_le_n_le_17",
                False,
            ),
            "p1 zero gap",
        )
        assert_tamper(
            lambda c: set_field(
                c["pillars"]["p1_timecut_lp_and_threshold"],
                "minimal_crossing_advantage_n",
                17,
            ),
            "N_min == 18",
        )
        assert_tamper(
            lambda c: set_field(
                c["pillars"]["p1_timecut_lp_and_threshold"],
                "n18_laminar_tree_optimum",
                36,
            ),
            "T_18 == 35",
        )
        assert_tamper(
            lambda c: set_field(c["pillars"]["p1_timecut_lp_and_threshold"], "n18_lp_optimum", "35/1"),
            "107/3",
        )
        assert_tamper(
            lambda c: set_field(c["pillars"]["p1_timecut_lp_and_threshold"], "n18_crossing_gap", "1/3"),
            "2/3",
        )
        assert_tamper(
            lambda c: set_field(c["pillars"]["p1_timecut_lp_and_threshold"], "n19_lp_optimum", "37/1"),
            "P_19 == 38",
        )
        assert_tamper(
            lambda c: set_field(c["pillars"]["p1_timecut_lp_and_threshold"], "n19_crossing_gap", "0/1"),
            "gap19 == 1",
        )

        # P2 guards
        assert_tamper(
            lambda c: set_field(c["pillars"], "p2_banked_cnf_envelope_and_port_gadget", "bad"),
            "p2 must be dict",
        )
        for fn, pat in (
            ("passed", "p2 passed"),
            ("linear_bit_length_envelope_verified", "p2 linear"),
            ("naive_2bank_superlinear_inflation_refuted", "p2 2bank"),
            ("every_field_tseitin_mod2_mod3_obstruction_verified", "p2 tseitin"),
        ):
            assert_tamper(
                lambda c, f=fn: set_field(
                    c["pillars"]["p2_banked_cnf_envelope_and_port_gadget"], f, False
                ),
                pat,
            )

        # P3 guards
        assert_tamper(
            lambda c: set_field(c["pillars"], "p3_lean4_package", "bad"),
            "p3 must be dict",
        )
        assert_tamper(
            lambda c: set_field(c["pillars"]["p3_lean4_package"], "passed", False),
            "p3 passed",
        )
        assert_tamper(
            lambda c: set_field(c["pillars"]["p3_lean4_package"], "file_sha256s", "bad"),
            "file_sha256s must be dict",
        )
        assert_tamper(
            lambda c: set_field(
                c["pillars"]["p3_lean4_package"]["file_sha256s"], "AxiomAudit.lean", "bad"
            ),
            "entries must be 64-hex",
        )
        assert_tamper(
            lambda c: set_field(
                c["pillars"]["p3_lean4_package"]["file_sha256s"], "AxiomAudit.lean", "0" * 64
            ),
            "SHA-256 mismatch",
        )
        assert_tamper(
            lambda c: set_field(c["pillars"]["p3_lean4_package"], "theorem_count", 29),
            "theorem_count != 30",
        )
        assert_tamper(
            lambda c: set_field(
                c["pillars"]["p3_lean4_package"], "manifest_zero_external_packages", False
            ),
            "manifest packages flag",
        )

        # P4 guards
        assert_tamper(
            lambda c: set_field(
                c["pillars"], "p4_crossing_c1p_and_char2_rank_obstructions", "bad"
            ),
            "p4 must be dict",
        )
        assert_tamper(
            lambda c: set_field(
                c["pillars"]["p4_crossing_c1p_and_char2_rank_obstructions"], "passed", False
            ),
            "p4 passed",
        )
        assert_tamper(
            lambda c: set_field(
                c["pillars"]["p4_crossing_c1p_and_char2_rank_obstructions"],
                "c1p_1d_contiguous_on_all_n18_active_intervals",
                False,
            ),
            "p4 c1p flag",
        )
        assert_tamper(
            lambda c: set_field(
                c["pillars"]["p4_crossing_c1p_and_char2_rank_obstructions"],
                "n18_strict_laminar_crossing_interval_pairs",
                True,
            ),
            "crossing count must be int",
        )
        assert_tamper(
            lambda c: set_field(
                c["pillars"]["p4_crossing_c1p_and_char2_rank_obstructions"],
                "n18_strict_laminar_crossing_interval_pairs",
                70,
            ),
            "must equal 71",
        )
        assert_tamper(
            lambda c: set_field(
                c["pillars"]["p4_crossing_c1p_and_char2_rank_obstructions"],
                "char2_vs_q_witness_j3_minus_i3_ranks",
                [3, 3],
            ),
            "ranks != \\[2, 3\\]",
        )
        assert_tamper(lambda c: set_field(c, "overall_passed", False), "overall_passed")

        # Envelope hash & re-hashed forgery checks
        for key, val, pat in (
            ("payload_sha256", "bad", "payload_sha256 must be 64-hex"),
            ("certificate_sha256", "bad", "certificate_sha256 must be 64-hex"),
            ("payload_sha256", "0" * 64, "payload_sha256 digest mismatch"),
            ("certificate_sha256", "0" * 64, "certificate_sha256 digest mismatch"),
        ):
            bh = copy.deepcopy(base)
            bh[key] = val
            with self.assertRaisesRegex(ValueError, pat):
                vtd.validate_certificate(bh)

        forged = copy.deepcopy(base)
        forged["pillars"]["p1_timecut_lp_and_threshold"]["n20_lp_optimum"] = "999/1"
        resign_cert(forged)
        with self.assertRaisesRegex(ValueError, "diverges from freshly recomputed"):
            vtd.validate_certificate(forged)

        bool_forged = copy.deepcopy(base)
        bool_forged["pillars"]["p4_crossing_c1p_and_char2_rank_obstructions"][
            "grid_18cell_3x6_vs_2x9_gcd_cycles"
        ] = [3, True]
        resign_cert(bool_forged)
        with self.assertRaisesRegex(ValueError, "diverges from freshly recomputed"):
            vtd.validate_certificate(bool_forged)

        # CLI modes, dir_fd O_NOFOLLOW ancestor/leaf/FIFO/size-cap guards, & structured RC=2 errors
        rel_fd = vtd._open_dir_nofollow(pathlib.Path("."), "cwd")
        os.close(rel_fd)

        with tempfile.TemporaryDirectory() as tmp:
            cpath = pathlib.Path(tmp).joinpath("cert.json")
            with self.assertRaisesRegex(ValueError, "certificate must be Path"):
                vtd.check_certificate_file("bad")  # type: ignore[arg-type]
            with self.assertRaisesRegex(ValueError, "invalid file path for certificate"):
                vtd.check_certificate_file(pathlib.Path("/"))
            with self.assertRaisesRegex(ValueError, "file not found for certificate"):
                vtd.check_certificate_file(cpath)

            # Bounded read size-cap boundaries (st_size check AND streaming loop check) + FIFO refusal
            cap_file = pathlib.Path(tmp).joinpath("cap.bin")
            cap_file.write_bytes(b"a" * 16)
            self.assertEqual(vtd._read_file_nofollow(cap_file, "cap", max_bytes=16), b"a" * 16)
            cap_file.write_bytes(b"a" * 17)
            with unittest.mock.patch(
                "os.read", side_effect=RuntimeError("must reject st_size before reading")
            ):
                with self.assertRaisesRegex(ValueError, "file exceeds size limit for cap"):
                    vtd._read_file_nofollow(cap_file, "cap", max_bytes=16)
            fake_st = unittest.mock.Mock(st_mode=stat.S_IFREG | 0o644, st_size=0)
            with unittest.mock.patch("os.fstat", return_value=fake_st):
                with self.assertRaisesRegex(ValueError, "file exceeds size limit for cap"):
                    vtd._read_file_nofollow(cap_file, "cap", max_bytes=16)

            fifo_path = pathlib.Path(tmp).joinpath("cert.fifo")
            os.mkfifo(fifo_path)
            with self.assertRaisesRegex(ValueError, "expected regular file for certificate"):
                vtd.check_certificate_file(fifo_path)

            # _write_file_nofollow validation guards
            with self.assertRaisesRegex(ValueError, "certificate must be Path"):
                vtd._write_file_nofollow("bad", b"x", "certificate")  # type: ignore[arg-type]
            with self.assertRaisesRegex(ValueError, "invalid file path for certificate"):
                vtd._write_file_nofollow(pathlib.Path("/"), b"x", "certificate")
            fake_fifo_st = unittest.mock.Mock(st_mode=stat.S_IFIFO | 0o644, st_size=0)
            with unittest.mock.patch("os.fstat", return_value=fake_fifo_st):
                with self.assertRaisesRegex(ValueError, "expected regular file for wtest"):
                    vtd._write_file_nofollow(pathlib.Path(tmp).joinpath("wtest.bin"), b"x", "wtest")
            with unittest.mock.patch("os.write", return_value=0):
                with self.assertRaisesRegex(ValueError, "short write for wtest"):
                    vtd._write_file_nofollow(pathlib.Path(tmp).joinpath("wtest2.bin"), b"x", "wtest")

            buf_w = io.StringIO()
            with unittest.mock.patch(
                "verify_timecut_duality.build_certificate",
                side_effect=lambda lean_dir=vtd.DEFAULT_LEAN_DIR: copy.deepcopy(base),
            ), unittest.mock.patch("sys.stdout", buf_w):
                self.assertEqual(vtd.main(["--write", "--cert-path", str(cpath)]), 0)
            self.assertIn("WROTE", buf_w.getvalue())

            for cli_args in (
                ["--cert-path", str(cpath)],
                ["--check", "--cert-path", str(cpath)],
            ):
                buf_c = io.StringIO()
                with unittest.mock.patch(
                    "verify_timecut_duality.build_certificate",
                    side_effect=lambda lean_dir=vtd.DEFAULT_LEAN_DIR: copy.deepcopy(base),
                ), unittest.mock.patch("sys.stdout", buf_c):
                    self.assertEqual(vtd.main(cli_args), 0)
                self.assertIn("PASS", buf_c.getvalue())

            mock_live_ret = {
                "file_sha256s": base["pillars"]["p3_lean4_package"]["file_sha256s"],
                "theorem_count": 30,
                "leanchecker_modules": ["CleanRoomTimeCutDuality", "AxiomAudit"],
                "zero_classical_choice": True,
            }
            buf_l = io.StringIO()
            with unittest.mock.patch(
                "verify_timecut_duality.build_certificate",
                side_effect=lambda lean_dir=vtd.DEFAULT_LEAN_DIR: copy.deepcopy(base),
            ), unittest.mock.patch(
                "verify_timecut_duality.verify_lean_package_live", return_value=mock_live_ret
            ), unittest.mock.patch("sys.stdout", buf_l):
                self.assertEqual(vtd.main(["--live-lean", "--cert-path", str(cpath)]), 0)
            self.assertIn("PASS_LEAN436", buf_l.getvalue())
            self.assertIn("theorems=30", buf_l.getvalue())

            buf_j = io.StringIO()
            with unittest.mock.patch(
                "verify_timecut_duality.build_certificate",
                side_effect=lambda lean_dir=vtd.DEFAULT_LEAN_DIR: copy.deepcopy(base),
            ), unittest.mock.patch("sys.stdout", buf_j):
                self.assertEqual(vtd.main(["--json"]), 0)
            self.assertEqual(buf_j.getvalue(), cpath.read_text(encoding="utf-8"))

            cpath.write_text(buf_j.getvalue() + "\n", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "bytes are not canonical"):
                vtd.check_certificate_file(cpath)

            cpath.write_text('{"schema_version": "a", "schema_version": "b"}\n', encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "duplicate JSON key"):
                vtd.check_certificate_file(cpath)

            # Structured RC=2 CLI error handling (zero tracebacks) on leaf symlink, grandparent symlink,
            # FIFO, 4400-digit int, [[require]] lakefile.toml, TimeoutExpired, MemoryError, & EPIPE
            sym_cert = pathlib.Path(tmp).joinpath("sym_cert.json")
            sym_cert.symlink_to(vtd.DEFAULT_CERT_PATH)
            with self.assertRaisesRegex(ValueError, "symlink forbidden for certificate"):
                vtd.check_certificate_file(sym_cert)

            real_sub = pathlib.Path(tmp).joinpath("real_parent", "nested")
            real_sub.mkdir(parents=True)
            shutil.copy2(vtd.DEFAULT_CERT_PATH, real_sub.joinpath("c.json"))
            sym_parent = pathlib.Path(tmp).joinpath("sym_parent")
            sym_parent.symlink_to(real_sub.parent)
            gp_sym_cert = sym_parent.joinpath("nested", "c.json")
            with self.assertRaisesRegex(
                ValueError, "symlink or non-directory forbidden for certificate: sym_parent"
            ):
                vtd.check_certificate_file(gp_sym_cert)

            big_int_cert = pathlib.Path(tmp).joinpath("bigint_cert.json")
            big_int_cert.write_text('{"x": ' + ("9" * 4400) + "}\n", encoding="utf-8")

            bad_lean_dir = pathlib.Path(tmp).joinpath("bad_lean_req")
            shutil.copytree(vtd.DEFAULT_LEAN_DIR, bad_lean_dir)
            bad_lean_dir.joinpath("lakefile.toml").write_text(
                vtd.DEFAULT_LEAN_DIR.joinpath("lakefile.toml").read_text(encoding="utf-8")
                + "\n[[require]]\n",
                encoding="utf-8",
            )
            valid_cert = pathlib.Path(tmp).joinpath("valid_cert.json")
            shutil.copy2(vtd.DEFAULT_CERT_PATH, valid_cert)

            dir_target = pathlib.Path(tmp).joinpath("cert_is_dir")
            dir_target.mkdir()

            # In-process & subprocess RC=2 verification (zero tracebacks)
            for cli_fail_args, err_substr, run_subproc in (
                (["--check", "--cert-path", str(sym_cert)], "symlink forbidden for certificate", True),
                (
                    ["--check", "--cert-path", str(gp_sym_cert)],
                    "symlink or non-directory forbidden for certificate",
                    True,
                ),
                (
                    ["--check", "--cert-path", str(fifo_path)],
                    "expected regular file for certificate",
                    True,
                ),
                (["--write", "--cert-path", str(sym_cert)], "symlink forbidden for certificate", False),
                (
                    ["--write", "--cert-path", str(gp_sym_cert)],
                    "symlink or non-directory forbidden for certificate",
                    True,
                ),
                (["--write", "--cert-path", "/"], "invalid file path for certificate", True),
                (["--check", "--cert-path", str(big_int_cert)], "exceeds 64 chars", True),
                (
                    ["--check", "--cert-path", str(valid_cert), "--lean-dir", str(bad_lean_dir)],
                    "zero external requires",
                    True,
                ),
            ):
                err_buf = io.StringIO()
                with unittest.mock.patch(
                    "verify_timecut_duality.build_certificate",
                    side_effect=lambda lean_dir=vtd.DEFAULT_LEAN_DIR: copy.deepcopy(base),
                ), unittest.mock.patch("sys.stderr", err_buf):
                    rc = vtd.main(cli_fail_args)
                self.assertEqual(rc, 2)
                parsed_err = vtd.strict_json_loads(err_buf.getvalue().strip())
                self.assertEqual(parsed_err["status"], "FAIL")
                self.assertIn(err_substr, parsed_err["error"])

                if run_subproc:
                    proc = subprocess.run(
                        ["/usr/bin/python3", "-I", "-B", str(VERIFIER_PATH), *cli_fail_args],
                        capture_output=True,
                        text=True,
                        timeout=30,
                        check=False,
                    )
                    self.assertEqual(proc.returncode, 2)
                    self.assertNotIn("Traceback", proc.stderr)
                    self.assertEqual(vtd.strict_json_loads(proc.stderr.strip())["status"], "FAIL")

            for exc_obj in (
                MemoryError("oom"),
                subprocess.TimeoutExpired("leanchecker", 300),
            ):
                err_m = io.StringIO()
                with unittest.mock.patch(
                    "verify_timecut_duality.check_certificate_file", side_effect=exc_obj
                ), unittest.mock.patch("sys.stderr", err_m):
                    self.assertEqual(vtd.main(["--check", "--cert-path", str(valid_cert)]), 2)
                self.assertEqual(vtd.strict_json_loads(err_m.getvalue().strip())["status"], "FAIL")

            err_os = io.StringIO()
            with unittest.mock.patch(
                "verify_timecut_duality.build_certificate",
                side_effect=lambda lean_dir=vtd.DEFAULT_LEAN_DIR: copy.deepcopy(base),
            ), unittest.mock.patch("sys.stderr", err_os):
                self.assertEqual(vtd.main(["--write", "--cert-path", str(dir_target)]), 2)
            self.assertEqual(
                vtd.strict_json_loads(err_os.getvalue().strip()),
                {"error": "filesystem, memory, recursion, or subprocess error", "status": "FAIL"},
            )

            # EPIPE / BrokenPipeError handling in _write_stream
            broken_stream = unittest.mock.Mock()
            broken_stream.write.side_effect = BrokenPipeError()
            broken_stream.close.side_effect = OSError()
            vtd._write_stream(broken_stream, "hi\n")


if __name__ == "__main__":  # pragma: no cover
    unittest.main()
