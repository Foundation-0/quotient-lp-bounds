"""Adversarial R5 and full mutation-killing test suite for verify_exact_farkas_delsarte.py.

Pure Python 3 stdlib, zero bare asserts, runs cleanly under -I -B, -I -O -B, and -I -B -W error.
"""
from __future__ import annotations

from fractions import Fraction
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

STUDY_DIR = Path(__file__).resolve().parent
if str(STUDY_DIR) not in sys.path:
    sys.path.insert(0, str(STUDY_DIR))

import verify_exact_farkas_delsarte as mod


EPS_1E9 = Fraction(1, 10 ** 9)


class TestPrimitivesAstAndEnergyGuard(unittest.TestCase):
    def test_exact_primitives_and_rejections(self) -> None:
        self.assertEqual(mod.q_int(5), Fraction(5, 1))
        with self.assertRaisesRegex(mod.CertVerifyError, "EXPECTED_STRICT_INT"):
            mod.q_int(True)  # type: ignore[arg-type]
        with self.assertRaisesRegex(mod.CertVerifyError, "EXPECTED_STRICT_INT"):
            mod.q_int(1.0)  # type: ignore[arg-type]

        self.assertEqual(mod.q_make(6, 4), Fraction(3, 2))
        with self.assertRaisesRegex(mod.CertVerifyError, "EXPECTED_INT_PAIR"):
            mod.q_make(True, 2)  # type: ignore[arg-type]
        with self.assertRaisesRegex(mod.CertVerifyError, "EXPECTED_INT_PAIR"):
            mod.q_make(2, True)  # type: ignore[arg-type]
        with self.assertRaisesRegex(mod.CertVerifyError, "ZERO_DENOMINATOR"):
            mod.q_make(3, 0)

        self.assertEqual(mod.q_div(Fraction(3, 4), Fraction(2, 5)), Fraction(15, 8))
        with self.assertRaisesRegex(mod.CertVerifyError, "EXPECTED_FRACTION"):
            mod.q_div(1, Fraction(1, 2))  # type: ignore[arg-type]
        with self.assertRaisesRegex(mod.CertVerifyError, "EXPECTED_FRACTION"):
            mod.q_div(Fraction(1, 2), 1)  # type: ignore[arg-type]
        with self.assertRaisesRegex(mod.CertVerifyError, "ZERO_DIVISION"):
            mod.q_div(Fraction(1, 2), Fraction(0, 1))

        self.assertEqual(mod.exact_div_z(12, 3), 4)
        self.assertEqual(mod.exact_div_z(-12, 3), -4)
        with self.assertRaisesRegex(mod.CertVerifyError, "EXACT_DIV_BAD_ARGS"):
            mod.exact_div_z(True, 2)  # type: ignore[arg-type]
        with self.assertRaisesRegex(mod.CertVerifyError, "EXACT_DIV_BAD_ARGS"):
            mod.exact_div_z(2, True)  # type: ignore[arg-type]
        with self.assertRaisesRegex(mod.CertVerifyError, "EXACT_DIV_ZERO"):
            mod.exact_div_z(6, 0)
        with self.assertRaisesRegex(mod.CertVerifyError, "BAREISS_INEXACT_DIVISION"):
            mod.exact_div_z(7, 2)

        self.assertEqual(mod._floor_div_nonneg_z(0, 5), 0)
        self.assertEqual(mod._floor_div_nonneg_z(5, 5), 1)
        self.assertEqual(mod._floor_div_nonneg_z(256, 9), 28)
        self.assertEqual(mod._mod_nonneg_z(256, 9), 4)
        for bad_n, bad_d in ((-1, 2), (2, 0), (2, -1), (True, 2), (2, True)):
            with self.assertRaisesRegex(mod.CertVerifyError, "BAD_FLOOR_DIV_ARGS"):
                mod._floor_div_nonneg_z(bad_n, bad_d)  # type: ignore[arg-type]

        self.assertEqual(mod.fmt_q(Fraction(6, 4)), "3/2")
        with self.assertRaisesRegex(mod.CertVerifyError, "FMT_EXPECTED_FRACTION"):
            mod.fmt_q(1)  # type: ignore[arg-type]

        self.assertEqual(mod.parse_q_str("3/4"), Fraction(3, 4))
        self.assertEqual(mod.parse_q_str("3/1"), Fraction(3, 1))
        self.assertEqual(mod.parse_q_str("0/1"), Fraction(0, 1))
        self.assertEqual(mod.parse_q_str("-7"), Fraction(-7, 1))
        self.assertEqual(mod.parse_q_str("0"), Fraction(0, 1))
        self.assertEqual(mod.parse_q_str("9" * 1024 + "/1"), Fraction(int("9" * 1024), 1))
        self.assertEqual(mod.parse_q_str("-" + "9" * 1024 + "/1"), Fraction(-int("9" * 1024), 1))
        self.assertEqual(mod.parse_q_str("1/" + "9" * 1024), Fraction(1, int("9" * 1024)))
        for big_q in ("9" * 1025 + "/1", "-" + "9" * 1025 + "/1", "1/" + "9" * 1025, "9" * 4400 + "/1", "1/" + "9" * 4400):
            with self.assertRaisesRegex(mod.CertVerifyError, "BAD_Q_DIGIT_LIMIT"):
                mod.parse_q_str(big_q)
        for bad in (
            "", 123, "1/2/3", "abc", "1/xyz", "1/0", "3/4\n",
            " 6/2 ", " 3/4", "3/4 ", "5_0/2", "1/-2", "+3/2", "-0", "03/4", "\u0663/\u0664",
        ):
            with self.assertRaisesRegex(mod.CertVerifyError, "BAD_Q_STR"):
                mod.parse_q_str(bad)  # type: ignore[arg-type]
        for noncanon in ("6/2", "4/6", "0/2"):
            with self.assertRaisesRegex(mod.CertVerifyError, "BAD_Q_NONCANONICAL"):
                mod.parse_q_str(noncanon)

        self.assertEqual(mod.exact_binom(6, 2), 15)
        self.assertEqual(mod.exact_binom(6, 4), 15)
        self.assertEqual(mod.exact_binom(6, 0), 1)
        self.assertEqual(mod.exact_binom(6, 6), 1)
        self.assertEqual(mod.exact_binom(6, -1), 0)
        self.assertEqual(mod.exact_binom(6, 7), 0)
        with self.assertRaisesRegex(mod.CertVerifyError, "BAD_BINOM_ARGS"):
            mod.exact_binom(-1, 0)
        with self.assertRaisesRegex(mod.CertVerifyError, "BAD_BINOM_ARGS"):
            mod.exact_binom(True, 0)  # type: ignore[arg-type]
        with self.assertRaisesRegex(mod.CertVerifyError, "BAD_BINOM_ARGS"):
            mod.exact_binom(5, True)  # type: ignore[arg-type]

        self.assertEqual(mod.lcm_int(6, 10), 30)
        self.assertEqual(mod.lcm_int(-6, 10), 30)
        with self.assertRaisesRegex(mod.CertVerifyError, "LCM_ZERO"):
            mod.lcm_int(0, 5)
        with self.assertRaisesRegex(mod.CertVerifyError, "LCM_ZERO"):
            mod.lcm_int(5, 0)

    def test_hardened_ast_purity_guard_and_negative_controls(self) -> None:
        clean_src = (
            "from errno import EISDIR, ENXIO\n"
            "from fractions import Fraction\n"
            "from math import gcd, isqrt\n"
            "from time import perf_counter_ns\n"
            "import json\n"
            "import os\n"
            "import sys\n"
            "import time\n"
            "def f(a, b, obj, fn, other):\n"
            "    x = 2\n"
            "    x += 1\n"
            "    x **= 2\n"
            "    t = time.perf_counter_ns() + perf_counter_ns()\n"
            "    _ = sys.stderr\n"
            "    _ = os.O_RDONLY\n"
            "    _ = json.dumps({})\n"
            "    _ = json.loads('{}', parse_float=fn, parse_constant=fn)\n"
            "    _ = other.loads('{}')\n"
            "    _ = fn().loads('{}')\n"
            "    _ = type(a) is int\n"
            "    _ = other(a) is int\n"
            "    _ = any(c.__name__ in ('float', 'complex') for c in type(a).__mro__)\n"
            "    _ = f'{a}'\n"
            "    return gcd(a, b) + isqrt(16) + pow(3, 4) + (2 ** 0) + obj.log(2) + Fraction(3, 4) + x + t\n"
        )
        res = mod.verify_ast_purity(clean_src)
        self.assertGreater(res["visited_nodes"], 20)
        self.assertEqual(res["ast_div"], 0)
        self.assertEqual(res["negative_pow"], 0)

        self_src = Path(mod.__file__).read_text(encoding="utf-8")
        self_audit = mod.verify_ast_purity(self_src)
        self.assertGreater(self_audit["visited_nodes"], 500)
        self.assertEqual(self_audit["ast_div"], 0)
        self.assertEqual(self_audit["float_or_complex_literals"], 0)
        self.assertEqual(self_audit["negative_pow"], 0)
        self.assertEqual(self_audit["fraction_str_or_from_float"], 0)

        with self.assertRaisesRegex(mod.CertVerifyError, "AST_SOURCE_NOT_STR"):
            mod.verify_ast_purity(123)  # type: ignore[arg-type]

        bad_cases = [
            ("", "AST_EMPTY_SOURCE"),
            ("def (\n", "AST_SYNTAX_ERROR"),
            ("x = 1\x00\n", "AST_SYNTAX_ERROR"),
            ("x = 1 / 2\n", "AST_FORBIDDEN_DIV"),
            ("x /= 2\n", "AST_FORBIDDEN_DIV"),
            ("p = Path('a') / 'b'\n", "AST_FORBIDDEN_DIV"),
            ("x = 1 // 2\n", "AST_FORBIDDEN_FLOORDIV"),
            ("x //= 2\n", "AST_FORBIDDEN_FLOORDIV"),
            ("x = '%f' % 1\n", "AST_FORBIDDEN_MOD"),
            ("x = fmt % 1\n", "AST_FORBIDDEN_MOD"),
            ("x %= 2\n", "AST_FORBIDDEN_MOD"),
            ("x = f'{1:.3f}'\n", "AST_FORBIDDEN_FORMAT_SPEC"),
            ("assert True\n", "AST_FORBIDDEN_BARE_ASSERT"),
            ("x = 1.5\n", "AST_FORBIDDEN_FLOAT_LITERAL"),
            ("x = 1j\n", "AST_FORBIDDEN_FLOAT_LITERAL"),
            ("x = 2 ** -1\n", "AST_FORBIDDEN_NEG_POW"),
            ("x = 2 ** (0 - 1)\n", "AST_FORBIDDEN_NEG_POW"),
            ("x = 2 ** k\n", "AST_FORBIDDEN_NEG_POW"),
            ("x **= -1\n", "AST_FORBIDDEN_NEG_POW"),
            ("x **= k\n", "AST_FORBIDDEN_NEG_POW"),
            ("x = pow(2, -1)\n", "AST_FORBIDDEN_NEG_POW"),
            ("x = pow(2)\n", "AST_FORBIDDEN_NEG_POW"),
            ("x = pow(2, 3, 5)\n", "AST_FORBIDDEN_NEG_POW"),
            ("x = pow(2, 3, mod=5)\n", "AST_FORBIDDEN_NEG_POW"),
            ("import math\n", "AST_FORBIDDEN_IMPORT"),
            ("import math as m\n", "AST_FORBIDDEN_IMPORT"),
            ("import fractions\n", "AST_FORBIDDEN_IMPORT"),
            ("import random\n", "AST_FORBIDDEN_IMPORT"),
            ("import datetime\n", "AST_FORBIDDEN_IMPORT"),
            ("import sys as s\n", "AST_FORBIDDEN_IMPORT_ALIAS"),
            ("import time as t\n", "AST_FORBIDDEN_IMPORT_ALIAS"),
            ("import json as j\n", "AST_FORBIDDEN_IMPORT_ALIAS"),
            ("import numpy as np\n", "AST_FORBIDDEN_IMPORT"),
            ("import operator\n", "AST_FORBIDDEN_IMPORT"),
            ("from . import helper\n", "AST_RELATIVE_IMPORT"),
            ("from .foo import bar\n", "AST_RELATIVE_IMPORT"),
            ("from scipy.optimize import linprog\n", "AST_FORBIDDEN_IMPORT"),
            ("from decimal import Decimal\n", "AST_FORBIDDEN_IMPORT"),
            ("from json import loads as l\n", "AST_FORBIDDEN_IMPORT"),
            ("from typing import *\n", "AST_FORBIDDEN_IMPORT"),
            ("from math import log\n", "AST_FORBIDDEN_IMPORT"),
            ("from math import gcd as g\n", "AST_FORBIDDEN_IMPORT"),
            ("from fractions import Fraction as F\n", "AST_FORBIDDEN_IMPORT"),
            ("from fractions import gcd\n", "AST_FORBIDDEN_IMPORT"),
            ("from sys import modules\n", "AST_FORBIDDEN_IMPORT"),
            ("from time import perf_counter\n", "AST_FORBIDDEN_IMPORT"),
            ("from time import perf_counter_ns as pcn\n", "AST_FORBIDDEN_IMPORT"),
            ("import errno\n", "AST_FORBIDDEN_IMPORT"),
            ("from errno import EPERM\n", "AST_FORBIDDEN_IMPORT"),
            ("from errno import ENXIO as e\n", "AST_FORBIDDEN_IMPORT"),
            ("x = math.log(2)\n", "AST_FORBIDDEN_MODULE_ATTR"),
            ("m = sys.modules['math']\n", "AST_FORBIDDEN_MODULE_ATTR"),
            ("t = time.perf_counter()\n", "AST_FORBIDDEN_MODULE_ATTR"),
            ("x = os.system('id')\n", "AST_FORBIDDEN_MODULE_ATTR"),
            ("x = json.JSONEncoder()\n", "AST_FORBIDDEN_MODULE_ATTR"),
            ("import json\nx = json.loads('1.5')\n", "AST_UNSAFE_JSON_LOADS"),
            ("import json\nx = json.loads('1.5', parse_float=None, parse_constant=fn)\n", "AST_UNSAFE_JSON_LOADS"),
            ("import json\nx = json.loads('1.5', parse_float=fn, parse_constant=None)\n", "AST_UNSAFE_JSON_LOADS"),
            ("import json\nx = json.loads('1.5', parse_float=fn)\n", "AST_UNSAFE_JSON_LOADS"),
            ("import json\nx = json.loads('1.5', **kw)\n", "AST_UNSAFE_JSON_LOADS"),
            ("x = Fraction.from_float(1)\n", "AST_FORBIDDEN_ATTR"),
            ("x = Fraction.from_decimal(1)\n", "AST_FORBIDDEN_ATTR"),
            ("x = obj.fromhex('0x1p0')\n", "AST_FORBIDDEN_ATTR"),
            ("x = (1).as_integer_ratio()\n", "AST_FORBIDDEN_ATTR"),
            ("x = '{:.2f}'.format(1)\n", "AST_FORBIDDEN_ATTR"),
            ("x = '{a:.2f}'.format_map({'a': 1})\n", "AST_FORBIDDEN_ATTR"),
            ("x = mv.cast('d')\n", "AST_FORBIDDEN_ATTR"),
            ("x = ast.literal_eval('1.5')\n", "AST_FORBIDDEN_ATTR"),
            ("x = obj.__mro__\n", "AST_FORBIDDEN_ATTR"),
            ("x = (1).real\n", "AST_FORBIDDEN_ATTR"),
            ("x = (1).imag\n", "AST_FORBIDDEN_ATTR"),
            ("x = (1).conjugate()\n", "AST_FORBIDDEN_ATTR"),
            ("x = ().__class__.__base__.__subclasses__()\n", "AST_FORBIDDEN_ATTR"),
            ("x = (1).__truediv__(2)\n", "AST_FORBIDDEN_ATTR"),
            ("x = (1).__rtruediv__(2)\n", "AST_FORBIDDEN_ATTR"),
            ("x = (1).__itruediv__(2)\n", "AST_FORBIDDEN_ATTR"),
            ("x = (1).__floordiv__(2)\n", "AST_FORBIDDEN_ATTR"),
            ("x = (1).__mod__(2)\n", "AST_FORBIDDEN_ATTR"),
            ("x = (2).__pow__(-1)\n", "AST_FORBIDDEN_ATTR"),
            ("x = (2).__rpow__(-1)\n", "AST_FORBIDDEN_ATTR"),
            ("x = (2).__ipow__(-1)\n", "AST_FORBIDDEN_ATTR"),
            ("x = (1).__float__()\n", "AST_FORBIDDEN_ATTR"),
            ("x = (1).__complex__()\n", "AST_FORBIDDEN_ATTR"),
            ("x = (1).__format__('.2f')\n", "AST_FORBIDDEN_ATTR"),
            ("x = (1).__getattribute__('__truediv__')(2)\n", "AST_FORBIDDEN_ATTR"),
            ("def f(s):\n    return s.modules['math']\n", "AST_FORBIDDEN_ATTR"),
            ("def f(t):\n    return t.time()\n", "AST_FORBIDDEN_ATTR"),
            ("from fractions import Fraction\nF = Fraction\nx = F('0.5')\n", "AST_FORBIDDEN_SYMBOL_ALIAS"),
            ("from fractions import Fraction\nF, G = Fraction, 1\n", "AST_FORBIDDEN_SYMBOL_ALIAS"),
            ("from fractions import Fraction\nF: object = Fraction\nx = F('0.5')\n", "AST_FORBIDDEN_SYMBOL_ALIAS"),
            ("from fractions import Fraction\nx = (F := Fraction)('0.5')\n", "AST_FORBIDDEN_SYMBOL_ALIAS"),
            ("from fractions import Fraction\nx = [Fraction][0]('0.5')\n", "AST_FORBIDDEN_SYMBOL_ALIAS"),
            ("import sys\ns = sys\nx = s.modules['math'].pi\n", "AST_FORBIDDEN_SYMBOL_ALIAS"),
            ("import time\nt = time\nx = t.time()\n", "AST_FORBIDDEN_SYMBOL_ALIAS"),
            ("import json\nj = json\nx = j.loads('1.5')\n", "AST_FORBIDDEN_SYMBOL_ALIAS"),
            ("import os\no = os\n", "AST_FORBIDDEN_SYMBOL_ALIAS"),
            ("p = pow\nx = p(2, -1)\n", "AST_FORBIDDEN_SYMBOL_ALIAS"),
            ("x = pow.__doc__\n", "AST_FORBIDDEN_SYMBOL_ALIAS"),
            ("t = type\n", "AST_FORBIDDEN_SYMBOL_ALIAS"),
            ("from fractions import Fraction\nx = type(Fraction(1, 2))('0.5')\n", "AST_FORBIDDEN_SYMBOL_ALIAS"),
            ("x = type(1) == int\n", "AST_FORBIDDEN_SYMBOL_ALIAS"),
            ("x = type(1) is int is True\n", "AST_FORBIDDEN_SYMBOL_ALIAS"),
            ("x = type(1, 2) is int\n", "AST_FORBIDDEN_SYMBOL_ALIAS"),
            ("x = type(1, k=2) is int\n", "AST_FORBIDDEN_SYMBOL_ALIAS"),
            ("x = type(1).__name__\n", "AST_FORBIDDEN_SYMBOL_ALIAS"),
            ("x = type(1, 2).__mro__\n", "AST_FORBIDDEN_ATTR"),
            ("x = type(1, k=2).__mro__\n", "AST_FORBIDDEN_ATTR"),
            ("from fractions import Fraction\nx = type(Fraction(1, 1)).__mro__[0]('0.5')\n", "AST_FORBIDDEN_ATTR"),
            ("from fractions import Fraction\nx = [c('0.5') for c in type(Fraction(1, 1)).__mro__]\n", "AST_FORBIDDEN_ATTR"),
            ("x = any(c.__name__ in ('float', 'complex') for c in type(1).__mro__ if c)\n", "AST_FORBIDDEN_ATTR"),
            ("x = any(c.__name__ == 'float' for c in type(1).__mro__)\n", "AST_FORBIDDEN_ATTR"),
            ("x = any(c.__name__ in (1,) for c in type(1).__mro__)\n", "AST_FORBIDDEN_ATTR"),
            ("x = any(c.__name__ in ('float',) for c in type(1).__mro__ for d in [1])\n", "AST_FORBIDDEN_ATTR"),
            ("x = memoryview(b'12345678')\n", "AST_FORBIDDEN_NAME"),
            ("import sys\nx: sys = 1\n", "AST_FORBIDDEN_SYMBOL_ALIAS"),
            ("from fractions import Fraction\nx = max(1, Fraction)\n", "AST_FORBIDDEN_SYMBOL_ALIAS"),
            ("import sys\nx = isinstance(1, sys)\n", "AST_FORBIDDEN_SYMBOL_ALIAS"),
            ("def Fraction(x):\n    return x\n", "AST_FORBIDDEN_SYMBOL_ALIAS"),
            ("x = float(1)\n", "AST_FORBIDDEN_NAME"),
            ("f = float\n", "AST_FORBIDDEN_NAME"),
            ("x = complex(1, 2)\n", "AST_FORBIDDEN_NAME"),
            ("x = format(1, '.2f')\n", "AST_FORBIDDEN_NAME"),
            ("x = divmod(5, 2)\n", "AST_FORBIDDEN_NAME"),
            ("x = round(1)\n", "AST_FORBIDDEN_NAME"),
            ("x = open('a')\n", "AST_FORBIDDEN_NAME"),
            ("x = eval('1')\n", "AST_FORBIDDEN_NAME"),
            ("exec('x=1')\n", "AST_FORBIDDEN_NAME"),
            ("g = getattr\n", "AST_FORBIDDEN_NAME"),
            ("from fractions import Fraction\nx = Fraction('1/2')\n", "AST_FORBIDDEN_FRACTION_STR"),
            ("from fractions import Fraction\nx = Fraction(f'{a}/2')\n", "AST_FORBIDDEN_FRACTION_STR"),
            ("from fractions import Fraction\nx = Fraction(*a, *b)\n", "AST_FORBIDDEN_FRACTION_STR"),
            ("from fractions import Fraction\nx = Fraction(numerator=1)\n", "AST_FORBIDDEN_FRACTION_KWARGS"),
            ("from fractions import Fraction\nx = Fraction()\n", "AST_FORBIDDEN_FRACTION_ARITY"),
            ("from fractions import Fraction\nx = Fraction(var)\n", "AST_FORBIDDEN_FRACTION_ARITY"),
            ("from fractions import Fraction\nx = Fraction(1, 2, 3)\n", "AST_FORBIDDEN_FRACTION_ARITY"),
        ]
        for snippet, expected in bad_cases:
            with self.subTest(snippet=snippet):
                with self.assertRaisesRegex(mod.CertVerifyError, expected):
                    mod.verify_ast_purity(snippet)

    def test_energy_guard_path_leaks_depth_and_strict_json_loader(self) -> None:
        bad_vals = [
            "45.2 W", "45 W", "45W", "45.2 W.", "45.2W!", "W?", "[W]", "45.2\u00d7W", "45.2-W",
            "45.2 [W]", "W: 45.2", "W=45.2", "W 45", "J 12", "kW 45.2", "45.2 kilowatts",
            "45.2\u200bW", "45.2 k\u200bW", "5 GW", "5 TW", "5 pW", "5 kilo watts", "5 kilo-watts",
            "5 m W", "15 Wh", "5 \u03bcW", "15 watthours", "15 watt hours", "15 watt-hour", "5\u2013W",
            "12\u00b7W", "3.9e2 W", "1.5E-3W", "0.5 kWh", "1.2 J/tok", "j/tok", "1 j/ tok",
            "energy per token", "tokens per joule", "joules per token", "MJ per token",
            "mJ/tok", "10 tok/J", "15 TDP", "TDP 15", "TDP", "70% less energy",
            "70 percent less power", "energy use dropped", "power savings", "power-savings",
            "x_nvml_y", "wa\u0000tt", "5 \u051d", "\u0435nergy", "3 \u043a\u0412\u0442",
            "\uff11\uff12\uff37", "45 milliwatts", "1.2 megawatts", "12.5 kilojoules",
            "W: 45.2 drain", "45.2[W] drain", "J: 5", "cap_45_w", "45_watts", "limit_45_w",
            "draw_45w", "45 Whr", "130w_psu", "max_45w", "45w", "5 PW", "45.2 \u03c9", "\u051datt",
            "45.2\u2219W", "fifty watts", "5 Ws", "wattage", "measured with RAPL",
            "NVML telemetry", "nvidia-smi draw", "power\tconsumption",
            "forty-five watts", "energy: 12", "power = 45", "rapluj", "J/token",
            "W/tok", "250 W/ token", "250 W / token", "tok_per_mwh", "nvml_power",
            "nvmlDeviceGetTotalEnergyConsumption",
        ]
        good_vals = [
            "5 ms", "latency 12", "70 C", "78\u00b0C", "70/78/85 C knees", "5 C deadband",
            "5 deg C deadband", "135/2", "45.0%", "0.5 mm", "ac", "battery", "unknown", "temp_c",
            "gpu_temp_exceeded", "UNCONTROLLED_LAPTOP_NOT_CLAIMED", "grad_W_q",
            "stdlib_sha256_chain", "cpu_jiffies_total", "a" * 64, "129,279.00 tok/s",
            "469.41 us/tok", "8.113 MiB", "sm_86", "wmma", "window 20", "warp 32",
            "16 warps/SM", "h256", "rows 1024", "tdp_like_free_text_no", "J2000 epoch-like",
            "J2000.0", "2024-W05", "sprint-W12", "node-w10", "q4-w3", "W-2", "W12", "kW12",
            "bench w/ perf counters", "taskset -c 3 w/ 5 reps", "12 ms/tok", "sm_clock 2100 MHz",
            "0.9 V", "1024 MiB/s", "not_on_ac_power",
            "j = 3", "i = 1, j = 3", "w = 7", "3 w/o pinning", "run 3 W/O cache",
            "w/ tokens", "j = 3 w/o pinning",
        ]
        for b in bad_vals:
            self.assertTrue(mod.is_forbidden_energy_value(b), f"Missed bad energy payload: {b!r}")
        for g in good_vals:
            self.assertFalse(mod.is_forbidden_energy_value(g), f"False positive on good value: {g!r}")

        # Linear-time ReDoS stress guard (CPU process_time immune to host scheduling jitter)
        t_redos0 = time.process_time()
        for probe in (
            "1" + "." * 4000,
            "1," * 2500,
            "1" + "." * 10000,
            "9" * 10000,
            "1.2." * 3000,
            "energy" + " " * 10000 + "ok",
        ):
            self.assertFalse(mod.is_forbidden_energy_value(probe))
        elapsed_redos = time.process_time() - t_redos0
        self.assertLess(elapsed_redos, 0.25, f"Energy regex exceeded linear-time budget: {elapsed_redos:.4f}s")

        with self.assertRaisesRegex(mod.CertVerifyError, "BAD_POLICY_STR"):
            mod.is_forbidden_energy_value(123)  # type: ignore[arg-type]
        with self.assertRaisesRegex(mod.CertVerifyError, "BAD_POLICY_KEY"):
            mod.is_forbidden_energy_key(123)  # type: ignore[arg-type]
        self.assertFalse(mod.is_forbidden_energy_key("energy_power_status"))
        for bad_k in ("power_draw_w", "avgPower", "rapl", "rapluj", "nvml", "nvml_power", "wattage", "pkg_w", "\u0435nergy_k"):
            self.assertTrue(mod.is_forbidden_energy_key(bad_k), f"Missed bad key: {bad_k!r}")

        mod.check_json_tree_clean({"ok": [1, "2/3", ("a", True)], "energy_power_status": mod.ENERGY_POLICY_EXPECTED})
        # Exact depth limit boundary: 32 passes (kills <= -> <), 33 and 500 fail cleanly without RecursionError
        deep_ok: object = "leaf"
        for _ in range(mod.MAX_JSON_DEPTH):
            deep_ok = [deep_ok]
        mod.check_json_tree_clean(deep_ok)
        with self.assertRaisesRegex(mod.CertVerifyError, "JSON_MAX_DEPTH_EXCEEDED"):
            mod.check_json_tree_clean([deep_ok])
        deep_500: object = "leaf"
        for _ in range(500):
            deep_500 = [deep_500]
        with self.assertRaisesRegex(mod.CertVerifyError, "JSON_MAX_DEPTH_EXCEEDED"):
            mod.check_json_tree_clean(deep_500)

        with self.assertRaisesRegex(mod.CertVerifyError, "JSON_FORBIDDEN_FLOAT"):
            mod.check_json_tree_clean({"v": 1.25})
        with self.assertRaisesRegex(mod.CertVerifyError, "JSON_FORBIDDEN_FLOAT"):
            mod.check_json_tree_clean({"v": 1j})
        with self.assertRaisesRegex(mod.CertVerifyError, "JSON_KEY_NOT_STR"):
            mod.check_json_tree_clean({1: "x"})
        with self.assertRaisesRegex(mod.CertVerifyError, "JSON_ALLOWLIST_SMUGGLE"):
            mod.check_json_tree_clean({"energy_power_status": 45})
        with self.assertRaisesRegex(mod.CertVerifyError, "JSON_ALLOWLIST_SMUGGLE"):
            mod.check_json_tree_clean({"energy_power_status": "other"})
        with self.assertRaisesRegex(mod.CertVerifyError, "JSON_ENERGY_CLAIM_VALUE"):
            mod.check_json_tree_clean({"nested": {"note": "x_nvml_y"}})
        with self.assertRaisesRegex(mod.CertVerifyError, "JSON_ENERGY_CLAIM_KEY"):
            mod.check_json_tree_clean({"rapl": "ok"})
        for tok in mod.FORBIDDEN_PATH_TOKENS:
            with self.assertRaisesRegex(mod.CertVerifyError, "JSON_PATH_LEAK"):
                mod.check_json_tree_clean({"msg": f"bad {tok} leak"})
            with self.assertRaisesRegex(mod.CertVerifyError, "JSON_PATH_LEAK"):
                mod.check_json_tree_clean({f"k_{tok}": 1})

        with tempfile.TemporaryDirectory() as td:
            tdp = Path(td)
            p = tdp.joinpath("sample.json")
            with self.assertRaisesRegex(mod.CertVerifyError, "JSON_MISSING"):
                mod.load_strict_json("not_a_path")  # type: ignore[arg-type]
            with self.assertRaisesRegex(mod.CertVerifyError, "JSON_MISSING"):
                mod.load_strict_json(p)
            p.write_text('{"a": 1, "a": 2}\n', encoding="utf-8")
            with self.assertRaisesRegex(mod.CertVerifyError, "JSON_DUP_KEY"):
                mod.load_strict_json(p)
            p.write_text('{"x": 1.5}\n', encoding="utf-8")
            with self.assertRaisesRegex(mod.CertVerifyError, "JSON_FORBIDDEN_FLOAT"):
                mod.load_strict_json(p)
            p.write_text('{"x": NaN}\n', encoding="utf-8")
            with self.assertRaisesRegex(mod.CertVerifyError, "JSON_BAD_CONST"):
                mod.load_strict_json(p)
            p.write_text("{bad json", encoding="utf-8")
            with self.assertRaisesRegex(mod.CertVerifyError, "JSON_PARSE_ERROR"):
                mod.load_strict_json(p)
            p.write_text("[1, 2, 3]\n", encoding="utf-8")
            with self.assertRaisesRegex(mod.CertVerifyError, "JSON_ROOT_NOT_DICT"):
                mod.load_strict_json(p)

            # Pre-json.loads raw depth cap (32 pass, 33 & 5000 fail, string braces/escapes ignored)
            p.write_text('{"a":' * 32 + "1" + "}" * 32 + "\n", encoding="utf-8")
            mod.load_strict_json(p)
            p.write_text('{"a":' * 33 + "1" + "}" * 33 + "\n", encoding="utf-8")
            with self.assertRaisesRegex(mod.CertVerifyError, "JSON_MAX_DEPTH_EXCEEDED"):
                mod.load_strict_json(p)
            p.write_text("[" * 5000 + "]" * 5000 + "\n", encoding="utf-8")
            with self.assertRaisesRegex(mod.CertVerifyError, "JSON_MAX_DEPTH_EXCEEDED"):
                mod.load_strict_json(p)
            p.write_text('{"s": "' + ("[" * 50) + '\\"' + ("[" * 50) + '"}\n', encoding="utf-8")
            mod.load_strict_json(p)

            # Integer digit cap boundary (1024 pass, 1025 & 4400 fail cleanly)
            p.write_text('{"x": ' + ("9" * 1024) + ', "y": -' + ("9" * 1024) + "}\n", encoding="utf-8")
            mod.load_strict_json(p)
            for bad_int in ("9" * 1025, "-" + "9" * 1025, "9" * 4400):
                p.write_text('{"x": ' + bad_int + "}\n", encoding="utf-8")
                with self.assertRaisesRegex(mod.CertVerifyError, "JSON_INT_DIGIT_LIMIT"):
                    mod.load_strict_json(p)

            # File size cap (exact boundary passes, +1 fails), non-regular dir/FIFO, symlinks, & OSErrors
            self.assertEqual(mod._READ_NOFOLLOW_FLAGS & os.O_NONBLOCK, os.O_NONBLOCK)
            self.assertEqual(mod._WRITE_NOFOLLOW_FLAGS & os.O_NONBLOCK, os.O_NONBLOCK)
            p.write_bytes(b'{"ok": "123456"}')
            self.assertEqual(mod.load_strict_json(p, max_bytes=16)[0], {"ok": "123456"})
            with self.assertRaisesRegex(mod.CertVerifyError, "FILE_TOO_LARGE"):
                mod.load_strict_json(p, max_bytes=15)
            with self.assertRaisesRegex(mod.CertVerifyError, "NOT_REGULAR_FILE"):
                mod.read_regular_bytes_nofollow(tdp)
            fifo_p = tdp.joinpath("pipe.fifo")
            os.mkfifo(str(fifo_p))
            with self.assertRaisesRegex(mod.CertVerifyError, "NOT_REGULAR_FILE"):
                mod.read_regular_bytes_nofollow(fifo_p)
            with self.assertRaisesRegex(mod.CertVerifyError, "NOT_REGULAR_FILE"):
                mod.write_regular_bytes_nofollow(tdp, b"{}")
            with self.assertRaisesRegex(mod.CertVerifyError, "NOT_REGULAR_FILE"):
                mod.write_regular_bytes_nofollow(fifo_p, b"{}")
            fifo_rd = os.open(str(fifo_p), os.O_RDONLY | os.O_NONBLOCK)
            try:
                with self.assertRaisesRegex(mod.CertVerifyError, "NOT_REGULAR_FILE"):
                    mod.write_regular_bytes_nofollow(fifo_p, b"{}")
            finally:
                os.close(fifo_rd)
            sym_p = tdp.joinpath("sym.json")
            os.symlink(str(p), str(sym_p))
            with self.assertRaisesRegex(mod.CertVerifyError, "SYMLINK_FORBIDDEN"):
                mod.load_strict_json(sym_p)
            with self.assertRaisesRegex(mod.CertVerifyError, "SYMLINK_FORBIDDEN"):
                mod.write_regular_bytes_nofollow(sym_p, b"{}")
            with self.assertRaisesRegex(mod.CertVerifyError, "NOT_REGULAR_FILE"):
                mod.write_regular_bytes_nofollow(Path("/dev/null"), b"{}")
            w_p = tdp.joinpath("short_write.json")
            with patch("os.write", return_value=0):
                with self.assertRaisesRegex(mod.CertVerifyError, "IO_SHORT_WRITE"):
                    mod.write_regular_bytes_nofollow(w_p, b"{}")
            with patch("os.write", side_effect=OSError("io fail")):
                with self.assertRaisesRegex(mod.CertVerifyError, "JSON_WRITE_ERROR"):
                    mod.write_regular_bytes_nofollow(w_p, b"{}")
            with patch("os.open", side_effect=PermissionError("denied")):
                with self.assertRaisesRegex(mod.CertVerifyError, "JSON_READ_ERROR"):
                    mod.load_strict_json(p)
                with self.assertRaisesRegex(mod.CertVerifyError, "JSON_WRITE_ERROR"):
                    mod.write_regular_bytes_nofollow(w_p, b"{}")
            with patch("os.read", side_effect=OSError("io fail")):
                with self.assertRaisesRegex(mod.CertVerifyError, "JSON_READ_ERROR"):
                    mod.load_strict_json(p)


class TestLinearAlgebraAndFarkasR5(unittest.TestCase):
    def test_fangcheng_vs_naive_solve_rank_and_residual(self) -> None:
        self.assertEqual(mod.fangcheng_rank_z([]), 0)
        self.assertEqual(mod.fangcheng_rank_z([[0, 2], [3, 4]]), 2)
        self.assertEqual(mod.fangcheng_rank_z([[1, 2, 3], [2, 4, 6], [0, 0, 0]]), 1)
        self.assertEqual(mod.fangcheng_rank_z([[0, 1], [0, 2]]), 1)
        self.assertEqual(mod.fangcheng_rank_z([[1, 0], [0, 1], [1, 1]]), 2)
        with self.assertRaisesRegex(mod.CertVerifyError, "RANK_RAGGED_MATRIX"):
            mod.fangcheng_rank_z([[1, 2], [3]])
        with self.assertRaisesRegex(mod.CertVerifyError, "RANK_NON_INT"):
            mod.fangcheng_rank_z([[True, 0], [0, 1]])  # type: ignore[list-item]

        a_int = [[0, 2, 1], [3, 1, 0], [0, 0, 5]]
        b_int = [5, 5, 15]
        sol_fc = mod.fangcheng_solve_z(a_int, b_int)
        a_q = [[Fraction(v, 1) for v in r] for r in a_int]
        b_q = [Fraction(v, 1) for v in b_int]
        sol_nv = mod.naive_dense_fraction_solve_q(a_q, b_q)
        self.assertEqual(sol_fc, sol_nv)
        self.assertEqual(sol_fc, [Fraction(4, 3), Fraction(1, 1), Fraction(3, 1)])
        self.assertTrue(mod.verify_linear_residual_q(a_int, b_int, sol_fc))

        # Bench helper verification guards
        mod._verify_bench_solutions(a_int, b_int, sol_fc, sol_nv, sol_fc)
        with self.assertRaisesRegex(mod.CertVerifyError, "BENCH_SOL_FC_MISMATCH"):
            mod._verify_bench_solutions(a_int, b_int, [Fraction(0, 1), sol_fc[1], sol_fc[2]], sol_nv, sol_fc)
        with self.assertRaisesRegex(mod.CertVerifyError, "BENCH_SOL_NAIVE_MISMATCH"):
            mod._verify_bench_solutions(a_int, b_int, sol_fc, [Fraction(0, 1), sol_nv[1], sol_nv[2]], sol_fc)
        mod._verify_small_ctrl_equal([Fraction(0, 1)], [Fraction(0, 1)])
        with self.assertRaisesRegex(mod.CertVerifyError, "BENCH_SMALL_CTRL_MISMATCH"):
            mod._verify_small_ctrl_equal([Fraction(0, 1)], [Fraction(1, 1)])

        bad_sol = [sol_fc[0] + EPS_1E9, sol_fc[1], sol_fc[2]]
        with self.assertRaisesRegex(mod.CertVerifyError, "LINEAR_RESIDUAL_NONZERO"):
            mod.verify_linear_residual_q(a_int, b_int, bad_sol)
        with self.assertRaisesRegex(mod.CertVerifyError, "NON_EXACT_VALUE"):
            mod.verify_linear_residual_q(a_int, b_int, [1.0, sol_fc[1], sol_fc[2]])  # type: ignore[list-item]
        with self.assertRaisesRegex(mod.CertVerifyError, "NON_EXACT_VALUE"):
            mod.verify_linear_residual_q([[0.5, 2, 1], [3, 1, 0], [0, 0, 5]], b_int, sol_fc)  # type: ignore[list-item]
        with self.assertRaisesRegex(mod.CertVerifyError, "NON_EXACT_VALUE"):
            mod.verify_linear_residual_q(a_int, [True, 5, 15], sol_fc)  # type: ignore[list-item]
        with self.assertRaisesRegex(mod.CertVerifyError, "RESIDUAL_ROW_WIDTH_MISMATCH"):
            mod.verify_linear_residual_q([[0, 2], [3, 1, 0], [0, 0, 5]], b_int, sol_fc)
        with self.assertRaisesRegex(mod.CertVerifyError, "RESIDUAL_DIM_MISMATCH"):
            mod.verify_linear_residual_q(a_int, b_int[:2], sol_fc)
        with self.assertRaisesRegex(mod.CertVerifyError, "RESIDUAL_DIM_MISMATCH"):
            mod.verify_linear_residual_q(a_int, b_int, sol_fc[:2])

        for fn, mat, rhs in (
            (mod.fangcheng_solve_z, [[1, 2], [2, 4]], [3, 6]),
            (mod.naive_dense_fraction_solve_q, [[Fraction(1, 1), Fraction(2, 1)], [Fraction(2, 1), Fraction(4, 1)]], [Fraction(3, 1), Fraction(6, 1)]),
        ):
            with self.assertRaisesRegex(mod.CertVerifyError, "SINGULAR_SYSTEM"):
                fn(mat, rhs)  # type: ignore[arg-type]
        with self.assertRaisesRegex(mod.CertVerifyError, "BAD_SOLVE_DIMS"):
            mod.fangcheng_solve_z([], [])
        with self.assertRaisesRegex(mod.CertVerifyError, "BAD_SOLVE_DIMS"):
            mod.fangcheng_solve_z([[1]], [1, 2])
        with self.assertRaisesRegex(mod.CertVerifyError, "NON_SQUARE_SYSTEM"):
            mod.fangcheng_solve_z([[1, 2], [3]], [1, 2])
        with self.assertRaisesRegex(mod.CertVerifyError, "SOLVE_NON_INT"):
            mod.fangcheng_solve_z([[1, 0], [0, 1]], [True, 1])  # type: ignore[list-item]
        with self.assertRaisesRegex(mod.CertVerifyError, "SOLVE_NON_INT"):
            mod.fangcheng_solve_z([[True, 0], [0, 1]], [1, 1])  # type: ignore[list-item]
        with self.assertRaisesRegex(mod.CertVerifyError, "BAD_SOLVE_DIMS"):
            mod.naive_dense_fraction_solve_q([], [])
        with self.assertRaisesRegex(mod.CertVerifyError, "BAD_SOLVE_DIMS"):
            mod.naive_dense_fraction_solve_q([[Fraction(1, 1)]], [Fraction(1, 1), Fraction(2, 1)])

        with self.assertRaisesRegex(mod.CertVerifyError, "DOT_LEN_MISMATCH"):
            mod._dot_q([Fraction(1, 1)], [])
        with self.assertRaisesRegex(mod.CertVerifyError, "NON_EXACT_VALUE"):
            mod._dot_q([1.0], [Fraction(1, 1)])  # type: ignore[list-item]
        with self.assertRaisesRegex(mod.CertVerifyError, "NON_EXACT_VALUE"):
            mod._dot_q([Fraction(1, 1)], [1.0])  # type: ignore[list-item]
        with self.assertRaisesRegex(mod.CertVerifyError, "NON_EXACT_VALUE"):
            mod._clear_matrix_denoms_z([[1.0]])  # type: ignore[list-item]

    def test_lp_primal_dual_farkas_and_sparse_refusals(self) -> None:
        a_max = [
            [Fraction(1, 1), Fraction(1, 1)],
            [Fraction(0, 1), Fraction(1, 1)],
            [Fraction(2, 1), Fraction(2, 1)],
            [Fraction(1, 1), Fraction(0, 1)],
        ]
        b_max = [Fraction(4, 1), Fraction(2, 1), Fraction(8, 1), Fraction(5, 1)]
        c_max = [Fraction(1, 1), Fraction(2, 1)]
        x_max = [Fraction(2, 1), Fraction(2, 1)]
        y_max = [Fraction(1, 1), Fraction(1, 1), Fraction(0, 1), Fraction(0, 1)]
        res = mod.verify_lp_primal_dual_q(a_max, b_max, c_max, x_max, y_max, "max_le", active_rows=[0, 1], active_cols=[0, 1])
        self.assertEqual(res["primal_obj"], "6/1")
        self.assertEqual(res["active_support_rank"], 2)

        a_min = [[Fraction(1, 1), Fraction(1, 1)], [Fraction(1, 1), Fraction(2, 1)]]
        b_min = [Fraction(2, 1), Fraction(3, 1)]
        c_min = [Fraction(3, 1), Fraction(4, 1)]
        x_min = [Fraction(1, 1), Fraction(1, 1)]
        y_min = [Fraction(2, 1), Fraction(1, 1)]
        res_min = mod.verify_lp_primal_dual_q(a_min, b_min, c_min, x_min, y_min, "min_ge", active_rows=[0, 1])
        self.assertEqual(res_min["primal_obj"], "7/1")

        # Sign flip, 1/10^9 primal/dual/gap, rank-deficient/negative/dup active support, float injection
        with self.assertRaisesRegex(mod.CertVerifyError, "DUAL_SIGN_VIOLATION"):
            mod.verify_lp_primal_dual_q(a_max, b_max, c_max, x_max, [Fraction(1, 1), Fraction(1, 1), -EPS_1E9, Fraction(0, 1)], "max_le")
        with self.assertRaisesRegex(mod.CertVerifyError, "PRIMAL_NEGATIVE_VAR"):
            mod.verify_lp_primal_dual_q(a_max, b_max, c_max, [-EPS_1E9, Fraction(2, 1)], y_max, "max_le")
        with self.assertRaisesRegex(mod.CertVerifyError, "PRIMAL_INFEASIBLE"):
            mod.verify_lp_primal_dual_q(a_max, b_max, c_max, [Fraction(2, 1) + EPS_1E9, Fraction(2, 1)], y_max, "max_le")
        with self.assertRaisesRegex(mod.CertVerifyError, "PRIMAL_INFEASIBLE"):
            mod.verify_lp_primal_dual_q(a_min, b_min, c_min, [Fraction(1, 1) - EPS_1E9, Fraction(1, 1)], y_min, "min_ge")
        with self.assertRaisesRegex(mod.CertVerifyError, "DUAL_INFEASIBLE"):
            mod.verify_lp_primal_dual_q(a_max, b_max, c_max, x_max, [Fraction(1, 1) - EPS_1E9, Fraction(1, 1), Fraction(0, 1), Fraction(0, 1)], "max_le")
        with self.assertRaisesRegex(mod.CertVerifyError, "DUAL_INFEASIBLE"):
            mod.verify_lp_primal_dual_q(a_min, b_min, c_min, x_min, [Fraction(2, 1) + EPS_1E9, Fraction(1, 1)], "min_ge")
        with self.assertRaisesRegex(mod.CertVerifyError, "DUALITY_GAP_NONZERO"):
            mod.verify_lp_primal_dual_q(a_max, b_max, c_max, x_max, [Fraction(1, 1) + EPS_1E9, Fraction(1, 1), Fraction(0, 1), Fraction(0, 1)], "max_le")
        with self.assertRaisesRegex(mod.CertVerifyError, "RANK_DEFICIENT_ACTIVE_SUPPORT"):
            mod.verify_lp_primal_dual_q(a_max, b_max, c_max, x_max, y_max, "max_le", active_rows=[0, 2])
        with self.assertRaisesRegex(mod.CertVerifyError, "INACTIVE_ROW_IN_SUPPORT"):
            mod.verify_lp_primal_dual_q(a_max, b_max, c_max, x_max, y_max, "max_le", active_rows=[0, 3])
        with self.assertRaisesRegex(mod.CertVerifyError, "EMPTY_ACTIVE_SUPPORT"):
            mod.verify_lp_primal_dual_q(a_max, b_max, c_max, x_max, y_max, "max_le", active_rows=[])
        with self.assertRaisesRegex(mod.CertVerifyError, "DUP_ACTIVE_ROW"):
            mod.verify_lp_primal_dual_q(a_max, b_max, c_max, x_max, y_max, "max_le", active_rows=[0, 0])
        with self.assertRaisesRegex(mod.CertVerifyError, "BAD_ACTIVE_ROW"):
            mod.verify_lp_primal_dual_q(a_max, b_max, c_max, x_max, y_max, "max_le", active_rows=[-1])
        with self.assertRaisesRegex(mod.CertVerifyError, "BAD_ACTIVE_ROW"):
            mod.verify_lp_primal_dual_q(a_max, b_max, c_max, x_max, y_max, "max_le", active_rows=[4])
        with self.assertRaisesRegex(mod.CertVerifyError, "BAD_ACTIVE_ROW"):
            mod.verify_lp_primal_dual_q(a_max, b_max, c_max, x_max, y_max, "max_le", active_rows=[True])  # type: ignore[list-item]
        with self.assertRaisesRegex(mod.CertVerifyError, "EMPTY_ACTIVE_COLS"):
            mod.verify_lp_primal_dual_q(a_max, b_max, c_max, x_max, y_max, "max_le", active_rows=[0], active_cols=[])
        with self.assertRaisesRegex(mod.CertVerifyError, "DUP_ACTIVE_COL"):
            mod.verify_lp_primal_dual_q(a_max, b_max, c_max, x_max, y_max, "max_le", active_rows=[0, 1], active_cols=[0, 0])
        with self.assertRaisesRegex(mod.CertVerifyError, "BAD_ACTIVE_COL"):
            mod.verify_lp_primal_dual_q(a_max, b_max, c_max, x_max, y_max, "max_le", active_rows=[0], active_cols=[-1])
        with self.assertRaisesRegex(mod.CertVerifyError, "BAD_ACTIVE_COL"):
            mod.verify_lp_primal_dual_q(a_max, b_max, c_max, x_max, y_max, "max_le", active_rows=[0], active_cols=[2])
        with self.assertRaisesRegex(mod.CertVerifyError, "BAD_ACTIVE_COL"):
            mod.verify_lp_primal_dual_q(a_max, b_max, c_max, x_max, y_max, "max_le", active_rows=[0], active_cols=[True])  # type: ignore[list-item]
        with self.assertRaisesRegex(mod.CertVerifyError, "NON_EXACT_VALUE"):
            mod.verify_lp_primal_dual_q(a_max, b_max, c_max, [-2.0, Fraction(2, 1)], y_max, "max_le")  # type: ignore[list-item]
        with self.assertRaisesRegex(mod.CertVerifyError, "NON_EXACT_VALUE"):
            mod.verify_lp_primal_dual_q(a_max, b_max, c_max, x_max, [-1.0, Fraction(1, 1), Fraction(0, 1), Fraction(0, 1)], "max_le")  # type: ignore[list-item]
        with self.assertRaisesRegex(mod.CertVerifyError, "BAD_LP_SENSE"):
            mod.verify_lp_primal_dual_q(a_max, b_max, c_max, x_max, y_max, "eq")
        with self.assertRaisesRegex(mod.CertVerifyError, "EMPTY_LP"):
            mod.verify_lp_primal_dual_q([], [], c_max, x_max, [], "max_le")
        with self.assertRaisesRegex(mod.CertVerifyError, "EMPTY_LP"):
            mod.verify_lp_primal_dual_q(a_max, b_max, [], [], y_max, "max_le")
        with self.assertRaisesRegex(mod.CertVerifyError, "LP_DIM_MISMATCH"):
            mod.verify_lp_primal_dual_q(a_max, b_max[:3], c_max, x_max, y_max, "max_le")
        with self.assertRaisesRegex(mod.CertVerifyError, "LP_DIM_MISMATCH"):
            mod.verify_lp_primal_dual_q(a_max, b_max, c_max, x_max[:1], y_max, "max_le")
        with self.assertRaisesRegex(mod.CertVerifyError, "LP_DIM_MISMATCH"):
            mod.verify_lp_primal_dual_q(a_max, b_max, c_max, x_max, y_max[:3], "max_le")
        with self.assertRaisesRegex(mod.CertVerifyError, "LP_ROW_WIDTH_MISMATCH"):
            mod.verify_lp_primal_dual_q([a_max[0][:1]] + a_max[1:], b_max, c_max, x_max, y_max, "max_le")

        # Farkas infeasibility refusals (including ragged rows and float injection in A and b)
        af = [[Fraction(1, 1)], [Fraction(-1, 1)]]
        bf = [Fraction(2, 1), Fraction(-3, 1)]
        yf = [Fraction(1, 1), Fraction(1, 1)]
        self.assertEqual(mod.verify_farkas_infeasibility_q(af, bf, yf)["b_dot_y"], "-1/1")
        with self.assertRaisesRegex(mod.CertVerifyError, "FARKAS_DIM_MISMATCH"):
            mod.verify_farkas_infeasibility_q([], [], [])
        with self.assertRaisesRegex(mod.CertVerifyError, "FARKAS_DIM_MISMATCH"):
            mod.verify_farkas_infeasibility_q(af, bf[:1], yf)
        with self.assertRaisesRegex(mod.CertVerifyError, "FARKAS_DIM_MISMATCH"):
            mod.verify_farkas_infeasibility_q(af, bf, yf[:1])
        with self.assertRaisesRegex(mod.CertVerifyError, "FARKAS_EMPTY_COLS"):
            mod.verify_farkas_infeasibility_q([[], []], bf, yf)
        with self.assertRaisesRegex(mod.CertVerifyError, "FARKAS_ROW_WIDTH_MISMATCH"):
            mod.verify_farkas_infeasibility_q([[Fraction(1, 1), Fraction(1, 1)], [Fraction(-1, 1), Fraction(-1, 1), Fraction(99, 1)]], bf, yf)
        with self.assertRaisesRegex(mod.CertVerifyError, "NON_EXACT_VALUE"):
            mod.verify_farkas_infeasibility_q([[0.5], [-0.5]], bf, yf)  # type: ignore[list-item]
        with self.assertRaisesRegex(mod.CertVerifyError, "NON_EXACT_VALUE"):
            mod.verify_farkas_infeasibility_q(af, [2.0, Fraction(-3, 1)], [-EPS_1E9, Fraction(1, 1)])  # type: ignore[list-item]
        with self.assertRaisesRegex(mod.CertVerifyError, "NON_EXACT_VALUE"):
            mod.verify_farkas_infeasibility_q(af, bf, [-1.0, Fraction(1, 1)])  # type: ignore[list-item]
        with self.assertRaisesRegex(mod.CertVerifyError, "FARKAS_DUAL_NEGATIVE"):
            mod.verify_farkas_infeasibility_q(af, bf, [-EPS_1E9, Fraction(1, 1)])
        with self.assertRaisesRegex(mod.CertVerifyError, "FARKAS_ATY_NONZERO"):
            mod.verify_farkas_infeasibility_q(af, bf, [Fraction(1, 1) + EPS_1E9, Fraction(1, 1)])
        with self.assertRaisesRegex(mod.CertVerifyError, "FARKAS_BTY_NOT_NEGATIVE"):
            mod.verify_farkas_infeasibility_q(af, [Fraction(3, 1), Fraction(-3, 1)], yf)

        # Sparse quotient LP verifier & helper guards (goals/edges bounds + Fraction type on mu/caps/w)
        goals = [0]
        edges = [(1, 0, Fraction(3, 2))]
        mu = [Fraction(1, 1), Fraction(2, 1)]
        caps = [Fraction(5, 1), Fraction(5, 1)]
        h = [Fraction(0, 1), Fraction(3, 2)]
        dy = [Fraction(2, 1)]
        dz = [Fraction(3, 1), Fraction(0, 1)]
        self.assertEqual(mod.verify_quotient_lp_sparse_q(2, goals, edges, mu, caps, h, dy, dz)["primal_obj"], "3/1")
        with self.assertRaisesRegex(mod.CertVerifyError, "SPARSE_DIM_MISMATCH"):
            mod.verify_quotient_lp_sparse_q(0, goals, edges, [], [], [], dy, [])
        with self.assertRaisesRegex(mod.CertVerifyError, "SPARSE_DIM_MISMATCH"):
            mod.verify_quotient_lp_sparse_q(True, [0], [], [Fraction(1, 1)], [Fraction(1, 1)], [Fraction(0, 1)], [], [Fraction(1, 1)])  # type: ignore[arg-type]
        with self.assertRaisesRegex(mod.CertVerifyError, "SPARSE_DIM_MISMATCH"):
            mod.verify_quotient_lp_sparse_q(2, goals, edges, mu[:1], caps, h, dy, dz)
        with self.assertRaisesRegex(mod.CertVerifyError, "SPARSE_DIM_MISMATCH"):
            mod.verify_quotient_lp_sparse_q(2, goals, edges, mu, caps[:1], h, dy, dz)
        with self.assertRaisesRegex(mod.CertVerifyError, "SPARSE_CERT_DIM_MISMATCH"):
            mod.verify_quotient_lp_sparse_q(2, goals, edges, mu, caps, h[:1], dy, dz)
        with self.assertRaisesRegex(mod.CertVerifyError, "SPARSE_CERT_DIM_MISMATCH"):
            mod.verify_quotient_lp_sparse_q(2, goals, edges, mu, caps, h, [], dz)
        with self.assertRaisesRegex(mod.CertVerifyError, "SPARSE_CERT_DIM_MISMATCH"):
            mod.verify_quotient_lp_sparse_q(2, goals, edges, mu, caps, h, dy, dz[:1])
        with self.assertRaisesRegex(mod.CertVerifyError, "SPARSE_BAD_GOAL"):
            mod.verify_quotient_lp_sparse_q(2, [-1], edges, mu, caps, h, dy, dz)
        with self.assertRaisesRegex(mod.CertVerifyError, "SPARSE_BAD_GOAL"):
            mod.verify_quotient_lp_sparse_q(2, [2], edges, mu, caps, h, dy, dz)
        with self.assertRaisesRegex(mod.CertVerifyError, "SPARSE_BAD_GOAL"):
            mod.verify_quotient_lp_sparse_q(2, [True], edges, mu, caps, h, dy, dz)  # type: ignore[list-item]
        with self.assertRaisesRegex(mod.CertVerifyError, "SPARSE_BAD_EDGE_VERTEX"):
            mod.verify_quotient_lp_sparse_q(2, goals, [(-1, 0, Fraction(3, 2))], mu, caps, h, dy, dz)
        with self.assertRaisesRegex(mod.CertVerifyError, "SPARSE_BAD_EDGE_VERTEX"):
            mod.verify_quotient_lp_sparse_q(2, goals, [(2, 0, Fraction(3, 2))], mu, caps, h, dy, dz)
        with self.assertRaisesRegex(mod.CertVerifyError, "SPARSE_BAD_EDGE_VERTEX"):
            mod.verify_quotient_lp_sparse_q(2, goals, [(True, 0, Fraction(3, 2))], mu, caps, h, dy, dz)  # type: ignore[list-item]
        with self.assertRaisesRegex(mod.CertVerifyError, "SPARSE_BAD_EDGE_VERTEX"):
            mod.verify_quotient_lp_sparse_q(2, goals, [(1, -1, Fraction(3, 2))], mu, caps, h, dy, dz)
        with self.assertRaisesRegex(mod.CertVerifyError, "SPARSE_BAD_EDGE_VERTEX"):
            mod.verify_quotient_lp_sparse_q(2, goals, [(1, 2, Fraction(3, 2))], mu, caps, h, dy, dz)
        with self.assertRaisesRegex(mod.CertVerifyError, "SPARSE_BAD_EDGE_VERTEX"):
            mod.verify_quotient_lp_sparse_q(2, goals, [(1, False, Fraction(3, 2))], mu, caps, h, dy, dz)  # type: ignore[list-item]
        with self.assertRaisesRegex(mod.CertVerifyError, "NON_EXACT_VALUE"):
            mod.verify_quotient_lp_sparse_q(2, goals, edges, [1.0, Fraction(2, 1)], caps, h, dy, dz)  # type: ignore[list-item]
        with self.assertRaisesRegex(mod.CertVerifyError, "NON_EXACT_VALUE"):
            mod.verify_quotient_lp_sparse_q(2, goals, edges, mu, [5.0, Fraction(5, 1)], h, dy, dz)  # type: ignore[list-item]
        with self.assertRaisesRegex(mod.CertVerifyError, "NON_EXACT_VALUE"):
            mod.verify_quotient_lp_sparse_q(2, goals, [(1, 0, 1.5)], mu, caps, h, dy, dz)  # type: ignore[list-item]
        with self.assertRaisesRegex(mod.CertVerifyError, "NON_EXACT_VALUE"):
            mod.verify_quotient_lp_sparse_q(2, goals, edges, mu, caps, [-1.0, Fraction(3, 2)], dy, dz)  # type: ignore[list-item]
        with self.assertRaisesRegex(mod.CertVerifyError, "NON_EXACT_VALUE"):
            mod.verify_quotient_lp_sparse_q(2, goals, edges, mu, caps, h, dy, [-1.0, Fraction(0, 1)])  # type: ignore[list-item]
        with self.assertRaisesRegex(mod.CertVerifyError, "NON_EXACT_VALUE"):
            mod.verify_quotient_lp_sparse_q(2, goals, edges, mu, caps, h, [-1.0], dz)  # type: ignore[list-item]
        with self.assertRaisesRegex(mod.CertVerifyError, "PRIMAL_NEGATIVE_VAR"):
            mod.verify_quotient_lp_sparse_q(2, goals, edges, mu, caps, [-EPS_1E9, Fraction(3, 2)], dy, dz)
        with self.assertRaisesRegex(mod.CertVerifyError, "DUAL_SIGN_VIOLATION"):
            mod.verify_quotient_lp_sparse_q(2, goals, edges, mu, caps, h, dy, [Fraction(3, 1), -EPS_1E9])
        with self.assertRaisesRegex(mod.CertVerifyError, "DUAL_SIGN_VIOLATION"):
            mod.verify_quotient_lp_sparse_q(2, goals, edges, mu, caps, h, [-EPS_1E9], dz)
        with self.assertRaisesRegex(mod.CertVerifyError, "PRIMAL_INFEASIBLE"):
            mod.verify_quotient_lp_sparse_q(2, goals, edges, mu, caps, [EPS_1E9, Fraction(3, 2)], dy, dz)
        with self.assertRaisesRegex(mod.CertVerifyError, "PRIMAL_INFEASIBLE"):
            mod.verify_quotient_lp_sparse_q(2, goals, edges, mu, caps, [Fraction(0, 1), Fraction(3, 2) + EPS_1E9], dy, dz)
        with self.assertRaisesRegex(mod.CertVerifyError, "DUAL_INFEASIBLE"):
            mod.verify_quotient_lp_sparse_q(2, goals, edges, mu, caps, h, [Fraction(2, 1) - EPS_1E9], dz)
        with self.assertRaisesRegex(mod.CertVerifyError, "DUALITY_GAP_NONZERO"):
            mod.verify_quotient_lp_sparse_q(2, goals, edges, mu, caps, h, [Fraction(2, 1) + EPS_1E9], [Fraction(3, 1) + EPS_1E9, Fraction(0, 1)])

        # Exact 1/1 permutation retention gate
        self.assertEqual(mod.verify_retention_gate_q(Fraction(3, 2), Fraction(3, 2)), Fraction(1, 1))
        with self.assertRaisesRegex(mod.CertVerifyError, "RETENTION_NONPOSITIVE_ORIG"):
            mod.verify_retention_gate_q(Fraction(1, 1), Fraction(0, 1))
        with self.assertRaisesRegex(mod.CertVerifyError, "RETENTION_NONPOSITIVE_ORIG"):
            mod.verify_retention_gate_q(Fraction(1, 1), 1)  # type: ignore[arg-type]
        with self.assertRaisesRegex(mod.CertVerifyError, "OBFUSCATION_RETENTION_MISMATCH"):
            mod.verify_retention_gate_q(Fraction(99, 100), Fraction(1, 1))
        with self.assertRaisesRegex(mod.CertVerifyError, "OBFUSCATION_RETENTION_MISMATCH"):
            mod.verify_retention_gate_q(Fraction(101, 100), Fraction(1, 1))

        self.assertEqual(mod.verify_local_subcone_q([Fraction(2, 1), Fraction(2, 1)], [Fraction(3, 1), Fraction(3, 1)], (0, 1), Fraction(2, 1), Fraction(1, 1)), ["2/1", "3/1"])
        with self.assertRaisesRegex(mod.CertVerifyError, "LOCAL_SUBCONE_INFEASIBLE"):
            mod.verify_local_subcone_q([Fraction(2, 1)], [Fraction(3, 1)], (0,), Fraction(2, 1) - EPS_1E9, Fraction(0, 1))
        with self.assertRaisesRegex(mod.CertVerifyError, "LOCAL_SUBCONE_INFEASIBLE"):
            mod.verify_local_subcone_q([Fraction(2, 1)], [Fraction(3, 1)], (0,), Fraction(3, 1) + EPS_1E9, Fraction(0, 1))


class TestCommittedArtifactsAndBenchmarkTamper(unittest.TestCase):
    def test_committed_artifacts_certificate_tamper_and_cli(self) -> None:
        cert_disk = STUDY_DIR.joinpath("exact_farkas_delsarte_certificate.json")
        bench_disk = STUDY_DIR.joinpath("wallclock_benchmark_receipt.json")
        cert = mod.check_certificate_artifact(cert_disk, require_pinned=True)
        self.assertEqual([c["delsarte_exact_bound"] for c in cert["payload"]["family1_delsarte"]["cases"]], ["16/1", "24/1", "32/1", "40/1"])
        self.assertEqual(cert["payload"]["family2_quotient_lp"]["orig_check"]["primal_obj"], "535/4")
        self.assertEqual(cert["payload"]["family3_zero_log_farkas"]["zu_chongzhi_global_farkas"]["b_dot_y"], "-32/113")
        bench = mod.check_benchmark_artifact(bench_disk, require_pinned=True)
        self.assertTrue(bench["payload"]["within_wallclock_budget"])

        # Pin mismatch refusal on committed artifacts
        with patch.object(mod, "PINNED_CERTIFICATE_SHA256", "0" * 64):
            with self.assertRaisesRegex(mod.CertVerifyError, "CERT_PIN_MISMATCH"):
                mod.check_certificate_artifact(cert_disk, require_pinned=True)
        with patch.object(mod, "PINNED_BENCHMARK_SHA256", "0" * 64):
            with self.assertRaisesRegex(mod.CertVerifyError, "BENCH_PIN_MISMATCH"):
                mod.check_benchmark_artifact(bench_disk, require_pinned=True)

        # Cap-binding quotient branch
        qa, qb, qc, qh, qy, qact = mod.synthesize_quotient_lp_exact(
            2, [0], [], [Fraction(1, 1), Fraction(2, 1)], [Fraction(5, 1), Fraction(3, 1)]
        )
        self.assertEqual(mod.verify_lp_primal_dual_q(qa, qb, qc, qh, qy, "max_le", active_rows=qact)["primal_obj"], "6/1")

        with tempfile.TemporaryDirectory() as td:
            cpath = Path(td).joinpath("cert.json")
            buf = io.StringIO()
            with patch("sys.stdout", buf):
                self.assertEqual(mod.main(["--write", str(cpath), "--require-pinned"]), 0)
            self.assertEqual(json.loads(buf.getvalue())["certificate_sha256"], cert["certificate_sha256"])

            buf2 = io.StringIO()
            with patch("sys.stdout", buf2):
                self.assertEqual(mod.main(["--check", str(cpath), "--require-pinned"]), 0)
            self.assertEqual(json.loads(buf2.getvalue())["status"], "PASS_CERT")

            buf3 = io.StringIO()
            with patch("sys.stdout", buf3):
                self.assertEqual(mod.main(["--require-pinned"]), 0)
            self.assertEqual(json.loads(buf3.getvalue())["certificate_sha256"], cert["certificate_sha256"])

            # --require-pinned enforced fail-closed across --write, --check, and stdout default mode
            unwritten = Path(td).joinpath("unwritten_pin.json")
            with patch.object(mod, "PINNED_CERTIFICATE_SHA256", "0" * 64):
                for pin_argv in (
                    ["--write", str(unwritten), "--require-pinned"],
                    ["--check", str(cpath), "--require-pinned"],
                    ["--require-pinned"],
                ):
                    err_pin = io.StringIO()
                    with patch("sys.stderr", err_pin):
                        self.assertEqual(mod.main(pin_argv), 2)
                    self.assertIn("CERT_PIN_MISMATCH", err_pin.getvalue())
            self.assertFalse(unwritten.exists())
            with patch("sys.stdout", io.StringIO()):
                self.assertEqual(mod.main(["--write", str(cpath)]), 0)
            with patch("sys.stdout", io.StringIO()):
                self.assertEqual(mod.main([]), 0)

            # Real subprocess checks covering __main__, symlinked --check, and symlinked --write
            proc_ok = subprocess.run(
                [sys.executable, "-I", "-B", str(STUDY_DIR.joinpath("verify_exact_farkas_delsarte.py")), "--check", str(cert_disk), "--require-pinned"],
                capture_output=True,
                text=True,
                check=False,
            )
            self.assertEqual(proc_ok.returncode, 0, proc_ok.stderr)
            self.assertEqual(json.loads(proc_ok.stdout)["status"], "PASS_CERT")

            sym_cert = Path(td).joinpath("sym_cert.json")
            os.symlink(str(cert_disk), str(sym_cert))
            proc_sym = subprocess.run(
                [sys.executable, "-I", "-B", str(STUDY_DIR.joinpath("verify_exact_farkas_delsarte.py")), "--check", str(sym_cert)],
                capture_output=True,
                text=True,
                check=False,
            )
            self.assertEqual(proc_sym.returncode, 2)
            self.assertIn("SYMLINK_FORBIDDEN", proc_sym.stderr)

            sym_out = Path(td).joinpath("sym_out.json")
            sentinel = Path(td).joinpath("sentinel.txt")
            sentinel.write_text("KEEP", encoding="utf-8")
            os.symlink(str(sentinel), str(sym_out))
            err_sw = io.StringIO()
            with patch("sys.stderr", err_sw):
                self.assertEqual(mod.main(["--write", str(sym_out)]), 2)
            self.assertIn("SYMLINK_FORBIDDEN", err_sw.getvalue())
            self.assertEqual(sentinel.read_text(encoding="utf-8"), "KEEP")

            # IO error on unwritable destination, unread FIFO, and directory exits cleanly with rc == 2
            fifo_out = Path(td).joinpath("out.fifo")
            os.mkfifo(str(fifo_out))
            proc_fifo = subprocess.run(
                [sys.executable, "-I", "-B", str(STUDY_DIR.joinpath("verify_exact_farkas_delsarte.py")), "--write", str(fifo_out)],
                capture_output=True,
                text=True,
                timeout=5,
                check=False,
            )
            self.assertEqual(proc_fifo.returncode, 2)
            self.assertIn("NOT_REGULAR_FILE", proc_fifo.stderr)

            proc_dir = subprocess.run(
                [sys.executable, "-I", "-B", str(STUDY_DIR.joinpath("verify_exact_farkas_delsarte.py")), "--write", td],
                capture_output=True,
                text=True,
                timeout=5,
                check=False,
            )
            self.assertEqual(proc_dir.returncode, 2)
            self.assertIn("NOT_REGULAR_FILE", proc_dir.stderr)

            bad_out = Path(td).joinpath("missing_dir", "cert.json")
            err_io = io.StringIO()
            with patch("sys.stderr", err_io):
                self.assertEqual(mod.main(["--write", str(bad_out)]), 2)
            self.assertIn("FAIL_CLOSED:", err_io.getvalue())

            orig = json.loads(cpath.read_text(encoding="utf-8"))
            tpath = Path(td).joinpath("tamper.json")
            tpath.write_bytes(cpath.read_bytes() + b" ")
            with self.assertRaisesRegex(mod.CertVerifyError, "CERT_RAW_BYTES_MISMATCH"):
                mod.check_certificate_artifact(tpath)

            extra = json.loads(json.dumps(orig))
            extra["bogus_external_sha256"] = "0" * 64
            tpath.write_bytes(mod.formatted_json_bytes(extra))
            with self.assertRaisesRegex(mod.CertVerifyError, "CERT_KEYS_MISMATCH"):
                mod.check_certificate_artifact(tpath)

            # Nested energy string and nested float in certificate JSON rejected
            e_bad = json.loads(json.dumps(orig))
            e_bad["payload"]["family1_delsarte"]["note"] = "1 j/ tok"
            tpath.write_bytes(mod.formatted_json_bytes(e_bad))
            with self.assertRaisesRegex(mod.CertVerifyError, "JSON_ENERGY_CLAIM_VALUE"):
                mod.check_certificate_artifact(tpath)
            tpath.write_text(cpath.read_text(encoding="utf-8").replace('"isqrt_10000": 100', '"isqrt_10000": 100.0', 1), encoding="utf-8")
            with self.assertRaisesRegex(mod.CertVerifyError, "JSON_FORBIDDEN_FLOAT"):
                mod.check_certificate_artifact(tpath)

            for err_code, mutator in (
                ("CERT_SCHEMA_MISMATCH", lambda d: d.__setitem__("schema", "bad")),
                ("CERT_PAYLOAD_NOT_DICT", lambda d: d.__setitem__("payload", [])),
                ("CERT_ENERGY_STATUS_BAD", lambda d: d["payload"].pop("energy_power_status")),
                ("CERT_PAYLOAD_SHA_MISMATCH", lambda d: d.__setitem__("payload_sha256", "0" * 64)),
                ("CERT_SHA_MISMATCH", lambda d: d.__setitem__("certificate_sha256", "0" * 64)),
            ):
                bad = json.loads(json.dumps(orig))
                mutator(bad)
                tpath.write_bytes(mod.formatted_json_bytes(bad))
                with self.assertRaisesRegex(mod.CertVerifyError, err_code):
                    mod.check_certificate_artifact(tpath)

            forged = json.loads(json.dumps(orig))
            forged["payload"]["exact_math_guard_check"]["isqrt_10000"] = 99
            forged["payload_sha256"] = mod.sha256_json(forged["payload"])
            forged["certificate_sha256"] = mod.sha256_json({
                "schema": forged["schema"],
                "payload": forged["payload"],
                "payload_sha256": forged["payload_sha256"],
            })
            tpath.write_bytes(mod.formatted_json_bytes(forged))
            with self.assertRaisesRegex(mod.CertVerifyError, "CERT_LIVE_RECOMPUTE_MISMATCH"):
                mod.check_certificate_artifact(tpath)
            err_buf = io.StringIO()
            with patch("sys.stderr", err_buf):
                self.assertEqual(mod.main(["--check", str(tpath)]), 2)
            self.assertIn("CERT_LIVE_RECOMPUTE_MISMATCH", err_buf.getvalue())

    def test_wallclock_benchmark_cli_and_tamper_guards(self) -> None:
        with self.assertRaisesRegex(mod.CertVerifyError, "BAD_REPEATS"):
            mod.run_wallclock_benchmark(repeats=1)
        with self.assertRaisesRegex(mod.CertVerifyError, "BAD_REPEATS"):
            mod.run_wallclock_benchmark(repeats=True)  # type: ignore[arg-type]

        with tempfile.TemporaryDirectory() as td:
            # Budget enforced BEFORE writing to disk (and exact == budget passes to kill <= -> <)
            over_path = Path(td).joinpath("never_written.json")
            with patch.object(mod, "WALLCLOCK_BUDGET_NS", 0):
                err_b = io.StringIO()
                with patch("sys.stderr", err_b):
                    self.assertEqual(mod.main(["--benchmark", str(over_path), "--repeats", "2"]), 2)
                self.assertIn("BENCH_TIME_OVER_BUDGET", err_b.getvalue())
                self.assertFalse(over_path.exists())
            with patch.object(mod.time, "perf_counter_ns", return_value=1), patch.object(mod, "WALLCLOCK_BUDGET_NS", 15):
                exact_bench = mod.run_wallclock_benchmark(repeats=2)
                self.assertEqual(exact_bench["payload"]["total_benchmark_ns"], 15)

            bpath = Path(td).joinpath("bench.json")
            err_bpin = io.StringIO()
            with patch("sys.stderr", err_bpin):
                self.assertEqual(mod.main(["--benchmark", str(bpath), "--repeats", "2", "--require-pinned"]), 2)
            self.assertIn("BENCH_LIVE_CANNOT_REQUIRE_PINNED", err_bpin.getvalue())
            self.assertFalse(bpath.exists())

            buf = io.StringIO()
            with patch("sys.stdout", buf):
                self.assertEqual(mod.main(["--benchmark", str(bpath), "--repeats", "2"]), 0)
            out = json.loads(buf.getvalue())
            self.assertEqual(out["status"], "WROTE_BENCH")

            buf2 = io.StringIO()
            with patch("sys.stdout", buf2):
                self.assertEqual(mod.main(["--check-bench", str(bpath)]), 0)
            self.assertEqual(json.loads(buf2.getvalue())["benchmark_sha256"], out["benchmark_sha256"])
            err_cbpin = io.StringIO()
            with patch("sys.stderr", err_cbpin):
                self.assertEqual(mod.main(["--check-bench", str(bpath), "--require-pinned"]), 2)
            self.assertIn("BENCH_PIN_MISMATCH", err_cbpin.getvalue())

            orig = json.loads(bpath.read_text(encoding="utf-8"))

            def _resign(d: dict) -> dict:
                d["payload_sha256"] = mod.sha256_json(d["payload"])
                d["benchmark_sha256"] = mod.sha256_json({
                    "schema": d["schema"],
                    "payload": d["payload"],
                    "payload_sha256": d["payload_sha256"],
                })
                return d

            tpath = Path(td).joinpath("bad_bench.json")
            tpath.write_bytes(bpath.read_bytes() + b" ")
            with self.assertRaisesRegex(mod.CertVerifyError, "BENCH_RAW_BYTES_MISMATCH"):
                mod.check_benchmark_artifact(tpath)

            # Nested energy string and nested float in benchmark JSON rejected
            eb = json.loads(json.dumps(orig))
            eb["payload"]["quotient_lp_n48_comparison"]["note"] = "wa\u0000tt"
            tpath.write_bytes(mod.formatted_json_bytes(eb))
            with self.assertRaisesRegex(mod.CertVerifyError, "JSON_ENERGY_CLAIM_VALUE"):
                mod.check_benchmark_artifact(tpath)
            tpath.write_text(bpath.read_text(encoding="utf-8").replace('"repeats": 2', '"repeats": 2.0', 1), encoding="utf-8")
            with self.assertRaisesRegex(mod.CertVerifyError, "JSON_FORBIDDEN_FLOAT"):
                mod.check_benchmark_artifact(tpath)

            bench_tampers = [
                ("BENCH_KEYS_MISMATCH", lambda d: d.__setitem__("extra", 1), False),
                ("BENCH_SCHEMA_MISMATCH", lambda d: d.__setitem__("schema", "bad"), False),
                ("BENCH_PAYLOAD_NOT_DICT", lambda d: d.__setitem__("payload", []), False),
                ("BENCH_PAYLOAD_KEYS_MISMATCH", lambda d: d["payload"].__setitem__("rogue_nested_note", "x"), True),
                ("BENCH_PAYLOAD_SCHEMA_MISMATCH", lambda d: d["payload"].__setitem__("schema", "bad"), True),
                ("BENCH_ENERGY_STATUS_BAD", lambda d: d["payload"].__setitem__("energy_power_status", "other"), False),
                ("BENCH_CLOCK_SOURCE_BAD", lambda d: d["payload"].__setitem__("clock_source", "time.time"), True),
                ("BENCH_BUDGET_CONST_MISMATCH", lambda d: d["payload"].__setitem__("wallclock_budget_ns", 1), True),
                ("BENCH_PAYLOAD_SHA_MISMATCH", lambda d: d.__setitem__("payload_sha256", "0" * 64), False),
                ("BENCH_SHA_MISMATCH", lambda d: d.__setitem__("benchmark_sha256", "0" * 64), False),
                ("BENCH_REPEATS_BAD", lambda d: d["payload"].__setitem__("repeats", 1), True),
                ("BENCH_REPEATS_BAD", lambda d: d["payload"].__setitem__("repeats", True), True),
                ("BENCH_TIME_BAD", lambda d: d["payload"].__setitem__("total_benchmark_ns", 0), True),
                ("BENCH_TIME_BAD", lambda d: d["payload"].__setitem__("total_benchmark_ns", True), True),
                ("BENCH_TIME_OVER_BUDGET", lambda d: d["payload"].__setitem__("total_benchmark_ns", mod.WALLCLOCK_BUDGET_NS + 1), True),
                ("BENCH_BUDGET_FLAG_FALSE", lambda d: d["payload"].__setitem__("within_wallclock_budget", False), True),
                ("BENCH_MEASURED_SUM_BAD", lambda d: d["payload"].__setitem__("measured_components_sum_ns", 0), True),
                ("BENCH_OVERHEAD_BAD", lambda d: d["payload"].__setitem__("unmeasured_setup_and_verify_ns", -1), True),
                ("BENCH_OVERHEAD_BAD", lambda d: d["payload"].__setitem__("unmeasured_setup_and_verify_ns", True), True),
                ("BENCH_SCALING_BAD", lambda d: d["payload"].__setitem__("linear_basis_scaling", []), True),
                ("BENCH_SCALING_ROW_BAD", lambda d: d["payload"]["linear_basis_scaling"].__setitem__(0, "bad"), True),
                ("BENCH_SCALING_ROW_KEYS_MISMATCH", lambda d: d["payload"]["linear_basis_scaling"][0].__setitem__("rogue", 1), True),
                ("BENCH_SCALING_DIM_MISMATCH", lambda d: d["payload"]["linear_basis_scaling"][0].__setitem__("dim", 9999), True),
                ("BENCH_SCALING_DIM_MISMATCH", lambda d: d["payload"]["linear_basis_scaling"][0].__setitem__("dim", True), True),
                ("BENCH_SCALING_REPEATS_MISMATCH", lambda d: d["payload"]["linear_basis_scaling"][0].__setitem__("repeats", 99), True),
                ("BENCH_SCALING_REPEATS_MISMATCH", lambda d: d["payload"]["linear_basis_scaling"][0].__setitem__("repeats", True), True),
                ("BENCH_SCALING_NS_BAD", lambda d: d["payload"]["linear_basis_scaling"][0].__setitem__("fangcheng_total_ns", 0), True),
                ("BENCH_RATIO_MISMATCH", lambda d: d["payload"]["linear_basis_scaling"][0].__setitem__("fangcheng_vs_naive_speedup_q", "999/1"), True),
                ("BENCH_RATIO_MISMATCH", lambda d: d["payload"]["linear_basis_scaling"][0].__setitem__("verify_vs_naive_speedup_q", "999/1"), True),
                ("BENCH_RATIO_MISMATCH", lambda d: d["payload"]["linear_basis_scaling"][0].__setitem__("verify_vs_fangcheng_speedup_q", "999/1"), True),
                ("BENCH_Q48_MISSING", lambda d: d["payload"].__setitem__("quotient_lp_n48_comparison", []), True),
                ("BENCH_Q48_KEYS_MISMATCH", lambda d: d["payload"]["quotient_lp_n48_comparison"].__setitem__("rogue", 1), True),
                ("BENCH_Q48_META_MISMATCH", lambda d: d["payload"]["quotient_lp_n48_comparison"].__setitem__("num_vertices", 99), True),
                ("BENCH_Q48_META_MISMATCH", lambda d: d["payload"]["quotient_lp_n48_comparison"].__setitem__("num_vertices", True), True),
                ("BENCH_Q48_META_MISMATCH", lambda d: d["payload"]["quotient_lp_n48_comparison"].__setitem__("num_edges", 99), True),
                ("BENCH_Q48_META_MISMATCH", lambda d: d["payload"]["quotient_lp_n48_comparison"].__setitem__("num_edges", True), True),
                ("BENCH_Q48_META_MISMATCH", lambda d: d["payload"]["quotient_lp_n48_comparison"].__setitem__("repeats", 99), True),
                ("BENCH_Q48_META_MISMATCH", lambda d: d["payload"]["quotient_lp_n48_comparison"].__setitem__("repeats", True), True),
                ("BENCH_Q48_NS_BAD", lambda d: d["payload"]["quotient_lp_n48_comparison"].__setitem__("sparse_farkas_verify_total_ns", 0), True),
                ("BENCH_Q48_RATIO_MISMATCH", lambda d: d["payload"]["quotient_lp_n48_comparison"].__setitem__("fangcheng_vs_naive_speedup_q", "999/1"), True),
                ("BENCH_Q48_RATIO_MISMATCH", lambda d: d["payload"]["quotient_lp_n48_comparison"].__setitem__("sparse_verify_vs_naive_speedup_q", "999/1"), True),
                ("BENCH_Q48_RATIO_MISMATCH", lambda d: d["payload"]["quotient_lp_n48_comparison"].__setitem__("sparse_verify_vs_fangcheng_speedup_q", "999/1"), True),
                ("BENCH_Q48_RATIO_MISMATCH", lambda d: d["payload"]["quotient_lp_n48_comparison"].__setitem__("sparse_verify_vs_dense_verify_speedup_q", "999/1"), True),
                ("BENCH_CTRL_MISSING", lambda d: d["payload"].__setitem__("tractable_small_control_slowdown", []), True),
                ("BENCH_CTRL_KEYS_MISMATCH", lambda d: d["payload"]["tractable_small_control_slowdown"].__setitem__("rogue", 1), True),
                ("BENCH_CTRL_META_MISMATCH", lambda d: d["payload"]["tractable_small_control_slowdown"].__setitem__("num_vertices", 99), True),
                ("BENCH_CTRL_META_MISMATCH", lambda d: d["payload"]["tractable_small_control_slowdown"].__setitem__("num_vertices", True), True),
                ("BENCH_CTRL_META_MISMATCH", lambda d: d["payload"]["tractable_small_control_slowdown"].__setitem__("num_edges", 99), True),
                ("BENCH_CTRL_META_MISMATCH", lambda d: d["payload"]["tractable_small_control_slowdown"].__setitem__("num_edges", True), True),
                ("BENCH_CTRL_META_MISMATCH", lambda d: d["payload"]["tractable_small_control_slowdown"].__setitem__("repeats", 99), True),
                ("BENCH_CTRL_META_MISMATCH", lambda d: d["payload"]["tractable_small_control_slowdown"].__setitem__("repeats", True), True),
                ("BENCH_CTRL_NS_BAD", lambda d: d["payload"]["tractable_small_control_slowdown"].__setitem__("direct_spfa_eval_total_ns", 0), True),
                ("BENCH_CTRL_RATIO_MISMATCH", lambda d: d["payload"]["tractable_small_control_slowdown"].__setitem__("certified_over_direct_slowdown_q", "999/1"), True),
                ("BENCH_CTRL_FLAG_MISMATCH", lambda d: d["payload"]["tractable_small_control_slowdown"].__setitem__("slowdown_observed", False), True),
                ("BENCH_COMPONENT_SUM_MISMATCH", lambda d: d["payload"].__setitem__("measured_components_sum_ns", d["payload"]["measured_components_sum_ns"] + 1), True),
                ("BENCH_TOTAL_ACCOUNTING_MISMATCH", lambda d: d["payload"].__setitem__("total_benchmark_ns", d["payload"]["total_benchmark_ns"] + 1), True),
            ]
            for err_code, mutator, resign in bench_tampers:
                bad = json.loads(json.dumps(orig))
                mutator(bad)
                if resign:
                    _resign(bad)
                tpath.write_bytes(mod.formatted_json_bytes(bad))
                with self.subTest(err_code=err_code):
                    if err_code == "BENCH_ENERGY_STATUS_BAD":
                        with self.assertRaisesRegex(mod.CertVerifyError, "JSON_ALLOWLIST_SMUGGLE"):
                            mod.check_benchmark_artifact(tpath)
                    else:
                        with self.assertRaisesRegex(mod.CertVerifyError, err_code):
                            mod.check_benchmark_artifact(tpath)

            # Exact budget & zero-overhead boundary checks (kills <= -> < and >= -> >)
            at_limit = json.loads(json.dumps(orig))
            at_limit["payload"]["unmeasured_setup_and_verify_ns"] = mod.WALLCLOCK_BUDGET_NS - at_limit["payload"]["measured_components_sum_ns"]
            at_limit["payload"]["total_benchmark_ns"] = mod.WALLCLOCK_BUDGET_NS
            _resign(at_limit)
            tpath.write_bytes(mod.formatted_json_bytes(at_limit))
            mod.check_benchmark_artifact(tpath)

            zero_ov = json.loads(json.dumps(orig))
            zero_ov["payload"]["unmeasured_setup_and_verify_ns"] = 0
            zero_ov["payload"]["total_benchmark_ns"] = zero_ov["payload"]["measured_components_sum_ns"]
            _resign(zero_ov)
            tpath.write_bytes(mod.formatted_json_bytes(zero_ov))
            mod.check_benchmark_artifact(tpath)


if __name__ == "__main__":
    unittest.main()
