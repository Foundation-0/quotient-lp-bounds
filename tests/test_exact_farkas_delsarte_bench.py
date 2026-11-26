"""Pure-stdlib integration verification for the exact-Q Farkas/Delsarte certificate study.

Discovered automatically by unittest (`python3 -O -B -m unittest discover -s tests -p 'test_*.py' -v`).
Zero third-party dependencies, zero bare asserts, runs cleanly under -I -B, -I -O -B, and -I -B -W error.
"""
from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys
import unittest

ROOT = Path(__file__).resolve().parent.parent
STUDY_DIR = ROOT.joinpath("studies", "exact_farkas_delsarte_bench")

PINNED_CERTIFICATE_SHA256 = "29b99332981c2ad709a7d778e42b60cc82c1f73cc8697788239e4db129335673"
PINNED_BENCHMARK_SHA256 = "ddb8d4f75ecd3eda8cffb4329a8b0a778a7a6985dd3094e98692dab2cfcdc6f9"


def _req(cond: bool, msg: str) -> None:
    if not cond:
        raise AssertionError(msg)


def _run_py(cwd: Path, args: list[str]) -> subprocess.CompletedProcess[str]:
    env = dict(os.environ)
    env["CUDA_VISIBLE_DEVICES"] = ""
    env["OPENBLAS_NUM_THREADS"] = "1"
    env["OMP_NUM_THREADS"] = "1"
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    env["PYTHONHASHSEED"] = "0"
    flags = ["-I", "-O", "-B"] if not __debug__ else ["-I", "-B"]
    if any(opt == "error" or opt.startswith("error:") for opt in sys.warnoptions):
        flags.extend(["-W", "error"])
    proc = subprocess.run(
        [sys.executable, *flags, *args],
        cwd=str(cwd),
        env=env,
        capture_output=True,
        text=True,
        timeout=120,
        check=False,
    )
    _req(
        proc.returncode == 0,
        f"Command {args!r} failed in {cwd.name} (rc={proc.returncode}):\n"
        f"STDOUT:\n{proc.stdout[-800:]}\nSTDERR:\n{proc.stderr[-800:]}",
    )
    return proc


class TestExactFarkasDelsarteBench(unittest.TestCase):
    def test_01_certificate_and_benchmark_receipt_check(self) -> None:
        p_cert = _run_py(
            STUDY_DIR,
            ["verify_exact_farkas_delsarte.py", "--check", "exact_farkas_delsarte_certificate.json", "--require-pinned"],
        )
        d_cert = json.loads(p_cert.stdout)
        _req(
            d_cert.get("status") == "PASS_CERT"
            and d_cert.get("certificate_sha256") == PINNED_CERTIFICATE_SHA256,
            f"Certificate check mismatch: {d_cert}",
        )

        p_bench = _run_py(
            STUDY_DIR,
            ["verify_exact_farkas_delsarte.py", "--check-bench", "wallclock_benchmark_receipt.json", "--require-pinned"],
        )
        d_bench = json.loads(p_bench.stdout)
        _req(
            d_bench.get("status") == "PASS_BENCH"
            and d_bench.get("benchmark_sha256") == PINNED_BENCHMARK_SHA256,
            f"Benchmark receipt check mismatch: {d_bench}",
        )

    def test_02_r5_adversarial_and_ast_purity_suite(self) -> None:
        _run_py(STUDY_DIR, ["test_exact_farkas_delsarte_r5.py"])


if __name__ == "__main__":
    unittest.main()
