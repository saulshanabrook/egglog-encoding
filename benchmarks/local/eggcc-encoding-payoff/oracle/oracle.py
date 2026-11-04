#!/usr/bin/env python3
"""Freeze independently computed expectations; never invoke or import EggCC."""

import argparse
import datetime
import hashlib
import io
import json
import os
from pathlib import Path
import random
import sys
import time
import unittest


WIDTH = 64
MODULUS = 2**WIDTH
MIN = -(2**63)
MAX = 2**63 - 1
RANDOM_SEED = 0xE66CCADD
RANDOM_PAIRS = 4096
MISSING = object()

PROGRAMS = {
    "add-positive": """@main(x: int) {
  zero: int = const 0;
  one: int = const 1;
  positive: bool = lt zero x;
  br positive .positive .done;
.positive:
  shifted: int = add x one;
  answer: bool = lt shifted zero;
  print answer;
.done:
  ret;
}
""",
    "sub-negative": """@main(x: int) {
  zero: int = const 0;
  one: int = const 1;
  negative: bool = lt x zero;
  br negative .negative .done;
.negative:
  shifted: int = sub x one;
  answer: bool = lt zero shifted;
  print answer;
.done:
  ret;
}
""",
}

# Predetermined expectations, independent of either arithmetic implementation.
CASES = [
    ("add-max", "add-positive", MAX, True, MIN, "true\n"),
    ("add-max-minus-one", "add-positive", MAX - 1, True, MAX, "false\n"),
    ("add-two", "add-positive", 2, True, 3, "false\n"),
    ("add-one", "add-positive", 1, True, 2, "false\n"),
    ("add-zero-skipped", "add-positive", 0, False, None, ""),
    ("add-negative-one-skipped", "add-positive", -1, False, None, ""),
    ("sub-min", "sub-negative", MIN, True, MAX, "true\n"),
    ("sub-min-plus-one", "sub-negative", MIN + 1, True, MIN, "false\n"),
    ("sub-negative-two", "sub-negative", -2, True, -3, "false\n"),
    ("sub-negative-one", "sub-negative", -1, True, -2, "false\n"),
    ("sub-zero-skipped", "sub-negative", 0, False, None, ""),
    ("sub-one-skipped", "sub-negative", 1, False, None, ""),
]


def signed_residue(exact, width=WIDTH):
    """Euclidean integer reduction followed by signed two's-complement decoding."""
    modulus = 2**width
    _, residue = divmod(exact, modulus)
    return residue if residue < 2 ** (width - 1) else residue - modulus


def bit_model(left, right, subtract=False, width=WIDTH):
    """Independent finite full-adder; subtraction complements bits and adds one."""
    modulus = 2**width
    left_bits = left if left >= 0 else left + modulus
    right_bits = right if right >= 0 else right + modulus
    carry = int(subtract)
    encoded = 0
    place = 1
    for _ in range(width):
        left_bits, a = divmod(left_bits, 2)
        right_bits, b = divmod(right_bits, 2)
        if subtract:
            b = 1 - b
        carry, bit = divmod(a + b + carry, 2)
        encoded += bit * place
        place *= 2
    return encoded if encoded < 2 ** (width - 1) else encoded - modulus


def evaluate(program, value):
    if not MIN <= value <= MAX:
        raise ValueError("argument is outside signed i64")
    if program == "add-positive":
        reached = 0 < value
        shifted = signed_residue(value + 1) if reached else None
        answer = shifted < 0 if reached else None
    elif program == "sub-negative":
        reached = value < 0
        shifted = signed_residue(value - 1) if reached else None
        answer = 0 < shifted if reached else None
    else:
        raise ValueError("unsupported oracle program")
    printed = [] if answer is None else ["true" if answer else "false"]
    return {
        "selected_inner_point_present": reached,
        "shifted_i64": None if shifted is None else str(shifted),
        "answer_bool": answer,
        "expected_prints": printed,
        "expected_stdout": "" if not printed else printed[0] + "\n",
    }


def classify_output(expected, observed=MISSING):
    """Require present textual output, including the valid present empty string."""
    if observed is MISSING or observed is None:
        return "missing-output"
    if not isinstance(observed, str):
        return "invalid-output-type"
    return "match" if observed == expected else "mismatch"


class OracleChecks(unittest.TestCase):
    def test_predetermined_source_cases(self):
        for name, program, value, reached, shifted, stdout in CASES:
            with self.subTest(case=name):
                observed = evaluate(program, value)
                self.assertEqual(observed["selected_inner_point_present"], reached)
                self.assertEqual(observed["shifted_i64"], None if shifted is None else str(shifted))
                self.assertEqual(observed["expected_stdout"], stdout)
                self.assertEqual(observed["expected_prints"], stdout.splitlines())

    def test_exhaustive_eight_bit_arithmetic(self):
        for left in range(-128, 128):
            for right in range(-128, 128):
                self.assertEqual(signed_residue(left + right, 8), bit_model(left, right, width=8))
                self.assertEqual(signed_residue(left - right, 8), bit_model(left, right, True, width=8))

    def test_i64_boundary_arithmetic(self):
        values = [MIN, MIN + 1, MIN + 2, -2, -1, 0, 1, 2, MAX - 2, MAX - 1, MAX]
        for left in values:
            for right in values:
                self.assertEqual(signed_residue(left + right), bit_model(left, right))
                self.assertEqual(signed_residue(left - right), bit_model(left, right, True))
        self.assertEqual(signed_residue(MAX + 1), MIN)
        self.assertEqual(signed_residue(MIN - 1), MAX)
        self.assertEqual(signed_residue(MAX + MAX), -2)
        self.assertEqual(signed_residue(MIN + MIN), 0)
        self.assertEqual(signed_residue(MIN - MAX), 1)

    def test_fixed_seed_i64_properties(self):
        rng = random.Random(RANDOM_SEED)
        for _ in range(RANDOM_PAIRS):
            left = rng.randrange(MIN, MAX + 1)
            right = rng.randrange(MIN, MAX + 1)
            total = signed_residue(left + right)
            difference = signed_residue(left - right)
            self.assertEqual(total, bit_model(left, right))
            self.assertEqual(difference, bit_model(left, right, True))
            self.assertEqual(signed_residue(total - right), left)
            self.assertEqual(signed_residue(difference + right), left)
            self.assertGreaterEqual(total, MIN)
            self.assertLessEqual(total, MAX)
            self.assertEqual(signed_residue(left + right + 7 * MODULUS), total)

    def test_skipped_empty_is_not_missing(self):
        self.assertEqual(classify_output("", ""), "match")
        self.assertEqual(classify_output(""), "missing-output")
        self.assertEqual(classify_output("", None), "missing-output")
        self.assertEqual(classify_output("", False), "invalid-output-type")
        self.assertEqual(classify_output("", "\n"), "mismatch")
        self.assertEqual(classify_output("true\n", "false\n"), "mismatch")
        self.assertEqual(classify_output("true\n", "true\n"), "match")

    def test_interval_claim_counterexamples(self):
        self.assertGreater(MAX, 0)
        self.assertLess(signed_residue(MAX + 1), 2)
        self.assertEqual(1 + 1, 2)  # The endpoint calculation itself does not overflow.
        self.assertLess(MIN, 0)
        self.assertGreater(signed_residue(MIN - 1), -2)
        self.assertEqual(-1 - 1, -2)

    def test_unsupported_or_out_of_domain_is_not_output(self):
        for program, value in [("unknown", 1), ("add-positive", MAX + 1), ("sub-negative", MIN - 1)]:
            with self.assertRaises(ValueError):
                evaluate(program, value)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output_dir", type=Path, help="new directory; existing evidence is never overwritten")
    args = parser.parse_args()
    started = datetime.datetime.now(datetime.timezone.utc).isoformat()
    timer = time.perf_counter()
    directory = args.output_dir.resolve()
    directory.mkdir(parents=True, exist_ok=False)
    fixtures = directory / "fixtures"
    fixtures.mkdir()
    rows = []
    for name, program, value, _, _, _ in CASES:
        body = f"# ARGS: {value}\n" + PROGRAMS[program]
        fixture = fixtures / f"{name}.bril"
        fixture.write_text(body, encoding="utf-8")
        rows.append({
            "case": name,
            "program": program,
            "input_i64": str(value),
            "fixture": f"fixtures/{fixture.name}",
            "fixture_sha256": hashlib.sha256(fixture.read_bytes()).hexdigest(),
            **evaluate(program, value),
        })
    matrix = {
        "schema": "eggcc-payoff-exact-oracle-v1",
        "semantic_domain": "signed i64; exact integer Add/Sub reduced modulo 2^64; signed LessThan",
        "status": "independent-expected-values-not-compiler-results",
        "integers": "decimal strings preserve all 64 bits in JSON readers",
        "fixtures_parser_or_native_validated": False,
        "source_object": "a0bbec127f83249074a46af3fd6f6126c90fe0fb",
        "interpreter_source_sha256": "dd991459c2baa77f52ba03a0533147c4b134a2da0ed343f105cb049e415f0491",
        "source_lines": "dag_in_context/src/interpreter.rs:239-244",
        "rows": rows,
    }
    (directory / "expected-matrix.json").write_text(json.dumps(matrix, indent=2, sort_keys=True) + "\n")
    log = io.StringIO()
    result = unittest.TextTestRunner(stream=log, verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(OracleChecks))
    (directory / "tests.stderr").write_text(log.getvalue())
    sys.stderr.write(log.getvalue())
    script = Path(__file__).resolve()
    receipt = {
        "status": "passed" if result.wasSuccessful() else "failed",
        "started_utc": started,
        "finished_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "elapsed_seconds": time.perf_counter() - timer,
        "pid": os.getpid(),
        "cwd": str(Path.cwd()),
        "argv": sys.orig_argv,
        "python_executable": sys.executable,
        "python_version": sys.version,
        "script": str(script),
        "script_sha256": hashlib.sha256(script.read_bytes()).hexdigest(),
        "matrix_sha256": hashlib.sha256((directory / "expected-matrix.json").read_bytes()).hexdigest(),
        "tests_run": result.testsRun,
        "test_failures": len(result.failures),
        "test_errors": len(result.errors),
        "test_skips": len(result.skipped),
        "golden_case_rows": len(rows),
        "reached_print_rows": sum(row["selected_inner_point_present"] for row in rows),
        "skipped_present_empty_rows": sum(row["expected_stdout"] == "" for row in rows),
        "exhaustive_eight_bit_operation_comparisons": 2 * 256**2,
        "i64_boundary_operation_comparisons": 2 * 11**2,
        "fixed_seed": RANDOM_SEED,
        "random_i64_pairs": RANDOM_PAIRS,
        "random_i64_operation_comparisons": 2 * RANDOM_PAIRS,
        "compiler_invocations": 0,
        "native_invocations": 0,
        "project_imports": 0,
    }
    (directory / "results.json").write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    stdout = f"{receipt['status']}: {result.testsRun} tests; {len(rows)} expected cases; no compiler invocation\n"
    (directory / "stdout.txt").write_text(stdout)
    files = sorted(path for path in directory.rglob("*") if path.is_file())
    manifest = {str(path.relative_to(directory)): hashlib.sha256(path.read_bytes()).hexdigest() for path in files}
    (directory / "manifest.json").write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    sys.stdout.write(stdout)
    return 0 if result.wasSuccessful() else 1


if __name__ == "__main__":
    raise SystemExit(main())
