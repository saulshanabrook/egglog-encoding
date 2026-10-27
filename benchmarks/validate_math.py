"""Validate the frozen Math12 boundary in bounded, sequential test processes.

Build the release test executable with ``cargo test --release -p
 egg-math-benchmark --no-run --message-format=json`` and pass its executable
path here. Each ignored Rust test case installs the existing native 16 GiB
limit before constructing a graph. This diagnostic collects no benchmark rows.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import time
from pathlib import Path
from typing import Any

from benchmarking.engines import MATH12_CHECK_LEFT, MATH12_CHECK_RIGHT, MATH12_WORKLOAD_PATH, MATH12_WORKLOAD_SHA256
from native_memory import NATIVE_LIMIT_BYTES

ROOT = Path(__file__).resolve().parents[1]
CASES = (
    ("egg", "off", 11),
    ("egg", "off", 12),
    ("egglog", "off", 11),
    ("egglog", "off", 12),
    ("egg", "check", 11),
    ("egglog", "check", 11),
    ("egg", "check", 12),
    ("egglog", "check", 12),
)


def validate(test_binary: Path, output: Path) -> dict[str, Any]:
    """Preserve evidence and continue independent cases after a cap or timeout."""
    output.mkdir(parents=True, exist_ok=True)
    if "sha256:" + hashlib.sha256((ROOT / MATH12_WORKLOAD_PATH).read_bytes()).hexdigest() != MATH12_WORKLOAD_SHA256:
        raise ValueError("Math12 fixture bytes differ from frozen preparation input")
    left, right = MATH12_CHECK_LEFT, MATH12_CHECK_RIGHT
    summary: dict[str, Any] = {
        "fixture": str(MATH12_WORKLOAD_PATH),
        "fixture_sha256": MATH12_WORKLOAD_SHA256,
        "test_binary": str(test_binary),
        "test_binary_sha256": "sha256:" + hashlib.sha256(test_binary.read_bytes()).hexdigest(),
        "native_limit_bytes": NATIVE_LIMIT_BYTES,
        "timeout_sec": 300,
        "cases": [],
        "complete": False,
    }
    expected_sizes: dict[int, tuple[dict[str, int], int]] = {}
    for engine, proof, iterations in CASES:
        name = f"{engine}-{proof}-{iterations}"
        command = [str(test_binary), "--exact", "tests::bounded_math12_case", "--ignored", "--nocapture"]
        environment = os.environ | {
            "RUST_TEST_THREADS": "1",
            "MIMALLOC_ARENA_RESERVE": "0",
            "MIMALLOC_DISALLOW_ARENA_ALLOC": "1",
            "MIMALLOC_RESERVE_OS_MEMORY": "0",
            "MIMALLOC_RESERVE_HUGE_OS_PAGES": "0",
            "MATH_BOUNDARY_ENGINE": engine,
            "MATH_BOUNDARY_PROOF": proof,
            "MATH_BOUNDARY_ITERATIONS": str(iterations),
            "MATH_BOUNDARY_LEFT": left,
            "MATH_BOUNDARY_RIGHT": right,
        }
        case: dict[str, Any] = {
            "engine": engine,
            "proof": proof,
            "iterations": iterations,
            "command": command,
            "stdout": name + ".stdout",
            "stderr": name + ".stderr",
        }
        start = time.monotonic()
        with (output / case["stdout"]).open("w") as stdout, (output / case["stderr"]).open("w") as stderr:
            try:
                process = subprocess.run(command, cwd=ROOT, env=environment, stdout=stdout, stderr=stderr, timeout=300)
                case["exit_code"] = process.returncode
                case["status"] = {
                    0: "success",
                    86: "native-allocation-exhausted",
                    87: "native-limit-setup-failed",
                }.get(process.returncode, "failed")
            except subprocess.TimeoutExpired:
                case["status"] = "timed-out"
        case["diagnostic_elapsed_sec"] = time.monotonic() - start
        if case["status"] == "success":
            lines = (output / case["stdout"]).read_text().splitlines()
            records = [
                json.loads(line.split("MATH_BOUNDARY_RESULT ", 1)[1])
                for line in lines
                if "MATH_BOUNDARY_RESULT " in line
            ]
            if len(records) != 1:
                case["status"] = "missing-logical-result"
            else:
                result = records[0]
                case["result"] = result
                sizes = (result["constructors"], result["classes"])
                if expected_sizes.setdefault(iterations, sizes) != sizes:
                    case["status"] = "logical-graph-parity-mismatch"
        summary["cases"].append(case)
        summary["all_cases_attempted"] = len(summary["cases"]) == len(CASES)
        summary["complete"] = summary["all_cases_attempted"] and all(
            row["status"] == "success" for row in summary["cases"]
        )
        failures = [row["status"] for row in summary["cases"] if row["status"] != "success"]
        summary["status"] = "success" if summary["complete"] else failures[0] if failures else "in-progress"
        (output / "validation.json").write_text(json.dumps(summary, indent=2) + "\n")
        print(f"{name}: {case['status']}", flush=True)
        if case["status"] not in {"success", "native-allocation-exhausted", "timed-out"}:
            break
    return summary


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--test-binary", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    summary = validate(args.test_binary.resolve(), args.output.resolve())
    raise SystemExit(0 if summary["complete"] else 1)


if __name__ == "__main__":
    main()
