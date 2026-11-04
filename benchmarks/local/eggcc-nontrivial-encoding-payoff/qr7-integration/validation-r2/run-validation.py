#!/usr/bin/env python3
"""Capture the bounded QR7 r2 source validation commands."""

from __future__ import annotations

import hashlib
import json
import os
import subprocess
import sys
import time
from datetime import UTC, datetime
from pathlib import Path

ROOT = Path("/private/tmp/eggcc-qr7-candidate-nits-r2")
DAG = ROOT / "dag_in_context"
HERE = Path(__file__).resolve().parent
COMMANDS = HERE / "commands"
TARGET = Path("/private/tmp/eggcc-qr7-candidate-nits-r2-target")
TIMEOUT_S = 1800


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def run(name: str, argv: list[str], cwd: Path) -> dict[str, object]:
    """Run one validation command and retain its complete streams and provenance."""
    output = COMMANDS / name
    if output.exists():
        raise RuntimeError(f"refusing to overwrite {output}")
    output.mkdir(parents=True)
    environment = dict(os.environ)
    for key in (
        "EGGLOG_BENCH_MEMORY_GUARD",
        "INSTA_UPDATE",
        "INSTA_FORCE_PASS",
        "CARGO_TARGET_DIR",
    ):
        environment.pop(key, None)
    environment.update(
        {
            "EGGCC_ROOT": str(ROOT),
            "RUSTUP_TOOLCHAIN": "1.91.0",
            "CARGO_BUILD_JOBS": "4",
            "RUST_TEST_THREADS": "4",
            "RAYON_NUM_THREADS": "1",
            "LLVM_SYS_180_PREFIX": "/opt/homebrew/opt/llvm@18",
            "LIBRARY_PATH": "/opt/homebrew/lib",
            "CARGO_TARGET_DIR": str(TARGET),
            "PYTHONDONTWRITEBYTECODE": "1",
            "PATH": "/opt/homebrew/opt/llvm@18/bin:" + environment["PATH"],
        }
    )
    executable = Path(subprocess.check_output(["which", argv[0]], env=environment).decode().strip())
    print(f"START {name}: {' '.join(argv)}", flush=True)
    started = datetime.now(UTC)
    monotonic_started = time.monotonic()
    try:
        completed = subprocess.run(
            argv,
            cwd=cwd,
            env=environment,
            capture_output=True,
            timeout=TIMEOUT_S,
            check=False,
        )
        timed_out = False
    except subprocess.TimeoutExpired as error:
        completed = subprocess.CompletedProcess(
            argv,
            124,
            stdout=error.stdout or b"",
            stderr=error.stderr or b"",
        )
        timed_out = True
    elapsed = time.monotonic() - monotonic_started
    finished = datetime.now(UTC)
    (output / "stdout").write_bytes(completed.stdout)
    (output / "stderr").write_bytes(completed.stderr)
    receipt: dict[str, object] = {
        "argv": argv,
        "cwd": str(cwd),
        "started_utc": started.isoformat().replace("+00:00", "Z"),
        "finished_utc": finished.isoformat().replace("+00:00", "Z"),
        "timeout_s": TIMEOUT_S,
        "exit_code": completed.returncode,
        "timed_out": timed_out,
        "elapsed_s_diagnostic": elapsed,
        "diagnostic_elapsed_is_performance_evidence": False,
        "environment": {
            key: environment[key]
            for key in (
                "EGGCC_ROOT",
                "RUSTUP_TOOLCHAIN",
                "CARGO_BUILD_JOBS",
                "RUST_TEST_THREADS",
                "RAYON_NUM_THREADS",
                "LLVM_SYS_180_PREFIX",
                "LIBRARY_PATH",
                "CARGO_TARGET_DIR",
                "PYTHONDONTWRITEBYTECODE",
            )
        },
        "absent_environment": [
            "EGGLOG_BENCH_MEMORY_GUARD",
            "INSTA_UPDATE",
            "INSTA_FORCE_PASS",
        ],
        "raytracing_requested": False,
        "executable": str(executable),
        "executable_sha256": sha256(executable.read_bytes()),
        "stdout_sha256": sha256(completed.stdout),
        "stderr_sha256": sha256(completed.stderr),
    }
    (output / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(
        f"END {name}: exit={completed.returncode} elapsed={elapsed:.1f}s",
        flush=True,
    )
    return receipt


def main() -> int:
    if COMMANDS.exists():
        raise RuntimeError(f"refusing to overwrite {COMMANDS}")
    if TARGET.exists():
        raise RuntimeError(f"refusing to reuse {TARGET}")
    expected = {
        "root-fmt": 0,
        "dag-fmt": 0,
        "dag-clippy": 101,
        "qr7-focused-tests": 0,
        "dag-full-tests-no-raytracewithscreen": 0,
        "release-eggcc": 0,
    }
    results = {
        "root-fmt": run("root-fmt", ["cargo", "fmt", "--check"], ROOT),
        "dag-fmt": run("dag-fmt", ["cargo", "fmt", "--check"], DAG),
        "dag-clippy": run(
            "dag-clippy",
            ["cargo", "clippy", "--tests", "--", "-D", "warnings"],
            DAG,
        ),
        "qr7-focused-tests": run(
            "qr7-focused-tests",
            ["cargo", "test", "--release", "qr7_"],
            DAG,
        ),
        "dag-full-tests-no-raytracewithscreen": run(
            "dag-full-tests-no-raytracewithscreen",
            [
                "cargo",
                "insta",
                "test",
                "--release",
                "--unreferenced=reject",
                "--",
                "--skip",
                "raytracewithscreen",
            ],
            DAG,
        ),
        "release-eggcc": run(
            "release-eggcc",
            ["cargo", "build", "--offline", "--locked", "--release", "--bin", "eggcc"],
            ROOT,
        ),
    }
    actual = {name: result["exit_code"] for name, result in results.items()}
    summary = {
        "schema_version": 1,
        "status": "commands-complete",
        "expected_exit_codes": expected,
        "actual_exit_codes": actual,
        "expected_exit_codes_match": actual == expected,
        "commands": results,
    }
    (HERE / "command-summary.json").write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"expected_exit_codes_match": actual == expected, "actual": actual}, indent=2))
    return 0 if actual == expected else 1


if __name__ == "__main__":
    sys.exit(main())
