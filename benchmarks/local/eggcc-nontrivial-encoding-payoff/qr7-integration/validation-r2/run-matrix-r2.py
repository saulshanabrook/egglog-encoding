#!/usr/bin/env python3
"""Run and capture the complete QR7 r2 semantic matrix."""

from __future__ import annotations

import hashlib
import json
import os
import shutil
import subprocess
import sys
import threading
from datetime import UTC, datetime
from pathlib import Path

REPOSITORY = Path("/Users/saul/p/egglog-encoding")
BASE = REPOSITORY / "benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration"
ROOT = BASE / "validation-r2/matrix-r2"
BINARY = Path("/private/tmp/eggcc-qr7-candidate-nits-r2-target/release/eggcc")
TIGER_SOURCE = BASE.parent / "admission/bin/tiger"
TIGER_TARGET = BINARY.parent / "tiger"
TIMEOUT_S = 3600


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def copy_stream(source: object, destinations: tuple[object, ...]) -> None:
    """Copy a child stream to its evidence file and the live terminal."""
    while data := source.readline():
        for destination in destinations:
            destination.write(data)
            destination.flush()


def run(label: str, argv: list[str], environment: dict[str, str]) -> dict[str, object]:
    """Run one matrix stage with live output and a complete receipt."""
    output = ROOT / "top-level" / label
    if output.exists():
        raise RuntimeError(f"refusing to overwrite {output}")
    output.mkdir(parents=True)
    started = datetime.now(UTC)
    process = subprocess.Popen(
        argv,
        cwd=REPOSITORY,
        env=environment,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        start_new_session=True,
    )
    assert process.stdout is not None
    assert process.stderr is not None
    with (output / "stdout").open("wb") as stdout, (output / "stderr").open("wb") as stderr:
        pumps = [
            threading.Thread(
                target=copy_stream,
                args=(process.stdout, (stdout, sys.stdout.buffer)),
                daemon=True,
            ),
            threading.Thread(
                target=copy_stream,
                args=(process.stderr, (stderr, sys.stderr.buffer)),
                daemon=True,
            ),
        ]
        for pump in pumps:
            pump.start()
        try:
            exit_code = process.wait(timeout=TIMEOUT_S)
            timed_out = False
        except subprocess.TimeoutExpired:
            process.kill()
            exit_code = process.wait()
            timed_out = True
        for pump in pumps:
            pump.join()
    finished = datetime.now(UTC)
    receipt: dict[str, object] = {
        "argv": argv,
        "cwd": str(REPOSITORY),
        "started_utc": started.isoformat().replace("+00:00", "Z"),
        "finished_utc": finished.isoformat().replace("+00:00", "Z"),
        "timeout_s": TIMEOUT_S,
        "exit_code": exit_code,
        "timed_out": timed_out,
        "environment": {
            "QR7_BINARY": environment["QR7_BINARY"],
            "QR7_OUTPUT_ROOT": environment["QR7_OUTPUT_ROOT"],
            "PYTHONDONTWRITEBYTECODE": environment["PYTHONDONTWRITEBYTECODE"],
        },
        "absent_environment": [
            "EGGLOG_BENCH_MEMORY_GUARD",
            "INSTA_UPDATE",
            "INSTA_FORCE_PASS",
        ],
        "raytracing_requested": False,
        "r2_binary_sha256": sha256(BINARY),
        "script": argv[1],
        "script_sha256": sha256(Path(argv[1])),
        "stdout_sha256": sha256(output / "stdout"),
        "stderr_sha256": sha256(output / "stderr"),
    }
    (output / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    if timed_out or exit_code != 0:
        raise RuntimeError(f"{label} failed; see {output}")
    return receipt


def main() -> None:
    if ROOT.exists():
        raise RuntimeError(f"refusing to overwrite {ROOT}")
    if sha256(BINARY) != "046efff7fcc7ea3a1e31ff8e35ccad32001967b75f97e4f2c1efaef0413b6333":
        raise RuntimeError("r2 binary identity drift")
    ROOT.mkdir(parents=True)
    tiger_expected = "130eaba8bb575e196b8e18898826356269efe6e28a56b9d3690ef42647d3b201"
    if sha256(TIGER_SOURCE) != tiger_expected:
        raise RuntimeError("retained tiger identity drift")
    if TIGER_TARGET.exists():
        raise RuntimeError(f"refusing to overwrite {TIGER_TARGET}")
    shutil.copy2(TIGER_SOURCE, TIGER_TARGET)
    if sha256(TIGER_TARGET) != tiger_expected:
        raise RuntimeError("provisioned tiger identity mismatch")
    setup = ROOT / "setup"
    setup.mkdir()
    (setup / "tiger-provision.json").write_text(
        json.dumps(
            {
                "schema_version": 1,
                "status": "retained-tiger-copied-adjacent-to-r2-eggcc",
                "source": str(TIGER_SOURCE),
                "target": str(TIGER_TARGET),
                "sha256": tiger_expected,
                "size": TIGER_TARGET.stat().st_size,
            },
            indent=2,
            sort_keys=True,
        )
        + "\n"
    )
    environment = dict(os.environ)
    for key in (
        "EGGLOG_BENCH_MEMORY_GUARD",
        "INSTA_UPDATE",
        "INSTA_FORCE_PASS",
    ):
        environment.pop(key, None)
    environment.update(
        {
            "QR7_BINARY": str(BINARY),
            "QR7_OUTPUT_ROOT": str(ROOT),
            "PYTHONDONTWRITEBYTECODE": "1",
        }
    )
    matrix = BASE / "matrix.py"
    inspection = BASE / "inspect.py"
    receipts = {}
    for phase in ("positive", "negative", "context-negative", "loop-negative"):
        receipts[phase] = run(
            phase,
            [sys.executable, str(matrix), phase],
            environment,
        )
    receipts["inspection"] = run(
        "inspection",
        [sys.executable, str(inspection)],
        environment,
    )
    (ROOT / "top-level-summary.json").write_text(
        json.dumps(
            {
                "schema_version": 1,
                "status": "all-four-matrix-phases-and-inspection-passed",
                "memory_guard_absent": True,
                "raytracing_requested": False,
                "timing_collected": False,
                "r2_binary": str(BINARY),
                "r2_binary_sha256": sha256(BINARY),
                "receipts": receipts,
            },
            indent=2,
            sort_keys=True,
        )
        + "\n"
    )


def compare() -> None:
    """Capture the post-matrix r1/r2 comparison and native inspection."""
    if not ROOT.is_dir():
        raise RuntimeError(f"missing completed matrix root {ROOT}")
    environment = dict(os.environ)
    for key in (
        "EGGLOG_BENCH_MEMORY_GUARD",
        "INSTA_UPDATE",
        "INSTA_FORCE_PASS",
    ):
        environment.pop(key, None)
    environment.update(
        {
            "QR7_BINARY": str(BINARY),
            "QR7_OUTPUT_ROOT": str(ROOT),
            "PYTHONDONTWRITEBYTECODE": "1",
        }
    )
    run(
        "r1-r2-comparison",
        [sys.executable, str(BASE / "validation-r2/compare-matrix-r2.py")],
        environment,
    )


if __name__ == "__main__":
    if sys.argv[1:] == ["compare"]:
        compare()
    elif not sys.argv[1:]:
        main()
    else:
        raise SystemExit("usage: run-matrix-r2.py [compare]")
