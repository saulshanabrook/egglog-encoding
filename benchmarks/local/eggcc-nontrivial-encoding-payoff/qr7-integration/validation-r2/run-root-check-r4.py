#!/usr/bin/env python3
"""Run the repository-required final check without benchmark memory admission."""

from __future__ import annotations

from datetime import UTC, datetime
import hashlib
import json
import os
from pathlib import Path
import subprocess


ROOT = Path("/Users/saul/p/egglog-encoding")
OUTPUT = Path(__file__).resolve().parent / "root-make-check-r4"
if OUTPUT.exists():
    raise SystemExit(f"refusing to overwrite {OUTPUT}")
OUTPUT.mkdir()

environment = dict(os.environ)
for name in (
    "CARGO_TARGET_DIR",
    "EGGLOG_BENCH_MEMORY_GUARD",
    "INSTA_FORCE_PASS",
    "INSTA_UPDATE",
    "MAKEFLAGS",
):
    environment.pop(name, None)

started = datetime.now(UTC)
try:
    completed = subprocess.run(
        ["make", "check"],
        cwd=ROOT,
        env=environment,
        capture_output=True,
        timeout=3600,
        check=False,
    )
    timed_out = False
except subprocess.TimeoutExpired as error:
    completed = subprocess.CompletedProcess(
        ["make", "check"],
        124,
        stdout=error.stdout or b"",
        stderr=error.stderr or b"",
    )
    timed_out = True
finished = datetime.now(UTC)

(OUTPUT / "stdout").write_bytes(completed.stdout)
(OUTPUT / "stderr").write_bytes(completed.stderr)
receipt = {
    "argv": ["make", "check"],
    "cwd": str(ROOT),
    "started_utc": started.isoformat().replace("+00:00", "Z"),
    "finished_utc": finished.isoformat().replace("+00:00", "Z"),
    "timeout_s": 3600,
    "timed_out": timed_out,
    "exit_code": completed.returncode,
    "stdout_sha256": hashlib.sha256(completed.stdout).hexdigest(),
    "stderr_sha256": hashlib.sha256(completed.stderr).hexdigest(),
    "absent_environment": ["EGGLOG_BENCH_MEMORY_GUARD"],
    "raytracing_requested": False,
}
(OUTPUT / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
print(json.dumps(receipt, indent=2))
raise SystemExit(completed.returncode)
