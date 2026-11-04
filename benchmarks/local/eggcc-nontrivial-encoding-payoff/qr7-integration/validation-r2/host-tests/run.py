#!/usr/bin/env python3
"""Capture the QR7 r2 root release test suite without accepting snapshots."""

from __future__ import annotations

import hashlib
import json
import os
import shutil
import subprocess
import time
from datetime import UTC, datetime
from pathlib import Path

REPOSITORY_ROOT = Path("/Users/saul/p/egglog-encoding")
SOURCE = Path("/private/tmp/eggcc-qr7-candidate-nits-r2")
TARGET = Path("/private/tmp/eggcc-qr7-candidate-nits-r2-target")
OUTPUT = Path(__file__).resolve().parent
COMMAND = OUTPUT / "command"
PENDING_COPY = OUTPUT / "pending-snapshots"
TIMEOUT_SECONDS = 1800
ARGV = [
    "cargo",
    "insta",
    "test",
    "--release",
    "--unreferenced=reject",
    "--",
    "--skip",
    "raytracewithscreen",
]


def sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def file_manifest(*, include_pending: bool) -> list[dict[str, object]]:
    rows = []
    for path in sorted(SOURCE.rglob("*")):
        relative = path.relative_to(SOURCE)
        if "target" in relative.parts or (not include_pending and path.name.endswith(".snap.new")):
            continue
        if path.is_symlink():
            payload = os.readlink(path).encode()
            kind = "symlink"
        elif path.is_file():
            payload = path.read_bytes()
            kind = "file"
        else:
            continue
        rows.append(
            {
                "relative": str(relative),
                "kind": kind,
                "size": len(payload),
                "sha256": sha256_bytes(payload),
            }
        )
    return rows


def snapshot_manifest(suffix: str) -> list[dict[str, object]]:
    rows = []
    for path in sorted((SOURCE / "tests/snapshots").glob(f"*{suffix}")):
        rows.append(
            {
                "relative": str(path.relative_to(SOURCE)),
                "size": path.stat().st_size,
                "sha256": sha256_file(path),
            }
        )
    return rows


def main() -> None:
    if COMMAND.exists() or PENDING_COPY.exists():
        raise RuntimeError("refusing to overwrite existing host-test evidence")
    initial_pending = snapshot_manifest(".snap.new")
    if initial_pending:
        raise RuntimeError(f"expected no initial pending snapshots, found {len(initial_pending)}")

    source_before = file_manifest(include_pending=False)
    checked_in_before = snapshot_manifest(".snap")
    (OUTPUT / "source-before.json").write_text(json.dumps(source_before, indent=2) + "\n")
    (OUTPUT / "checked-in-snapshots-before.json").write_text(json.dumps(checked_in_before, indent=2) + "\n")

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
            "EGGCC_ROOT": str(SOURCE),
            "RUSTUP_TOOLCHAIN": "1.91.0",
            "CARGO_BUILD_JOBS": "4",
            "RUST_TEST_THREADS": "4",
            "RAYON_NUM_THREADS": "1",
            "LLVM_SYS_180_PREFIX": "/opt/homebrew/opt/llvm@18",
            "LIBRARY_PATH": "/opt/homebrew/lib",
            "CARGO_TARGET_DIR": str(TARGET),
            "PYTHONDONTWRITEBYTECODE": "1",
            "CARGO_TERM_COLOR": "never",
            "PATH": "/opt/homebrew/opt/llvm@18/bin:" + environment["PATH"],
        }
    )
    executable = Path(
        subprocess.run(
            ["which", ARGV[0]],
            env=environment,
            check=True,
            capture_output=True,
        )
        .stdout.decode()
        .strip()
    )

    COMMAND.mkdir()
    stdout_path = COMMAND / "stdout"
    stderr_path = COMMAND / "stderr"
    started = datetime.now(UTC)
    monotonic_started = time.monotonic()
    timed_out = False
    with stdout_path.open("wb") as stdout, stderr_path.open("wb") as stderr:
        try:
            completed = subprocess.run(
                ARGV,
                cwd=SOURCE,
                env=environment,
                stdout=stdout,
                stderr=stderr,
                timeout=TIMEOUT_SECONDS,
                check=False,
            )
            exit_code = completed.returncode
        except subprocess.TimeoutExpired:
            exit_code = 124
            timed_out = True
    elapsed = time.monotonic() - monotonic_started
    finished = datetime.now(UTC)

    pending_after = snapshot_manifest(".snap.new")
    checked_in_after = snapshot_manifest(".snap")
    source_after = file_manifest(include_pending=False)
    (OUTPUT / "source-after.json").write_text(json.dumps(source_after, indent=2) + "\n")
    (OUTPUT / "checked-in-snapshots-after.json").write_text(json.dumps(checked_in_after, indent=2) + "\n")
    (OUTPUT / "pending-snapshots.json").write_text(json.dumps(pending_after, indent=2) + "\n")
    PENDING_COPY.mkdir()
    for row in pending_after:
        source = SOURCE / row["relative"]
        shutil.copyfile(source, PENDING_COPY / source.name)

    receipt = {
        "schema_version": 1,
        "argv": ARGV,
        "cwd": str(SOURCE),
        "started_utc": started.isoformat().replace("+00:00", "Z"),
        "finished_utc": finished.isoformat().replace("+00:00", "Z"),
        "timeout_seconds": TIMEOUT_SECONDS,
        "elapsed_seconds_diagnostic": elapsed,
        "diagnostic_elapsed_is_performance_evidence": False,
        "exit_code": exit_code,
        "timed_out": timed_out,
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
                "CARGO_TERM_COLOR",
            )
        },
        "absent_environment": [
            "EGGLOG_BENCH_MEMORY_GUARD",
            "INSTA_UPDATE",
            "INSTA_FORCE_PASS",
        ],
        "raytracing_requested": False,
        "explicitly_skipped_test": "raytracewithscreen",
        "executable": str(executable),
        "executable_sha256": sha256_file(executable),
        "stdout_sha256": sha256_file(stdout_path),
        "stderr_sha256": sha256_file(stderr_path),
        "initial_pending_snapshots": len(initial_pending),
        "pending_snapshots_after": len(pending_after),
        "checked_in_snapshots_unchanged": checked_in_before == checked_in_after,
        "source_excluding_generated_snapshots_unchanged": source_before == source_after,
        "source_before_sha256": sha256_file(OUTPUT / "source-before.json"),
        "source_after_sha256": sha256_file(OUTPUT / "source-after.json"),
        "pending_snapshot_manifest_sha256": sha256_file(OUTPUT / "pending-snapshots.json"),
    }
    (COMMAND / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")


if __name__ == "__main__":
    main()
