#!/usr/bin/env python3
"""Create and validate a source-exact EggCC U0 nits control."""

from __future__ import annotations

import hashlib
import json
import os
import subprocess
import tarfile
import time
from datetime import UTC, datetime
from pathlib import Path

REVISION = "a0bbec127f83249074a46af3fd6f6126c90fe0fb"
EXPECTED_TREE = "66f7a1c5654616cf0e9b557e064e73b9c3b1ad18"
REPOSITORY = Path("/Users/saul/p/eggcc")
SOURCE = Path("/private/tmp/eggcc-qr7-u0-nits-r2")
ROOT_TARGET = Path("/private/tmp/eggcc-qr7-u0-nits-r2-root-target")
DAG_TARGET = Path("/private/tmp/eggcc-qr7-u0-nits-r2-dag-target")
OUTPUT = Path(__file__).resolve().parent
ARCHIVE = OUTPUT / f"eggcc-{REVISION}.tar"
TOOLCHAIN = "1.91.0"


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def run_checked(argv: list[str], *, cwd: Path | None = None) -> bytes:
    return subprocess.run(
        argv,
        cwd=cwd,
        check=True,
        capture_output=True,
    ).stdout


def git_text(*args: str) -> str:
    return run_checked(["git", "-C", str(REPOSITORY), *args]).decode().strip()


def archive_and_extract() -> dict[str, object]:
    if SOURCE.exists():
        raise RuntimeError(f"refusing to reuse source tree: {SOURCE}")
    if ARCHIVE.exists():
        raise RuntimeError(f"refusing to replace archive: {ARCHIVE}")

    commit = git_text("rev-parse", f"{REVISION}^{{commit}}")
    tree = git_text("rev-parse", f"{REVISION}^{{tree}}")
    if commit != REVISION or tree != EXPECTED_TREE:
        raise RuntimeError(f"unexpected source identity: commit={commit}, tree={tree}")

    with ARCHIVE.open("wb") as archive_stream:
        subprocess.run(
            ["git", "-C", str(REPOSITORY), "archive", "--format=tar", REVISION],
            check=True,
            stdout=archive_stream,
        )

    SOURCE.mkdir(parents=True)
    with tarfile.open(ARCHIVE, "r") as archive:
        archive.extractall(SOURCE, filter="data")

    return {
        "repository": str(REPOSITORY),
        "revision": REVISION,
        "tree": tree,
        "commit_object_sha256": sha256_bytes(
            run_checked(["git", "-C", str(REPOSITORY), "cat-file", "commit", REVISION])
        ),
        "archive": str(ARCHIVE),
        "archive_size_bytes": ARCHIVE.stat().st_size,
        "archive_sha256": sha256_file(ARCHIVE),
        "source_root": str(SOURCE),
    }


def tracked_manifest() -> list[dict[str, object]]:
    raw = run_checked(["git", "-C", str(REPOSITORY), "ls-tree", "-rz", "--full-tree", REVISION])
    rows = []
    for entry in raw.split(b"\0"):
        if not entry:
            continue
        metadata, raw_path = entry.split(b"\t", 1)
        mode, kind, object_id = metadata.decode().split()
        relative = raw_path.decode()
        path = SOURCE / relative
        if kind == "blob" and mode == "120000":
            payload = os.readlink(path).encode()
        elif kind == "blob":
            payload = path.read_bytes()
        else:
            payload = b""
        rows.append(
            {
                "path": relative,
                "mode": mode,
                "kind": kind,
                "git_object": object_id,
                "size_bytes": len(payload),
                "sha256": sha256_bytes(payload) if kind == "blob" else None,
            }
        )
    return rows


def manifest_digest(rows: list[dict[str, object]]) -> str:
    payload = json.dumps(rows, sort_keys=True, separators=(",", ":")).encode()
    return sha256_bytes(payload)


def environment(target: Path) -> tuple[dict[str, str], dict[str, object]]:
    env = os.environ.copy()
    env.pop("EGGLOG_BENCH_MEMORY_GUARD", None)
    env.update(
        {
            "RUSTUP_TOOLCHAIN": TOOLCHAIN,
            "CARGO_BUILD_JOBS": "4",
            "RUST_TEST_THREADS": "4",
            "RAYON_NUM_THREADS": "1",
            "CARGO_TARGET_DIR": str(target),
            "CARGO_TERM_COLOR": "never",
            "LLVM_SYS_180_PREFIX": "/opt/homebrew/opt/llvm@18",
            "LIBRARY_PATH": "/opt/homebrew/lib",
        }
    )
    recorded = {
        key: env[key]
        for key in (
            "RUSTUP_TOOLCHAIN",
            "CARGO_BUILD_JOBS",
            "RUST_TEST_THREADS",
            "RAYON_NUM_THREADS",
            "CARGO_TARGET_DIR",
            "CARGO_TERM_COLOR",
            "LLVM_SYS_180_PREFIX",
            "LIBRARY_PATH",
            "PATH",
        )
    }
    recorded["absent"] = ["EGGLOG_BENCH_MEMORY_GUARD"]
    return env, recorded


def capture(name: str, logical_argv: list[str], *, cwd: Path, target: Path) -> dict[str, object]:
    destination = OUTPUT / "commands" / name
    destination.mkdir(parents=True)
    stdout_path = destination / "stdout"
    stderr_path = destination / "stderr"
    env, recorded_env = environment(target)
    executed_argv = ["rustup", "run", TOOLCHAIN, *logical_argv]
    started = datetime.now(UTC)
    start_clock = time.monotonic()
    timed_out = False
    with stdout_path.open("wb") as stdout, stderr_path.open("wb") as stderr:
        try:
            result = subprocess.run(
                executed_argv,
                cwd=cwd,
                env=env,
                stdout=stdout,
                stderr=stderr,
                timeout=3600,
                check=False,
            )
            exit_code = result.returncode
        except subprocess.TimeoutExpired:
            timed_out = True
            exit_code = 124
    finished = datetime.now(UTC)
    receipt = {
        "schema_version": 1,
        "name": name,
        "argv": logical_argv,
        "executed_argv": executed_argv,
        "cwd": str(cwd),
        "timeout_seconds": 3600,
        "started_utc": started.isoformat(),
        "finished_utc": finished.isoformat(),
        "elapsed_seconds": time.monotonic() - start_clock,
        "exit_code": exit_code,
        "timed_out": timed_out,
        "environment": recorded_env,
        "stdout_sha256": sha256_file(stdout_path),
        "stderr_sha256": sha256_file(stderr_path),
    }
    receipt_path = destination / "receipt.json"
    receipt_path.write_text(json.dumps(receipt, indent=2) + "\n")
    return receipt


def main() -> None:
    source_identity = archive_and_extract()
    before = tracked_manifest()
    before_digest = manifest_digest(before)
    (OUTPUT / "source-manifest-before.json").write_text(json.dumps(before, indent=2) + "\n")

    rustc = run_checked(["rustup", "run", TOOLCHAIN, "rustc", "-Vv"]).decode()
    cargo = run_checked(["rustup", "run", TOOLCHAIN, "cargo", "-Vv"]).decode()
    rustfmt = run_checked(["rustup", "run", TOOLCHAIN, "rustfmt", "-Vv"]).decode()
    clippy = run_checked(["rustup", "run", TOOLCHAIN, "cargo", "clippy", "-V"]).decode()

    commands = [
        capture(
            "root-fmt",
            ["cargo", "fmt", "--check"],
            cwd=SOURCE,
            target=ROOT_TARGET,
        ),
        capture(
            "dag-fmt",
            ["cargo", "fmt", "--check"],
            cwd=SOURCE / "dag_in_context",
            target=DAG_TARGET,
        ),
        capture(
            "root-clippy",
            ["cargo", "clippy", "--tests", "--", "-D", "warnings"],
            cwd=SOURCE,
            target=ROOT_TARGET,
        ),
        capture(
            "dag-clippy",
            ["cargo", "clippy", "--tests", "--", "-D", "warnings"],
            cwd=SOURCE / "dag_in_context",
            target=DAG_TARGET,
        ),
    ]

    after = tracked_manifest()
    after_digest = manifest_digest(after)
    (OUTPUT / "source-manifest-after.json").write_text(json.dumps(after, indent=2) + "\n")
    identity = {
        "schema_version": 1,
        **source_identity,
        "tracked_entries": len(before),
        "tracked_blob_entries": sum(row["kind"] == "blob" for row in before),
        "source_manifest_before_sha256": before_digest,
        "source_manifest_after_sha256": after_digest,
        "source_unchanged_by_commands": before == after,
        "toolchain": {
            "requested": TOOLCHAIN,
            "rustc": rustc,
            "cargo": cargo,
            "rustfmt": rustfmt,
            "clippy": clippy,
        },
        "commands": commands,
        "tests_or_benchmarks_run": False,
        "raytracing_run": False,
    }
    (OUTPUT / "source-identity.json").write_text(json.dumps(identity, indent=2) + "\n")
    if before != after:
        raise RuntimeError("validation commands modified tracked source")


if __name__ == "__main__":
    main()
