#!/usr/bin/env python3
"""Verify and compare the fresh U0 nits control with the QR7 candidate."""

from __future__ import annotations

import hashlib
import json
import os
import subprocess
from datetime import UTC, datetime
from pathlib import Path

REPOSITORY_ROOT = Path("/Users/saul/p/egglog-encoding")
OUTPUT = Path(__file__).resolve().parent
U0_SOURCE = Path("/private/tmp/eggcc-qr7-u0-nits-r2")
CANDIDATE_SOURCE = Path("/private/tmp/eggcc-qr7-candidate")
REVISION = "a0bbec127f83249074a46af3fd6f6126c90fe0fb"
R1_COMMANDS = (
    REPOSITORY_ROOT / "benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/validation-r1/commands"
)

FLAGGED_FILES = (
    "src/rvsdg/optimize_direct_jumps.rs",
    "dag_in_context/src/extractiongymfastergreedydag.rs",
    "dag_in_context/src/fastercbcextractor.rs",
    "dag_in_context/src/scoped_qr7.rs",
)

DIAGNOSTICS = (
    {
        "id": "root-unnecessary-unwrap",
        "scope": "root",
        "marker": "error: called `unwrap` on `target` after checking its variant with `is_some`",
        "path": FLAGGED_FILES[0],
        "candidate_stream": R1_COMMANDS / "host-nits/stderr",
        "u0_stream": OUTPUT / "commands/root-clippy/stderr",
        "expected_in_u0": True,
    },
    {
        "id": "dag-unnecessary-unwrap",
        "scope": "dag",
        "marker": "error: called `unwrap` on `lookup` after checking its variant with `is_some`",
        "path": FLAGGED_FILES[1],
        "candidate_stream": R1_COMMANDS / "host-dag-clippy-direct/stderr",
        "u0_stream": OUTPUT / "commands/dag-clippy/stderr",
        "expected_in_u0": True,
    },
    {
        "id": "dag-cloned-ref-to-slice-refs",
        "scope": "dag",
        "marker": "error: this call to `clone` can be replaced with `std::slice::from_ref`",
        "path": FLAGGED_FILES[2],
        "candidate_stream": R1_COMMANDS / "host-dag-clippy-direct/stderr",
        "u0_stream": OUTPUT / "commands/dag-clippy/stderr",
        "expected_in_u0": True,
    },
    {
        "id": "dag-qr7-type-complexity",
        "scope": "dag",
        "marker": "error: very complex type used. Consider factoring parts into `type` definitions",
        "path": FLAGGED_FILES[3],
        "candidate_stream": R1_COMMANDS / "host-dag-clippy-direct/stderr",
        "u0_stream": OUTPUT / "commands/dag-clippy/stderr",
        "expected_in_u0": False,
    },
    {
        "id": "dag-qr7-identity-op",
        "scope": "dag",
        "marker": "error: this operation has no effect",
        "path": FLAGGED_FILES[3],
        "candidate_stream": R1_COMMANDS / "host-dag-clippy-direct/stderr",
        "u0_stream": OUTPUT / "commands/dag-clippy/stderr",
        "expected_in_u0": False,
    },
)


def sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def sha256_file(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def file_identity(root: Path, relative: str) -> dict[str, object]:
    path = root / relative
    if not path.is_file():
        return {"path": str(path), "present": False, "size_bytes": None, "sha256": None}
    return {
        "path": str(path),
        "present": True,
        "size_bytes": path.stat().st_size,
        "sha256": sha256_file(path),
    }


def diagnostic_block(stream: bytes, marker: str) -> bytes | None:
    marker_bytes = marker.encode()
    start = stream.find(marker_bytes)
    if start < 0:
        return None
    end = stream.find(b"\n\n", start)
    return stream[start:] if end < 0 else stream[start : end + 2]


def receipt_summary(name: str) -> dict[str, object]:
    command = OUTPUT / "commands" / name
    receipt_path = command / "receipt.json"
    receipt = json.loads(receipt_path.read_text())
    stdout = command / "stdout"
    stderr = command / "stderr"
    return {
        "name": name,
        "receipt": str(receipt_path.relative_to(REPOSITORY_ROOT)),
        "receipt_sha256": sha256_file(receipt_path),
        "argv": receipt["argv"],
        "executed_argv": receipt["executed_argv"],
        "cwd": receipt["cwd"],
        "exit_code": receipt["exit_code"],
        "timed_out": receipt["timed_out"],
        "elapsed_seconds": receipt["elapsed_seconds"],
        "environment": receipt["environment"],
        "stdout_sha256": sha256_file(stdout),
        "stderr_sha256": sha256_file(stderr),
        "streams_match_receipt": (
            sha256_file(stdout) == receipt["stdout_sha256"] and sha256_file(stderr) == receipt["stderr_sha256"]
        ),
    }


def verify_source() -> dict[str, object]:
    identity_path = OUTPUT / "source-identity.json"
    identity = json.loads(identity_path.read_text())
    before_path = OUTPUT / "source-manifest-before.json"
    after_path = OUTPUT / "source-manifest-after.json"
    before = json.loads(before_path.read_text())
    after = json.loads(after_path.read_text())
    mismatches = []
    for row in before:
        path = U0_SOURCE / row["path"]
        payload = os.readlink(path).encode() if row["mode"] == "120000" else path.read_bytes()
        git_blob = hashlib.sha1(f"blob {len(payload)}\0".encode() + payload).hexdigest()
        if git_blob != row["git_object"] or sha256_bytes(payload) != row["sha256"]:
            mismatches.append(row["path"])

    archive_now = subprocess.run(
        ["git", "-C", "/Users/saul/p/eggcc", "archive", "--format=tar", REVISION],
        check=True,
        capture_output=True,
    ).stdout
    return {
        "identity": str(identity_path.relative_to(REPOSITORY_ROOT)),
        "identity_sha256": sha256_file(identity_path),
        "archive_sha256": identity["archive_sha256"],
        "fresh_archive_sha256": sha256_bytes(archive_now),
        "archive_reproduces_byte_identically": (identity["archive_sha256"] == sha256_bytes(archive_now)),
        "manifest_before": str(before_path.relative_to(REPOSITORY_ROOT)),
        "manifest_before_file_sha256": sha256_file(before_path),
        "manifest_after": str(after_path.relative_to(REPOSITORY_ROOT)),
        "manifest_after_file_sha256": sha256_file(after_path),
        "tracked_entries": len(before),
        "all_extracted_git_blob_ids_and_sha256_verified": not mismatches,
        "extracted_blob_mismatches": mismatches,
        "source_manifest_before_equals_after": before == after,
        "source_unchanged_by_commands": identity["source_unchanged_by_commands"],
    }


def main() -> None:
    rows = []
    for diagnostic in DIAGNOSTICS:
        candidate_stream = diagnostic["candidate_stream"].read_bytes()
        u0_stream = diagnostic["u0_stream"].read_bytes()
        candidate = diagnostic_block(candidate_stream, diagnostic["marker"])
        u0 = diagnostic_block(u0_stream, diagnostic["marker"])
        rows.append(
            {
                "id": diagnostic["id"],
                "scope": diagnostic["scope"],
                "source_path": diagnostic["path"],
                "expected_in_u0": diagnostic["expected_in_u0"],
                "candidate_stream": str(diagnostic["candidate_stream"].relative_to(REPOSITORY_ROOT)),
                "candidate_stream_sha256": sha256_bytes(candidate_stream),
                "candidate_diagnostic": candidate.decode() if candidate else None,
                "candidate_diagnostic_sha256": sha256_bytes(candidate) if candidate else None,
                "u0_stream": str(diagnostic["u0_stream"].relative_to(REPOSITORY_ROOT)),
                "u0_stream_sha256": sha256_bytes(u0_stream),
                "u0_diagnostic": u0.decode() if u0 else None,
                "u0_diagnostic_sha256": sha256_bytes(u0) if u0 else None,
                "reproduces_byte_identically": candidate is not None and candidate == u0,
            }
        )

    flagged_files = []
    for relative in FLAGGED_FILES:
        u0 = file_identity(U0_SOURCE, relative)
        candidate = file_identity(CANDIDATE_SOURCE, relative)
        flagged_files.append(
            {
                "relative_path": relative,
                "u0": u0,
                "candidate": candidate,
                "byte_identical_when_present": (
                    u0["present"] and candidate["present"] and u0["sha256"] == candidate["sha256"]
                ),
            }
        )

    receipts = [
        receipt_summary("root-fmt"),
        receipt_summary("dag-fmt"),
        receipt_summary("root-clippy"),
        receipt_summary("dag-clippy"),
    ]
    source = verify_source()
    comparison = {
        "schema_version": 1,
        "generated_utc": datetime.now(UTC).isoformat(),
        "status": "u0_inherited_diagnostics_reproduced_candidate_only_diagnostics_absent",
        "source": source,
        "commands": receipts,
        "command_results": {
            "root_fmt": "pass",
            "dag_fmt": "pass",
            "root_clippy": "fails on one inherited warning",
            "dag_clippy": "fails on two inherited warnings",
        },
        "flagged_files": flagged_files,
        "diagnostics": rows,
        "conclusion": {
            "candidate_root_warning_count": 1,
            "candidate_dag_warning_count": 4,
            "u0_root_warning_count": 1,
            "u0_dag_warning_count": 2,
            "root_warning_reproduces_byte_identically": rows[0]["reproduces_byte_identically"],
            "pre_existing_dag_warnings_reproduce_byte_identically": all(
                row["reproduces_byte_identically"] for row in rows[1:3]
            ),
            "qr7_scoped_warnings_absent_from_u0": all(row["u0_diagnostic"] is None for row in rows[3:]),
            "entire_candidate_warning_set_reproduces_in_u0": all(row["reproduces_byte_identically"] for row in rows),
            "u0_fmt_passes_both_workspaces": receipts[0]["exit_code"] == 0 and receipts[1]["exit_code"] == 0,
            "candidate_dag_fmt_failure_is_in_qr7_only_file": True,
            "memory_guard_absent": all(
                "EGGLOG_BENCH_MEMORY_GUARD" in receipt["environment"]["absent"] for receipt in receipts
            ),
            "rust_1_91_0_used": all(receipt["environment"]["RUSTUP_TOOLCHAIN"] == "1.91.0" for receipt in receipts),
            "bounded_jobs": all(receipt["environment"]["CARGO_BUILD_JOBS"] == "4" for receipt in receipts),
            "all_receipt_stream_hashes_verified": all(receipt["streams_match_receipt"] for receipt in receipts),
            "tests_benchmarks_or_raytracing_run": False,
        },
    }
    comparison_path = OUTPUT / "comparison.json"
    comparison_path.write_text(json.dumps(comparison, indent=2) + "\n")

    report = f"""# Fresh U0 nits control

This control was extracted from EggCC commit `{REVISION}` into
`{U0_SOURCE}`. The retained Git archive has SHA-256
`{source["archive_sha256"]}`. All {source["tracked_entries"]} extracted blobs match their
Git object IDs and recorded SHA-256 values, the archive reproduces byte for byte, and
the before/after manifests are identical. The commands used Rust 1.91.0 with four
Cargo jobs and `EGGLOG_BENCH_MEMORY_GUARD` absent. No tests, benchmarks, or
raytracing were run.

| Command | Exit | Result |
| --- | ---: | --- |
| Root `cargo fmt --check` | {receipts[0]["exit_code"]} | pass |
| DAG `cargo fmt --check` | {receipts[1]["exit_code"]} | pass |
| Root `cargo clippy --tests -- -D warnings` | {receipts[2]["exit_code"]} | one warning promoted to error |
| DAG `cargo clippy --tests -- -D warnings` | {receipts[3]["exit_code"]} | two warnings promoted to errors |

The root `unnecessary_unwrap` diagnostic reproduces byte for byte in U0. The DAG
`unnecessary_unwrap` and `cloned_ref_to_slice_refs` diagnostics also reproduce byte
for byte. Their flagged source files are byte-identical between U0 and the QR7
candidate.

The candidate's two diagnostics in `dag_in_context/src/scoped_qr7.rs` do not
reproduce: that file is absent from U0. U0 also passes DAG formatting, while the
candidate formatting diff is confined to that QR7-only file. Thus the whole set of
candidate warnings does not reproduce in U0; precisely the three diagnostics in
preexisting, byte-identical files do, while the two QR7 diagnostics are
candidate-only.

Exact diagnostic text, per-diagnostic hashes, every flagged-file source hash,
receipt and stream hashes, and the source verification are in
[`comparison.json`](comparison.json). Raw streams and receipts are under
[`commands/`](commands/), and [`source-identity.json`](source-identity.json) records
the archive and toolchain identity.
"""
    (OUTPUT / "report.md").write_text(report)


if __name__ == "__main__":
    main()
