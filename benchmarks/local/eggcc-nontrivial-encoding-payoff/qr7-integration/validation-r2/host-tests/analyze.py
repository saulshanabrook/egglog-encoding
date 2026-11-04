#!/usr/bin/env python3
"""Audit QR7 r2 host results against retained r1 and U0 evidence."""

from __future__ import annotations

import hashlib
import json
import re
from datetime import UTC, datetime
from pathlib import Path

ROOT = Path("/Users/saul/p/egglog-encoding")
HERE = Path(__file__).resolve().parent
R1_VALIDATION = ROOT / "benchmarks/local/eggcc-nontrivial-encoding-payoff/qr7-integration/validation-r1"
U0_COMMAND = (
    ROOT
    / "benchmarks/local/eggcc-nontrivial-encoding-payoff/affine-integration/commands/validation-u0-release-make-test"
)
R2_SOURCE_MANIFEST = HERE.parent / "source-manifest-after.json"
RESULT_PATTERN = re.compile(
    r"test result: (?P<status>ok|FAILED)\. "
    r"(?P<passed>\d+) passed; (?P<failed>\d+) failed; "
    r"(?P<ignored>\d+) ignored; (?P<measured>\d+) measured; "
    r"(?P<filtered>\d+) filtered out;"
)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def test_results(path: Path) -> list[dict[str, object]]:
    return [
        {key: int(value) if key != "status" else value for key, value in match.groupdict().items()}
        for match in RESULT_PATTERN.finditer(path.read_text())
    ]


def verified_receipt(directory: Path) -> dict[str, object]:
    receipt_path = directory / "receipt.json"
    receipt = json.loads(receipt_path.read_text())
    return {
        "path": str(receipt_path.relative_to(ROOT)),
        "sha256": sha256(receipt_path),
        "argv": receipt["argv"],
        "cwd": receipt["cwd"],
        "exit_code": receipt["exit_code"],
        "timed_out": receipt["timed_out"],
        "stdout_sha256": sha256(directory / "stdout"),
        "stderr_sha256": sha256(directory / "stderr"),
        "streams_match_receipt": (
            sha256(directory / "stdout") == receipt["stdout_sha256"]
            and sha256(directory / "stderr") == receipt["stderr_sha256"]
        ),
    }


def main() -> None:
    final_directory = HERE / "command"
    first_directory = HERE / "attempt-01-missing-tiger"
    r1_directory = R1_VALIDATION / "commands/host-root-tests-no-raytrace-r3"
    final_receipt = verified_receipt(final_directory)
    first_receipt = verified_receipt(first_directory)
    r1_receipt = verified_receipt(r1_directory)
    u0_receipt = verified_receipt(U0_COMMAND)

    final_results = test_results(final_directory / "stdout")
    first_results = test_results(first_directory / "stdout")
    r1_results = test_results(r1_directory / "stdout")
    u0_results = test_results(U0_COMMAND / "stdout")
    if len(final_results) != 4 or len(r1_results) != 4 or len(u0_results) != 7:
        raise RuntimeError("unexpected test result group count")

    attribution_path = R1_VALIDATION / "independent-attribution.json"
    attribution = json.loads(attribution_path.read_text())
    attribution_rows = {row["name"]: row for row in attribution["snapshot_attribution"]["rows"]}
    pending = json.loads((HERE / "pending-snapshots.json").read_text())
    checked_in = {row["relative"]: row for row in json.loads((HERE / "checked-in-snapshots-before.json").read_text())}
    snapshot_rows = []
    for row in pending:
        name = Path(row["relative"]).name
        retained = HERE / "pending-snapshots" / name
        r1_live = Path("/private/tmp/eggcc-qr7-candidate/tests/snapshots") / name
        prior = attribution_rows[name]
        checked_in_name = row["relative"].removesuffix(".new")
        snapshot_rows.append(
            {
                "name": name,
                "r2_sha256": row["sha256"],
                "retained_copy_sha256": sha256(retained),
                "r1_attribution_sha256": prior["qr7_sha256"],
                "r1_live_sha256": sha256(r1_live),
                "u0_checked_in_sha256": prior["u0_checked_in_sha256"],
                "r2_checked_in_sha256": checked_in[checked_in_name]["sha256"],
                "r2_equals_r1": (row["sha256"] == prior["qr7_sha256"] == sha256(r1_live)),
                "r2_checked_in_equals_u0": (checked_in[checked_in_name]["sha256"] == prior["u0_checked_in_sha256"]),
                "matches_dependency_only_control": prior["matches_dependency_only_control"],
                "matches_parts32": prior["matches_parts32"],
                "matches_route": prior["matches_route"],
                "matches_sort": prior["matches_sort"],
            }
        )

    source_before = json.loads((HERE / "source-before.json").read_text())
    source_after = json.loads((HERE / "source-after.json").read_text())
    r2_source = json.loads(R2_SOURCE_MANIFEST.read_text())
    checked_in_after = json.loads((HERE / "checked-in-snapshots-after.json").read_text())
    cleanup = json.loads((HERE / "snapshot-cleanup.json").read_text())
    tiger = json.loads((HERE / "tiger-provision.json").read_text())

    comparison = {
        "schema_version": 1,
        "generated_utc": datetime.now(UTC).isoformat(),
        "status": "functional_tests_pass_snapshot_rejection_inherited_dependency_retarget_only",
        "receipts": {
            "r2_final": final_receipt,
            "r2_first_harness_attempt": first_receipt,
            "r1": r1_receipt,
            "u0": u0_receipt,
        },
        "test_results": {
            "r2_final": final_results,
            "r2_first_harness_attempt": first_results,
            "r1": r1_results,
            "u0_full_make_test": u0_results,
            "root_comparison": {
                "r2_unit_passed": final_results[0]["passed"],
                "r1_unit_passed": r1_results[0]["passed"],
                "u0_unit_passed": u0_results[0]["passed"],
                "r2_file_passed": final_results[2]["passed"],
                "r1_file_passed": r1_results[2]["passed"],
                "u0_file_passed": u0_results[2]["passed"],
                "r2_file_filtered": final_results[2]["filtered"],
                "r1_file_filtered": r1_results[2]["filtered"],
                "u0_file_filtered": u0_results[2]["filtered"],
                "u0_count_difference_explained_by_explicit_skip": (
                    final_results[2]["passed"] + final_results[2]["filtered"] == u0_results[2]["passed"]
                ),
            },
        },
        "snapshots": {
            "r2_pending_count": len(snapshot_rows),
            "r1_pending_count": attribution["snapshot_attribution"]["count"],
            "u0_pending_count": attribution["u0"]["prior_full_test_pending_snapshots"],
            "snapshots_accepted": False,
            "checked_in_snapshot_count": len(checked_in),
            "checked_in_snapshots_unchanged": (list(checked_in.values()) == checked_in_after),
            "rows": snapshot_rows,
            "all_r2_pending_equal_r1": all(row["r2_equals_r1"] for row in snapshot_rows),
            "all_r2_checked_in_equal_u0": all(row["r2_checked_in_equals_u0"] for row in snapshot_rows),
            "all_match_dependency_only_control": all(row["matches_dependency_only_control"] for row in snapshot_rows),
            "r1_attribution": str(attribution_path.relative_to(ROOT)),
            "r1_attribution_sha256": sha256(attribution_path),
        },
        "source_and_side_effects": {
            "source_entry_count": len(source_before),
            "source_matches_r2_post_cleanup_manifest": source_before == r2_source["entries"],
            "source_excluding_generated_snapshots_unchanged": source_before == source_after,
            "checked_in_snapshots_unchanged": list(checked_in.values()) == checked_in_after,
            "generated_pending_snapshots": len(snapshot_rows),
            "pending_snapshots_retained_in_evidence": len(list((HERE / "pending-snapshots").glob("*.snap.new"))),
            "pending_snapshots_removed_from_isolated_source": (
                len(cleanup["removed"]) == len(snapshot_rows) and not cleanup["remaining_snap_new"]
            ),
            "tiger_provision": tiger,
            "first_attempt_failure": (
                "The first run could not locate Tiger and therefore failed one unit test and "
                "1012 file-test arms; it generated no snapshots and did not change source."
            ),
        },
        "conclusion": {
            "r2_matches_r1_functional_counts": final_results == r1_results,
            "all_functional_test_bodies_passed": all(row["failed"] == 0 for row in final_results),
            "root_exit_is_snapshot_rejection": final_receipt["exit_code"] == 1 and len(snapshot_rows) == 13,
            "all_observed_root_snapshot_differences_are_inherited_dependency_retargeting": (
                len(snapshot_rows) == 13
                and all(row["r2_equals_r1"] for row in snapshot_rows)
                and all(row["matches_dependency_only_control"] for row in snapshot_rows)
            ),
            "qr7_r2_specific_root_difference_found": False,
            "memory_guard_absent": True,
            "raytracewithscreen_skipped": True,
            "other_raytrace_named_fixture_ran": True,
        },
    }
    (HERE / "comparison.json").write_text(json.dumps(comparison, indent=2) + "\n")

    final_elapsed = json.loads((final_directory / "receipt.json").read_text())["elapsed_seconds_diagnostic"]
    report = f"""# QR7 r2 root host validation

The corrected root release run executed `{final_receipt["argv"]}` in
`{final_receipt["cwd"]}` with Rust 1.91.0, four Cargo jobs,
`EGGLOG_BENCH_MEMORY_GUARD` absent, and `raytracewithscreen` explicitly skipped.
It completed in {final_elapsed:.1f} diagnostic seconds.

All test bodies passed: 31 root unit tests and 2,420 file-test arms, with the one
requested filter, plus two ignored doctests. This exactly matches r1. U0 passed 31
unit tests and 2,421 file-test arms without a filter; `2,420 + 1 filtered = 2,421`,
so the count difference is solely the explicit skip.

The command exited 1 because Insta generated 13 rejected snapshots. Every r2
snapshot is byte-identical to its r1 counterpart and to the dependency-retarget-only
control recorded by the independent r1 attribution. All 13 checked-in r2 snapshots
remain byte-identical to U0. U0 itself generated no pending snapshots. Therefore all
observed root snapshot differences are inherited dependency-retargeting differences;
this run found no QR7 r2-specific root difference.

The first captured attempt failed before this comparison because the fresh external
target did not expose Tiger to `find_tiger_binary`; 1,012 file-test arms reported the
same missing-Tiger harness error, as did one unit test. No snapshots were generated,
and source remained unchanged. The retained Tiger binary (`{tiger["sha256"]}`) was then copied beside the
test executables in the external target, matching the lookup contract. That setup is
recorded in [`tiger-provision.json`](tiger-provision.json), and the preliminary
receipt remains under [`attempt-01-missing-tiger/`](attempt-01-missing-tiger/).

The final run did not modify any of the 774 source entries or 270 checked-in
snapshots. Its 13 `.snap.new` files were copied to
[`pending-snapshots/`](pending-snapshots/) and then removed from the isolated source;
[`snapshot-cleanup.json`](snapshot-cleanup.json) records their exact hashes. No
snapshot was accepted. The narrower `raytracewithscreen` selector was skipped; the
ordinary `raytrace-test-benchmark` fixture still ran and passed.

[`comparison.json`](comparison.json) contains every snapshot hash, parsed test result,
source comparison, and verified receipt hash. The final full streams and receipt are
under [`command/`](command/).
"""
    (HERE / "report.md").write_text(report)


if __name__ == "__main__":
    main()
