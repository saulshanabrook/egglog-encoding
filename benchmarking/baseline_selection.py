"""Select a proof cohort exclusively from complete normal-mode measurements."""

from __future__ import annotations

import hashlib
import json
import math
from collections.abc import Mapping, Sequence
from dataclasses import asdict, dataclass, replace
from pathlib import Path
from statistics import fmean
from typing import Any, Literal

from rich import box
from rich.console import Console
from rich.table import Table
from rich.text import Text

from .admission import ProofTreatment
from .collection import build_collection_plan, collect_rows, emit_collection_plan, preflight_collection
from .models import BenchmarkEndpoint, ComparisonSpec, ResolvedTarget
from .pilot import require_suite_admission
from .reports.store import CacheKey, ReportStore, serialize_report_record
from .suites import SuiteSelection

BASELINE_ROUNDS = 10
MIN_WALL_SEC = 0.1
MAX_WALL_SEC = 30.0
SELECTION_RELATIVE_PATH = Path("benchmarks/local/baseline-selection.json")


@dataclass(frozen=True)
class BaselineResult:
    status: Literal["selected", "excluded", "failed", "pending"]
    count: int
    mean_wall_sec: float | None = None
    mean_peak_rss_bytes: float | None = None
    reason: str | None = None


def classify_baseline(rows: Sequence[Mapping[str, Any]]) -> BaselineResult:
    """Classify an already selected exact-identity normal-mode sample.

    Callers use ReportStore.latest_records with BASELINE_ROUNDS. Neither proof
    outcomes, memory use, nor source-family weights enter this rule. Failed
    rows cannot be discarded to obtain a complete-looking sample. Peak RSS is
    descriptive only and has no mean unless all selected readings are valid.
    """

    if any(row.get("treatment", "off") != "off" for row in rows) or len(rows) > BASELINE_ROUNDS:
        raise ValueError("baseline selection requires up to 10 exact-identity off observations")
    for row in reversed(rows):
        if row["status"] != "success":
            return BaselineResult("failed", len(rows), reason=f"off: {row.get('error_message') or row['status']}")
    if len(rows) != BASELINE_ROUNDS:
        return BaselineResult("pending", len(rows), reason=f"{BASELINE_ROUNDS - len(rows)} normal-mode runs missing")
    walls = [row["wall_sec"] for row in rows]
    if any(value is None or not math.isfinite(value) or value < 0 for value in walls):
        return BaselineResult("failed", len(rows), reason="normal-mode time is unavailable or invalid")
    peaks = [row.get("max_rss_bytes") for row in rows]
    mean_peak = (
        fmean(value for value in peaks if value is not None)
        if all(value is not None and math.isfinite(value) and value > 0 for value in peaks)
        else None
    )
    mean_wall = fmean(value for value in walls if value is not None)
    selected = MIN_WALL_SEC < mean_wall < MAX_WALL_SEC
    return BaselineResult(
        "selected" if selected else "excluded",
        len(rows),
        mean_wall,
        mean_peak,
        None if selected else "normal-mode mean time lies outside the time window",
    )


def selection_snapshot(
    selection: SuiteSelection, target: ResolvedTarget, store: ReportStore, timeout_sec: int
) -> dict[str, Any]:
    """Bind every cohort decision to its cache identity and original sample rows."""

    endpoint = BenchmarkEndpoint(target, "off")
    entries: list[dict[str, Any]] = []
    for file in selection.files:
        sample = store.latest_records(CacheKey.for_endpoint(endpoint, file, timeout_sec), BASELINE_ROUNDS)
        baseline = classify_baseline([row.record for row in sample])
        failure = store.latest_failure(CacheKey.for_endpoint(endpoint, file, timeout_sec), BASELINE_ROUNDS)
        if failure is not None:
            row = failure.record
            baseline = BaselineResult("failed", len(sample), reason=f"off: {row['error_message'] or row['status']}")
        aliases = [
            case
            for case in selection.cases
            if any(
                (alias.sha256, alias.fact_directory_sha256) == (file.sha256, file.fact_directory_sha256)
                for alias in selection.case_files[case.id]
            )
        ]
        entries.append(
            {
                "file_path": file.display_path,
                "file_sha256": file.sha256,
                "fact_directory_sha256": file.fact_directory_sha256,
                "aliases": [case.id for case in aliases],
                "families": list(dict.fromkeys(case.family for case in aliases)),
                "proof_query_blocked": selection.proof_blockers.get((file.sha256, file.fact_directory_sha256)),
                "baseline": asdict(baseline),
                "row_indices": [row.row_index for row in sample],
                "sample_sha256": hashlib.sha256(
                    b"\n".join(serialize_report_record(row.record) for row in sample)
                ).hexdigest(),
            }
        )
    # An identity is counted once within a family, even if several source cases
    # alias it. Cross-family aliases belong to both families; the total is unique.
    categories = ("selected", "too_fast", "too_slow", "pending", "failed")
    counts = dict.fromkeys(categories, 0)
    family_counts = {
        family: dict.fromkeys(categories, 0) for family in dict.fromkeys(c.family for c in selection.cases)
    }
    for entry in entries:
        baseline = entry["baseline"]
        category = baseline["status"]
        if category == "excluded":
            category = "too_fast" if baseline["mean_wall_sec"] <= MIN_WALL_SEC else "too_slow"
        counts[category] += 1
        for family in entry["families"]:
            family_counts[family][category] += 1
    return {
        "suite": selection.name,
        "report": str(store.path),
        "binary_sha256": target.binary_sha256_for("off"),
        "timeout_sec": timeout_sec,
        "policy": {
            "rounds": BASELINE_ROUNDS,
            "min_wall_sec_exclusive": MIN_WALL_SEC,
            "max_wall_sec_exclusive": MAX_WALL_SEC,
        },
        "baseline_complete": counts["pending"] == 0,
        "counts": counts,
        "family_counts": family_counts,
        "workloads": entries,
        "source_exclusions": [
            {
                "id": case.id,
                "family": case.family,
                "workloads": selection.source_exclusions[case.id],
                "reason": case.provenance["benchmark_selection"]["reason"],
            }
            for case in selection.cases
            if selection.source_exclusions.get(case.id)
        ],
        "source_blockers": [
            {
                "id": case.id,
                "family": case.family,
                "status": "missing" if case.id in selection.capture_errors else case.status,
                "reason": selection.capture_errors.get(case.id, case.reason or case.status),
            }
            for case in selection.cases
            if (case.status != "captured" or case.id in selection.capture_errors)
            and case.provenance.get("benchmark_selection", {}).get("workloads") != []
        ],
    }


def write_selection_snapshot(path: Path, snapshot: dict[str, Any]) -> None:
    """Keep the latest status plus immutable, content-addressed selection evidence."""

    content = json.dumps(snapshot, indent=2, sort_keys=True) + "\n"
    path.parent.mkdir(parents=True, exist_ok=True)
    if not path.exists() or path.read_text() != content:
        temporary = path.with_suffix(".tmp")
        temporary.write_text(content)
        temporary.replace(path)
    if snapshot["baseline_complete"]:
        encoded = content.encode()
        archive = path.parent / "baseline-selections" / (hashlib.sha256(encoded).hexdigest() + ".json")
        archive.parent.mkdir(parents=True, exist_ok=True)
        if archive.exists():
            if archive.read_bytes() != encoded:
                raise ValueError(f"immutable baseline selection archive changed: {archive}")
        else:
            temporary = archive.with_suffix(".tmp")
            temporary.write_bytes(encoded)
            temporary.replace(archive)


def run_baseline_campaign(
    selection: SuiteSelection,
    target: ResolvedTarget,
    store: ReportStore,
    timeout_sec: int,
    console: Console,
    *,
    baseline_only: bool = False,
    treatment: ProofTreatment = "proof-extraction",
) -> ComparisonSpec | None:
    """Finish all baselines, then collect the selected proof mode in one plan.

    Every measured run uses the ordinary append-only collector. Existing failed
    baseline or proof samples are terminal; a safety interruption saves the
    partial selection before propagating to the CLI's ordinary error handler.
    """

    baseline = BenchmarkEndpoint(target, "off")
    candidate = BenchmarkEndpoint(target, treatment)
    snapshot_path = selection.root / SELECTION_RELATIVE_PATH
    plan = build_collection_plan(store, target, (baseline,), selection.files, BASELINE_ROUNDS, timeout_sec, False, True)
    try:
        preflight_collection(plan, timeout_sec)
        emit_collection_plan(console, plan)
        collect_rows(store, plan, timeout_sec, console)
    finally:
        snapshot = selection_snapshot(selection, target, store, timeout_sec)
        write_selection_snapshot(snapshot_path, snapshot)
        counts = snapshot["counts"]
        console.print(
            Text(
                f"Normal-mode cohort: {counts['selected']} selected; "
                f"{len(snapshot['source_blockers'])} source blockers or deferred cases. Selection: {snapshot_path}"
            )
        )
        table = Table("Family", "Selected", "Too fast", "Too slow", "Pending", "Failed", box=box.SIMPLE_HEAD)
        for column in table.columns[1:]:
            column.justify = "right"
        for family, values in (*snapshot["family_counts"].items(), ("Total (unique)", counts)):
            table.add_row(
                family,
                str(values["selected"]),
                str(values["too_fast"]) + (" so far" if values["pending"] else ""),
                str(values["too_slow"]) + (" so far" if values["pending"] else ""),
                str(values["pending"]),
                str(values["failed"]),
            )
        console.print(table)
        console.print(
            Text(
                f"Too fast: mean ≤ {MIN_WALL_SEC:g}s; too slow: mean ≥ {MAX_WALL_SEC:g}s. "
                "Memory does not select the cohort."
            )
        )
        if counts["pending"]:
            console.print(Text("Counts are provisional while normal-mode runs are pending."))
        if sum(sum(values.values()) for values in snapshot["family_counts"].values()) != len(snapshot["workloads"]):
            console.print(Text("Shared workloads count once in each family; the total counts unique workloads."))
    if baseline_only:
        return None
    if not snapshot["baseline_complete"]:
        raise ValueError("baseline selection is incomplete; finish normal-mode observations before proof collection")
    selected_files = tuple(
        file
        for file, entry in zip(selection.files, snapshot["workloads"], strict=True)
        if entry["baseline"]["status"] == "selected"
    )
    if not selected_files:
        return None
    files, _diagnostics, issues = require_suite_admission(
        replace(selection, files=selected_files),
        (target,),
        store=store,
        timeout_sec=timeout_sec,
        rounds=BASELINE_ROUNDS,
        treatment=treatment,
    )
    for file, reason in issues:
        console.print(Text(f"{file.display_path}: selected; {reason}"))
    plan = build_collection_plan(
        store,
        target,
        (candidate,),
        files,
        BASELINE_ROUNDS,
        timeout_sec,
        False,
        True,
        tuple(file for file, _reason in issues),
    )
    preflight_collection(plan, timeout_sec)
    emit_collection_plan(console, plan)
    collect_rows(store, plan, timeout_sec, console)
    return ComparisonSpec(
        baseline,
        candidate,
        selected_files,
        BASELINE_ROUNDS,
        timeout_sec,
        validation_issues=tuple(issues),
        suite_mode=True,
    )
