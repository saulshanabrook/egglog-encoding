"""Select expanded workloads from all matching normal-mode observations."""

from __future__ import annotations

import math
from collections import Counter
from collections.abc import Mapping, Sequence
from dataclasses import dataclass
from statistics import fmean
from typing import Any, Literal

from rich.console import Console
from rich.text import Text

from .collection import build_collection_plan, collect_rows, emit_collection_plan, preflight_collection
from .models import BenchmarkEndpoint, ComparisonSpec, DisequalityEncoding, ResolvedTarget
from .reports.store import CacheKey, ReportStore
from .suites import ProofTreatment, SuiteSelection, suite_outcomes

BASELINE_ROUNDS = 10
MIN_WALL_SEC = 0.1
MAX_WALL_SEC = 30.0


@dataclass(frozen=True)
class BaselineResult:
    status: Literal["selected", "excluded", "failed", "pending"]
    count: int
    mean_wall_sec: float | None = None
    reason: str | None = None


def classify_baseline(rows: Sequence[Mapping[str, Any]]) -> BaselineResult:
    """Use every exact-identity off observation, with no count or memory criterion."""

    if any(row.get("treatment", "off") != "off" for row in rows):
        raise ValueError("baseline selection requires exact-identity off observations")
    if not rows:
        return BaselineResult("pending", 0, reason="normal-mode observations are missing")
    for row in reversed(rows):
        if row["status"] != "success":
            return BaselineResult("failed", len(rows), reason=f"off: {row.get('error_message') or row['status']}")
    walls = [row["wall_sec"] for row in rows]
    if any(value is None or not math.isfinite(value) for value in walls):
        return BaselineResult("failed", len(rows), reason="normal-mode time is unavailable or invalid")
    mean = fmean(walls)
    selected = MIN_WALL_SEC < mean < MAX_WALL_SEC
    return BaselineResult(
        "selected" if selected else "excluded",
        len(rows),
        mean,
        None if selected else "normal-mode mean time lies outside the time window",
    )


def run_baseline_campaign(
    selection: SuiteSelection,
    target: ResolvedTarget,
    store: ReportStore,
    timeout_sec: int,
    console: Console,
    *,
    rounds: int = BASELINE_ROUNDS,
    baseline_only: bool = False,
    treatment: ProofTreatment = "proof-extraction",
    disequality_encoding: DisequalityEncoding = "nee",
    baseline_encoding: DisequalityEncoding = "nee",
) -> ComparisonSpec | None:
    """Top up all baselines before collecting proofs for the all-observation cohort."""

    baseline = BenchmarkEndpoint(target, "off", baseline_encoding)
    candidate = BenchmarkEndpoint(target, treatment, disequality_encoding)
    validation, deferred = suite_outcomes(selection, (baseline, candidate), timeout_sec)
    blocked = tuple(file for file, _ in deferred)
    plan = build_collection_plan(store, target, (baseline,), selection.files, rounds, timeout_sec, False, True, blocked)
    preflight_collection(plan, timeout_sec)
    emit_collection_plan(console, plan)
    collect_rows(store, plan, timeout_sec, console)
    results = {
        file: classify_baseline(
            [row.record for row in store.latest_records(CacheKey.for_endpoint(baseline, file, timeout_sec))]
        )
        for file in selection.files
    }
    counts = Counter(result.status for result in results.values())
    console.print(Text("Normal-mode cohort: " + "; ".join(f"{n} {status}" for status, n in sorted(counts.items()))))
    for file, result in results.items():
        if result.status in ("failed", "pending"):
            console.print(Text(f"{file.display_path}: {result.status}; {result.reason}"))
    for file, reason in deferred:
        console.print(Text(f"{file.display_path}: safety-deferred; {reason}"))
    if baseline_only:
        return None
    if any(
        result.count < rounds and result.status != "failed" and file not in blocked for file, result in results.items()
    ):
        raise ValueError("finish normal-mode collection before collecting proofs")
    files = tuple(file for file, result in results.items() if result.status == "selected")
    if not files:
        return None
    plan = build_collection_plan(store, target, (candidate,), files, rounds, timeout_sec, False, True, blocked)
    preflight_collection(plan, timeout_sec)
    emit_collection_plan(console, plan)
    collect_rows(store, plan, timeout_sec, console)
    issues = tuple((file, reason) for file, reason in (*validation, *deferred) if file in files)
    return ComparisonSpec(baseline, candidate, files, rounds, timeout_sec, validation_issues=issues, suite_mode=True)
