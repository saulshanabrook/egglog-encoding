"""Headline aggregation, matched coverage, and distinct checked-program counts."""

from __future__ import annotations

import io
import json
import math
from copy import deepcopy
from pathlib import Path
from typing import Any

import pytest
from rich.console import Console

from benchmarking.pilot_figures import export_pilot
from benchmarking.pilot_headlines import headline_results, headline_tex

from .test_pilot_figures import snapshot_fixture


def two_workload_snapshot() -> dict[str, Any]:
    snapshot = snapshot_fixture()
    original = next(row for row in snapshot["comparisons"] if row["experiment"] == "slotted")
    second = {**original, "logical_id": "sha256:second", "baseline": "second-ref", "candidate": "second-ours"}
    snapshot["comparisons"].append(second)
    for index, times in ((0, (100.0, 1.0)), (1, (50.0, 4.0))):
        first = snapshot["conditions"][index]
        clone = deepcopy(first)
        clone.update(id=second["baseline" if index == 0 else "candidate"], logical_id=second["logical_id"])
        snapshot["conditions"].append(clone)
        for condition, time in zip((first, clone), times, strict=True):
            for observation in condition["observations"]:
                observation["wall_sec"] = time
    return snapshot


def test_aggregation_can_reverse_direction_and_does_not_pool_suites() -> None:
    result = headline_results(two_workload_snapshot())
    slotted = result["comparisons"]["slotted"]
    assert slotted["reference_mean_runtime_sec"] == 50.5
    assert slotted["ours_mean_runtime_sec"] == 27
    assert slotted["speedup_ratio_of_mean_runtimes"] == pytest.approx(101 / 54)
    assert slotted["speedup_geometric_mean"] == pytest.approx(math.sqrt(2 * 0.25))
    assert slotted["speedup_geometric_mean"] != pytest.approx((2 + 0.25) / 2)
    assert len(result["comparisons"]) == 4
    numbers = result["numbers"]
    assert numbers["EvalExtensionSpeedupRatioOfMeanRuntimesMin"] == pytest.approx(101 / 54)
    assert numbers["EvalExtensionSpeedupRatioOfMeanRuntimesMax"] == pytest.approx(100 / 0.0033)
    tex = headline_tex(result)
    assert r"\providecommand{\EvalSlottedRestrictedSpeedupRatioOfMeanRuntimes}{1.87}" in tex
    assert r"\providecommand{\EvalSlottedRestrictedSpeedupGeometricMean}{0.707}" in tex


@pytest.mark.parametrize("state", ("missing", "failed", "excluded", "semantic-proof-failure"))
def test_incomplete_timings_are_not_silently_dropped(state: str) -> None:
    snapshot = two_workload_snapshot()
    condition = snapshot["conditions"][-1]
    if state == "missing":
        condition["observations"].pop()
    elif state == "failed":
        condition["observations"][0]["status"] = "timeout"
    elif state == "excluded":
        condition["exclusion"] = {"reason": "reviewed resource exclusion"}
    else:
        condition["validation"] = {"status": "failed", "issue": "invalid proof", "summary": None}
    result = headline_results(snapshot)
    slotted = result["comparisons"]["slotted"]
    assert slotted["coverage"]["planned"] == 2
    assert slotted["coverage"]["complete"] == 1
    ratio = slotted["speedup_ratio_of_mean_runtimes"]
    assert ratio == (2 if state == "excluded" else None)
    if state != "excluded":
        assert result["numbers"]["EvalExtensionSpeedupRatioOfMeanRuntimesMin"] is None
        assert r"\todo{SlottedRestrictedSpeedupGeometricMean}" in headline_tex(result)


def test_range_requires_every_comparison() -> None:
    snapshot = snapshot_fixture()
    snapshot["comparisons"] = [row for row in snapshot["comparisons"] if row["experiment"] != "disequality"]
    numbers = headline_results(snapshot)["numbers"]
    assert numbers["EvalMathProofsSpeedupRatioOfMeanRuntimes"] is not None
    assert numbers["EvalExtensionSpeedupRatioOfMeanRuntimesMin"] is None
    assert numbers["EvalExtensionSpeedupGeometricMeanMax"] is None


@pytest.mark.parametrize("evidence", ("passed", "pending", "no-summary", "partial", "empty", "failed"))
def test_corpus_counts_checked_programs_not_conditions_or_users(evidence: str) -> None:
    snapshot = snapshot_fixture()
    snapshot["files"].append(deepcopy(snapshot["files"][0]))
    snapshot["files"].append({**snapshot["files"][0], "logical_id": "sha256:unverified"})
    proof = snapshot["conditions"][2]
    if evidence in ("pending", "failed"):
        proof["validation"]["status"] = evidence
    elif evidence == "no-summary":
        proof["validation"]["summary"] = None
    elif evidence == "partial":
        proof["validation"]["summary"]["verified_certificates"] = 1
    elif evidence == "empty":
        proof["validation"]["summary"].update(produced_certificates=0, verified_certificates=0)
    # Separate validation evidence remains meaningful with no timed observations.
    proof["observations"] = []
    snapshot["conditions"].append({**deepcopy(proof), "id": "another-condition"})
    result = headline_results(snapshot)
    assert result["corpus"]["program_count"] == 2
    assert result["corpus"]["checked_program_count"] == (1 if evidence == "passed" else 0)
    assert result["numbers"]["EvalCorpusCheckedProgramCount"] == (1 if evidence == "passed" else None)
    assert result["numbers"]["EvalCorpusCheckedProjectCount"] == (1 if evidence == "passed" else None)


def test_pilot_export_includes_headlines_and_replays_same_numbers(tmp_path: Path) -> None:
    snapshot = two_workload_snapshot()
    export_pilot(snapshot, tmp_path, Console(file=io.StringIO()), images=False)
    expected = (tmp_path / "headline.numbers.tex").read_text()
    assert (
        json.loads((tmp_path / "headline.results.json").read_text())["numbers"] == headline_results(snapshot)["numbers"]
    )
    saved = json.loads((tmp_path / "extensions-runtime.results.json").read_text())["pilot_snapshot"]
    export_pilot(saved, tmp_path / "replay", Console(file=io.StringIO()), images=False)
    assert (tmp_path / "replay/headline.numbers.tex").read_text() == expected
