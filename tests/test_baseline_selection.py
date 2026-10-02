"""All normal observations select the cohort; proof outcomes never select it."""

from __future__ import annotations

import io
from pathlib import Path
from typing import Any

import pytest
from rich.console import Console

from benchmarking import baseline_selection as selection
from benchmarking import collection, processes, suites, targets
from benchmarking.models import BenchmarkEndpoint
from benchmarking.reports.store import CacheKey, ReportStore

from .corpus_fixtures import prepare_corpus
from .report_fixtures import make_record, make_target, make_timing_summary


@pytest.mark.parametrize(
    "wall,expected",
    [
        (0.1, "excluded"),
        (0.10001, "selected"),
        (30, "excluded"),
        (29.999, "selected"),
        (None, "failed"),
        (float("nan"), "failed"),
        (float("inf"), "failed"),
    ],
)
@pytest.mark.parametrize("count", [1, 9, 10, 31])
def test_time_window_has_no_count_or_memory_criterion(wall: float | None, expected: str, count: int) -> None:
    rows = [{"status": "success", "wall_sec": wall, "max_rss_bytes": 20 * 1024**3}] * count
    assert selection.classify_baseline(rows).status == expected
    assert selection.classify_baseline(rows).count == count


def test_every_off_observation_contributes_and_old_failures_remain_visible() -> None:
    rows: list[dict[str, Any]] = [{"status": "success", "wall_sec": 0.05}] * 40
    rows.insert(0, {"status": "success", "wall_sec": 10})
    assert selection.classify_baseline(rows).status == "selected"
    rows[0] = {"status": "failure", "wall_sec": None, "error_message": "old failure"}
    assert selection.classify_baseline(rows).reason == "off: old failure"
    assert selection.classify_baseline([]).status == "pending"
    with pytest.raises(ValueError, match="off observations"):
        selection.classify_baseline([{"treatment": "proofs"}])


@pytest.mark.parametrize("proof_treatment", suites.PROOF_TREATMENTS)
def test_campaign_tops_up_all_baselines_before_proofs_and_reuses_all_cached_rows(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    proof_treatment: suites.ProofTreatment,
) -> None:
    prepare_corpus(tmp_path, contents=("(check (= 1 1))\n", "(check (= 2 2))\n"))
    suite = suites.resolve_suite("expanded", tmp_path)
    binary = tmp_path / "fake"
    binary.write_bytes(b"fake engine")
    target = make_target(binary_path=binary, binary_sha256=targets.sha256_file(binary))
    store = ReportStore(tmp_path / "report.jsonl")
    for i in range(13):
        store.append(
            make_record(
                i,
                started_at=f"2026-01-01T00:00:{i:02}Z",
                file_sha256=suite.files[0].sha256,
                binary_sha256=target.binary_sha256,
            )
        )
    calls: list[tuple[str, str]] = []

    def measured(*args: Any) -> collection.ProcessObservation:
        calls.append((args[2].sha256, args[3]))
        return collection.ProcessObservation(
            processes.TimingResult("success", processes.TimingRow(0.2, 1000), None), make_timing_summary()
        )

    monkeypatch.setattr(collection, "run_process", measured)
    monkeypatch.setattr(selection, "preflight_collection", lambda *_: None)
    result = selection.run_baseline_campaign(
        suite, target, store, 120, Console(file=io.StringIO()), rounds=3, treatment=proof_treatment
    )
    assert result is not None and result.files == suite.files and result.suite_mode
    assert calls[:3] == [(suite.files[1].sha256, "off")] * 3
    assert all(treatment == proof_treatment for _, treatment in calls[3:])
    assert len(calls) == 9
    key = CacheKey.for_endpoint(BenchmarkEndpoint(target, "off"), suite.files[0], 120)
    assert len(store.latest_records(key)) == 13
    calls.clear()
    selection.run_baseline_campaign(
        suite, target, store, 120, Console(file=io.StringIO()), rounds=3, treatment=proof_treatment
    )
    assert calls == []


def test_incomplete_baseline_prevents_any_proof_launch(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    prepare_corpus(tmp_path)
    plans = []
    monkeypatch.setattr(selection, "preflight_collection", lambda *_: None)
    monkeypatch.setattr(selection, "collect_rows", lambda _store, plan, *_: plans.append(plan))
    with pytest.raises(ValueError, match="finish normal-mode"):
        selection.run_baseline_campaign(
            suites.resolve_suite("expanded", tmp_path),
            make_target(),
            ReportStore(tmp_path / "report.jsonl"),
            120,
            Console(file=io.StringIO()),
            rounds=2,
        )
    assert len(plans) == 1 and all(run.treatment == "off" for run in plans[0].runs)
