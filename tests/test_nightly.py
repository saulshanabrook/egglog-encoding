"""Exercise bounded nightly orchestration without building or benchmarking."""

from __future__ import annotations

import os
from pathlib import Path
from typing import Any

import pytest

from benchmarking import collection, models, processes, targets
from benchmarking.reports.store import ReportStore
from process_guard import ResourceStopped
from scripts import nightly_bench as nightly

from .report_fixtures import make_target, make_timing_summary


@pytest.fixture
def nightly_case(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> dict[str, Any]:
    file = models.FileSpec("file.egg", tmp_path / "file.egg", "sha256:file")
    resolved = {}
    for label in ("branch", "main"):
        binary = tmp_path / label
        binary.write_text(label)
        resolved[label] = make_target(target_label=label, binary_path=binary, binary_sha256=targets.sha256_file(binary))
    case: dict[str, Any] = {"targets": resolved, "builds": [], "runs": [], "renders": [], "file": file}

    def resolve(groups: Any, *_args: Any, **_kwargs: Any) -> dict[models.TargetRequest, models.ResolvedTarget]:
        request = groups[0][0]
        case["builds"].append(request.label)
        assert processes.COLLECTION_DEADLINE.get() is not None
        return {request: resolved[request.label]}

    def measure(
        binary: Path, _cwd: Path, _file: models.FileSpec, treatment: str, *_args: Any
    ) -> collection.ProcessObservation:
        case["runs"].append((binary.name, treatment))
        return collection.ProcessObservation(
            processes.TimingResult("success", processes.TimingRow(0.01, 1000), None), make_timing_summary()
        )

    write = nightly.write_interactive_report

    def render(store: Any, comparison: models.ComparisonSpec, path: Path) -> Path:
        case["renders"].append((len(store.records), comparison))
        return write(store, comparison, path)

    monkeypatch.setattr(nightly, "resolve_files", lambda *_args: (file,))
    monkeypatch.setattr(nightly, "resolve_targets", resolve)
    monkeypatch.setattr(nightly, "preflight_collection", lambda *_args: None)
    monkeypatch.setattr(collection, "run_process", measure)
    monkeypatch.setattr(nightly, "write_interactive_report", render)
    return case


def test_nightly_builds_once_reuses_off_and_publishes_between_comparisons(
    tmp_path: Path, nightly_case: dict[str, Any]
) -> None:
    output = tmp_path / "output"
    previous_path = os.environ.get("PATH")
    previous_guard = os.environ.get("EGGLOG_BENCH_MEMORY_GUARD")
    assert nightly.main([str(output)]) == 0
    assert nightly_case["builds"] == ["branch", "main"]
    assert nightly_case["runs"] == (
        [("branch", mode) for _ in range(6) for mode in ("off", "proofs")]
        + [("main", mode) for _ in range(6) for mode in ("off", "proofs")]
        + [(label, mode) for mode in ("term", "proof-extraction") for label in ("branch", "main") for _ in range(6)]
    )
    assert [count for count, _comparison in nightly_case["renders"]] == [12, 24, 30, 36, 42, 48, 48]
    comparison = nightly_case["renders"][-1][1]
    assert comparison.candidate.target.display_label == "branch"
    assert comparison.baseline.target.display_label == "main"
    assert comparison.candidate.treatment == comparison.baseline.treatment == "proofs"
    assert comparison.rounds == 6
    assert {row["timeout_sec"] for row in ReportStore(output / "index.jsonl").records} == {120}
    assert processes.COLLECTION_DEADLINE.get() is None
    assert os.environ.get("PATH") == previous_path
    assert os.environ.get("EGGLOG_BENCH_MEMORY_GUARD") == previous_guard


@pytest.mark.parametrize("resource_stop", [False, True])
def test_nightly_retains_partial_results_and_stops_all_later_modes(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, nightly_case: dict[str, Any], resource_stop: bool
) -> None:
    measure = collection.run_process
    calls = 0

    def interrupted(*args: Any) -> collection.ProcessObservation:
        nonlocal calls
        calls += 1
        if calls == 2:
            if resource_stop:
                return collection.ProcessObservation(
                    processes.TimingResult(
                        "failure",
                        processes.TimingRow(),
                        processes.ErrorRow("host memory pressure"),
                        resource_stopped=True,
                    ),
                    None,
                )
            raise processes.BudgetExpired("test budget")
        return measure(*args)

    monkeypatch.setattr(collection, "run_process", interrupted)
    output = tmp_path / "output"
    assert nightly.main([str(output)]) == int(resource_stop)
    assert calls == 2
    records = ReportStore(output / "index.jsonl").records
    assert len(records) == (2 if resource_stop else 1)
    assert records[-1]["status"] == ("failure" if resource_stop else "success")
    assert len(nightly_case["renders"]) == 1
    comparison = nightly_case["renders"][0][1]
    assert "Partial nightly" in " ".join(comparison.report_notes)
    assert (output / "index.html").is_file()
    assert processes.COLLECTION_DEADLINE.get() is None


@pytest.mark.parametrize("stage", ["build", "preflight"])
def test_nightly_safety_stop_before_measurements_still_publishes(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, nightly_case: dict[str, Any], stage: str
) -> None:
    calls = []

    def stopped(*_args: Any, **_kwargs: Any) -> Any:
        calls.append(stage)
        raise ResourceStopped("resource guard refused launch")

    monkeypatch.setattr(nightly, "resolve_targets" if stage == "build" else "preflight_collection", stopped)
    output = tmp_path / "output"
    assert nightly.main([str(output)]) == 1
    assert calls == [stage]
    assert not nightly_case["runs"]
    assert not ReportStore(output / "index.jsonl").records
    assert (output / "index.html").is_file()


@pytest.mark.parametrize("missing_main", [False, True])
def test_nightly_headline_falls_back_without_duplicate_endpoint_or_fabricated_identity(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, nightly_case: dict[str, Any], missing_main: bool
) -> None:
    if missing_main:
        resolve = nightly.resolve_targets

        def main_unavailable(
            groups: Any, *args: Any, **kwargs: Any
        ) -> dict[models.TargetRequest, models.ResolvedTarget]:
            if groups[0][0].label == "main":
                raise ValueError("main cannot build")
            return resolve(groups, *args, **kwargs)

        monkeypatch.setattr(nightly, "resolve_targets", main_unavailable)
    else:
        nightly_case["targets"]["main"] = nightly_case["targets"]["branch"]
    assert nightly.main([str(tmp_path / "output"), "--rounds", "1"]) == 0
    assert len(nightly_case["runs"]) == 4
    comparison = nightly_case["renders"][-1][1]
    assert comparison.candidate.treatment == "proofs"
    assert comparison.baseline.treatment == "off"
    assert comparison.candidate.cache_identity != comparison.baseline.cache_identity
    assert any("Initial comparison uses branch proofs / off" in note for note in comparison.report_notes)


def test_nightly_reserves_rendering_time_with_one_shared_deadline(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, nightly_case: dict[str, Any]
) -> None:
    deadlines = []
    resolve = nightly.resolve_targets

    def capture(*args: Any, **kwargs: Any) -> Any:
        deadlines.append(processes.COLLECTION_DEADLINE.get())
        return resolve(*args, **kwargs)

    monkeypatch.setattr(nightly.time, "monotonic", lambda: 100.0)
    monkeypatch.setattr(nightly, "resolve_targets", capture)
    assert nightly.main([str(tmp_path / "output"), "--rounds", "1", "--budget-sec", "120"]) == 0
    assert deadlines == [160.0, 160.0]


def test_nightly_ordinary_failure_stops_only_its_file_and_mode(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, nightly_case: dict[str, Any]
) -> None:
    measure = collection.run_process

    def sometimes_fails(*args: Any) -> collection.ProcessObservation:
        observation = measure(*args)
        if args[0].name == "branch" and args[3] == "proofs":
            return collection.ProcessObservation(
                processes.TimingResult("failure", processes.TimingRow(0.01), processes.ErrorRow("bad rule")), None
            )
        return observation

    monkeypatch.setattr(collection, "run_process", sometimes_fails)
    output = tmp_path / "output"
    assert nightly.main([str(output)]) == 0
    assert nightly_case["runs"].count(("branch", "proofs")) == 1
    for label in ("branch", "main"):
        for mode in ("off", "proofs", "term", "proof-extraction"):
            if (label, mode) != ("branch", "proofs"):
                assert nightly_case["runs"].count((label, mode)) == 6
    store = ReportStore(output / "index.jsonl")
    assert store.row_count == 43
    assert sum(row["status"] == "failure" for row in store.records) == 1
