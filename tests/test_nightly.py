"""Exercise nightly report publication without builds or benchmarks."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

import pytest

from benchmarking import collection, models, processes, targets, workloads
from benchmarking.reports.store import ReportStore
from scripts import nightly_bench as nightly

from .report_fixtures import make_target, make_timing_summary


@pytest.fixture
def nightly_case(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> dict[str, Any]:
    path = tmp_path / "file.egg"
    path.write_text("(check (= 1 1))\n")
    file = models.FileSpec("file.egg", path, targets.sha256_file(path))
    resolved = {}
    for label in ("branch", "main"):
        binary = tmp_path / label
        binary.write_text(label)
        resolved[label] = make_target(target_label=label, binary_path=binary, binary_sha256=targets.sha256_file(binary))
    case: dict[str, Any] = {
        "targets": resolved,
        "builds": [],
        "runs": [],
        "preflights": [],
        "fetches": [],
        "file": file,
    }

    def resolve(
        requests: tuple[collection.BenchmarkRequest, ...], *_args: Any, **_kwargs: Any
    ) -> dict[models.TargetRequest, models.ResolvedTarget]:
        request = requests[0].endpoint.target
        assert request.label is not None
        case["builds"].append(request.label)
        assert [item.endpoint.treatment for item in requests] == ["off", "proof-testing"]
        assert all(item.endpoint.target == request and item.files == (file,) for item in requests)
        return {request: resolved[request.label]}

    def measure(
        binary: Path, _cwd: Path, _file: models.FileSpec, treatment: str, *_args: Any
    ) -> collection.ProcessObservation:
        case["runs"].append((binary.name, treatment))
        return collection.ProcessObservation(
            processes.TimingResult("success", processes.TimingRow(0.01, 1000), None), make_timing_summary()
        )

    monkeypatch.setattr(workloads, "resolve_files", lambda *_args: (file,))
    monkeypatch.setattr(collection, "resolve_requests", resolve)
    monkeypatch.setattr(
        collection, "preflight_collection", lambda plan, *_args: case["preflights"].append(plan.target.display_label)
    )
    monkeypatch.setattr(collection, "run_process", measure)
    monkeypatch.setattr(targets, "run_text", lambda command, *_a, **_k: case["fetches"].append(command))
    return case


def test_collects_checked_and_off_once_and_renders_cached_reports(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, nightly_case: dict[str, Any]
) -> None:
    output = tmp_path / "output"
    assert nightly.main([str(output)]) == 0
    assert nightly_case["builds"] == ["branch", "main"]
    assert nightly_case["fetches"] == [["git", "fetch", "origin", "+refs/heads/main:refs/remotes/origin/main"]]
    assert nightly_case["runs"] == [
        (label, treatment) for label in ("branch", "main") for treatment in ("off", "proof-testing")
    ]
    store = ReportStore(output / "index.jsonl")
    assert store.row_count == 4 and {row["timeout_sec"] for row in store.records} == {120}
    before = store.path.read_bytes()
    monkeypatch.setattr(collection, "resolve_requests", lambda *a, **k: pytest.fail("render must not resolve/build"))
    monkeypatch.setattr(collection, "collect_rows", lambda *a, **k: pytest.fail("render must not collect"))
    nightly._render(
        argparse.Namespace(output_dir=output, rounds=1, timeout_sec=120),
        store.grouped_report(),
        nightly_case["targets"],
        (nightly_case["file"],),
    )
    assert store.path.read_bytes() == before
    assert (output / "index.html").is_file()
    assert "proof-testing" in (output / "branch-vs-main.md").read_text()
    assert json.loads((output / "index-grouped.json").read_text())["groups"]


@pytest.mark.parametrize("after_rows", [0, 1, 2])
def test_collection_error_keeps_completed_rows_and_renders_missing_endpoints(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, nightly_case: dict[str, Any], after_rows: int
) -> None:
    measure = collection.run_process
    calls = 0

    def interrupted(*args: Any) -> collection.ProcessObservation:
        nonlocal calls
        calls += 1
        if calls > after_rows:
            raise OSError("collection failed")
        return measure(*args)

    monkeypatch.setattr(collection, "run_process", interrupted)
    output = tmp_path / "output"
    assert nightly.main([str(output)]) == 1
    assert ReportStore(output / "index.jsonl").row_count == after_rows
    assert calls == after_rows + 1
    assert (output / "index.html").is_file()
    assert "collection failed" in (output / "status.txt").read_text()


def test_unsupported_main_is_fatal_and_preserves_branch_rows(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, nightly_case: dict[str, Any]
) -> None:
    def preflight(plan: collection.CollectionPlan, *_args: Any) -> None:
        if plan.target.display_label == "main":
            raise ValueError("main does not support --memory-limit-bytes")

    monkeypatch.setattr(collection, "preflight_collection", preflight)
    output = tmp_path / "output"
    assert nightly.main([str(output)]) == 1
    assert nightly_case["runs"] == [("branch", "off"), ("branch", "proof-testing")]
    assert ReportStore(output / "index.jsonl").row_count == 2
    assert "missing" in (output / "branch-vs-main.md").read_text().lower()


def test_fetch_failure_preserves_branch_and_never_builds_main(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, nightly_case: dict[str, Any]
) -> None:
    def failed(*_args: Any, **_kwargs: Any) -> str:
        raise OSError("fetch failed")

    monkeypatch.setattr(targets, "run_text", failed)
    output = tmp_path / "output"
    assert nightly.main([str(output)]) == 1
    assert nightly_case["builds"] == ["branch"]
    assert nightly_case["runs"] == [("branch", "off"), ("branch", "proof-testing")]
    assert ReportStore(output / "index.jsonl").row_count == 2
    assert "fetch failed" in (output / "status.txt").read_text()


def test_native_control_failure_is_retained_before_stopping_all_collection(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, nightly_case: dict[str, Any]
) -> None:
    measure = collection.run_process

    def failed(*args: Any) -> collection.ProcessObservation:
        measure(*args)
        return collection.ProcessObservation(
            processes.TimingResult(
                "failure",
                processes.TimingRow(0.01),
                processes.ErrorRow("native setup failed", exit_code=87),
                stop_collection=True,
            ),
            None,
        )

    monkeypatch.setattr(collection, "run_process", failed)
    output = tmp_path / "output"
    assert nightly.main([str(output)]) == 1
    assert nightly_case["builds"] == ["branch"]
    assert nightly_case["runs"] == [("branch", "off")]
    rows = ReportStore(output / "index.jsonl").records
    assert len(rows) == 1 and rows[0]["error_exit_code"] == 87
    assert "failed observation was retained" in (output / "status.txt").read_text()
    assert (output / "index.html").is_file()


def test_identical_binaries_share_rows_without_fabricated_distinct_endpoints(
    tmp_path: Path, nightly_case: dict[str, Any]
) -> None:
    nightly_case["targets"]["main"] = nightly_case["targets"]["branch"]
    output = tmp_path / "output"
    assert nightly.main([str(output)]) == 0
    assert len(nightly_case["runs"]) == 2
    assert "same executable" in (output / "branch-vs-main.md").read_text()
    assert all(
        group["labels"] == ["branch", "main"]
        for group in json.loads((output / "index-grouped.json").read_text())["groups"]
    )


def test_ordinary_workload_failure_keeps_other_conditions(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, nightly_case: dict[str, Any]
) -> None:
    measure = collection.run_process

    def fails_once(*args: Any) -> collection.ProcessObservation:
        result = measure(*args)
        if args[0].name == "branch" and args[3] == "proof-testing":
            return collection.ProcessObservation(
                processes.TimingResult("failure", processes.TimingRow(0.01), processes.ErrorRow("bad proof")), None
            )
        return result

    monkeypatch.setattr(collection, "run_process", fails_once)
    output = tmp_path / "output"
    assert nightly.main([str(output)]) == 0
    rows = ReportStore(output / "index.jsonl").records
    assert len(rows) == 4 and sum(row["status"] == "failure" for row in rows) == 1
    assert rows[1]["error_message"] == "bad proof"
    assert nightly_case["runs"][-2:] == [("main", "off"), ("main", "proof-testing")]
    assert "failure row selected" in (output / "branch-vs-main.md").read_text()


def test_round_and_workload_timeout_overrides_are_preserved(tmp_path: Path, nightly_case: dict[str, Any]) -> None:
    output = tmp_path / "output"
    assert nightly.main([str(output), "--rounds", "2", "--timeout-sec", "7"]) == 0
    rows = ReportStore(output / "index.jsonl").records
    assert len(rows) == 8 and {row["timeout_sec"] for row in rows} == {7}


def test_render_failure_preserves_rows_and_status(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, nightly_case: dict[str, Any]
) -> None:
    def failed(*_args: Any) -> None:
        raise ValueError("render failed")

    monkeypatch.setattr(nightly, "_render", failed)
    output = tmp_path / "output"
    assert nightly.main([str(output)]) == 1
    assert ReportStore(output / "index.jsonl").row_count == 4
    assert "render failed" in (output / "status.txt").read_text()
    assert (output / "index.html").is_file()


def test_nightly_preserves_its_fixture_roster_and_make_bootstrap() -> None:
    makefile = (nightly.REPO_ROOT / "Makefile").read_text()
    assert "nightly: nightly-uv nightly-rustup" in makefile
    assert "nightly-local: nightly-uv nightly-rustup" in makefile
    assert len(nightly.WORKLOADS) == 7 and len(set(nightly.WORKLOADS)) == 7
    assert all((nightly.REPO_ROOT / path).is_file() for path in nightly.WORKLOADS)
