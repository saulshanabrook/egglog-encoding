"""Suite terminal failures and guarded builds retain the ordinary runner boundary."""

from __future__ import annotations

import io
from dataclasses import replace
from pathlib import Path
from typing import Any

import pytest
from rich.console import Console

from benchmarking import collection, models, processes, suites, targets
from benchmarking.reports.store import ReportStore

from .corpus_fixtures import prepare_corpus
from .report_fixtures import make_record, make_target


@pytest.fixture
def prepared_environment(tmp_path: Path) -> tuple[Path, models.ResolvedTarget]:
    prepare_corpus(tmp_path)
    binary = tmp_path / "target/release/egglog-experimental"
    binary.parent.mkdir(parents=True)
    binary.write_bytes(b"fake engine")
    target = make_target(binary_path=binary, binary_sha256=targets.sha256_file(binary))
    return tmp_path, replace(target, row=replace(target.row, path=str(tmp_path)))


@pytest.mark.parametrize("status", ["failure", "timed-out"])
def test_failure_stops_its_treatment_for_suite_and_positional_requests(
    prepared_environment: tuple[Path, models.ResolvedTarget],
    monkeypatch: pytest.MonkeyPatch,
    status: models.Status,
) -> None:
    root, target = prepared_environment
    file = suites.resolve_suite("eggcc", root).files[0]
    store = ReportStore(root / "test.jsonl")
    calls: list[str] = []

    def measured(
        _binary: Path, _root: Path, _file: models.FileSpec, treatment: str, _timeout: int, _encoding: str
    ) -> collection.ProcessObservation:
        calls.append(treatment)
        return collection.ProcessObservation(
            processes.TimingResult(status, processes.TimingRow(), processes.ErrorRow("terminal error")), None
        )

    monkeypatch.setattr(collection, "run_process", measured)
    endpoints = (models.BenchmarkEndpoint(target, "off"), models.BenchmarkEndpoint(target, "proof-extraction"))
    plan = collection.build_collection_plan(store, target, endpoints, (file,), 30, 120, False, True)
    collection.collect_rows(store, plan, 120, Console(file=io.StringIO()))
    assert calls == ["off", "proof-extraction"]
    assert store.row_count == 2
    assert (
        collection.build_collection_plan(
            store, target, endpoints, (file,), 30, 120, False, True
        ).total_missing_observations
        == 0
    )
    assert (
        collection.build_collection_plan(store, target, endpoints, (file,), 30, 120, False).total_missing_observations
        == 0
    )
    for suite_mode in (False, True):
        assert (
            collection.build_collection_plan(
                store, target, endpoints, (file,), 1, 120, True, suite_mode
            ).total_missing_observations
            == 2
        )
    assert (
        collection.build_collection_plan(
            store, target, endpoints, (file,), 30, 121, False, True
        ).total_missing_observations
        == 60
    )


def test_any_selected_failure_prevents_automatic_topup(
    prepared_environment: tuple[Path, models.ResolvedTarget],
) -> None:
    root, target = prepared_environment
    file = suites.resolve_suite("eggcc", root).files[0]
    store = ReportStore(root / "test.jsonl")
    statuses: tuple[models.Status, ...] = ("timed-out", "success")
    for index, status in enumerate(statuses):
        row = make_record(
            index,
            started_at=f"2026-09-22T00:00:0{index}Z",
            status=status,
            binary_sha256=target.binary_sha256,
            file_sha256=file.sha256,
        )
        store.append(row)
    plan = collection.build_collection_plan(
        store, target, (models.BenchmarkEndpoint(target, "off"),), (file,), 30, 120, False, True
    )
    assert plan.total_missing_observations == 0
    assert plan.runs[0].cached_statuses == ("timed-out", "success")


def test_suite_build_is_guarded_and_single_job(
    prepared_environment: tuple[Path, models.ResolvedTarget],
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from dataclasses import replace

    from process_guard import MemoryGuard

    monkeypatch.delenv("CARGO_TARGET_DIR", raising=False)
    root, target = prepared_environment
    events: list[Any] = []

    class Guard:
        reason = None

        def start(self, pid: int) -> None:
            events.append(("guard", pid))

        def close(self) -> None:
            events.append("close")

    class Process:
        pid = 123

        def wait(self, timeout: float | None = None) -> int:
            assert timeout is None
            events.append("wait")
            return 0

    def build(args: list[str], **kwargs: Any) -> Process:
        assert args == ["cargo", "build", "--release", "-p", "egglog-experimental", "--jobs", "1"]
        assert kwargs["start_new_session"] is True
        events.append("build")
        return Process()

    monkeypatch.setenv("EGGLOG_BENCH_MEMORY_GUARD", "1")
    monkeypatch.setattr(MemoryGuard, "from_environment", lambda: Guard())
    monkeypatch.setattr(targets.subprocess, "Popen", build)
    monkeypatch.setattr(targets, "terminate_process_group", lambda _process: events.append("cleanup"))
    path, identity = targets.build_target(replace(target.row, path=str(root)), Console(file=io.StringIO()))
    assert path == target.binary_path and identity == target.binary_sha256
    assert events == ["build", ("guard", 123), "wait", "close", "cleanup"]


def test_cached_suite_label_keeps_exact_validation_error_without_building_or_screening(
    prepared_environment: tuple[Path, models.ResolvedTarget],
    monkeypatch: pytest.MonkeyPatch,
    capsys: Any,
) -> None:
    import json

    from benchmarking import benchmark

    root, target = prepared_environment
    suite = suites.resolve_suite("eggcc", root)
    file = suite.files[0]
    report = root / "rows.jsonl"
    store = ReportStore(report)
    for treatment in ("off", "proof-extraction"):
        for index in range(3):
            row = make_record(
                index,
                started_at="2026-01-01T00:00:00Z",
                binary_sha256=target.binary_sha256,
                file_sha256=file.sha256,
                treatment=treatment,
                target_label="cached",
            )
            row["target_path"] = str(root)
            store.append(row)
    manifest = json.loads(suite.manifest.path.read_text())
    manifest["outcomes"] = [
        {
            "file_sha256": file.sha256,
            "fact_directory_sha256": "",
            "binary_sha256": target.binary_sha256,
            "timeout_sec": 120,
            "disequality_encoding": "nee",
            "kind": "validation",
            "policy": suites.VALIDATION_POLICY,
            "status": "failure",
            "reason": "strict witness failed",
        }
    ]
    suite.manifest.path.write_text(json.dumps(manifest))
    monkeypatch.setattr(benchmark, "__file__", str(root / "benchmarking/benchmark.py"))
    monkeypatch.setattr(benchmark, "git_root_for_path", lambda _: root)
    monkeypatch.setattr(
        collection, "build_resolved_target", lambda *_: pytest.fail("fully cached label must not build")
    )
    monkeypatch.setattr(collection, "run_process", lambda *_: pytest.fail("fully cached label must not collect"))
    before = report.read_bytes()
    assert (
        benchmark.main(
            [
                "--suite",
                "eggcc",
                "--target",
                "cached=",
                "--treatment",
                "proof-extraction",
                "--rounds",
                "2",
                "--timeout-sec",
                "120",
                "--report",
                str(report),
                "--format",
                "markdown",
            ]
        )
        == 0
    )
    assert "strict witness failed" in capsys.readouterr().out
    assert report.read_bytes() == before
