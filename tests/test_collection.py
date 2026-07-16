"""Test cache-aware plans, estimates, and integrated record collection."""

from __future__ import annotations

import io
import json
import sys
from pathlib import Path

import pytest

from benchmarking import collection, models, processes
from benchmarking import output as runner_output
from benchmarking.reports.database import ReportDatabase
from benchmarking.reports.results import EstimateAggregate

from .conftest import ROOT, make_record, make_spec, make_target, make_timing_summary, write_report


def test_estimate_model_is_exact_only_and_updates_from_successful_processes() -> None:
    exact_key = models.EstimateKey("sha256:bin", "sha256:file", "off", 120)
    other_key = models.EstimateKey("sha256:other", "sha256:file", "off", 120)
    model = collection.EstimateModel.from_aggregates(
        (EstimateAggregate(exact_key, 2, 6.0), EstimateAggregate(other_key, 5, 250.0))
    )
    other_timeout_key = models.EstimateKey("sha256:bin", "sha256:file", "off", 60)

    assert model.process_mean(exact_key) == pytest.approx(3.0)
    assert model.estimate_processes(exact_key, 3) == collection.DurationEstimate(seconds=9.0, unknown_processes=0)
    assert model.estimate_processes(other_timeout_key, 3) == collection.DurationEstimate(
        seconds=None, unknown_processes=3
    )

    model.record_process(exact_key, processes.TimingResult("success", processes.TimingRow(wall_sec=4.0), None))

    assert model.process_mean(exact_key) == pytest.approx(10.0 / 3.0)


def test_collection_plan_counts_cache_and_missing_rows(tmp_path: Path) -> None:
    report = tmp_path / "report.jsonl"
    write_report(report, make_record(0, started_at="2026-07-04T12:00:00Z", wall_sec=1.0))
    target = make_target()
    file_spec = models.FileSpec("file.egg", ROOT / "file.egg", "sha256:file")
    spec = make_spec(file_spec)

    with ReportDatabase(report) as database:
        plan = collection.build_collection_plan(database, target, spec, False)
        force_plan = collection.build_collection_plan(database, target, spec, True)

    assert plan.cells[0].cached_statuses == ("success",)
    assert plan.cells[0].missing_observations == 1
    assert plan.total_planned_processes == 2
    assert force_plan.cells[0].missing_observations == 2
    assert force_plan.total_planned_processes == 3


def test_collection_plan_does_not_reuse_main_rows_for_dd(tmp_path: Path) -> None:
    report = tmp_path / "report.jsonl"
    write_report(
        report,
        make_record(
            0,
            started_at="2026-07-04T12:00:00Z",
            backend="main",
            treatment="term",
            wall_sec=1.0,
        ),
    )
    target = make_target()
    file_spec = models.FileSpec("file.egg", ROOT / "file.egg", "sha256:file")
    spec = models.BenchmarkSpec(
        files=(file_spec,),
        treatments=("term",),
        rounds=1,
        timeout_sec=120,
        backends=("main", "dd"),
    )

    with ReportDatabase(report) as database:
        plan = collection.build_collection_plan(database, target, spec, False)

    main_cell, dd_cell = plan.cells
    assert main_cell.backend == "main"
    assert main_cell.missing_observations == 0
    assert dd_cell.backend == "dd"
    assert dd_cell.missing_observations == 1


def test_collection_plan_writes_human_output_to_stderr(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    report = tmp_path / "report.jsonl"
    write_report(report, make_record(0, started_at="2026-07-04T12:00:00Z", wall_sec=1.0))
    target_label = "target [red]literal[/red] x[/blue]"
    file_label = "[/].egg"
    target = make_target(target_label=target_label)
    file_spec = models.FileSpec(file_label, ROOT / "file.egg", "sha256:file")
    stream = io.StringIO()
    monkeypatch.setattr(sys, "stderr", stream)
    output = runner_output.RunnerOutput()

    with ReportDatabase(report) as database:
        plan = collection.build_collection_plan(database, target, make_spec(file_spec), False)
        model = collection.EstimateModel.from_aggregates(database.successful_estimate_aggregates())
        collection.emit_collection_plan(output, plan, model)

    output_text = stream.getvalue()
    assert "cache and estimate plan" in output_text
    assert target_label in output_text
    assert file_label in output_text
    assert "1/2" in output_text
    assert "Estimated fresh collection time" in output_text


def test_collect_rows_appends_process_and_ruleset_timing_together(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    report = tmp_path / "report.jsonl"
    file_spec = models.FileSpec("file.egg", ROOT / "file.egg", "sha256:file")
    spec = models.BenchmarkSpec((file_spec,), ("off",), 1, 120)
    target = make_target(binary_path=ROOT / "egglog-experimental")
    summary = make_timing_summary()
    success = processes.TimingResult("success", processes.TimingRow(wall_sec=1.25, max_rss_bytes=4096), None)
    monkeypatch.setattr(collection, "run_startup_warmup", lambda *_args: success)
    monkeypatch.setattr(
        collection,
        "run_process",
        lambda *_args: collection.ProcessObservation(success, summary),
    )

    with ReportDatabase(report) as database:
        plan = collection.build_collection_plan(database, target, spec, False)
        startup_warmup = collection.preflight_collection(plan, spec)
        collection.collect_rows(
            database,
            plan,
            spec,
            runner_output.RunnerOutput(),
            collection.EstimateModel(),
            startup_warmup,
        )
        selected = database.selected_statuses(models.EstimateKey.for_cell(target, file_spec, "main", "off", 120), 1)

    persisted = json.loads(report.read_text(encoding="utf-8"))
    assert "row_index" not in persisted
    assert persisted["wall_sec"] == 1.25
    assert persisted["timing_summary"] == summary
    assert selected == ("success",)


def test_collect_rows_rejects_unsupported_timing_summary_before_append(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    report = tmp_path / "report.jsonl"
    file_spec = models.FileSpec("file.egg", ROOT / "file.egg", "sha256:file")
    spec = models.BenchmarkSpec((file_spec,), ("off",), 1, 120)
    target = make_target(binary_path=ROOT / "egglog-experimental")

    def write_unsupported_summary(
        command: list[str],
        _checkout_path: Path,
        _timeout_sec: int,
    ) -> processes.TimingResult:
        summary_path = Path(command[command.index("--timing-summary") + 1])
        summary_path.write_text(
            json.dumps({"schema_version": 1, "rulesets": []}),
            encoding="utf-8",
        )
        return processes.TimingResult("success", processes.TimingRow(wall_sec=1.0), None)

    monkeypatch.setattr(collection, "run_command", write_unsupported_summary)

    with ReportDatabase(report) as database:
        plan = collection.build_collection_plan(database, target, spec, False)
        startup_warmup = processes.TimingResult("success", processes.TimingRow(wall_sec=0.1), None)
        with pytest.raises(ValueError, match=r"unsupported timing summary.*1"):
            collection.collect_rows(
                database,
                plan,
                spec,
                runner_output.RunnerOutput(),
                collection.EstimateModel(),
                startup_warmup,
            )

    assert report.read_text(encoding="utf-8") == ""
