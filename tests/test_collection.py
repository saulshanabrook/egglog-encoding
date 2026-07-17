"""Test cache-aware plans, estimates, and integrated record collection."""

from __future__ import annotations

import io
import json
from pathlib import Path

import pytest
from rich.console import Console

from benchmarking import collection, models, processes, targets
from benchmarking import output as runner_output
from benchmarking.reports.store import EstimateAggregate, ReportStore

from .conftest import ROOT, make_record, make_target, make_timing_summary, write_report


def endpoint(
    target: models.ResolvedTarget,
    backend: models.Backend = "main",
    treatment: models.Treatment = "off",
) -> models.BenchmarkEndpoint:
    return models.BenchmarkEndpoint(target, backend, treatment)


def planned_run(
    target: models.ResolvedTarget,
    *,
    filename: str = "file.egg",
    treatment: models.Treatment = "off",
    required: int = 6,
    cached: tuple[models.Status, ...] = (),
    missing: int | None = None,
) -> collection.BenchmarkRunPlan:
    """Construct one exact cache cell for collection-output tests."""

    file_sha = f"sha256:{filename}"
    file_spec = models.FileSpec(filename, ROOT / filename, file_sha)
    return collection.BenchmarkRunPlan(
        file=file_spec,
        backend="main",
        treatment=treatment,
        required_rows=required,
        cached_statuses=cached,
        missing_observations=required - len(cached) if missing is None else missing,
        estimate_key=models.EstimateKey.for_endpoint(endpoint(target, treatment=treatment), file_spec, 120),
    )


def rendered_collection_plan(
    plan: collection.CollectionPlan,
    estimate_model: collection.EstimateModel,
    *,
    width: int = 120,
) -> str:
    """Render one operational summary without coupling tests to process stderr."""

    stream = io.StringIO()
    output = runner_output.RunnerOutput()
    output.console = Console(file=stream, width=width, color_system=None)
    collection.emit_collection_plan(output, plan, estimate_model)
    return stream.getvalue().rstrip()


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
    selected_endpoint = endpoint(target)

    store = ReportStore(report)
    plan = collection.build_collection_plan(store, target, (selected_endpoint,), (file_spec,), 2, 120, False)
    force_plan = collection.build_collection_plan(store, target, (selected_endpoint,), (file_spec,), 2, 120, True)

    assert plan.runs[0].cached_statuses == ("success",)
    assert plan.runs[0].missing_observations == 1
    assert plan.total_missing_observations == 1
    assert force_plan.runs[0].missing_observations == 2
    assert force_plan.total_missing_observations == 2


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
    endpoints = (endpoint(target, "main", "term"), endpoint(target, "dd", "term"))

    plan = collection.build_collection_plan(ReportStore(report), target, endpoints, (file_spec,), 1, 120, False)

    main_run, dd_run = plan.runs
    assert main_run.backend == "main"
    assert main_run.missing_observations == 0
    assert dd_run.backend == "dd"
    assert dd_run.missing_observations == 1


def test_pair_collection_reuses_each_endpoint_independently_and_force_runs_both(tmp_path: Path) -> None:
    report = tmp_path / "report.jsonl"
    write_report(
        report,
        make_record(0, started_at="2026-07-04T12:00:00Z", backend="main", treatment="off"),
    )
    target = make_target()
    file_spec = models.FileSpec("file.egg", ROOT / "file.egg", "sha256:file")
    endpoints = (endpoint(target, "main", "off"), endpoint(target, "main", "proofs"))

    store = ReportStore(report)
    plan = collection.build_collection_plan(store, target, endpoints, (file_spec,), 1, 120, False)
    forced = collection.build_collection_plan(store, target, endpoints, (file_spec,), 1, 120, True)

    baseline, candidate = plan.runs
    assert baseline.cached_statuses == ("success",)
    assert baseline.missing_observations == 0
    assert candidate.cached_statuses == ()
    assert candidate.missing_observations == 1
    assert [run.missing_observations for run in forced.runs] == [1, 1]


@pytest.mark.parametrize("width", [80, 120])
def test_fully_cached_six_file_plan_is_one_line(width: int) -> None:
    target_label = "target [red]literal[/red] x[/blue]"
    target = make_target(target_label=target_label)
    filenames = (
        "math-microbenchmark.egg",
        "eggcc-2mm-pass1.egg",
        "pointer-analysis-small.egg",
        "hardboiled_conv1d_32.egg",
        "luminal-llama.egg",
        "herbie.egg",
    )
    treatments: tuple[models.Treatment, ...] = ("off", "proofs")
    runs = tuple(
        planned_run(target, filename=filename, treatment=treatment, cached=("success",) * 6)
        for filename in filenames
        for treatment in treatments
    )

    rendered = rendered_collection_plan(
        collection.CollectionPlan(target, runs), collection.EstimateModel(), width=width
    )

    assert rendered == f"{target_label}: 72/72 runs cached · nothing to collect"


def test_cached_failure_and_timeout_are_explicit() -> None:
    target = make_target()
    run = planned_run(
        target,
        cached=("success", "success", "success", "success", "failure", "timed-out"),
    )

    rendered = rendered_collection_plan(collection.CollectionPlan(target, (run,)), collection.EstimateModel())

    assert rendered == "abc123: 6/6 runs cached (1 failed, 1 timed out) · nothing to collect"


def test_partial_and_forced_plans_show_only_total_work_and_coarse_eta() -> None:
    target = make_target()
    partial = planned_run(target, cached=("success",) * 4)
    forced = planned_run(target, cached=("success",) * 6, missing=6)
    model = collection.EstimateModel(
        {
            partial.estimate_key: (4, 46.0),
        }
    )

    partial_text = rendered_collection_plan(collection.CollectionPlan(target, (partial,)), model)
    forced_text = rendered_collection_plan(collection.CollectionPlan(target, (forced,)), model)

    assert partial_text == "abc123: 4/6 runs cached · collecting 2 fresh · ETA ~23s"
    assert forced_text == "abc123: 6/6 runs cached · collecting 6 fresh · ETA ~1m09s"


def test_unknown_and_mixed_estimates_name_unestimated_runs() -> None:
    target = make_target()
    known = planned_run(target, filename="known.egg", required=3, cached=("success", "success"))
    unknown = planned_run(target, filename="unknown.egg", required=3, cached=("success",))
    plan = collection.CollectionPlan(target, (known, unknown))

    all_unknown = rendered_collection_plan(plan, collection.EstimateModel())
    mixed = rendered_collection_plan(plan, collection.EstimateModel({known.estimate_key: (1, 23.0)}))

    assert all_unknown == "abc123: 3/6 runs cached · collecting 3 fresh · ETA unknown (3 unestimated runs)"
    assert mixed == "abc123: 3/6 runs cached · collecting 3 fresh · ETA at least 23s; 2 unestimated runs"


@pytest.mark.parametrize(
    ("seconds", "expected"),
    [
        (0.4, "<1s"),
        (23.4, "~23s"),
        (102.0, "~1m42s"),
        (3720.0, "~1h02m"),
    ],
)
def test_collection_estimates_use_coarse_planning_units(seconds: float, expected: str) -> None:
    assert collection.format_duration(seconds) == expected


def test_collect_rows_appends_process_and_ruleset_timing_together(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    report = tmp_path / "report.jsonl"
    file_spec = models.FileSpec("file.egg", ROOT / "file.egg", "sha256:file")
    target = make_target(binary_path=ROOT / "egglog-experimental")
    selected_endpoint = endpoint(target)
    summary = make_timing_summary()
    success = processes.TimingResult("success", processes.TimingRow(wall_sec=1.25, max_rss_bytes=4096), None)
    monkeypatch.setattr(collection, "run_preflight", lambda *_args: success)
    monkeypatch.setattr(
        collection,
        "run_process",
        lambda *_args: collection.ProcessObservation(success, summary),
    )

    store = ReportStore(report)
    plan = collection.build_collection_plan(store, target, (selected_endpoint,), (file_spec,), 1, 120, False)
    collection.preflight_collection(plan, 120)
    collection.collect_rows(
        store,
        plan,
        120,
        runner_output.RunnerOutput(),
        collection.EstimateModel(),
    )
    key = models.EstimateKey.for_endpoint(selected_endpoint, file_spec, 120)
    selected = store.selected_statuses_for_keys((key,), 1)[key]

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
    benchmark_file = tmp_path / "file.egg"
    benchmark_file.write_text("(check (= 1 1))\n", encoding="utf-8")
    file_spec = models.FileSpec("file.egg", benchmark_file, targets.sha256_file(benchmark_file))
    target = make_target(binary_path=ROOT / "egglog-experimental")
    selected_endpoint = endpoint(target)

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

    store = ReportStore(report)
    plan = collection.build_collection_plan(store, target, (selected_endpoint,), (file_spec,), 1, 120, False)
    with pytest.raises(ValueError, match=r"unsupported timing summary.*1"):
        collection.collect_rows(
            store,
            plan,
            120,
            runner_output.RunnerOutput(),
            collection.EstimateModel(),
        )

    assert report.read_text(encoding="utf-8") == ""


@pytest.mark.parametrize("mutated_input", ("file", "facts"))
def test_collect_rows_rejects_mutated_workload_before_append(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    mutated_input: str,
) -> None:
    benchmark_file = tmp_path / "file.egg"
    benchmark_file.write_text("(check (= 1 1))\n", encoding="utf-8")
    facts = tmp_path / "facts"
    facts.mkdir()
    fact_file = facts / "input.tsv"
    fact_file.write_text("before\n", encoding="utf-8")
    file_spec = models.FileSpec(
        benchmark_file.name,
        benchmark_file,
        targets.sha256_file(benchmark_file),
        facts,
        targets.sha256_directory(facts),
    )
    target = make_target(binary_path=ROOT / "egglog-experimental")
    selected_endpoint = endpoint(target)

    def mutate_workload(
        command: list[str],
        _checkout_path: Path,
        _timeout_sec: int,
    ) -> processes.TimingResult:
        summary_path = Path(command[command.index("--timing-summary") + 1])
        summary_path.write_text(json.dumps(make_timing_summary()), encoding="utf-8")
        if mutated_input == "file":
            benchmark_file.write_text("(check (= 2 2))\n", encoding="utf-8")
        else:
            fact_file.write_text("after\n", encoding="utf-8")
        return processes.TimingResult("success", processes.TimingRow(wall_sec=1.0), None)

    monkeypatch.setattr(collection, "run_command", mutate_workload)
    store = ReportStore(tmp_path / "report.jsonl")
    plan = collection.build_collection_plan(store, target, (selected_endpoint,), (file_spec,), 1, 120, False)

    with pytest.raises(ValueError, match=r"workload changed during execution: file\.egg"):
        collection.collect_rows(store, plan, 120, runner_output.RunnerOutput(), collection.EstimateModel())

    assert store.row_count == 0
    assert store.path.read_text(encoding="utf-8") == ""


def test_redirected_collection_logs_each_run_and_one_status_summary(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    target = make_target(binary_path=ROOT / "egglog-experimental")
    run = planned_run(target, required=3)
    plan = collection.CollectionPlan(target, (run,))
    success = collection.ProcessObservation(
        processes.TimingResult("success", processes.TimingRow(wall_sec=0.25), None),
        make_timing_summary(),
    )
    failure = collection.ProcessObservation(
        processes.TimingResult(
            "failure",
            processes.TimingRow(wall_sec=0.5),
            processes.ErrorRow("bad rule\nmore context", exit_code=1),
        ),
        None,
    )
    timed_out = collection.ProcessObservation(
        processes.TimingResult(
            "timed-out",
            processes.TimingRow(),
            processes.ErrorRow("timed out after 120 seconds"),
        ),
        None,
    )
    observations = iter((success, failure, timed_out))
    monkeypatch.setattr(collection, "run_process", lambda *_args: next(observations))
    stream = io.StringIO()
    output = runner_output.RunnerOutput()
    output.console = Console(file=stream, width=120, color_system=None, force_terminal=False)
    store = ReportStore(tmp_path / "report.jsonl")

    collection.collect_rows(store, plan, 120, output, collection.EstimateModel())

    assert stream.getvalue().splitlines() == [
        "  [1/3] file.egg · main/off · 1/3: succeeded after 0.250s",
        "  [2/3] file.egg · main/off · 2/3: failed after 0.500s: bad rule more context",
        "  [3/3] file.egg · main/off · 3/3: timed out after 120 seconds",
        "abc123: collected 3 fresh runs · 1 successful, 1 failed, 1 timed out",
    ]
    assert store.row_count == 3


@pytest.mark.parametrize("width", [80, 120])
def test_terminal_progress_keeps_success_transient_but_surfaces_failure(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    width: int,
) -> None:
    target = make_target(binary_path=ROOT / "egglog-experimental")
    run = planned_run(target, required=2)
    plan = collection.CollectionPlan(target, (run,))
    success = collection.ProcessObservation(
        processes.TimingResult("success", processes.TimingRow(wall_sec=0.25), None),
        make_timing_summary(),
    )
    failure = collection.ProcessObservation(
        processes.TimingResult(
            "failure",
            processes.TimingRow(wall_sec=0.5),
            processes.ErrorRow("bad rule", exit_code=1),
        ),
        None,
    )
    observations = iter((success, failure))
    monkeypatch.setattr(collection, "run_process", lambda *_args: next(observations))
    stream = io.StringIO()
    output = runner_output.RunnerOutput()
    output.console = Console(file=stream, width=width, color_system=None, force_terminal=True)

    collection.collect_rows(
        ReportStore(tmp_path / f"report-{width}.jsonl"),
        plan,
        120,
        output,
        collection.EstimateModel(),
    )

    rendered = stream.getvalue()
    assert "succeeded after" not in rendered
    assert "file.egg" in rendered
    assert "main/off" in rendered
    assert "failed after 0.500s: bad rule" in rendered
    assert "abc123: collected 2 fresh runs · 1 successful, 1 failed" in rendered
