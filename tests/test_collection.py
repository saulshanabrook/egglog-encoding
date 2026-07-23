"""Test cache-aware plans and integrated record collection."""

from __future__ import annotations

import io
import json
from pathlib import Path
from typing import cast

import pytest
from rich.console import Console

from benchmarking import benchmark, collection, models, processes, targets
from benchmarking.reports.store import CacheKey, ReportStore

from .report_fixtures import ROOT, make_record, make_target, make_timing_summary, write_report

FILE_SPEC = models.FileSpec("file.egg", ROOT / "file.egg", "sha256:file")


def endpoint(
    target: models.ResolvedTarget,
    backend: models.Backend = "main",
    treatment: models.Treatment = "off",
) -> models.BenchmarkEndpoint:
    return models.BenchmarkEndpoint(target, backend, treatment)


def stable_file_spec(tmp_path: Path) -> models.FileSpec:
    """Create one immutable workload identity for run-process tests."""

    path = tmp_path / "file.egg"
    path.write_text("(check (= 1 1))\n", encoding="utf-8")
    return models.FileSpec(path.name, path, targets.sha256_file(path))


def planned_run(
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
    )


def rendered_collection_plan(
    plan: collection.CollectionPlan,
    *,
    width: int = 120,
) -> str:
    """Render one operational summary without coupling tests to process stderr."""

    stream = io.StringIO()
    console = Console(file=stream, width=width, color_system=None)
    collection.emit_collection_plan(console, plan)
    return stream.getvalue().rstrip()


def test_collection_plans_group_only_the_same_resolved_target(monkeypatch: pytest.MonkeyPatch) -> None:
    shared_target = make_target(target_label="shared", binary_sha256="sha256:shared")
    comparison = models.ComparisonSpec(
        models.BenchmarkEndpoint(shared_target, "main", "off"),
        models.BenchmarkEndpoint(shared_target, "dd", "proofs"),
        (FILE_SPEC,),
        1,
        120,
    )
    observed: list[tuple[models.ResolvedTarget, tuple[models.BenchmarkEndpoint, ...], bool]] = []
    sentinel = cast(collection.CollectionPlan, object())

    def build_plan(
        _store: ReportStore,
        target: models.ResolvedTarget,
        endpoints: tuple[models.BenchmarkEndpoint, ...],
        _files: tuple[models.FileSpec, ...],
        _rounds: int,
        _timeout_sec: int,
        force_run: bool,
    ) -> collection.CollectionPlan:
        observed.append((target, endpoints, force_run))
        return sentinel

    monkeypatch.setattr(benchmark, "build_collection_plan", build_plan)

    plans = benchmark.collection_plans(cast(ReportStore, object()), comparison, True)

    assert plans == (sentinel,)
    assert observed == [(shared_target, (comparison.baseline, comparison.candidate), True)]


def test_collection_plans_keep_distinct_targets_with_the_same_binary_separate(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    baseline_target = make_target(target_label="cached", binary_sha256="sha256:shared", binary_path=None)
    candidate_target = make_target(
        target_label="current",
        binary_sha256="sha256:shared",
        binary_path=ROOT / "egglog-experimental",
    )
    comparison = models.ComparisonSpec(
        models.BenchmarkEndpoint(baseline_target, "main", "off"),
        models.BenchmarkEndpoint(candidate_target, "main", "proofs"),
        (FILE_SPEC,),
        1,
        120,
    )
    observed: list[models.ResolvedTarget] = []

    def build_plan(
        _store: ReportStore,
        target: models.ResolvedTarget,
        _endpoints: tuple[models.BenchmarkEndpoint, ...],
        _files: tuple[models.FileSpec, ...],
        _rounds: int,
        _timeout_sec: int,
        _force_run: bool,
    ) -> collection.CollectionPlan:
        observed.append(target)
        return cast(collection.CollectionPlan, object())

    monkeypatch.setattr(benchmark, "build_collection_plan", build_plan)

    benchmark.collection_plans(cast(ReportStore, object()), comparison, False)

    assert observed == [baseline_target, candidate_target]


def test_same_checkout_target_aliases_build_once_with_union_backend_features(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    baseline_request = targets.parse_target(".")
    candidate_request = targets.parse_target(str(ROOT))
    rows = {
        baseline_request: models.TargetRow(".", str(ROOT), "HEAD", "abc123", False),
        candidate_request: models.TargetRow(str(ROOT), str(ROOT), "HEAD", "abc123", False),
    }
    binary_path = ROOT / "target/release/egglog-experimental"
    materialized: list[models.TargetRequest] = []
    builds: list[tuple[models.TargetRequest, tuple[str, ...]]] = []

    def materialize(request: models.TargetRequest, *_args: object) -> models.TargetRow:
        materialized.append(request)
        return rows[request]

    monkeypatch.setattr(collection, "materialize_target_request", materialize)

    def build(
        request: models.TargetRequest,
        row: models.TargetRow,
        _console: Console,
        _profile: targets.BuildProfile,
        features: tuple[str, ...],
    ) -> models.ResolvedTarget:
        assert materialized == [baseline_request, candidate_request]
        builds.append((request, features))
        return models.ResolvedTarget(request, row, "sha256:union", binary_path)

    monkeypatch.setattr(collection, "build_resolved_target", build)
    baseline = models.EndpointRequest(baseline_request, "main", "off")
    candidate = models.EndpointRequest(candidate_request, "dd", "proofs")

    resolved = collection.resolve_targets(
        (
            (baseline_request, (baseline,)),
            (candidate_request, (candidate,)),
        ),
        cast(ReportStore, object()),
        (FILE_SPEC,),
        1,
        120,
        False,
        ROOT,
        ROOT,
        Console(stderr=True),
    )

    assert builds == [(baseline_request, ("dd-backend",))]
    assert resolved[baseline_request].request == baseline_request
    assert resolved[candidate_request].request == candidate_request
    assert resolved[baseline_request].row.source == "."
    assert resolved[candidate_request].row.source == str(ROOT)
    assert resolved[baseline_request].binary_path == resolved[candidate_request].binary_path == binary_path
    assert resolved[baseline_request].binary_sha256 == resolved[candidate_request].binary_sha256 == "sha256:union"


def test_batch_target_resolution_reuses_complete_cache_label_before_building_pending_target(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    report = tmp_path / "report.jsonl"
    write_report(
        report,
        make_record(
            0,
            started_at="2026-07-04T12:00:00Z",
            target_label="cached",
            binary_sha256="sha256:cached",
        ),
    )
    cached_request = targets.parse_target("cached=")
    fresh_request = targets.parse_target(".")
    fresh_row = models.TargetRow(".", str(tmp_path / "checkout"), "HEAD", "fresh123", False)
    binary_path = tmp_path / "checkout/target/release/egglog-experimental"
    materialized: list[models.TargetRequest] = []
    builds: list[tuple[str, ...]] = []

    def materialize(request: models.TargetRequest, *_args: object) -> models.TargetRow:
        materialized.append(request)
        return fresh_row

    def build(
        request: models.TargetRequest,
        row: models.TargetRow,
        _console: Console,
        _profile: targets.BuildProfile,
        features: tuple[str, ...],
    ) -> models.ResolvedTarget:
        builds.append(features)
        return models.ResolvedTarget(request, row, "sha256:fresh", binary_path)

    monkeypatch.setattr(collection, "materialize_target_request", materialize)
    monkeypatch.setattr(collection, "build_resolved_target", build)
    groups = (
        (cached_request, (models.EndpointRequest(cached_request, "main", "off"),)),
        (fresh_request, (models.EndpointRequest(fresh_request, "dd", "proofs"),)),
    )

    resolved = collection.resolve_targets(
        groups,
        ReportStore(report),
        (FILE_SPEC,),
        1,
        120,
        False,
        tmp_path,
        ROOT,
        Console(stderr=True),
    )

    assert materialized == [fresh_request]
    assert builds == [("dd-backend",)]
    assert resolved[cached_request].binary_sha256 == "sha256:cached"
    assert resolved[cached_request].binary_path is None
    assert resolved[fresh_request].binary_sha256 == "sha256:fresh"
    assert resolved[fresh_request].binary_path == binary_path


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
        planned_run(filename=filename, treatment=treatment, cached=("success",) * 6)
        for filename in filenames
        for treatment in treatments
    )

    rendered = rendered_collection_plan(collection.CollectionPlan(target, runs), width=width)

    assert rendered == f"{target_label}: 72/72 runs cached · nothing to collect"


def test_cached_failure_and_timeout_are_explicit() -> None:
    target = make_target()
    run = planned_run(cached=("success", "success", "success", "success", "failure", "timed-out"))

    rendered = rendered_collection_plan(collection.CollectionPlan(target, (run,)))

    assert rendered == "abc123: 6/6 runs cached (1 failed, 1 timed out) · nothing to collect"


def test_partial_and_forced_plans_show_only_total_work() -> None:
    target = make_target()
    partial = planned_run(cached=("success",) * 4)
    forced = planned_run(cached=("success",) * 6, missing=6)

    partial_text = rendered_collection_plan(collection.CollectionPlan(target, (partial,)))
    forced_text = rendered_collection_plan(collection.CollectionPlan(target, (forced,)))

    assert partial_text == "abc123: 4/6 runs cached · collecting 2 fresh"
    assert forced_text == "abc123: 6/6 runs cached · collecting 6 fresh"


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
    collection.collect_rows(store, plan, 120, Console(stderr=True))
    key = CacheKey.for_endpoint(selected_endpoint, file_spec, 120)
    selected = store.selected_statuses_for_keys((key,), 1)[key]

    persisted = json.loads(report.read_text(encoding="utf-8"))
    assert "row_index" not in persisted
    assert persisted["wall_sec"] == 1.25
    assert persisted["timing_summary"] == summary
    assert selected == ("success",)


def test_preflight_requires_extraction_capability_only_for_fresh_rows(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    target = make_target(binary_path=ROOT / "egglog-experimental")
    calls: list[tuple[str, ...]] = []
    success = processes.TimingResult("success", processes.TimingRow(wall_sec=0.01), None)
    failure = processes.TimingResult(
        "failure",
        processes.TimingRow(wall_sec=0.01),
        processes.ErrorRow("successful process output did not contain '--proof-extraction'"),
    )

    def preflight(
        _binary_path: Path,
        _checkout_path: Path,
        _timeout_sec: int,
        required_outputs: tuple[str, ...],
    ) -> processes.TimingResult:
        calls.append(required_outputs)
        return failure if "--proof-extraction" in required_outputs else success

    monkeypatch.setattr(collection, "run_preflight", preflight)
    cached = planned_run(treatment="proof-extraction", cached=("success",), required=1)
    collection.preflight_collection(collection.CollectionPlan(target, (cached, planned_run(required=1))), 120)

    fresh = planned_run(treatment="proof-extraction", required=1)
    with pytest.raises(ValueError, match=r"preflight failed.*--proof-extraction"):
        collection.preflight_collection(collection.CollectionPlan(target, (fresh,)), 120)

    assert calls == [("--timing-summary",), ("--timing-summary", "--proof-extraction")]


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
            Console(stderr=True),
        )

    assert report.read_text(encoding="utf-8") == ""


def test_run_process_passes_backend_flag_only_for_dd(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    commands: list[list[str]] = []
    file_spec = stable_file_spec(tmp_path)

    def fake_run_command(command: list[str], checkout_path: Path, timeout_sec: int) -> processes.TimingResult:
        commands.append(command)
        assert checkout_path == ROOT
        assert timeout_sec == 120
        summary_path = Path(command[command.index("--timing-summary") + 1])
        summary_path.write_text(
            json.dumps(
                {
                    "schema_version": 2,
                    "rulesets": [
                        {
                            "name": "rules",
                            "search_ns": 4,
                            "apply_ns": 6,
                            "unattributed_ns": 10,
                            "merge_ns": 20,
                            "rebuild_ns": 30,
                        }
                    ],
                }
            ),
            encoding="utf-8",
        )
        return processes.TimingResult("success", processes.TimingRow(wall_sec=1.0), None)

    monkeypatch.setattr(collection, "run_command", fake_run_command)

    main = collection.run_process(ROOT / "egglog-experimental", ROOT, file_spec, "main", "off", 120)
    dd = collection.run_process(ROOT / "egglog-experimental", ROOT, file_spec, "dd", "proofs", 120)

    assert "--backend" not in commands[0]
    assert commands[1][commands[1].index("--backend") : commands[1].index("--backend") + 2] == [
        "--backend",
        "dd",
    ]
    assert "--proofs" in commands[1]
    assert main.timing_summary is not None
    assert main.timing_summary["rulesets"][0]["search_ns"] == 4
    assert main.timing_summary["rulesets"][0]["apply_ns"] == 6
    assert main.timing_summary["rulesets"][0]["unattributed_ns"] == 10
    assert main.timing_summary["rulesets"][0]["merge_ns"] == 20
    assert dd.timing_summary is not None


def test_run_process_rejects_success_without_timing_summary(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    file_spec = stable_file_spec(tmp_path)
    monkeypatch.setattr(
        collection,
        "run_command",
        lambda *_args: processes.TimingResult("success", processes.TimingRow(wall_sec=1.0), None),
    )

    with pytest.raises(ValueError, match="did not produce --timing-summary"):
        collection.run_process(ROOT / "egglog-experimental", ROOT, file_spec, "main", "off", 120)


def test_run_process_does_not_require_summary_after_failure(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    file_spec = stable_file_spec(tmp_path)
    failure = processes.TimingResult("failure", processes.TimingRow(wall_sec=1.0), processes.ErrorRow("failed"))
    monkeypatch.setattr(collection, "run_command", lambda *_args: failure)

    observation = collection.run_process(ROOT / "egglog-experimental", ROOT, file_spec, "main", "off", 120)

    assert observation.result is failure
    assert observation.timing_summary is None


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
        collection.collect_rows(store, plan, 120, Console(stderr=True))

    assert store.row_count == 0
    assert store.path.read_text(encoding="utf-8") == ""


def test_redirected_collection_logs_each_run_and_one_status_summary(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    target = make_target(binary_path=ROOT / "egglog-experimental")
    run = planned_run(required=3)
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
    console = Console(file=stream, width=120, color_system=None, force_terminal=False)
    store = ReportStore(tmp_path / "report.jsonl")

    collection.collect_rows(store, plan, 120, console)

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
    run = planned_run(required=2)
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
    console = Console(file=stream, width=width, color_system=None, force_terminal=True)

    collection.collect_rows(
        ReportStore(tmp_path / f"report-{width}.jsonl"),
        plan,
        120,
        console,
    )

    rendered = stream.getvalue()
    assert "succeeded after" not in rendered
    assert "file.egg" in rendered
    assert "main/off" in rendered
    assert "ETA" not in rendered
    assert "failed after 0.500s: bad rule" in rendered
    assert "abc123: collected 2 fresh runs · 1 successful, 1 failed" in rendered
