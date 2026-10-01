"""Test cache-aware plans and integrated record collection."""

from __future__ import annotations

import io
import json
from dataclasses import replace
from pathlib import Path
from typing import cast

import pytest
from rich.console import Console

from benchmarking import benchmark, collection, models, processes, targets
from benchmarking.reports.store import CacheKey, ReportStore

from .report_fixtures import ROOT, make_record, make_target, make_timing_summary, write_report

FILE_SPEC = models.FileSpec("file.egg", ROOT / "file.egg", "sha256:file")


@pytest.fixture
def executable_target(tmp_path: Path) -> models.ResolvedTarget:
    """Give mocked collection processes an actual immutable executable identity."""

    binary = tmp_path / "egglog-experimental"
    binary.write_text("mocked engine executable\n")
    return make_target(binary_path=binary, binary_sha256=targets.sha256_file(binary))


def endpoint(
    target: models.ResolvedTarget,
    treatment: models.Treatment = "off",
) -> models.BenchmarkEndpoint:
    return models.BenchmarkEndpoint(target, treatment)


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
        models.BenchmarkEndpoint(shared_target, "off"),
        models.BenchmarkEndpoint(shared_target, "proofs"),
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
        _suite_mode: bool,
        _blocked_files: tuple[models.FileSpec, ...],
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
        models.BenchmarkEndpoint(baseline_target, "off"),
        models.BenchmarkEndpoint(candidate_target, "proofs"),
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
        _suite_mode: bool,
        _blocked_files: tuple[models.FileSpec, ...],
    ) -> collection.CollectionPlan:
        observed.append(target)
        return cast(collection.CollectionPlan, object())

    monkeypatch.setattr(benchmark, "build_collection_plan", build_plan)

    benchmark.collection_plans(cast(ReportStore, object()), comparison, False)

    assert observed == [baseline_target, candidate_target]


def test_same_checkout_target_aliases_build_once(
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
        engines: tuple[str, ...],
    ) -> models.ResolvedTarget:
        assert materialized == [baseline_request, candidate_request]
        builds.append((request, engines))
        return models.ResolvedTarget(request, row, "sha256:union", binary_path)

    monkeypatch.setattr(collection, "build_resolved_target", build)
    baseline = models.EndpointRequest(baseline_request, "off")
    candidate = models.EndpointRequest(candidate_request, "proofs")

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

    assert builds == [(baseline_request, ("egglog",))]
    assert resolved[baseline_request].request == baseline_request
    assert resolved[candidate_request].request == candidate_request
    assert resolved[baseline_request].row.source == "."
    assert resolved[candidate_request].row.source == str(ROOT)
    assert resolved[baseline_request].binary_path == resolved[candidate_request].binary_path == binary_path
    assert resolved[baseline_request].binary_sha256 == resolved[candidate_request].binary_sha256 == "sha256:union"


def test_same_target_builds_each_engine_required_by_its_treatments(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    request = targets.parse_target(".")
    row = models.TargetRow(".", str(ROOT), "HEAD", "abc123", False)
    built = make_target(binary_path=ROOT / "egglog-experimental")
    observed_engines: list[tuple[str, ...]] = []

    monkeypatch.setattr(collection, "materialize_target_request", lambda *_args: row)

    def build(
        _request: models.TargetRequest,
        _row: models.TargetRow,
        _console: Console,
        _profile: targets.BuildProfile,
        engines: tuple[str, ...],
    ) -> models.ResolvedTarget:
        observed_engines.append(engines)
        return built

    monkeypatch.setattr(collection, "build_resolved_target", build)
    endpoints = (
        models.EndpointRequest(request, "off"),
        models.EndpointRequest(request, "egg"),
    )

    collection.resolve_targets(
        ((request, endpoints),),
        cast(ReportStore, object()),
        (FILE_SPEC,),
        1,
        120,
        False,
        ROOT,
        ROOT,
        Console(stderr=True),
    )

    assert observed_engines == [("egglog", "egg")]


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
    builds: list[tuple[models.TargetRequest, tuple[str, ...]]] = []

    def materialize(request: models.TargetRequest, *_args: object) -> models.TargetRow:
        materialized.append(request)
        return fresh_row

    def build(
        request: models.TargetRequest,
        row: models.TargetRow,
        _console: Console,
        _profile: targets.BuildProfile,
        engines: tuple[str, ...],
    ) -> models.ResolvedTarget:
        builds.append((request, engines))
        return models.ResolvedTarget(request, row, "sha256:fresh", binary_path)

    monkeypatch.setattr(collection, "materialize_target_request", materialize)
    monkeypatch.setattr(collection, "build_resolved_target", build)
    groups = (
        (cached_request, (models.EndpointRequest(cached_request, "off"),)),
        (fresh_request, (models.EndpointRequest(fresh_request, "proofs"),)),
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
    assert builds == [(fresh_request, ("egglog",))]
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


def test_pair_collection_reuses_each_endpoint_independently_and_force_runs_both(tmp_path: Path) -> None:
    report = tmp_path / "report.jsonl"
    write_report(
        report,
        make_record(0, started_at="2026-07-04T12:00:00Z", treatment="off"),
    )
    target = make_target()
    file_spec = models.FileSpec("file.egg", ROOT / "file.egg", "sha256:file")
    endpoints = (endpoint(target, "off"), endpoint(target, "proofs"))

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
    executable_target: models.ResolvedTarget,
) -> None:
    report = tmp_path / "report.jsonl"
    file_spec = models.FileSpec("file.egg", ROOT / "file.egg", "sha256:file")
    target = executable_target
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


def test_preflight_checks_each_required_engine_binary(monkeypatch: pytest.MonkeyPatch) -> None:
    egglog_binary = ROOT / "egglog-experimental"
    egg_binary = ROOT / "egg-math-benchmark"
    original = make_target(binary_sha256="sha256:egglog", binary_path=egglog_binary)
    target = models.ResolvedTarget(
        original.request,
        original.row,
        original.binary_sha256,
        original.binary_path,
        (
            models.EngineBinary("egglog", "sha256:egglog", egglog_binary),
            models.EngineBinary("egg", "sha256:egg", egg_binary),
        ),
        "egglog",
    )
    calls: list[tuple[Path, tuple[str, ...]]] = []

    def preflight(
        binary_path: Path,
        _checkout_path: Path,
        _timeout_sec: int,
        required_outputs: tuple[str, ...],
    ) -> processes.TimingResult:
        calls.append((binary_path, required_outputs))
        return processes.TimingResult("success", processes.TimingRow(wall_sec=0.01), None)

    monkeypatch.setattr(collection, "run_preflight", preflight)
    plan = collection.CollectionPlan(
        target,
        (
            planned_run(treatment="proof-testing", required=1),
            planned_run(treatment="egg-proof-testing", required=1),
        ),
    )

    collection.preflight_collection(plan, 120)

    assert calls == [
        (egglog_binary, ("--timing-summary", "--proof-testing")),
        (egg_binary, ("--timing-summary", "--iterations", "--check-left", "--check-right")),
    ]


def test_collected_row_uses_selected_engine_binary_and_hash(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    egglog_binary = tmp_path / "egglog-experimental"
    egg_binary = tmp_path / "egg-math-benchmark"
    egglog_binary.write_text("egglog binary\n")
    egg_binary.write_text("native egg binary\n")
    egglog_hash = targets.sha256_file(egglog_binary)
    egg_hash = targets.sha256_file(egg_binary)
    original = make_target(binary_sha256=egglog_hash, binary_path=egglog_binary)
    target = models.ResolvedTarget(
        original.request,
        original.row,
        original.binary_sha256,
        original.binary_path,
        (
            models.EngineBinary("egglog", egglog_hash, egglog_binary),
            models.EngineBinary("egg", egg_hash, egg_binary),
        ),
        "egglog",
    )
    file_spec = models.FileSpec(
        "egglog-experimental/tests/math-microbenchmark-rational.egg",
        ROOT / "egglog-experimental/tests/math-microbenchmark-rational.egg",
        "sha256:math",
    )
    selected_endpoint = models.BenchmarkEndpoint(target, "egg")
    success = processes.TimingResult("success", processes.TimingRow(wall_sec=0.5), None)
    observed_binaries: list[Path] = []

    def run_process(binary_path: Path, *_args: object) -> collection.ProcessObservation:
        observed_binaries.append(binary_path)
        return collection.ProcessObservation(success, make_timing_summary())

    monkeypatch.setattr(collection, "run_process", run_process)
    store = ReportStore(tmp_path / "report.jsonl")
    plan = collection.build_collection_plan(store, target, (selected_endpoint,), (file_spec,), 1, 120, False)

    collection.collect_rows(store, plan, 120, Console(stderr=True))

    assert observed_binaries == [egg_binary]
    assert store.records[0]["binary_sha256"] == egg_hash
    assert CacheKey.for_endpoint(selected_endpoint, file_spec, 120).binary_sha256 == egg_hash


@pytest.mark.parametrize("replacement_timing", ["before", "during"])
def test_collect_rows_rejects_replaced_executable_without_changing_cache(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    executable_target: models.ResolvedTarget,
    replacement_timing: str,
) -> None:
    target = executable_target
    binary_path = target.binary_path
    assert binary_path is not None
    replacement = tmp_path / "replacement"
    replacement.write_text("replacement engine executable\n")
    file = stable_file_spec(tmp_path)
    report = tmp_path / "report.jsonl"
    write_report(
        report,
        make_record(
            0,
            started_at="2026-09-21T00:00:00Z",
            binary_sha256=target.binary_sha256,
            file_sha256=file.sha256,
        ),
    )
    original_cache = report.read_bytes()
    store = ReportStore(report)
    plan = collection.build_collection_plan(store, target, (endpoint(target),), (file,), 1, 120, True)
    process_calls = []

    def run_process(path: Path, *_args: object) -> collection.ProcessObservation:
        process_calls.append(path)
        assert replacement_timing == "during", "replacement before a run must prevent process launch"
        replacement.replace(path)
        return collection.ProcessObservation(
            processes.TimingResult("success", processes.TimingRow(wall_sec=0.5), None),
            make_timing_summary(),
        )

    monkeypatch.setattr(collection, "run_process", run_process)
    if replacement_timing == "before":
        replacement.replace(binary_path)

    with pytest.raises(ValueError, match="benchmark executable changed before or during execution"):
        collection.collect_rows(store, plan, 120, Console(stderr=True))

    assert process_calls == ([binary_path] if replacement_timing == "during" else [])
    assert store.row_count == 1
    assert report.read_bytes() == original_cache


def test_fully_cached_collection_does_not_require_the_old_executable(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, executable_target: models.ResolvedTarget
) -> None:
    target = executable_target
    assert target.binary_path is not None
    file = stable_file_spec(tmp_path)
    report = tmp_path / "report.jsonl"
    write_report(
        report,
        make_record(
            0,
            started_at="2026-09-21T00:00:00Z",
            binary_sha256=target.binary_sha256,
            file_sha256=file.sha256,
        ),
    )
    original_cache = report.read_bytes()
    store = ReportStore(report)
    plan = collection.build_collection_plan(store, target, (endpoint(target),), (file,), 1, 120, False)
    target.binary_path.unlink()
    monkeypatch.setattr(collection, "run_process", lambda *_args: pytest.fail("cached rows must not run"))

    collection.collect_rows(store, plan, 120, Console(stderr=True))

    assert store.row_count == 1
    assert report.read_bytes() == original_cache


def test_collect_rows_rejects_unsupported_timing_summary_before_append(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    executable_target: models.ResolvedTarget,
) -> None:
    report = tmp_path / "report.jsonl"
    benchmark_file = tmp_path / "file.egg"
    benchmark_file.write_text("(check (= 1 1))\n", encoding="utf-8")
    file_spec = models.FileSpec("file.egg", benchmark_file, targets.sha256_file(benchmark_file))
    target = executable_target
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

    assert not report.exists()


def test_run_process_passes_treatment_flags(
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
                    "schema_version": 4,
                    "typecheck_ns": 1,
                    "frontend_parse_ns": 2,
                    "frontend_other_ns": 3,
                    "frontend_install_ns": 4,
                    "commands_actions_ns": 5,
                    "commands_check_ns": 6,
                    "commands_other_ns": 7,
                    "native_rebuild_ns": 8,
                    "rulesets": [
                        {
                            "name": "rules",
                            "role": "program",
                            "assembly_ns": 3,
                            "search_ns": 4,
                            "apply_ns": 6,
                            "execution_ns": 10,
                            "merge_ns": 20,
                        }
                    ],
                }
            ),
            encoding="utf-8",
        )
        return processes.TimingResult("success", processes.TimingRow(wall_sec=1.0), None)

    monkeypatch.setattr(collection, "run_command", fake_run_command)

    off = collection.run_process(ROOT / "egglog-experimental", ROOT, file_spec, "off", 120)
    proofs = collection.run_process(ROOT / "egglog-experimental", ROOT, file_spec, "proofs", 120)

    assert "--proofs" not in commands[0]
    assert "--proofs" in commands[1]
    assert off.timing_summary is not None
    assert off.timing_summary["rulesets"] == [
        {
            "name": "rules",
            "role": "program",
            "assembly_ns": 3,
            "search_ns": 4,
            "apply_ns": 6,
            "execution_ns": 10,
            "merge_ns": 20,
        }
    ]
    assert off.timing_summary["native_rebuild_ns"] == 8
    assert proofs.timing_summary is not None


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
        collection.run_process(ROOT / "egglog-experimental", ROOT, file_spec, "off", 120)


def test_run_process_does_not_require_summary_after_failure(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    file_spec = stable_file_spec(tmp_path)
    failure = processes.TimingResult("failure", processes.TimingRow(wall_sec=1.0), processes.ErrorRow("failed"))
    monkeypatch.setattr(collection, "run_command", lambda *_args: failure)

    observation = collection.run_process(ROOT / "egglog-experimental", ROOT, file_spec, "off", 120)

    assert observation.result is failure
    assert observation.timing_summary is None


@pytest.mark.parametrize("mutated_input", ("file", "facts"))
def test_collect_rows_rejects_mutated_workload_before_append(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    mutated_input: str,
    executable_target: models.ResolvedTarget,
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
    target = executable_target
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
    assert not store.path.exists()


def test_redirected_collection_logs_each_run_and_one_status_summary(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    executable_target: models.ResolvedTarget,
) -> None:
    target = executable_target
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
        "abc123: ETA pending (remaining executable time)",
        "  [1/3] file.egg · off · 1/3: succeeded after 0.250s · ETA ~0:00:01",
        "  [2/3] file.egg · off · 2/3: failed after 0.500s: bad rule more context · ETA ~0:00:01",
        "  [3/3] file.egg · off · 3/3: timed out after 120 seconds · ETA ~0:00:00",
        "abc123: collected 3 fresh runs · 1 successful, 1 failed, 1 timed out",
    ]
    assert store.row_count == 3


@pytest.mark.parametrize("width", [80, 119, 120, 160, 200])
def test_terminal_progress_keeps_success_transient_but_surfaces_failure(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    width: int,
    executable_target: models.ResolvedTarget,
) -> None:
    target = executable_target
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
    assert "off" in rendered
    assert "ETA" in rendered
    assert "failed after 0.500s: bad rule" in rendered
    assert "abc123: collected 2 fresh runs · 1 successful, 1 failed" in rendered


def test_collection_eta_weights_remaining_work_by_endpoint_and_ignores_failures(tmp_path: Path) -> None:
    store = ReportStore(tmp_path / "report.jsonl")
    off = planned_run(required=10, missing=2)
    proofs = planned_run(treatment="proofs", required=10, missing=3)
    plan = collection.CollectionPlan(make_target(), (off, proofs))
    for treatment, wall, status in (
        ("off", 1.0, "success"),
        ("off", 3.0, "success"),
        ("proofs", 100.0, "success"),
        ("proofs", 200.0, "success"),
        ("proofs", 999.0, "failure"),
        ("proofs", None, "timed-out"),
    ):
        store.append(
            make_record(
                0,
                started_at="2026-01-01T00:00:00Z",
                file_sha256=off.file.sha256,
                treatment=cast(models.Treatment, treatment),
                wall_sec=cast(float | None, wall),
                status=cast(models.Status, status),
            )
        )
    # 2 * mean(1, 3) + 3 * mean(100, 200), not a throughput average across runs.
    assert collection._collection_eta(store, plan, 120, {off: 2, proofs: 3}, set()) == "ETA ~0:07:34"
    assert collection._collection_eta(store, plan, 120, {off: 0, proofs: 0}, set()) == "ETA ~0:00:00"


@pytest.mark.parametrize("mismatch", ["binary", "file", "facts", "treatment", "timeout", "encoding"])
def test_collection_eta_waits_for_matching_successful_measurements(tmp_path: Path, mismatch: str) -> None:
    store = ReportStore(tmp_path / "report.jsonl")
    run = planned_run(required=10)
    plan = collection.CollectionPlan(make_target(), (run,))
    record = make_record(0, started_at="2026-01-01T00:00:00Z", file_sha256=run.file.sha256)
    if mismatch == "binary":
        record["binary_sha256"] = "sha256:other"
    elif mismatch == "file":
        record["file_sha256"] = "sha256:other"
    elif mismatch == "facts":
        record["fact_directory_sha256"] = "sha256:other"
    elif mismatch == "treatment":
        record["treatment"] = "proofs"
    elif mismatch == "encoding":
        run = replace(run, disequality_encoding="ee")
        plan = collection.CollectionPlan(make_target(), (run,))
    else:
        record["timeout_sec"] = 300
    store.append(record)
    assert collection._collection_eta(store, plan, 120, {run: 10}, set()) == "ETA pending"
    # A terminal failure removes this workload's remaining repetitions from the ETA.
    assert collection._collection_eta(store, plan, 120, {run: 10}, {run.file}) == "ETA ~0:00:00"


def test_resource_guard_failure_is_retained_before_collection_halts(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, executable_target: models.ResolvedTarget
) -> None:
    run = planned_run(required=30)
    plan = collection.CollectionPlan(executable_target, (run,))
    calls = 0

    def stopped(*_args: object) -> collection.ProcessObservation:
        nonlocal calls
        calls += 1
        return collection.ProcessObservation(
            processes.TimingResult(
                "failure",
                processes.TimingRow(),
                processes.ErrorRow("resource guard stopped workload: host memory pressure"),
                resource_stopped=True,
            ),
            None,
        )

    monkeypatch.setattr(collection, "run_process", stopped)
    store = ReportStore(tmp_path / "report.jsonl")
    with pytest.raises(ValueError, match="failed observation was retained.*before launching another workload"):
        collection.collect_rows(store, plan, 120, Console(file=io.StringIO()))
    assert calls == store.row_count == 1
    record = store.records[0]
    assert record["status"] == "failure"
    assert record["wall_sec"] is None
    assert "host memory pressure" in str(record["error_message"])
    resumed = collection.build_collection_plan(
        store, executable_target, (endpoint(executable_target),), (run.file,), 30, 120, False
    )
    assert resumed.runs[0].cached_statuses == ("failure",)
    assert resumed.total_missing_observations == 29


def test_suite_reduced_sample_retains_old_failure_until_explicit_retry(tmp_path: Path) -> None:
    store = ReportStore(tmp_path / "report.jsonl")
    target = make_target()
    proof = endpoint(target, "proofs")
    for index in range(11):
        store.append(
            make_record(
                index,
                started_at="2026-01-01T00:00:00Z",
                treatment="proofs",
                status="timed-out" if index == 0 else "success",
            )
        )
    assert all(
        row.record["status"] == "success"
        for row in store.latest_records(CacheKey.for_endpoint(proof, FILE_SPEC, 120), 10)
    )
    plan = collection.build_collection_plan(store, target, (proof,), (FILE_SPEC,), 10, 120, False, True)
    assert plan.total_missing_observations == 0
    assert store.latest_failure(CacheKey.for_endpoint(proof, FILE_SPEC, 120), 10) is not None
    retry = collection.build_collection_plan(store, target, (proof,), (FILE_SPEC,), 10, 120, True, True)
    assert retry.total_missing_observations == 10
