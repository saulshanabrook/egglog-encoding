"""Test cache-aware plans and integrated record collection."""

from __future__ import annotations

import io
import json
from dataclasses import replace
from pathlib import Path
from typing import cast

import pytest
from rich.console import Console

from benchmarking import collection, engines, models, processes, targets
from benchmarking.reports.store import CacheKey, ReportStore

from .report_fixtures import ROOT, make_record, make_target, make_timing_summary, write_report

FILE_SPEC = models.FileSpec("file.egg", ROOT / "file.egg", "sha256:file")


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


def test_plan_collection_merges_overlaps_without_expanding_other_scopes(tmp_path: Path) -> None:
    target = make_target()
    other = models.FileSpec("other.egg", ROOT / "other.egg", "sha256:other")
    store = ReportStore(tmp_path / "reports.jsonl")
    store.append(make_record(0, started_at="2026-07-04T12:00:00Z"))
    requests = (
        collection.BenchmarkRequest(models.EndpointRequest(target.request, "off"), (FILE_SPEC, other)),
        collection.BenchmarkRequest(models.EndpointRequest(target.request, "proofs"), (FILE_SPEC,)),
        collection.BenchmarkRequest(models.EndpointRequest(target.request, "off"), (other,)),
        collection.BenchmarkRequest(models.EndpointRequest(target.request, "proof-testing"), (other,)),
    )
    resolved = {target.request: target}

    (plan,) = collection.plan_collection(store, requests, resolved, 2, 120, False)
    (forced,) = collection.plan_collection(store, requests, resolved, 2, 120, True)

    assert [(run.file.display_path, run.treatment, run.missing_observations) for run in plan.runs] == [
        ("file.egg", "off", 1),
        ("other.egg", "off", 2),
        ("file.egg", "proofs", 2),
        ("other.egg", "proof-testing", 2),
    ]
    assert len(forced.runs) == 4
    assert forced.total_missing_observations == 8


def test_plan_collection_keeps_distinct_targets_with_the_same_binary_separate(tmp_path: Path) -> None:
    baseline_target = make_target(target_label="cached", binary_sha256="sha256:shared", binary_path=None)
    candidate_target = make_target(
        target_label="current",
        binary_sha256="sha256:shared",
        binary_path=ROOT / "egglog-experimental",
    )
    requests = (
        collection.BenchmarkRequest(models.EndpointRequest(baseline_target.request, "off"), (FILE_SPEC,)),
        collection.BenchmarkRequest(models.EndpointRequest(candidate_target.request, "proofs"), (FILE_SPEC,)),
    )
    resolved = {target.request: target for target in (baseline_target, candidate_target)}

    plans = collection.plan_collection(ReportStore(tmp_path / "reports.jsonl"), requests, resolved, 1, 120, False)

    assert [plan.target for plan in plans] == [baseline_target, candidate_target]


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


@pytest.mark.parametrize("target_dir_is_absolute", [False, True])
@pytest.mark.parametrize("treatments", [("off", "proofs"), ("egg", "egg-proofs"), ("off", "egg")])
def test_distinct_checkouts_reject_one_cargo_target_dir(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
    target_dir_is_absolute: bool,
    treatments: tuple[models.Treatment, models.Treatment],
) -> None:
    baseline_request = targets.parse_target("baseline")
    candidate_request = targets.parse_target("candidate")
    rows = {
        baseline_request: models.TargetRow("baseline", str(tmp_path / "baseline"), "HEAD", "baseline123", False),
        candidate_request: models.TargetRow("candidate", str(tmp_path / "candidate"), "HEAD", "candidate123", False),
    }
    target_dir = str(tmp_path / "shared-target") if target_dir_is_absolute else "../shared-target"
    monkeypatch.setenv("CARGO_TARGET_DIR", target_dir)
    monkeypatch.setattr(
        collection,
        "materialize_target_request",
        lambda request, *_args: rows[request],
    )

    with pytest.raises(ValueError, match="cannot share one CARGO_TARGET_DIR"):
        collection.resolve_targets(
            (
                (
                    baseline_request,
                    (models.EndpointRequest(baseline_request, treatments[0]),),
                ),
                (
                    candidate_request,
                    (models.EndpointRequest(candidate_request, treatments[1]),),
                ),
            ),
            cast(ReportStore, object()),
            (FILE_SPEC,),
            1,
            120,
            False,
            tmp_path,
            ROOT,
            Console(stderr=True),
        )


@pytest.mark.parametrize("candidate_treatment", ["egg-ee", "off"])
def test_isolated_native_checkouts_allow_a_shared_cargo_target_dir(
    candidate_treatment: models.Treatment,
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    baseline_request = targets.parse_target("baseline")
    candidate_request = targets.parse_target("candidate")
    rows = {
        baseline_request: models.TargetRow("baseline", str(tmp_path / "baseline"), "HEAD", "baseline123", False),
        candidate_request: models.TargetRow("candidate", str(tmp_path / "candidate"), "HEAD", "candidate123", False),
    }
    monkeypatch.setenv("CARGO_TARGET_DIR", str(tmp_path / "shared-target"))
    monkeypatch.setattr(collection, "materialize_target_request", lambda request, *_args: rows[request])
    builds: list[models.TargetRequest] = []

    def build(
        request: models.TargetRequest,
        row: models.TargetRow,
        _console: Console,
        _profile: targets.BuildProfile,
        _engines: tuple[models.Engine, ...],
    ) -> models.ResolvedTarget:
        builds.append(request)
        return models.ResolvedTarget(request, row, f"sha256:{row.git_sha}", Path(row.path) / "binary")

    monkeypatch.setattr(collection, "build_resolved_target", build)
    resolved = collection.resolve_targets(
        (
            (baseline_request, (models.EndpointRequest(baseline_request, "egg-ee"),)),
            (candidate_request, (models.EndpointRequest(candidate_request, candidate_treatment),)),
        ),
        cast(ReportStore, object()),
        (FILE_SPEC,),
        1,
        120,
        False,
        tmp_path,
        ROOT,
        Console(stderr=True),
    )

    assert builds == [baseline_request, candidate_request]
    assert tuple(resolved) == (baseline_request, candidate_request)


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


def test_request_resolution_checks_only_each_endpoints_own_files(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    path = tmp_path / "reports.jsonl"
    write_report(
        path,
        make_record(0, started_at="2026-07-04T12:00:00Z", target_label="cached"),
        make_record(
            1,
            started_at="2026-07-04T12:00:01Z",
            target_label="cached",
            treatment="proofs",
            file_sha256="sha256:other",
        ),
    )
    target_request = targets.parse_target("cached=")
    other = models.FileSpec("other.egg", ROOT / "other.egg", "sha256:other")
    requests = (
        collection.BenchmarkRequest(models.EndpointRequest(target_request, "off"), (FILE_SPEC,)),
        collection.BenchmarkRequest(models.EndpointRequest(target_request, "proofs"), (other,)),
    )
    monkeypatch.setattr(collection, "materialize_git_ref", lambda *_a: pytest.fail("exact requirements are cached"))
    monkeypatch.setattr(collection, "build_resolved_target", lambda *_a: pytest.fail("exact requirements are cached"))

    resolved = collection.resolve_requests(requests, ReportStore(path), 1, 120, False, ROOT, ROOT, Console())

    assert resolved[target_request].binary_sha256 == "sha256:bin"
    assert resolved[target_request].binary_path is None


def test_shared_collection_refreshes_all_aliases_when_every_run_is_cached(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    path = tmp_path / "reports.jsonl"
    write_report(path, make_record(0, started_at="2026-07-04T12:00:00Z"))
    before = path.read_bytes()
    first = make_target(target_label="figures")
    alias = make_target(target_label="alias")
    requests = tuple(
        collection.BenchmarkRequest(models.EndpointRequest(target.request, "off"), (FILE_SPEC,))
        for target in (first, alias)
    )
    resolved = {target.request: target for target in (first, alias)}
    store = ReportStore(path)
    plans = collection.plan_collection(store, requests, resolved, 1, 120, False)
    monkeypatch.setattr(collection, "run_process", lambda *_a: pytest.fail("all observations are cached"))
    monkeypatch.setattr(collection, "run_preflight", lambda *_a: pytest.fail("no fresh preflight is needed"))

    grouped = collection.collect(store, plans, requests, resolved, 120, Console(file=io.StringIO()))

    assert len(plans) == 1
    assert grouped.data["groups"][0]["labels"] == ["alias", "figures"]
    assert grouped.records[0]["target_label"] is None
    assert path.read_bytes() == before
    assert json.loads(path.with_name("reports-grouped.json").read_bytes())["groups"][0]["labels"] == [
        "alias",
        "figures",
    ]


def test_shared_collection_rejects_conflicting_label_bindings_before_launch(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    first = make_target(target_label="figures", binary_sha256="sha256:first")
    second = replace(
        make_target(target_label="figures", binary_sha256="sha256:second"),
        request=targets.parse_target("figures=@other"),
    )
    requests = tuple(
        collection.BenchmarkRequest(models.EndpointRequest(target.request, "off"), (FILE_SPEC,))
        for target in (first, second)
    )
    resolved = {target.request: target for target in (first, second)}
    store = ReportStore(tmp_path / "reports.jsonl")
    plans = collection.plan_collection(store, requests, resolved, 1, 120, False)
    monkeypatch.setattr(collection, "preflight_collection", lambda *_a: pytest.fail("ambiguous label must fail first"))

    with pytest.raises(ValueError, match="label 'figures' resolves to different egglog binaries"):
        collection.collect(store, plans, requests, resolved, 120, Console(file=io.StringIO()))
    assert not store.path.exists()


def test_multiple_targets_share_round_progress_and_stop_only_the_failed_identity(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    first = make_target(target_label="first", binary_sha256="sha256:first", binary_path=tmp_path / "first")
    second = make_target(target_label="second", binary_sha256="sha256:second", binary_path=tmp_path / "second")
    run = planned_run(required=2)
    calls: list[str] = []

    def observe(binary: Path, *_args: object) -> collection.ProcessObservation:
        calls.append(binary.name)
        if binary.name == "first":
            return collection.ProcessObservation(
                processes.TimingResult("failure", processes.TimingRow(), processes.ErrorRow("failed")), None
            )
        return collection.ProcessObservation(
            processes.TimingResult("success", processes.TimingRow(wall_sec=0.25), None), make_timing_summary()
        )

    monkeypatch.setattr(collection, "run_process", observe)
    stream = io.StringIO()
    store = ReportStore(tmp_path / "reports.jsonl")

    collection.collect_rows(
        store,
        (collection.CollectionPlan(first, (run,)), collection.CollectionPlan(second, (run,))),
        120,
        Console(file=stream),
    )

    assert calls == ["first", "second", "second"]
    assert store.row_count == 3
    assert stream.getvalue().count("collected 3 fresh runs") == 1
    assert "2 targets: collected 3 fresh runs" in stream.getvalue()


def test_collection_plan_counts_cache_and_missing_rows(tmp_path: Path) -> None:
    report = tmp_path / "report.jsonl"
    write_report(report, make_record(0, started_at="2026-07-04T12:00:00Z", wall_sec=1.0))
    target = make_target()
    file_spec = models.FileSpec("file.egg", ROOT / "file.egg", "sha256:file")
    requests = (collection.BenchmarkRequest(models.EndpointRequest(target.request, "off"), (file_spec,)),)

    store = ReportStore(report)
    (plan,) = collection.plan_collection(store, requests, {target.request: target}, 2, 120, False)
    (force_plan,) = collection.plan_collection(store, requests, {target.request: target}, 2, 120, True)

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
    requests = (
        collection.BenchmarkRequest(models.EndpointRequest(target.request, "off"), (file_spec,)),
        collection.BenchmarkRequest(models.EndpointRequest(target.request, "proofs"), (file_spec,)),
    )

    store = ReportStore(report)
    (plan,) = collection.plan_collection(store, requests, {target.request: target}, 1, 120, False)
    (forced,) = collection.plan_collection(store, requests, {target.request: target}, 1, 120, True)

    baseline, candidate = plan.runs
    assert baseline.cached_statuses == ("success",)
    assert baseline.missing_observations == 0
    assert candidate.cached_statuses == ()
    assert candidate.missing_observations == 1
    assert [run.missing_observations for run in forced.runs] == [1, 1]


@pytest.mark.parametrize("status", ["failure", "timed-out"])
def test_cached_failure_stops_only_its_condition_until_forced(tmp_path: Path, status: models.Status) -> None:
    store = ReportStore(tmp_path / "report.jsonl")
    store.append(make_record(0, started_at="2026-07-04T12:00:00Z", status=status))
    target = make_target()
    requests = (models.EndpointRequest(target.request, "off"),)
    benchmark_requests = tuple(collection.BenchmarkRequest(request, (FILE_SPEC,)) for request in requests)
    (plan,) = collection.plan_collection(store, benchmark_requests, {target.request: target}, 3, 120, False)
    assert plan.total_missing_observations == 0
    assert collection.label_has_enough_rows(store, target, requests, (FILE_SPEC,), 3, 120)
    assert not collection.label_has_enough_rows(store, target, requests, (FILE_SPEC,), 3, 121)

    endpoints = (
        models.EndpointRequest(target.request, "off"),
        models.EndpointRequest(target.request, "proofs"),
        models.EndpointRequest(target.request, "off", "ee"),
    )
    other_file = models.FileSpec("other.egg", ROOT / "other.egg", "sha256:other")
    benchmark_requests = tuple(collection.BenchmarkRequest(endpoint, (FILE_SPEC, other_file)) for endpoint in endpoints)
    (plan,) = collection.plan_collection(store, benchmark_requests, {target.request: target}, 3, 120, False)
    assert [run.missing_observations for run in plan.runs] == [0, 3, 3, 3, 3, 3]
    benchmark_requests = tuple(collection.BenchmarkRequest(endpoint, (FILE_SPEC,)) for endpoint in endpoints)
    (forced,) = collection.plan_collection(store, benchmark_requests, {target.request: target}, 3, 120, True)
    assert [run.missing_observations for run in forced.runs] == [3, 3, 3]
    assert store.row_count == 1


@pytest.mark.parametrize("status", ["failure", "timed-out"])
def test_fresh_failure_stops_only_its_condition(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, status: models.Status
) -> None:
    target = make_target(binary_path=ROOT / "egglog-experimental")
    runs = (
        planned_run(required=3),
        planned_run(treatment="proofs", required=3),
        planned_run(filename="other.egg", required=3),
    )
    calls: list[tuple[str, models.Treatment]] = []

    def observe(
        _binary: Path,
        _checkout: Path,
        file: models.FileSpec,
        treatment: models.Treatment,
        _timeout: int,
        _encoding: models.DisequalityEncoding,
    ) -> collection.ProcessObservation:
        calls.append((file.display_path, treatment))
        if file.display_path == "file.egg" and treatment == "off":
            return collection.ProcessObservation(
                processes.TimingResult(status, processes.TimingRow(), processes.ErrorRow("failed")), None
            )
        return collection.ProcessObservation(
            processes.TimingResult("success", processes.TimingRow(wall_sec=0.25), None), make_timing_summary()
        )

    monkeypatch.setattr(collection, "run_process", observe)
    store = ReportStore(tmp_path / "report.jsonl")
    collection.collect_rows(store, collection.CollectionPlan(target, runs), 120, Console(file=io.StringIO()))
    assert calls.count(("file.egg", "off")) == 1
    assert calls.count(("file.egg", "proofs")) == calls.count(("other.egg", "off")) == 3
    assert store.row_count == 7
    assert [row["status"] for row in store.records].count(status) == 1


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
    requests = (collection.BenchmarkRequest(models.EndpointRequest(target.request, "off"), (file_spec,)),)
    summary = make_timing_summary()
    success = processes.TimingResult("success", processes.TimingRow(wall_sec=1.25, max_rss_bytes=4096), None)
    monkeypatch.setattr(collection, "run_preflight", lambda *_args: success)
    monkeypatch.setattr(
        collection,
        "run_process",
        lambda *_args: collection.ProcessObservation(success, summary),
    )

    store = ReportStore(report)
    (plan,) = collection.plan_collection(store, requests, {target.request: target}, 1, 120, False)
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

    assert calls == [
        ("--timing-summary", "--memory-limit-bytes"),
        ("--timing-summary", "--memory-limit-bytes", "--proof-extraction"),
    ]


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
        (egglog_binary, ("--timing-summary", "--memory-limit-bytes", "--proof-testing")),
        (egg_binary, ("--timing-summary", "--memory-limit-bytes")),
    ]


def test_preflight_requires_math12_witness_flags_only_for_fresh_math12(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    egg_binary = ROOT / "egg-math-benchmark"
    target = replace(make_target(), engine_binaries=(models.EngineBinary("egg", "sha256:egg", egg_binary),))
    math12 = replace(
        planned_run(treatment="egg", required=1),
        file=models.FileSpec("math12.egg", ROOT / "absent.egg", engines.MATH12_WORKLOAD_SHA256),
    )
    math11 = planned_run(treatment="egg", required=1)
    calls: list[tuple[str, ...]] = []

    def preflight(
        _binary: Path, _checkout: Path, _timeout: int, required_outputs: tuple[str, ...]
    ) -> processes.TimingResult:
        calls.append(required_outputs)
        return processes.TimingResult("success", processes.TimingRow(wall_sec=0.01), None)

    monkeypatch.setattr(collection, "run_preflight", preflight)
    collection.preflight_collection(collection.CollectionPlan(target, (math12,)), 120)
    cached12 = replace(math12, cached_statuses=("success",), missing_observations=0)
    collection.preflight_collection(collection.CollectionPlan(target, (cached12, math11)), 120)

    assert calls == [
        ("--timing-summary", "--memory-limit-bytes", "--iterations", "--check-left", "--check-right"),
        ("--timing-summary", "--memory-limit-bytes"),
    ]


def test_collected_row_uses_selected_engine_binary_and_hash(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
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
    file_spec = models.FileSpec(
        "egglog-experimental/tests/math-microbenchmark-rational.egg",
        ROOT / "egglog-experimental/tests/math-microbenchmark-rational.egg",
        "sha256:math",
    )
    selected_endpoint = models.BenchmarkEndpoint(target, "egg")
    requests = (collection.BenchmarkRequest(models.EndpointRequest(target.request, "egg"), (file_spec,)),)
    success = processes.TimingResult("success", processes.TimingRow(wall_sec=0.5), None)
    observed_binaries: list[Path] = []

    def run_process(binary_path: Path, *_args: object) -> collection.ProcessObservation:
        observed_binaries.append(binary_path)
        return collection.ProcessObservation(success, make_timing_summary())

    monkeypatch.setattr(collection, "run_process", run_process)
    store = ReportStore(tmp_path / "report.jsonl")
    (plan,) = collection.plan_collection(store, requests, {target.request: target}, 1, 120, False)

    collection.collect_rows(store, plan, 120, Console(stderr=True))

    assert observed_binaries == [egg_binary]
    assert store.records[0]["binary_sha256"] == "sha256:egg"
    assert CacheKey.for_endpoint(selected_endpoint, file_spec, 120).binary_sha256 == "sha256:egg"


def test_collect_rows_rejects_unsupported_timing_summary_before_append(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    report = tmp_path / "report.jsonl"
    benchmark_file = tmp_path / "file.egg"
    benchmark_file.write_text("(check (= 1 1))\n", encoding="utf-8")
    file_spec = models.FileSpec("file.egg", benchmark_file, targets.sha256_file(benchmark_file))
    target = make_target(binary_path=ROOT / "egglog-experimental")
    requests = (collection.BenchmarkRequest(models.EndpointRequest(target.request, "off"), (file_spec,)),)

    def write_unsupported_summary(
        command: list[str],
        _checkout_path: Path,
        _timeout_sec: int,
        *,
        native_limit: bool,
    ) -> processes.TimingResult:
        assert native_limit
        summary_path = Path(command[command.index("--timing-summary") + 1])
        summary_path.write_text(
            json.dumps({"schema_version": 1, "rulesets": []}),
            encoding="utf-8",
        )
        return processes.TimingResult("success", processes.TimingRow(wall_sec=1.0), None)

    monkeypatch.setattr(collection, "run_command", write_unsupported_summary)

    store = ReportStore(report)
    (plan,) = collection.plan_collection(store, requests, {target.request: target}, 1, 120, False)
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

    def fake_run_command(
        command: list[str], checkout_path: Path, timeout_sec: int, *, native_limit: bool
    ) -> processes.TimingResult:
        assert native_limit
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
        lambda *_args, **_kwargs: processes.TimingResult("success", processes.TimingRow(wall_sec=1.0), None),
    )

    with pytest.raises(ValueError, match="did not produce --timing-summary"):
        collection.run_process(ROOT / "egglog-experimental", ROOT, file_spec, "off", 120)


def test_run_process_does_not_require_summary_after_failure(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    file_spec = stable_file_spec(tmp_path)
    failure = processes.TimingResult("failure", processes.TimingRow(wall_sec=1.0), processes.ErrorRow("failed"))
    monkeypatch.setattr(collection, "run_command", lambda *_args, **_kwargs: failure)

    observation = collection.run_process(ROOT / "egglog-experimental", ROOT, file_spec, "off", 120)

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
    requests = (collection.BenchmarkRequest(models.EndpointRequest(target.request, "off"), (file_spec,)),)

    def mutate_workload(
        command: list[str],
        _checkout_path: Path,
        _timeout_sec: int,
        *,
        native_limit: bool,
    ) -> processes.TimingResult:
        assert native_limit
        summary_path = Path(command[command.index("--timing-summary") + 1])
        summary_path.write_text(json.dumps(make_timing_summary()), encoding="utf-8")
        if mutated_input == "file":
            benchmark_file.write_text("(check (= 2 2))\n", encoding="utf-8")
        else:
            fact_file.write_text("after\n", encoding="utf-8")
        return processes.TimingResult("success", processes.TimingRow(wall_sec=1.0), None)

    monkeypatch.setattr(collection, "run_command", mutate_workload)
    store = ReportStore(tmp_path / "report.jsonl")
    (plan,) = collection.plan_collection(store, requests, {target.request: target}, 1, 120, False)

    with pytest.raises(ValueError, match=r"workload changed during execution: file\.egg"):
        collection.collect_rows(store, plan, 120, Console(stderr=True))

    assert store.row_count == 0
    assert not store.path.exists()


def test_redirected_collection_logs_each_run_and_one_status_summary(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    target = make_target(binary_path=ROOT / "egglog-experimental")
    plan = collection.CollectionPlan(
        target,
        (
            planned_run(required=1),
            planned_run(treatment="proofs", required=1),
            planned_run(filename="other.egg", required=1),
        ),
    )
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
        "  [1/3] file.egg · off · 1/1: succeeded after 0.250s",
        "  [2/3] file.egg · proofs · 1/1: failed after 0.500s: bad rule more context",
        "  [3/3] other.egg · off · 1/1: timed out after 120 seconds",
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
    assert "off" in rendered
    assert "ETA" not in rendered
    assert "failed after 0.500s: bad rule" in rendered
    assert "abc123: collected 2 fresh runs · 1 successful, 1 failed" in rendered


def test_preflight_requires_math12_flag_only_for_fresh_math12(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    egg_binary = ROOT / "egg-math-benchmark"
    target = replace(make_target(), engine_binaries=(models.EngineBinary("egg", "sha256:egg", egg_binary),))
    math12 = replace(
        planned_run(treatment="egg", required=1),
        file=models.FileSpec("math12.egg", ROOT / "absent.egg", engines.MATH12_WORKLOAD_SHA256),
    )
    math11 = planned_run(treatment="egg", required=1)
    calls: list[tuple[str, ...]] = []

    def preflight(
        _binary: Path, _checkout: Path, _timeout: int, required_outputs: tuple[str, ...]
    ) -> processes.TimingResult:
        calls.append(required_outputs)
        return processes.TimingResult("success", processes.TimingRow(wall_sec=0.01), None)

    monkeypatch.setattr(collection, "run_preflight", preflight)
    collection.preflight_collection(collection.CollectionPlan(target, (math12,)), 120)
    cached12 = replace(math12, cached_statuses=("success",), missing_observations=0)
    collection.preflight_collection(collection.CollectionPlan(target, (cached12, math11)), 120)

    assert calls == [
        ("--timing-summary", "--memory-limit-bytes", "--math12"),
        ("--timing-summary", "--memory-limit-bytes"),
    ]
