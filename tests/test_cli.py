"""Test pair-only benchmark CLI parsing, validation, and orchestration."""

from __future__ import annotations

from pathlib import Path
from typing import Any, cast

import pytest

from benchmarking import benchmark, collection, models, processes, targets, workloads
from benchmarking import output as runner_output
from benchmarking.reports.database import ReportDatabase

from .conftest import ROOT, make_record, make_target, write_report


def test_parse_target_variants() -> None:
    assert targets.parse_target(".") == models.TargetRequest(raw=".", source=".", label=None)
    assert targets.parse_target("main=@main") == models.TargetRequest(raw="main=@main", source="@main", label="main")
    assert targets.parse_target("prev-run=") == models.TargetRequest(raw="prev-run=", source="", label="prev-run")
    assert targets.parse_target("#33") == models.TargetRequest(raw="#33", source="#33", label="#33")
    assert targets.parse_target("candidate=#33") == models.TargetRequest(
        raw="candidate=#33", source="#33", label="candidate"
    )


@pytest.mark.parametrize("raw", ["#", "#0", "#abc", "candidate=#0"])
def test_parse_target_rejects_invalid_pr_targets(raw: str) -> None:
    with pytest.raises(ValueError, match="invalid PR target"):
        targets.parse_target(raw)


def test_pair_cli_defaults_to_current_main_off_vs_proofs() -> None:
    args = benchmark.parse_benchmark_args([])
    baseline, candidate = benchmark.endpoint_requests(args)

    assert baseline == models.EndpointRequest(targets.parse_target("."), "main", "off")
    assert candidate == models.EndpointRequest(targets.parse_target("."), "main", "proofs")
    assert args.detail == "summary"
    assert args.report == benchmark.DEFAULT_REPORT == ".reports.duckdb"
    assert args.command == "benchmark"


def test_compare_target_inherits_candidate_but_compare_backend_stays_main() -> None:
    args = benchmark.parse_benchmark_args(["--target", "mine=@branch", "--backend", "dd"])
    baseline, candidate = benchmark.endpoint_requests(args)

    assert baseline.target == candidate.target == targets.parse_target("mine=@branch")
    assert baseline.backend == "main"
    assert baseline.treatment == "off"
    assert candidate.backend == "dd"
    assert candidate.treatment == "proofs"


def test_pair_cli_accepts_arbitrary_explicit_endpoints() -> None:
    args = benchmark.parse_benchmark_args(
        [
            "--compare-target",
            "old=@origin/main",
            "--compare-backend",
            "dd",
            "--compare-treatment",
            "term",
            "--target",
            "new=.",
            "--backend",
            "main",
            "--treatment",
            "proofs",
            "--detail",
            "rulesets",
        ]
    )
    baseline, candidate = benchmark.endpoint_requests(args)

    assert baseline == models.EndpointRequest(targets.parse_target("old=@origin/main"), "dd", "term")
    assert candidate == models.EndpointRequest(targets.parse_target("new=."), "main", "proofs")
    assert args.detail == "rulesets"


@pytest.mark.parametrize("detail", ["summary", "files", "phases", "rulesets"])
def test_pair_cli_accepts_each_named_detail_level(detail: str) -> None:
    assert benchmark.parse_benchmark_args(["--detail", detail]).detail == detail


@pytest.mark.parametrize(
    "argv",
    [
        ("--treatments", "off,proofs"),
        ("--backend", "main,dd"),
        ("--phase-timings",),
        ("--detailed-timing",),
        ("--duckdb-ui",),
        ("--detail", "3"),
        ("--report", "-"),
    ],
)
def test_pair_cli_rejects_removed_or_unsupported_options(argv: tuple[str, ...]) -> None:
    with pytest.raises(SystemExit):
        benchmark.parse_benchmark_args(argv)


def test_live_report_server_is_opt_in_with_an_optional_port() -> None:
    ordinary = benchmark.parse_benchmark_args([])
    automatic_port = benchmark.parse_benchmark_args(["--serve"])
    fixed_port = benchmark.parse_benchmark_args(["--serve", "--serve-port", "4312"])

    assert not ordinary.serve
    assert ordinary.serve_port is None
    assert automatic_port.serve
    assert automatic_port.serve_port is None
    assert fixed_port.serve
    assert fixed_port.serve_port == 4312


def test_live_report_port_requires_server(capsys: Any) -> None:
    with pytest.raises(SystemExit):
        benchmark.parse_benchmark_args(["--serve-port", "4312"])

    assert "--serve-port requires --serve" in capsys.readouterr().err


@pytest.mark.parametrize("port", ["0", "65536"])
def test_live_report_server_rejects_invalid_ports(port: str) -> None:
    with pytest.raises(SystemExit):
        benchmark.parse_benchmark_args(["--serve", "--serve-port", port])


def test_endpoint_validation_uses_backend_registry(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setitem(
        models.BACKEND_SPECS,
        "future",
        models.BackendSpec(("proofs",), ("--backend", "future"), ("future-backend",)),
    )
    request = targets.parse_target(".")

    args = benchmark.parse_benchmark_args(["--backend", "future"])
    _baseline, candidate = benchmark.endpoint_requests(args)

    assert candidate == models.EndpointRequest(request, "future", "proofs")
    assert targets.backend_flags("future") == ["--backend", "future"]
    assert models.backend_cargo_features(("main", "future")) == ("future-backend",)
    with pytest.raises(ValueError, match="backend future does not support treatment off"):
        models.EndpointRequest(request, "future", "off")


def test_pair_cli_rejects_identical_endpoints_before_target_resolution() -> None:
    args = benchmark.parse_benchmark_args(["--treatment", "off"])

    with pytest.raises(ValueError, match="baseline and candidate endpoints must be different"):
        benchmark.endpoint_requests(args)


def test_comparison_permits_shared_binary_across_different_treatments() -> None:
    target = make_target(binary_sha256="sha256:shared")
    file_spec = models.FileSpec("file.egg", ROOT / "file.egg", "sha256:file")
    baseline = models.BenchmarkEndpoint(target, "main", "off")
    candidate = models.BenchmarkEndpoint(target, "main", "proofs")

    comparison = models.ComparisonSpec(baseline, candidate, (file_spec,), 2, 120)

    assert baseline.cache_identity == ("sha256:shared", "main", "off")
    assert candidate.cache_identity == ("sha256:shared", "main", "proofs")
    assert comparison.baseline.target is comparison.candidate.target


def test_comparison_rejects_identical_cache_endpoints() -> None:
    target = make_target(binary_sha256="sha256:shared")
    file_spec = models.FileSpec("file.egg", ROOT / "file.egg", "sha256:file")
    endpoint = models.BenchmarkEndpoint(target, "main", "proofs")

    with pytest.raises(ValueError, match="baseline and candidate endpoints must be different"):
        models.ComparisonSpec(endpoint, endpoint, (file_spec,), 1, 120)


def test_endpoint_requests_group_one_shared_target_and_two_distinct_targets() -> None:
    shared = targets.parse_target(".")
    baseline = models.EndpointRequest(shared, "main", "off")
    candidate = models.EndpointRequest(shared, "main", "proofs")

    assert benchmark.group_endpoint_requests(baseline, candidate) == ((shared, (baseline, candidate)),)

    other = models.EndpointRequest(targets.parse_target("@origin/main"), "main", "proofs")
    assert benchmark.group_endpoint_requests(baseline, other) == (
        (shared, (baseline,)),
        (other.target, (other,)),
    )


def test_collection_plans_group_only_the_same_resolved_target(monkeypatch: pytest.MonkeyPatch) -> None:
    shared_target = make_target(target_label="shared", binary_sha256="sha256:shared")
    file_spec = models.FileSpec("file.egg", ROOT / "file.egg", "sha256:file")
    comparison = models.ComparisonSpec(
        models.BenchmarkEndpoint(shared_target, "main", "off"),
        models.BenchmarkEndpoint(shared_target, "dd", "proofs"),
        (file_spec,),
        1,
        120,
    )
    observed: list[tuple[models.ResolvedTarget, tuple[models.BenchmarkEndpoint, ...], bool]] = []
    sentinel = cast(collection.CollectionPlan, object())

    def build_plan(
        _database: ReportDatabase,
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

    plans = benchmark.collection_plans(cast(ReportDatabase, object()), comparison, True)

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
    file_spec = models.FileSpec("file.egg", ROOT / "file.egg", "sha256:file")
    comparison = models.ComparisonSpec(
        models.BenchmarkEndpoint(baseline_target, "main", "off"),
        models.BenchmarkEndpoint(candidate_target, "main", "proofs"),
        (file_spec,),
        1,
        120,
    )
    observed: list[models.ResolvedTarget] = []

    def build_plan(
        _database: ReportDatabase,
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

    benchmark.collection_plans(cast(ReportDatabase, object()), comparison, False)

    assert observed == [baseline_target, candidate_target]


def test_shared_target_resolution_builds_union_backend_features(monkeypatch: pytest.MonkeyPatch) -> None:
    request = targets.parse_target(".")
    row = models.TargetRow(".", str(ROOT), "HEAD", "abc123", False)
    target = make_target(binary_path=ROOT / "egglog-experimental")
    file_spec = models.FileSpec("file.egg", ROOT / "file.egg", "sha256:file")
    built_features: list[tuple[str, ...]] = []

    monkeypatch.setattr(collection, "materialize_target_request", lambda *_args: row)

    def build(
        _request: models.TargetRequest,
        _row: models.TargetRow,
        _output: runner_output.RunnerOutput,
        _profile: targets.BuildProfile,
        features: tuple[str, ...],
    ) -> models.ResolvedTarget:
        built_features.append(features)
        return target

    monkeypatch.setattr(collection, "build_resolved_target", build)

    resolved = collection.resolve_targets(
        (
            (
                request,
                (
                    models.EndpointRequest(request, "main", "off"),
                    models.EndpointRequest(request, "dd", "proofs"),
                ),
            ),
        ),
        cast(ReportDatabase, object()),
        (file_spec,),
        1,
        120,
        False,
        ROOT,
        ROOT,
        runner_output.RunnerOutput(),
    )

    assert resolved == {request: target}
    assert built_features == [("dd-backend",)]


def test_same_checkout_target_aliases_build_once_with_union_backend_features(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    baseline_request = targets.parse_target(".")
    candidate_request = targets.parse_target(str(ROOT))
    file_spec = models.FileSpec("file.egg", ROOT / "file.egg", "sha256:file")
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
        _output: runner_output.RunnerOutput,
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
        cast(ReportDatabase, object()),
        (file_spec,),
        1,
        120,
        False,
        ROOT,
        ROOT,
        runner_output.RunnerOutput(),
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
    report = tmp_path / "report.duckdb"
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
    file_spec = models.FileSpec("file.egg", ROOT / "file.egg", "sha256:file")
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
        _output: runner_output.RunnerOutput,
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

    with ReportDatabase(report) as database:
        resolved = collection.resolve_targets(
            groups,
            database,
            (file_spec,),
            1,
            120,
            False,
            tmp_path,
            ROOT,
            runner_output.RunnerOutput(),
        )

    assert materialized == [fresh_request]
    assert builds == [("dd-backend",)]
    assert resolved[cached_request].binary_sha256 == "sha256:cached"
    assert resolved[cached_request].binary_path is None
    assert resolved[fresh_request].binary_sha256 == "sha256:fresh"
    assert resolved[fresh_request].binary_path == binary_path


def test_validate_workloads_rejects_duplicate_cache_identities(tmp_path: Path) -> None:
    benchmark_file = tmp_path / "file.egg"
    benchmark_file.write_text("(check (= 1 1))\n", encoding="utf-8")
    first = models.FileSpec("first.egg", benchmark_file, "sha256:same", fact_directory_sha256="sha256:facts")
    second = models.FileSpec("second.egg", benchmark_file, "sha256:same", fact_directory_sha256="sha256:facts")

    with pytest.raises(ValueError, match=r"first\.egg.*second\.egg.*identical file and fact-directory hashes"):
        workloads.validate_workloads((first, second))


def test_same_file_with_different_fact_contents_is_a_distinct_workload(tmp_path: Path) -> None:
    benchmark_file = tmp_path / "file.egg"
    benchmark_file.write_text("(check (= 1 1))\n", encoding="utf-8")
    first = models.FileSpec("first.egg", benchmark_file, "sha256:same", fact_directory_sha256="sha256:facts-a")
    second = models.FileSpec("second.egg", benchmark_file, "sha256:same", fact_directory_sha256="sha256:facts-b")

    workloads.validate_workloads((first, second))


def test_resolve_files_rejects_executable_prove_benchmark_file(tmp_path: Path) -> None:
    prove_file = tmp_path / "prove.egg"
    prove_file.write_text(
        "; comments may mention (prove ...)\n(datatype Expr)\n(prove (Fact))\n",
        encoding="utf-8",
    )

    with pytest.raises(ValueError, match="explicit prove command"):
        workloads.resolve_files([str(prove_file)], tmp_path)


def test_resolve_files_allows_prove_mentions_in_comments(tmp_path: Path) -> None:
    check_file = tmp_path / "check.egg"
    check_file.write_text(
        "; comments may mention (prove ...)\n(datatype Expr)\n(check (Fact))\n",
        encoding="utf-8",
    )

    assert workloads.resolve_files([str(check_file)], tmp_path)[0].absolute_path == check_file.resolve()


def test_default_workloads_are_the_six_research_cases() -> None:
    files = workloads.resolve_files([], ROOT)
    assert tuple(file.display_path for file in files) == (
        "egglog/tests/math-microbenchmark.egg",
        "egglog-experimental/tests/fixtures/eggcc-2mm-pass1.egg",
        "benchmarks/pointer-analysis-small.egg",
        "egglog/tests/hardboiled_conv1d_32.egg",
        "benchmarks/luminal-llama.egg",
        "egglog/tests/web-demo/herbie.egg",
    )
    pointer = next(file for file in files if file.display_path == "benchmarks/pointer-analysis-small.egg")
    assert pointer.fact_directory == (ROOT / "benchmarks/data/pointer-analysis-small").resolve()
    assert pointer.fact_directory_sha256.startswith("sha256:")


def test_explicit_fact_directory_is_resolved_and_hashed(tmp_path: Path) -> None:
    benchmark_file = tmp_path / "input.egg"
    benchmark_file.write_text('(input Edge "edge.tsv")\n', encoding="utf-8")
    facts = tmp_path / "facts"
    facts.mkdir()
    (facts / "edge.tsv").write_text("a\tb\n", encoding="utf-8")

    (file_spec,) = workloads.resolve_files(["input.egg"], tmp_path, "facts")

    assert file_spec.fact_directory == facts.resolve()
    assert file_spec.fact_directory_sha256 == targets.sha256_directory(facts)


def test_fact_directory_requires_explicit_benchmark_file(tmp_path: Path) -> None:
    with pytest.raises(ValueError, match="requires at least one explicit benchmark file"):
        workloads.resolve_files([], tmp_path, "facts")


def test_main_validates_old_report_before_target_resolution(
    monkeypatch: pytest.MonkeyPatch,
    capsys: Any,
    tmp_path: Path,
) -> None:
    report = tmp_path / "old.duckdb"
    report.write_text("{}\n", encoding="utf-8")
    monkeypatch.setattr(benchmark, "git_root_for_path", lambda _path: ROOT)
    monkeypatch.setattr(
        benchmark,
        "resolve_targets",
        lambda *_args: pytest.fail("an incompatible report must fail before target resolution/build"),
    )

    result = benchmark.main(["--report", str(report), "--rounds", "1"])

    assert result == 2
    assert "invalid or incompatible benchmark report" in capsys.readouterr().err


def test_main_preflights_both_fresh_targets_before_collecting(
    monkeypatch: pytest.MonkeyPatch,
    capsys: Any,
    tmp_path: Path,
) -> None:
    report = tmp_path / "reports.duckdb"
    benchmark_file = tmp_path / "file.egg"
    benchmark_file.write_text("(check (= 1 1))\n", encoding="utf-8")
    file_spec = models.FileSpec("file.egg", benchmark_file, "sha256:file")
    targets_by_label = {
        "old": make_target(target_label="old", binary_sha256="sha256:old", binary_path=tmp_path / "old-bin"),
        "new": make_target(target_label="new", binary_sha256="sha256:new", binary_path=tmp_path / "new-bin"),
    }
    monkeypatch.setattr(benchmark, "git_root_for_path", lambda _path: ROOT)
    monkeypatch.setattr(benchmark, "resolve_files", lambda *_args: (file_spec,))
    monkeypatch.setattr(
        benchmark,
        "resolve_targets",
        lambda request_groups, *_args: {
            request: targets_by_label[request.label or ""] for request, _endpoints in request_groups
        },
    )
    preflighted: list[str] = []

    def fail_new_preflight(plan: collection.CollectionPlan, _timeout: int) -> processes.TimingResult:
        label = plan.target.display_label
        preflighted.append(label)
        if label == "new":
            raise ValueError("target new does not support --timing-summary")
        return processes.TimingResult("success", processes.TimingRow(wall_sec=0.1), None)

    monkeypatch.setattr(benchmark, "preflight_collection", fail_new_preflight)
    monkeypatch.setattr(
        benchmark,
        "collect_rows",
        lambda *_args: pytest.fail("collection must wait until both targets pass preflight"),
    )

    result = benchmark.main(
        [
            "--report",
            str(report),
            "--rounds",
            "1",
            "--compare-target",
            "old=.",
            "--compare-treatment",
            "proofs",
            "--target",
            "new=.",
            "--treatment",
            "proofs",
            "file.egg",
        ]
    )

    assert result == 2
    assert preflighted == ["old", "new"]
    with ReportDatabase(report) as database:
        assert database._connection.execute("SELECT count(*) FROM report_rows").fetchone() == (0,)
    assert "does not support --timing-summary" in capsys.readouterr().err
