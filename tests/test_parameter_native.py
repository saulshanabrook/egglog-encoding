"""Validate native commands, physical input identities, builds, and reports."""

import subprocess
import sys
from dataclasses import replace
from pathlib import Path
from typing import cast

import pytest
from rich.console import Console

from benchmarking import benchmark, collection, models, targets, workloads
from benchmarking.engines import Engine, Treatment
from benchmarking.reports.analysis import analyze_pair
from benchmarking.reports.presentation import build_report_catalog
from benchmarking.reports.render import render_markdown_report_document
from benchmarking.reports.store import CacheKey, ReportStore, serialize_report_record
from tests.report_fixtures import make_record, make_target

METHODS: tuple[Treatment, ...] = ("egg-de", "egg-ee", "egg-nee", "egg-oee")


@pytest.mark.parametrize("treatment", METHODS)
def test_native_command_uses_the_physical_input(treatment: Treatment, tmp_path: Path) -> None:
    native = models.FileSpec("fixture.in", tmp_path / "fixture.in", "sha256:native")
    logical = models.FileSpec(
        "fixture.egg", tmp_path / "fixture.egg", "sha256:egglog", engine_inputs=((cast(Engine, treatment), native),)
    )
    binary = tmp_path / treatment
    expected = [str(binary), str(native.absolute_path), "100000", "10000"]
    assert targets.workload_command(binary, native, treatment) == expected
    assert targets.workload_command(binary, logical, treatment) == expected
    with pytest.raises(ValueError, match="native .in"):
        targets.workload_command(binary, replace(logical, engine_inputs=()), treatment)
    with pytest.raises(ValueError, match="fact-directory"):
        targets.workload_command(binary, replace(native, fact_directory=tmp_path), treatment)
    with pytest.raises(ValueError, match="only supported by egglog"):
        targets.workload_command(binary, native, treatment, "ee")
    with pytest.raises(ValueError, match="only supported by egglog"):
        models.EndpointRequest(make_target().request, treatment, "ee")
    args = benchmark.parse_benchmark_args([str(native.absolute_path), "--treatment", treatment])
    assert benchmark.endpoint_requests(args)[1].treatment == treatment


def test_registered_workload_binds_native_file_with_its_own_hash(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    egglog = tmp_path / "parameter-analysis.egg"
    native = egglog.with_suffix(".in")
    egglog.write_text("(check-contradiction)\n")
    native.write_text("1\n2\n")
    monkeypatch.setattr(workloads, "PARAMETER_WORKLOAD_PATH", egglog)
    (logical,) = workloads.resolve_files([egglog.name], tmp_path)
    assert logical.sha256 == targets.sha256_file(egglog)
    assert logical.for_engine("egglog") == logical
    for method in METHODS:
        physical = logical.for_engine(cast(Engine, method))
        assert physical.absolute_path == native
        assert physical.display_path == native.name
        assert physical.sha256 == targets.sha256_file(native)
        assert physical.sha256 != logical.sha256


@pytest.mark.parametrize("treatment", METHODS)
def test_native_success_is_measured_without_a_summary(treatment: Treatment, tmp_path: Path) -> None:
    source = tmp_path / "fixture.in"
    source.write_text("1\n2\n")
    fixture = models.FileSpec(source.name, source, targets.sha256_file(source))
    binary = tmp_path / "native"
    binary.write_text(
        f"#!{sys.executable}\nimport sys\n"
        f"assert sys.argv[1:] == [{str(source)!r}, '100000', '10000']\n"
        "print('method,base,diseq_num,contradiction')\n"
        "print('ee,100000,00010000,Y')\n"
    )
    binary.chmod(0o755)
    observation = collection.run_process(binary, tmp_path, fixture, treatment, 10)
    assert observation.result.status == "success"
    assert observation.result.timing.wall_sec is not None
    assert observation.result.timing.wall_sec > 0
    assert observation.timing_summary is None


def test_native_nonzero_exit_is_a_retained_process_failure(tmp_path: Path) -> None:
    source = tmp_path / "fixture.in"
    source.write_text("1\n2\n")
    fixture = models.FileSpec(source.name, source, targets.sha256_file(source))
    binary = tmp_path / "native"
    binary.write_text(f"#!{sys.executable}\nraise SystemExit(7)\n")
    binary.chmod(0o755)
    observation = collection.run_process(binary, tmp_path, fixture, "egg-ee", 10)
    assert observation.result.status == "failure"
    assert observation.result.timing.wall_sec is not None
    assert observation.result.error is not None
    assert observation.result.error.exit_code == 7
    assert observation.timing_summary is None


def test_native_cache_and_plan_use_physical_input_identity(tmp_path: Path) -> None:
    target = replace(
        make_target(),
        engine_binaries=tuple(models.EngineBinary(cast(Engine, method), "sha256:bin", None) for method in METHODS),
    )
    native = models.FileSpec("fixture.in", tmp_path / "fixture.in", "sha256:native")
    logical = models.FileSpec(
        "fixture.egg",
        tmp_path / "fixture.egg",
        "sha256:egglog",
        engine_inputs=tuple((cast(Engine, method), native) for method in METHODS),
    )
    endpoints = tuple(models.BenchmarkEndpoint(target, method) for method in METHODS)
    store = ReportStore(tmp_path / "report.jsonl")
    record = make_record(0, started_at="2026-09-30T00:00:00Z", treatment="egg-ee", file_sha256=native.sha256)
    record["file_path"] = native.display_path
    record["timing_summary"] = None
    store.append(record)
    store = ReportStore(store.path)
    assert CacheKey.for_endpoint(endpoints[1], logical, 120).file_sha256 == native.sha256
    plan = collection.build_collection_plan(store, target, endpoints, (logical,), 1, 120, False)
    assert [(run.treatment, run.missing_observations) for run in plan.runs] == [
        ("egg-de", 1),
        ("egg-ee", 0),
        ("egg-nee", 1),
        ("egg-oee", 1),
    ]
    assert all(run.file == native for run in plan.runs)
    assert store.records[0]["timing_summary"] is None
    record["treatment"] = "off"
    with pytest.raises(ValueError, match="missing its timing summary"):
        serialize_report_record(record)


@pytest.mark.parametrize("treatment", METHODS)
@pytest.mark.parametrize("profile", ["release", "profiling"])
def test_native_build_uses_the_isolated_manifest_and_selected_profile(
    treatment: Treatment, profile: targets.BuildProfile, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    native = tmp_path / "benchmarks/disequality/native"
    target_dir = tmp_path / "benchmarks/local/parameter-native/target"
    binary = target_dir / profile / treatment
    binary.parent.mkdir(parents=True)
    binary.write_text("binary")
    calls: list[list[str]] = []

    def run(command: list[str], **kwargs: object) -> subprocess.CompletedProcess[str]:
        assert kwargs["cwd"] == tmp_path
        assert kwargs["check"] is True
        calls.append(command)
        return subprocess.CompletedProcess(command, 0)

    monkeypatch.setattr(targets.subprocess, "run", run)
    row = models.TargetRow(".", str(tmp_path), "HEAD", "abc", False)
    actual, digest = targets.build_target(row, Console(quiet=True), profile, cast(Engine, treatment))
    assert actual == binary
    assert digest == targets.sha256_file(binary)
    assert calls == [
        [
            "cargo",
            "build",
            *(["--release"] if profile == "release" else ["--profile", profile]),
            "--locked",
            "--manifest-path",
            str(native / "Cargo.toml"),
            "--target-dir",
            str(target_dir),
            "--bin",
            treatment,
        ],
    ]


def test_native_preflight_never_launches_help_or_conversion(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    binary = tmp_path / "egg-ee"
    target = replace(make_target(), engine_binaries=(models.EngineBinary("egg-ee", "sha256:bin", binary),))
    fixture = models.FileSpec("fixture.in", tmp_path / "fixture.in", "sha256:file")
    endpoint = models.BenchmarkEndpoint(target, "egg-ee")
    store = ReportStore(tmp_path / "report.jsonl")

    def unexpected_command(*args: object, **kwargs: object) -> None:
        pytest.fail("native preflight must not launch a process")

    monkeypatch.setattr(collection, "run_command", unexpected_command)
    fresh = collection.build_collection_plan(store, target, (endpoint,), (fixture,), 1, 120, False)
    collection.preflight_collection(fresh, 120)
    record = make_record(0, started_at="2026-09-30T00:00:00Z", treatment="egg-ee")
    record["timing_summary"] = None
    store.append(record)
    cached = collection.build_collection_plan(store, target, (endpoint,), (fixture,), 1, 120, False)
    assert cached.total_missing_observations == 0
    collection.preflight_collection(cached, 120)
    forced = collection.build_collection_plan(store, target, (endpoint,), (fixture,), 1, 120, True)
    collection.preflight_collection(forced, 120)


def test_native_detailed_report_uses_bound_inputs_and_marks_phases_unavailable(tmp_path: Path) -> None:
    target = replace(make_target(), engine_binaries=(models.EngineBinary("egg-ee", "sha256:native-bin", None),))
    native = models.FileSpec("fixture.in", tmp_path / "fixture.in", "sha256:native-file")
    logical = models.FileSpec(
        "fixture.egg", tmp_path / "fixture.egg", "sha256:file", engine_inputs=(("egg-ee", native),)
    )
    comparison = models.ComparisonSpec(
        models.BenchmarkEndpoint(target, "off"),
        models.BenchmarkEndpoint(target, "egg-ee"),
        (logical,),
        2,
        120,
    )
    store = ReportStore(tmp_path / "report.jsonl")
    for index in range(2):
        store.append(make_record(index, started_at=f"2026-09-30T00:00:0{index}Z", wall_sec=2.0))
        record = make_record(
            index,
            started_at=f"2026-09-30T00:00:0{index}Z",
            treatment="egg-ee",
            binary_sha256="sha256:native-bin",
            file_sha256=native.sha256,
            wall_sec=1.0,
        )
        record["file_path"] = native.display_path
        record["timing_summary"] = None
        store.append(record)
    view = analyze_pair(store.grouped_report(), comparison, "rulesets")
    assert view.summary[0].ratio.estimate.point == 0.5
    assert view.timing == ()
    markdown = render_markdown_report_document(
        build_report_catalog(store.grouped_report(), comparison, detail="rulesets")
    )
    assert "Phase timings are unavailable" in markdown
    assert "Timing unavailable" in markdown
