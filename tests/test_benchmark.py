"""Test benchmark CLI parsing, comparison composition, and main orchestration."""

from __future__ import annotations

import json
import os
from pathlib import Path
from typing import Any

import pytest

import bench as entrypoint
from benchmarking import benchmark, collection, models, profile, targets
from benchmarking.reports.grouped import grouped_report_path
from benchmarking.reports.store import GroupedReport, ReportStore

from .report_fixtures import ROOT, make_record, make_target, write_report

FILE_SPEC = models.FileSpec("file.egg", ROOT / "file.egg", "sha256:file")


def test_public_entrypoint_dispatches_benchmark_and_profile(monkeypatch: pytest.MonkeyPatch) -> None:
    calls: list[tuple[str, tuple[str, ...]]] = []

    def benchmark_main(argv: tuple[str, ...]) -> int:
        calls.append(("benchmark", argv))
        return 3

    def profile_main(argv: tuple[str, ...]) -> int:
        calls.append(("profile", argv))
        return 4

    monkeypatch.setattr(benchmark, "main", benchmark_main)
    monkeypatch.setattr(profile, "main", profile_main)

    assert entrypoint.main(("--rounds", "1")) == 3
    assert entrypoint.main(("profile", "file.egg")) == 4
    assert calls == [("benchmark", ("--rounds", "1")), ("profile", ("file.egg",))]


def test_pair_cli_defaults_to_current_main_off_vs_proofs() -> None:
    args = benchmark.parse_benchmark_args([])
    baseline, candidate = benchmark.endpoint_requests(args)

    assert baseline == models.EndpointRequest(targets.parse_target("."), "off")
    assert candidate == models.EndpointRequest(targets.parse_target("."), "proofs")
    assert args.detail == "summary"
    assert args.command == "benchmark"


def test_compare_target_inherits_candidate_target() -> None:
    args = benchmark.parse_benchmark_args(["--target", "mine=@branch"])
    baseline, candidate = benchmark.endpoint_requests(args)

    assert baseline.target == candidate.target == targets.parse_target("mine=@branch")
    assert baseline.treatment == "off"
    assert candidate.treatment == "proofs"


def test_pair_cli_accepts_arbitrary_explicit_endpoints() -> None:
    args = benchmark.parse_benchmark_args(
        [
            "--compare-target",
            "old=@origin/main",
            "--compare-treatment",
            "term",
            "--target",
            "new=.",
            "--treatment",
            "proofs",
            "--detail",
            "rulesets",
        ]
    )
    baseline, candidate = benchmark.endpoint_requests(args)

    assert baseline == models.EndpointRequest(targets.parse_target("old=@origin/main"), "term")
    assert candidate == models.EndpointRequest(targets.parse_target("new=."), "proofs")
    assert args.detail == "rulesets"


def test_pair_cli_accepts_egg_treatments() -> None:
    args = benchmark.parse_benchmark_args(["--treatment", "egg-proof-testing"])
    _baseline, candidate = benchmark.endpoint_requests(args)

    assert candidate.treatment == "egg-proof-testing"


@pytest.mark.parametrize("detail", ["summary", "files", "phases", "rulesets"])
def test_pair_cli_accepts_each_named_detail_level(detail: str) -> None:
    assert benchmark.parse_benchmark_args(["--detail", detail]).detail == detail


@pytest.mark.parametrize(
    "argv",
    [
        ("--treatments", "off,proofs"),
        ("--phase-timings",),
        ("--detailed-timing",),
        ("--serve",),
        ("--serve-port", "4312"),
        ("--detail", "3"),
        ("--report", "-"),
    ],
)
def test_pair_cli_rejects_removed_or_unsupported_options(argv: tuple[str, ...]) -> None:
    with pytest.raises(SystemExit):
        benchmark.parse_benchmark_args(argv)


def test_interactive_report_is_opt_in() -> None:
    ordinary = benchmark.parse_benchmark_args([])
    interactive = benchmark.parse_benchmark_args(["--open"])

    assert not ordinary.open
    assert interactive.open


def test_pair_cli_rejects_identical_endpoints_before_target_resolution() -> None:
    args = benchmark.parse_benchmark_args(["--treatment", "off"])

    with pytest.raises(ValueError, match="baseline and candidate endpoints must be different"):
        benchmark.endpoint_requests(args)


def test_comparison_permits_shared_binary_across_different_treatments() -> None:
    target = make_target(binary_sha256="sha256:shared")
    baseline = models.BenchmarkEndpoint(target, "off")
    candidate = models.BenchmarkEndpoint(target, "proofs")

    comparison = models.ComparisonSpec(baseline, candidate, (FILE_SPEC,), 2, 120)

    assert baseline.cache_identity == ("sha256:shared", "off", "nee")
    assert candidate.cache_identity == ("sha256:shared", "proofs", "nee")
    assert comparison.baseline.target is comparison.candidate.target


def test_comparison_rejects_identical_cache_endpoints() -> None:
    target = make_target(binary_sha256="sha256:shared")
    endpoint = models.BenchmarkEndpoint(target, "proofs")

    with pytest.raises(ValueError, match="baseline and candidate endpoints must be different"):
        models.ComparisonSpec(endpoint, endpoint, (FILE_SPEC,), 1, 120)


def test_endpoint_requests_group_one_shared_target_and_two_distinct_targets() -> None:
    shared = targets.parse_target(".")
    baseline = models.EndpointRequest(shared, "off")
    candidate = models.EndpointRequest(shared, "proofs")

    assert benchmark.group_endpoint_requests(baseline, candidate) == ((shared, (baseline, candidate)),)

    other = models.EndpointRequest(targets.parse_target("@origin/main"), "proofs")
    assert benchmark.group_endpoint_requests(baseline, other) == (
        (shared, (baseline,)),
        (other.target, (other,)),
    )


def test_main_validates_old_report_before_target_resolution(
    monkeypatch: pytest.MonkeyPatch,
    capsys: Any,
    tmp_path: Path,
) -> None:
    report = tmp_path / "old.jsonl"
    old = dict(make_record(0, started_at="2026-07-04T12:00:00Z"))
    del old["report_schema_version"]
    report.write_text(json.dumps(old) + "\n", encoding="utf-8")
    monkeypatch.setattr(benchmark, "git_root_for_path", lambda _path: ROOT)
    monkeypatch.setattr(
        benchmark,
        "resolve_targets",
        lambda *_args: pytest.fail("an incompatible report must fail before target resolution/build"),
    )

    result = benchmark.main(["--report", str(report), "--rounds", "1"])

    assert result == 2
    assert "invalid or incompatible benchmark report" in capsys.readouterr().err


def test_main_reports_interactive_write_oserror(
    monkeypatch: pytest.MonkeyPatch,
    capsys: Any,
    tmp_path: Path,
) -> None:
    report = tmp_path / "reports.jsonl"
    write_report(
        report,
        make_record(0, started_at="2026-07-17T00:00:00Z", treatment="off"),
        make_record(1, started_at="2026-07-17T00:00:01Z", treatment="proofs"),
    )
    target = make_target()
    monkeypatch.setattr(benchmark, "git_root_for_path", lambda _path: ROOT)
    monkeypatch.setattr(benchmark, "resolve_files", lambda *_args: (FILE_SPEC,))
    monkeypatch.setattr(
        benchmark,
        "resolve_targets",
        lambda groups, *_args: {request: target for request, _endpoints in groups},
    )

    def fail_write(*_args: object) -> Path:
        raise PermissionError("[bold]read-only[/bold] destination")

    monkeypatch.setattr(benchmark, "write_interactive_report", fail_write)

    result = benchmark.main(["--report", str(report), "--rounds", "1", "--timeout-sec", "120", "--open", "file.egg"])

    assert result == 2
    assert "[bold]read-only[/bold] destination" in capsys.readouterr().err


def test_main_preflights_both_fresh_targets_before_collecting(
    monkeypatch: pytest.MonkeyPatch,
    capsys: Any,
    tmp_path: Path,
) -> None:
    report = tmp_path / "reports.jsonl"
    targets_by_label = {
        "old": make_target(target_label="old", binary_sha256="sha256:old", binary_path=tmp_path / "old-bin"),
        "new": make_target(target_label="new", binary_sha256="sha256:new", binary_path=tmp_path / "new-bin"),
    }
    monkeypatch.setattr(benchmark, "git_root_for_path", lambda _path: ROOT)
    monkeypatch.setattr(benchmark, "resolve_files", lambda *_args: (FILE_SPEC,))
    monkeypatch.setattr(
        benchmark,
        "resolve_targets",
        lambda request_groups, *_args: {
            request: targets_by_label[request.label or ""] for request, _endpoints in request_groups
        },
    )
    preflighted: list[str] = []

    def fail_new_preflight(plan: collection.CollectionPlan, _timeout: int) -> None:
        label = plan.target.display_label
        preflighted.append(label)
        if label == "new":
            raise ValueError("target new does not support --timing-summary")

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
    assert not report.exists()
    assert "does not support --timing-summary" in capsys.readouterr().err


def test_cached_main_writes_all_samples_but_reports_requested_rounds_from_same_snapshot(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    path = tmp_path / "report.jsonl"
    treatments: tuple[models.Treatment, ...] = ("off", "proofs")
    records = [
        make_record(index, started_at=f"2026-09-30T00:00:{index:02d}Z", treatment=treatment, target_label="original")
        for treatment in treatments
        for index in range(10)
    ]
    write_report(path, *records)
    os.utime(path, ns=(1_000_000_000, 1_000_000_000))
    before = path.stat()
    target = make_target(target_label="new-label")
    monkeypatch.setattr(benchmark, "git_root_for_path", lambda _path: ROOT)
    monkeypatch.setattr(benchmark, "resolve_files", lambda *_args: (FILE_SPEC,))
    monkeypatch.setattr(benchmark, "resolve_targets", lambda groups, *_args: {request: target for request, _ in groups})
    observed: list[GroupedReport] = []
    original_write = benchmark.write_grouped_report
    original_catalog = benchmark.build_report_catalog

    def write(snapshot: GroupedReport, destination: Path) -> Path:
        observed.append(snapshot)
        return original_write(snapshot, destination)

    def catalog(snapshot: GroupedReport, comparison: models.ComparisonSpec, detail: models.DetailLevel) -> Any:
        assert observed == [snapshot]
        assert comparison.rounds == 5
        assert len(snapshot.records) == 20
        assert {tuple(group["labels"]) for group in snapshot.data["groups"]} == {("original",)}
        return original_catalog(snapshot, comparison, detail)

    monkeypatch.setattr(benchmark, "write_grouped_report", write)
    monkeypatch.setattr(benchmark, "build_report_catalog", catalog)

    assert benchmark.main(["--report", str(path), "--rounds", "5", "--timeout-sec", "120", "file.egg"]) == 0
    assert len(observed) == 1
    assert path.stat().st_mtime_ns == before.st_mtime_ns
    data = json.loads(grouped_report_path(path).read_bytes())
    assert [len(group["samples"]) for group in data["groups"]] == [10, 10]


@pytest.mark.parametrize("failure", [ValueError, KeyboardInterrupt])
def test_main_refreshes_grouped_snapshot_after_partial_collection(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, failure: type[BaseException]
) -> None:
    path = tmp_path / "report.jsonl"
    target = make_target()
    monkeypatch.setattr(benchmark, "git_root_for_path", lambda _path: ROOT)
    monkeypatch.setattr(benchmark, "resolve_files", lambda *_args: (FILE_SPEC,))
    monkeypatch.setattr(benchmark, "resolve_targets", lambda groups, *_args: {request: target for request, _ in groups})
    monkeypatch.setattr(benchmark, "preflight_collection", lambda *_args: None)

    def collect(store: ReportStore, *_args: object) -> None:
        store.append(make_record(0, started_at="2026-09-30T00:00:00Z", status="failure"))
        raise failure("collection stopped")

    monkeypatch.setattr(benchmark, "collect_rows", collect)
    argv = ["--report", str(path), "--rounds", "1", "--timeout-sec", "120", "file.egg"]
    if failure is KeyboardInterrupt:
        with pytest.raises(KeyboardInterrupt, match="collection stopped"):
            benchmark.main(argv)
    else:
        assert benchmark.main(argv) == 2
    data = json.loads(grouped_report_path(path).read_bytes())
    assert len(data["groups"]) == 1
    assert [sample["status"] for sample in data["groups"][0]["samples"]] == ["failure"]


def test_grouped_write_failure_does_not_mask_collection_failure(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, capsys: Any
) -> None:
    path = tmp_path / "report.jsonl"
    target = make_target()
    monkeypatch.setattr(benchmark, "git_root_for_path", lambda _path: ROOT)
    monkeypatch.setattr(benchmark, "resolve_files", lambda *_args: (FILE_SPEC,))
    monkeypatch.setattr(benchmark, "resolve_targets", lambda groups, *_args: {request: target for request, _ in groups})

    def fail_preflight(*_args: object) -> None:
        raise ValueError("original collection failure")

    def fail_write(*_args: object) -> Path:
        raise PermissionError("snapshot destination unavailable")

    monkeypatch.setattr(benchmark, "preflight_collection", fail_preflight)
    monkeypatch.setattr(benchmark, "write_grouped_report", fail_write)
    assert benchmark.main(["--report", str(path), "--rounds", "1", "file.egg"]) == 2
    output = capsys.readouterr().err
    assert "could not refresh grouped report" in output
    assert "original collection failure" in output


def test_duplicate_physical_inputs_fail_before_building(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    native = models.FileSpec("parameter.in", tmp_path / "parameter.in", "sha256:native")
    logical = models.FileSpec(
        "parameter.egg",
        tmp_path / "parameter.egg",
        "sha256:egglog",
        engine_inputs=(("egg-ee", native), ("egg-de", native)),
    )
    monkeypatch.setattr(benchmark, "resolve_files", lambda *args: (logical, native))
    monkeypatch.setattr(benchmark, "resolve_targets", lambda *args: pytest.fail("must reject before building"))
    assert (
        benchmark.main(
            [
                "--treatment",
                "egg-ee",
                "--compare-treatment",
                "egg-de",
                "--report",
                str(tmp_path / "cache.jsonl"),
            ]
        )
        == 2
    )
    assert not (tmp_path / "cache.jsonl").exists()
