"""Test benchmark CLI parsing, comparison composition, and main orchestration."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest

import bench as entrypoint
from benchmarking import benchmark, collection, models, profile, targets

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

    assert baseline == models.EndpointRequest(targets.parse_target("."), "main", "off")
    assert candidate == models.EndpointRequest(targets.parse_target("."), "main", "proofs")
    assert args.detail == "summary"
    assert args.command == "benchmark"


def test_compare_target_inherits_candidate_but_compare_backend_stays_main() -> None:
    args = benchmark.parse_benchmark_args(["--target", "mine=@branch", "--backend", "dd"])
    baseline, candidate = benchmark.endpoint_requests(args)

    assert baseline.target == candidate.target == targets.parse_target("mine=@branch")
    assert baseline.backend == "main"
    assert baseline.treatment == "off"
    assert candidate.backend == "dd"
    assert candidate.treatment == "proofs"


def test_dd_rejects_explicit_proof_extraction_treatment() -> None:
    args = benchmark.parse_benchmark_args(["--backend", "dd", "--treatment", "proof-extraction"])

    with pytest.raises(ValueError, match="backend dd does not support treatment proof-extraction"):
        benchmark.endpoint_requests(args)


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
    baseline = models.BenchmarkEndpoint(target, "main", "off")
    candidate = models.BenchmarkEndpoint(target, "main", "proofs")

    comparison = models.ComparisonSpec(baseline, candidate, (FILE_SPEC,), 2, 120)

    assert baseline.cache_identity == ("sha256:shared", "main", "off")
    assert candidate.cache_identity == ("sha256:shared", "main", "proofs")
    assert comparison.baseline.target is comparison.candidate.target


def test_proof_extraction_has_a_distinct_cache_identity_from_proofs() -> None:
    target = make_target(binary_sha256="sha256:shared")
    proofs = models.BenchmarkEndpoint(target, "main", "proofs")
    extraction = models.BenchmarkEndpoint(target, "main", "proof-extraction")

    assert proofs.cache_identity == ("sha256:shared", "main", "proofs")
    assert extraction.cache_identity == ("sha256:shared", "main", "proof-extraction")
    assert proofs.cache_identity != extraction.cache_identity


def test_comparison_rejects_identical_cache_endpoints() -> None:
    target = make_target(binary_sha256="sha256:shared")
    endpoint = models.BenchmarkEndpoint(target, "main", "proofs")

    with pytest.raises(ValueError, match="baseline and candidate endpoints must be different"):
        models.ComparisonSpec(endpoint, endpoint, (FILE_SPEC,), 1, 120)


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

    result = benchmark.main(["--report", str(report), "--rounds", "1", "--open", "file.egg"])

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
    assert report.read_text(encoding="utf-8") == ""
    assert "does not support --timing-summary" in capsys.readouterr().err
