"""Check encoding-aware benchmark selection, subprocess commands, and cache identities."""

from dataclasses import replace
from pathlib import Path

import pytest

from benchmarking import benchmark, collection, models, targets
from benchmarking.engines import MATH_WORKLOAD_PATH
from benchmarking.reports.store import CacheKey, ReportStore
from tests.report_fixtures import make_record, make_target


def test_encoding_endpoints_and_cached_results_are_distinct(tmp_path: Path) -> None:
    args = benchmark.parse_benchmark_args(["--treatment", "off", "--disequality-encoding", "ee"])
    before, after = benchmark.endpoint_requests(args)
    assert (before.disequality_encoding, after.disequality_encoding) == ("nee", "ee")
    target = make_target()
    baseline = models.BenchmarkEndpoint(target, "off", "nee")
    candidate = models.BenchmarkEndpoint(target, "off", "ee")
    file = models.FileSpec("test.egg", tmp_path / "test.egg", "sha256:file")
    models.ComparisonSpec(baseline, candidate, (file,), 1, 120)
    assert CacheKey.for_endpoint(baseline, file, 120) != CacheKey.for_endpoint(candidate, file, 120)
    store = ReportStore(tmp_path / "results.jsonl")
    store.append(make_record(0, started_at="2026-09-16T00:00:00Z"))
    plan = collection.build_collection_plan(store, target, (baseline, candidate), (file,), 1, 120, False)
    assert [(run.disequality_encoding, run.missing_observations) for run in plan.runs] == [("nee", 0), ("ee", 1)]


def test_encoding_flags_depend_only_on_endpoint_not_workload(tmp_path: Path) -> None:
    file = models.FileSpec("test.egg", tmp_path / "test.egg", "sha256:file")
    # Command construction does not need to read or classify the workload.
    command = targets.workload_command(Path("binary"), file, "proofs")
    assert "--disequality-encoding" not in command
    assert "--proofs" in command
    command = targets.workload_command(Path("binary"), file, "proofs", "ee")
    assert command[command.index("--disequality-encoding") + 1] == "ee"
    assert "--proofs" in command
    with pytest.raises(ValueError, match="only supported by egglog"):
        models.EndpointRequest(make_target().request, "egg", "ee")
    native_file = replace(file, absolute_path=Path(__file__).resolve().parents[1] / MATH_WORKLOAD_PATH)
    assert targets.workload_command(Path("binary"), native_file, "egg") == ["binary", "--proof-mode", "off"]
    with pytest.raises(ValueError, match="only supported by egglog"):
        targets.workload_command(Path("binary"), native_file, "egg", "ee")


def test_encoding_is_persisted_and_reconstructed(tmp_path: Path) -> None:
    from benchmarking.reports.interactive_runtime import _endpoint_from_record

    record = make_record(0, started_at="2026-09-16T00:00:00Z", disequality_encoding="ee")
    endpoint = _endpoint_from_record(record)
    assert endpoint.disequality_encoding == "ee"
    assert endpoint.cache_identity != replace(endpoint, disequality_encoding="nee").cache_identity


def test_encoding_and_treatment_change_warns(tmp_path: Path) -> None:
    from benchmarking.reports.presentation import build_report_catalog
    from benchmarking.reports.render import render_markdown_report_document

    target = make_target()
    comparison = models.ComparisonSpec(
        models.BenchmarkEndpoint(target, "off", "nee"),
        models.BenchmarkEndpoint(target, "proofs", "ee"),
        (models.FileSpec("file.egg", tmp_path / "file.egg", "sha256:file"),),
        1,
        120,
    )
    markdown = render_markdown_report_document(build_report_catalog(ReportStore(tmp_path / "report.jsonl"), comparison))
    assert "disequality encoding and another endpoint setting" in markdown
