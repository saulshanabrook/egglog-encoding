"""Check encoding-aware benchmark selection, subprocess commands, and cache identities."""

from dataclasses import replace
from pathlib import Path

import pytest

from benchmarking import benchmark, collection, models, targets
from benchmarking.engines import MATH_WORKLOAD_PATH
from benchmarking.reports.store import CacheKey, ReportStore

from .report_fixtures import make_record, make_target


def test_ee_requests_do_not_reuse_historical_nee_results(tmp_path: Path) -> None:
    args = benchmark.parse_benchmark_args([])
    before, after = benchmark.endpoint_requests(args)
    assert (before.disequality_encoding, after.disequality_encoding) == ("ee", "ee")
    target = make_target()
    baseline = models.BenchmarkEndpoint(target.row, target.binary_sha256_for("off"), "off", "nee")
    candidate = models.BenchmarkEndpoint(target.row, target.binary_sha256_for("off"), "off", "ee")
    file = models.FileSpec("test.egg", tmp_path / "test.egg", "sha256:file")
    assert CacheKey.for_endpoint(baseline, file) != CacheKey.for_endpoint(candidate, file)
    store = ReportStore(tmp_path / "results.jsonl")
    store.append(make_record(0, started_at="2026-09-16T00:00:00Z", disequality_encoding="nee"))
    request = collection.BenchmarkRequest(before, (file,))
    (plan,) = collection.plan_collection(store, (request,), {before.target: target}, 1, 120, False)
    assert [(run.disequality_encoding, run.missing_observations) for run in plan.runs] == [("ee", 1)]


@pytest.mark.parametrize("flag", ["--disequality-encoding", "--compare-disequality-encoding"])
@pytest.mark.parametrize("encoding", ["nee", "ee"])
def test_benchmark_has_no_disequality_encoding_selector(flag: str, encoding: str) -> None:
    with pytest.raises(SystemExit):
        benchmark.parse_benchmark_args([flag, encoding])


def test_ee_launches_remain_explicit_for_older_source_targets(tmp_path: Path) -> None:
    file = models.FileSpec("test.egg", tmp_path / "test.egg", "sha256:file")
    # Command construction does not need to read or classify the workload.
    command = targets.workload_command(Path("binary"), file, "proofs")
    assert command[command.index("--disequality-encoding") + 1] == "ee"
    assert "--proofs" in command
    with pytest.raises(ValueError, match="only the ee disequality encoding is supported"):
        models.EndpointRequest(make_target().request, "off", "nee")
    with pytest.raises(ValueError, match="only the ee disequality encoding is supported"):
        targets.workload_command(Path("binary"), file, "off", "nee")
    native_file = replace(file, absolute_path=Path(__file__).resolve().parents[2] / MATH_WORKLOAD_PATH)
    assert targets.workload_command(Path("binary"), native_file, "egg") == ["binary", "--proof-mode", "off"]


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
        models.BenchmarkEndpoint(target.row, target.binary_sha256_for("off"), "off", "nee"),
        models.BenchmarkEndpoint(target.row, target.binary_sha256_for("proofs"), "proofs", "ee"),
        (models.FileSpec("file.egg", tmp_path / "file.egg", "sha256:file"),),
        1,
        120,
    )
    markdown = render_markdown_report_document(
        build_report_catalog(ReportStore(tmp_path / "report.jsonl").grouped_report(), comparison)
    )
    assert "disequality encoding and another endpoint setting" in markdown
