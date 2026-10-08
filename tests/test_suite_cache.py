"""Suite statistics use all exact identities while positional reports retain their tail."""

from __future__ import annotations

import math
import statistics
from dataclasses import replace
from pathlib import Path

import pytest
from scipy.stats import t

from benchmarking import collection, models
from benchmarking.reports.analysis import analyze_pair
from benchmarking.reports.store import CacheKey, ReportStore

from .report_fixtures import make_record, make_target


def test_all_samples_and_unequal_counts_control_means_and_fieller(tmp_path: Path) -> None:
    store = ReportStore(tmp_path / "rows.jsonl")
    target = make_target()
    file = models.FileSpec("case", tmp_path / "case", "sha256:file")
    samples = {"off": [1.0, 1.01, 1.02, 1.03], "proofs": [2.0, 2.04, 2.08]}
    for treatment, values in samples.items():
        for i, value in enumerate(values):
            store.append(make_record(i, started_at=f"2026-01-01T00:00:{i:02}Z", treatment=treatment, wall_sec=value))  # type: ignore[arg-type]
    # These other coordinates must never contribute.
    for extra in (
        {"disequality_encoding": "ee"},
        {"timeout_sec": 300},
        {"binary_sha256": "other"},
        {"fact_directory_sha256": "facts"},
        {"file_sha256": "other"},
    ):
        store.append(make_record(99, started_at="2026-02-01T00:00:00Z", wall_sec=1000.0, **extra))
    comparison = models.ComparisonSpec(
        models.BenchmarkEndpoint(target, "off"),
        models.BenchmarkEndpoint(target, "proofs"),
        (file,),
        2,
        120,
        suite_mode=True,
    )
    row = analyze_pair(store.grouped_report(), comparison, "files").files[0]
    bm, cm = map(statistics.mean, samples.values())
    bv, cv = [statistics.variance(values) / len(values) for values in samples.values()]
    assert row.baseline.point == bm and row.candidate.point == cm
    assert row.baseline.ci_low == pytest.approx(bm - t.ppf(0.975, 3) * math.sqrt(bv))
    assert row.candidate.ci_high == pytest.approx(cm + t.ppf(0.975, 2) * math.sqrt(cv))
    critical = t.ppf(0.975, 2) ** 2
    a = bm * bm - critical * bv
    d = cm * cm - critical * cv
    spread = math.sqrt((bm * cm) ** 2 - a * d) / a
    assert row.ratio.estimate.ci_low == pytest.approx(bm * cm / a - spread)
    ordinary = analyze_pair(store.grouped_report(), replace(comparison, suite_mode=False), "files").files[0]
    assert ordinary.baseline.point == pytest.approx(1.025)
    assert ordinary.candidate.point == pytest.approx(2.06)


def test_one_sample_has_point_only_and_old_failure_cannot_be_hidden_by_thirty_successes(tmp_path: Path) -> None:
    store = ReportStore(tmp_path / "rows.jsonl")
    target = make_target()
    file = models.FileSpec("case", tmp_path / "case", "sha256:file")
    store.append(make_record(0, started_at="2026-01-01T00:00:00Z", status="failure"))
    for i in range(40):
        store.append(make_record(i, started_at=f"2026-02-01T00:00:{i:02}Z"))
    store.append(make_record(100, started_at="2026-03-01T00:00:00Z", treatment="proofs", wall_sec=2))
    comparison = models.ComparisonSpec(
        models.BenchmarkEndpoint(target, "off"),
        models.BenchmarkEndpoint(target, "proofs"),
        (file,),
        10,
        120,
        suite_mode=True,
    )
    result = analyze_pair(store.grouped_report(), comparison, "files").files[0]
    assert result.ratio.result_class == "invalid" and "failure" in str(result.ratio.issue)
    assert result.candidate.point == 2 and result.candidate.ci_low is None
    key = CacheKey.for_endpoint(comparison.baseline, file, 120)
    assert len(store.latest_records(key)) == 41
    assert (
        collection.build_collection_plan(
            store, target, (comparison.baseline,), (file,), 50, 120, False, True
        ).total_missing_observations
        == 0
    )


def test_strict_failure_suppresses_conclusion_without_screening_collection(tmp_path: Path) -> None:
    store = ReportStore(tmp_path / "rows.jsonl")
    target = make_target()
    file = models.FileSpec("case", tmp_path / "case", "sha256:file")
    endpoints = (models.BenchmarkEndpoint(target, "off"), models.BenchmarkEndpoint(target, "proofs"))
    assert (
        collection.build_collection_plan(
            store, target, endpoints, (file,), 2, 120, False, True
        ).total_missing_observations
        == 4
    )
    for treatment in ("off", "proofs"):
        store.append(make_record(0, started_at="2026-01-01T00:00:00Z", treatment=treatment))
    comparison = models.ComparisonSpec(
        *endpoints, (file,), 2, 120, suite_mode=True, validation_issues=((file, "exact strict failure"),)
    )
    result = analyze_pair(store.grouped_report(), comparison, "files").files[0]
    assert result.ratio.issue == "exact strict failure" and result.ratio.result_class == "invalid"


def test_fixed_math_suite_plans_all_four_endpoints_and_reuses_off_observations(tmp_path: Path) -> None:
    from benchmarking import benchmark, math_workloads, suites

    from .corpus_fixtures import prepare_corpus

    prepare_corpus(
        tmp_path,
        family="math-growth",
        contents=((math_workloads.ROOT / math_workloads.MATH_WORKLOAD_PATH).read_text(),),
    )
    suite = suites.resolve_suite("math-11", tmp_path)
    assert len(suite.files) == 1 and suite.files[0].sha256 == "sha256:" + math_workloads.LEGACY_SHA256
    assert suites.resolve_suite("expanded", tmp_path).files == suite.files
    target = replace(
        make_target(),
        engine_binaries=(
            models.EngineBinary("egg", "sha256:egg", None),
            models.EngineBinary("egglog", "sha256:bin", None),
        ),
    )
    store = ReportStore(tmp_path / "rows.jsonl")
    for i in range(12):
        store.append(
            make_record(i, started_at="2026-01-01T00:00:00Z", timeout_sec=300, file_sha256=suite.files[0].sha256)
        )
    baseline = models.BenchmarkEndpoint(target, "off")
    for treatment in ("proof-extraction", "egg", "egg-proof-extraction"):
        candidate = models.BenchmarkEndpoint(target, treatment)
        comparison = models.ComparisonSpec(baseline, candidate, suite.files, 10, 300, suite_mode=True)
        (plan,) = benchmark.collection_plans(store, comparison, False)
        off, proof = plan.runs
        assert off.missing_observations == 0
        assert len(off.cached_statuses) == 12
        assert proof.missing_observations == 10 and proof.treatment == treatment
