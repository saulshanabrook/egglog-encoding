"""Test pure pair statistics, phase attribution, and ruleset comparisons."""

from __future__ import annotations

import math
from pathlib import Path
from typing import cast

import pytest

from benchmarking import models
from benchmarking.reports.analysis import analyze_pair
from benchmarking.reports.records import ReportRecord
from benchmarking.reports.store import ReportStore

from .conftest import make_record, make_ruleset_timing, make_target, make_timing_summary, write_report


def _endpoint(
    label: str,
    binary_sha256: str,
    *,
    backend: models.Backend = "main",
    treatment: models.Treatment = "off",
) -> models.BenchmarkEndpoint:
    return models.BenchmarkEndpoint(
        make_target(target_label=label, binary_sha256=binary_sha256),
        backend,
        treatment,
    )


def _comparison(
    tmp_path: Path,
    files: tuple[models.FileSpec, ...] | None = None,
    *,
    rounds: int = 1,
    timeout_sec: int = 120,
    baseline: models.BenchmarkEndpoint | None = None,
    candidate: models.BenchmarkEndpoint | None = None,
) -> models.ComparisonSpec:
    if files is None:
        files = (models.FileSpec("file.egg", tmp_path / "file.egg", "sha256:file"),)
    return models.ComparisonSpec(
        baseline or _endpoint("baseline", "sha256:baseline"),
        candidate or _endpoint("candidate", "sha256:candidate"),
        files,
        rounds,
        timeout_sec,
    )


def test_analysis_computes_only_the_requested_detail_rows(tmp_path: Path) -> None:
    report = tmp_path / "report.jsonl"
    comparison = _comparison(tmp_path)
    write_report(
        report,
        make_record(0, started_at="2026-07-15T12:00:00Z", binary_sha256="sha256:baseline"),
        make_record(1, started_at="2026-07-15T12:00:01Z", binary_sha256="sha256:candidate"),
    )

    store = ReportStore(report)
    summary = analyze_pair(store, comparison, "summary")
    files = analyze_pair(store, comparison, "files")
    phases = analyze_pair(store, comparison, "phases")
    rulesets = analyze_pair(store, comparison, "rulesets")

    assert len(summary.summary) == 5
    assert not summary.files and not summary.phases and not summary.rulesets
    assert files.files and not files.phases and not files.rulesets
    assert phases.files and phases.phases and not phases.rulesets
    assert rulesets.files and rulesets.phases and rulesets.rulesets


def test_pair_statistics_and_fieller_intervals(tmp_path: Path) -> None:
    report = tmp_path / "report.jsonl"
    comparison = _comparison(tmp_path, rounds=3)
    t_critical = 4.302652729911275
    records: list[ReportRecord] = []
    for binary_sha256, values in (
        ("sha256:baseline", (9.9, 10.0, 10.1)),
        ("sha256:candidate", (7.9, 8.0, 8.1)),
    ):
        for wall_sec in values:
            records.append(
                make_record(
                    len(records),
                    started_at=f"2026-07-15T12:00:{len(records):02d}Z",
                    binary_sha256=binary_sha256,
                    wall_sec=wall_sec,
                    max_rss_bytes=100,
                )
            )
    write_report(report, *records)

    views = analyze_pair(ReportStore(report), comparison, "files")

    wall = next(row for row in views.files if row.metric == "wall_sec")
    expected_half_width = t_critical * math.sqrt(0.01 / 3)
    expected_low, expected_high = _fieller_bounds(10.0, 0.01 / 3, 8.0, 0.01 / 3, t_critical)
    assert wall.baseline_mean == pytest.approx(10.0)
    assert wall.baseline_ci_low == pytest.approx(10.0 - expected_half_width)
    assert wall.baseline_ci_high == pytest.approx(10.0 + expected_half_width)
    assert wall.point == pytest.approx(0.8)
    assert wall.ci_low == pytest.approx(expected_low)
    assert wall.ci_high == pytest.approx(expected_high)
    suite = views.summary[0]
    assert suite.summary_kind == "suite"
    assert suite.point == pytest.approx(0.8)


def test_summary_has_wall_suite_and_metric_tails_with_stable_ties(tmp_path: Path) -> None:
    report = tmp_path / "report.jsonl"
    files = tuple(
        models.FileSpec(f"file-{index}.egg", tmp_path / f"file-{index}.egg", f"sha256:file-{index}")
        for index in range(3)
    )
    comparison = _comparison(tmp_path, files)
    records: list[ReportRecord] = []
    for file in files:
        records.extend(
            (
                make_record(
                    len(records),
                    started_at=f"2026-07-15T12:00:{len(records):02d}Z",
                    binary_sha256="sha256:baseline",
                    file_sha256=file.sha256,
                    wall_sec=1.0,
                    max_rss_bytes=100,
                ),
                make_record(
                    len(records) + 1,
                    started_at=f"2026-07-15T12:00:{len(records) + 1:02d}Z",
                    binary_sha256="sha256:candidate",
                    file_sha256=file.sha256,
                    wall_sec=2.0,
                    max_rss_bytes=200,
                ),
            )
        )
    write_report(report, *records)

    summary = analyze_pair(ReportStore(report), comparison, "summary").summary

    assert [(row.metric, row.summary_kind) for row in summary] == [
        ("wall_sec", "suite"),
        ("wall_sec", "lowest_file"),
        ("wall_sec", "highest_file"),
        ("max_rss_bytes", "lowest_file"),
        ("max_rss_bytes", "highest_file"),
    ]
    assert [row.file_order for row in summary] == [None, 0, 2, 0, 2]
    assert all(row.point == pytest.approx(2.0) for row in summary)


def test_invalid_file_breaks_suite_but_not_valid_file_tails(tmp_path: Path) -> None:
    report = tmp_path / "report.jsonl"
    files = (
        models.FileSpec("valid.egg", tmp_path / "valid.egg", "sha256:valid-file"),
        models.FileSpec("invalid.egg", tmp_path / "invalid.egg", "sha256:invalid-file"),
    )
    comparison = _comparison(tmp_path, files)
    write_report(
        report,
        make_record(
            0,
            started_at="2026-07-15T12:00:00Z",
            binary_sha256="sha256:baseline",
            file_sha256=files[0].sha256,
            wall_sec=1.0,
            max_rss_bytes=100,
        ),
        make_record(
            1,
            started_at="2026-07-15T12:00:01Z",
            binary_sha256="sha256:candidate",
            file_sha256=files[0].sha256,
            wall_sec=0.5,
            max_rss_bytes=80,
        ),
        make_record(
            2,
            started_at="2026-07-15T12:00:02Z",
            binary_sha256="sha256:baseline",
            file_sha256=files[1].sha256,
            wall_sec=1.0,
            max_rss_bytes=100,
        ),
        make_record(
            3,
            started_at="2026-07-15T12:00:03Z",
            binary_sha256="sha256:candidate",
            file_sha256=files[1].sha256,
            status="failure",
        ),
    )

    summary = analyze_pair(ReportStore(report), comparison, "summary").summary

    suite, *tails = summary
    assert suite.result_class == "invalid"
    assert suite.point is None
    assert suite.issue == "failure row selected"
    assert all(row.file_order == 0 for row in tails)
    assert all(row.point is not None for row in tails)


def test_valid_tail_does_not_inherit_an_unrelated_invalid_file_issue(tmp_path: Path) -> None:
    report = tmp_path / "report.jsonl"
    files = (
        models.FileSpec("valid.egg", tmp_path / "valid.egg", "sha256:valid-file"),
        models.FileSpec("invalid.egg", tmp_path / "invalid.egg", "sha256:invalid-file"),
    )
    comparison = _comparison(tmp_path, files, rounds=2)
    records: list[ReportRecord] = []
    for binary_sha256, wall_sec, max_rss_bytes in (
        ("sha256:baseline", 1.0, 100),
        ("sha256:candidate", 0.5, 80),
    ):
        for _ in range(2):
            records.append(
                make_record(
                    len(records),
                    started_at=f"2026-07-15T12:00:{len(records):02d}Z",
                    binary_sha256=binary_sha256,
                    file_sha256=files[0].sha256,
                    wall_sec=wall_sec,
                    max_rss_bytes=max_rss_bytes,
                )
            )
    for binary_sha256, status in (
        ("sha256:baseline", "success"),
        ("sha256:candidate", "failure"),
    ):
        for _ in range(2):
            records.append(
                make_record(
                    len(records),
                    started_at=f"2026-07-15T12:00:{len(records):02d}Z",
                    binary_sha256=binary_sha256,
                    file_sha256=files[1].sha256,
                    status=cast(models.Status, status),
                    wall_sec=1.0,
                    max_rss_bytes=100,
                )
            )
    write_report(report, *records)

    suite, *tails = analyze_pair(ReportStore(report), comparison, "summary").summary

    assert suite.issue == "failure row selected"
    assert all(row.file_order == 0 for row in tails)
    assert all(row.issue is None for row in tails)


def test_phase_rows_are_exact_components_and_other_is_wall_residual(tmp_path: Path) -> None:
    report = tmp_path / "report.jsonl"
    comparison = _comparison(tmp_path)
    baseline_timing = make_timing_summary(
        make_ruleset_timing(
            search_ns=100,
            apply_ns=200,
            unattributed_ns=17,
            merge_ns=300,
            rebuild_ns=400,
        )
    )
    candidate_timing = make_timing_summary(
        make_ruleset_timing(
            search_ns=200,
            apply_ns=100,
            unattributed_ns=23,
            merge_ns=600,
            rebuild_ns=200,
        )
    )
    write_report(
        report,
        make_record(
            0,
            started_at="2026-07-15T12:00:00Z",
            binary_sha256="sha256:baseline",
            wall_sec=0.0000015,
            timing_summary=baseline_timing,
        ),
        make_record(
            1,
            started_at="2026-07-15T12:00:01Z",
            binary_sha256="sha256:candidate",
            wall_sec=0.000002,
            timing_summary=candidate_timing,
        ),
    )

    phases = analyze_pair(ReportStore(report), comparison, "phases").phases

    assert [row.phase for row in phases] == ["search", "apply", "merge", "rebuild", "other"]
    assert [(row.baseline_ns, row.candidate_ns) for row in phases] == [
        (100.0, 200.0),
        (200.0, 100.0),
        (300.0, 600.0),
        (400.0, 200.0),
        (500.0, 900.0),
    ]
    assert [row.delta_ns for row in phases] == [100.0, -100.0, 300.0, -200.0, 400.0]


def test_ruleset_union_distinguishes_absence_from_zero_and_aggregates_iterations(tmp_path: Path) -> None:
    report = tmp_path / "report.jsonl"
    comparison = _comparison(tmp_path, rounds=2)
    zero = make_ruleset_timing(
        "recorded-zero",
        search_ns=0,
        apply_ns=0,
        unattributed_ns=0,
        merge_ns=0,
        rebuild_ns=0,
    )
    write_report(
        report,
        make_record(
            0,
            started_at="2026-07-15T12:00:00Z",
            binary_sha256="sha256:baseline",
            timing_summary=make_timing_summary(
                make_ruleset_timing("baseline-only", search_ns=10, apply_ns=0, merge_ns=0, rebuild_ns=0),
                make_ruleset_timing("sporadic", search_ns=8, apply_ns=0, merge_ns=0, rebuild_ns=0),
                zero,
            ),
        ),
        make_record(
            1,
            started_at="2026-07-15T12:00:01Z",
            binary_sha256="sha256:baseline",
            timing_summary=make_timing_summary(
                make_ruleset_timing("baseline-only", search_ns=10, apply_ns=0, merge_ns=0, rebuild_ns=0),
                zero,
            ),
        ),
        make_record(
            2,
            started_at="2026-07-15T12:00:02Z",
            binary_sha256="sha256:candidate",
            timing_summary=make_timing_summary(
                make_ruleset_timing("candidate-only", search_ns=20, apply_ns=0, merge_ns=0, rebuild_ns=0),
                zero,
            ),
        ),
        make_record(
            3,
            started_at="2026-07-15T12:00:03Z",
            binary_sha256="sha256:candidate",
            timing_summary=make_timing_summary(
                make_ruleset_timing("candidate-only", search_ns=20, apply_ns=0, merge_ns=0, rebuild_ns=0),
                zero,
            ),
        ),
    )

    rows = {row.name: row for row in analyze_pair(ReportStore(report), comparison, "rulesets").rulesets}

    assert rows["baseline-only"].baseline_total_ns == 10
    assert rows["baseline-only"].candidate_total_ns is None
    assert rows["baseline-only"].point is None
    assert rows["candidate-only"].baseline_total_ns is None
    assert rows["candidate-only"].candidate_total_ns == 20
    assert rows["candidate-only"].point is None
    assert rows["sporadic"].baseline_total_ns == 4
    assert rows["recorded-zero"].baseline_total_ns == 0
    assert rows["recorded-zero"].candidate_total_ns == 0
    assert rows["recorded-zero"].point is None


def test_ruleset_presentation_is_fixed_top_ten_by_absolute_delta_then_name(tmp_path: Path) -> None:
    report = tmp_path / "report.jsonl"
    comparison = _comparison(tmp_path)
    names = tuple(reversed(tuple(f"rules-{index:02d}" for index in range(12))))
    baseline_rules = tuple(
        make_ruleset_timing(name, search_ns=100, apply_ns=0, merge_ns=0, rebuild_ns=0) for name in names
    )
    candidate_rules = tuple(
        make_ruleset_timing(name, search_ns=101, apply_ns=0, merge_ns=0, rebuild_ns=0) for name in names
    )
    write_report(
        report,
        make_record(
            0,
            started_at="2026-07-15T12:00:00Z",
            binary_sha256="sha256:baseline",
            timing_summary=make_timing_summary(*baseline_rules),
        ),
        make_record(
            1,
            started_at="2026-07-15T12:00:01Z",
            binary_sha256="sha256:candidate",
            timing_summary=make_timing_summary(*candidate_rules),
        ),
    )

    rulesets = analyze_pair(ReportStore(report), comparison, "rulesets").rulesets

    assert len(rulesets) == 10
    assert [row.name for row in rulesets] == [f"rules-{index:02d}" for index in range(10)]
    assert {row.ruleset_count for row in rulesets} == {12}


def _fieller_bounds(
    baseline_mean: float,
    baseline_var_mean: float,
    candidate_mean: float,
    candidate_var_mean: float,
    t_critical: float,
) -> tuple[float, float]:
    a = baseline_mean**2 - t_critical**2 * baseline_var_mean
    d = candidate_mean**2 - t_critical**2 * candidate_var_mean
    radicand = (baseline_mean * candidate_mean) ** 2 - a * d
    center = baseline_mean * candidate_mean / a
    half_width = math.sqrt(radicand) / a
    return (center - half_width, center + half_width)
