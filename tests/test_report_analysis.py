"""Test pure pair statistics, phase attribution, and ruleset comparisons."""

from __future__ import annotations

import math
from dataclasses import replace
from pathlib import Path
from typing import cast

import pytest

from benchmarking import models
from benchmarking.known_failures import KNOWN_FAILURES, known_failure_reason
from benchmarking.reports.analysis import analyze_pair
from benchmarking.reports.store import ReportRecord, ReportStore

from .report_fixtures import make_record, make_ruleset_timing, make_target, make_timing_summary, write_report


def _endpoint(
    label: str,
    binary_sha256: str,
    *,
    treatment: models.Treatment = "off",
) -> models.BenchmarkEndpoint:
    return models.BenchmarkEndpoint(
        make_target(target_label=label, binary_sha256=binary_sha256),
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
        make_record(
            1,
            started_at="2026-07-15T12:00:01Z",
            binary_sha256="sha256:candidate",
            timing_summary=make_timing_summary(make_ruleset_timing(search_ns=400_000_001)),
        ),
    )

    store = ReportStore(report).grouped_report()
    summary = analyze_pair(store, comparison, "summary")
    files = analyze_pair(store, comparison, "files")
    phases = analyze_pair(store, comparison, "phases")
    rulesets = analyze_pair(store, comparison, "rulesets")

    assert len(summary.summary) == 5
    assert not summary.files and not summary.timing
    assert files.files and not files.timing
    assert phases.files and phases.timing
    assert rulesets.files and rulesets.timing


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

    views = analyze_pair(ReportStore(report).grouped_report(), comparison, "files")

    wall = next(row for row in views.files if row.metric == "wall_sec")
    expected_half_width = t_critical * math.sqrt(0.01 / 3)
    expected_low, expected_high = _fieller_bounds(10.0, 0.01 / 3, 8.0, 0.01 / 3, t_critical)
    assert wall.baseline.point == pytest.approx(10.0)
    assert wall.baseline.ci_low == pytest.approx(10.0 - expected_half_width)
    assert wall.baseline.ci_high == pytest.approx(10.0 + expected_half_width)
    assert wall.ratio.estimate.point == pytest.approx(0.8)
    assert wall.ratio.estimate.ci_low == pytest.approx(expected_low)
    assert wall.ratio.estimate.ci_high == pytest.approx(expected_high)
    suite = views.summary[0]
    assert suite.summary_kind == "suite"
    assert suite.ratio.estimate.point == pytest.approx(0.8)


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

    summary = analyze_pair(ReportStore(report).grouped_report(), comparison, "summary").summary

    assert [(row.metric, row.summary_kind) for row in summary] == [
        ("wall_sec", "suite"),
        ("wall_sec", "lowest_file"),
        ("wall_sec", "highest_file"),
        ("max_rss_bytes", "lowest_file"),
        ("max_rss_bytes", "highest_file"),
    ]
    assert [row.file_order for row in summary] == [None, 0, 2, 0, 2]
    assert all(row.ratio.estimate.point == pytest.approx(2.0) for row in summary)


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

    summary = analyze_pair(ReportStore(report).grouped_report(), comparison, "summary").summary

    suite, *tails = summary
    assert suite.ratio.result_class == "invalid"
    assert suite.ratio.estimate.point is None
    assert suite.ratio.issue == "failure row selected"
    assert all(row.file_order == 0 for row in tails)
    assert all(row.ratio.estimate.point is not None for row in tails)


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

    suite, *tails = analyze_pair(ReportStore(report).grouped_report(), comparison, "summary").summary

    assert suite.ratio.issue == "failure row selected"
    assert all(row.file_order == 0 for row in tails)
    assert all(row.ratio.issue is None for row in tails)


def test_validation_failure_preserves_means_but_excludes_ratios_and_timing(tmp_path: Path) -> None:
    report = tmp_path / "report.jsonl"
    files = tuple(
        models.FileSpec(f"file-{index}.egg", tmp_path / f"file-{index}.egg", f"sha256:file-{index}")
        for index in range(2)
    )
    reason = "strict proof validation failed: invalid witness"
    comparison = replace(_comparison(tmp_path, files), suite_mode=True, validation_issues=((files[1], reason),))
    records = [
        make_record(
            endpoint_order * 2 + file_order,
            started_at=f"2026-07-15T12:00:0{endpoint_order * 2 + file_order}Z",
            binary_sha256=endpoint.target.binary_sha256,
            file_sha256=file.sha256,
            wall_sec=1.0 + endpoint_order,
            max_rss_bytes=100,
        )
        for endpoint_order, endpoint in enumerate((comparison.baseline, comparison.candidate))
        for file_order, file in enumerate(files)
    ]
    write_report(report, *records)

    views = analyze_pair(ReportStore(report).grouped_report(), comparison, "rulesets")

    assert all(row.summary_kind == "file" for row in views.summary)
    assert all(row.ratio.estimate.point is not None for row in views.summary if row.file_order == 0)
    assert all(row.ratio.estimate.point is None for row in views.summary if row.file_order == 1)
    assert all(row.ratio.issue == reason for row in views.summary if row.file_order == 1)
    invalid_wall = next(row for row in views.files if row.file_order == 1 and row.metric == "wall_sec")
    assert invalid_wall.baseline.point == 1.0
    assert invalid_wall.candidate.point == 2.0
    assert invalid_wall.ratio.estimate.point is None
    assert invalid_wall.ratio.issue == reason
    assert [row.file_order for row in views.timing] == [0, 1]
    assert views.timing[1].wall_delta_ns is None
    assert views.timing[1].issue == reason


@pytest.mark.parametrize("status,label", [("failure", "failure"), ("timed-out", "timeout")])
@pytest.mark.parametrize("failed_endpoint", ["baseline", "candidate"])
def test_terminal_observation_precedes_missing_rounds(
    tmp_path: Path, status: models.Status, label: str, failed_endpoint: str
) -> None:
    report = tmp_path / "report.jsonl"
    comparison = _comparison(tmp_path, rounds=30)
    failed = make_record(0, started_at="2026-07-15T12:00:00Z", binary_sha256=f"sha256:{failed_endpoint}", status=status)
    failed["error_message"] = "specific error\nfull diagnostic in cache"
    write_report(report, failed)
    store = ReportStore(report)

    ordinary = analyze_pair(store.grouped_report(), comparison, "files")
    suite = analyze_pair(store.grouped_report(), replace(comparison, suite_mode=True), "files")

    assert ordinary.summary[0].ratio.issue == f"{label} row selected (1/30 attempts): specific error"
    assert suite.summary[0].ratio.issue == f"{label} row selected (1/30 attempts): specific error"
    assert suite.summary[0].ratio.estimate.point is None
    assert suite.files[0].baseline.point is None


@pytest.mark.parametrize("cached", [False, True])
def test_known_failure_precedes_missing_rows_and_excludes_cached_ratios(tmp_path: Path, cached: bool) -> None:
    failure = KNOWN_FAILURES[0]
    file = models.FileSpec(failure.file, tmp_path / "parameter.egg", failure.file_sha256)
    comparison = _comparison(
        tmp_path, (file,), rounds=3, candidate=_endpoint("candidate", "sha256:candidate", treatment="proofs")
    )
    store = ReportStore(tmp_path / "report.jsonl")
    if cached:
        store.append(
            make_record(0, started_at="2026-07-15T12:00:00Z", file_sha256=file.sha256, binary_sha256="sha256:baseline")
        )
        store.append(
            make_record(
                1,
                started_at="2026-07-15T12:00:01Z",
                file_sha256=file.sha256,
                binary_sha256="sha256:candidate",
                treatment="proofs",
            )
        )

    views = analyze_pair(store.grouped_report(), comparison, "rulesets")

    reason = known_failure_reason(file, "proofs")
    assert reason is not None
    assert all(row.ratio.issue == reason for row in views.summary)
    assert all(row.ratio.issue == reason and row.ratio.estimate.point is None for row in views.files)
    assert all(row.issue == reason and row.wall_delta_ns is None for row in views.timing)
    assert len(store.records) == (2 if cached else 0)
    assert store.path.exists() == cached


def test_mechanism_buckets_are_additive_and_residual_closes_to_wall(tmp_path: Path) -> None:
    report = tmp_path / "report.jsonl"
    comparison = _comparison(tmp_path)
    baseline_timing = make_timing_summary(
        make_ruleset_timing(
            search_ns=100,
            apply_ns=200,
            execution_ns=17,
            merge_ns=300,
        ),
        native_rebuild_ns=400,
    )
    candidate_timing = make_timing_summary(
        make_ruleset_timing(
            search_ns=200,
            apply_ns=100,
            execution_ns=23,
            merge_ns=600,
        ),
        native_rebuild_ns=200,
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

    suite, file_row = analyze_pair(ReportStore(report).grouped_report(), comparison, "phases").timing

    assert suite.file_order is None
    assert file_row.file_order == 0
    assert file_row.wall_delta_ns == pytest.approx(500.0)
    assert file_row.mechanism_deltas == pytest.approx([0.0, 0.0, 306.0, -200.0, 0.0, 394.0])
    assert sum(delta or 0.0 for delta in file_row.mechanism_deltas) == pytest.approx(file_row.wall_delta_ns)
    assert suite.wall_delta_ns == file_row.wall_delta_ns
    assert suite.mechanism_deltas == file_row.mechanism_deltas


def test_process_rulesets_and_global_rebuild_are_each_subtracted_from_residual(tmp_path: Path) -> None:
    report = tmp_path / "report.jsonl"
    comparison = _comparison(tmp_path)
    timing = make_timing_summary(
        make_ruleset_timing(
            assembly_ns=31,
            search_ns=37,
            apply_ns=41,
            execution_ns=43,
            merge_ns=47,
        ),
        frontend_parse_ns=11,
        typecheck_ns=13,
        frontend_other_ns=17,
        frontend_install_ns=19,
        commands_actions_ns=23,
        commands_check_ns=7,
        commands_other_ns=29,
        native_rebuild_ns=53,
    )
    zero_timing = make_timing_summary(
        make_ruleset_timing(
            assembly_ns=0,
            search_ns=0,
            apply_ns=0,
            execution_ns=0,
            merge_ns=0,
        ),
        native_rebuild_ns=0,
    )
    write_report(
        report,
        make_record(
            0,
            started_at="2026-07-15T12:00:00Z",
            binary_sha256="sha256:baseline",
            wall_sec=0.000001,
            timing_summary=zero_timing,
        ),
        make_record(
            1,
            started_at="2026-07-15T12:00:01Z",
            binary_sha256="sha256:candidate",
            wall_sec=0.0000015,
            timing_summary=timing,
        ),
    )

    views = analyze_pair(ReportStore(report).grouped_report(), comparison, "rulesets")
    file_row = views.timing[1]

    assert file_row.wall_delta_ns == pytest.approx(500.0)
    assert file_row.mechanism_deltas == pytest.approx([13.0, 47.0, 199.0, 53.0, 59.0, 129.0])
    assert sum(delta or 0.0 for delta in file_row.mechanism_deltas) == pytest.approx(500.0)
    assert file_row.program.phases == pytest.approx((31, 37, 41, 43, 47, 0))
    assert file_row.equality.phases == pytest.approx((0, 0, 0, 0, 0, 53))
    assert file_row.equality.native_rebuild_delta_ns == 53


def test_mechanism_decomposition_uses_endpoint_means_and_wall_context(tmp_path: Path) -> None:
    report = tmp_path / "report.jsonl"
    comparison = _comparison(tmp_path, rounds=2)
    records: list[ReportRecord] = []
    for binary_sha256, searches, walls_ns in (
        ("sha256:baseline", (100, 300), (1_000, 1_200)),
        ("sha256:candidate", (200, 400), (1_500, 1_700)),
    ):
        for search_ns, wall_ns in zip(searches, walls_ns, strict=True):
            records.append(
                make_record(
                    len(records),
                    started_at=f"2026-07-15T12:00:{len(records):02d}Z",
                    binary_sha256=binary_sha256,
                    wall_sec=wall_ns / 1_000_000_000.0,
                    timing_summary=make_timing_summary(
                        make_ruleset_timing(search_ns=search_ns, apply_ns=0, merge_ns=0),
                        native_rebuild_ns=0,
                    ),
                )
            )
    write_report(report, *records)

    file_row = analyze_pair(ReportStore(report).grouped_report(), comparison, "phases").timing[1]

    assert file_row.wall_delta_ns == pytest.approx(500.0)
    assert file_row.program.phases.total == 100
    assert file_row.residual_delta_ns == 400


def test_ruleset_union_aligns_absence_with_zero_and_aggregates_iterations(tmp_path: Path) -> None:
    report = tmp_path / "report.jsonl"
    comparison = _comparison(tmp_path, rounds=2)
    zero = make_ruleset_timing(
        "recorded-zero",
        search_ns=0,
        apply_ns=0,
        execution_ns=0,
        merge_ns=0,
    )
    write_report(
        report,
        make_record(
            0,
            started_at="2026-07-15T12:00:00Z",
            binary_sha256="sha256:baseline",
            timing_summary=make_timing_summary(
                make_ruleset_timing("baseline-only", search_ns=10, apply_ns=0, merge_ns=0),
                make_ruleset_timing("sporadic", search_ns=8, apply_ns=0, merge_ns=0),
                zero,
                native_rebuild_ns=0,
            ),
        ),
        make_record(
            1,
            started_at="2026-07-15T12:00:01Z",
            binary_sha256="sha256:baseline",
            timing_summary=make_timing_summary(
                make_ruleset_timing("baseline-only", search_ns=10, apply_ns=0, merge_ns=0),
                zero,
                native_rebuild_ns=0,
            ),
        ),
        make_record(
            2,
            started_at="2026-07-15T12:00:02Z",
            binary_sha256="sha256:candidate",
            timing_summary=make_timing_summary(
                make_ruleset_timing("candidate-only", search_ns=20, apply_ns=0, merge_ns=0),
                make_ruleset_timing(
                    "assembly-only",
                    assembly_ns=5,
                    search_ns=0,
                    apply_ns=0,
                    merge_ns=0,
                ),
                zero,
                native_rebuild_ns=0,
            ),
        ),
        make_record(
            3,
            started_at="2026-07-15T12:00:03Z",
            binary_sha256="sha256:candidate",
            timing_summary=make_timing_summary(
                make_ruleset_timing("candidate-only", search_ns=20, apply_ns=0, merge_ns=0),
                make_ruleset_timing(
                    "assembly-only",
                    assembly_ns=5,
                    search_ns=0,
                    apply_ns=0,
                    merge_ns=0,
                ),
                zero,
                native_rebuild_ns=0,
            ),
        ),
    )

    views = analyze_pair(ReportStore(report).grouped_report(), comparison, "rulesets")
    file_row = views.timing[1]
    rows = {row.name: row for row in file_row.program.rulesets}

    assert rows["baseline-only"].phases.search == -10
    assert rows["candidate-only"].phases.search == 20
    assert rows["sporadic"].phases.search == -4
    assert rows["assembly-only"].phases.assembly == 5
    assert rows["assembly-only"].phases.total == 5
    assert "recorded-zero" not in rows
    assert len(file_row.program.rulesets) == 4
    assert file_row.program.phases.total == 11


def test_role_changes_are_separate_ruleset_changes_and_rebuild_is_global(tmp_path: Path) -> None:
    report = tmp_path / "report.jsonl"
    comparison = _comparison(tmp_path)
    baseline = make_timing_summary(
        make_ruleset_timing("rules/λ", search_ns=10, apply_ns=0, merge_ns=0),
        native_rebuild_ns=7,
    )
    candidate = make_timing_summary(
        make_ruleset_timing("rules/λ", role="equality", search_ns=12, apply_ns=0, merge_ns=0),
        native_rebuild_ns=3,
    )
    write_report(
        report,
        make_record(
            0,
            started_at="2026-07-15T12:00:00Z",
            binary_sha256="sha256:baseline",
            timing_summary=baseline,
        ),
        make_record(
            1,
            started_at="2026-07-15T12:00:01Z",
            binary_sha256="sha256:candidate",
            timing_summary=candidate,
        ),
    )

    file_row = analyze_pair(ReportStore(report).grouped_report(), comparison, "rulesets").timing[1]
    assert file_row.program.rulesets[0].phases.search == -10
    assert file_row.equality.rulesets[0].phases.search == 12
    assert file_row.equality.native_rebuild_delta_ns == -4
    assert file_row.program.rulesets[0].phases.rebuild == 0
    assert file_row.equality.rulesets[0].phases.rebuild == 0


def test_ruleset_parent_groups_equal_program_and_equality_mechanisms(tmp_path: Path) -> None:
    report = tmp_path / "report.jsonl"
    comparison = _comparison(tmp_path)
    candidate = make_timing_summary(
        make_ruleset_timing(
            "source",
            assembly_ns=2,
            search_ns=3,
            apply_ns=5,
            execution_ns=7,
            merge_ns=11,
        ),
        make_ruleset_timing(
            "maintenance",
            assembly_ns=17,
            search_ns=19,
            apply_ns=23,
            execution_ns=29,
            merge_ns=31,
            role="equality",
        ),
        native_rebuild_ns=50,
    )
    write_report(
        report,
        make_record(
            0,
            started_at="2026-07-15T12:00:00Z",
            binary_sha256="sha256:baseline",
            timing_summary=make_timing_summary(
                make_ruleset_timing(search_ns=0, apply_ns=0, merge_ns=0),
                native_rebuild_ns=0,
            ),
        ),
        make_record(
            1,
            started_at="2026-07-15T12:00:01Z",
            binary_sha256="sha256:candidate",
            timing_summary=candidate,
        ),
    )

    views = analyze_pair(ReportStore(report).grouped_report(), comparison, "rulesets")
    file_row = views.timing[1]
    maintenance = file_row.equality.rulesets[0]
    assert file_row.program.phases.total == file_row.mechanism_deltas[2] == 28
    assert maintenance.phases.total == 119
    assert file_row.equality.native_rebuild_delta_ns == 50
    assert file_row.equality.phases.total == file_row.mechanism_deltas[3] == 169
    assert maintenance.phases.total + file_row.equality.native_rebuild_delta_ns == file_row.equality.phases.total


def test_all_maintenance_children_are_shown_and_zero_native_rebuild_is_hidden(tmp_path: Path) -> None:
    report = tmp_path / "report.jsonl"
    comparison = _comparison(tmp_path)
    names = tuple(f"maintenance-{index}" for index in range(7))
    source = make_ruleset_timing(
        "source",
        assembly_ns=0,
        search_ns=0,
        apply_ns=0,
        execution_ns=0,
        merge_ns=0,
    )
    baseline_maintenance = tuple(
        make_ruleset_timing(
            name,
            assembly_ns=0,
            search_ns=0,
            apply_ns=0,
            execution_ns=0,
            merge_ns=0,
            role="equality",
        )
        for name in names
    )
    candidate_maintenance = tuple(
        make_ruleset_timing(
            name,
            assembly_ns=0,
            search_ns=index + 1,
            apply_ns=0,
            execution_ns=0,
            merge_ns=0,
            role="equality",
        )
        for index, name in enumerate(names)
    )
    write_report(
        report,
        make_record(
            0,
            started_at="2026-07-15T12:00:00Z",
            binary_sha256="sha256:baseline",
            timing_summary=make_timing_summary(source, *baseline_maintenance),
            wall_sec=0.000001,
        ),
        make_record(
            1,
            started_at="2026-07-15T12:00:01Z",
            binary_sha256="sha256:candidate",
            timing_summary=make_timing_summary(source, *candidate_maintenance),
            wall_sec=0.000001,
        ),
    )

    file_row = analyze_pair(ReportStore(report).grouped_report(), comparison, "rulesets").timing[1]
    assert len(file_row.equality.rulesets) == 7
    assert [row.name for row in file_row.equality.rulesets] == list(names)
    assert file_row.equality.phases.total == sum(range(1, 8))
    assert file_row.equality.native_rebuild_delta_ns == 0


def test_negative_residual_is_preserved_as_an_attribution_warning(tmp_path: Path) -> None:
    report = tmp_path / "report.jsonl"
    comparison = _comparison(tmp_path)
    timing = make_timing_summary(
        make_ruleset_timing(search_ns=10, apply_ns=0, merge_ns=0),
        native_rebuild_ns=0,
    )
    write_report(
        report,
        make_record(
            0,
            started_at="2026-07-15T12:00:00Z",
            binary_sha256="sha256:baseline",
            wall_sec=5 / 1_000_000_000,
            timing_summary=timing,
        ),
        make_record(
            1,
            started_at="2026-07-15T12:00:01Z",
            binary_sha256="sha256:candidate",
            wall_sec=6 / 1_000_000_000,
            timing_summary=timing,
        ),
    )

    file_row = analyze_pair(ReportStore(report).grouped_report(), comparison, "phases").timing[1]
    assert file_row.residual_warning
    assert file_row.residual_delta_ns == pytest.approx(1)


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


def test_ten_run_sample_and_fieller_use_df_nine(tmp_path: Path) -> None:
    report = tmp_path / "report.jsonl"
    comparison = _comparison(tmp_path, rounds=10)
    records: list[ReportRecord] = []
    for binary, mean in (("sha256:baseline", 10), ("sha256:candidate", 20)):
        for index in range(30):
            records.append(
                make_record(
                    len(records),
                    started_at="2026-01-01T00:00:00Z",
                    binary_sha256=binary,
                    wall_sec=100 if index < 20 else mean + (index - 24.5) / 10,
                )
            )
    write_report(report, *records)
    wall = next(
        row
        for row in analyze_pair(ReportStore(report).grouped_report(), comparison, "files").files
        if row.metric == "wall_sec"
    )
    var_mean = 0.09166666666666666 / 10
    critical = 2.2621571627409915  # Student-t 0.975 quantile, 9 degrees of freedom.
    low, high = _fieller_bounds(10, var_mean, 20, var_mean, critical)
    assert wall.baseline.point == pytest.approx(10)
    assert wall.baseline.ci_low == pytest.approx(10 - critical * math.sqrt(var_mean))
    assert wall.ratio.estimate.ci_low == pytest.approx(low)
    assert wall.ratio.estimate.ci_high == pytest.approx(high)


def test_suite_report_preserves_failure_outside_reduced_sample(tmp_path: Path) -> None:
    report = tmp_path / "report.jsonl"
    comparison = replace(_comparison(tmp_path, rounds=10), suite_mode=True)
    records = [make_record(0, started_at="2026-01-01T00:00:00Z", binary_sha256="sha256:candidate", status="timed-out")]
    for binary in ("sha256:baseline", "sha256:candidate"):
        for _index in range(10):
            records.append(make_record(len(records), started_at="2026-01-01T00:00:00Z", binary_sha256=binary))
    write_report(report, *records)
    wall = next(
        row
        for row in analyze_pair(ReportStore(report).grouped_report(), comparison, "files").files
        if row.metric == "wall_sec"
    )
    assert wall.ratio.result_class == "invalid"
    assert "timeout row selected (11/10 attempts)" in (wall.ratio.issue or "")
