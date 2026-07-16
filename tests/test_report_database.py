"""Test trusted direct-JSONL persistence, bulk selection, and DuckDB analysis."""

from __future__ import annotations

import json
import math
from pathlib import Path
from typing import cast

import pytest

from benchmarking import models
from benchmarking.reports.database import ReportDatabase, SqlReportScope
from benchmarking.reports.records import (
    ReportRecord,
    RulesetTimingRecord,
    TimingSummaryRecord,
)
from benchmarking.reports.results import ComparisonRequest

from .conftest import make_record, make_ruleset_timing, make_target, make_timing_summary, write_report

PRESENTATION_RELATIONS = (
    "presentation_targets",
    "presentation_files",
    "presentation_cells",
    "presentation_cell_estimates",
    "presentation_file_ratios",
    "presentation_comparison_rollups",
    "presentation_compact_timings",
    "presentation_ruleset_timings",
)


def test_missing_report_is_an_empty_direct_view_without_database_artifacts(tmp_path: Path) -> None:
    report = tmp_path / "nested" / "report.jsonl"

    with ReportDatabase(report) as database:
        assert database.successful_estimate_aggregates() == ()

    assert report.read_text(encoding="utf-8") == ""
    assert list(report.parent.iterdir()) == [report]


def test_append_is_immediately_queryable(tmp_path: Path) -> None:
    report = tmp_path / "report.jsonl"
    record = make_record(0, started_at="2026-07-15T12:00:00Z", target_label="current")

    with ReportDatabase(report) as database:
        database.append(record)
        pointer = database.find_label_pointer("current")

    assert pointer is not None
    assert pointer.binary_sha256 == record["binary_sha256"]
    raw = json.loads(report.read_text(encoding="utf-8"))
    assert raw == record
    assert "row_index" not in raw


def test_report_path_metacharacters_are_literal_not_a_glob(tmp_path: Path) -> None:
    report = tmp_path / "a'quoted[?*].jsonl"
    sibling = tmp_path / "a?.jsonl"
    write_report(report, make_record(0, started_at="2026-07-15T12:00:00Z"))
    write_report(
        sibling,
        make_record(
            1,
            started_at="2026-07-15T12:00:01Z",
            binary_sha256="sha256:sibling",
        ),
    )

    with ReportDatabase(report) as database:
        aggregates = database.successful_estimate_aggregates()

    assert [aggregate.key.binary_sha256 for aggregate in aggregates] == ["sha256:bin"]


def test_historical_estimates_are_grouped_as_counts_and_sums_in_sql(tmp_path: Path) -> None:
    report = tmp_path / "report.jsonl"
    write_report(
        report,
        make_record(0, started_at="2026-07-15T12:00:00Z", wall_sec=1.5),
        make_record(1, started_at="2026-07-15T12:00:01Z", wall_sec=2.5),
        make_record(2, started_at="2026-07-15T12:00:02Z", status="failure", wall_sec=100.0),
        make_record(3, started_at="2026-07-15T12:00:03Z", status="timed-out"),
        make_record(4, started_at="2026-07-15T12:00:04Z", timeout_sec=60, wall_sec=7.0),
    )

    with ReportDatabase(report) as database:
        aggregates = database.successful_estimate_aggregates()

    assert [
        (aggregate.key.timeout_sec, aggregate.sample_count, aggregate.total_wall_sec) for aggregate in aggregates
    ] == [(60, 1, 7.0), (120, 2, 4.0)]


def test_output_views_and_source_path_are_visible_to_another_connection(tmp_path: Path) -> None:
    report = tmp_path / "report.jsonl"
    write_report(report, make_record(0, started_at="2026-07-15T12:00:00Z"))
    target = make_target(target_label="current")
    file_spec = models.FileSpec("file.egg", tmp_path / "file.egg", "sha256:file")
    spec = models.BenchmarkSpec((file_spec,), ("off",), rounds=1, timeout_sec=120)

    with ReportDatabase(report) as database:
        database.install_scope((target,), spec, t_critical_95=None, requests=())
        database.report_view_data(include_timing=True)
        other_connection = database._connection.cursor()
        try:
            views = dict(
                other_connection.execute(
                    """
                    SELECT view_name, temporary
                    FROM duckdb_views()
                    WHERE view_name LIKE 'presentation_%'
                    """
                ).fetchall()
            )
            macros = {
                name: (function_type, parameters, parameter_types)
                for name, function_type, parameters, parameter_types in other_connection.execute(
                    """
                    SELECT function_name, function_type, parameters, parameter_types
                    FROM duckdb_functions()
                    WHERE function_name LIKE 'presentation_%'
                    """
                ).fetchall()
            }
            source_count = other_connection.execute("SELECT count(*) FROM report_rows").fetchone()
            scoped_target = other_connection.execute(
                "SELECT target_role, target_label FROM presentation_targets"
            ).fetchone()
            macro_target = other_connection.execute(
                """
                SELECT target_role, target_label
                FROM presentation_targets(
                    (SELECT scope FROM current_report_scope WHERE singleton)
                )
                """
            ).fetchone()
        finally:
            other_connection.close()

    assert set(views) == set(PRESENTATION_RELATIONS)
    assert not any(views.values())
    assert set(macros) == set(PRESENTATION_RELATIONS)
    assert all(function_type == "table_macro" for function_type, _, _ in macros.values())
    assert all(parameters == ["requested_scope"] for _, parameters, _ in macros.values())
    assert all(len(parameter_types) == 1 for _, _, parameter_types in macros.values())
    assert source_count == (1,)
    assert scoped_target == ("target", "current")
    assert macro_target == scoped_target


def test_presentation_views_and_typed_macros_preserve_column_names_and_types(tmp_path: Path) -> None:
    expected = """
### presentation_targets
- target_order: UINTEGER
- target_role: VARCHAR
- target_label: VARCHAR
- target_source: VARCHAR
- target_path: VARCHAR
- target_git_ref: VARCHAR
- target_git_sha: VARCHAR
- target_is_dirty: BOOLEAN
- binary_sha256: VARCHAR
### presentation_files
- file_order: UINTEGER
- file_sha256: VARCHAR
- fact_directory_sha256: VARCHAR
- file_path: VARCHAR
- absolute_file_path: VARCHAR
- fact_directory_path: VARCHAR
### presentation_cells
- cell_order: UINTEGER
- backend: VARCHAR
- treatment: ENUM('off', 'term', 'proofs')
### presentation_cell_estimates
- metric_order: UTINYINT
- target_order: UINTEGER
- file_order: UINTEGER
- cell_order: UINTEGER
- metric: VARCHAR
- backend: VARCHAR
- treatment: ENUM('off', 'term', 'proofs')
- sample_count: UINTEGER
- has_samples: BOOLEAN
- mean: DOUBLE
- ci_low: DOUBLE
- ci_high: DOUBLE
- result_class: VARCHAR
- issue: VARCHAR
### presentation_file_ratios
- comparison_order: UINTEGER
- metric_order: UTINYINT
- file_order: UINTEGER
- metric: VARCHAR
- baseline_target_order: UINTEGER
- baseline_cell_order: UINTEGER
- candidate_target_order: UINTEGER
- candidate_cell_order: UINTEGER
- baseline_sample_count: UINTEGER
- candidate_sample_count: UINTEGER
- has_samples: BOOLEAN
- point: DOUBLE
- ci_low: DOUBLE
- ci_high: DOUBLE
- change_fraction: DOUBLE
- change_ci_low: DOUBLE
- change_ci_high: DOUBLE
- is_valid: BOOLEAN
- ci_entirely_below_one: BOOLEAN
- ci_entirely_above_one: BOOLEAN
- result_class: VARCHAR
- issue: VARCHAR
### presentation_comparison_rollups
- comparison_order: UINTEGER
- metric_order: UTINYINT
- metric: VARCHAR
- baseline_target_order: UINTEGER
- baseline_cell_order: UINTEGER
- candidate_target_order: UINTEGER
- candidate_cell_order: UINTEGER
- baseline_total: DOUBLE
- candidate_total: DOUBLE
- has_samples: BOOLEAN
- suite_point: DOUBLE
- suite_ci_low: DOUBLE
- suite_ci_high: DOUBLE
- suite_change_fraction: DOUBLE
- suite_change_ci_low: DOUBLE
- suite_change_ci_high: DOUBLE
- suite_ci_entirely_below_two: BOOLEAN
- suite_result_class: VARCHAR
- suite_issue: VARCHAR
- geometric_mean_point: DOUBLE
- geometric_mean_change_fraction: DOUBLE
- geometric_mean_result_class: VARCHAR
- geometric_mean_issue: VARCHAR
- file_count: UINTEGER
- comparable_file_count: UINTEGER
- better_file_count: UINTEGER
- best_file_order: UINTEGER
- best_point: DOUBLE
- best_ci_low: DOUBLE
- best_ci_high: DOUBLE
- best_change_fraction: DOUBLE
- best_result_class: VARCHAR
- best_issue: VARCHAR
- worst_file_order: UINTEGER
- worst_point: DOUBLE
- worst_ci_low: DOUBLE
- worst_ci_high: DOUBLE
- worst_change_fraction: DOUBLE
- worst_result_class: VARCHAR
- worst_issue: VARCHAR
### presentation_compact_timings
- target_order: UINTEGER
- file_order: UINTEGER
- cell_order: UINTEGER
- backend: VARCHAR
- treatment: ENUM('off', 'term', 'proofs')
- search_ns: DOUBLE
- apply_ns: DOUBLE
- search_and_apply_ns: DOUBLE
- unattributed_ns: DOUBLE
- pre_merge_ns: DOUBLE
- merge_ns: DOUBLE
- rebuild_ns: DOUBLE
- ruleset_total_ns: DOUBLE
- outside_rulesets_ns: DOUBLE
- other_ns: DOUBLE
- wall_ns: DOUBLE
- has_samples: BOOLEAN
- result_class: VARCHAR
- issue: VARCHAR
### presentation_ruleset_timings
- file_order: UINTEGER
- cell_order: UINTEGER
- ruleset_order: UINTEGER
- target_order: UINTEGER
- backend: VARCHAR
- treatment: ENUM('off', 'term', 'proofs')
- name: VARCHAR
- search_ns: DOUBLE
- apply_ns: DOUBLE
- search_and_apply_ns: DOUBLE
- unattributed_ns: DOUBLE
- pre_merge_ns: DOUBLE
- merge_ns: DOUBLE
- rebuild_ns: DOUBLE
- total_ns: DOUBLE
- maximum_target_total: DOUBLE
- result_ruleset_total_ns: DOUBLE
- has_samples: BOOLEAN
- result_class: VARCHAR
- ruleset_share: DOUBLE
""".strip()

    with ReportDatabase(tmp_path / "report.jsonl") as database:
        actual_sections: list[str] = []
        for name in PRESENTATION_RELATIONS:
            view_schema = database._connection.execute(f"DESCRIBE FROM {name}").fetchall()
            macro_schema = database._connection.execute(
                f"""
                DESCRIBE FROM {name}(
                    (SELECT scope FROM current_report_scope WHERE singleton)
                )
                """
            ).fetchall()
            view_columns = [(row[0], row[1]) for row in view_schema]
            macro_columns = [(row[0], row[1]) for row in macro_schema]
            assert macro_columns == view_columns
            actual_sections.append(
                "\n".join([f"### {name}", *(f"- {column}: {data_type}" for column, data_type in view_columns)])
            )

    assert "\n".join(actual_sections) == expected


def test_arbitrary_scope_macro_recomputes_without_changing_current_view(tmp_path: Path) -> None:
    report = tmp_path / "report.jsonl"
    write_report(
        report,
        make_record(0, started_at="2026-07-15T12:00:00Z", wall_sec=1.0),
        make_record(1, started_at="2026-07-15T12:00:01Z", wall_sec=3.0),
    )
    target = make_target(target_label="current")
    file_spec = models.FileSpec("file.egg", tmp_path / "file.egg", "sha256:file")
    spec = models.BenchmarkSpec((file_spec,), ("off",), rounds=2, timeout_sec=120)

    with ReportDatabase(report) as database:
        database.install_scope((target,), spec, t_critical_95=12.706204736432095, requests=())
        stored = database._connection.execute("SELECT scope FROM current_report_scope WHERE singleton").fetchone()
        assert stored is not None
        alternate_scope = cast(SqlReportScope, stored[0])
        alternate_scope["rounds"] = 1
        current_before = database._connection.execute(
            "SELECT mean FROM presentation_cell_estimates WHERE metric = 'wall_sec'"
        ).fetchone()
        alternate = database._connection.execute(
            """
            SELECT mean
            FROM presentation_cell_estimates(?::report_scope_t)
            WHERE metric = 'wall_sec'
            """,
            [alternate_scope],
        ).fetchone()
        current_after = database._connection.execute(
            "SELECT mean FROM presentation_cell_estimates WHERE metric = 'wall_sec'"
        ).fetchone()

    assert current_before == (2.0,)
    assert alternate == (3.0,)
    assert current_after == current_before


def test_python_and_duckdb_schemas_match_and_nested_values_round_trip(tmp_path: Path) -> None:
    report = tmp_path / "report.jsonl"
    record = make_record(
        0,
        started_at="2026-07-15T12:00:00Z",
        max_rss_bytes=1234,
        timing_summary=make_timing_summary(
            make_ruleset_timing(
                "rules/\N{GREEK SMALL LETTER LAMDA}",
                search_ns=6,
                apply_ns=5,
                unattributed_ns=4,
                merge_ns=7,
                rebuild_ns=3,
            ),
            make_ruleset_timing("", search_ns=0, apply_ns=0, merge_ns=5, rebuild_ns=0),
        ),
    )

    with ReportDatabase(report) as database:
        database.append(record)
        described = database._connection.execute("DESCRIBE report_rows").fetchall()
        sql_fields = tuple(row[0] for row in described if row[0] != "row_index")
        python_fields = tuple(ReportRecord.__annotations__)
        cursor = database._connection.execute(f"SELECT {', '.join(python_fields)} FROM report_rows")
        result_fields = tuple(column[0] for column in cursor.description)
        loaded = cursor.fetchone()

    assert sql_fields == python_fields
    assert loaded is not None
    round_tripped = dict(zip(result_fields, loaded, strict=True))
    assert round_tripped == record
    summary = cast(dict[str, object], round_tripped["timing_summary"])
    assert tuple(summary) == tuple(TimingSummaryRecord.__annotations__)
    rulesets = cast(list[dict[str, object]], summary["rulesets"])
    assert tuple(rulesets[0]) == tuple(RulesetTimingRecord.__annotations__)
    assert "search_and_apply_ns" not in rulesets[0]
    assert "pre_merge_ns" not in rulesets[0]


@pytest.mark.parametrize("mixed", [False, True], ids=["old", "mixed"])
def test_old_report_shapes_fail_during_database_construction(tmp_path: Path, mixed: bool) -> None:
    report = tmp_path / "report.jsonl"
    current = make_record(0, started_at="2026-07-15T12:00:00Z")
    old = cast(dict[str, object], make_record(1, started_at="2026-07-15T12:00:01Z"))
    old["report_schema_version"] = 1
    records = (current, cast(ReportRecord, old)) if mixed else (cast(ReportRecord, old),)
    write_report(report, *records)

    with pytest.raises(
        ValueError,
        match=r"invalid or incompatible benchmark report.*Move or remove.*recompute",
    ):
        ReportDatabase(report)


@pytest.mark.parametrize("empty_rulesets", [False, True], ids=["missing-field", "empty"])
def test_old_timing_summary_fails_during_database_construction(tmp_path: Path, empty_rulesets: bool) -> None:
    report = tmp_path / "report.jsonl"
    old = cast(dict[str, object], make_record(0, started_at="2026-07-15T12:00:00Z"))
    summary = cast(dict[str, object], old["timing_summary"])
    summary["schema_version"] = 1
    rulesets = cast(list[dict[str, object]], summary["rulesets"])
    if empty_rulesets:
        rulesets.clear()
    else:
        del rulesets[0]["unattributed_ns"]
    write_report(report, cast(ReportRecord, old))

    with pytest.raises(
        ValueError,
        match=r"invalid or incompatible benchmark report.*Move or remove.*recompute",
    ):
        ReportDatabase(report)


def test_bulk_status_selection_uses_all_cache_dimensions_and_jsonl_tie_order(tmp_path: Path) -> None:
    report = tmp_path / "report.jsonl"
    records = (
        make_record(0, started_at="2026-07-15T12:00:00Z", status="failure", wall_sec=1.0),
        make_record(1, started_at="2026-07-15T12:00:01Z", status="timed-out"),
        make_record(2, started_at="2026-07-15T12:00:01Z", wall_sec=3.0),
        make_record(
            3,
            started_at="2026-07-15T12:00:02Z",
            wall_sec=9.0,
            fact_directory_sha256="sha256:other-facts",
        ),
    )
    write_report(report, *records)
    exact = models.EstimateKey("sha256:bin", "sha256:file", "off", 120)
    other_facts = models.EstimateKey(
        "sha256:bin",
        "sha256:file",
        "off",
        120,
        fact_directory_sha256="sha256:other-facts",
    )

    with ReportDatabase(report) as database:
        selected = database.selected_statuses_for_keys((exact, other_facts), 2)
        target = make_target(binary_sha256="sha256:bin")
        file_spec = models.FileSpec("file.egg", tmp_path / "file.egg", "sha256:file")
        spec = models.BenchmarkSpec((file_spec,), ("off",), rounds=2, timeout_sec=120)
        database.install_scope((target,), spec, t_critical_95=12.706204736432095, requests=())
        scoped_statuses = tuple(
            row[0]
            for row in database._connection.execute(
                """
                SELECT status
                FROM scoped_observations(
                    (SELECT scope FROM current_report_scope WHERE singleton)
                )
                ORDER BY started_at::TIMESTAMPTZ, row_index
                """
            ).fetchall()
        )

    assert selected[exact] == ("timed-out", "success")
    assert selected[other_facts] == ("success",)
    assert scoped_statuses == selected[exact]


def test_scope_cell_and_comparison_statistics_match_expected_formulas(tmp_path: Path) -> None:
    report = tmp_path / "report.jsonl"
    file_spec = models.FileSpec("file.egg", tmp_path / "file.egg", "sha256:file")
    spec = models.BenchmarkSpec((file_spec,), ("off",), rounds=2, timeout_sec=120)
    baseline = make_target(target_label="baseline", binary_sha256="sha256:baseline")
    candidate = make_target(target_label="candidate", binary_sha256="sha256:candidate")
    write_report(
        report,
        make_record(0, started_at="2026-07-15T12:00:00Z", binary_sha256="sha256:baseline", wall_sec=1.0),
        make_record(1, started_at="2026-07-15T12:00:01Z", binary_sha256="sha256:baseline", wall_sec=1.2),
        make_record(2, started_at="2026-07-15T12:00:00Z", binary_sha256="sha256:candidate", wall_sec=2.0),
        make_record(3, started_at="2026-07-15T12:00:01Z", binary_sha256="sha256:candidate", wall_sec=2.2),
    )

    with ReportDatabase(report) as database:
        database.install_scope(
            (baseline, candidate),
            spec,
            t_critical_95=12.706204736432095,
            requests=(ComparisonRequest(0, 0, 1, 0),),
        )
        views = database.report_view_data(include_timing=False)

    cells = [row for row in views.cell_estimates if row.metric == "wall_sec"]
    comparison = next(row for row in views.comparison_rollups if row.metric == "wall_sec")
    file_ratio = next(row for row in views.file_ratios if row.metric == "wall_sec")
    assert len(cells) == 2
    assert cells[0].sample_count == 2
    assert cells[0].mean == pytest.approx(1.1)
    assert file_ratio.point == pytest.approx(2.1 / 1.1)
    assert comparison.suite_point == pytest.approx(2.1 / 1.1)
    assert comparison.geometric_mean_point == pytest.approx(2.1 / 1.1)


def test_sql_t_and_fieller_intervals_match_reference_formulas(tmp_path: Path) -> None:
    report = tmp_path / "report.jsonl"
    files = (
        models.FileSpec("first.egg", tmp_path / "first.egg", "sha256:first"),
        models.FileSpec("second.egg", tmp_path / "second.egg", "sha256:second"),
    )
    spec = models.BenchmarkSpec(files, ("off",), rounds=3, timeout_sec=120)
    baseline = make_target(target_label="baseline", binary_sha256="sha256:baseline")
    candidate = make_target(target_label="candidate", binary_sha256="sha256:candidate")
    t_critical = 4.302652729911275
    samples = (
        (baseline.binary_sha256, files[0].sha256, (9.9, 10.0, 10.1)),
        (candidate.binary_sha256, files[0].sha256, (7.9, 8.0, 8.1)),
        (baseline.binary_sha256, files[1].sha256, (19.8, 20.0, 20.2)),
        (candidate.binary_sha256, files[1].sha256, (21.8, 22.0, 22.2)),
    )
    records: list[ReportRecord] = []
    for binary_sha256, file_sha256, values in samples:
        for wall_sec in values:
            records.append(
                make_record(
                    len(records),
                    started_at=f"2026-07-15T12:00:{len(records):02d}Z",
                    binary_sha256=binary_sha256,
                    file_sha256=file_sha256,
                    wall_sec=wall_sec,
                )
            )
    write_report(report, *records)

    with ReportDatabase(report) as database:
        database.install_scope(
            (baseline, candidate),
            spec,
            t_critical_95=t_critical,
            requests=(ComparisonRequest(0, 0, 1, 0),),
        )
        views = database.report_view_data(include_timing=False)

    baseline_first = next(
        row
        for row in views.cell_estimates
        if row.metric == "wall_sec" and row.target_order == 0 and row.file_order == 0
    )
    expected_cell_half_width = t_critical * math.sqrt(0.01 / 3)
    assert baseline_first.mean == pytest.approx(10.0)
    assert baseline_first.ci_low == pytest.approx(10.0 - expected_cell_half_width)
    assert baseline_first.ci_high == pytest.approx(10.0 + expected_cell_half_width)

    first_file = next(row for row in views.file_ratios if row.metric == "wall_sec" and row.file_order == 0)
    expected_file_low, expected_file_high = _fieller_bounds(
        baseline_mean=10.0,
        baseline_var_mean=0.01 / 3,
        candidate_mean=8.0,
        candidate_var_mean=0.01 / 3,
        t_critical=t_critical,
    )
    assert first_file.point == pytest.approx(0.8)
    assert first_file.ci_low == pytest.approx(expected_file_low)
    assert first_file.ci_high == pytest.approx(expected_file_high)

    suite = next(row for row in views.comparison_rollups if row.metric == "wall_sec")
    expected_suite_low, expected_suite_high = _fieller_bounds(
        baseline_mean=30.0,
        baseline_var_mean=(0.01 + 0.04) / 3,
        candidate_mean=30.0,
        candidate_var_mean=(0.01 + 0.04) / 3,
        t_critical=t_critical,
    )
    assert suite.baseline_total == pytest.approx(30.0)
    assert suite.candidate_total == pytest.approx(30.0)
    assert suite.suite_point == pytest.approx(1.0)
    assert suite.suite_ci_low == pytest.approx(expected_suite_low)
    assert suite.suite_ci_high == pytest.approx(expected_suite_high)


@pytest.mark.parametrize(
    ("rounds", "baseline_values", "candidate_values", "t_critical", "expected_issue"),
    [
        (1, (1.0,), (2.0,), None, "CI undefined for n < 2"),
        (
            2,
            (1.0, 2.0),
            (1.0, 1.1),
            12.706204736432095,
            "Fieller interval undefined",
        ),
    ],
    ids=["one-sample", "fieller-denominator-crosses-zero"],
)
def test_file_and_suite_interval_undefined_branches(
    tmp_path: Path,
    rounds: int,
    baseline_values: tuple[float, ...],
    candidate_values: tuple[float, ...],
    t_critical: float | None,
    expected_issue: str,
) -> None:
    report = tmp_path / "report.jsonl"
    file_spec = models.FileSpec("file.egg", tmp_path / "file.egg", "sha256:file")
    spec = models.BenchmarkSpec((file_spec,), ("off",), rounds=rounds, timeout_sec=120)
    baseline = make_target(target_label="baseline", binary_sha256="sha256:baseline")
    candidate = make_target(target_label="candidate", binary_sha256="sha256:candidate")
    records: list[ReportRecord] = []
    for binary_sha256, values in (
        (baseline.binary_sha256, baseline_values),
        (candidate.binary_sha256, candidate_values),
    ):
        for wall_sec in values:
            records.append(
                make_record(
                    len(records),
                    started_at=f"2026-07-15T12:00:{len(records):02d}Z",
                    binary_sha256=binary_sha256,
                    wall_sec=wall_sec,
                )
            )
    write_report(report, *records)

    with ReportDatabase(report) as database:
        database.install_scope(
            (baseline, candidate),
            spec,
            t_critical_95=t_critical,
            requests=(ComparisonRequest(0, 0, 1, 0),),
        )
        views = database.report_view_data(include_timing=False)

    file_ratio = next(row for row in views.file_ratios if row.metric == "wall_sec")
    suite = next(row for row in views.comparison_rollups if row.metric == "wall_sec")
    assert file_ratio.point is not None
    assert file_ratio.ci_low is None
    assert file_ratio.ci_high is None
    assert file_ratio.result_class == "point_only"
    assert file_ratio.issue == expected_issue
    assert suite.suite_point is not None
    assert suite.suite_ci_low is None
    assert suite.suite_ci_high is None
    assert suite.suite_result_class == "point_only"
    assert suite.suite_issue == expected_issue


def test_zero_candidate_mean_keeps_suite_ratio_and_marks_geometric_mean_unavailable(tmp_path: Path) -> None:
    report = tmp_path / "report.jsonl"
    file_spec = models.FileSpec("file.egg", tmp_path / "file.egg", "sha256:file")
    spec = models.BenchmarkSpec((file_spec,), ("off",), rounds=2, timeout_sec=120)
    baseline = make_target(target_label="baseline", binary_sha256="sha256:baseline")
    candidate = make_target(target_label="candidate", binary_sha256="sha256:candidate")
    write_report(
        report,
        make_record(0, started_at="2026-07-15T12:00:00Z", binary_sha256="sha256:baseline", wall_sec=1.0),
        make_record(1, started_at="2026-07-15T12:00:01Z", binary_sha256="sha256:baseline", wall_sec=1.0),
        make_record(2, started_at="2026-07-15T12:00:00Z", binary_sha256="sha256:candidate", wall_sec=0.0),
        make_record(3, started_at="2026-07-15T12:00:01Z", binary_sha256="sha256:candidate", wall_sec=0.0),
    )

    with ReportDatabase(report) as database:
        database.install_scope(
            (baseline, candidate),
            spec,
            t_critical_95=12.706204736432095,
            requests=(ComparisonRequest(0, 0, 1, 0),),
        )
        views = database.report_view_data(include_timing=False)
        comparison = next(row for row in views.comparison_rollups if row.metric == "wall_sec")

    assert comparison.suite_point == 0.0
    assert comparison.geometric_mean_point is None
    assert comparison.geometric_mean_issue == "mean unavailable"


def test_comparison_rollup_view_owns_best_worst_counts_and_totals(tmp_path: Path) -> None:
    report = tmp_path / "report.jsonl"
    files = tuple(
        models.FileSpec(f"file-{index}.egg", tmp_path / f"file-{index}.egg", f"sha256:file-{index}")
        for index in range(3)
    )
    spec = models.BenchmarkSpec(files, ("off",), rounds=1, timeout_sec=120)
    baseline = make_target(target_label="baseline", binary_sha256="sha256:baseline")
    candidate = make_target(target_label="candidate", binary_sha256="sha256:candidate")
    records: list[ReportRecord] = []
    for file_order, candidate_wall in enumerate((0.5, 2.0, None)):
        records.append(
            make_record(
                len(records),
                started_at=f"2026-07-15T12:00:0{len(records)}Z",
                binary_sha256=baseline.binary_sha256,
                file_sha256=files[file_order].sha256,
                wall_sec=1.0,
            )
        )
        records.append(
            make_record(
                len(records),
                started_at=f"2026-07-15T12:00:0{len(records)}Z",
                binary_sha256=candidate.binary_sha256,
                file_sha256=files[file_order].sha256,
                status="success" if candidate_wall is not None else "failure",
                wall_sec=candidate_wall,
            )
        )
    write_report(report, *records)

    with ReportDatabase(report) as database:
        database.install_scope(
            (baseline, candidate),
            spec,
            t_critical_95=None,
            requests=(ComparisonRequest(0, 0, 1, 0),),
        )
        views = database.report_view_data(include_timing=False)
        rollup = next(row for row in views.comparison_rollups if row.metric == "wall_sec")

    assert rollup.file_count == 3
    assert rollup.comparable_file_count == 2
    assert rollup.better_file_count == 0
    assert rollup.best_file_order == 0
    assert rollup.best_point == 0.5
    assert rollup.best_result_class == "point_only"
    assert rollup.worst_file_order == 2
    assert rollup.worst_point is None
    assert rollup.worst_result_class == "invalid"
    assert rollup.baseline_total == 3.0
    assert rollup.candidate_total is None


def test_report_scope_rejects_targets_with_the_same_binary(tmp_path: Path) -> None:
    report = tmp_path / "report.jsonl"
    file_spec = models.FileSpec("file.egg", tmp_path / "file.egg", "sha256:file")
    spec = models.BenchmarkSpec((file_spec,), ("off",), rounds=2, timeout_sec=120)
    first = make_target(target_label="first", binary_sha256="sha256:shared")
    second = make_target(target_label="second", binary_sha256="sha256:shared")

    with (
        ReportDatabase(report) as database,
        pytest.raises(ValueError, match=r"targets 'first' and 'second' produced the same binary SHA-256"),
    ):
        database.install_scope((first, second), spec, t_critical_95=12.706204736432095, requests=())


def test_invalid_result_rulesets_do_not_contaminate_valid_result_union(tmp_path: Path) -> None:
    report = tmp_path / "report.jsonl"
    file_spec = models.FileSpec("file.egg", tmp_path / "file.egg", "sha256:file")
    spec = models.BenchmarkSpec((file_spec,), ("off",), rounds=2, timeout_sec=120)
    invalid = make_target(target_label="invalid", binary_sha256="sha256:invalid")
    valid = make_target(target_label="valid", binary_sha256="sha256:valid")
    write_report(
        report,
        make_record(
            0,
            started_at="2026-07-15T12:00:00Z",
            binary_sha256="sha256:invalid",
            timing_summary=make_timing_summary(make_ruleset_timing("invalid-only")),
        ),
        make_record(
            1,
            started_at="2026-07-15T12:00:01Z",
            binary_sha256="sha256:invalid",
            status="failure",
        ),
        make_record(
            2,
            started_at="2026-07-15T12:00:00Z",
            binary_sha256="sha256:valid",
            timing_summary=make_timing_summary(
                make_ruleset_timing("valid", search_ns=60, apply_ns=40, unattributed_ns=10, merge_ns=20, rebuild_ns=5)
            ),
        ),
        make_record(
            3,
            started_at="2026-07-15T12:00:01Z",
            binary_sha256="sha256:valid",
            timing_summary=make_timing_summary(),
        ),
    )

    with ReportDatabase(report) as database:
        database.install_scope((invalid, valid), spec, t_critical_95=12.706204736432095, requests=())
        views = database.report_view_data(include_timing=True)

    timings = {row.target_order: row for row in views.compact_timings}
    invalid_metric = next(row for row in views.cell_estimates if row.target_order == 0 and row.metric == "wall_sec")
    assert invalid_metric.issue == timings[0].issue
    assert invalid_metric.result_class == timings[0].result_class
    assert timings[0].issue == "failure row selected"
    assert timings[0].result_class == "invalid"
    assert not timings[0].has_samples
    assert timings[0].search_ns is None
    assert timings[0].apply_ns is None
    assert timings[0].search_and_apply_ns is None
    assert timings[0].unattributed_ns is None
    assert timings[0].pre_merge_ns is None
    assert timings[0].merge_ns is None
    assert timings[0].rebuild_ns is None
    assert timings[0].ruleset_total_ns is None
    assert timings[0].outside_rulesets_ns is None
    assert timings[0].other_ns is None
    assert timings[0].wall_ns is None
    assert timings[1].issue is None
    assert timings[1].search_ns is not None
    assert timings[1].apply_ns is not None
    assert timings[1].search_and_apply_ns == timings[1].search_ns + timings[1].apply_ns
    assert timings[1].unattributed_ns is not None
    assert timings[1].pre_merge_ns == timings[1].search_and_apply_ns + timings[1].unattributed_ns
    assert timings[1].ruleset_total_ns is not None
    assert timings[1].wall_ns is not None
    assert timings[1].outside_rulesets_ns == timings[1].wall_ns - timings[1].ruleset_total_ns
    assert timings[1].other_ns == timings[1].unattributed_ns + timings[1].outside_rulesets_ns
    valid_rulesets = [row for row in views.ruleset_timings if row.target_order == 1]
    assert [ruleset.name for ruleset in valid_rulesets] == ["rules", "valid"]
    assert "invalid-only" not in {ruleset.name for ruleset in valid_rulesets}
    means = {ruleset.name: ruleset for ruleset in valid_rulesets}
    assert means["valid"].search_ns == 30
    assert means["valid"].apply_ns == 20
    assert means["valid"].search_and_apply_ns == 50
    assert means["valid"].unattributed_ns == 5
    assert means["valid"].pre_merge_ns == 55


def test_ruleset_union_distinguishes_absence_from_recorded_zero(tmp_path: Path) -> None:
    report = tmp_path / "report.jsonl"
    file_spec = models.FileSpec("file.egg", tmp_path / "file.egg", "sha256:file")
    spec = models.BenchmarkSpec((file_spec,), ("off",), rounds=2, timeout_sec=120)
    baseline = make_target(target_label="baseline", binary_sha256="sha256:baseline")
    candidate = make_target(target_label="candidate", binary_sha256="sha256:candidate")
    zero = make_ruleset_timing("recorded-zero", search_ns=0, apply_ns=0, unattributed_ns=0, merge_ns=0, rebuild_ns=0)
    write_report(
        report,
        make_record(
            0,
            started_at="2026-07-15T12:00:00Z",
            binary_sha256=baseline.binary_sha256,
            timing_summary=make_timing_summary(
                make_ruleset_timing("baseline-only", search_ns=10, apply_ns=0, merge_ns=0, rebuild_ns=0),
                make_ruleset_timing("sporadic", search_ns=8, apply_ns=0, unattributed_ns=6, merge_ns=0, rebuild_ns=0),
                zero,
            ),
        ),
        make_record(
            1,
            started_at="2026-07-15T12:00:01Z",
            binary_sha256=baseline.binary_sha256,
            timing_summary=make_timing_summary(
                make_ruleset_timing("baseline-only", search_ns=10, apply_ns=0, merge_ns=0, rebuild_ns=0),
                zero,
            ),
        ),
        make_record(
            2,
            started_at="2026-07-15T12:00:00Z",
            binary_sha256=candidate.binary_sha256,
            timing_summary=make_timing_summary(
                make_ruleset_timing("candidate-only", search_ns=20, apply_ns=0, merge_ns=0, rebuild_ns=0),
                zero,
            ),
        ),
        make_record(
            3,
            started_at="2026-07-15T12:00:01Z",
            binary_sha256=candidate.binary_sha256,
            timing_summary=make_timing_summary(
                make_ruleset_timing("candidate-only", search_ns=20, apply_ns=0, merge_ns=0, rebuild_ns=0),
                zero,
            ),
        ),
    )

    with ReportDatabase(report) as database:
        database.install_scope((baseline, candidate), spec, t_critical_95=12.706204736432095, requests=())
        views = database.report_view_data(include_timing=True)

    rows = {(row.target_order, row.name): row for row in views.ruleset_timings}
    for target_order, absent_name in ((0, "candidate-only"), (1, "baseline-only"), (1, "sporadic")):
        absent = rows[target_order, absent_name]
        assert not absent.has_samples
        assert absent.result_class == "available"
        assert absent.search_ns is None
        assert absent.apply_ns is None
        assert absent.search_and_apply_ns is None
        assert absent.unattributed_ns is None
        assert absent.pre_merge_ns is None
        assert absent.merge_ns is None
        assert absent.rebuild_ns is None
        assert absent.total_ns is None
        assert absent.ruleset_share is None

    for target_order in (0, 1):
        recorded_zero = rows[target_order, "recorded-zero"]
        assert recorded_zero.has_samples
        assert recorded_zero.search_ns == 0
        assert recorded_zero.total_ns == 0
        assert recorded_zero.ruleset_share == 0

    # Missing rounds remain zero contributions after the ruleset has appeared,
    # keeping detailed phase totals consistent with the compact all-round mean.
    assert rows[0, "sporadic"].search_ns == 4
    assert rows[0, "sporadic"].unattributed_ns == 3
    assert rows[0, "sporadic"].pre_merge_ns == 7
    compact = {row.target_order: row for row in views.compact_timings}
    baseline_search = sum(row.search_ns or 0 for row in views.ruleset_timings if row.target_order == 0)
    baseline_unattributed = sum(row.unattributed_ns or 0 for row in views.ruleset_timings if row.target_order == 0)
    assert compact[0].search_ns == baseline_search == 14
    assert compact[0].unattributed_ns == baseline_unattributed == 3


def test_append_failure_does_not_claim_a_persisted_row(tmp_path: Path) -> None:
    report = tmp_path / "report.jsonl"
    record = make_record(0, started_at="2026-07-15T12:00:00Z")

    with ReportDatabase(report) as database:
        report.unlink()
        report.mkdir()
        with pytest.raises(IsADirectoryError):
            database.append(record)

    assert report.is_dir()


def test_packaged_sql_loads_outside_repository_working_directory(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.chdir(tmp_path)

    with ReportDatabase(Path("report.jsonl")) as database:
        assert database.successful_estimate_aggregates() == ()

    assert (tmp_path / "report.jsonl").is_file()


def _fieller_bounds(
    *,
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
    return center - half_width, center + half_width
