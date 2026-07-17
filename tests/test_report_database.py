"""Test persistent DuckDB storage and pair-native report relations."""

from __future__ import annotations

import math
import subprocess
import sys
from pathlib import Path
from typing import cast

import duckdb
import pytest

from benchmarking import models
from benchmarking.reports import database as report_database
from benchmarking.reports.database import ReportDatabase, _fetch_rows
from benchmarking.reports.records import (
    ReportRecord,
    RulesetTimingRecord,
    TimingSummaryRecord,
)
from benchmarking.reports.results import (
    EndpointView,
    FileComparisonView,
    PhaseComparisonView,
    RulesetComparisonView,
    SummaryView,
)

from .conftest import make_record, make_ruleset_timing, make_target, make_timing_summary, write_report

PRESENTATION_RELATIONS = (
    "presentation_endpoints",
    "presentation_summary",
    "presentation_files",
    "presentation_phases",
    "presentation_rulesets",
)
PERSISTENT_TYPES = {
    "report_status_t",
    "report_treatment_t",
    "ruleset_timing_record_t",
    "timing_summary_record_t",
    "report_record_t",
}
SESSION_TYPES = {
    "selection_key_t",
    "report_scope_endpoint_t",
    "report_scope_file_t",
    "report_scope_t",
}


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


def test_missing_report_creates_an_empty_persistent_cache(tmp_path: Path) -> None:
    report = tmp_path / "nested" / "report.duckdb"

    with ReportDatabase(report) as database:
        assert database.successful_estimate_aggregates() == ()

    assert report.stat().st_size > 0
    assert list(report.parent.iterdir()) == [report]

    with ReportDatabase(report) as database:
        assert database.successful_estimate_aggregates() == ()


def test_append_is_immediately_queryable(tmp_path: Path) -> None:
    report = tmp_path / "report.duckdb"
    record = make_record(0, started_at="2026-07-15T12:00:00Z", target_label="current")
    replacement = make_record(
        1,
        started_at="2026-07-15T12:00:00Z",
        target_label="current",
        binary_sha256="sha256:replacement",
    )

    with ReportDatabase(report) as database:
        database.append(record)
        pointer = database.find_label_pointer("current")

    assert pointer is not None
    assert pointer.binary_sha256 == record["binary_sha256"]
    with ReportDatabase(report) as database:
        persisted = database.find_label_pointer("current")
        database.append(replacement)
        latest = database.find_label_pointer("current")
        row_indices = database._connection.execute("SELECT row_index FROM report_rows ORDER BY row_index").fetchall()

    assert persisted == pointer
    assert latest is not None
    assert latest.binary_sha256 == replacement["binary_sha256"]
    assert row_indices == [(0,), (1,)]


def test_failed_typed_insert_is_atomic_and_does_not_consume_the_sequence(tmp_path: Path) -> None:
    report = tmp_path / "report.duckdb"
    invalid = make_record(0, started_at="2026-07-15T12:00:00Z")
    invalid["timeout_sec"] = -1
    valid = make_record(1, started_at="2026-07-15T12:00:01Z")

    with ReportDatabase(report) as database:
        with pytest.raises(duckdb.Error, match="out of range"):
            database.append(invalid)
        assert database._connection.execute("SELECT * FROM report_rows").fetchall() == []
        database.append(valid)
        assert database._connection.execute("SELECT row_index, started_at FROM report_rows").fetchall() == [
            (0, valid["started_at"])
        ]

    with ReportDatabase(report) as database:
        assert database._connection.execute("SELECT row_index, started_at FROM report_rows").fetchall() == [
            (0, valid["started_at"])
        ]


def test_locked_cache_reports_wait_diagnostic_and_remains_readable(tmp_path: Path) -> None:
    report = tmp_path / "report.duckdb"
    write_report(report, make_record(0, started_at="2026-07-15T12:00:00Z"))
    holder = subprocess.Popen(
        [
            sys.executable,
            "-c",
            (
                "import duckdb, sys; "
                "connection = duckdb.connect(sys.argv[1]); "
                "print('ready', flush=True); sys.stdin.read()"
            ),
            str(report),
        ],
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    assert holder.stdout is not None
    try:
        assert holder.stdout.readline().strip() == "ready"
        with pytest.raises(ValueError, match=r"locked by another process.*Wait.*do not remove"):
            ReportDatabase(report)
    finally:
        if holder.poll() is None:
            holder.communicate(input="\n", timeout=5)

    with ReportDatabase(report) as database:
        assert len(database.successful_estimate_aggregates()) == 1


def test_failed_new_bootstrap_removes_only_its_artifacts_and_can_retry(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    report = tmp_path / "report.duckdb"
    original_resource = report_database._sql_resource

    def broken_resource(name: str) -> str:
        sql = original_resource(name)
        if name == "schema.sql":
            return sql + "\nSELECT * FROM missing_bootstrap_relation;"
        return sql

    monkeypatch.setattr(report_database, "_sql_resource", broken_resource)
    with pytest.raises(duckdb.Error, match="missing_bootstrap_relation"):
        ReportDatabase(report)

    assert not report.exists()
    assert not Path(f"{report}.wal").exists()
    assert not Path(f"{report}.tmp").exists()

    monkeypatch.setattr(report_database, "_sql_resource", original_resource)
    with ReportDatabase(report) as database:
        assert database._connection.execute("SELECT count(*) FROM report_rows").fetchone() == (0,)


def test_historical_estimates_are_grouped_as_counts_and_sums_in_sql(tmp_path: Path) -> None:
    report = tmp_path / "report.duckdb"
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


def test_five_presentation_relations_are_temporary_views_with_named_tuple_schemas(tmp_path: Path) -> None:
    expected_columns = (
        EndpointView._fields,
        SummaryView._fields,
        FileComparisonView._fields,
        PhaseComparisonView._fields,
        RulesetComparisonView._fields,
    )
    with ReportDatabase(tmp_path / "report.duckdb") as database:
        views = dict(
            database._connection.execute(
                """
                SELECT view_name, temporary
                FROM duckdb_views()
                WHERE view_name LIKE 'presentation_%'
                """
            ).fetchall()
        )
        macros = database._connection.execute(
            """
            SELECT function_name
            FROM duckdb_functions()
            WHERE function_name LIKE 'presentation_%'
            """
        ).fetchall()
        for name, expected in zip(PRESENTATION_RELATIONS, expected_columns, strict=True):
            columns = tuple(row[0] for row in database._connection.execute(f"DESCRIBE FROM {name}").fetchall())
            assert columns == expected

    assert set(views) == set(PRESENTATION_RELATIONS)
    assert all(views.values())
    assert macros == []


def test_only_record_types_and_tables_persist_across_report_sessions(tmp_path: Path) -> None:
    report = tmp_path / "report.duckdb"
    with ReportDatabase(report) as database:
        custom_types = dict(
            database._connection.execute(
                """
                SELECT type_name, database_name
                FROM duckdb_types()
                WHERE type_name IN (
                    'report_status_t',
                    'report_treatment_t',
                    'ruleset_timing_record_t',
                    'timing_summary_record_t',
                    'report_record_t',
                    'selection_key_t',
                    'report_scope_endpoint_t',
                    'report_scope_file_t',
                    'report_scope_t'
                )
                """
            ).fetchall()
        )

    assert set(custom_types) == PERSISTENT_TYPES | SESSION_TYPES
    assert {name for name, database_name in custom_types.items() if database_name == "temp"} == SESSION_TYPES
    assert all(custom_types[name] != "temp" for name in PERSISTENT_TYPES)

    connection = duckdb.connect(str(report), read_only=True)
    try:
        persisted_types = {
            row[0]
            for row in connection.execute("SELECT type_name FROM duckdb_types() WHERE type_name LIKE '%_t'").fetchall()
        }
        persisted_tables = {
            row[0] for row in connection.execute("SELECT table_name FROM duckdb_tables() WHERE NOT internal").fetchall()
        }
        persisted_views = {
            row[0] for row in connection.execute("SELECT view_name FROM duckdb_views() WHERE NOT internal").fetchall()
        }
    finally:
        connection.close()

    assert persisted_types >= PERSISTENT_TYPES
    assert not SESSION_TYPES & persisted_types
    assert persisted_tables == {"report_cache_metadata", "report_rows"}
    assert not set(PRESENTATION_RELATIONS) & persisted_views


def test_scope_is_a_single_immutable_pair_and_can_compare_backend_treatment_endpoints(tmp_path: Path) -> None:
    baseline = _endpoint("main/off", "sha256:shared", backend="main", treatment="off")
    candidate = _endpoint("DD/term", "sha256:shared", backend="dd", treatment="term")
    comparison = _comparison(tmp_path, baseline=baseline, candidate=candidate)

    with ReportDatabase(tmp_path / "report.duckdb") as database:
        database.install_scope(comparison, None)
        endpoints = database.report_view_data("summary").endpoints
        with pytest.raises(RuntimeError, match="already installed"):
            database.install_scope(comparison, None)
        count = database._connection.execute("SELECT count(*) FROM current_report_scope").fetchone()

    assert [(row.endpoint_role, row.backend, row.treatment) for row in endpoints] == [
        ("baseline", "main", "off"),
        ("candidate", "dd", "term"),
    ]
    assert count == (1,)


def test_report_view_data_fetches_only_the_requested_detail_relations(tmp_path: Path) -> None:
    report = tmp_path / "report.duckdb"
    comparison = _comparison(tmp_path)
    write_report(
        report,
        make_record(0, started_at="2026-07-15T12:00:00Z", binary_sha256="sha256:baseline"),
        make_record(1, started_at="2026-07-15T12:00:01Z", binary_sha256="sha256:candidate"),
    )

    with ReportDatabase(report) as database:
        with pytest.raises(RuntimeError, match="not installed"):
            database.report_view_data("summary")
        database.install_scope(comparison, None)
        summary = database.report_view_data("summary")
        files = database.report_view_data("files")
        phases = database.report_view_data("phases")
        rulesets = database.report_view_data("rulesets")

    assert len(summary.endpoints) == 2
    assert len(summary.summary) == 5
    assert not summary.files and not summary.phases and not summary.rulesets
    assert files.files and not files.phases and not files.rulesets
    assert phases.files and phases.phases and not phases.rulesets
    assert rulesets.files and rulesets.phases and rulesets.rulesets


def test_python_and_duckdb_record_schemas_match_and_nested_values_round_trip(tmp_path: Path) -> None:
    report = tmp_path / "report.duckdb"
    record = make_record(
        0,
        started_at="2026-07-15T12:00:00Z",
        max_rss_bytes=1234,
        timing_summary=make_timing_summary(
            make_ruleset_timing(
                "rules/N{GREEK SMALL LETTER LAMDA}",
                search_ns=6,
                apply_ns=5,
                unattributed_ns=4,
                merge_ns=7,
                rebuild_ns=3,
            )
        ),
    )

    with ReportDatabase(report) as database:
        database.append(record)
        described = database._connection.execute("DESCRIBE report_rows").fetchall()
        sql_fields = tuple(row[0] for row in described if row[0] != "row_index")
        python_fields = tuple(ReportRecord.__annotations__)
        cursor = database._connection.execute(f"SELECT {', '.join(python_fields)} FROM report_rows")
        loaded = cursor.fetchone()

    assert sql_fields == python_fields
    assert loaded is not None
    round_tripped = dict(zip(python_fields, loaded, strict=True))
    assert round_tripped == record
    summary = cast(dict[str, object], round_tripped["timing_summary"])
    assert tuple(summary) == tuple(TimingSummaryRecord.__annotations__)
    rulesets = cast(list[dict[str, object]], summary["rulesets"])
    assert tuple(rulesets[0]) == tuple(RulesetTimingRecord.__annotations__)


def test_incompatible_cache_version_fails_during_construction(tmp_path: Path) -> None:
    report = tmp_path / "report.duckdb"
    with ReportDatabase(report) as database:
        database._connection.execute("UPDATE report_cache_metadata SET schema_version = 0")

    with pytest.raises(ValueError, match=r"invalid or incompatible benchmark report.*recompute"):
        ReportDatabase(report)


def test_existing_non_database_artifact_fails_without_being_recreated(tmp_path: Path) -> None:
    report = tmp_path / "report.duckdb"
    report.write_text("{}\n", encoding="utf-8")

    with pytest.raises(ValueError, match=r"invalid or incompatible benchmark report.*recompute"):
        ReportDatabase(report)

    assert report.read_text(encoding="utf-8") == "{}\n"


def test_bulk_status_selection_uses_all_cache_dimensions_and_append_tie_order(tmp_path: Path) -> None:
    report = tmp_path / "report.duckdb"
    write_report(
        report,
        make_record(0, started_at="2026-07-15T12:00:00Z", status="failure"),
        make_record(1, started_at="2026-07-15T12:00:01Z", status="timed-out"),
        make_record(2, started_at="2026-07-15T12:00:01Z"),
        make_record(
            3,
            started_at="2026-07-15T12:00:02Z",
            fact_directory_sha256="sha256:other-facts",
        ),
    )
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

    assert selected[exact] == ("timed-out", "success")
    assert selected[other_facts] == ("success",)


def test_pair_statistics_and_fieller_intervals_are_computed_in_sql(tmp_path: Path) -> None:
    report = tmp_path / "report.duckdb"
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

    with ReportDatabase(report) as database:
        database.install_scope(comparison, t_critical)
        views = database.report_view_data("files")

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
    report = tmp_path / "report.duckdb"
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

    with ReportDatabase(report) as database:
        database.install_scope(comparison, None)
        summary = database.report_view_data("summary").summary

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
    report = tmp_path / "report.duckdb"
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

    with ReportDatabase(report) as database:
        database.install_scope(comparison, None)
        summary = database.report_view_data("summary").summary

    suite, *tails = summary
    assert suite.result_class == "invalid"
    assert suite.point is None
    assert suite.issue == "failure row selected"
    assert all(row.file_order == 0 for row in tails)
    assert all(row.point is not None for row in tails)


def test_valid_tail_does_not_inherit_an_unrelated_invalid_file_issue(tmp_path: Path) -> None:
    report = tmp_path / "report.duckdb"
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

    with ReportDatabase(report) as database:
        database.install_scope(comparison, 12.706204736432095)
        suite, *tails = database.report_view_data("summary").summary

    assert suite.issue == "failure row selected"
    assert all(row.file_order == 0 for row in tails)
    assert all(row.issue is None for row in tails)


def test_phase_rows_are_exact_components_and_other_is_wall_residual(tmp_path: Path) -> None:
    report = tmp_path / "report.duckdb"
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

    with ReportDatabase(report) as database:
        database.install_scope(comparison, None)
        phases = database.report_view_data("phases").phases

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
    report = tmp_path / "report.duckdb"
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

    with ReportDatabase(report) as database:
        database.install_scope(comparison, 12.706204736432095)
        rows = {row.name: row for row in database.report_view_data("rulesets").rulesets}

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
    report = tmp_path / "report.duckdb"
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

    with ReportDatabase(report) as database:
        database.install_scope(comparison, None)
        rulesets = database.report_view_data("rulesets").rulesets

    assert len(rulesets) == 10
    assert [row.name for row in rulesets] == [f"rules-{index:02d}" for index in range(10)]
    assert [row.ruleset_rank for row in rulesets] == list(range(1, 11))
    assert {row.ruleset_count for row in rulesets} == {12}


def test_complete_cached_endpoints_requires_latest_rounds_for_every_file_and_counts_any_status(tmp_path: Path) -> None:
    report = tmp_path / "report.duckdb"
    files = (
        models.FileSpec("first.egg", tmp_path / "first.egg", "sha256:first", fact_directory_sha256="facts:first"),
        models.FileSpec("second.egg", tmp_path / "second.egg", "sha256:second", fact_directory_sha256="facts:second"),
    )
    records: list[ReportRecord] = []

    def add(
        binary: str,
        file: models.FileSpec,
        second: int,
        *,
        status: models.Status = "success",
        label: str | None = None,
        timeout_sec: int = 120,
    ) -> None:
        records.append(
            make_record(
                len(records),
                started_at=f"2026-07-15T12:00:{second:02d}Z",
                binary_sha256=binary,
                file_sha256=file.sha256,
                fact_directory_sha256=file.fact_directory_sha256,
                status=status,
                target_label=label,
                timeout_sec=timeout_sec,
            )
        )

    add("sha256:complete", files[0], 0, status="failure", label="old")
    add("sha256:complete", files[0], 1, status="timed-out", label="middle")
    add("sha256:complete", files[1], 2, label="new")
    add("sha256:complete", files[1], 3, status="failure", label="newest")
    add("sha256:incomplete", files[0], 4)
    add("sha256:incomplete", files[0], 5)
    add("sha256:incomplete", files[1], 6)
    add("sha256:wrong-timeout", files[0], 7, timeout_sec=60)
    add("sha256:wrong-timeout", files[0], 8, timeout_sec=60)
    add("sha256:wrong-timeout", files[1], 9, timeout_sec=60)
    add("sha256:wrong-timeout", files[1], 10, timeout_sec=60)
    write_report(report, *records)

    with ReportDatabase(report) as database:
        endpoints = database.complete_cached_endpoints(files, rounds=2, timeout_sec=120)

    assert len(endpoints) == 1
    assert endpoints[0].binary_sha256 == "sha256:complete"
    assert endpoints[0].row.label == "newest"
    assert endpoints[0].cache_identity == ("sha256:complete", "main", "off")


def test_fetch_rows_rejects_sql_python_column_drift(tmp_path: Path) -> None:
    with ReportDatabase(tmp_path / "report.duckdb") as database:
        cursor = database._connection.execute("SELECT 0 AS wrong_column")
        with pytest.raises(RuntimeError, match="do not match"):
            _fetch_rows(cursor, EndpointView)


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
