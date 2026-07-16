"""Own the transient DuckDB catalog over the append-only benchmark JSONL.

This module appends trusted writer records, creates the direct JSONL scan,
installs the current typed report scope, loads the parameterized analysis
macros and current-scope presentation views, converts those rows to typed
contracts, and owns the optional DuckDB UI lifecycle. Persisted writer shapes
belong in :mod:`benchmarking.reports.records`; statistical and grouping
semantics belong in ``reports/sql``; table layout and text rendering belong in
the sibling summary, timing, and render modules.
"""

from __future__ import annotations

import json
from collections.abc import Sequence
from importlib import resources
from pathlib import Path
from typing import Any, NamedTuple, TypedDict

import duckdb

from ..models import (
    Backend,
    BenchmarkSpec,
    EstimateKey,
    ResolvedTarget,
    Status,
    TargetRow,
    Treatment,
    benchmark_cells,
    validate_unique_file_identities,
    validate_unique_target_binaries,
)
from .records import TIMING_SUMMARY_SCHEMA_VERSION, ReportRecord
from .results import (
    CachedTarget,
    CellEstimateView,
    CompactTimingView,
    ComparisonRequest,
    ComparisonRollupView,
    EstimateAggregate,
    FileRatioView,
    ReportViewData,
    RulesetTimingView,
    TargetView,
)


class _LabelPointerRow(NamedTuple):
    target_source: str
    target_path: str
    target_git_ref: str
    target_git_sha: str
    target_is_dirty: bool
    binary_sha256: str


class _SelectedStatusRow(NamedTuple):
    request_order: int
    status: Status


class _EstimateAggregateQueryRow(NamedTuple):
    binary_sha256: str
    file_sha256: str
    fact_directory_sha256: str
    backend: Backend
    treatment: Treatment
    timeout_sec: int
    sample_count: int
    total_wall_sec: float


class SqlReportScopeTarget(TypedDict):
    """Python mirror of SQL ``report_scope_target_t``."""

    binary_sha256: str
    target_label: str
    target_source: str
    target_path: str
    target_git_ref: str
    target_git_sha: str
    target_is_dirty: bool


class SqlReportScopeFile(TypedDict):
    """Python mirror of SQL ``report_scope_file_t``."""

    file_sha256: str
    fact_directory_sha256: str
    file_path: str
    absolute_file_path: str
    fact_directory_path: str | None


class SqlReportScopeCell(TypedDict):
    """Python mirror of SQL ``report_scope_cell_t``."""

    backend: Backend
    treatment: Treatment


class SqlReportScopeComparison(TypedDict):
    """Python mirror of SQL ``report_scope_comparison_t``."""

    baseline_target_order: int
    baseline_cell_order: int
    candidate_target_order: int
    candidate_cell_order: int


class SqlReportScope(TypedDict):
    """Python mirror of SQL ``report_scope_t`` passed to report table macros."""

    targets: list[SqlReportScopeTarget]
    files: list[SqlReportScopeFile]
    cells: list[SqlReportScopeCell]
    comparisons: list[SqlReportScopeComparison]
    rounds: int
    timeout_sec: int
    t_critical_95: float | None


class ReportDatabase:
    """Provide one transient SQL session with repeatable cache queries and one report scope."""

    def __init__(self, path: Path) -> None:
        self.path = path
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self.path.touch(exist_ok=True)
        # This private in-memory catalog owns only schemas, scope relations, and
        # report views. ``report_rows`` scans the JSONL directly; no report data
        # is copied into or persisted as a DuckDB database.
        self._connection = duckdb.connect(":memory:")
        self._closed = False
        try:
            self._connection.execute("SET threads = 1")
            self._connection.execute("SET preserve_insertion_order = true")
            # The UI queries through another connection to this database
            # instance, so bind the source path in a catalog macro rather than
            # a connection-local SET VARIABLE.
            report_path = _duckdb_string_literal(_escape_duckdb_glob(self.path))
            self._connection.execute(f"CREATE MACRO report_path() AS {report_path}")
            self._connection.execute(_sql_resource("schema.sql"))
            self._ensure_report_loads()
            self._connection.execute(_sql_resource("analysis.sql"))
            self._connection.execute(_sql_resource("presentation.sql"))
        except BaseException:
            self._connection.close()
            self._closed = True
            raise

    @property
    def display_path(self) -> str:
        """Return the path text used in report headings and diagnostics."""

        return str(self.path)

    def __enter__(self) -> ReportDatabase:
        self._ensure_open()
        return self

    def __exit__(self, _exc_type: object, _exc_value: object, _traceback: object) -> None:
        self.close()

    def close(self) -> None:
        """Release the transient connection without creating database artifacts."""

        if not self._closed:
            self._connection.close()
            self._closed = True

    def start_ui(self) -> str:
        """Open DuckDB's local UI on this report session and return its status."""

        self._ensure_open()
        try:
            row = self._connection.execute("CALL start_ui()").fetchone()
        except duckdb.Error as error:
            raise ValueError(
                "could not open the DuckDB UI; DuckDB may have been unable to install, "
                f"load, or start its ui extension: {error}"
            ) from error
        if row is None:
            raise ValueError("could not open the DuckDB UI: CALL start_ui() returned no status")
        status = str(row[0])
        if "different DuckDB instance" in status:
            raise ValueError(f"could not open the DuckDB UI for this report session: {status}")
        return status

    def _ensure_report_loads(self) -> None:
        """Reject a cache that does not satisfy the current record contracts."""

        try:
            # count(*) can be answered without projecting the cast record.
            # Referencing one member forces DuckDB to cast every complete JSON
            # object to report_record_t. The explicit version count also rejects
            # an old summary whose empty ruleset list cannot reveal its shape.
            counts = self._connection.execute(
                """
                SELECT
                    count(started_at),
                    count(*) FILTER (
                        WHERE timing_summary IS NOT NULL
                          AND timing_summary.schema_version != ?
                    )
                FROM report_rows
                """,
                [TIMING_SUMMARY_SCHEMA_VERSION],
            ).fetchone()
        except duckdb.Error as error:
            raise ValueError(self._incompatible_report_message()) from error
        if counts is None or counts[1] != 0:
            raise ValueError(self._incompatible_report_message())

    def append(self, record: ReportRecord) -> None:
        """Serialize one trusted writer record, then append one JSON line."""

        self._ensure_open()
        encoded = json.dumps(record, ensure_ascii=False, allow_nan=False, separators=(",", ":"))
        with self.path.open("a", encoding="utf-8") as handle:
            handle.write(encoded + "\n")

    def find_label_pointer(self, label: str) -> CachedTarget | None:
        """Return the latest JSONL row carrying ``label``, or ``None``."""

        self._ensure_open()
        rows = _fetch_rows(
            self._connection.execute(
                """
            SELECT
                target_source,
                target_path,
                target_git_ref,
                target_git_sha,
                target_is_dirty,
                binary_sha256
            FROM report_rows
            WHERE target_label = ?
            ORDER BY started_at::TIMESTAMPTZ DESC, row_index DESC
            LIMIT 1
            """,
                [label],
            ),
            _LabelPointerRow,
        )
        if not rows:
            return None
        row = rows[0]
        return CachedTarget(
            TargetRow(
                source=row.target_source,
                path=row.target_path,
                git_ref=row.target_git_ref,
                git_sha=row.target_git_sha,
                is_dirty=row.target_is_dirty,
                label=label,
            ),
            row.binary_sha256,
        )

    def selected_statuses(self, key: EstimateKey, rounds: int) -> tuple[Status, ...]:
        """Select statuses from the latest rounds for one exact cache key."""

        return self.selected_statuses_for_keys((key,), rounds)[key]

    def selected_statuses_for_keys(
        self,
        keys: Sequence[EstimateKey],
        rounds: int,
    ) -> dict[EstimateKey, tuple[Status, ...]]:
        """Select latest statuses for all distinct cache keys in one direct-file scan."""

        self._ensure_open()
        if rounds < 1:
            raise ValueError("rounds must be positive")
        distinct_keys = tuple(dict.fromkeys(keys))
        if not distinct_keys:
            return {}
        selection_keys = [
            {
                "request_order": order,
                "binary_sha256": key.binary_sha256,
                "file_sha256": key.file_sha256,
                "fact_directory_sha256": key.fact_directory_sha256,
                "backend": key.backend,
                "treatment": key.treatment,
                "timeout_sec": key.timeout_sec,
            }
            for order, key in enumerate(distinct_keys)
        ]
        rows = _fetch_rows(
            self._connection.execute(
                """
            WITH selection_keys AS (
                SELECT key.*
                FROM unnest(?::selection_key_t[]) AS parameters(key)
            ),
            ranked AS (
                SELECT
                    keys.request_order,
                    reports.row_index,
                    reports.started_at,
                    reports.status,
                    row_number() OVER (
                        PARTITION BY keys.request_order
                        ORDER BY reports.started_at::TIMESTAMPTZ DESC, reports.row_index DESC
                    ) AS selection_rank
                FROM selection_keys AS keys
                JOIN report_rows AS reports
                    ON reports.binary_sha256 = keys.binary_sha256
                    AND reports.file_sha256 = keys.file_sha256
                    AND reports.fact_directory_sha256 = keys.fact_directory_sha256
                    AND reports.backend = keys.backend
                    AND reports.treatment = keys.treatment
                    AND reports.timeout_sec = keys.timeout_sec
            )
            SELECT
                request_order,
                status
            FROM ranked
            WHERE selection_rank <= ?
            ORDER BY request_order, started_at::TIMESTAMPTZ, row_index
            """,
                [selection_keys, rounds],
            ),
            _SelectedStatusRow,
        )
        selected: dict[EstimateKey, list[Status]] = {key: [] for key in distinct_keys}
        for row in rows:
            selected[distinct_keys[row.request_order]].append(row.status)
        return {key: tuple(statuses) for key, statuses in selected.items()}

    def successful_estimate_aggregates(self) -> tuple[EstimateAggregate, ...]:
        """Return SQL-grouped historical wall totals for ETA modeling."""

        self._ensure_open()
        rows = _fetch_rows(
            self._connection.execute(
                """
            SELECT
                binary_sha256,
                file_sha256,
                fact_directory_sha256,
                backend,
                treatment,
                timeout_sec,
                sample_count,
                total_wall_sec
            FROM historical_process_estimates
            ORDER BY binary_sha256, file_sha256, fact_directory_sha256, backend, treatment, timeout_sec
            """
            ),
            _EstimateAggregateQueryRow,
        )
        return tuple(
            EstimateAggregate(
                EstimateKey(
                    binary_sha256=row.binary_sha256,
                    file_sha256=row.file_sha256,
                    treatment=row.treatment,
                    timeout_sec=row.timeout_sec,
                    backend=row.backend,
                    fact_directory_sha256=row.fact_directory_sha256,
                ),
                row.sample_count,
                row.total_wall_sec,
            )
            for row in rows
        )

    def install_scope(
        self,
        targets: Sequence[ResolvedTarget],
        spec: BenchmarkSpec,
        t_critical_95: float | None,
        requests: Sequence[ComparisonRequest],
    ) -> None:
        """Install one immutable typed scope for the current report views."""

        self._ensure_open()
        cells = benchmark_cells(spec)
        if not targets:
            raise ValueError("report scope requires at least one target")
        if not spec.files:
            raise ValueError("report scope requires at least one file")
        validate_unique_target_binaries(targets)
        validate_unique_file_identities(spec.files)
        if not cells:
            raise ValueError("report scope requires at least one supported backend/treatment cell")
        if spec.rounds < 1:
            raise ValueError("report scope rounds must be positive")
        if spec.timeout_sec < 1:
            raise ValueError("report scope timeout must be positive")

        scope: SqlReportScope = {
            "targets": [
                {
                    "binary_sha256": target.binary_sha256,
                    "target_label": target.display_label,
                    "target_source": target.row.source,
                    "target_path": target.row.path,
                    "target_git_ref": target.row.git_ref,
                    "target_git_sha": target.row.git_sha,
                    "target_is_dirty": target.row.is_dirty,
                }
                for target in targets
            ],
            "files": [
                {
                    "file_sha256": file.sha256,
                    "fact_directory_sha256": file.fact_directory_sha256,
                    "file_path": file.display_path,
                    "absolute_file_path": str(file.absolute_path),
                    "fact_directory_path": None if file.fact_directory is None else str(file.fact_directory),
                }
                for file in spec.files
            ],
            "cells": [{"backend": cell.backend, "treatment": cell.treatment} for cell in cells],
            "comparisons": [
                {
                    "baseline_target_order": request.baseline_target_order,
                    "baseline_cell_order": request.baseline_cell_order,
                    "candidate_target_order": request.candidate_target_order,
                    "candidate_cell_order": request.candidate_cell_order,
                }
                for request in requests
            ],
            "rounds": spec.rounds,
            "timeout_sec": spec.timeout_sec,
            "t_critical_95": t_critical_95,
        }
        self._connection.execute(
            "INSERT INTO current_report_scope VALUES (TRUE, ?::report_scope_t)",
            [scope],
        )

    def report_view_data(
        self,
        *,
        include_timing: bool,
    ) -> ReportViewData:
        """Query every Python-consumed presentation view for the current scope."""

        self._ensure_open()
        targets = _fetch_rows(
            self._connection.execute("SELECT * FROM presentation_targets ORDER BY target_order"),
            TargetView,
        )
        cell_estimates = _fetch_rows(
            self._connection.execute(
                """
                SELECT * FROM presentation_cell_estimates
                ORDER BY metric_order, target_order, file_order, cell_order
                """
            ),
            CellEstimateView,
        )
        file_ratios = _fetch_rows(
            self._connection.execute(
                """
                SELECT * FROM presentation_file_ratios
                ORDER BY comparison_order, metric_order, file_order
                """
            ),
            FileRatioView,
        )
        comparison_rollups = _fetch_rows(
            self._connection.execute(
                """
                SELECT * FROM presentation_comparison_rollups
                ORDER BY comparison_order, metric_order
                """
            ),
            ComparisonRollupView,
        )
        compact_timings: list[CompactTimingView] = []
        ruleset_timings: list[RulesetTimingView] = []
        if include_timing:
            compact_timings = _fetch_rows(
                self._connection.execute(
                    """
                    SELECT * FROM presentation_compact_timings
                    ORDER BY file_order, cell_order, target_order
                    """
                ),
                CompactTimingView,
            )
            ruleset_timings = _fetch_rows(
                self._connection.execute(
                    """
                    SELECT * FROM presentation_ruleset_timings
                    ORDER BY file_order, cell_order, ruleset_order, target_order
                    """
                ),
                RulesetTimingView,
            )
        return ReportViewData(
            targets=tuple(targets),
            cell_estimates=tuple(cell_estimates),
            file_ratios=tuple(file_ratios),
            comparison_rollups=tuple(comparison_rollups),
            compact_timings=tuple(compact_timings),
            ruleset_timings=tuple(ruleset_timings),
        )

    def _ensure_open(self) -> None:
        if self._closed:
            raise RuntimeError("report database is closed")

    def _incompatible_report_message(self) -> str:
        return (
            f"invalid or incompatible benchmark report {self.path}. "
            "Move or remove this report and recompute the benchmarks."
        )


def _sql_resource(name: str) -> str:
    return resources.files("benchmarking.reports.sql").joinpath(name).read_text(encoding="utf-8")


def _escape_duckdb_glob(path: Path) -> str:
    """Make file-table-function glob metacharacters literal in ``path``."""

    literals = {"*": "[*]", "?": "[?]", "[": "[[]", "]": "[]]"}
    return "".join(literals.get(character, character) for character in str(path))


def _duckdb_string_literal(value: str) -> str:
    """Quote runtime text as a DuckDB literal for catalog DDL."""

    return "'" + value.replace("'", "''") + "'"


def _fetch_rows[RowT](cursor: duckdb.DuckDBPyConnection, row_type: type[RowT]) -> list[RowT]:
    """Construct named rows after checking the SQL/Python column boundary."""

    description = cursor.description
    if description is None:
        raise RuntimeError("DuckDB query did not return columns")
    row_constructor: Any = row_type
    expected_columns = tuple(row_constructor._fields)
    actual_columns = tuple(column[0] for column in description)
    if actual_columns != expected_columns:
        raise RuntimeError(f"DuckDB columns {actual_columns!r} do not match {expected_columns!r}")
    rows: list[RowT] = []
    for values in cursor.fetchall():
        row: RowT = row_constructor(*values)
        rows.append(row)
    return rows
