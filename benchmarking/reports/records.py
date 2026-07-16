"""Define the trusted JSONL record shapes written by the benchmark runner.

The three persisted ``TypedDict`` shapes below mirror the same-named SQL types
in ``reports/sql/schema.sql``. DuckDB access belongs in
:mod:`benchmarking.reports.database`; derived immutable query results belong in
:mod:`benchmarking.reports.results`.
"""

from __future__ import annotations

from typing import Final, Literal, TypedDict

from ..models import Backend, Status, Treatment

TIMING_SUMMARY_SCHEMA_VERSION: Final = 2


class RulesetTimingRecord(TypedDict):
    """Persisted engine time; mirrors SQL ``ruleset_timing_record_t``."""

    name: str
    search_ns: int
    apply_ns: int
    unattributed_ns: int
    merge_ns: int
    rebuild_ns: int


class TimingSummaryRecord(TypedDict):
    """Engine timing summary; mirrors SQL ``timing_summary_record_t``."""

    schema_version: Literal[2]
    rulesets: list[RulesetTimingRecord]


class ReportRecord(TypedDict):
    """One benchmark observation; mirrors SQL ``report_record_t``."""

    started_at: str
    status: Status
    target_label: str | None
    target_source: str
    target_path: str
    target_git_ref: str
    target_git_sha: str
    target_is_dirty: bool
    binary_sha256: str
    file_path: str
    file_sha256: str
    fact_directory_path: str | None
    fact_directory_sha256: str
    backend: Backend
    treatment: Treatment
    timeout_sec: int
    wall_sec: float | None
    max_rss_bytes: int | None
    error_exit_code: int | None
    error_signal: int | None
    error_message: str | None
    timing_summary: TimingSummaryRecord | None
