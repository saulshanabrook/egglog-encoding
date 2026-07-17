"""Define and encode the trusted JSONL shapes written by the benchmark runner.

The three ``TypedDict`` definitions are the sole persisted schema. The standard
library JSON codec reads and writes whole observations; cache indexing lives in
:mod:`benchmarking.reports.store`, while derived immutable rows live with their
computations in :mod:`benchmarking.reports.analysis`.
"""

from __future__ import annotations

import json
from typing import Final, Literal, TypedDict, cast

from ..models import Backend, Status, Treatment

type TimingSummarySchemaVersion = Literal[2]
TIMING_SUMMARY_SCHEMA_VERSION: Final[TimingSummarySchemaVersion] = 2


class RulesetTimingRecord(TypedDict):
    """Persisted engine time for one ruleset."""

    name: str
    search_ns: int
    apply_ns: int
    unattributed_ns: int
    merge_ns: int
    rebuild_ns: int


class TimingSummaryRecord(TypedDict):
    """Versioned engine timing summary embedded in one successful row."""

    schema_version: TimingSummarySchemaVersion
    rulesets: list[RulesetTimingRecord]


class ReportRecord(TypedDict):
    """One complete benchmark observation persisted as one JSON line."""

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


def parse_report_record(data: bytes | str) -> ReportRecord:
    """Parse one JSON object and enforce the current trusted-writer contract."""

    record = cast(ReportRecord, json.loads(data))
    _require_current_timing(record)
    return record


def serialize_report_record(record: ReportRecord) -> tuple[ReportRecord, bytes]:
    """Return a record and its newline-free JSON encoding."""

    _require_current_timing(record)
    return record, json.dumps(record, ensure_ascii=False, separators=(",", ":")).encode()


def _require_current_timing(record: ReportRecord) -> None:
    """Reject old timing data and keep successful rows self-contained."""

    summary = record["timing_summary"]
    if summary is not None and summary["schema_version"] != TIMING_SUMMARY_SCHEMA_VERSION:
        raise ValueError(f"unsupported timing summary schema_version {summary['schema_version']!r}")
    if record["status"] == "success" and summary is None:
        raise ValueError("successful benchmark record is missing its timing summary")
