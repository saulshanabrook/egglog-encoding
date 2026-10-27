"""Define the report wire format and own its append-only cache.

This module owns the trusted ``TypedDict`` schema, standard-library JSON codec,
exact cache key, physical row order, append/index behavior, and cache-selection
queries. Pair statistics and presentation live above this persistence boundary.
"""

from __future__ import annotations

import json
from collections.abc import Mapping, Sequence
from dataclasses import asdict, dataclass
from datetime import datetime
from math import isfinite
from pathlib import Path
from typing import Final, Literal, NotRequired, TypedDict, cast

from native_memory import NATIVE_ALLOCATION_EXIT, NATIVE_LIMIT_BYTES

from ..engines import TREATMENT_SPECS, Engine
from ..models import (
    BenchmarkEndpoint,
    DisequalityEncoding,
    FileSpec,
    Status,
    TargetRow,
    Treatment,
)

type ReportSchemaVersion = Literal[5]
REPORT_SCHEMA_VERSION: Final[ReportSchemaVersion] = 5

type GroupedSchemaVersion = Literal[2]
GROUPED_SCHEMA_VERSION: Final[GroupedSchemaVersion] = 2

type TimingSummarySchemaVersion = Literal[4]
TIMING_SUMMARY_SCHEMA_VERSION: Final[TimingSummarySchemaVersion] = 4


type RulesetTimingRole = Literal["program", "equality"]


class RulesetTimingRecord(TypedDict):
    """Exclusive own-work timing for one named ruleset."""

    name: str
    role: RulesetTimingRole
    assembly_ns: int
    search_ns: int
    apply_ns: int
    execution_ns: int
    merge_ns: int


class TimingSummaryRecord(TypedDict):
    """Versioned engine timing summary embedded in one successful row."""

    schema_version: TimingSummarySchemaVersion
    typecheck_ns: int
    frontend_parse_ns: int
    frontend_other_ns: int
    frontend_install_ns: int
    commands_actions_ns: int
    commands_check_ns: int
    commands_other_ns: int
    native_rebuild_ns: int
    rulesets: list[RulesetTimingRecord]


class ReportRecord(TypedDict):
    """One complete benchmark observation persisted as one JSON line."""

    report_schema_version: ReportSchemaVersion
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
    treatment: Treatment
    disequality_encoding: DisequalityEncoding
    timeout_sec: int
    wall_sec: float | None
    max_rss_bytes: int | None
    error_exit_code: int | None
    error_signal: int | None
    error_message: str | None
    error_memory_limit_bytes: NotRequired[int]  # Configured allowance; inherited address-space limits may be tighter.
    timing_summary: TimingSummaryRecord | None


@dataclass(frozen=True)
class CacheKey:
    """Exact persisted identity used to select reusable observations."""

    binary_sha256: str
    file_sha256: str
    treatment: Treatment
    fact_directory_sha256: str = ""
    disequality_encoding: DisequalityEncoding = "nee"

    @classmethod
    def for_endpoint(
        cls,
        endpoint: BenchmarkEndpoint,
        file_spec: FileSpec,
    ) -> CacheKey:
        """Build the identity shared by collection and reporting."""

        file_spec = file_spec.for_engine(TREATMENT_SPECS[endpoint.treatment].engine)
        return cls(
            binary_sha256=endpoint.target.binary_sha256_for(endpoint.treatment),
            file_sha256=file_spec.sha256,
            treatment=endpoint.treatment,
            disequality_encoding=endpoint.disequality_encoding,
            fact_directory_sha256=file_spec.fact_directory_sha256,
        )


@dataclass(frozen=True)
class CachedTarget:
    """Latest persisted target identity addressed by a user label."""

    row: TargetRow
    binary_sha256: str


@dataclass(frozen=True)
class IndexedRecord:
    """One parsed observation with its persistent append-order identity."""

    row_index: int
    started_at: datetime
    record: ReportRecord

    @property
    def order_key(self) -> tuple[datetime, int]:
        """Return the timestamp-first ordering shared by every cache query."""

        return (self.started_at, self.row_index)


def select_records(
    rows: Sequence[IndexedRecord], rounds: int, timeout_sec: int, memory_limit_bytes: int
) -> tuple[IndexedRecord, ...]:
    """Select newest applicable observations, retaining failures at unchanged bounds.

    Successful completion under an equal/tighter deadline is sufficient even
    when process-launch overhead exceeds that deadline or wall time is absent.
    Only a raised bound retires its resource failure; ordinary errors persist.
    """
    if rounds < 1:
        raise ValueError("rounds must be positive")
    eligible = []
    for row in rows:
        record = row.record
        wall = record["wall_sec"]
        if record["status"] == "success":
            if record["timeout_sec"] > timeout_sec and not (
                wall is not None and isfinite(wall) and 0 < wall <= timeout_sec
            ):
                continue
        elif "process-group cleanup failed:" in (record["error_message"] or ""):
            pass  # A control failure is not repaired by raising a workload limit.
        elif record["status"] == "timed-out":
            if timeout_sec > record["timeout_sec"]:
                continue
        elif record["error_exit_code"] == NATIVE_ALLOCATION_EXIT and TREATMENT_SPECS[record["treatment"]].engine in (
            "egglog",
            "egg",
        ):
            bound = record.get("error_memory_limit_bytes")
            if bound is None or memory_limit_bytes > bound:
                continue
        eligible.append(row)
    return tuple(sorted(eligible, key=lambda row: row.order_key)[-rounds:])


class GroupedKey(TypedDict):
    binary_sha256: str
    file_sha256: str
    treatment: Treatment
    fact_directory_sha256: str
    disequality_encoding: DisequalityEncoding


class GroupedSample(ReportRecord):
    """The full JSONL observation, including disequality encoding, plus its row index."""

    row_index: int


class ObservationGroup(TypedDict):
    key: GroupedKey
    labels: list[str]
    samples: list[GroupedSample]


class GroupedReportRecord(TypedDict):
    """Version the grouping structure separately from its shared ReportRecord samples.

    Grouping-only changes can regenerate this snapshot without invalidating raw observations.
    """

    grouped_schema_version: GroupedSchemaVersion
    report_schema_version: ReportSchemaVersion
    groups: list[ObservationGroup]


class GroupedReport:
    """One complete, immutable-in-use report snapshot shared by all renderers."""

    def __init__(self, data: GroupedReportRecord, display_path: str) -> None:
        self.data = data
        self.display_path = display_path
        self._by_key = {
            CacheKey(**group["key"]): tuple(
                IndexedRecord(sample["row_index"], datetime.fromisoformat(sample["started_at"]), sample)
                for sample in group["samples"]
            )
            for group in data["groups"]
        }
        self.records = tuple(
            row.record
            for row in sorted((row for rows in self._by_key.values() for row in rows), key=lambda row: row.row_index)
        )

    def latest_records(
        self, key: CacheKey, rounds: int, timeout_sec: int, memory_limit_bytes: int = NATIVE_LIMIT_BYTES
    ) -> tuple[IndexedRecord, ...]:
        """Select the requested tail without discarding the snapshot's other samples."""

        return select_records(self._by_key.get(key, ()), rounds, timeout_sec, memory_limit_bytes)


class ReportStore:
    """Load one report snapshot and keep its append/query indexes current."""

    def __init__(self, path: Path) -> None:
        self.path = path
        self._rows: list[IndexedRecord] = []
        self._by_key: dict[CacheKey, list[IndexedRecord]] = {}
        self._by_label: dict[str, list[IndexedRecord]] = {}
        try:
            with self.path.open("rb") as handle:
                for line in handle:
                    self._index(self._indexed(parse_report_record(line)))
        except FileNotFoundError:
            pass
        except (OSError, ValueError, KeyError, TypeError) as error:
            raise ValueError(self._incompatible_report_message()) from error

    @property
    def display_path(self) -> str:
        """Return the path text used in report headings and diagnostics."""

        return str(self.path)

    @property
    def row_count(self) -> int:
        """Return the number of observations in this loaded cache snapshot."""

        return len(self._rows)

    @property
    def records(self) -> tuple[ReportRecord, ...]:
        """Return the loaded observations in fixed physical order."""

        return tuple(row.record for row in self._rows)

    def append(self, record: ReportRecord) -> None:
        """Append one validated observation and update in-process indexes."""

        encoded = serialize_report_record(record)
        indexed = self._indexed(record)
        self.path.parent.mkdir(parents=True, exist_ok=True)
        with self.path.open("ab") as handle:
            handle.write(encoded + b"\n")
        self._index(indexed)

    def grouped_report(self, label_bindings: Mapping[tuple[str, Engine], str] | None = None) -> GroupedReport:
        """Freeze observations and refresh aliases from any targets resolved this invocation.

        Bindings override historical labels without changing sample provenance or
        adding observations when the current binary is already fully cached.
        """

        latest: dict[tuple[str, Engine], IndexedRecord] = {}
        for label, rows in self._by_label.items():
            for row in rows:
                identity = (label, TREATMENT_SPECS[row.record["treatment"]].engine)
                if identity not in latest or row.order_key > latest[identity].order_key:
                    latest[identity] = row
        bindings = {identity: row.record["binary_sha256"] for identity, row in latest.items()}
        if label_bindings is not None:
            bindings.update(label_bindings)
        labels: dict[tuple[Engine, str], list[str]] = {}
        for (label, engine), binary_sha256 in bindings.items():
            labels.setdefault((engine, binary_sha256), []).append(label)
        groups: list[ObservationGroup] = [
            {
                "key": cast(GroupedKey, asdict(key)),
                "labels": sorted(labels.get((TREATMENT_SPECS[key.treatment].engine, key.binary_sha256), ())),
                "samples": [
                    {**row.record, "row_index": row.row_index} for row in sorted(rows, key=lambda row: row.order_key)
                ],
            }
            for key, rows in self._by_key.items()
        ]
        return GroupedReport(
            {
                "grouped_schema_version": GROUPED_SCHEMA_VERSION,
                "report_schema_version": REPORT_SCHEMA_VERSION,
                "groups": groups,
            },
            self.display_path,
        )

    def find_label_pointer(self, label: str, engine: Engine | None = None) -> CachedTarget | None:
        """Return the latest row carrying ``label`` for an optional engine."""

        rows = self._by_label.get(label)
        if not rows:
            return None
        matching = (
            rows
            if engine is None
            else [row for row in rows if TREATMENT_SPECS[row.record["treatment"]].engine == engine]
        )
        if not matching:
            return None
        record = max(matching, key=lambda row: row.order_key).record
        return CachedTarget(
            TargetRow(
                source=record["target_source"],
                path=record["target_path"],
                git_ref=record["target_git_ref"],
                git_sha=record["target_git_sha"],
                is_dirty=record["target_is_dirty"],
                label=label,
            ),
            record["binary_sha256"],
        )

    def selected_statuses_for_keys(
        self,
        keys: Sequence[CacheKey],
        rounds: int,
        timeout_sec: int,
        memory_limit_bytes: int = NATIVE_LIMIT_BYTES,
    ) -> dict[CacheKey, tuple[Status, ...]]:
        """Select latest statuses for every distinct exact cache key."""

        if rounds < 1:
            raise ValueError("rounds must be positive")
        return {
            key: tuple(
                row.record["status"] for row in self.latest_records(key, rounds, timeout_sec, memory_limit_bytes)
            )
            for key in dict.fromkeys(keys)
        }

    def latest_records(
        self, key: CacheKey, rounds: int, timeout_sec: int, memory_limit_bytes: int = NATIVE_LIMIT_BYTES
    ) -> tuple[IndexedRecord, ...]:
        """Return up to ``rounds`` newest rows in chronological presentation order."""

        return select_records(self._by_key.get(key, ()), rounds, timeout_sec, memory_limit_bytes)

    def _indexed(self, record: ReportRecord) -> IndexedRecord:
        return IndexedRecord(
            row_index=len(self._rows),
            started_at=datetime.fromisoformat(record["started_at"]),
            record=record,
        )

    def _index(self, indexed: IndexedRecord) -> None:
        self._rows.append(indexed)
        record = indexed.record
        key = _record_key(record)
        self._by_key.setdefault(key, []).append(indexed)
        label = record["target_label"]
        if label is not None:
            self._by_label.setdefault(label, []).append(indexed)

    def _incompatible_report_message(self) -> str:
        return (
            f"invalid or incompatible benchmark report {self.path}. "
            "Move or remove this report and recompute the benchmarks."
        )


def _record_key(record: ReportRecord) -> CacheKey:
    return CacheKey(
        binary_sha256=record["binary_sha256"],
        file_sha256=record["file_sha256"],
        treatment=record["treatment"],
        disequality_encoding=record["disequality_encoding"],
        fact_directory_sha256=record["fact_directory_sha256"],
    )


def parse_report_record(data: bytes | str) -> ReportRecord:
    """Parse one JSON object and enforce the current trusted-writer contract."""

    record = cast(ReportRecord, json.loads(data))
    _require_current_record(record)
    return record


def parse_timing_summary(data: bytes | str) -> TimingSummaryRecord:
    """Parse one engine timing summary emitted by a benchmark process."""

    summary = cast(TimingSummaryRecord, json.loads(data))
    _require_current_timing_summary(summary)
    return summary


def serialize_report_record(record: ReportRecord) -> bytes:
    """Return the record's validated, newline-free JSON encoding."""

    _require_current_record(record)
    return json.dumps(record, ensure_ascii=False, separators=(",", ":")).encode()


def parse_grouped_report(data: bytes | str, display_path: str) -> GroupedReport:
    """Read the versioned trusted-writer snapshot without touching its source cache."""

    record = cast(GroupedReportRecord, json.loads(data))
    _require_current_grouped_report(record)
    return GroupedReport(record, display_path)


def serialize_grouped_report(report: GroupedReport) -> bytes:
    """Encode the shared typed snapshot deterministically for files and HTML."""

    _require_current_grouped_report(report.data)
    return json.dumps(report.data, ensure_ascii=False, separators=(",", ":")).encode() + b"\n"


def _require_current_grouped_report(record: GroupedReportRecord) -> None:
    if record["grouped_schema_version"] != GROUPED_SCHEMA_VERSION:
        raise ValueError(f"unsupported grouped report schema version {record['grouped_schema_version']!r}")
    if record["report_schema_version"] != REPORT_SCHEMA_VERSION:
        raise ValueError(f"unsupported report schema version {record['report_schema_version']!r}")
    for group in record["groups"]:
        for sample in group["samples"]:
            _require_current_record(sample)


def _require_current_record(record: ReportRecord) -> None:
    """Reject old report data and keep successful rows self-contained."""

    if record["report_schema_version"] != REPORT_SCHEMA_VERSION:
        raise ValueError(f"unsupported report schema version {record['report_schema_version']!r}")

    summary = record["timing_summary"]
    if summary is not None:
        _require_current_timing_summary(summary)
    if record["status"] == "success" and summary is None and TREATMENT_SPECS[record["treatment"]].timing_summary:
        raise ValueError("successful benchmark record is missing its timing summary")


def _require_current_timing_summary(summary: TimingSummaryRecord) -> None:
    """Reject timing summaries from an incompatible disposable cache format."""

    if summary["schema_version"] != TIMING_SUMMARY_SCHEMA_VERSION:
        raise ValueError(f"unsupported timing summary schema_version {summary['schema_version']!r}")
