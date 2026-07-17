"""Own append-only JSONL persistence and exact benchmark-cache selection.

``ReportStore`` loads the disposable report once, preserves physical row order,
indexes exact cache keys and labels, appends observations written by this tool,
and answers collection/live-discovery queries. Pair statistics and presentation
rows belong in :mod:`benchmarking.reports.analysis`.
"""

from __future__ import annotations

import math
from collections.abc import Sequence
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path

from ..models import (
    Backend,
    EstimateKey,
    FileSpec,
    Status,
    TargetRow,
    Treatment,
    validate_unique_file_identities,
)
from .records import ReportRecord, parse_report_record, serialize_report_record


@dataclass(frozen=True)
class CachedTarget:
    """Latest persisted target identity addressed by a user label."""

    row: TargetRow
    binary_sha256: str


@dataclass(frozen=True)
class CachedEndpoint:
    """One row-complete cached endpoint available to the live report."""

    row: TargetRow
    binary_sha256: str
    backend: Backend
    treatment: Treatment

    @property
    def cache_identity(self) -> tuple[str, Backend, Treatment]:
        """Return the report-key dimensions shared by every endpoint file."""

        return (self.binary_sha256, self.backend, self.treatment)


@dataclass(frozen=True)
class EstimateAggregate:
    """Historical successful wall-time count and sum for one exact cache key."""

    key: EstimateKey
    sample_count: int
    total_wall_sec: float


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


class ReportStore:
    """Load one report snapshot and keep its append/query indexes current."""

    def __init__(self, path: Path) -> None:
        self.path = path
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self.path.touch(exist_ok=True)
        self._rows: list[IndexedRecord] = []
        self._by_key: dict[EstimateKey, list[IndexedRecord]] = {}
        self._by_label: dict[str, list[IndexedRecord]] = {}
        try:
            with self.path.open("rb") as handle:
                for line in handle:
                    self._add(parse_report_record(line))
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

    def append(self, record: ReportRecord) -> None:
        """Append one validated observation and update in-process indexes."""

        normalized, encoded = serialize_report_record(record)
        indexed = self._indexed(normalized)
        with self.path.open("ab") as handle:
            handle.write(encoded + b"\n")
        self._index(indexed)

    def find_label_pointer(self, label: str) -> CachedTarget | None:
        """Return the latest row carrying ``label``, or ``None``."""

        rows = self._by_label.get(label)
        if not rows:
            return None
        record = max(rows, key=lambda row: row.order_key).record
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

    def selected_statuses(self, key: EstimateKey, rounds: int) -> tuple[Status, ...]:
        """Select statuses from the latest rounds for one exact cache key."""

        return tuple(row.record["status"] for row in self.latest_records(key, rounds))

    def selected_statuses_for_keys(
        self,
        keys: Sequence[EstimateKey],
        rounds: int,
    ) -> dict[EstimateKey, tuple[Status, ...]]:
        """Select latest statuses for every distinct exact cache key."""

        if rounds < 1:
            raise ValueError("rounds must be positive")
        return {
            key: tuple(row.record["status"] for row in self.latest_records(key, rounds)) for key in dict.fromkeys(keys)
        }

    def latest_records(self, key: EstimateKey, rounds: int) -> tuple[IndexedRecord, ...]:
        """Return up to ``rounds`` newest rows in chronological presentation order."""

        if rounds < 1:
            raise ValueError("rounds must be positive")
        ordered = sorted(self._by_key.get(key, ()), key=lambda row: row.order_key)
        return tuple(ordered[-rounds:])

    def successful_estimate_aggregates(self) -> tuple[EstimateAggregate, ...]:
        """Return historical successful wall totals for ETA modeling."""

        aggregates: list[EstimateAggregate] = []
        for key in sorted(self._by_key, key=_estimate_key_order):
            values = [
                row.record["wall_sec"]
                for row in self._by_key[key]
                if row.record["status"] == "success" and row.record["wall_sec"] is not None
            ]
            if values:
                aggregates.append(EstimateAggregate(key, len(values), math.fsum(values)))
        return tuple(aggregates)

    def complete_cached_endpoints(
        self,
        files: Sequence[FileSpec],
        rounds: int,
        timeout_sec: int,
    ) -> tuple[CachedEndpoint, ...]:
        """Return endpoints with enough latest rows for every requested file."""

        if not files:
            raise ValueError("cached endpoint discovery requires at least one file")
        validate_unique_file_identities(files)
        if rounds < 1:
            raise ValueError("rounds must be positive")
        if timeout_sec < 1:
            raise ValueError("timeout must be positive")

        requested = tuple((file.sha256, file.fact_directory_sha256) for file in files)
        requested_set = set(requested)
        candidates = {
            (key.binary_sha256, key.backend, key.treatment)
            for key in self._by_key
            if key.timeout_sec == timeout_sec and (key.file_sha256, key.fact_directory_sha256) in requested_set
        }
        complete: list[CachedEndpoint] = []
        for binary_sha256, backend, treatment in candidates:
            selected: list[IndexedRecord] = []
            for file_sha256, fact_directory_sha256 in requested:
                key = EstimateKey(
                    binary_sha256=binary_sha256,
                    file_sha256=file_sha256,
                    treatment=treatment,
                    timeout_sec=timeout_sec,
                    backend=backend,
                    fact_directory_sha256=fact_directory_sha256,
                )
                rows = self.latest_records(key, rounds)
                if len(rows) != rounds:
                    break
                selected.extend(rows)
            else:
                newest = max(selected, key=lambda row: row.order_key).record
                complete.append(
                    CachedEndpoint(
                        TargetRow(
                            source=newest["target_source"],
                            path=newest["target_path"],
                            git_ref=newest["target_git_ref"],
                            git_sha=newest["target_git_sha"],
                            is_dirty=newest["target_is_dirty"],
                            label=newest["target_label"],
                        ),
                        binary_sha256,
                        backend,
                        treatment,
                    )
                )
        return tuple(sorted(complete, key=_cached_endpoint_order))

    def _add(self, record: ReportRecord) -> None:
        self._index(self._indexed(record))

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


def _record_key(record: ReportRecord) -> EstimateKey:
    return EstimateKey(
        binary_sha256=record["binary_sha256"],
        file_sha256=record["file_sha256"],
        treatment=record["treatment"],
        timeout_sec=record["timeout_sec"],
        backend=record["backend"],
        fact_directory_sha256=record["fact_directory_sha256"],
    )


def _estimate_key_order(key: EstimateKey) -> tuple[str, str, str, Backend, Treatment, int]:
    return (
        key.binary_sha256,
        key.file_sha256,
        key.fact_directory_sha256,
        key.backend,
        key.treatment,
        key.timeout_sec,
    )


def _cached_endpoint_order(endpoint: CachedEndpoint) -> tuple[str, Backend, Treatment, str]:
    row = endpoint.row
    label = row.label if row.label is not None else row.git_ref
    return (label, endpoint.backend, endpoint.treatment, endpoint.binary_sha256)
