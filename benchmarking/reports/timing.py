"""Lay out and format engine-timing rows returned by DuckDB report views.

This module maps selected coordinates into compact and detailed tables and
formats durations, shares, and availability messages. SQL views own phase
aggregation, the cross-target ruleset union, absent-ruleset nullability,
ordering, and share calculation. Rich and Markdown syntax, terminal widths,
and styling belong in ``render``.
"""

from __future__ import annotations

import math
from collections.abc import Sequence
from dataclasses import dataclass
from typing import Final

from ..models import BenchmarkSpec, ResolvedTarget, benchmark_cells
from .results import CompactTimingView, RulesetTimingView

NULL: Final = "—"
DEFAULT_RULESET: Final = "<default ruleset>"
TIMING_CAPTION: Final = (
    "Other is wall time minus Search, Apply, Merge, and Rebuild; it includes Unattributed "
    "pre-merge time and time outside recorded rulesets. A leading ! means displayed phase "
    "time exceeds wall time; timing attribution is descriptive."
)


@dataclass(frozen=True)
class CompactTimingRow:
    """One selected target/file/backend/treatment result in the compact view."""

    target: str
    cell: str
    search: str
    apply: str
    merge: str
    rebuild: str
    other: str
    wall: str
    status: str


@dataclass(frozen=True)
class CompactTimingTable:
    """All selected results for one benchmark file."""

    file: str
    rows: tuple[CompactTimingRow, ...]


@dataclass(frozen=True)
class RulesetTimingRow:
    """One formatted ruleset mean in a detailed result table."""

    ruleset: str
    total: str
    share: str
    search: str
    apply: str
    unattributed: str
    merge: str
    rebuild: str


@dataclass(frozen=True)
class DetailedTimingBlock:
    """One target's detailed result within a file/cell comparison group."""

    title: str
    rows: tuple[RulesetTimingRow, ...]
    message: str | None = None


@dataclass(frozen=True)
class TimingReport:
    """Complete compact timing overview plus optional exhaustive detail."""

    compact: tuple[CompactTimingTable, ...]
    detailed: tuple[DetailedTimingBlock, ...]
    caption: str = TIMING_CAPTION


def build_timing_report(
    compact_rows: Sequence[CompactTimingView],
    ruleset_rows: Sequence[RulesetTimingView],
    targets: Sequence[ResolvedTarget],
    spec: BenchmarkSpec,
    *,
    detailed: bool,
    file_labels: Sequence[str] | None = None,
) -> TimingReport:
    """Build timing views in benchmark selector order.

    The rows must come from the output-facing views for one installed scope.
    Missing query rows are nevertheless rendered as invalid results so a UI
    bug cannot silently omit a selected cell.
    """

    labels = tuple(file.display_path for file in spec.files) if file_labels is None else tuple(file_labels)
    if len(labels) != len(spec.files):
        raise ValueError("file_labels must contain one label per selected file")

    compact_by_coordinate = {(row.target_order, row.file_order, row.cell_order): row for row in compact_rows}
    rulesets_by_coordinate: dict[tuple[int, int, int], list[RulesetTimingView]] = {}
    for row in ruleset_rows:
        rulesets_by_coordinate.setdefault((row.target_order, row.file_order, row.cell_order), []).append(row)
    cells = benchmark_cells(spec)
    compact_tables: list[CompactTimingTable] = []
    for file_order, label in enumerate(labels):
        rows: list[CompactTimingRow] = []
        for cell_order, cell in enumerate(cells):
            for target_order, target in enumerate(targets):
                summary = compact_by_coordinate.get((target_order, file_order, cell_order))
                rows.append(_compact_row(target.display_label, f"{cell.backend}/{cell.treatment}", summary))
        compact_tables.append(CompactTimingTable(label, tuple(rows)))

    detail_blocks: list[DetailedTimingBlock] = []
    if detailed:
        for file_order, label in enumerate(labels):
            for cell_order, cell in enumerate(cells):
                for target_order, target in enumerate(targets):
                    key = (target_order, file_order, cell_order)
                    summary = compact_by_coordinate.get(key)
                    title = f"{label} · {cell.backend}/{cell.treatment} · {target.display_label}"
                    detail_blocks.append(_detailed_block(title, summary, rulesets_by_coordinate.get(key, ())))

    return TimingReport(tuple(compact_tables), tuple(detail_blocks))


def format_duration(value_ns: float | None, *, attribution: bool = False) -> str:
    """Format nanoseconds with three significant digits and a local unit."""

    if value_ns is None:
        return NULL
    prefix = "!" if attribution and value_ns < 0 else ""
    magnitude = abs(value_ns)
    if magnitude == 0:
        return "0 ns"
    if magnitude < 1_000:
        scaled, unit = value_ns, "ns"
    elif magnitude < 1_000_000:
        scaled, unit = value_ns / 1_000, "us"
    elif magnitude < 1_000_000_000:
        scaled, unit = value_ns / 1_000_000, "ms"
    else:
        scaled, unit = value_ns / 1_000_000_000, "s"
    return f"{prefix}{_three_significant_digits(scaled)} {unit}"


def format_share(value: float | None) -> str:
    """Format a SQL-derived share without presenting a tiny nonzero value as zero."""

    if value is None:
        return NULL
    percentage = 100 * value
    if 0 < percentage < 0.1:
        return "<0.1%"
    return f"{percentage:.1f}%"


def _compact_row(target: str, cell: str, summary: CompactTimingView | None) -> CompactTimingRow:
    if summary is None:
        return CompactTimingRow(target, cell, NULL, NULL, NULL, NULL, NULL, NULL, "missing result")
    if summary.issue is not None:
        return CompactTimingRow(target, cell, NULL, NULL, NULL, NULL, NULL, NULL, summary.issue)
    return CompactTimingRow(
        target,
        cell,
        format_duration(summary.search_ns),
        format_duration(summary.apply_ns),
        format_duration(summary.merge_ns),
        format_duration(summary.rebuild_ns),
        format_duration(summary.other_ns, attribution=True),
        format_duration(summary.wall_ns),
        "success",
    )


def _detailed_block(
    title: str,
    summary: CompactTimingView | None,
    rulesets: Sequence[RulesetTimingView],
) -> DetailedTimingBlock:
    if summary is None:
        return DetailedTimingBlock(title, (), "Status: missing result")
    if summary.issue is not None:
        return DetailedTimingBlock(title, (), f"Status: {summary.issue}")
    if not rulesets:
        return DetailedTimingBlock(title, (), "No rulesets recorded.")

    rows: list[RulesetTimingRow] = []
    for ruleset in rulesets:
        rows.append(
            RulesetTimingRow(
                DEFAULT_RULESET if ruleset.name == "" else ruleset.name,
                format_duration(ruleset.total_ns),
                format_share(ruleset.ruleset_share),
                format_duration(ruleset.search_ns),
                format_duration(ruleset.apply_ns),
                format_duration(ruleset.unattributed_ns),
                format_duration(ruleset.merge_ns),
                format_duration(ruleset.rebuild_ns),
            )
        )
    return DetailedTimingBlock(title, tuple(rows))


def _three_significant_digits(value: float) -> str:
    magnitude = abs(value)
    if magnitude == 0:
        return "0"
    decimal_places = max(0, 2 - math.floor(math.log10(magnitude)))
    return f"{value:.{decimal_places}f}"
