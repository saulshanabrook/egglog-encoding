"""Build renderer-neutral engine-timing tables from DuckDB report relations.

This module maps selected coordinates into generic catalog blocks and formats
durations, shares, and availability messages. SQL views own phase aggregation,
the cross-target ruleset union, absent-ruleset nullability, ordering, and share
calculation. Rich/Markdown syntax and terminal widths belong in ``render``.
"""

from __future__ import annotations

import math
from collections.abc import Sequence
from typing import Final

from ..models import BenchmarkCell, BenchmarkSpec, FileSpec, ResolvedTarget, benchmark_cells
from .catalog import (
    ReportBlock,
    ReportColumn,
    ReportMessage,
    ReportRow,
    ReportSection,
    ReportTable,
    report_id,
    text_cell,
)
from .results import CompactTimingView, RulesetTimingView

NULL: Final = "—"
DEFAULT_RULESET: Final = "<default ruleset>"
TIMING_CAPTION: Final = (
    "Other is wall time minus Search, Apply, Merge, and Rebuild; it includes Unattributed "
    "pre-merge time and time outside recorded rulesets. A leading ! means displayed phase "
    "time exceeds wall time; timing attribution is descriptive."
)


def build_timing_sections(
    compact_rows: Sequence[CompactTimingView],
    ruleset_rows: Sequence[RulesetTimingView],
    targets: Sequence[ResolvedTarget],
    spec: BenchmarkSpec,
    *,
    detailed: bool,
    file_labels: Sequence[str] | None = None,
) -> tuple[ReportSection, ...]:
    """Build timing sections in benchmark selector order from one installed scope."""

    labels = tuple(file.display_path for file in spec.files) if file_labels is None else tuple(file_labels)
    if len(labels) != len(spec.files):
        raise ValueError("file_labels must contain one label per selected file")

    compact_by_coordinate = {(row.target_order, row.file_order, row.cell_order): row for row in compact_rows}
    rulesets_by_coordinate: dict[tuple[int, int, int], list[RulesetTimingView]] = {}
    for row in ruleset_rows:
        rulesets_by_coordinate.setdefault((row.target_order, row.file_order, row.cell_order), []).append(row)

    cells = benchmark_cells(spec)
    compact_tables = tuple(
        _compact_table(
            file_spec,
            labels[file_order],
            file_order,
            cells,
            targets,
            compact_by_coordinate,
        )
        for file_order, file_spec in enumerate(spec.files)
    )
    timing_blocks: tuple[ReportBlock, ...] = (
        *compact_tables,
        ReportMessage(
            report_id("timing", "caption"),
            None,
            TIMING_CAPTION,
            tone="muted",
            layout="caption",
        ),
    )
    sections = [ReportSection("timing", "Engine Timing", timing_blocks)]

    if detailed:
        detail_blocks: list[ReportBlock] = []
        for file_order, file_spec in enumerate(spec.files):
            for cell_order, cell in enumerate(cells):
                for target_order, target in enumerate(targets):
                    key = (target_order, file_order, cell_order)
                    title = f"{labels[file_order]} · {cell.backend}/{cell.treatment} · {target.display_label}"
                    detail_blocks.append(
                        _detailed_block(
                            target,
                            file_spec,
                            cell,
                            title,
                            compact_by_coordinate.get(key),
                            rulesets_by_coordinate.get(key, ()),
                        )
                    )
        sections.append(ReportSection("detailed-timing", "Detailed Timing", tuple(detail_blocks)))

    return tuple(sections)


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


def _compact_table(
    file_spec: FileSpec,
    label: str,
    file_order: int,
    cells: Sequence[BenchmarkCell],
    targets: Sequence[ResolvedTarget],
    compact_by_coordinate: dict[tuple[int, int, int], CompactTimingView],
) -> ReportTable:
    rows = tuple(
        _compact_row(
            target,
            file_spec,
            cell,
            compact_by_coordinate.get((target_order, file_order, cell_order)),
        )
        for cell_order, cell in enumerate(cells)
        for target_order, target in enumerate(targets)
    )
    return ReportTable(
        report_id("timing", "compact", file_spec.sha256, file_spec.fact_directory_sha256),
        label,
        (
            ReportColumn("target", "Target"),
            ReportColumn("cell", "Backend/Treatment"),
            ReportColumn("search_ns", "Search", "right"),
            ReportColumn("apply_ns", "Apply", "right"),
            ReportColumn("merge_ns", "Merge", "right"),
            ReportColumn("rebuild_ns", "Rebuild", "right"),
            ReportColumn("other_ns", "Other", "right"),
            ReportColumn("wall_ns", "Wall", "right"),
            ReportColumn("status", "Status"),
        ),
        rows,
        layout="wide",
    )


def _compact_row(
    target: ResolvedTarget,
    file_spec: FileSpec,
    cell: BenchmarkCell,
    summary: CompactTimingView | None,
) -> ReportRow:
    row_id = report_id(
        "timing",
        "compact-row",
        target.binary_sha256,
        file_spec.sha256,
        file_spec.fact_directory_sha256,
        cell.backend,
        cell.treatment,
    )
    identity = (text_cell(target.display_label), text_cell(f"{cell.backend}/{cell.treatment}"))
    if summary is None:
        return ReportRow(row_id, (*identity, *(_missing_duration_cells()), text_cell("missing result")))
    if summary.issue is not None:
        return ReportRow(row_id, (*identity, *(_missing_duration_cells()), text_cell(summary.issue)))
    return ReportRow(
        row_id,
        (
            *identity,
            text_cell(summary.search_ns, format_duration(summary.search_ns)),
            text_cell(summary.apply_ns, format_duration(summary.apply_ns)),
            text_cell(summary.merge_ns, format_duration(summary.merge_ns)),
            text_cell(summary.rebuild_ns, format_duration(summary.rebuild_ns)),
            text_cell(summary.other_ns, format_duration(summary.other_ns, attribution=True)),
            text_cell(summary.wall_ns, format_duration(summary.wall_ns)),
            text_cell("success"),
        ),
    )


def _missing_duration_cells() -> tuple:
    return tuple(text_cell(None, NULL) for _ in range(6))


def _detailed_block(
    target: ResolvedTarget,
    file_spec: FileSpec,
    cell: BenchmarkCell,
    title: str,
    summary: CompactTimingView | None,
    rulesets: Sequence[RulesetTimingView],
) -> ReportBlock:
    block_id = report_id(
        "timing",
        "rulesets",
        target.binary_sha256,
        file_spec.sha256,
        file_spec.fact_directory_sha256,
        cell.backend,
        cell.treatment,
    )
    if summary is None:
        return ReportMessage(block_id, title, "Status: missing result")
    if summary.issue is not None:
        return ReportMessage(block_id, title, f"Status: {summary.issue}")
    if not rulesets:
        return ReportMessage(block_id, title, "No rulesets recorded.")

    rows = tuple(
        ReportRow(
            report_id(block_id, "ruleset", ruleset.name),
            (
                text_cell(ruleset.name, DEFAULT_RULESET if ruleset.name == "" else ruleset.name),
                text_cell(ruleset.total_ns, format_duration(ruleset.total_ns)),
                text_cell(ruleset.ruleset_share, format_share(ruleset.ruleset_share)),
                text_cell(ruleset.search_ns, format_duration(ruleset.search_ns)),
                text_cell(ruleset.apply_ns, format_duration(ruleset.apply_ns)),
                text_cell(ruleset.unattributed_ns, format_duration(ruleset.unattributed_ns)),
                text_cell(ruleset.merge_ns, format_duration(ruleset.merge_ns)),
                text_cell(ruleset.rebuild_ns, format_duration(ruleset.rebuild_ns)),
            ),
        )
        for ruleset in rulesets
    )
    return ReportTable(
        block_id,
        title,
        (
            ReportColumn("ruleset", "Ruleset"),
            ReportColumn("total_ns", "Total", "right"),
            ReportColumn("share", "Share", "right"),
            ReportColumn("search_ns", "Search", "right"),
            ReportColumn("apply_ns", "Apply", "right"),
            ReportColumn("unattributed_ns", "Unattributed", "right"),
            ReportColumn("merge_ns", "Merge", "right"),
            ReportColumn("rebuild_ns", "Rebuild", "right"),
        ),
        rows,
        layout="wide",
    )


def _three_significant_digits(value: float) -> str:
    magnitude = abs(value)
    if magnitude == 0:
        return "0"
    decimal_places = max(0, 2 - math.floor(math.log10(magnitude)))
    return f"{value:.{decimal_places}f}"
