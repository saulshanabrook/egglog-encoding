"""Render ordinary and engine-timing report models as Rich or Markdown.

This module owns terminal-width warnings, wrapping, styling, escaping, headings,
and tables; persistence, calculations, and report policy belong elsewhere.
"""

from __future__ import annotations

import shlex
from collections.abc import Sequence
from typing import TYPE_CHECKING

from rich import box
from rich.console import Group, RenderableType
from rich.rule import Rule
from rich.table import Table
from rich.text import Text
from rich.tree import Tree

from .results import ReportTableData
from .timing import CompactTimingRow, DetailedTimingBlock, TimingReport

if TYPE_CHECKING:
    from .summary import ReportDocument

RICH_TIMING_MIN_WIDTH = 120
RICH_TIMING_NARROW_WARNING = (
    "Warning: Rich timing output is designed for terminals at least 120 columns wide "
    "(detected {width}); output may wrap. Widen the terminal or use --format markdown."
)

RESULT_STYLES = {
    "descriptive": "dim",
    "established": "green",
    "faster": "green",
    "invalid": "bold red",
    "less": "green",
    "more": "red",
    "not established": "red",
    "point only": "dim",
    "slower": "red",
    "unclear": "yellow",
}


def styled_status(status: str, text: str | None = None) -> Text:
    return Text(text or status, style=RESULT_STYLES.get(status, ""))


def report_table(title: str, *, caption: str | None = None, show_lines: bool = False) -> Table:
    return Table(
        title=Text(title, style="bold"),
        caption=None if caption is None else Text(caption, style="dim"),
        caption_justify="left",
        header_style="bold",
        box=box.SIMPLE_HEAVY,
        show_lines=show_lines,
    )


def rich_result_cell(value: str) -> Text:
    if value.startswith("invalid:"):
        return styled_status("invalid", value)
    if value == "<2x established":
        return styled_status("established", value)
    if value == "<2x not established":
        return styled_status("not established", value)
    if value in RESULT_STYLES:
        return styled_status(value)
    return Text(value)


def render_rich_table(table_data: ReportTableData) -> Table:
    table = report_table(table_data.title, caption=table_data.caption)
    alignments = table_data.alignments or tuple("left" for _ in table_data.headers)
    for header, alignment in zip(table_data.headers, alignments, strict=True):
        table.add_column(
            Text(header), no_wrap=alignment == "right", justify="right" if alignment == "right" else "left"
        )
    result_columns = {"Result", "Best result"}
    for row in table_data.rows:
        values: list[Text] = []
        for header, value in zip(table_data.headers, row, strict=True):
            values.append(rich_result_cell(value) if header in result_columns else Text(value))
        table.add_row(*values)
    return table


def markdown_escape_cell(value: object) -> str:
    text = str(value)
    return text.replace("\\", "\\\\").replace("|", "\\|").replace("\r\n", "\n").replace("\n", "<br>")


def render_markdown_table(table_data: ReportTableData, *, heading_level: int = 3) -> str:
    alignments = table_data.alignments or tuple("left" for _ in table_data.headers)
    separator_cells = tuple("---:" if alignment == "right" else "---" for alignment in alignments)
    lines = [
        f"{'#' * heading_level} {table_data.title}",
        "",
        "| " + " | ".join(markdown_escape_cell(header) for header in table_data.headers) + " |",
        "| " + " | ".join(separator_cells) + " |",
    ]
    for row in table_data.rows:
        lines.append("| " + " | ".join(markdown_escape_cell(value) for value in row) + " |")
    if table_data.caption:
        lines.extend(["", f"*{markdown_escape_cell(table_data.caption)}*"])
    return "\n".join(lines)


def benchmark_command_block(argv: Sequence[str]) -> str:
    return "```shell\n$ " + shlex.join(["./bench.py", *argv]) + "\n```"


def render_rich_report_document(document: ReportDocument, width: int) -> Group:
    """Render all Rich report sections in their decision-oriented order."""

    renderables: list[RenderableType] = [
        Rule("[bold]Benchmark report[/bold]"),
        Text.assemble("Report: ", (document.report_path, "bold")),
        Text.assemble("Selected rows per result: ", (str(document.rounds), "bold")),
        _render_targets_tree(document),
    ]
    renderables.extend(render_rich_table(table) for table in document.comparisons)
    renderables.extend(render_rich_table(table) for table in document.diagnostics)
    if document.timing is not None:
        renderables.append(render_rich_timing(document.timing, width))
    renderables.append(Rule("[bold]Benchmark summary[/bold]"))
    renderables.extend(render_rich_table(table) for table in document.summary)
    return Group(*renderables)


def render_markdown_report_document(document: ReportDocument) -> str:
    """Render all Markdown report sections from the same renderer-neutral data."""

    parts: list[str] = []
    if document.command_argv is not None:
        parts.append(benchmark_command_block(document.command_argv))
    parts.extend(
        (
            "# Benchmark Report",
            f"- Report: `{document.report_path}`\n- Selected rows per result: `{document.rounds}`",
            render_markdown_table(document.targets_table, heading_level=2),
        )
    )
    if document.comparisons:
        parts.append("## Comparisons")
        parts.extend(render_markdown_table(table) for table in document.comparisons)
    if document.diagnostics:
        parts.append("## Target Diagnostics")
        parts.extend(render_markdown_table(table) for table in document.diagnostics)
    if document.timing is not None:
        parts.append(render_markdown_timing(document.timing))
    parts.append("## Benchmark Summary")
    parts.extend(render_markdown_table(table) for table in document.summary)
    return "\n\n".join(part.strip() for part in parts if part.strip())


def _render_targets_tree(document: ReportDocument) -> Tree:
    tree = Tree(Text("Targets", style="bold"), guide_style="dim")
    for target in document.targets:
        dirty = "dirty" if target.target_is_dirty else "clean"
        binary = target.binary_sha256.removeprefix("sha256:")[:12]
        branch = tree.add(Text.assemble((target.target_role, "bold"), " ", target.target_label))
        branch.add(Text.assemble("source: ", target.target_source))
        branch.add(Text.assemble("git: ", target.target_git_sha[:12], f" ({dirty})"))
        if target.target_git_ref != "HEAD":
            branch.add(Text.assemble("ref: ", target.target_git_ref))
        branch.add(Text.assemble("binary: ", binary))
        branch.add(Text.assemble("path: ", target.target_path))
    return tree


def render_rich_timing(report: TimingReport, width: int) -> Group:
    """Render the canonical timing tables, with one warning below 120 columns."""

    renderables: list[RenderableType] = []
    if width < RICH_TIMING_MIN_WIDTH:
        renderables.append(Text(RICH_TIMING_NARROW_WARNING.format(width=width), style="yellow"))
    renderables.append(Text("Engine timing", style="bold", justify="center"))
    renderables.extend(_rich_compact_timing_table(table.file, table.rows) for table in report.compact)
    renderables.append(Text(report.caption, style="dim"))
    if report.detailed:
        renderables.append(Text("Detailed timing", style="bold", justify="center"))
        for block in report.detailed:
            if block.message is not None:
                renderables.append(Text(block.title, style="bold"))
                renderables.append(Text(block.message, style="dim"))
            else:
                renderables.append(_rich_detailed_timing_table(block))
    return Group(*renderables)


def render_markdown_timing(report: TimingReport) -> str:
    """Render complete timing names and values independently of terminal width."""

    lines = ["## Engine Timing"]
    for table in report.compact:
        lines.extend(
            [
                "",
                f"### {_markdown_heading(table.file)}",
                "",
                *_markdown_table_lines(
                    ("Target", "Backend/Treatment", "Search", "Apply", "Merge", "Rebuild", "Other", "Wall", "Status"),
                    tuple(
                        (
                            row.target,
                            row.cell,
                            row.search,
                            row.apply,
                            row.merge,
                            row.rebuild,
                            row.other,
                            row.wall,
                            row.status,
                        )
                        for row in table.rows
                    ),
                    right_aligned=frozenset({"Search", "Apply", "Merge", "Rebuild", "Other", "Wall"}),
                ),
            ]
        )
    lines.extend(["", f"*{markdown_escape_cell(report.caption)}*"])
    if report.detailed:
        lines.extend(["", "## Detailed Timing"])
        for block in report.detailed:
            lines.extend(["", f"### {_markdown_heading(block.title)}", ""])
            if block.message is not None:
                lines.append(markdown_escape_cell(block.message))
            else:
                lines.extend(
                    _markdown_table_lines(
                        ("Ruleset", "Total", "Share", "Search", "Apply", "Merge", "Rebuild"),
                        tuple(
                            (row.ruleset, row.total, row.share, row.search, row.apply, row.merge, row.rebuild)
                            for row in block.rows
                        ),
                        right_aligned=frozenset({"Total", "Share", "Search", "Apply", "Merge", "Rebuild"}),
                    )
                )
    return "\n".join(lines)


def _rich_compact_timing_table(file: str, rows: Sequence[CompactTimingRow]) -> Table:
    table = Table(
        title=Text(file, style="bold"),
        header_style="bold",
        box=box.SIMPLE_HEAVY,
        expand=True,
        collapse_padding=True,
        padding=(0, 1),
    )
    table.add_column("Target", overflow="fold")
    table.add_column("Backend/Treatment", overflow="fold")
    for header in ("Search", "Apply", "Merge", "Rebuild", "Other", "Wall"):
        table.add_column(header, justify="right", no_wrap=True)
    table.add_column("Status", overflow="fold")
    for value in rows:
        table.add_row(
            Text(value.target),
            Text(value.cell),
            Text(value.search),
            Text(value.apply),
            Text(value.merge),
            Text(value.rebuild),
            Text(value.other),
            Text(value.wall),
            Text(value.status),
        )
    return table


def _rich_detailed_timing_table(block: DetailedTimingBlock) -> Table:
    table = Table(
        title=Text(block.title, style="bold"),
        header_style="bold",
        box=box.SIMPLE_HEAVY,
        expand=True,
        collapse_padding=True,
        padding=(0, 1),
    )
    table.add_column("Ruleset", overflow="fold")
    for header in ("Total", "Share", "Search", "Apply", "Merge", "Rebuild"):
        table.add_column(header, justify="right", no_wrap=True)
    for row in block.rows:
        table.add_row(
            Text(row.ruleset),
            Text(row.total),
            Text(row.share),
            Text(row.search),
            Text(row.apply),
            Text(row.merge),
            Text(row.rebuild),
        )
    return table


def _markdown_table_lines(
    headers: tuple[str, ...],
    rows: tuple[tuple[str, ...], ...],
    *,
    right_aligned: frozenset[str],
) -> list[str]:
    lines = [
        "| " + " | ".join(markdown_escape_cell(header) for header in headers) + " |",
        "| " + " | ".join("---:" if header in right_aligned else "---" for header in headers) + " |",
    ]
    lines.extend("| " + " | ".join(markdown_escape_cell(value) for value in row) + " |" for row in rows)
    return lines


def _markdown_heading(value: str) -> str:
    return value.replace("\n", " ").replace("#", "\\#")
