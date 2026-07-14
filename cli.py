"""Terminal rendering of benchmark reports with Rich.

Renders the shared ``ReportTable`` catalog from ``tables.py`` to the console:
grouped per target (to match the historical layout) and styling result cells by
status. All numbers, formatting, and table structure come from ``tables.py``.
"""

from __future__ import annotations

from collections.abc import Sequence

from pandera.typing import DataFrame
from rich import box
from rich.console import Console
from rich.markup import escape
from rich.table import Table
from rich.text import Text
from rich.tree import Tree

from models import BenchmarkSpec, ReportDestination, ResolvedTarget
from report import Cell, Column, ReportTable, build_report_tables
from report_frame import ReportFrame

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


def result_style(status: str) -> str:
    return RESULT_STYLES.get(status, "")


def styled_status(status: str, text: str | None = None) -> Text:
    return Text(text or status, style=result_style(status))


def report_table(title: str, *, caption: str | None = None, show_lines: bool = False) -> Table:
    return Table(
        title=title,
        title_style="bold",
        caption=caption,
        caption_style="dim",
        caption_justify="left",
        header_style="bold",
        box=box.SIMPLE_HEAVY,
        show_lines=show_lines,
    )


def render_report(
    console: Console,
    report_destination: ReportDestination,
    rows: DataFrame[ReportFrame],
    targets: Sequence[ResolvedTarget],
    spec: BenchmarkSpec,
) -> None:
    console.rule("[bold]Benchmark report[/bold]")
    console.print(f"Report: [bold]{escape(report_destination.display_path)}[/bold]")
    console.print(f"Selected rows per cell: [bold]{spec.rounds}[/bold]")

    render_targets_tree(console, targets)

    sections: dict[str, list[ReportTable]] = {"change": [], "diagnostic": [], "summary": []}
    for table in build_report_tables(rows, targets, spec):
        sections[table.cli_section].append(table)

    for table in sections["change"]:
        render_report_table(console, table)
    # Diagnostics are interleaved per target (overhead, means, RSS for each).
    for target in targets:
        for table in sections["diagnostic"]:
            render_report_table(console, table, only_group=target.binary_sha256)

    console.rule("[bold]Benchmark summary[/bold]")
    for table in sections["summary"]:
        render_report_table(console, table)


def render_report_table(console: Console, table: ReportTable, *, only_group: str | None = None) -> None:
    """Render a table to the console. Grouped tables split into one Rich table per
    ``group_keys`` identity (so same-labeled targets stay separate); the title uses
    the display label from the ``group_by`` column."""
    group_by = table.group_by
    if group_by is None:
        _render_group(console, table, table.cli_title(None), table.columns, list(table.rows))
        return
    order: list[str] = []
    buckets: dict[str, list[dict[str, Cell]]] = {}
    for identity, row in zip(table.group_keys, table.rows, strict=True):
        if identity not in buckets:
            buckets[identity] = []
            order.append(identity)
        buckets[identity].append(row)
    columns = tuple(column for column in table.columns if column.label != group_by)
    for identity in order:
        if only_group is not None and identity != only_group:
            continue
        rows = buckets[identity]
        _render_group(console, table, table.cli_title(rows[0][group_by].text), columns, rows)


def _render_group(
    console: Console,
    table: ReportTable,
    title: str,
    columns: Sequence[Column],
    rows: list[dict[str, Cell]],
) -> None:
    if not rows:
        return
    columns = [
        column for column in columns if not (column.drop_if_empty and all(not row[column.label].text for row in rows))
    ]
    rich_table = report_table(title, caption=table.caption)
    for column in columns:
        rich_table.add_column(column.label, no_wrap=column.numeric, justify="right" if column.numeric else "left")
    for index, row in enumerate(rows):
        cells: list[str | Text] = []
        for column in columns:
            cell = row[column.label]
            text = cell.text
            if table.merge == column.label and index > 0 and rows[index - 1][column.label].text == text:
                text = ""
            cells.append(styled_status(cell.status, text) if cell.status is not None else text)
        rich_table.add_row(*cells)
    console.print(rich_table)


def render_targets_tree(console: Console, targets: Sequence[ResolvedTarget]) -> None:
    tree = Tree("[bold]Targets[/bold]", guide_style="dim")
    for index, target in enumerate(targets):
        role = "target"
        if len(targets) > 1:
            role = "baseline" if index == 0 else "candidate"
        dirty = "dirty" if target.row.is_dirty else "clean"
        binary = target.binary_sha256.removeprefix("sha256:")[:12]
        branch = tree.add(f"[bold]{role}[/bold] {escape(target.display_label)}")
        branch.add(f"source: {escape(target.row.source)}")
        branch.add(f"git: {target.row.git_sha[:12]} ({dirty})")
        if target.row.git_ref != "HEAD":
            branch.add(f"ref: {escape(target.row.git_ref)}")
        branch.add(f"binary: {binary}")
        branch.add(f"path: {escape(target.row.path)}")
    console.print(tree)
