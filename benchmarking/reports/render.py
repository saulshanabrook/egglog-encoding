"""Render the shared benchmark report catalog as Rich or Markdown.

This module owns terminal-width warnings, repeated-cell collapsing, styling,
escaping, headings, and table syntax. Persistence, calculations, report scope,
and section-selection policy belong elsewhere.
"""

from __future__ import annotations

import shlex
from collections.abc import Sequence

from rich import box
from rich.console import Group, RenderableType
from rich.rule import Rule
from rich.table import Table
from rich.text import Text
from rich.tree import Tree

from .catalog import CellTone, ReportCatalog, ReportCell, ReportColumn, ReportMessage, ReportSection, ReportTable

RICH_TIMING_MIN_WIDTH = 120
RICH_TIMING_NARROW_WARNING = (
    "Warning: Rich timing output is designed for terminals at least 120 columns wide "
    "(detected {width}); output may wrap. Widen the terminal or use --format markdown."
)

TONE_STYLES: dict[CellTone, str] = {
    "default": "",
    "positive": "green",
    "negative": "red",
    "warning": "yellow",
    "error": "bold red",
    "muted": "dim",
}


def report_table(title: str, *, caption: str | None = None, wide: bool = False) -> Table:
    """Create one consistently styled Rich report table."""

    return Table(
        title=Text(title, style="bold"),
        caption=None if caption is None else Text(caption, style="dim"),
        caption_justify="left",
        header_style="bold",
        box=box.SIMPLE_HEAVY,
        expand=wide,
        collapse_padding=wide,
        padding=(0, 1),
    )


def render_rich_table(table_data: ReportTable) -> Table:
    """Render one catalog table without interpreting its display strings."""

    wide = table_data.layout == "wide"
    table = report_table(table_data.title, caption=table_data.caption, wide=wide)
    visible = tuple((index, column) for index, column in enumerate(table_data.columns) if column.visible)
    for _, column in visible:
        if column.alignment == "left" and wide:
            table.add_column(Text(column.label), justify="left", overflow="fold")
        else:
            table.add_column(
                Text(column.label),
                no_wrap=column.alignment == "right",
                justify="right" if column.alignment == "right" else "left",
            )
    for values in _display_rows(table_data, visible):
        table.add_row(*(Text(value.display, style=TONE_STYLES[value.tone]) for value in values))
    return table


def markdown_escape_cell(value: object) -> str:
    """Escape one Markdown table cell without changing its visible meaning."""

    text = str(value)
    return text.replace("\\", "\\\\").replace("|", "\\|").replace("\r\n", "\n").replace("\n", "<br>")


def render_markdown_table(table_data: ReportTable, *, heading_level: int = 3) -> str:
    """Render one catalog table as Markdown."""

    visible = tuple((index, column) for index, column in enumerate(table_data.columns) if column.visible)
    separator_cells = tuple("---:" if column.alignment == "right" else "---" for _, column in visible)
    title = _markdown_heading(table_data.title) if table_data.layout == "wide" else table_data.title
    lines = [
        f"{'#' * heading_level} {title}",
        "",
        "| " + " | ".join(markdown_escape_cell(column.label) for _, column in visible) + " |",
        "| " + " | ".join(separator_cells) + " |",
    ]
    for values in _display_rows(table_data, visible):
        lines.append("| " + " | ".join(markdown_escape_cell(value.display) for value in values) + " |")
    if table_data.caption:
        lines.extend(["", f"*{markdown_escape_cell(table_data.caption)}*"])
    return "\n".join(lines)


def benchmark_command_block(argv: Sequence[str]) -> str:
    """Render the reproducible benchmark command used for a Markdown report."""

    return "```shell\n$ " + shlex.join(["./bench.py", *argv]) + "\n```"


def render_rich_report_document(catalog: ReportCatalog, width: int) -> Group:
    """Render all Rich catalog sections in their decision-oriented order."""

    renderables: list[RenderableType] = [
        Rule("[bold]Benchmark report[/bold]"),
        Text.assemble("Report: ", (catalog.report_path, "bold")),
        Text.assemble("Selected rows per result: ", (str(catalog.rounds), "bold")),
    ]
    for section in catalog.sections:
        renderables.extend(_rich_section_renderables(section, width))
    return Group(*renderables)


def render_markdown_report_document(catalog: ReportCatalog) -> str:
    """Render every Markdown section from the same catalog used by Rich."""

    parts: list[str] = []
    if catalog.command_argv is not None:
        parts.append(benchmark_command_block(catalog.command_argv))
    parts.extend(
        (
            "# Benchmark Report",
            f"- Report: `{catalog.report_path}`\n- Selected rows per result: `{catalog.rounds}`",
        )
    )
    for section in catalog.sections:
        parts.extend(_markdown_section_parts(section))
    return "\n\n".join(part.strip() for part in parts if part.strip())


def render_rich_sections(sections: Sequence[ReportSection], width: int) -> Group:
    """Render selected catalog sections without the full report preamble."""

    return Group(*(renderable for section in sections for renderable in _rich_section_renderables(section, width)))


def render_markdown_sections(sections: Sequence[ReportSection]) -> str:
    """Render selected catalog sections without the full report preamble."""

    parts = [part for section in sections for part in _markdown_section_parts(section)]
    return "\n\n".join(part.strip() for part in parts if part.strip())


def _rich_section_renderables(section: ReportSection, width: int) -> tuple[RenderableType, ...]:
    renderables: list[RenderableType] = []
    if section.id == "timing":
        if width < RICH_TIMING_MIN_WIDTH:
            renderables.append(Text(RICH_TIMING_NARROW_WARNING.format(width=width), style="yellow"))
        renderables.append(Text("Engine timing", style="bold", justify="center"))
        renderables.extend(_render_rich_block(block) for block in section.blocks)
    elif section.id == "detailed-timing":
        renderables.append(Text("Detailed timing", style="bold", justify="center"))
        renderables.extend(_render_rich_block(block) for block in section.blocks)
    elif section.id == "summary":
        renderables.append(Rule("[bold]Benchmark summary[/bold]"))
        renderables.extend(_render_rich_block(block) for block in section.blocks)
    else:
        renderables.extend(_render_rich_block(block) for block in section.blocks)
    return tuple(renderables)


def _markdown_section_parts(section: ReportSection) -> tuple[str, ...]:
    parts: list[str] = []
    if section.id == "targets":
        parts.extend(
            render_markdown_table(block, heading_level=2) for block in section.blocks if isinstance(block, ReportTable)
        )
        return tuple(parts)
    if section.title is not None:
        parts.append(f"## {_markdown_heading(section.title)}")
    parts.extend(_render_markdown_block(block) for block in section.blocks)
    return tuple(parts)


def _render_rich_block(block: ReportTable | ReportMessage) -> RenderableType:
    if isinstance(block, ReportTable):
        if block.layout == "target-tree":
            return _render_rich_targets(block)
        return render_rich_table(block)
    if block.layout == "caption":
        return Text(block.text, style=TONE_STYLES[block.tone])
    if block.title is None:
        return Text(block.text, style=TONE_STYLES[block.tone])
    return Group(Text(block.title, style="bold"), Text(block.text, style=TONE_STYLES[block.tone] or "dim"))


def _render_markdown_block(block: ReportTable | ReportMessage) -> str:
    if isinstance(block, ReportTable):
        return render_markdown_table(block)
    if block.layout == "caption":
        return f"*{markdown_escape_cell(block.text)}*"
    if block.title is None:
        return markdown_escape_cell(block.text)
    return f"### {_markdown_heading(block.title)}\n\n{markdown_escape_cell(block.text)}"


def _render_rich_targets(table: ReportTable) -> Tree:
    """Preserve the compact Rich target tree from the shared target table."""

    tree = Tree(Text(table.title, style="bold"), guide_style="dim")
    column_indexes = {column.id: index for index, column in enumerate(table.columns)}
    for row in table.rows:
        cells = {column_id: row.cells[index] for column_id, index in column_indexes.items()}
        dirty = "dirty" if cells["dirty"].raw is True else "clean"
        binary = str(cells["binary"].raw).removeprefix("sha256:")[:12]
        git_sha = str(cells["git"].raw)
        git_ref = str(cells["git_ref"].raw)
        branch = tree.add(Text.assemble((cells["role"].display, "bold"), " ", cells["label"].display))
        branch.add(Text.assemble("source: ", cells["source"].display))
        branch.add(Text.assemble("git: ", git_sha[:12], f" ({dirty})"))
        if git_ref != "HEAD":
            branch.add(Text.assemble("ref: ", git_ref))
        branch.add(Text.assemble("binary: ", binary))
        branch.add(Text.assemble("path: ", cells["path"].display))
    return tree


def _display_rows(
    table: ReportTable,
    visible: Sequence[tuple[int, ReportColumn]],
) -> tuple[tuple[ReportCell, ...], ...]:
    previous: dict[int, object] = {}
    rows: list[tuple[ReportCell, ...]] = []
    for row in table.rows:
        values: list[ReportCell] = []
        for index, column in visible:
            cell = row.cells[index]
            if column.collapse_repeats and index in previous and previous[index] == cell.raw:
                cell = ReportCell(cell.raw, "", cell.tone)
            else:
                previous[index] = cell.raw
            values.append(cell)
        rows.append(tuple(values))
    return tuple(rows)


def _markdown_heading(value: str) -> str:
    return value.replace("\n", " ").replace("#", "\\#")
