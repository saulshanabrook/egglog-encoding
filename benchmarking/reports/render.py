"""Render the shared pair-report catalog as Rich or Markdown.

This module owns terminal-width warnings, Rich's summary-last ordering,
repeated-cell collapsing, styling, escaping, headings, and table syntax.
Persistence, calculations, and section selection belong elsewhere.
"""

from __future__ import annotations

from collections.abc import Sequence

from rich import box
from rich.console import Group, RenderableType
from rich.rule import Rule
from rich.table import Table
from rich.text import Text

from .catalog import CellTone, ReportCatalog, ReportCell, ReportColumn, ReportMessage, ReportSection, ReportTable

RICH_DETAIL_MIN_WIDTH = 120
RICH_DETAIL_NARROW_WARNING = (
    "Warning: detailed Rich report output is designed for terminals at least 120 columns wide "
    "(detected {width}); output may wrap. Widen the terminal or use --format markdown."
)

DETAIL_SECTION_IDS = frozenset({"files", "phases", "rulesets"})

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


def render_markdown_table(table_data: ReportTable, *, heading_level: int | None = 3) -> str:
    """Render one catalog table as Markdown."""

    visible = tuple((index, column) for index, column in enumerate(table_data.columns) if column.visible)
    separator_cells = tuple("---:" if column.alignment == "right" else "---" for _, column in visible)
    title = _markdown_heading(table_data.title) if table_data.layout == "wide" else table_data.title
    lines = [
        "| " + " | ".join(markdown_escape_cell(column.label) for _, column in visible) + " |",
        "| " + " | ".join(separator_cells) + " |",
    ]
    if heading_level is not None:
        lines[:0] = [f"{'#' * heading_level} {title}", ""]
    for values in _display_rows(table_data, visible):
        lines.append("| " + " | ".join(markdown_escape_cell(value.display) for value in values) + " |")
    if table_data.caption:
        lines.extend(["", f"*{markdown_escape_cell(table_data.caption)}*"])
    return "\n".join(lines)


def render_rich_report_document(catalog: ReportCatalog, width: int) -> Group:
    """Render details before the summary so the decision remains visible last."""

    ordered = tuple(section for section in catalog.sections if section.id != "summary") + tuple(
        section for section in catalog.sections if section.id == "summary"
    )
    has_detail = any(section.id in DETAIL_SECTION_IDS for section in catalog.sections)
    warning_pending = width < RICH_DETAIL_MIN_WIDTH and has_detail
    renderables: list[RenderableType] = [Rule("[bold]Benchmark report[/bold]")]
    for section in ordered:
        if warning_pending and section.id in DETAIL_SECTION_IDS:
            renderables.append(Text(RICH_DETAIL_NARROW_WARNING.format(width=width), style="yellow"))
            warning_pending = False
        renderables.extend(_rich_section_renderables(section))
    return Group(*renderables)


def render_markdown_report_document(catalog: ReportCatalog) -> str:
    """Render canonical selection-summary-files-phases-rulesets order."""

    parts: list[str] = ["# Benchmark Report"]
    for section in catalog.sections:
        parts.extend(_markdown_section_parts(section))
    return "\n\n".join(part.strip() for part in parts if part.strip())


def _rich_section_renderables(section: ReportSection) -> tuple[RenderableType, ...]:
    renderables: list[RenderableType] = []
    if section.title is not None and not _has_redundant_table_title(section):
        renderables.append(Rule(Text(section.title, style="bold")))
    renderables.extend(_render_rich_block(block) for block in section.blocks)
    return tuple(renderables)


def _markdown_section_parts(section: ReportSection) -> tuple[str, ...]:
    parts: list[str] = []
    if section.title is not None:
        parts.append(f"## {_markdown_heading(section.title)}")
    if _has_redundant_table_title(section):
        table = section.blocks[0]
        assert isinstance(table, ReportTable)
        parts.append(render_markdown_table(table, heading_level=None))
    else:
        parts.extend(_render_markdown_block(block) for block in section.blocks)
    return tuple(parts)


def _has_redundant_table_title(section: ReportSection) -> bool:
    return (
        section.title is not None
        and len(section.blocks) == 1
        and isinstance(section.blocks[0], ReportTable)
        and section.blocks[0].title == section.title
    )


def _render_rich_block(block: ReportTable | ReportMessage) -> RenderableType:
    if isinstance(block, ReportTable):
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
