"""Serialize the shared benchmark report catalog as Rich or Markdown.

Markdown follows the catalog's canonical reading order. Rich reverses the
detail drill-down so terminal users finish on the compact comparison and
decision summary. This module alone owns terminal width behavior, styling,
escaping, headings, and table syntax.
"""

from __future__ import annotations

from rich import box
from rich.cells import cell_len
from rich.console import Group, RenderableType
from rich.rule import Rule
from rich.table import Table
from rich.text import Text

from .catalog import CellTone, ReportCatalog, ReportMessage, ReportSection, ReportTable

RICH_DETAIL_MIN_WIDTH = 120
RICH_TEXT_COLUMN_MIN_WIDTH = 12
RICH_DETAIL_NARROW_WARNING = (
    "Warning: detailed Rich report output is designed for terminals at least 120 columns wide "
    "(detected {width}); output may wrap. Widen the terminal or use --format markdown."
)

DETAIL_SECTION_IDS = frozenset({"files", "phases", "rulesets"})
RICH_SECTION_ORDER = ("rulesets", "phases", "files", "selection", "summary")

TONE_STYLES: dict[CellTone, str] = {
    "default": "",
    "positive": "green",
    "emphasis": "bold",
    "warning": "yellow",
    "error": "bold red",
    "muted": "dim",
}


def render_rich_table(
    table_data: ReportTable,
    *,
    show_title: bool = True,
    preferred_widths: tuple[int, ...] | None = None,
) -> Table:
    """Render one catalog table without interpreting its display strings."""

    table = Table(
        title=Text(table_data.title, style="bold") if show_title else None,
        caption=None if table_data.caption is None else Text(table_data.caption, style="dim"),
        caption_justify="left",
        header_style="bold",
        box=box.SIMPLE_HEAVY,
        expand=True,
        collapse_padding=True,
        padding=(0, 1),
    )
    widths: tuple[int | None, ...] = preferred_widths or tuple(None for _ in table_data.columns)
    for column, preferred_width in zip(table_data.columns, widths, strict=True):
        if preferred_width is None:
            ratio = width = min_width = None
            no_wrap = False
        elif column.alignment == "right":
            ratio = min_width = None
            width = preferred_width
            no_wrap = True
        else:
            ratio = preferred_width
            width = None
            min_width = min(
                preferred_width,
                max(_max_line_width(column.label), RICH_TEXT_COLUMN_MIN_WIDTH),
            )
            no_wrap = False
        table.add_column(
            Text(column.label),
            justify="right" if column.alignment == "right" else "left",
            overflow="fold",
            ratio=ratio,
            width=width,
            min_width=min_width,
            no_wrap=no_wrap,
        )
    for row in table_data.rows:
        table.add_row(*(Text(cell.display, style=TONE_STYLES[cell.tone]) for cell in row.cells))
    return table


def markdown_escape_cell(value: object) -> str:
    """Escape one Markdown table cell without changing its visible meaning."""

    text = str(value)
    return text.replace("\\", "\\\\").replace("|", "\\|").replace("\r\n", "\n").replace("\n", "<br>")


def render_markdown_table(table_data: ReportTable, *, heading_level: int | None = 3) -> str:
    """Render one catalog table as Markdown."""

    separator_cells = tuple("---:" if column.alignment == "right" else "---" for column in table_data.columns)
    lines = [
        "| " + " | ".join(markdown_escape_cell(column.label) for column in table_data.columns) + " |",
        "| " + " | ".join(separator_cells) + " |",
    ]
    if heading_level is not None:
        lines[:0] = [f"{'#' * heading_level} {_markdown_heading(table_data.title)}", ""]
    for row in table_data.rows:
        lines.append("| " + " | ".join(markdown_escape_cell(cell.display) for cell in row.cells) + " |")
    if table_data.caption:
        lines.extend(["", f"*{markdown_escape_cell(table_data.caption)}*"])
    return "\n".join(lines)


def render_rich_report_document(catalog: ReportCatalog, width: int) -> Group:
    """Render rulesets, phases, files, comparison, then the final summary."""

    shared_column_widths = _shared_column_widths(catalog)
    sections = {section.id: section for section in catalog.sections}
    ordered = tuple(sections[section_id] for section_id in RICH_SECTION_ORDER if section_id in sections)
    ordered_ids = {section.id for section in ordered}
    ordered += tuple(section for section in catalog.sections if section.id not in ordered_ids)
    has_detail = any(section.id in DETAIL_SECTION_IDS for section in catalog.sections)
    warning_pending = width < RICH_DETAIL_MIN_WIDTH and has_detail
    renderables: list[RenderableType] = []
    for section in ordered:
        if warning_pending and section.id in DETAIL_SECTION_IDS:
            renderables.append(Text(RICH_DETAIL_NARROW_WARNING.format(width=width), style="yellow"))
            warning_pending = False
        renderables.extend(_rich_section_renderables(section, shared_column_widths))
    return Group(*renderables)


def render_markdown_report_document(catalog: ReportCatalog) -> str:
    """Render the canonical Comparison, Summary, Files, Phases, Rulesets order."""

    parts: list[str] = ["# Benchmark Report"]
    for section in catalog.sections:
        parts.extend(_markdown_section_parts(section))
    return "\n\n".join(part.strip() for part in parts if part.strip())


def _rich_section_renderables(
    section: ReportSection,
    shared_column_widths: dict[str, tuple[int, ...]],
) -> tuple[RenderableType, ...]:
    renderables: list[RenderableType] = []
    if section.title is not None:
        renderables.append(Rule(Text(section.title, style="bold"), style="green"))
    hide_first_table_title = _first_table_repeats_section_title(section)
    for index, block in enumerate(section.blocks):
        renderables.append(
            _render_rich_block(
                block,
                show_table_title=not (index == 0 and hide_first_table_title),
                preferred_widths=shared_column_widths.get(block.id) if isinstance(block, ReportTable) else None,
            )
        )
    return tuple(renderables)


def _markdown_section_parts(section: ReportSection) -> tuple[str, ...]:
    parts: list[str] = []
    if section.title is not None:
        parts.append(f"## {_markdown_heading(section.title)}")
    for index, block in enumerate(section.blocks):
        if isinstance(block, ReportTable) and index == 0 and block.title == section.title:
            parts.append(render_markdown_table(block, heading_level=None))
        else:
            parts.append(_render_markdown_block(block))
    return tuple(parts)


def _first_table_repeats_section_title(section: ReportSection) -> bool:
    return (
        section.title is not None
        and bool(section.blocks)
        and isinstance(section.blocks[0], ReportTable)
        and section.blocks[0].title == section.title
    )


def _render_rich_block(
    block: ReportTable | ReportMessage,
    *,
    show_table_title: bool = True,
    preferred_widths: tuple[int, ...] | None = None,
) -> RenderableType:
    if isinstance(block, ReportTable):
        return render_rich_table(block, show_title=show_table_title, preferred_widths=preferred_widths)
    if block.title is None:
        return Text(block.text, style=TONE_STYLES[block.tone] or "dim")
    return Group(Text(block.title, style="bold"), Text(block.text, style=TONE_STYLES[block.tone] or "dim"))


def _render_markdown_block(block: ReportTable | ReportMessage) -> str:
    if isinstance(block, ReportTable):
        return render_markdown_table(block)
    if block.title is None:
        return f"*{markdown_escape_cell(block.text)}*"
    return f"### {_markdown_heading(block.title)}\n\n{markdown_escape_cell(block.text)}"


def _markdown_heading(value: str) -> str:
    return value.replace("\n", " ").replace("#", "\\#")


def _shared_column_widths(catalog: ReportCatalog) -> dict[str, tuple[int, ...]]:
    """Give repeated table schemas one content-derived Rich column layout."""

    families: dict[tuple[tuple[str, str, str], ...], list[ReportTable]] = {}
    for section in catalog.sections:
        for block in section.blocks:
            if isinstance(block, ReportTable):
                signature = tuple((column.id, column.label, column.alignment) for column in block.columns)
                families.setdefault(signature, []).append(block)

    result: dict[str, tuple[int, ...]] = {}
    for tables in families.values():
        if len(tables) < 2:
            continue
        widths = tuple(
            max(
                1,
                _max_line_width(tables[0].columns[column_index].label),
                *(_max_line_width(row.cells[column_index].display) for table in tables for row in table.rows),
            )
            for column_index in range(len(tables[0].columns))
        )
        for table in tables:
            result[table.id] = widths
    return result


def _max_line_width(value: str) -> int:
    """Measure the widest terminal line without counting Unicode code points as cells."""

    return max((cell_len(line) for line in value.splitlines()), default=0)
