"""Define the renderer-neutral document model for benchmark pair reports.

The catalog contains stable section, table, row, and cell identities plus the
text and tones shared by Rich, Markdown, and interactive output. Statistical
analysis lives in :mod:`benchmarking.reports.analysis`; renderer-specific
layout lives in :mod:`benchmarking.reports.render`.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from typing import Literal

type ReportScalar = str | int | float | bool | None
TableAlignment = Literal["left", "right"]
CellTone = Literal["default", "positive", "negative", "warning", "error", "muted"]


@dataclass(frozen=True)
class ReportCell:
    """One machine-readable value and its exact human-facing representation."""

    raw: ReportScalar
    display: str
    tone: CellTone = "default"


@dataclass(frozen=True)
class ReportColumn:
    """One stable table column and its shared alignment."""

    id: str
    label: str
    alignment: TableAlignment = "left"


@dataclass(frozen=True)
class ReportRow:
    """One stable row whose cells correspond exactly to its table's columns."""

    id: str
    cells: tuple[ReportCell, ...]


@dataclass(frozen=True)
class ReportTable:
    """One complete renderer-neutral table in a report catalog."""

    id: str
    title: str
    columns: tuple[ReportColumn, ...]
    rows: tuple[ReportRow, ...]
    caption: str | None = None


@dataclass(frozen=True)
class ReportMessage:
    """A titled status or untitled explanatory block within a report section."""

    id: str
    title: str | None
    text: str
    tone: CellTone = "default"


type ReportBlock = ReportTable | ReportMessage


@dataclass(frozen=True)
class ReportSection:
    """An ordered group of report tables and messages with one stable identity."""

    id: str
    title: str | None
    blocks: tuple[ReportBlock, ...]


@dataclass(frozen=True)
class ReportCatalog:
    """The complete shared presentation catalog for one explicit comparison."""

    sections: tuple[ReportSection, ...]


def report_id(*parts: str | int) -> str:
    """Return an unambiguous stable ID without relying on display labels."""

    return json.dumps(parts, ensure_ascii=False, separators=(",", ":"))


def text_cell(value: ReportScalar, display: str | None = None, *, tone: CellTone = "default") -> ReportCell:
    """Construct a cell while preserving the typed value behind its display text."""

    if display is None:
        display = "" if value is None else str(value)
    return ReportCell(value, display, tone)
