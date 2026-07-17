"""Define renderer-neutral options and output contracts for pair reports.

This module owns the cumulative detail option, stable presentation identities,
raw-versus-display cells, section ordering, and structural invariants shared by
Rich, Markdown, and live views. It performs no persistence queries, statistical
analysis, or renderer-specific serialization.
"""

from __future__ import annotations

import json
from collections.abc import Iterable
from dataclasses import dataclass
from typing import Literal

from ..models import DetailLevel

type ReportScalar = str | int | float | bool | None
TableAlignment = Literal["left", "right"]
CellTone = Literal["default", "positive", "negative", "warning", "error", "muted"]
TableLayout = Literal["standard", "wide"]
MessageLayout = Literal["text", "caption"]


@dataclass(frozen=True)
class ReportOptions:
    """The cumulative presentation detail requested for one comparison."""

    detail: DetailLevel = "summary"


@dataclass(frozen=True)
class ReportCell:
    """One machine-readable value and its exact human-facing representation."""

    raw: ReportScalar
    display: str
    tone: CellTone = "default"


@dataclass(frozen=True)
class ReportColumn:
    """One stable table column and its renderer-neutral display policy."""

    id: str
    label: str
    alignment: TableAlignment = "left"
    collapse_repeats: bool = False
    visible: bool = True


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
    layout: TableLayout = "standard"

    def __post_init__(self) -> None:
        _require_unique("column", (column.id for column in self.columns), owner=self.id)
        _require_unique("row", (row.id for row in self.rows), owner=self.id)
        width = len(self.columns)
        for row in self.rows:
            if len(row.cells) != width:
                raise ValueError(
                    f"report row {row.id!r} has {len(row.cells)} cells; table {self.id!r} has {width} columns"
                )


@dataclass(frozen=True)
class ReportMessage:
    """A titled status or untitled caption block within a report section."""

    id: str
    title: str | None
    text: str
    tone: CellTone = "default"
    layout: MessageLayout = "text"


type ReportBlock = ReportTable | ReportMessage


@dataclass(frozen=True)
class ReportSection:
    """An ordered group of report tables and messages with one stable identity."""

    id: str
    title: str | None
    blocks: tuple[ReportBlock, ...]

    def __post_init__(self) -> None:
        _require_unique("block", (block.id for block in self.blocks), owner=self.id)


@dataclass(frozen=True)
class ReportCatalog:
    """The complete shared presentation catalog for one explicit comparison."""

    sections: tuple[ReportSection, ...]

    def __post_init__(self) -> None:
        _require_unique("section", (section.id for section in self.sections), owner="report")
        _require_unique(
            "block",
            (block.id for section in self.sections for block in section.blocks),
            owner="report",
        )


def report_id(*parts: str | int) -> str:
    """Return an unambiguous stable ID without relying on display labels."""

    return json.dumps(parts, ensure_ascii=False, separators=(",", ":"))


def text_cell(value: ReportScalar, display: str | None = None, *, tone: CellTone = "default") -> ReportCell:
    """Construct a cell while preserving the typed value behind its display text."""

    if display is None:
        display = "" if value is None else str(value)
    return ReportCell(value, display, tone)


def _require_unique(kind: str, values: Iterable[str], *, owner: str) -> None:
    seen: set[str] = set()
    for value in values:
        if value in seen:
            raise ValueError(f"duplicate report {kind} ID {value!r} in {owner!r}")
        seen.add(value)
