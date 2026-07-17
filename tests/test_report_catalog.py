"""Test stable report identities, raw cells, invariants, and display-only collapsing."""

from __future__ import annotations

import pytest

from benchmarking.reports.catalog import (
    ReportCatalog,
    ReportColumn,
    ReportRow,
    ReportSection,
    ReportTable,
    report_id,
    text_cell,
)
from benchmarking.reports.render import render_markdown_report_document


def test_catalog_retains_full_repeated_values_and_renderer_collapses_them() -> None:
    table = ReportTable(
        report_id("table", "comparison", "sha256:target"),
        "Comparison",
        (
            ReportColumn("file", "File", collapse_repeats=True),
            ReportColumn("ratio", "Ratio", "right"),
        ),
        (
            ReportRow(report_id("row", "sha256:file", "off"), (text_cell("file.egg"), text_cell(1.0, "1.000x"))),
            ReportRow(
                report_id("row", "sha256:file", "proofs"),
                (text_cell("file.egg"), text_cell(1.5, "1.500x")),
            ),
        ),
    )
    catalog = ReportCatalog((ReportSection("comparisons", "Comparisons", (table,)),))

    assert tuple(row.cells[0].display for row in table.rows) == ("file.egg", "file.egg")
    assert tuple(row.cells[1].raw for row in table.rows) == (1.0, 1.5)
    markdown = render_markdown_report_document(catalog)
    assert "| file.egg | 1.000x |" in markdown
    assert "|  | 1.500x |" in markdown


def test_catalog_rejects_duplicate_ids_and_wrong_row_widths() -> None:
    column = ReportColumn("value", "Value")
    row = ReportRow("row", (text_cell(1),))

    with pytest.raises(ValueError, match="duplicate report column ID"):
        ReportTable("table", "Title", (column, column), (ReportRow("row", (text_cell(1), text_cell(2))),))
    with pytest.raises(ValueError, match="duplicate report row ID"):
        ReportTable("table", "Title", (column,), (row, row))
    with pytest.raises(ValueError, match="has 0 cells"):
        ReportTable("table", "Title", (column,), (ReportRow("row", ()),))


def test_report_id_is_unambiguous_and_independent_of_display_labels() -> None:
    assert report_id("target", "ab", "c") != report_id("target", "a", "bc")
    assert report_id("target", "sha256:abc") == report_id("target", "sha256:abc")
