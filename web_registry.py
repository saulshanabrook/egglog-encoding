"""eval-live registry for the report tables — a generic loop, no per-table code.

Registers every table from ``report.build_report_tables`` so adding a table in
``report.py`` appears in the web view and ``--dump-dir`` automatically. Runs in
Python (dump) and as the Pyodide graph script (web). The authoritative scope
(``ReportSelection``) and the present table set are baked in by the host as
``_SELECTION`` / ``_PRESENT_TABLES``; the browser never reconstructs scope from
rows. Rows are recomputed from the (filtered) data with validation skipped —
pandera is unavailable in-browser.
"""

from __future__ import annotations

from collections.abc import Callable
from typing import Any, cast

import eval_live
import pandas as pd

import models
import report

# Visual-only styles (eval-live keeps meaning caller-side): mirror the CLI palette.
STATUS_STYLE: dict[str, Any] = {
    "faster": {"color": "green"},
    "less": {"color": "green"},
    "established": {"color": "green"},
    "slower": {"color": "red"},
    "more": {"color": "red"},
    "not established": {"color": "red"},
    "invalid": {"color": "red", "bold": True},
    "unclear": {"color": "goldenrod"},
    "point only": {"dim": True},
    "descriptive": {"dim": True},
}

_scope: dict[str, Any] = {"targets": [], "spec": None}
_last: dict[str, Any] = {"data": None, "catalog": None}


def configure(selection: models.ReportSelection) -> None:
    """Set the authoritative scope used to recompute tables (targets + spec)."""
    _scope["targets"] = models.selection_targets(selection)
    _scope["spec"] = models.selection_spec(selection)


def _web_cell(cell: report.Cell) -> Any:
    if cell.status is None:
        return cell.text
    return {"text": cell.text, "style": STATUS_STYLE.get(cell.status)}


def _catalog(data: dict[str, Any]) -> list[report.ReportTable]:
    if _last["data"] is not data:  # one build per render pass (all table fns share the data object)
        records = data.get("Benchmark report", [])
        _last["data"] = data
        if records and _scope["spec"] is not None:
            frame = pd.DataFrame(records)
            _last["catalog"] = report.build_report_tables(
                cast("Any", frame), _scope["targets"], _scope["spec"], validate=False
            )
        else:
            _last["catalog"] = []
    return cast("list[report.ReportTable]", _last["catalog"])


def present_tables(data: dict[str, Any]) -> list[tuple[str, str | None]]:
    """The (web_name, caption) of every table present for this data."""
    return [(table.web_name, table.caption) for table in _catalog(data)]


def _web_rows(table: report.ReportTable) -> list[dict[str, Any]]:
    dropped = {
        column.label
        for column in table.columns
        if column.drop_if_empty and all(not row[column.label].text for row in table.rows)
    }
    return [
        {column.label: _web_cell(row[column.label]) for column in table.columns if column.label not in dropped}
        for row in table.rows
    ]


def _narrow_raw_rows(filtered_rows: list[dict[str, Any]], data: dict[str, Any]) -> dict[str, Any]:
    """Narrow raw rows to those matching the visible computed rows (File/Treatment/Target).

    An empty set of visible rows narrows to nothing (not a wildcard).
    """
    if not filtered_rows:
        return {**data, "Benchmark report": []}
    files = {row["File"] for row in filtered_rows if "File" in row}
    treatments = {row["Treatment"] for row in filtered_rows if "Treatment" in row}
    labels = {row["Target"] for row in filtered_rows if "Target" in row}
    target_shas = {target.binary_sha256 for target in _scope["targets"] if target.display_label in labels}
    kept = [
        rec
        for rec in data.get("Benchmark report", [])
        if (not files or rec["file_path"] in files)
        and (not treatments or rec["treatment"] in treatments)
        and (not labels or rec["binary_sha256"] in target_shas)
    ]
    return {**data, "Benchmark report": kept}


def _make_fn(web_name: str) -> Callable[[dict[str, Any]], list[dict[str, Any]]]:
    def fn(data: dict[str, Any]) -> list[dict[str, Any]]:
        for table in _catalog(data):
            if table.web_name == web_name:
                return _web_rows(table)
        return []

    return fn


def _register(reg: Any, present: list[tuple[str, str | None]]) -> None:
    for web_name, caption in present:
        reg.table(web_name, _make_fn(web_name), _narrow_raw_rows, caption=caption)


_selection = globals().get("_SELECTION")
if _selection is not None:  # graph-script (web) path: configure scope + register the baked table set
    configure(models.report_selection_from_dict(_selection))
    _registry = eval_live.Registry()
    _register(_registry, globals().get("_PRESENT_TABLES", []))
    eval_live.registry = _registry
