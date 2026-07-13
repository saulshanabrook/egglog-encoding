"""eval-live registry for the report tables — a generic loop, no per-table code.

Registers every table from ``tables.build_report_tables`` so adding a table in
``tables.py`` makes it appear in the web view and ``--dump-dir`` automatically.
Runs in Python (dump) and as the Pyodide graph script (web); the set of tables to
register is baked in as ``_PRESENT_TABLES`` by ``web.graph_script_source`` (web) or
passed to ``_register`` (dump). Rows are recomputed from the (filtered) data, so
validation is skipped — pandera is unavailable in-browser.
"""

from __future__ import annotations

from collections.abc import Callable
from pathlib import Path
from typing import Any, cast

import eval_live
import pandas as pd

import models
import tables

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

_last: dict[str, Any] = {"data": None, "catalog": None}


def _web_cell(cell: tables.Cell) -> Any:
    if cell.status is None:
        return cell.text
    return {"text": cell.text, "style": STATUS_STYLE.get(cell.status)}


def _reconstruct(data: dict[str, Any]) -> tuple[pd.DataFrame, models.BenchmarkSpec, list[models.ResolvedTarget]]:
    records = data.get("Benchmark report", [])
    metadata = data.get("metadata") or [{}]
    rounds = int(metadata[0].get("rounds", 1) or 1)
    frame = pd.DataFrame(records)

    files: list[models.FileSpec] = []
    seen_files: set[str] = set()
    targets: list[models.ResolvedTarget] = []
    seen_targets: set[str] = set()
    present_treatments: set[str] = set()
    timeout = 120
    for rec in records:
        present_treatments.add(rec["treatment"])
        timeout = int(rec["timeout_sec"])
        file_sha = rec["file_sha256"]
        if file_sha not in seen_files:
            seen_files.add(file_sha)
            files.append(
                models.FileSpec(display_path=rec["file_path"], absolute_path=Path(rec["file_path"]), sha256=file_sha)
            )
        binary = rec["binary_sha256"]
        if binary not in seen_targets:
            seen_targets.add(binary)
            row = models.TargetRow(
                source=rec["target_source"],
                path=rec["target_path"],
                git_ref=rec["target_git_ref"],
                git_sha=rec["target_git_sha"],
                is_dirty=bool(rec["target_is_dirty"]),
                label=rec.get("target_label"),
            )
            request = models.TargetRequest(
                raw=rec["target_source"], source=rec["target_source"], label=rec.get("target_label")
            )
            targets.append(models.ResolvedTarget(request=request, row=row, binary_sha256=binary, binary_path=None))

    treatments = cast(
        "tuple[models.Treatment, ...]", tuple(t for t in ("off", "term", "proofs") if t in present_treatments)
    )
    spec = models.BenchmarkSpec(files=tuple(files), treatments=treatments, rounds=rounds, timeout_sec=timeout)
    return frame, spec, targets


def _catalog(data: dict[str, Any]) -> list[tables.ReportTable]:
    if _last["data"] is not data:  # one build per render pass (all table fns share the data object)
        frame, spec, targets = _reconstruct(data)
        _last["data"] = data
        _last["catalog"] = tables.build_report_tables(cast("Any", frame), targets, spec, validate=False)
    return cast("list[tables.ReportTable]", _last["catalog"])


def present_tables(data: dict[str, Any]) -> list[tuple[str, str | None]]:
    """The (web_name, caption) of every table present for this data."""
    return [(table.web_name, table.caption) for table in _catalog(data)]


def _web_rows(table: tables.ReportTable) -> list[dict[str, Any]]:
    dropped = {
        column.label
        for column in table.columns
        if column.drop_if_empty and all(not row[column.label].text for row in table.rows)
    }
    return [
        {column.label: _web_cell(row[column.label]) for column in table.columns if column.label not in dropped}
        for row in table.rows
    ]


def _narrow_by_file_treatment(filtered_rows: list[dict[str, Any]], data: dict[str, Any]) -> dict[str, Any]:
    files = {r["File"] for r in filtered_rows if "File" in r}
    treatments = {r["Treatment"] for r in filtered_rows if "Treatment" in r}
    kept = [
        rec
        for rec in data.get("Benchmark report", [])
        if (not files or rec["file_path"] in files) and (not treatments or rec["treatment"] in treatments)
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
        reg.table(web_name, _make_fn(web_name), _narrow_by_file_treatment, caption=caption)


_present = globals().get("_PRESENT_TABLES")
if _present is not None:  # graph-script (web) path: register the baked-in table set
    _registry = eval_live.Registry()
    _register(_registry, _present)
    eval_live.registry = _registry
