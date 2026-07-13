"""eval-live registry for the benchmark report (web view + on-disk dump).

Runs both in Python (``render_to_dir`` for ``--dump-dir``) and in the browser
(its source is the Pyodide graph script; tables recompute as the user filters).
Numbers come from ``tables.py`` — the same compute the CLI uses. Spec and targets
are derived from the rows; validation is skipped (pandera is unavailable in-browser).
"""

from __future__ import annotations

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


def _styled(status: str, text: str | None = None) -> dict[str, Any]:
    return {"text": text or status, "style": STATUS_STYLE.get(status)}


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


def _cell_maps(
    data: dict[str, Any], *, rss: bool
) -> tuple[models.BenchmarkSpec, list[models.ResolvedTarget], dict[Any, Any]]:
    frame, spec, targets = _reconstruct(data)
    summarize = tables.target_rss_cell_summaries if rss else tables.target_cell_summaries
    # The browser passes a plain (unvalidated) DataFrame here by design.
    cell_maps = {target: summarize(cast("Any", frame), target, spec, validate=False) for target in targets}
    return spec, targets, cell_maps


def _narrow_by_file_treatment(filtered_rows: list[dict[str, Any]], data: dict[str, Any]) -> dict[str, Any]:
    files = {r["File"] for r in filtered_rows if "File" in r}
    treatments = {r["Treatment"] for r in filtered_rows if "Treatment" in r}
    kept = [
        rec
        for rec in data.get("Benchmark report", [])
        if (not files or rec["file_path"] in files) and (not treatments or rec["treatment"] in treatments)
    ]
    return {**data, "Benchmark report": kept}


def per_file_wall_time(data: dict[str, Any]) -> list[dict[str, Any]]:
    spec, targets, cell_maps = _cell_maps(data, rss=False)
    rows: list[dict[str, Any]] = []
    for target in targets:
        for file_spec in spec.files:
            for treatment in spec.treatments:
                cell = cell_maps[target][(file_spec.sha256, treatment)]
                rows.append(
                    {
                        "Target": target.display_label,
                        "File": file_spec.display_path,
                        "Treatment": treatment,
                        "Wall time": tables.format_seconds_summary(cell),
                        "Issue": cell.issue or "",
                    }
                )
    return rows


def per_file_peak_rss(data: dict[str, Any]) -> list[dict[str, Any]]:
    spec, targets, cell_maps = _cell_maps(data, rss=True)
    if not any(cell.samples for cmap in cell_maps.values() for cell in cmap.values()):
        return []
    rows: list[dict[str, Any]] = []
    for target in targets:
        for file_spec in spec.files:
            for treatment in spec.treatments:
                cell = cell_maps[target][(file_spec.sha256, treatment)]
                rows.append(
                    {
                        "Target": target.display_label,
                        "File": file_spec.display_path,
                        "Treatment": treatment,
                        "Peak RSS": tables.format_bytes_summary(cell),
                    }
                )
    return rows


def overhead_ratios(data: dict[str, Any]) -> list[dict[str, Any]]:
    spec, targets, cell_maps = _cell_maps(data, rss=False)
    ratio_columns = tables.ratio_specs(spec.treatments)
    if not ratio_columns:
        return []
    rows: list[dict[str, Any]] = []
    for target in targets:
        cell_map = cell_maps[target]
        for file_spec in spec.files:
            row: dict[str, Any] = {"Target": target.display_label, "File": file_spec.display_path}
            for baseline_treatment, candidate_treatment, ratio_name in ratio_columns:
                ratio = tables.ratio_summary(
                    cell_map[(file_spec.sha256, baseline_treatment)],
                    cell_map[(file_spec.sha256, candidate_treatment)],
                )
                row[ratio_name] = tables.format_ratio_summary(ratio)
            rows.append(row)
    return rows


def wall_time_change(data: dict[str, Any]) -> list[dict[str, Any]]:
    spec, targets, cell_maps = _cell_maps(data, rss=False)
    if len(targets) < 2:
        return []
    baseline = targets[0]
    rows: list[dict[str, Any]] = []
    for target in targets[1:]:
        for file_spec in spec.files:
            for treatment in spec.treatments:
                ratio = tables.ratio_summary(
                    cell_maps[baseline][(file_spec.sha256, treatment)],
                    cell_maps[target][(file_spec.sha256, treatment)],
                )
                rows.append(
                    {
                        "Target": target.display_label,
                        "File": file_spec.display_path,
                        "Treatment": treatment,
                        "Time ratio": tables.format_ratio_summary(ratio),
                        "Wall-time change": tables.format_wall_time_change(ratio),
                        "Result": _styled(tables.comparison_result(ratio)),
                    }
                )
    return rows


def peak_rss_change(data: dict[str, Any]) -> list[dict[str, Any]]:
    spec, targets, cell_maps = _cell_maps(data, rss=True)
    if len(targets) < 2 or not any(cell.samples for cmap in cell_maps.values() for cell in cmap.values()):
        return []
    baseline = targets[0]
    rows: list[dict[str, Any]] = []
    for target in targets[1:]:
        for file_spec in spec.files:
            for treatment in spec.treatments:
                ratio = tables.ratio_summary(
                    cell_maps[baseline][(file_spec.sha256, treatment)],
                    cell_maps[target][(file_spec.sha256, treatment)],
                )
                rows.append(
                    {
                        "Target": target.display_label,
                        "File": file_spec.display_path,
                        "Treatment": treatment,
                        "RSS ratio": tables.format_ratio_summary(ratio),
                        "RSS change": tables.format_percent_change(ratio),
                        "Result": _styled(tables.lower_is_better_result(ratio)),
                    }
                )
    return rows


def build_registry() -> Any:
    reg = eval_live.Registry()
    reg.table(
        "Per-file wall time",
        per_file_wall_time,
        _narrow_by_file_treatment,
        caption="Within-target wall-time estimates (mean with 95% CI). Not target-vs-baseline ratios.",
    )
    reg.table(
        "Per-file peak RSS",
        per_file_peak_rss,
        _narrow_by_file_treatment,
        caption="Within-target peak resident set size estimates.",
    )
    reg.table(
        "Overhead ratios",
        overhead_ratios,
        _narrow_by_file_treatment,
        caption="Within-target treatment ratios. Not target-vs-baseline wall-time change.",
    )
    reg.table(
        "Wall-time change vs baseline",
        wall_time_change,
        _narrow_by_file_treatment,
        caption=tables.TARGET_WALL_TIME_CAPTION,
    )
    reg.table(
        "Peak RSS change vs baseline",
        peak_rss_change,
        _narrow_by_file_treatment,
        caption=tables.TARGET_PEAK_RSS_CAPTION,
    )
    return reg


eval_live.registry = build_registry()
