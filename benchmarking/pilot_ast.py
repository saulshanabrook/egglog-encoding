"""Bind deterministic compiler sizes and their coverage to portable pilot figures."""

from __future__ import annotations

import csv
import io
import json
import math
import os
import tempfile
from collections.abc import Sequence
from pathlib import Path
from typing import Any

from .config import DEFAULT_MEMORY_LIMIT_BYTES, DEFAULT_TIMEOUT_SEC
from .models import FileSpec
from .slotted_ast import COLUMNS, PIPELINE, export_slotted_ast, slotted_ast_records
from .translation_ast import PIPELINE as TRANSLATION_PIPELINE
from .translation_ast import SAFETY_STATUSES, TranslationRequest, translation_ast_records

PASS_LABELS = {
    "c": "corelog+c",
    "cp": "egglog+p",
    "d": "egglog+d",
    "dcp": "egglog+dp",
    "s": "egglog+s",
    "scp": "egglog+sp",
}
LEGACY_PASS_LABELS = {f"extlog_{profile}": label for profile, label in PASS_LABELS.items()}
RESTRICTED_PASS_LABELS = {"s": "egglog+s′", "scp": "egglog+s′p"}
PASS_COLORS = {
    "corelog+c": "#0072b2",
    "egglog+p": "#d55e00",
    "egglog+d": "#009e73",
    "egglog+dp": "#cc79a7",
    "egglog+s′": "#e69f00",
    "egglog+s′p": "#6a3d9a",
    "egglog+s": "#56b4e9",
    "egglog+sp": "#8c564b",
}
SLOTTED_TREATMENT_LABELS = {
    "slotted-no-aliasing": RESTRICTED_PASS_LABELS["s"],
    "slotted-proof-extraction-no-aliasing": RESTRICTED_PASS_LABELS["scp"],
    "slotted": PASS_LABELS["s"],
    "slotted-proof-extraction": PASS_LABELS["scp"],
}
TRANSLATION_NOTE = (
    "Whole-program S-expression nodes: each list, atom, and literal counts once. "
    "The denominator is self-contained raw source; emitted scaffolding remains in the output. "
    "Each point is an independently compiled input/configuration, not a consecutive pass intermediate. "
    "Compilation does not execute programs, extract proofs, or verify them. "
    "Counts are deterministic; missing and failed cases remain in coverage, not at zero. "
    "Compiler/input identities are independent of timing endpoints."
)


def log_major_ticks(domain: Sequence[float]) -> list[float]:
    """Choose at most six explicit major ticks, without logarithmic minor marks."""
    low, high = domain
    powers = range(math.floor(math.log10(low)), math.ceil(math.log10(high)) + 1)
    ticks = [10.0**power for power in powers if low <= 10.0**power <= high]
    if len(ticks) < 2:
        ticks = [
            factor * 10.0**power for power in powers for factor in (1, 2, 5) if low <= factor * 10.0**power <= high
        ]
    return ticks[:: max(1, math.ceil(len(ticks) / 6))]


def ratio_guide_factors(ratios: Sequence[float]) -> list[float]:
    """Bracket observed ratios with conventional multiples while retaining orientation guides."""
    values = [r for r in ratios if math.isfinite(r) and r > 0]
    low, high = min([0.5, *values]), max([10.0, *values])
    candidates = sorted(
        {
            m * 10.0**p
            for p in range(math.floor(math.log10(low)) - 1, math.ceil(math.log10(high)) + 1)
            for m in (1, 2, 5)
        }
    )
    lower = max(v for v in candidates if v <= low)
    upper = min(v for v in candidates if v >= high)
    return sorted({lower, 0.5, 1.0, 2.0, 5.0, *[v for v in candidates if 10 <= v <= upper]})


def ratio_guide_labels(
    guides: Sequence[dict[str, Any]],
    x_domain: Sequence[float],
    y_domain: Sequence[float],
    width: float,
    height: float,
    points: Sequence[dict[str, Any]],
) -> list[dict[str, Any]]:
    """Place ratio labels on their lines, avoiding labels and mean points at the actual panel size."""
    x0, x1 = map(math.log, x_domain)
    y0, y1 = map(math.log, y_domain)
    occupied = [
        (
            width * (math.log(p["x"]) - x0) / (x1 - x0) - 3,
            height * (y1 - math.log(p["y"])) / (y1 - y0) - 3,
            width * (math.log(p["x"]) - x0) / (x1 - x0) + 3,
            height * (y1 - math.log(p["y"])) / (y1 - y0) + 3,
        )
        for p in points
    ]
    labels = []
    for guide in guides:
        label = str(guide.get("factor", guide.get("label")))
        candidates = []
        for fraction in (0.92, 0.84, 0.76, 0.68, 0.60, 0.54):
            x = guide["x"] * (guide["x2"] / guide["x"]) ** fraction
            y = guide["y"] * (guide["y2"] / guide["y"]) ** fraction
            px, py = width * (math.log(x) - x0) / (x1 - x0), height * (y1 - math.log(y)) / (y1 - y0)
            box = (px - 6 * len(label), py - 16, px + 1, py - 3)
            outside = max(0, -box[0]) + max(0, -box[1]) + max(0, box[2] - width) + max(0, box[3] - height)
            overlap = sum(
                max(0, min(box[2], b[2]) - max(box[0], b[0])) * max(0, min(box[3], b[3]) - max(box[1], b[1]))
                for b in occupied
            )
            candidates.append((outside * 10000 + overlap, x, y, box))
            if outside == overlap == 0:
                break
        _, x, y, box = min(candidates, key=lambda c: c[0])
        labels.append({"x": x, "y": y, "label": label})
        occupied.append(box)
    return labels


def translation_program_size_snapshot(
    config: dict[str, Any],
    files: dict[str, FileSpec],
    cache: Path,
    *,
    collect: bool,
    compiler: Path | None = None,
    timeout_sec: int = DEFAULT_TIMEOUT_SEC,
    memory_limit_bytes: int | None = DEFAULT_MEMORY_LIMIT_BYTES,
) -> dict[str, Any]:
    """Freeze broad source/configuration coverage separately from legacy Slotted rows."""
    experiments = {experiment["id"]: experiment for experiment in config["experiments"]}
    requests = []
    for name, profiles, family, no_aliasing in (
        ("corpus-congruence", ("c", "cp"), "egglog corpus", None),
        ("math", ("c", "cp"), "Math", None),
        ("disequality", ("d", "dcp"), "Disequality", None),
        ("slotted", ("s", "scp"), "Slotted restricted", True),
        ("slotted-complete", ("s", "scp"), "Slotted complete", False),
    ):
        for display in experiments.get(name, {}).get("files", []):
            project = Path(display).parent.name if family == "egglog corpus" else ""
            for profile in profiles:
                requests.append(TranslationRequest(files[display], profile, family, project, no_aliasing))
    records = translation_ast_records(
        requests,
        cache,
        collect=collect,
        compiler=compiler,
        timeout_sec=timeout_sec,
        memory_limit_bytes=memory_limit_bytes,
    )
    planned = [
        {
            "file": request.file.display_path,
            "file_sha256": request.file.sha256,
            "profile": request.profile,
            "no_aliasing": request.no_aliasing,
            "family": request.family,
            "project": request.project,
        }
        for request in requests
    ]
    safety = next((record for record in records if record["status"] in SAFETY_STATUSES), None)
    return {
        "status": "halted" if safety else "complete" if len(records) == len(planned) else "pending",
        "pipeline": TRANSLATION_PIPELINE,
        "inputs": planned,
        "records": list(records),
        "issue": f"collection halted after {safety['file']} ({safety['profile']}): {safety['row']['error']}"
        if safety
        else None,
    }


def translation_program_size_results(snapshot: dict[str, Any]) -> dict[str, Any]:
    """Retain every planned configuration while plotting successful deterministic counts."""
    indexed = {
        (record["file_sha256"], record["profile"], record["no_aliasing"]): record for record in snapshot["records"]
    }
    points, rows = [], []
    for planned in snapshot["inputs"]:
        record = indexed.get((planned["file_sha256"], planned["profile"], planned["no_aliasing"]))
        row = {
            **planned,
            "status": record["status"] if record else "pending",
            "configuration": (RESTRICTED_PASS_LABELS if planned["no_aliasing"] else PASS_LABELS)[planned["profile"]],
            "source_ast_nodes": None,
            "normalized_source_ast_nodes": None,
            "output_ast_nodes": None,
            "growth": None,
            "error": None,
        }
        if record:
            row.update(
                {
                    key: record["row"].get(key)
                    for key in (
                        "source_ast_nodes",
                        "normalized_source_ast_nodes",
                        "output_ast_nodes",
                        "error",
                        "error_stage",
                    )
                }
            )
            row["compiler_binary_sha256"] = record["compiler_binary_sha256"]
        x, y = row["source_ast_nodes"], row["output_ast_nodes"]
        if row["status"] == "ok" and x is not None and y is not None and x > 0 and y > 0:
            row["growth"] = y / x
            points.append(
                {
                    **row,
                    "x": x,
                    "y": y,
                    "workload": planned["file"],
                }
            )
        rows.append(row)
    coverage = []
    for profile, no_aliasing in (
        ("c", None),
        ("cp", None),
        ("d", None),
        ("dcp", None),
        ("s", True),
        ("scp", True),
        ("s", False),
        ("scp", False),
    ):
        matching = [row for row in rows if row["profile"] == profile and row["no_aliasing"] == no_aliasing]
        coverage.append(
            {
                "profile": profile,
                "no_aliasing": no_aliasing,
                "configuration": (RESTRICTED_PASS_LABELS if no_aliasing else PASS_LABELS)[profile],
                "planned": len(matching),
                **{
                    status: sum(row["status"] == status for row in matching)
                    for status in ("ok", "pending", "error", "failure", "timed-out", "memory-limited", "safety-failure")
                },
            }
        )
    return {
        "figure": "program-size",
        "metric": TRANSLATION_NOTE,
        "points": points,
        "rows": rows,
        "coverage": coverage,
        "translation_program_size_snapshot": snapshot,
    }


def translation_program_size_spec(results: dict[str, Any], *, width: int = 420, height: int = 260) -> dict[str, Any]:
    """Fit each log axis to its deterministic counts and clip multiplier guides."""
    xs = [point["x"] for point in results["points"]]
    ys = [point["y"] for point in results["points"]]
    x_domain = [min(xs) / 1.3, max(xs) * 1.3] if xs else [1, 1000000]
    y_domain = [min(ys) / 1.3, max(ys) * 1.3] if ys else [1, 1000000]
    axes = {
        "x": {
            "field": "x",
            "type": "quantitative",
            "title": "Input AST nodes",
            "scale": {"type": "log", "domain": x_domain},
            "axis": {"values": log_major_ticks(x_domain), "grid": False},
        },
        "y": {
            "field": "y",
            "type": "quantitative",
            "title": "Generated AST nodes",
            "scale": {"type": "log", "domain": y_domain},
            "axis": {"values": log_major_ticks(y_domain), "grid": False},
        },
    }
    color = {
        "field": "configuration",
        "type": "nominal",
        "scale": {
            "domain": list(PASS_COLORS),
            "range": list(PASS_COLORS.values()),
        },
        "legend": {"title": None, "orient": "bottom", "direction": "horizontal", "columns": 4, "labelFontSize": 10},
    }
    guides: list[dict[str, Any]] = []
    for factor in ratio_guide_factors([p["y"] / p["x"] for p in results["points"]]):
        low, high = max(x_domain[0], y_domain[0] / factor), min(x_domain[1], y_domain[1] / factor)
        if low < high:
            guides.append({"x": low, "x2": high, "y": low * factor, "y2": high * factor, "label": f"{factor:g}×"})
    return {
        "$schema": "https://vega.github.io/schema/vega-lite/v6.json",
        "width": width,
        "height": height,
        "layer": [
            {
                "data": {"values": guides},
                "mark": {"type": "rule", "stroke": "#888888", "strokeDash": [4, 3], "strokeWidth": 0.7},
                "encoding": {**axes, "x2": {"field": "x2"}, "y2": {"field": "y2"}},
            },
            {
                "data": {"values": ratio_guide_labels(guides, x_domain, y_domain, width, height, results["points"])},
                "mark": {"type": "text", "align": "right", "dy": -7, "fontSize": 10, "color": "#555555"},
                "encoding": {**axes, "text": {"field": "label"}},
            },
            {
                "data": {"values": results["points"]},
                "mark": {
                    "type": "circle",
                    "filled": True,
                    "opacity": 0.55,
                    "size": 18,
                    "stroke": "#333333",
                    "strokeWidth": 0.3,
                },
                "encoding": {
                    **axes,
                    "color": color,
                    "tooltip": [
                        {"field": key}
                        for key in (
                            "workload",
                            "configuration",
                            "family",
                            "project",
                            "x",
                            "y",
                            "growth",
                            "file_sha256",
                            "compiler_binary_sha256",
                        )
                    ],
                },
            },
        ],
        "config": {
            "font": "Arial",
            "axis": {
                "labelFontSize": 10,
                "titleFontSize": 11,
                "titleFontWeight": "normal",
                "grid": False,
            },
            "title": {"fontSize": 12, "fontWeight": "normal", "subtitleFontSize": 10},
            "legend": {"layout": {"bottom": {"anchor": "middle", "direction": "horizontal", "center": True}}},
            "view": {"stroke": None},
        },
    }


def export_translation_program_size(snapshot: dict[str, Any], destination: Path) -> tuple[Path, ...]:
    """Export the complete portable AST snapshot, graph specification and exact-value appendix."""
    results = translation_program_size_results(snapshot)
    columns = (
        "file",
        "profile",
        "no_aliasing",
        "configuration",
        "family",
        "project",
        "status",
        "source_ast_nodes",
        "normalized_source_ast_nodes",
        "output_ast_nodes",
        "growth",
        "error",
        "file_sha256",
        "compiler_binary_sha256",
    )
    output = io.StringIO()
    writer = csv.DictWriter(output, fieldnames=columns, extrasaction="ignore", lineterminator="\n")
    writer.writeheader()
    writer.writerows(results["rows"])
    coverage = [
        r"\begin{tabular}{lrrr}",
        r"\toprule",
        r"Configuration & Planned & Available & Pending/failed \\",
        r"\midrule",
    ]
    markdown = [
        TRANSLATION_NOTE,
        "",
        "| Configuration | Planned | Available | Pending/failed |",
        "| --- | ---: | ---: | ---: |",
    ]
    for row in results["coverage"]:
        label = row["configuration"].replace("′", r"$^\prime$")
        coverage.append(f"{label} & {row['planned']} & {row['ok']} & {row['planned'] - row['ok']}" + r" \\")
        markdown.append(f"| {row['configuration']} | {row['planned']} | {row['ok']} | {row['planned'] - row['ok']} |")
    coverage.extend((r"\bottomrule", r"\end{tabular}", ""))
    if snapshot.get("issue"):
        markdown.extend(("", snapshot["issue"]))
    contents = {
        "results.json": json.dumps(results, ensure_ascii=False, allow_nan=False, separators=(",", ":")) + "\n",
        "bound.vl.json": json.dumps(translation_program_size_spec(results), ensure_ascii=False, allow_nan=False) + "\n",
        "csv": output.getvalue(),
        "table.tex": "\n".join(coverage),
        "md": "\n".join(markdown) + "\n",
        "files.txt": "".join(
            f"{row['file']}\t{row['profile']}\t{row['no_aliasing']}\t{row['file_sha256']}\n" for row in results["rows"]
        ),
        "numbers.tex": (
            f"\\newcommand{{\\ProgramSizePlanned}}{{{len(results['rows'])}}}\n"
            f"\\newcommand{{\\ProgramSizeAvailable}}{{{len(results['points'])}}}\n"
        ),
    }
    destination.mkdir(parents=True, exist_ok=True)
    for suffix, content in contents.items():
        (destination / f"program-size.{suffix}").write_text(content)
    return tuple(destination / f"program-size.{suffix}" for suffix in contents)


def program_size_snapshot(files: tuple[FileSpec, ...], cache: Path, *, collect: bool) -> dict[str, Any]:
    """Resolve the current compiler when collecting; preserve missing cached coverage otherwise."""
    planned = [{"file": file.display_path, "file_sha256": file.sha256} for file in files]
    try:
        records = slotted_ast_records(files, cache, collect=collect)
    except ValueError as error:
        if collect:
            raise
        return {"status": "pending", "pipeline": PIPELINE, "inputs": planned, "records": [], "issue": str(error)}
    return {"status": "complete", "pipeline": PIPELINE, "inputs": planned, "records": list(records), "issue": None}


def export_program_size(snapshot: dict[str, Any], destination: Path) -> tuple[Path, ...]:
    """Reuse the AST renderer under new names without inspecting inputs or a compiler."""
    destination.mkdir(parents=True, exist_ok=True)
    names = {
        "ast.tex": "table.tex",
        "ast.json": "results.json",
        "ast.csv": "csv",
        "ast.md": "md",
        "files.txt": "files.txt",
    }
    records = snapshot["records"]
    if records:
        with tempfile.TemporaryDirectory(dir=destination) as scratch:
            folder = Path(scratch)
            for path in export_slotted_ast(records, folder):
                suffix = path.name.removeprefix("slotted-runtime.")
                if suffix == "ast.json":
                    report = json.loads(path.read_bytes())
                    report.update(
                        figure="slotted-program-size",
                        timing_identity="Compile-only compiler/input identities are independent of timing endpoints",
                        program_size_snapshot=snapshot,
                    )
                    path.write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n")
                os.replace(path, destination / f"slotted-program-size.{names[suffix]}")
    else:
        contents = {
            "table.tex": r"\fbox{\parbox{0.9\linewidth}{\centering Program-size compilation results pending.}}" + "\n",
            "results.json": json.dumps({"figure": "slotted-program-size", **snapshot}, ensure_ascii=False) + "\n",
            "csv": ",".join(COLUMNS) + "\n",
            "md": "Program-size compilation results pending.\n\n" + (snapshot.get("issue") or "") + "\n",
            "files.txt": "".join(f"{file['file']}\n" for file in snapshot["inputs"]),
        }
        for suffix, content in contents.items():
            (destination / f"slotted-program-size.{suffix}").write_text(content)
    return tuple(destination / f"slotted-program-size.{suffix}" for suffix in names.values())
