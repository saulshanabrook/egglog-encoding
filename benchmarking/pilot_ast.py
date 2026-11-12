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
from .translation_ast import PROFILES, SAFETY_STATUSES, TranslationRequest, translation_ast_records

PASS_LABELS = {
    "c": "corelog+c",
    "cp": "egglog+p",
    "d": "egglog+d",
    "dcp": "egglog+dp",
    "s": "egglog+s",
    "scp": "egglog+sp",
}
LEGACY_PASS_LABELS = {f"extlog_{profile}": label for profile, label in PASS_LABELS.items()}
PASS_COLORS = dict(
    zip(PASS_LABELS.values(), ("#0072b2", "#56b4e9", "#d55e00", "#cc79a7", "#e69f00", "#b59b00"), strict=True)
)
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
    for name, profiles, family in (
        ("corpus-congruence", ("c", "cp"), "Applications"),
        ("math", ("c", "cp"), "Math"),
        ("disequality", ("d", "dcp"), "Disequality"),
        ("slotted", ("s", "scp"), "Slotted restricted"),
    ):
        for display in experiments.get(name, {}).get("files", []):
            project = Path(display).parent.name if family == "Applications" else ""
            for profile in profiles:
                requests.append(
                    TranslationRequest(
                        files[display], profile, family, project, True if profile in ("s", "scp") else None
                    )
                )
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
                    "configuration": PASS_LABELS[planned["profile"]],
                    "workload": planned["file"],
                }
            )
        rows.append(row)
    coverage = [
        {
            "profile": profile,
            "planned": sum(row["profile"] == profile for row in rows),
            **{
                status: sum(row["profile"] == profile and row["status"] == status for row in rows)
                for status in ("ok", "pending", "error", "failure", "timed-out", "memory-limited", "safety-failure")
            },
        }
        for profile in PROFILES
    ]
    return {
        "figure": "program-size",
        "metric": TRANSLATION_NOTE,
        "points": points,
        "rows": rows,
        "coverage": coverage,
        "translation_program_size_snapshot": snapshot,
    }


def translation_program_size_spec(results: dict[str, Any]) -> dict[str, Any]:
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
        "legend": {"title": None, "orient": "bottom", "columns": 2, "labelLimit": 270, "labelFontSize": 10},
    }
    guides: list[dict[str, Any]] = []
    for factor in (1, 10, 100):
        low, high = max(x_domain[0], y_domain[0] / factor), min(x_domain[1], y_domain[1] / factor)
        if low < high:
            guides.append({"x": low, "x2": high, "y": low * factor, "y2": high * factor, "label": f"{factor}×"})
    complete, total = len(results["points"]), len(results["rows"])
    return {
        "$schema": "https://vega.github.io/schema/vega-lite/v6.json",
        "width": 460,
        "height": 350,
        "title": {
            "text": "Compiler output program size",
            "subtitle": [
                f"{complete}/{total} input/configurations available; deterministic compile-only counts",
                "Whole-program representation, including emitted scaffolding; failed/pending cases remain in coverage.",
            ],
        },
        "layer": [
            {
                "data": {"values": guides},
                "mark": {"type": "rule", "stroke": "#888888", "strokeDash": [4, 3], "strokeWidth": 0.7},
                "encoding": {**axes, "x2": {"field": "x2"}, "y2": {"field": "y2"}},
            },
            {
                "data": {
                    "values": [
                        {
                            "x": row["x2"] * (row["x"] / row["x2"]) ** 0.08,
                            "y": row["y2"] * (row["y"] / row["y2"]) ** 0.08,
                            "label": row["label"],
                        }
                        for row in guides
                    ]
                },
                "mark": {"type": "text", "align": "right", "dy": -7, "fontSize": 10, "color": "#555555"},
                "encoding": {**axes, "text": {"field": "label"}},
            },
            {
                "data": {"values": results["points"]},
                "mark": {
                    "type": "circle",
                    "filled": True,
                    "opacity": 0.7,
                    "size": 35,
                    "stroke": "#333333",
                    "strokeWidth": 0.45,
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
                "grid": False,
            },
            "view": {"stroke": None},
        },
    }


def export_translation_program_size(snapshot: dict[str, Any], destination: Path) -> tuple[Path, ...]:
    """Export the complete portable AST snapshot, graph specification and exact-value appendix."""
    results = translation_program_size_results(snapshot)
    columns = (
        "file",
        "profile",
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
        coverage.append(
            f"{PASS_LABELS[row['profile']]} & {row['planned']} & {row['ok']} & {row['planned'] - row['ok']}" + r" \\"
        )
        markdown.append(
            f"| {PASS_LABELS[row['profile']]} | {row['planned']} | {row['ok']} | {row['planned'] - row['ok']} |"
        )
    coverage.extend((r"\bottomrule", r"\end{tabular}", ""))
    if snapshot.get("issue"):
        markdown.extend(("", snapshot["issue"]))
    contents = {
        "results.json": json.dumps(results, ensure_ascii=False, allow_nan=False, separators=(",", ":")) + "\n",
        "bound.vl.json": json.dumps(translation_program_size_spec(results), ensure_ascii=False, allow_nan=False) + "\n",
        "csv": output.getvalue(),
        "table.tex": "\n".join(coverage),
        "md": "\n".join(markdown) + "\n",
        "files.txt": "".join(f"{row['file']}\t{row['profile']}\t{row['file_sha256']}\n" for row in results["rows"]),
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
