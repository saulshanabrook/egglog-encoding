"""Collect and export the coverage-preserving, three-observation evaluation pilot.

Legacy figure publication remains strict. This entrypoint is selected explicitly
with ``bench.py figures --pilot`` and exports all six coordinated views from one
snapshot, even when the selected collection scope is still incomplete.
"""

from __future__ import annotations

import argparse
import glob
import gzip
import json
import os
import re
import shlex
import shutil
import subprocess
import sys
import tempfile
from collections.abc import Sequence
from dataclasses import asdict, replace
from pathlib import Path
from typing import Any, cast

from rich.console import Console

from .collection import (
    BenchmarkRequest,
    collect,
    plan_collection,
    resolve_requests,
    select_proof_validation,
    validate_proof_requests,
)
from .config import DEFAULT_MEMORY_LIMIT_BYTES, DEFAULT_TIMEOUT_SEC
from .engines import PROOF_ORACLES, TREATMENT_SPECS, TREATMENTS, Treatment
from .figures import ROOT, VEGA_PACKAGES, _figure_inventory, renderer_metadata
from .models import BenchmarkEndpoint, BuiltBinary, EndpointRequest, FileSpec, ResolvedTarget
from .native_memory import add_memory_limit_options
from .pilot_ast import (
    PASS_COLORS,
    export_program_size,
    export_translation_program_size,
    log_major_ticks,
    program_size_snapshot,
    translation_program_size_results,
    translation_program_size_snapshot,
    translation_program_size_spec,
)
from .pilot_results import BUNDLE_NAMES, PILOT_DATA_VERSION, coverage_tables, pilot_results, pilot_tex
from .proof_validation import read_proof_source_bindings, read_proof_validation, select_remote_proof_validation
from .reports.catalog import report_id
from .reports.store import ReportStore, select_observations
from .targets import parse_target, sha256_file, target_row_for_request
from .workloads import resolve_files

DEFAULT_CONFIG = ROOT / "figures/pilot.json"
DEFAULT_REPORT = ROOT / "data-cache/claims-eval-pilot.jsonl"
DEFAULT_OUTPUT = ROOT / "figures/output/claims-eval-pilot"


def freeze_target(target: ResolvedTarget, directory: Path) -> ResolvedTarget:
    """Bind collection to verified immutable copies rather than mutable build outputs."""
    binaries = target.binaries or (
        BuiltBinary(target.primary_binary or "egglog-experimental", target.binary_sha256, target.binary_path),
    )
    frozen = []
    for binary in binaries:
        if binary.path is None:
            frozen.append(binary)
            continue
        destination = directory / binary.sha256.removeprefix("sha256:") / binary.path.name
        destination.parent.mkdir(parents=True, exist_ok=True)
        if not destination.is_file():
            with tempfile.TemporaryDirectory(dir=destination.parent) as scratch:
                staged = Path(scratch) / binary.path.name
                shutil.copyfile(binary.path, staged)
                if sha256_file(staged) != binary.sha256:
                    raise ValueError(f"build output changed before freezing {binary.binary_name}")
                staged.chmod(0o555)
                os.replace(staged, destination)
        if sha256_file(destination) != binary.sha256:
            raise ValueError(f"frozen executable identity changed: {destination}")
        frozen.append(replace(binary, path=destination))
    primary = next(
        binary for binary in frozen if binary.binary_name == (target.primary_binary or frozen[0].binary_name)
    )
    return replace(target, binary_path=primary.path, binaries=tuple(frozen), primary_binary=primary.binary_name)


def load_experiments(path: Path) -> tuple[dict[str, Any], dict[str, FileSpec]]:
    """Resolve each heterogeneous series once, retaining all planned inputs."""
    config = json.loads(path.read_bytes())
    if {experiment["id"] for experiment in config["experiments"]} != {
        "math",
        "math-proofs",
        "slotted",
        "slotted-proofs",
        "slotted-complete",
        "slotted-complete-proofs",
        "disequality",
        "disequality-proofs",
        "corpus-congruence",
    }:
        raise ValueError("pilot catalog must name all nine experiments")
    files: dict[str, FileSpec] = {}
    for experiment in config["experiments"]:
        if experiment["candidate"] not in TREATMENTS or (
            experiment["reference"] is not None and experiment["reference"] not in TREATMENTS
        ):
            raise ValueError(f"unknown pilot endpoint in {experiment['id']}")
        selected: list[str] = []
        for pattern in experiment["files"]:
            matches = sorted(glob.glob(str(path.parent / pattern)))
            if not matches:
                raise ValueError(f"{experiment['id']}: input pattern matched nothing: {pattern}")
            for match in matches:
                source = Path(match).resolve()
                display = os.path.relpath(source, ROOT)
                if display not in files:
                    file = resolve_files([str(source)], ROOT)[0]
                    config.setdefault("table_expectations", {})[file.sha256] = [
                        asdict(rule) for rule in file.exclusions if rule.kind == "expected-failure"
                    ]
                    # Table-count expectations remain coverage metadata; they do
                    # not suppress executable workloads from performance plots.
                    aliases: dict[Treatment, Treatment] = {
                        "proof-extraction": "proof-testing",
                        "slotted-proof-extraction": "slotted",
                        "slotted-proof-testing": "slotted",
                        "slotted-proof-extraction-no-aliasing": "slotted-no-aliasing",
                        "slotted-proof-testing-no-aliasing": "slotted-no-aliasing",
                        "slotted-ref-multi-proofs": "slotted-ref-multi",
                        "slotted-ref-multi-proof-testing": "slotted-ref-multi",
                        "slotted-ref-nested-proofs": "slotted-ref-nested",
                        "slotted-ref-nested-proof-testing": "slotted-ref-nested",
                    }
                    exclusions = tuple(
                        replace(
                            rule,
                            treatments=tuple(
                                dict.fromkeys(
                                    (
                                        *rule.treatments,
                                        *(
                                            name
                                            for name, original in aliases.items()
                                            if original in rule.treatments
                                            # Checked replay limits do not bound production-only performance.
                                            and not (name == "proof-extraction" and rule.kind == "resource")
                                            and not any(name in explicit.treatments for explicit in file.exclusions)
                                        ),
                                    )
                                )
                            ),
                        )
                        for rule in file.exclusions
                        if rule.kind != "expected-failure"
                    )
                    file = replace(
                        file,
                        display_path=display,
                        exclusions=exclusions,
                        binary_inputs=tuple(
                            (
                                binary,
                                replace(
                                    physical,
                                    display_path=os.path.relpath(physical.absolute_path, ROOT),
                                    exclusions=exclusions,
                                ),
                            )
                            for binary, physical in file.binary_inputs
                        ),
                    )
                    files[display] = file
                if display not in selected:
                    selected.append(display)
        experiment["files"] = selected
    return config, files


def make_snapshot(
    config: dict[str, Any],
    files: dict[str, FileSpec],
    store: ReportStore,
    target: ResolvedTarget,
    *,
    rounds: int,
    threads: int,
    timeout_sec: int,
    memory_limit_bytes: int | None,
    ast_snapshot: dict[str, Any] | None = None,
    translation_ast_snapshot: dict[str, Any] | None = None,
    validation_evidence: Sequence[dict[str, Any]] = (),
    proof_source_bindings: dict[str, str] | None = None,
) -> dict[str, Any]:
    """Freeze selected timed rows, checked evidence, corpus provenance, and scope."""
    inventory = _figure_inventory(ROOT, tuple(files.values()))
    metadata = {row["file_sha256"]: row for row in inventory["workloads"]}
    corpus = next(
        experiment["files"] for experiment in config["experiments"] if experiment["id"] == "corpus-congruence"
    )
    sources = json.loads((ROOT / "benchmarks/corpus/manifest.json").read_bytes())["sources"]
    file_metadata = {}
    for display, file in files.items():
        info: dict[str, Any] = dict(metadata[file.sha256]) if file.sha256 in metadata else {}
        project = info.get("family", "") if display in corpus else ""
        source = file.absolute_path.read_text()
        # Count source LOC including initialization facts, never lowered output.
        clean = re.sub(
            r'"(?:\\.|[^"\\])*"|;[^\n]*', lambda match: match.group() if match.group().startswith('"') else "", source
        )
        file_metadata[display] = {
            "logical_id": file.sha256,
            "path": display,
            "label": info.get("label", Path(display).stem),
            "project": project,
            "input_loc": sum(bool(line.strip()) for line in clean.splitlines()),
            "table_correspondence": "known-difference"
            if config.get("table_expectations", {}).get(file.sha256)
            else "not-checked",
            "ordinary_output_parity": "not-compared",
        }
    binaries = {binary.binary_name: binary.sha256 for binary in target.binaries}
    if not binaries and target.binary_sha256:
        binaries[target.primary_binary or "egglog-experimental"] = target.binary_sha256
    # A staged collection can build only one engine. Retain other frozen engine
    # bindings from this exact source identity when exporting the shared snapshot.
    if target.row.label is not None:
        for binary in dict.fromkeys(spec.binary_name for spec in TREATMENT_SPECS.values()):
            pointer = store.find_label_pointer(target.row.label, binary)
            if binary not in binaries and pointer is not None and pointer.row == target.row:
                binaries[binary] = pointer.binary_sha256
    conditions: dict[str, dict[str, Any]] = {}
    comparisons = []
    for experiment in config["experiments"]:
        pairs = [(experiment.get("scope", "extensions"), experiment["reference"], experiment["candidate"])]
        if experiment["id"] == "corpus-congruence":
            pairs.append(("applications", "off", "proof-extraction"))
        for scope, reference, candidate in pairs:
            for display in experiment["files"]:
                file = files[display]
                info = file_metadata[display]
                endpoints = []
                for treatment in (reference, candidate):
                    if treatment is None:
                        identifier = report_id("pending-reference", experiment["id"], file.sha256)
                        endpoints.append(identifier)
                        conditions[identifier] = {
                            "id": identifier,
                            **info,
                            "treatment": "pending",
                            "binary_sha256": None,
                            "file_sha256": file.sha256,
                            "threads": 1,
                            "requested_threads": threads,
                            "observations": [],
                            "exclusion": None,
                            "validation": None,
                        }
                        continue
                    binary = TREATMENT_SPECS[treatment].binary_name
                    binary_sha = binaries.get(binary)
                    endpoint = BenchmarkEndpoint(
                        target.row, binary_sha or "unavailable", treatment, memory_limit_bytes, threads
                    )
                    physical = file.for_binary(binary)
                    identifier = report_id(binary_sha, physical.sha256, treatment, endpoint.threads)
                    endpoints.append(identifier)
                    if identifier in conditions:
                        continue
                    selection = select_observations(store, endpoint, file, rounds, timeout_sec)
                    validation = None
                    if treatment in PROOF_ORACLES:
                        validation = select_proof_validation(store, endpoint, file, 3 * timeout_sec)
                        remote = select_remote_proof_validation(
                            validation_evidence, endpoint, file, source_bindings=proof_source_bindings
                        )
                        if remote is not None:
                            validation = {**remote, "local_evidence": validation}
                    conditions[identifier] = {
                        "id": identifier,
                        **info,
                        "treatment": treatment,
                        "binary_sha256": binary_sha,
                        "file_sha256": physical.sha256,
                        "threads": endpoint.threads,
                        "requested_threads": endpoint.requested_threads,
                        "observations": [{**row.record, "row_index": row.row_index} for row in selection.rows],
                        "exclusion": asdict(selection.exclusion) if selection.exclusion else None,
                        "validation": validation,
                    }
                project = info["project"]
                series = f"{experiment['label']} ({experiment['candidate_label']})"
                if scope == "applications":
                    series = config["projects"][project]["label"]
                comparisons.append(
                    {
                        "scope": scope,
                        "experiment": experiment["id"],
                        "series": series,
                        "project": project,
                        "logical_id": file.sha256,
                        "label": info["label"],
                        "candidate_label": ("egglog+p" if candidate == "proof-extraction" else "corelog+c")
                        if scope == "applications"
                        else experiment["candidate_label"],
                        "reference_label": experiment["reference_label"],
                        "baseline": endpoints[0],
                        "candidate": endpoints[1],
                    }
                )
    return {
        "pilot_data_version": PILOT_DATA_VERSION,
        "rounds": rounds,
        "requested_threads": threads,
        "timeout_sec": timeout_sec,
        "memory_limit_bytes": memory_limit_bytes,
        "experiments": config["experiments"],
        "projects": {
            key: {"id": key, **value, "provenance": sources.get(key)} for key, value in config["projects"].items()
        },
        "files": list(file_metadata.values()),
        "conditions": list(conditions.values()),
        "comparisons": comparisons,
        "program_size": ast_snapshot or {"status": "pending", "inputs": [], "records": [], "issue": None},
        "translation_program_size": translation_ast_snapshot
        or {"status": "pending", "inputs": [], "records": [], "issue": None},
        "provenance": {
            "target": asdict(target.row),
            "binaries": binaries,
            "executable_paths": {
                binary.binary_name: str(binary.path) if binary.path else None for binary in target.binaries
            },
            "source_blockers": inventory["unavailable_cases"],
            "proof_timing": "recording, extraction, materialization and simplification; no verifier or serialization",
            "proof_validation": "best-effort separate strict replay; remote runs supply validity evidence only",
            "disequality_proof_scope": (
                "encoded/generated-name equality axioms and disequality witness; no source lifting"
            ),
            "rounds": rounds,
            "requested_threads": threads,
            "timeout_sec": timeout_sec,
            "memory_limit_bytes": memory_limit_bytes,
        },
    }


def bound_spec(results: dict[str, Any]) -> dict[str, Any]:
    """Bind a shared declarative scatter template to the selected pilot points."""
    snapshot = results["pilot_snapshot"]
    applications = results["figure"].startswith("applications-")
    speedup = results["figure"].endswith("-speedup")
    memory = results["metric"] == "memory"
    measurement = "peak RSS (MiB)" if memory else "runtime (s)"
    points = results["points"]
    xs = [
        point[field]
        for point in points
        for field in ("x", "x_low", "x_high")
        if point[field] is not None and point[field] > 0
    ]
    ys = [
        point[field]
        for point in points
        for field in ("y", "y_low", "y_high")
        if point[field] is not None and point[field] > 0
    ]
    x_domain = [min(xs) / 1.3, max(xs) * 1.3] if xs else [0.001, 1000]
    y_domain = [min(ys) / 1.3, max(ys) * 1.3] if ys else ([0.01, 100] if speedup else [0.001, 1000])
    if applications:
        labels = [info["label"] for info in snapshot["projects"].values()]
        colors = [info["color"] for info in snapshot["projects"].values()]
    else:
        labels = list(PASS_COLORS)
        colors = list(PASS_COLORS.values())
    color = {
        "field": "series" if applications else "configuration",
        "type": "nominal",
        "scale": {"domain": labels, "range": colors},
        "legend": {"title": None, "orient": "bottom", "columns": 2, "labelLimit": 270, "labelFontSize": 10},
    }
    axes = {
        "x": {
            "field": "x",
            "type": "quantitative",
            "scale": {"type": "log", "domain": x_domain},
            "axis": {"values": log_major_ticks(x_domain), "grid": False},
            "title": f"egglog {measurement}" if applications else f"Reference {measurement}",
        },
        "y": {
            "field": "y",
            "type": "quantitative",
            "scale": {"type": "log", "domain": y_domain},
            "axis": {"values": log_major_ticks(y_domain), "grid": False},
            "title": "Speedup (reference / candidate)"
            if speedup
            else f"{'egglog+p' if applications else 'Our'} {measurement}",
        },
    }
    layers: list[dict[str, Any]] = []
    guides: list[dict[str, Any]] = []
    if speedup:
        for factor in (0.5, 1, 2, 5, 10):
            if y_domain[0] <= factor <= y_domain[1]:
                guides.append(
                    {"x": x_domain[0], "x2": x_domain[1], "y": factor, "y2": factor, "factor": f"{factor:g}×"}
                )
    else:
        for factor in (0.5, 1, 2, 5, 10):
            low, high = max(x_domain[0], y_domain[0] / factor), min(x_domain[1], y_domain[1] / factor)
            if low < high:
                guides.append({"x": low, "x2": high, "y": low * factor, "y2": high * factor, "factor": f"{factor:g}×"})
    layers.append(
        {
            "data": {"values": guides},
            "mark": {"type": "rule", "stroke": "#888888", "strokeDash": [4, 3], "strokeWidth": 0.7, "clip": True},
            "encoding": {
                "x": axes["x"],
                "x2": {"field": "x2"},
                "y": axes["y"],
                "y2": {"field": "y2"},
                "tooltip": {"field": "factor"},
            },
        }
    )
    guide_labels = [
        {
            "x": row["x2"] * (row["x"] / row["x2"]) ** 0.08,
            "y": row["y2"] * (row["y"] / row["y2"]) ** 0.08,
            "label": row["factor"],
        }
        for row in guides
    ]
    layers.append(
        {
            "data": {
                "values": [
                    row
                    for row in guide_labels
                    if x_domain[0] <= row["x"] <= x_domain[1] and y_domain[0] <= row["y"] <= y_domain[1]
                ]
            },
            "mark": {"type": "text", "align": "right", "dy": -7, "fontSize": 10, "color": "#555555"},
            "encoding": {"x": axes["x"], "y": axes["y"], "text": {"field": "label"}},
        }
    )
    layers.extend(
        [
            {
                "transform": [
                    {"filter": "isValid(datum.x_low) && isValid(datum.x_high)"},
                    {"calculate": f"max(datum.x_low, {x_domain[0]})", "as": "x_plot_low"},
                ],
                "mark": {"type": "rule", "opacity": 0.28, "strokeWidth": 0.4, "clip": True},
                "encoding": {
                    "x": {**axes["x"], "field": "x_plot_low"},
                    "x2": {"field": "x_high"},
                    "y": axes["y"],
                    "color": color,
                },
            },
            {
                "transform": [
                    {"filter": "isValid(datum.y_low) && isValid(datum.y_high)"},
                    {"calculate": f"max(datum.y_low, {y_domain[0]})", "as": "y_plot_low"},
                ],
                "mark": {"type": "rule", "opacity": 0.28, "strokeWidth": 0.4, "clip": True},
                "encoding": {
                    "x": axes["x"],
                    "y": {**axes["y"], "field": "y_plot_low"},
                    "y2": {"field": "y_high"},
                    "color": color,
                },
            },
            {
                "mark": {
                    "type": "circle",
                    "filled": True,
                    "opacity": 0.75,
                    "size": 30,
                    "stroke": "#333333",
                    "strokeWidth": 0.45,
                },
                "encoding": {
                    **axes,
                    "color": color,
                    "tooltip": [
                        {"field": key}
                        for key in (
                            "series",
                            "configuration",
                            "workload",
                            "x",
                            "x_low",
                            "x_high",
                            "y",
                            "y_low",
                            "y_high",
                            "interval_issue",
                            "reference_threads",
                            "candidate_threads",
                            "reference_n",
                            "candidate_n",
                            "proof_validation_status",
                            "proof_validation_issue",
                        )
                    ],
                },
            },
        ]
    )
    complete = len(points)
    total = len(results["comparisons"])
    return {
        "$schema": "https://vega.github.io/schema/vega-lite/v6.json",
        "width": 460,
        "height": 350,
        "title": {
            "text": "Proofs for existing egglog programs"
            if applications
            else "Compiler passes versus integrated systems",
            "subtitle": [
                f"{results['rounds']} observations per configuration; {complete}/{total} comparisons available",
                "95% mean-runtime and Fieller ratio intervals; pending and failed cases remain in coverage."
                if speedup
                else f"Marginal 95% mean {'peak-RSS' if memory else 'runtime'} intervals; "
                "pending and failed cases remain in coverage.",
            ]
            + (
                ["CI limits at or below zero are clipped to the log-axis boundary."]
                if any(
                    point[field] is not None and point[field] <= 0 for point in points for field in ("x_low", "y_low")
                )
                else []
            ),
        },
        "data": {"values": points},
        "layer": layers,
        "config": {
            "font": "Arial",
            "axis": {
                "labelFontSize": 10,
                "titleFontSize": 11,
                "titleFontWeight": "normal",
                "grid": False,
            },
            "title": {"fontSize": 12, "fontWeight": "normal", "subtitleFontSize": 10},
            "view": {"stroke": None},
        },
    }


def paired_runtime_size_spec(runtime: dict[str, Any], sizes: dict[str, Any]) -> dict[str, Any]:
    """Place runtime and representation growth beside one shared pass legend."""
    panels = [bound_spec(runtime), translation_program_size_spec(sizes)]
    for panel, title, subtitle in zip(
        panels,
        ("(a) Runtime", "(b) Program size"),
        (
            f"{len(runtime['points'])}/{len(runtime['comparisons'])} pairs; mean and 95% CI",
            f"{len(sizes['points'])}/{len(sizes['rows'])} configurations; deterministic",
        ),
        strict=True,
    ):
        panel.pop("$schema")
        panel.pop("config")
        panel.update(
            width=205,
            height=185,
            title={
                "text": title,
                "subtitle": subtitle,
                "fontSize": 11,
                "fontWeight": "normal",
                "subtitleFontSize": 9.5,
            },
        )
        for layer in panel["layer"]:
            for axis in ("x", "y"):
                axis_spec = layer["encoding"][axis]["axis"]
                ticks = axis_spec["values"]
                axis_spec["values"] = ticks[:: max(1, (len(ticks) + 3) // 4)]
                if title == "(b) Program size":
                    axis_spec["format"] = ".0s"
            if "color" in layer["encoding"]:
                layer["encoding"]["color"]["legend"] = {
                    "title": None,
                    "orient": "bottom",
                    "columns": 3,
                    "labelFontSize": 9.5,
                    "symbolSize": 35,
                }
            if layer["mark"]["type"] == "text":
                layer["mark"].update(fontSize=9.5, dy=-5)
            elif layer["mark"]["type"] == "circle":
                layer["mark"]["size"] = 20
    return {
        "$schema": "https://vega.github.io/schema/vega-lite/v6.json",
        "hconcat": panels,
        "spacing": 24,
        "resolve": {
            "scale": {"x": "independent", "y": "independent", "color": "shared"},
            "legend": {"color": "shared"},
        },
        "config": {
            "font": "Arial",
            "axis": {"labelFontSize": 9.5, "titleFontSize": 11, "titleFontWeight": "normal", "grid": False},
            "view": {"stroke": None},
        },
    }


def export_pilot(
    snapshot: dict[str, Any], destination: Path, console: Console, *, images: bool = True
) -> tuple[Path, ...]:
    """Render all coordinated assets before replacing any previous pilot output."""
    destination.mkdir(parents=True, exist_ok=True)
    outputs = []
    renderer = renderer_metadata()
    command = [*shlex.split(os.environ.get("NPX", "npx --yes")), *[f"--package={package}" for package in VEGA_PACKAGES]]
    with tempfile.TemporaryDirectory(dir=destination, prefix=".pilot.") as temporary:
        folder = Path(temporary)
        for name in BUNDLE_NAMES:
            result = pilot_results(snapshot, name)
            result["renderer"] = renderer
            spec = bound_spec(result)
            numbers, table = pilot_tex(result)
            for suffix, value in (
                ("results.json", json.dumps(result, ensure_ascii=False, allow_nan=False, separators=(",", ":")) + "\n"),
                ("bound.vl.json", json.dumps(spec, ensure_ascii=False, allow_nan=False, separators=(",", ":")) + "\n"),
                ("numbers.tex", numbers),
                ("table.tex", table),
            ):
                path = folder / f"{name}.{suffix}"
                path.write_text(value)
                outputs.append(path.name)
            if images:
                for extension in ("pdf", "svg", "png"):
                    path = folder / f"{name}.{extension}"
                    args = [*command, f"vl2{extension}", str(folder / f"{name}.bound.vl.json"), str(path)]
                    if extension == "png":
                        args.extend(("-s", "3"))
                    subprocess.run(args, cwd=ROOT, check=True, stdout=sys.stderr, stderr=sys.stderr)
                    if not path.is_file() or not path.stat().st_size:
                        raise ValueError(f"pilot renderer produced no {extension}")
                    outputs.append(path.name)
        for name, value in coverage_tables(snapshot).items():
            (folder / name).write_text(value)
            outputs.append(name)
        outputs.extend(
            path.name
            for path in export_program_size(
                snapshot.get("program_size", {"status": "pending", "inputs": [], "records": [], "issue": None}),
                folder,
            )
        )
        outputs.extend(
            path.name
            for path in export_translation_program_size(
                snapshot.get(
                    "translation_program_size", {"status": "pending", "inputs": [], "records": [], "issue": None}
                ),
                folder,
            )
        )
        runtime = pilot_results(snapshot, "extensions-runtime")
        sizes = translation_program_size_results(
            snapshot.get("translation_program_size", {"status": "pending", "inputs": [], "records": [], "issue": None})
        )
        paired = {
            "figure": "extensions-runtime-size",
            "runtime": {key: value for key, value in runtime.items() if key != "pilot_snapshot"},
            "program_size": sizes,
            "pilot_snapshot": snapshot,
            "renderer": renderer,
        }
        for suffix, value in (
            ("results.json", json.dumps(paired, ensure_ascii=False, allow_nan=False, separators=(",", ":")) + "\n"),
            (
                "bound.vl.json",
                json.dumps(paired_runtime_size_spec(runtime, sizes), ensure_ascii=False, allow_nan=False) + "\n",
            ),
        ):
            path = folder / f"extensions-runtime-size.{suffix}"
            path.write_text(value)
            outputs.append(path.name)
        if images:
            for stem in ("program-size", "extensions-runtime-size"):
                for extension in ("pdf", "svg", "png"):
                    path = folder / f"{stem}.{extension}"
                    args = [*command, f"vl2{extension}", str(folder / f"{stem}.bound.vl.json"), str(path)]
                    if extension == "png":
                        args.extend(("-s", "3"))
                    subprocess.run(args, cwd=ROOT, check=True, stdout=sys.stderr, stderr=sys.stderr)
                    if not path.is_file() or not path.stat().st_size:
                        raise ValueError(f"pilot {stem} renderer produced no {extension}")
                    outputs.append(path.name)
        for name in outputs:
            os.replace(folder / name, destination / name)
    console.print(f"Exported pilot ({snapshot['rounds']} observations requested) to {destination}", markup=False)
    return tuple(destination / name for name in outputs)


def main(argv: Sequence[str] | None = None) -> int:
    """Collect the selected pilot scope or replay its portable snapshot offline."""
    parser = argparse.ArgumentParser(prog="./bench.py figures --pilot")
    parser.add_argument("names", nargs="*", help="collection scopes; all six coordinated views are exported")
    parser.add_argument("--config", type=Path, default=DEFAULT_CONFIG)
    parser.add_argument("--rounds", type=int, default=3)
    parser.add_argument("--threads", type=int, default=4)
    parser.add_argument("--timeout-sec", type=int, default=DEFAULT_TIMEOUT_SEC)
    parser.add_argument("--target", default=f"claims-eval-pilot={ROOT}")
    parser.add_argument("--report", type=Path, default=DEFAULT_REPORT)
    parser.add_argument("--output-dir", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--ast-cache", type=Path, help="compile-only size cache; default beside the report")
    parser.add_argument(
        "--translation-ast-cache", type=Path, help="broad source/configuration AST cache; default beside the report"
    )
    parser.add_argument(
        "--translation-ast-compiler", type=Path, help="use this compiler executable for explicit AST collection"
    )
    parser.add_argument("--reuse-from", type=Path)
    parser.add_argument("--no-runs", action="store_true")
    parser.add_argument("--validation-only", action="store_true")
    parser.add_argument(
        "--proof-validation",
        type=Path,
        help="import delegated strict replay evidence; collect production locally without local validation",
    )
    parser.add_argument("--proof-source-receipt", type=Path, help="frozen production binary/source binding receipt")
    parser.add_argument("-v", "--verbose", action="store_true")
    add_memory_limit_options(parser, default=DEFAULT_MEMORY_LIMIT_BYTES)
    args = parser.parse_args(argv)
    if set(args.names) - {*BUNDLE_NAMES, "composition", "program-size", "translation-program-size"}:
        parser.error(
            "unknown pilot scope; choose "
            + ", ".join((*BUNDLE_NAMES, "composition", "program-size", "translation-program-size"))
        )
    if min(args.rounds, args.threads, args.timeout_sec) < 1 or str(args.report) == "-":
        parser.error("rounds, threads and timeout must be positive; --report requires a filesystem path")
    console = Console(stderr=True)
    try:
        if args.reuse_from is not None:
            if not args.no_runs:
                raise ValueError("pilot portable replay requires --no-runs; use --target for new collection")
            path = args.reuse_from / "extensions-runtime.results.json"
            if path.is_file():
                result = json.loads(path.read_bytes())
            else:
                with gzip.open(str(path) + ".gz", "rt") as handle:
                    result = json.load(handle)
            snapshot = result["pilot_snapshot"]
            if snapshot["pilot_data_version"] != PILOT_DATA_VERSION:
                raise ValueError("unsupported pilot snapshot version")
            export_pilot(snapshot, args.output_dir.resolve(), console)
            return 0
        config, files = load_experiments(args.config.resolve())
        requested = args.names or (*BUNDLE_NAMES, "composition", "program-size", "translation-program-size")
        extensions = any(name.startswith("extensions-") for name in requested)
        applications = any(name.startswith("applications-") for name in requested)
        composition = "composition" in requested
        target_request = parse_target(args.target)
        collect_sizes = "program-size" in requested and not args.no_runs
        collect_translation_sizes = "translation-program-size" in requested and not args.no_runs
        if (collect_sizes or collect_translation_sizes) and Path(target_request.source).expanduser().resolve() != ROOT:
            raise ValueError("program-size collection uses this checkout; supply --target LABEL=.")
        ast_files = next(experiment["files"] for experiment in config["experiments"] if experiment["id"] == "slotted")
        ast_snapshot = program_size_snapshot(
            tuple(files[path] for path in ast_files),
            (args.ast_cache or args.report.expanduser().resolve().parent / "slotted-program-size.jsonl").resolve(),
            collect=collect_sizes,
        )
        translation_snapshot = translation_program_size_snapshot(
            config,
            files,
            (
                args.translation_ast_cache
                or args.report.expanduser().resolve().parent / "translation-program-size.jsonl"
            ).resolve(),
            collect=collect_translation_sizes,
            compiler=args.translation_ast_compiler.expanduser().resolve() if args.translation_ast_compiler else None,
            timeout_sec=args.timeout_sec,
            memory_limit_bytes=args.memory_limit_bytes,
        )
        requests = []
        for experiment in config["experiments"]:
            treatments: set[Treatment] = set()
            if (extensions and experiment.get("scope", "extensions") == "extensions") or (
                composition and experiment.get("scope") == "composition"
            ):
                treatments.add(experiment["candidate"])
                if not experiment.get("reference_pending"):
                    treatments.add(experiment["reference"])
            if applications and experiment["id"] == "corpus-congruence":
                treatments.update(("off", "term", "proof-extraction"))
            for treatment in sorted(treatments):
                requests.append(
                    BenchmarkRequest(
                        EndpointRequest(
                            target_request, cast(Treatment, treatment), args.memory_limit_bytes, args.threads
                        ),
                        tuple(files[path] for path in experiment["files"]),
                    )
                )
        store = ReportStore(args.report.expanduser().resolve())
        collection_failed = collect_translation_sizes and translation_snapshot["status"] == "halted"
        if args.no_runs or not requests or collection_failed:
            pointers = [
                (binary, store.find_label_pointer(target_request.label or "claims-eval-pilot", binary))
                for binary in dict.fromkeys(spec.binary_name for spec in TREATMENT_SPECS.values())
            ]
            row = next((pointer.row for _, pointer in pointers if pointer is not None), None)
            if row is None:
                row = target_row_for_request(target_request, ROOT, "HEAD")
            binaries = tuple(
                BuiltBinary(binary, pointer.binary_sha256, None)
                for binary, pointer in pointers
                # Unchanged native executables retain their own source-row provenance.
                if pointer is not None
            )
            target = ResolvedTarget(
                target_request,
                row,
                binaries[0].sha256 if binaries else "",
                None,
                binaries,
                binaries[0].binary_name if binaries else None,
            )
        else:
            targets = resolve_requests(
                tuple(requests), store, args.rounds, args.timeout_sec, False, Path.cwd(), ROOT, console
            )
            target = targets[target_request]
            target = freeze_target(target, store.path.parent / "executables")
            targets[target_request] = target
            try:
                if not args.validation_only:
                    plans = plan_collection(store, tuple(requests), targets, args.rounds, args.timeout_sec, False)
                    collect(store, plans, tuple(requests), targets, args.timeout_sec, console, verbose=args.verbose)
                if args.proof_validation is None:
                    validate_proof_requests(store, tuple(requests), targets, args.timeout_sec, console)
            except (OSError, ValueError, subprocess.SubprocessError) as error:
                console.print(f"collection stopped: {error}", markup=False)
                collection_failed = True
        snapshot = make_snapshot(
            config,
            files,
            store,
            target,
            rounds=args.rounds,
            threads=args.threads,
            timeout_sec=args.timeout_sec,
            memory_limit_bytes=args.memory_limit_bytes,
            ast_snapshot=ast_snapshot,
            translation_ast_snapshot=translation_snapshot,
            validation_evidence=read_proof_validation(args.proof_validation) if args.proof_validation else (),
            proof_source_bindings=read_proof_source_bindings(
                args.proof_source_receipt or store.path.parent / "proof-base-candidate.json"
            ),
        )
        export_pilot(snapshot, args.output_dir.expanduser().resolve(), console)
        if not args.no_runs and collection_failed:
            return 2
    except (OSError, ValueError, KeyError, subprocess.SubprocessError) as error:
        console.print(f"error: {error}", markup=False)
        return 2
    return 0
