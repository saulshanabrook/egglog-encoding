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
    export_program_size,
    export_translation_program_size,
    program_size_snapshot,
    translation_program_size_snapshot,
)
from .pilot_results import BUNDLE_NAMES, PILOT_DATA_VERSION, coverage_tables, pilot_results, pilot_tex
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
                        "candidate_label": ("extlog_cp" if candidate == "proof-extraction" else "extlog_c")
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
    if not speedup:
        xs = ys = xs + ys
    x_domain = [min(xs) / 1.3, max(xs) * 1.3] if xs else [0.001, 1000]
    y_domain = [min(ys + [1]) / 1.3, max(ys + [1]) * 1.3] if speedup and ys else ([0.01, 100] if speedup else x_domain)
    if applications:
        labels = [info["label"] for info in snapshot["projects"].values()]
        colors = [info["color"] for info in snapshot["projects"].values()]
    else:
        labels = [
            f"{info['label']} ({info['candidate_label']})"
            for info in snapshot["experiments"]
            if info.get("scope", "extensions") == "extensions"
        ]
        colors = [info["color"] for info in snapshot["experiments"] if info.get("scope", "extensions") == "extensions"]
    color = {
        "field": "series",
        "type": "nominal",
        "scale": {"domain": labels, "range": colors},
        "legend": {"title": None, "orient": "bottom", "columns": 2, "labelLimit": 270, "labelFontSize": 10},
    }
    axes = {
        "x": {
            "field": "x",
            "type": "quantitative",
            "scale": {"type": "log", "domain": x_domain},
            "title": f"egglog {measurement}" if applications else f"Reference {measurement}",
        },
        "y": {
            "field": "y",
            "type": "quantitative",
            "scale": {"type": "log", "domain": y_domain},
            "title": "Speedup (reference / extlog)" if speedup else f"extlog {measurement}",
        },
    }
    layers: list[dict[str, Any]] = []
    guides = (
        [{"x": x_domain[0], "x2": x_domain[1], "y": 1, "y2": 1, "factor": "1×"}]
        if speedup
        else [
            {
                "x": x_domain[0],
                "x2": x_domain[1],
                "y": x_domain[0] * factor,
                "y2": x_domain[1] * factor,
                "factor": f"{factor:g}×",
            }
            for factor in (0.5, 1, 2, 10)
        ]
    )
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
    guide_labels: list[dict[str, Any]] = (
        [
            {
                "x": min(x_domain[1], y_domain[1] / factor) / 1.4,
                "y": min(x_domain[1] * factor, y_domain[1]) / 1.4,
                "label": f"{factor:g}×",
            }
            for factor in (0.5, 1, 2, 10)
        ]
        if not speedup
        else [{"x": x_domain[1] / 1.4, "y": 1, "label": "1×"}]
    )
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
                "mark": {"type": "rule", "opacity": 0.45, "strokeWidth": 0.65, "clip": True},
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
                "mark": {"type": "rule", "opacity": 0.45, "strokeWidth": 0.65, "clip": True},
                "encoding": {
                    "x": axes["x"],
                    "y": {**axes["y"], "field": "y_plot_low"},
                    "y2": {"field": "y_high"},
                    "color": color,
                },
            },
            {
                "mark": {
                    "type": "point",
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
                "tickCount": 6,
                "gridColor": "#e5e5e5",
                "gridWidth": 0.5,
            },
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
        if images:
            for extension in ("pdf", "svg", "png"):
                path = folder / f"program-size.{extension}"
                args = [*command, f"vl2{extension}", str(folder / "program-size.bound.vl.json"), str(path)]
                if extension == "png":
                    args.extend(("-s", "3"))
                subprocess.run(args, cwd=ROOT, check=True, stdout=sys.stderr, stderr=sys.stderr)
                if not path.is_file() or not path.stat().st_size:
                    raise ValueError(f"pilot AST renderer produced no {extension}")
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
                if pointer is not None and pointer.row == row
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
        )
        export_pilot(snapshot, args.output_dir.expanduser().resolve(), console)
        if not args.no_runs and collection_failed:
            return 2
    except (OSError, ValueError, KeyError, subprocess.SubprocessError) as error:
        console.print(f"error: {error}", markup=False)
        return 2
    return 0
