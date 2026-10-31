"""Collect a flat figure catalog with the shared benchmark pipeline, then render Vega."""

from __future__ import annotations

import argparse
import glob
import json
import os
import shlex
import subprocess
import sys
import tempfile
from collections.abc import Sequence
from copy import deepcopy
from dataclasses import dataclass, replace
from pathlib import Path
from time import perf_counter
from typing import Any, TypedDict

from rich.console import Console

from benchmarks.reproduction.corpus import MANIFEST_RELATIVE_PATH, VALIDATION_POLICY, load_manifest
from benchmarks.reproduction.native import NATIVE_ALLOCATION_FAILURE
from native_memory import NATIVE_LIMIT_BYTES

from .engines import TREATMENT_SPECS, TREATMENTS, Treatment
from .models import BenchmarkEndpoint, EndpointRequest, FileSpec, ResolvedTarget, validate_unique_file_identities
from .reports.grouped import grouped_report_path, write_grouped_report
from .reports.store import CacheKey, GroupedReport
from .targets import parse_target
from .workloads import resolve_files

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_CONFIG = ROOT / "figures/catalog.json"
VEGA_PACKAGES = ("vega@6.4.0", "vega-lite@6.4.3", "vega-cli@6.4.0", "canvas@3.2.3")


@dataclass(frozen=True)
class Figure:
    name: str
    spec: Path
    patterns: tuple[str, ...]
    treatments: tuple[Treatment, ...]


@dataclass(frozen=True)
class FigureConfig:
    path: Path
    rounds: int
    timeout_sec: int
    figures: tuple[Figure, ...]


@dataclass(frozen=True)
class ResolvedFigure:
    figure: Figure
    files: tuple[FileSpec, ...]
    spec: dict[str, Any]


class FigureWorkload(TypedDict):
    label: str
    family: str
    file_sha256: str
    fact_directory_sha256: str
    validation_failures: dict[str, str]


class FigureInventory(TypedDict):
    workloads: list[FigureWorkload]
    unavailable_cases: list[dict[str, Any]]


def _figure_inventory(root: Path, selected: Sequence[FileSpec] | None = None) -> FigureInventory:
    """Project saved corpus metadata without collecting or regenerating inputs."""

    directory = (root / MANIFEST_RELATIVE_PATH).parent.resolve()
    published = (
        None if selected is None else [file for file in selected if file.absolute_path.is_relative_to(directory)]
    )
    if published == []:
        return {"workloads": [], "unavailable_cases": []}
    # Figure selection has already hashed its files. Do not inspect unrelated
    # prepared inputs when a custom configuration selects a small subset.
    manifest = load_manifest(root)
    identities = None if published is None else {(file.sha256, file.fact_directory_sha256) for file in published}
    registered = {
        (directory / item["file"]).resolve(): (item["sha256"], item["facts_sha256"]) for item in manifest.workloads
    }
    if published is not None and any(
        registered.get(file.absolute_path) != (file.sha256, file.fact_directory_sha256) for file in published
    ):
        raise ValueError("selected published corpus input changed or is unregistered; review its manifest")
    cases = {case["id"]: case for case in manifest.cases}
    workloads: dict[tuple[str, str], FigureWorkload] = {}
    for source in manifest.workloads:
        identity = (source["sha256"], source["facts_sha256"])
        if identities is not None and identity not in identities:
            continue
        first = source["aliases"][0]
        case = cases[first["case"]]
        workloads[identity] = {
            "label": case["id"] + (f" / call {first['order'] + 1}" if len(case["workloads"]) > 1 else ""),
            "family": case["family"],
            "file_sha256": source["sha256"],
            "fact_directory_sha256": source["facts_sha256"],
            "validation_failures": {},
        }
    for outcome in manifest.outcomes:
        item = workloads.get((outcome["file_sha256"], outcome["fact_directory_sha256"]))
        if item is None or outcome["kind"] != "validation" or outcome["policy"] != VALIDATION_POLICY:
            continue
        key = f"{outcome['binary_sha256']}/{outcome['disequality_encoding']}"
        if outcome["status"] == "success":
            item["validation_failures"].pop(key, None)
        elif outcome["reason"] not in (
            NATIVE_ALLOCATION_FAILURE,
            f"timed out after {outcome['timeout_sec']:g} seconds",
        ):
            item["validation_failures"][key] = outcome["reason"] or "Strict proof validation failed"
    return {
        "workloads": list(workloads.values()),
        "unavailable_cases": [case for case in manifest.cases if case["status"] in ("blocked", "pending")],
    }


def _unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    """Reject duplicate declarations before JSON would silently overwrite them."""
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate configuration key: {key}")
        result[key] = value
    return result


def load_config(path: Path) -> FigureConfig:
    """Read the figure definitions without touching workloads."""
    path = path.expanduser().resolve()
    data = json.loads(path.read_text(), object_pairs_hook=_unique_object)
    if not isinstance(data, dict) or set(data) != {"rounds", "timeout_sec", "figures"}:
        raise ValueError("figure config requires exactly rounds, timeout_sec, and figures")
    for key in ("rounds", "timeout_sec"):
        if type(data[key]) is not int or data[key] < 1:
            raise ValueError(f"{key} must be a positive integer")
    if not isinstance(data["figures"], dict) or not data["figures"]:
        raise ValueError("figures must be a nonempty object of named figures")
    figures = []
    for name, item in data["figures"].items():
        if not name or Path(name).name != name or name in (".", ".."):
            raise ValueError(f"invalid figure name: {name!r}")
        if not isinstance(item, dict) or set(item) != {"spec", "files", "treatments"}:
            raise ValueError(f"{name}: requires exactly spec, files, and treatments")
        if not isinstance(item["spec"], str) or not item["spec"]:
            raise ValueError(f"{name}: spec must be a path")
        for key in ("files", "treatments"):
            if (
                not isinstance(item[key], list)
                or not item[key]
                or any(not isinstance(value, str) or not value for value in item[key])
            ):
                raise ValueError(f"{name}: {key} must be a nonempty list of strings")
        if len(set(item["treatments"])) != len(item["treatments"]):
            raise ValueError(f"{name}: duplicate treatment")
        unknown = set(item["treatments"]) - set(TREATMENTS)
        if unknown:
            raise ValueError(f"{name}: unknown treatments: {', '.join(sorted(unknown))}")
        figures.append(
            Figure(name, (path.parent / item["spec"]).resolve(), tuple(item["files"]), tuple(item["treatments"]))
        )
    return FigureConfig(path, data["rounds"], data["timeout_sec"], tuple(figures))


def parse_args(argv: Sequence[str]) -> tuple[argparse.Namespace, FigureConfig]:
    """Make configured names available in help without resolving files or builds."""
    preliminary = argparse.ArgumentParser(add_help=False)
    preliminary.add_argument("--config", type=Path, default=DEFAULT_CONFIG)
    known, _ = preliminary.parse_known_args(argv)
    try:
        config = load_config(known.config)
    except (OSError, ValueError, TypeError) as error:
        preliminary.error(str(error))
    parser = argparse.ArgumentParser(
        prog="./bench.py figures",
        description="Collect missing cached observations once, then render selected figures.",
        epilog="Configured figures:\n" + "\n".join(f"  {f.name}: {f.spec}" for f in config.figures),
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument("names", nargs="*", help="configured figure names (default: all)")
    parser.add_argument("--config", type=Path, default=DEFAULT_CONFIG, help="flat figure JSON catalog")
    parser.add_argument("-v", "--verbose", action="store_true", help="show phase timings and per-attempt starts")
    parser.add_argument(
        "--rounds", type=int, default=config.rounds, help="observations per condition (overrides catalog)"
    )
    parser.add_argument(
        "--target", default=f"figures={ROOT}", help="source target (default: this checkout, label figures)"
    )
    parser.add_argument("--report", type=Path, default=Path(".reports.jsonl"), help="append-only observation cache")
    parser.add_argument(
        "--output-dir", type=Path, help="common output directory (default: each specification directory)"
    )
    args = parser.parse_args(argv)
    if args.rounds < 1:
        parser.error("--rounds must be positive")
    if str(args.report) == "-":
        parser.error("--report requires a file path; '-' streaming is not supported")
    if len(args.names) != len(set(args.names)):
        parser.error("duplicate figure name")
    unknown = set(args.names) - {figure.name for figure in config.figures}
    if unknown:
        parser.error("unknown figure names: " + ", ".join(sorted(unknown)) + "; select a JSON catalog with --config")
    return args, replace(config, rounds=args.rounds)


def resolve_figures(config: FigureConfig, names: Sequence[str], invocation_cwd: Path) -> tuple[ResolvedFigure, ...]:
    """Resolve shared inputs once while preserving each figure's ordered scope."""
    result = []
    inputs: dict[Path, FileSpec] = {}
    specs: dict[Path, dict[str, Any]] = {}
    for figure in config.figures:
        if names and figure.name not in names:
            continue
        if figure.spec not in specs:
            if not figure.spec.is_file():
                raise ValueError(f"figure spec does not exist: {figure.spec}")
            spec = json.loads(figure.spec.read_bytes())
            if not isinstance(spec, dict) or not isinstance(spec.get("data"), dict) or not spec["data"].get("url"):
                raise ValueError(f"{figure.name}: specification must declare a primary data.url")
            specs[figure.spec] = spec
        paths: dict[Path, None] = {}
        for pattern in figure.patterns:
            matches = sorted(glob.glob(str(config.path.parent / pattern), recursive=True))
            if not matches:
                raise ValueError(f"{figure.name}: file pattern matched nothing: {pattern}")
            for match in matches:
                path = Path(match).resolve()
                if path not in inputs:
                    if not path.is_file():
                        raise ValueError(f"{figure.name}: not a workload file: {path}")
                    inputs[path] = resolve_files([os.path.relpath(path, invocation_cwd)], invocation_cwd, None)[0]
                paths[path] = None
        files = tuple(inputs[path] for path in paths)
        validate_unique_file_identities(files)
        result.append(ResolvedFigure(figure, files, specs[figure.spec]))
    return tuple(result)


def render_figures(
    figures: Sequence[ResolvedFigure],
    config: FigureConfig,
    grouped: GroupedReport,
    report_path: Path,
    target: ResolvedTarget,
    output_dir: Path | None,
    console: Console,
    inventory: FigureInventory,
) -> tuple[Path, ...]:
    """Bind shared sample selections and render Vega through temporary files."""
    from scipy import stats

    metadata = {(item["file_sha256"], item["fact_directory_sha256"]): item for item in inventory["workloads"]}
    label = target.row.label
    if label is None:
        raise ValueError("figure target must have a label")
    command = [*shlex.split(os.environ.get("NPX", "npx --yes")), *[f"--package={p}" for p in VEGA_PACKAGES]]
    rendered = []
    for resolved in figures:
        figure = resolved.figure
        selected_inputs = []
        incomplete = 0
        for file in resolved.files:
            info = metadata.get((file.sha256, file.fact_directory_sha256))
            for treatment in figure.treatments:
                physical = file.for_engine(TREATMENT_SPECS[treatment].engine)
                rows = grouped.latest_records(
                    CacheKey.for_endpoint(BenchmarkEndpoint(target, treatment), file),
                    config.rounds,
                    config.timeout_sec,
                    NATIVE_LIMIT_BYTES,
                )
                incomplete += len(rows) < config.rounds or any(row.record["status"] != "success" for row in rows)
                selected_inputs.append(
                    {
                        "logical_id": f"{file.sha256}/{file.fact_directory_sha256}",
                        "label": info["label"] if info else file.display_path,
                        "family": info["family"] if info else "",
                        "file_sha256": physical.sha256,
                        "fact_directory_sha256": physical.fact_directory_sha256,
                        "treatment": treatment,
                        "selected_row_indices": [row.row_index for row in rows],
                        "validation_failures": info["validation_failures"] if info else {},
                    }
                )
        bindings = {
            "target_label": label,
            "timeout_sec": config.timeout_sec,
            "rounds": config.rounds,
            "t_critical": None if config.rounds == 1 else float(stats.t.ppf(0.975, config.rounds - 1)),
            "selected_inputs": selected_inputs,
            "source_blockers": inventory["unavailable_cases"],
        }
        spec = deepcopy(resolved.spec)
        for parameter in spec.get("params", []):
            if parameter.get("name") in bindings:
                parameter["value"] = bindings[parameter["name"]]
        spec["data"]["url"] = grouped_report_path(report_path).as_uri()
        destination = (output_dir or figure.spec.parent).resolve()
        destination.mkdir(parents=True, exist_ok=True)
        outputs = [destination / f"{figure.name}.{extension}" for extension in ("pdf", "svg", "png")]
        console.print(f"Rendering {figure.name}", markup=False)
        # Render the complete set before replacing any existing image.
        with tempfile.TemporaryDirectory(dir=destination, prefix=f".{figure.name}.") as temporary:
            bound_path = Path(temporary) / f"{figure.name}.vl.json"
            bound_path.write_text(json.dumps(spec, ensure_ascii=False, indent=2) + "\n")
            for output in outputs:
                generated = Path(temporary) / output.name
                args = [
                    *command,
                    "vl2" + output.suffix[1:],
                    str(bound_path),
                    str(generated),
                    "--base",
                    str(figure.spec.parent),
                ]
                if output.suffix == ".png":
                    args += ["-s", "3"]
                subprocess.run(args, cwd=ROOT, check=True, stdout=sys.stderr, stderr=sys.stderr)
                if not generated.is_file() or not generated.stat().st_size:
                    raise ValueError(f"renderer produced no image: {output}")
            for output in outputs:
                os.replace(Path(temporary) / output.name, output)
        for output in outputs:
            console.print(str(output), soft_wrap=True, markup=False)
            rendered.append(output)
        if incomplete:
            console.print(
                f"{figure.name}: {incomplete}/{len(selected_inputs)} incomplete or unsuccessful conditions",
                markup=False,
            )
    return tuple(rendered)


def main(argv: Sequence[str] | None = None) -> int:
    """Use the ordinary shared benchmark phases for one deduplicated figure invocation."""
    raw = tuple(sys.argv[1:] if argv is None else argv)
    args, config = parse_args(raw)
    from .collection import BenchmarkRequest, collect, current_label_bindings, plan_collection, resolve_requests
    from .reports.store import ReportStore

    console = Console(stderr=True)
    try:
        cwd = Path.cwd()
        figure_count = len(args.names) or len(config.figures)
        console.print(
            f"Resolving inputs for {figure_count} figure{'s' if figure_count != 1 else ''} · "
            f"{config.rounds} sample{'s' if config.rounds != 1 else ''}/condition"
        )
        started = perf_counter()
        figures = resolve_figures(config, args.names, cwd)
        all_files = tuple(dict.fromkeys(file for figure in figures for file in figure.files))
        if args.verbose:
            input_count = len(all_files)
            console.print(
                f"  resolved {input_count} unique input{'s' if input_count != 1 else ''} "
                f"in {perf_counter() - started:.1f}s"
            )
        console.print("Loading corpus metadata")
        started = perf_counter()
        inventory = _figure_inventory(ROOT, all_files)
        if args.verbose:
            console.print(f"  loaded {len(inventory['workloads'])} metadata records in {perf_counter() - started:.1f}s")
        target_request = parse_target(str(args.target))
        if not target_request.source:
            raise ValueError("figures requires a source target, not a cached label lookup")
        if target_request.label is None:
            target_request = parse_target(f"figures={args.target}")
        report_path = args.report.expanduser().resolve()
        console.print(f"Loading cache {report_path}", soft_wrap=True, markup=False)
        started = perf_counter()
        store = ReportStore(report_path)
        if args.verbose:
            console.print(f"  loaded {store.row_count} observations in {perf_counter() - started:.1f}s")
        requests = tuple(
            BenchmarkRequest(EndpointRequest(target_request, treatment), figure.files)
            for figure in figures
            for treatment in figure.figure.treatments
        )
        console.print("Resolving targets")
        started = perf_counter()
        targets = resolve_requests(requests, store, config.rounds, config.timeout_sec, False, cwd, ROOT, console)
        if args.verbose:
            target_count = len(targets)
            console.print(
                f"  resolved {target_count} target{'s' if target_count != 1 else ''} in {perf_counter() - started:.1f}s"
            )
        plans = plan_collection(store, requests, targets, config.rounds, config.timeout_sec, False)
        status = 0
        try:
            grouped = collect(store, plans, requests, targets, config.timeout_sec, console, verbose=args.verbose)
        except KeyboardInterrupt:
            return 130
        except (OSError, ValueError, subprocess.SubprocessError) as error:
            console.print(f"collection error: {error}")
            # A failed snapshot write must not make an older executable look current.
            console.print(f"Writing {grouped_report_path(report_path)}", soft_wrap=True, markup=False)
            started = perf_counter()
            grouped = store.grouped_report(current_label_bindings(requests, targets))
            write_grouped_report(grouped, grouped_report_path(report_path))
            if args.verbose:
                console.print(f"  wrote grouped snapshot in {perf_counter() - started:.1f}s")
            status = 2
        render_figures(
            figures,
            config,
            grouped,
            report_path,
            targets[target_request],
            args.output_dir.expanduser().resolve() if args.output_dir else None,
            console,
            inventory,
        )
        return status
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        console.print(f"error: {error}")
        return 2
