"""Collect a flat figure catalog with the shared benchmark pipeline, then render Vega."""

from __future__ import annotations

import argparse
import glob
import hashlib
import json
import os
import shlex
import subprocess
import sys
import tempfile
from collections.abc import Sequence
from dataclasses import asdict, dataclass, replace
from pathlib import Path
from typing import Any

from rich.console import Console
from scipy import stats

from benchmarks.paper import FigureInventory, figure_inventory

from .engines import TREATMENT_SPECS, TREATMENTS, Treatment
from .models import EndpointRequest, FileSpec, ResolvedTarget
from .reports.grouped import grouped_report_path, write_grouped_report
from .reports.store import GroupedReport, ObservationGroup
from .targets import parse_target, sha256_file, workload_command
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


def _unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    """Reject duplicate declarations before JSON would silently overwrite them."""
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate configuration key: {key}")
        result[key] = value
    return result


def load_config(path: Path) -> FigureConfig:
    """Read the deliberately small user-authored catalog without touching workloads."""
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
    """Expand each figure independently; never cross unrelated files and treatments."""
    result = []
    for figure in config.figures:
        if names and figure.name not in names:
            continue
        if not figure.spec.is_file():
            raise ValueError(f"figure spec does not exist: {figure.spec}")
        spec = json.loads(figure.spec.read_bytes())
        if not isinstance(spec, dict) or not isinstance(spec.get("data"), dict) or not spec["data"].get("url"):
            raise ValueError(f"{figure.name}: specification must declare a primary data.url")
        paths: dict[Path, None] = {}
        for pattern in figure.patterns:
            matches = sorted(glob.glob(str(config.path.parent / pattern), recursive=True))
            if not matches:
                raise ValueError(f"{figure.name}: file pattern matched nothing: {pattern}")
            for match in matches:
                path = Path(match).resolve()
                if not path.is_file():
                    raise ValueError(f"{figure.name}: not a workload file: {path}")
                paths[path] = None
        display_paths = [os.path.relpath(path, invocation_cwd) for path in paths]
        files = resolve_files(display_paths, invocation_cwd, None)
        result.append(ResolvedFigure(figure, files))
    return tuple(result)


def write_if_changed(path: Path, data: bytes) -> None:
    """Replace derived files atomically while preserving unchanged output mtimes."""
    if path.is_file() and path.read_bytes() == data:
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary: Path | None = None
    try:
        with tempfile.NamedTemporaryFile(dir=path.parent, prefix=f".{path.name}.", delete=False) as handle:
            temporary = Path(handle.name)
            handle.write(data)
        os.replace(temporary, path)
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)


def render_figures(
    figures: Sequence[ResolvedFigure],
    config: FigureConfig,
    grouped: GroupedReport,
    report_path: Path,
    target: ResolvedTarget,
    output_dir: Path | None,
    invocation: Sequence[str],
    console: Console,
    inventory: FigureInventory | None = None,
) -> tuple[Path, ...]:
    """Bind declared Vega parameters and data, render incrementally, and retain provenance."""
    all_files = tuple(dict.fromkeys(file for figure in figures for file in figure.files))
    if inventory is None:
        inventory = figure_inventory(ROOT, config.timeout_sec, all_files)
    grouped_digest = sha256_file(grouped_report_path(report_path))
    metadata = {(item["file_sha256"], item["fact_directory_sha256"]): item for item in inventory["workloads"]}
    label = target.row.label
    if label is None:
        raise ValueError("figure target must have a label")
    labeled_groups: dict[tuple[str, str, Treatment, str, int], ObservationGroup] = {}
    for group in grouped.data["groups"]:
        if label not in group["labels"]:
            continue
        key = group["key"]
        identity = (
            key["file_sha256"],
            key["fact_directory_sha256"],
            key["treatment"],
            key["disequality_encoding"],
            key["timeout_sec"],
        )
        if identity in labeled_groups:
            raise ValueError("grouped label addresses multiple executable identities for one input")
        labeled_groups[identity] = group
    rendered = []
    for resolved in figures:
        figure = resolved.figure
        selected_inputs = []
        selections: list[dict[str, Any]] = []
        for file in resolved.files:
            info = metadata.get((file.sha256, file.fact_directory_sha256))
            for treatment in figure.treatments:
                physical = file.for_engine(TREATMENT_SPECS[treatment].engine)
                selected_inputs.append(
                    {
                        "logical_id": f"{file.sha256}/{file.fact_directory_sha256}",
                        "label": info["label"] if info else file.display_path,
                        "family": info["family"] if info else "",
                        "file_sha256": physical.sha256,
                        "fact_directory_sha256": physical.fact_directory_sha256,
                        "treatment": treatment,
                        "validation_failures": info["validation_failures"] if info else {},
                    }
                )
                selected_group = labeled_groups.get(
                    (physical.sha256, physical.fact_directory_sha256, treatment, "nee", config.timeout_sec)
                )
                rows = selected_group["samples"][-config.rounds :] if selected_group is not None else []
                try:
                    binary_path = target.binary_path_for(treatment)
                except ValueError:
                    binary_path = None
                template_binary = binary_path or Path(f"<{TREATMENT_SPECS[treatment].engine}-executable>")
                selections.append(
                    {
                        "logical_path": file.display_path,
                        "physical_path": physical.display_path,
                        "treatment": treatment,
                        "reconstructed_workload_command": workload_command(template_binary, file, treatment),
                        "requested_rows": config.rounds,
                        "selected_rows": len(rows),
                        "rows": [
                            {
                                key: row.get(key)
                                for key in (
                                    "row_index",
                                    "started_at",
                                    "status",
                                    "binary_sha256",
                                    "file_sha256",
                                    "fact_directory_sha256",
                                    "treatment",
                                    "disequality_encoding",
                                    "timeout_sec",
                                    "target_label",
                                    "target_source",
                                    "target_git_ref",
                                    "target_git_sha",
                                    "target_is_dirty",
                                    "file_path",
                                    "fact_directory_path",
                                )
                            }
                            for row in rows
                        ],
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
        spec = json.loads(figure.spec.read_bytes())
        for parameter in spec.get("params", []):
            if parameter.get("name") in bindings:
                parameter["value"] = bindings[parameter["name"]]
        spec["data"]["url"] = grouped_report_path(report_path).as_uri()
        destination = (output_dir or figure.spec.parent).resolve()
        bound_path = destination / f"{figure.name}.bound.vl.json"
        receipt_path = destination / f"{figure.name}.receipt.json"
        encoded_spec = json.dumps(spec, ensure_ascii=False, indent=2).encode() + b"\n"
        write_if_changed(bound_path, encoded_spec)
        selected_bytes = json.dumps(selections, ensure_ascii=False, sort_keys=True, separators=(",", ":")).encode()
        # The source snapshot is complete; this receipt records selection/provenance,
        # not computed plotting statistics or a second observation cache.
        receipt = {
            "figure": figure.name,
            "config": str(config.path),
            "spec": str(figure.spec),
            "invocation": ["./bench.py", "figures", *invocation],
            "rounds": config.rounds,
            "timeout_sec": config.timeout_sec,
            "target": asdict(target.row),
            "engine_binaries": [asdict(b) for b in target.engine_binaries],
            "selection_sha256": hashlib.sha256(selected_bytes).hexdigest(),
            "selected_observations": selections,
            "corpus_metadata": inventory,
            "report": str(report_path),
            "grouped_report": str(grouped_report_path(report_path)),
            "renderer_packages": VEGA_PACKAGES,
            "timing_boundary": "Whole process: launch, input I/O, parsing/lowering, execution, requested proof work.",
            "proof_output": "Native Egg materializes explanations in memory; timed runs do not serialize proof files.",
            "commands": "Historical argv is not stored; templates use treatment and physical input.",
        }
        fingerprint = hashlib.sha256(
            encoded_spec + grouped_digest.encode() + json.dumps(VEGA_PACKAGES).encode()
        ).hexdigest()
        receipt["render_sha256"] = fingerprint
        try:
            previous = json.loads(receipt_path.read_bytes())
        except (OSError, ValueError):
            previous = {}
        command = [*shlex.split(os.environ.get("NPX", "npx --yes")), *[f"--package={p}" for p in VEGA_PACKAGES]]
        outputs = [destination / f"{figure.name}.{extension}" for extension in ("pdf", "svg", "png")]
        unchanged = previous.get("render_sha256") == fingerprint and all(
            output.is_file()
            and previous.get("outputs", {}).get(str(output)) == sha256_file(output).removeprefix("sha256:")
            for output in outputs
        )
        if not unchanged:
            # A failed renderer must not replace one member of an otherwise
            # coherent PDF/SVG/PNG set or make an empty image look cached.
            with tempfile.TemporaryDirectory(dir=destination, prefix=f".{figure.name}.") as temporary:
                pending = []
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
                    pending.append((generated, output))
                for generated, output in pending:
                    os.replace(generated, output)
        receipt["outputs"] = {str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in outputs}
        write_if_changed(receipt_path, json.dumps(receipt, default=str, ensure_ascii=False, indent=2).encode() + b"\n")
        for output in outputs:
            console.print(str(output), soft_wrap=True)
            rendered.append(output)
        incomplete = sum(
            len(selection["rows"]) < config.rounds or any(row["status"] != "success" for row in selection["rows"])
            for selection in selections
        )
        if incomplete:
            console.print(f"{figure.name}: {incomplete}/{len(selections)} incomplete or unsuccessful conditions")
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
        figures = resolve_figures(config, args.names, cwd)
        inventory = figure_inventory(
            ROOT, config.timeout_sec, tuple(dict.fromkeys(file for figure in figures for file in figure.files))
        )
        target_request = parse_target(str(args.target))
        if not target_request.source:
            raise ValueError("figures requires a source target, not a cached label lookup")
        if target_request.label is None:
            target_request = parse_target(f"figures={args.target}")
        report_path = args.report.expanduser().resolve()
        store = ReportStore(report_path)
        requests = tuple(
            BenchmarkRequest(EndpointRequest(target_request, treatment), figure.files)
            for figure in figures
            for treatment in figure.figure.treatments
        )
        targets = resolve_requests(requests, store, config.rounds, config.timeout_sec, False, cwd, ROOT, console)
        plans = plan_collection(store, requests, targets, config.rounds, config.timeout_sec, False)
        status = 0
        try:
            grouped = collect(store, plans, requests, targets, config.timeout_sec, console)
        except KeyboardInterrupt:
            return 130
        except (OSError, ValueError, subprocess.SubprocessError) as error:
            console.print(f"collection error: {error}")
            # A failed snapshot write must not make an older executable look current.
            grouped = store.grouped_report(current_label_bindings(requests, targets))
            write_grouped_report(grouped, grouped_report_path(report_path))
            status = 2
        render_figures(
            figures,
            config,
            grouped,
            report_path,
            targets[target_request],
            args.output_dir.expanduser().resolve() if args.output_dir else None,
            raw,
            console,
            inventory,
        )
        return status
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        console.print(f"error: {error}")
        return 2
