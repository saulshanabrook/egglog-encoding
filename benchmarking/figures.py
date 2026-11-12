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
from dataclasses import asdict, dataclass, replace
from pathlib import Path
from time import perf_counter
from typing import Any, TypedDict, cast

from rich.console import Console

from benchmarks.reproduction.corpus import MANIFEST_RELATIVE_PATH, VALIDATION_POLICY, load_manifest
from benchmarks.reproduction.native import NATIVE_ALLOCATION_FAILURE

from .config import DEFAULT_AST_CACHE, DEFAULT_MEMORY_LIMIT_BYTES, DEFAULT_REPORT, DEFAULT_TIMEOUT_SEC
from .engines import PROOF_ORACLES, TREATMENT_SPECS, TREATMENTS, Treatment
from .figure_reuse import FIGURE_DATA_VERSION, FigureData
from .models import (
    BenchmarkEndpoint,
    BuiltBinary,
    EndpointRequest,
    FileSpec,
    ResolvedTarget,
    validate_unique_file_identities,
)
from .native_memory import add_memory_limit_options
from .reports.grouped import grouped_report_path, write_grouped_report
from .reports.store import CacheKey, GroupedReport, select_observations
from .targets import parse_target
from .workloads import exclusion_bindings, resolve_files

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_CONFIG = ROOT / "figures/catalog.json"
DEFAULT_OUTPUT_DIR = ROOT / "figures/output/eval"
VEGA_PACKAGES = ("vega@6.4.0", "vega-lite@6.4.3", "vega-cli@6.4.0", "canvas@3.2.3")


@dataclass(frozen=True)
class Figure:
    name: str
    spec: Path
    patterns: tuple[str, ...]
    treatments: tuple[Treatment, ...]
    checks: tuple[Treatment, ...] = ()


@dataclass(frozen=True)
class LmfaoConfig:
    data: Path
    backend: Path


@dataclass(frozen=True)
class FigureConfig:
    path: Path
    rounds: int
    timeout_sec: int
    figures: tuple[Figure, ...]
    memory_limit_bytes: int | None = DEFAULT_MEMORY_LIMIT_BYTES
    lmfao: LmfaoConfig | None = None
    threads: int = 1


@dataclass(frozen=True)
class ResolvedFigure:
    figure: Figure
    files: tuple[FileSpec, ...]
    spec: dict[str, Any]


class FigureWorkload(TypedDict):
    label: str
    family: str
    file_sha256: str
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
    identities = None if published is None else {file.sha256 for file in published}
    registered = {(directory / item["file"]).resolve(): item["sha256"] for item in manifest.workloads}
    if published is not None and any(registered.get(file.absolute_path) != file.sha256 for file in published):
        raise ValueError("selected published corpus input changed or is unregistered; review its manifest")
    cases = {case["id"]: case for case in manifest.cases}
    workloads: dict[str, FigureWorkload] = {}
    for source in manifest.workloads:
        identity = source["sha256"]
        if identities is not None and identity not in identities:
            continue
        first = source["aliases"][0]
        case = cases[first["case"]]
        workloads[identity] = {
            "label": case["id"] + (f" / call {first['order'] + 1}" if len(case["workloads"]) > 1 else ""),
            "family": case["family"],
            "file_sha256": source["sha256"],
            "validation_failures": {},
        }
    for outcome in manifest.outcomes:
        item = workloads.get(outcome["file_sha256"])
        if item is None or outcome["kind"] != "validation" or outcome["policy"] != VALIDATION_POLICY:
            continue
        key = outcome["binary_sha256"]
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
    data = json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=_unique_object)
    if (
        not isinstance(data, dict)
        or not {"rounds", "figures"} <= set(data)
        or set(data) - {"rounds", "timeout_sec", "figures", "lmfao"}
    ):
        raise ValueError("figure config requires rounds and figures, with optional timeout_sec and lmfao")
    data.setdefault("timeout_sec", DEFAULT_TIMEOUT_SEC)
    for key in ("rounds", "timeout_sec"):
        if type(data[key]) is not int or data[key] < 1:
            raise ValueError(f"{key} must be a positive integer")
    lmfao = None
    if "lmfao" in data:
        item = data["lmfao"]
        if (
            not isinstance(item, dict)
            or set(item) != {"data", "backend"}
            or any(not isinstance(value, str) or not value for value in item.values())
        ):
            raise ValueError("lmfao requires data and backend paths")
        lmfao = LmfaoConfig((path.parent / item["data"]).resolve(), (path.parent / item["backend"]).resolve())
    if not isinstance(data["figures"], dict) or (not data["figures"] and lmfao is None):
        raise ValueError("figures must be a nonempty object of named figures")
    figures = []
    for name, item in data["figures"].items():
        if name == "lmfao":
            raise ValueError("lmfao is a table configured by the top-level lmfao entry")
        if not name or Path(name).name != name or name in (".", ".."):
            raise ValueError(f"invalid figure name: {name!r}")
        if (
            not isinstance(item, dict)
            or not {"spec", "files", "treatments"} <= set(item)
            or set(item) - {"spec", "files", "treatments", "checks"}
        ):
            raise ValueError(f"{name}: requires spec, files, treatments, and optional checks")
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
        checks = item.get("checks", [])
        if not isinstance(checks, list) or any(not isinstance(value, str) for value in checks):
            raise ValueError(f"{name}: checks must be a list of treatments")
        unknown = set(item["treatments"] + checks) - set(TREATMENTS)
        if unknown:
            raise ValueError(f"{name}: unknown treatments: {', '.join(sorted(unknown))}")
        figures.append(
            Figure(
                name,
                (path.parent / item["spec"]).resolve(),
                tuple(item["files"]),
                tuple(item["treatments"]),
                tuple(checks),
            )
        )
    return FigureConfig(path, data["rounds"], data["timeout_sec"], tuple(figures), lmfao=lmfao)


def parse_args(argv: Sequence[str]) -> tuple[argparse.Namespace, FigureConfig]:
    """Make configured names available in help without resolving files or builds."""
    preliminary = argparse.ArgumentParser(add_help=False)
    preliminary.add_argument("--config", type=Path, default=DEFAULT_CONFIG)
    preliminary.add_argument("--reuse-from", type=Path)
    known, _ = preliminary.parse_known_args(argv)
    explicit = {token.split("=", 1)[0] for token in argv}
    try:
        config = (
            FigureConfig(known.config, 10, DEFAULT_TIMEOUT_SEC, ())
            if known.reuse_from is not None and not explicit & {"--config", "--target"}
            else load_config(known.config)
        )
    except (OSError, ValueError, TypeError) as error:
        preliminary.error(str(error))
    parser = argparse.ArgumentParser(
        prog="./bench.py figures",
        description="Collect paper experiments, then render selected figures and tables.",
        epilog="Configured outputs:\n"
        + "\n".join(f"  {f.name}: {f.spec}" for f in config.figures)
        + ("\n  lmfao: covariance execution and optimization table" if config.lmfao else ""),
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument("names", nargs="*", help="configured figure/table names (default: all)")
    parser.add_argument("--config", type=Path, default=DEFAULT_CONFIG, help="flat figure JSON catalog")
    parser.add_argument("-v", "--verbose", action="store_true", help="show phase timings and per-attempt starts")
    parser.add_argument(
        "--rounds", type=int, default=config.rounds, help="observations per condition (overrides catalog)"
    )
    parser.add_argument(
        "--target", default=f"figures={ROOT}", help="source target (default: this checkout, label figures)"
    )
    parser.add_argument(
        "--no-runs", action="store_true", help="render cached target labels only; never build or collect"
    )
    parser.add_argument(
        "--reuse-from", type=Path, help="reuse per-figure exported observations, bindings, and AST data"
    )
    parser.add_argument("--ast-cache", type=Path, default=Path(DEFAULT_AST_CACHE), help="Slotted AST JSONL cache path")
    parser.add_argument("--report", type=Path, default=Path(DEFAULT_REPORT), help="append-only observation cache")
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=DEFAULT_OUTPUT_DIR,
        help="output directory (default: this checkout's figures/output/eval)",
    )
    parser.add_argument("--timeout-sec", type=int, default=config.timeout_sec, help="per-process resource guard")
    parser.add_argument("--threads", type=int, default=1, help="requested workers per process (default: 1)")
    parser.add_argument("--lmfao-data", type=Path, help="override the catalog's prepared LMFAO dataset")
    parser.add_argument("--lmfao-backend", type=Path, help="override the catalog's prepared LMFAO executable")
    parser.add_argument("--lmfao-cxxflags", help="C++ flags for LMFAO generated programs, including any Boost path")
    parser.add_argument("--proof-validation", type=Path, help="delegated proof replay evidence for LMFAO")
    parser.add_argument("--proof-source-receipt", type=Path, help="frozen production binary/source binding receipt")
    add_memory_limit_options(parser, default=DEFAULT_MEMORY_LIMIT_BYTES)
    args = parser.parse_args(argv)
    if args.rounds < 1 or args.timeout_sec < 1 or args.threads < 1:
        parser.error("--rounds, --timeout-sec and --threads must be positive")
    if str(args.report) == "-":
        parser.error("--report requires a file path; '-' streaming is not supported")
    if len(args.names) != len(set(args.names)):
        parser.error("duplicate figure name")
    known_names = {figure.name for figure in config.figures} | ({"lmfao"} if config.lmfao else set())
    unknown = set(args.names) - known_names
    if unknown and args.reuse_from is None:
        parser.error("unknown figure names: " + ", ".join(sorted(unknown)) + "; select a JSON catalog with --config")
    if config.lmfao:
        config = replace(
            config,
            lmfao=LmfaoConfig(
                args.lmfao_data.expanduser().resolve() if args.lmfao_data else config.lmfao.data,
                args.lmfao_backend.expanduser().resolve() if args.lmfao_backend else config.lmfao.backend,
            ),
        )
    return args, replace(
        config,
        rounds=args.rounds,
        timeout_sec=args.timeout_sec,
        memory_limit_bytes=args.memory_limit_bytes,
        threads=args.threads,
    )


def prepare_lmfao(args: argparse.Namespace, config: FigureConfig) -> argparse.Namespace | None:
    """Check external prerequisites before any paper collection or build."""
    if config.lmfao is None or (args.names and "lmfao" not in args.names):
        return None
    from .lmfao.cli import parse_args as lmfao_args
    from .lmfao.cli import verify_backend
    from .lmfao.data import validate_inputs

    source = parse_target(args.target).source
    if not source or Path(source).expanduser().resolve() != ROOT:
        raise ValueError("LMFAO requires --target to name this checkout; select other figures for another target")
    selected = lmfao_args(
        [
            "--data",
            str(config.lmfao.data),
            "--backend",
            str(config.lmfao.backend),
            "--output-dir",
            str(args.output_dir.expanduser().resolve() / "lmfao"),
        ]
    )
    selected.samples, selected.timeout = config.rounds, config.timeout_sec
    selected.report = args.report.expanduser().resolve()
    selected.memory_limit_bytes = config.memory_limit_bytes
    selected.threads = config.threads
    selected.proof_validation = args.proof_validation.expanduser().resolve() if args.proof_validation else None
    selected.proof_source_receipt = (
        args.proof_source_receipt.expanduser().resolve() if args.proof_source_receipt else None
    )
    if args.lmfao_cxxflags is not None:
        selected.cxxflags = args.lmfao_cxxflags
    if not args.no_runs:
        verify_backend(selected.backend)
        validate_inputs(selected.data)
    return selected


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
            spec = json.loads(figure.spec.read_bytes().decode("utf-8"))
            if (
                not isinstance(spec, dict)
                or not isinstance(spec.get("data"), dict)
                or not ({"url", "values"} & spec["data"].keys())
            ):
                raise ValueError(f"{figure.name}: specification must declare a primary data source")
            specs[figure.spec] = spec
        paths: dict[Path, None] = {}
        for pattern in figure.patterns:
            exclude = pattern.startswith("!")
            glob_pattern = pattern[1:] if exclude else pattern
            if not glob_pattern:
                raise ValueError(f"{figure.name}: empty file pattern: {pattern!r}")
            matches = sorted(glob.glob(str(config.path.parent / glob_pattern), recursive=True))
            if not matches:
                raise ValueError(f"{figure.name}: file pattern matched nothing: {pattern}")
            for match in matches:
                path = Path(match).resolve()
                if not path.is_file():
                    raise ValueError(f"{figure.name}: not a workload file: {path}")
                if exclude:
                    paths.pop(path, None)
                else:
                    paths[path] = None
        if not paths:
            raise ValueError(f"{figure.name}: file patterns selected no workloads")
        for path in paths:
            if path not in inputs:
                inputs[path] = resolve_files([os.path.relpath(path, invocation_cwd)], invocation_cwd)[0]
                file = inputs[path]
                # Table-size expectations belong to the correctness oracle;
                # figure timings still include these executable workloads.
                file = replace(
                    file,
                    exclusions=tuple(rule for rule in file.exclusions if rule.kind != "expected-failure"),
                    binary_inputs=tuple(
                        (
                            binary,
                            replace(
                                physical,
                                exclusions=tuple(
                                    rule for rule in physical.exclusions if rule.kind != "expected-failure"
                                ),
                            ),
                        )
                        for binary, physical in file.binary_inputs
                    ),
                )
                inputs[path] = replace(
                    file,
                    exclusions=file.exclusions
                    + tuple(
                        replace(rule, treatments=aliases)
                        for rule in file.exclusions
                        if (
                            aliases := tuple(
                                mode
                                for mode, oracle in PROOF_ORACLES.items()
                                if oracle in rule.treatments and mode not in rule.treatments
                            )
                        )
                    ),
                )
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
    ast_records: Sequence[dict[str, Any]] = (),
    extra_outputs: dict[str, str] | None = None,
) -> tuple[Path, ...]:
    """Bind shared sample selections and render Vega through temporary files."""
    from scipy import stats

    from .figure_results import corpus_view_domains, figure_results

    metadata = {item["file_sha256"]: item for item in inventory["workloads"]}
    label = target.row.label
    if label is None:
        raise ValueError("figure target must have a label")
    (output_dir or DEFAULT_OUTPUT_DIR).mkdir(parents=True, exist_ok=True)
    prepared = []
    for resolved in figures:
        figure = resolved.figure
        selected_inputs = []
        for file in resolved.files:
            info = metadata.get(file.sha256)
            for treatment in figure.treatments:
                physical = file.for_binary(TREATMENT_SPECS[treatment].binary_name)
                endpoint = BenchmarkEndpoint(
                    target.row,
                    target.binary_sha256_for(treatment),
                    treatment,
                    memory_limit_bytes=config.memory_limit_bytes,
                    threads=config.threads,
                )
                key = CacheKey.for_endpoint(endpoint, file)
                selection = select_observations(grouped, endpoint, file, config.rounds, config.timeout_sec)
                excluded, rows = selection.exclusion, selection.rows
                correctness_mode = PROOF_ORACLES.get(treatment, treatment)
                if correctness_mode != treatment:
                    # Recording inherits correctness exclusions, while resource
                    # deferrals apply to the timed treatment's own samples.
                    strict = select_observations(
                        grouped,
                        replace(endpoint, treatment=correctness_mode),
                        file,
                        config.rounds,
                        config.timeout_sec,
                    )
                    if strict.exclusion is not None and strict.exclusion.kind != "resource":
                        excluded = excluded or strict.exclusion
                    if excluded is not None:
                        rows = ()
                validation_issue = (
                    info["validation_failures"].get(key.binary_sha256, "")
                    if info and correctness_mode == "proof-testing"
                    else ""
                )
                selected_inputs.append(
                    {
                        "logical_id": file.sha256,
                        "label": info["label"] if info else file.display_path,
                        "family": info["family"] if info else "",
                        "file_sha256": physical.sha256,
                        "treatment": treatment,
                        "threads": endpoint.threads,
                        "requested_threads": endpoint.requested_threads,
                        "binary_sha256": key.binary_sha256,
                        "memory_limit_bytes": endpoint.memory_limit_bytes,
                        "selected_row_indices": [row.row_index for row in rows],
                        "validation_failures": info["validation_failures"] if info else {},
                        "validation_issue": validation_issue,
                        "exclusion": None
                        if excluded is None
                        else {
                            "kind": excluded.kind,
                            "reason": excluded.reason,
                            "evidence": excluded.evidence,
                        },
                    }
                )
        t_critical = None if config.rounds == 1 else float(stats.t.ppf(0.975, config.rounds - 1))
        bindings = {
            "target_label": label,
            "timeout_sec": config.timeout_sec,
            "rounds": config.rounds,
            "memory_limit_bytes": config.memory_limit_bytes,
            "threads": config.threads,
            "t_critical": t_critical,
            "selected_inputs": selected_inputs,
            "treatments": figure.treatments,
            "source_blockers": inventory["unavailable_cases"],
        }
        spec = deepcopy(resolved.spec)
        for parameter in spec.get("params", []):
            if parameter.get("name") in bindings:
                parameter["value"] = bindings[parameter["name"]]
        spec["data"]["url"] = grouped_report_path(report_path).as_uri()
        results = figure_results(figure.name, selected_inputs, grouped, config.rounds, t_critical)
        if figure.name.startswith("corpus-"):
            domains = corpus_view_domains(results)
            results["view_domains"] = domains
            for parameter in spec.get("params", []):
                if parameter["name"] == "view_domains":
                    parameter.pop("expr", None)
                    parameter["value"] = domains
            if not any(domain["zoom"] < domain["full"] for domain in domains.values()):
                # Empty facets still reserve axes/space in Vega-Lite. Omit the
                # entire optional composition when every value fits the detail.
                del spec["vconcat"][1]
        results["provenance"] = {
            "target": asdict(target.row),
            "catalog_path": str(config.path),
            "spec_path": str(figure.spec),
            "report_path": str(report_path),
            "timeout_sec": config.timeout_sec,
            "memory_limit_bytes": config.memory_limit_bytes,
            "threads": config.threads,
            "source_blockers": inventory["unavailable_cases"],
            "view_domains": results.get("view_domains"),
        }
        prepared.append(FigureData(figure.name, spec, grouped, results["provenance"], tuple(ast_records)))
    return render_figure_data(prepared, output_dir or DEFAULT_OUTPUT_DIR, console, extra_outputs=extra_outputs)


def renderer_metadata() -> dict[str, Any]:
    """Identify the renderer checkout, allowing installed distributions outside Git."""
    from .targets import git_dirty, git_sha

    try:
        return {"git_sha": git_sha(ROOT), "is_dirty": git_dirty(ROOT)}
    except (OSError, subprocess.SubprocessError):
        return {"git_sha": None, "is_dirty": None}


def render_figure_data(
    data: Sequence[FigureData],
    destination: Path,
    console: Console,
    *,
    images: bool = True,
    extra_outputs: dict[str, str] | None = None,
    renderer: dict[str, Any] | None = None,
) -> tuple[Path, ...]:
    """Validate and atomically publish snapshots; images=False skips only drawing."""
    from .figure_results import figure_results, latex_results

    command = [*shlex.split(os.environ.get("NPX", "npx --yes")), *[f"--package={p}" for p in VEGA_PACKAGES]]
    renderer = renderer_metadata() if renderer is None else renderer
    destination = destination.resolve()
    destination.mkdir(parents=True, exist_ok=True)
    prepared = []
    for item in data:
        name, spec = item.name, deepcopy(item.spec)
        parameters = {parameter["name"]: parameter["value"] for parameter in spec["params"] if "value" in parameter}
        results = figure_results(
            name, parameters["selected_inputs"], item.grouped, parameters["rounds"], parameters["t_critical"]
        )
        for condition in results["conditions"]:
            issue = (
                f"excluded ({condition['exclusion']['kind']}): {condition['exclusion']['reason']}"
                if condition["exclusion"]
                else condition["validation_issue"]
                or (f"{condition['failed_n']} failed observations" if condition["failed_n"] else None)
                or (
                    f"{condition['sample_n']}/{parameters['rounds']} observations"
                    if condition["sample_n"] != parameters["rounds"]
                    else None
                )
                or next(
                    (
                        f"{metric}: measurement unavailable"
                        for metric, values in condition["metrics"].items()
                        if values["valid_n"] != parameters["rounds"]
                    ),
                    None,
                )
            )
            if issue:
                raise ValueError(
                    f"{name}: {condition['label']} · {condition['treatment']}: {issue}; no figure outputs replaced"
                )
        prepared.append((item, spec, parameters, results))
    rendered: list[Path] = []
    with tempfile.TemporaryDirectory(dir=destination, prefix=".figures.") as temporary:
        for item, spec, parameters, results in prepared:
            name = item.name
            results.update(figure_data_version=FIGURE_DATA_VERSION, provenance=item.provenance, renderer=renderer)
            # Include only selected measurements; full profiling/provenance lives outside the plot view.
            selections: dict[tuple[str, str, str, int], set[int]] = {}
            for selected in parameters["selected_inputs"]:
                identity = (
                    selected["binary_sha256"],
                    selected["file_sha256"],
                    selected["treatment"],
                    selected["threads"],
                )
                selections.setdefault(identity, set()).update(selected["selected_row_indices"])
            groups = []
            for group in item.grouped.data["groups"]:
                key = group["key"]
                indices = selections.get((key["binary_sha256"], key["file_sha256"], key["treatment"], key["threads"]))
                if indices is not None:
                    groups.append(
                        {
                            **group,
                            "samples": [
                                {
                                    key: cast(Any, row)[key]
                                    for key in (
                                        "row_index",
                                        "started_at",
                                        "status",
                                        "wall_sec",
                                        "max_rss_bytes",
                                        "timeout_sec",
                                        "memory_limit_bytes",
                                        "threads",
                                        "requested_threads",
                                    )
                                }
                                for row in group["samples"]
                                if row["row_index"] in indices
                            ],
                        }
                    )
            spec["data"] = {"values": [{"groups": groups}]}
            for condition in results["conditions"]:
                for row in condition["observations"]:
                    row.pop("timing_summary", None)
            numbers, table = latex_results(results)
            console.print(f"Rendering {name}" if images else f"Exporting {name}", markup=False)
            bound_path = Path(temporary) / f"{name}.bound.vl.json"
            bound_path.write_text(json.dumps(spec, ensure_ascii=False, separators=(",", ":")) + "\n", encoding="utf-8")
            metadata_outputs = [bound_path]
            for suffix, content in (
                (
                    "results.json",
                    json.dumps(results, ensure_ascii=False, allow_nan=False, separators=(",", ":")) + "\n",
                ),
                ("numbers.tex", numbers),
                ("table.tex", table),
            ):
                exported = Path(temporary) / f"{name}.{suffix}"
                exported.write_text(content, encoding="utf-8")
                metadata_outputs.append(exported)
            outputs = []
            if images:
                for extension in ("pdf", "svg", "png"):
                    generated = Path(temporary) / f"{name}.{extension}"
                    args = [*command, "vl2" + extension, str(bound_path), str(generated), "--base", temporary]
                    if extension == "png":
                        args += ["-s", "3"]
                    completed = subprocess.run(
                        args, cwd=ROOT, check=True, stdout=sys.stderr, stderr=subprocess.PIPE, text=True
                    )
                    if completed is not None and completed.stderr:
                        print(completed.stderr, file=sys.stderr, end="")
                        if "ERROR" in completed.stderr:
                            raise ValueError(f"{name}: Vega renderer failed; no figure outputs replaced")
                    if not generated.is_file() or not generated.stat().st_size:
                        raise ValueError(f"renderer produced no image: {generated}")
                    outputs.append(generated)
            outputs.extend(metadata_outputs)
            if name == "slotted-runtime":
                from .slotted_ast import export_slotted_ast

                if not item.ast_records:
                    raise ValueError("slotted-runtime requires a persisted AST measurement snapshot")
                outputs.extend(export_slotted_ast(item.ast_records, Path(temporary)))
            rendered.extend(destination / path.name for path in outputs)
        for name, content in (extra_outputs or {}).items():
            (Path(temporary) / name).write_text(content, encoding="utf-8")
            rendered.append(destination / name)
        for output in rendered:
            os.replace(Path(temporary) / output.name, output)
    for output in rendered:
        console.print(str(output), soft_wrap=True, markup=False)
    return tuple(rendered)


def main(argv: Sequence[str] | None = None) -> int:
    """Use the ordinary shared benchmark phases for one deduplicated figure invocation."""
    raw = tuple(sys.argv[1:] if argv is None else argv)
    args, config = parse_args(raw)
    from .collection import BenchmarkRequest, collect, current_label_bindings, plan_collection, resolve_requests
    from .reports.store import ReportStore, parse_grouped_report

    console = Console(stderr=True)
    try:
        if args.reuse_from is not None and not any(token.split("=", 1)[0] == "--target" for token in raw):
            from .figure_reuse import import_figure, restyle_figure, reuse_figure

            directory = args.reuse_from.expanduser().resolve()
            explicit = {token.split("=", 1)[0] for token in raw}
            if "--threads" in explicit:
                raise ValueError(
                    "portable replay retains recorded worker counts; use --target to collect a new selection"
                )
            names = args.names or (
                [figure.name for figure in config.figures]
                if "--config" in explicit
                else sorted(
                    {
                        path.name.removesuffix(".gz").removesuffix(".results.json")
                        for pattern in ("*.results.json", "*.results.json.gz")
                        for path in directory.glob(pattern)
                    }
                )
            )
            if not names:
                raise ValueError(f"no per-figure results found in {directory}")
            if any(Path(name).name != name for name in names):
                raise ValueError("figure names must be filenames, not paths")
            extra_outputs = {}
            if "lmfao" in names:
                from .lmfao.report import paper_results

                if explicit & {
                    "--rounds",
                    "--timeout-sec",
                    "--memory-limit",
                    "--memory-limit-gib",
                    "--no-memory-limit",
                }:
                    raise ValueError("LMFAO table replay retains recorded limits and samples; recollect to change them")
                extra_outputs = paper_results(
                    json.loads((directory / "lmfao.results.json").read_text(encoding="utf-8"))
                )
                names = [name for name in names if name != "lmfao"]
            data = [import_figure(name, directory) for name in names]
            if "--config" in explicit:
                styles = {figure.name: figure.spec for figure in config.figures}
                for item in data:
                    if item.name not in styles:
                        raise ValueError(f"{item.name}: no matching figure in explicit --config")
                    restyle_figure(item, styles[item.name])
            overrides = {
                name: getattr(args, name)
                for name, flag in (("rounds", "--rounds"), ("timeout_sec", "--timeout-sec"))
                if flag in explicit
            }
            if explicit & {"--memory-limit", "--memory-limit-gib", "--no-memory-limit"}:
                overrides["memory_limit_bytes"] = args.memory_limit_bytes
            for item in data:
                reuse_figure(item, args.report.expanduser().resolve(), args.no_runs, overrides, console)
            render_figure_data(
                data,
                args.output_dir.expanduser().resolve(),
                console,
                renderer=renderer_metadata(),
                extra_outputs=extra_outputs,
            )
            return 0
        cwd = Path.cwd()
        lmfao = prepare_lmfao(args, config)
        figure_count = len(args.names) or (len(config.figures) + int(lmfao is not None))
        console.print(
            f"Resolving inputs for {figure_count} paper output{'s' if figure_count != 1 else ''} · "
            f"{config.rounds} sample{'s' if config.rounds != 1 else ''}/condition"
        )
        started = perf_counter()
        figures = resolve_figures(config, args.names, cwd)
        lmfao_files = {}
        if lmfao is not None:
            from .lmfao.optimizer import optimizer_inputs, optimizer_report, optimizer_requests

            lmfao_files = optimizer_inputs(lmfao.output_dir, lmfao.rewrite_rounds)
        all_files = tuple(
            dict.fromkeys([*(file for figure in figures for file in figure.files), *lmfao_files.values()])
        )
        imports = []
        if args.reuse_from is not None:
            from .figure_reuse import import_figure

            directory = args.reuse_from.expanduser().resolve()
            imports = [
                import_figure(item.figure.name, directory)
                for item in figures
                if any((directory / f"{item.figure.name}.results.json{suffix}").exists() for suffix in ("", ".gz"))
            ]
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
        if not target_request.source and not args.no_runs:
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
            BenchmarkRequest(
                EndpointRequest(
                    target_request, treatment, memory_limit_bytes=config.memory_limit_bytes, threads=config.threads
                ),
                figure.files,
            )
            for figure in figures
            for treatment in figure.figure.treatments
        )
        if lmfao is not None:
            requests += optimizer_requests(lmfao_files, target_request, config.memory_limit_bytes, config.threads)
        status = 0
        if args.no_runs:
            binaries = []
            row = None
            for binary_name in dict.fromkeys(
                TREATMENT_SPECS[request.endpoint.treatment].binary_name for request in requests
            ):
                pointer = store.find_label_pointer(str(target_request.label), binary_name)
                if pointer is None:
                    raise ValueError(f"no cached {binary_name} rows for label {target_request.label!r}")
                if row is not None and pointer.row != row:
                    raise ValueError("cached engine labels have different target provenance; choose a consistent label")
                row = pointer.row
                binaries.append(BuiltBinary(binary_name, pointer.binary_sha256, None))
            assert row is not None
            targets = {
                target_request: ResolvedTarget(
                    target_request, row, binaries[0].sha256, None, tuple(binaries), binaries[0].binary_name
                )
            }
            grouped = parse_grouped_report(grouped_report_path(report_path).read_bytes(), str(report_path))
        else:
            console.print("Resolving targets")
            started = perf_counter()
            targets = resolve_requests(requests, store, config.rounds, config.timeout_sec, False, cwd, ROOT, console)
            if args.verbose:
                target_count = len(targets)
                console.print(
                    f"  resolved {target_count} target{'s' if target_count != 1 else ''} "
                    f"in {perf_counter() - started:.1f}s"
                )
            planning: ReportStore | GroupedReport = store
            if imports:
                from .figure_reuse import merge_grouped

                planning = merge_grouped(store.grouped_report(), imports, str(target_request.label))
            plans = plan_collection(planning, requests, targets, config.rounds, config.timeout_sec, False)
            try:
                grouped = collect(store, plans, requests, targets, config.timeout_sec, console, verbose=args.verbose)
            except KeyboardInterrupt:
                return 130
            except (OSError, ValueError, subprocess.SubprocessError) as error:
                console.print(f"collection error: {error}")
                # A failed snapshot write must not make an older executable look current.
                console.print(f"Writing {grouped_report_path(report_path)}", soft_wrap=True, markup=False)
                started = perf_counter()
                grouped = store.grouped_report(current_label_bindings(requests, targets), exclusion_bindings(all_files))
                write_grouped_report(grouped, grouped_report_path(report_path))
                if args.verbose:
                    console.print(f"  wrote grouped snapshot in {perf_counter() - started:.1f}s")
                status = 2
        if imports:
            from .figure_reuse import merge_grouped

            grouped = merge_grouped(grouped, imports, str(target_request.label))
        ast_records: tuple[dict[str, Any], ...] = ()
        for resolved in figures:
            if resolved.figure.name == "slotted-runtime":
                from .slotted_ast import slotted_ast_records

                console.print("Loading Slotted AST cache", markup=False)
                ast_records = slotted_ast_records(
                    resolved.files, args.ast_cache.expanduser().resolve(), collect=not args.no_runs
                )
        extra_outputs = {}
        if lmfao is not None:
            from .lmfao.cli import run as run_lmfao
            from .lmfao.report import paper_results

            if args.no_runs:
                saved = json.loads((lmfao.output_dir.parent / "lmfao.results.json").read_text(encoding="utf-8"))
                if (
                    saved["binary_sha256"]["slotted"] != targets[target_request].binary_sha256_for("slotted")
                    or saved["optimizer_memory_limit_bytes"] != config.memory_limit_bytes
                    or saved["optimizer_timeout_seconds"] != config.timeout_sec
                    or saved.get("egraph_workers", 1) != config.threads
                    or any(item["requested_samples"] != config.rounds for item in saved["optimizer"].values())
                    or any(
                        saved["optimizer"][mode]["input_sha256"] != file.sha256 for mode, file in lmfao_files.items()
                    )
                ):
                    raise ValueError("LMFAO saved table does not match this selection; use --reuse-from or recollect")
                extra_outputs = paper_results(saved)
            else:
                observed = optimizer_report(
                    lmfao.output_dir,
                    store,
                    targets[target_request],
                    lmfao_files,
                    config.rounds,
                    config.timeout_sec,
                    config.memory_limit_bytes,
                    lmfao.rewrite_rounds,
                    config.threads,
                )
                if "slotted" not in observed.successful or any(
                    row["status"] not in ("timed-out", "memory-limited")
                    for result in observed.report["optimizer"].values()
                    for row in result["failures"]
                ):
                    raise ValueError("LMFAO requires successful slotted samples and no non-resource optimizer errors")
                extra_outputs = paper_results(run_lmfao(lmfao, collected=observed))
        render_figures(
            figures,
            config,
            grouped,
            report_path,
            targets[target_request],
            args.output_dir.expanduser().resolve() if args.output_dir else None,
            console,
            inventory,
            ast_records,
            **({"extra_outputs": extra_outputs} if extra_outputs else {}),
        )
        return status
    except (OSError, ValueError, RuntimeError, subprocess.SubprocessError) as error:
        console.print(f"error: {error}")
        return 2
