"""Collect frozen LMFAO inputs through the shared benchmark/cache machinery."""

from __future__ import annotations

import json
import os
import statistics
import subprocess
import sys
import time
from collections.abc import Iterable
from pathlib import Path
from typing import Any

from rich.console import Console

from benchmarking.collection import BenchmarkRequest, collect, plan_collection, resolve_requests
from benchmarking.engines import PROCESS_ENV, Treatment
from benchmarking.models import BenchmarkEndpoint, EndpointRequest, FileSpec
from benchmarking.native_memory import NATIVE_LIMIT_BYTES, native_memory_command
from benchmarking.reports.store import ReportRecord, ReportStore, select_observations
from benchmarking.targets import parse_target, sha256_file, workload_command
from benchmarking.workloads import resolve_files

ROOT = Path(__file__).resolve().parents[2]
INPUTS = ROOT / "benchmarks/lmfao/inputs"
TREATMENTS: tuple[Treatment, ...] = ("slotted", "slotted-ref-multi")


def extractor_path(profile: str) -> Path:
    target = Path(os.environ.get("CARGO_TARGET_DIR", "target"))
    executable = "lmfao-extract.exe" if os.name == "nt" else "lmfao-extract"
    return ROOT / target / profile / executable


def write_json(path: Path, value: Any) -> None:
    path.write_text(json.dumps(value, indent=2) + "\n")


def seconds_summary(values: Iterable[float]) -> dict[str, float | int] | None:
    samples = list(values)
    if not samples:
        return None
    return {
        "median_seconds": statistics.median(samples),
        "min_seconds": min(samples),
        "max_seconds": max(samples),
        "samples": len(samples),
    }


def summarize_optimizer(rows: list[ReportRecord], budget: int, requested: int, issue: str | None) -> dict[str, Any]:
    completed = [row for row in rows if row["status"] == "success"]
    return {
        "rewrite_round_budget": budget,
        "requested_samples": requested,
        "completed_samples": len(completed),
        "issue": issue,
        "process_seconds": seconds_summary(row["wall_sec"] for row in completed if row["wall_sec"] is not None),
        "ruleset_work_seconds": seconds_summary(
            sum(
                r["assembly_ns"] + r["search_ns"] + r["apply_ns"] + r["execution_ns"] + r["merge_ns"]
                for r in row["timing_summary"]["rulesets"]
            )
            / 1e9
            for row in completed
            if row["timing_summary"] is not None
        ),
        "failures": [row for row in rows if row["status"] != "success"],
    }


def export_graph(
    binary: Path,
    file: FileSpec,
    treatment: Treatment,
    output: Path,
    names: str,
    timeout: int,
    memory_limit_bytes: int | None = NATIVE_LIMIT_BYTES,
) -> dict[str, Any]:
    """Rerun a frozen input with read-only export, outside optimizer samples."""
    physical = file.for_binary("slotted-reference" if treatment == "slotted-ref-multi" else "egglog-experimental")
    if treatment == "slotted":
        source = physical.absolute_path.read_text() + f"\n(slotted-export {json.dumps(str(output))} {names})\n"
    else:
        frozen = json.loads(physical.absolute_path.read_text())
        frozen["multi"] += "\ndump\n"
        source = json.dumps(frozen)
    path = output.with_suffix(physical.absolute_path.suffix)
    path.write_text(source)
    exported = FileSpec(str(path), path, sha256_file(path))
    command, env = native_memory_command(
        workload_command(binary, exported, treatment), {**os.environ, **PROCESS_ENV}, memory_limit_bytes
    )
    result = subprocess.run(command, cwd=ROOT, env=env, capture_output=True, text=True, timeout=timeout, check=True)
    if treatment == "slotted-ref-multi":
        graph = next(line.removeprefix("GRAPH ") for line in result.stdout.splitlines() if line.startswith("GRAPH "))
        output.write_text(graph + "\n")
    return dict(json.loads(output.read_text()))


def collect_optimizers(
    output: Path,
    samples: int,
    timeout: int,
    report_path: Path | None = None,
    memory_limit_bytes: int | None = NATIVE_LIMIT_BYTES,
    *,
    treatments: tuple[Treatment, ...] = TREATMENTS,
    variants: tuple[str, ...] = ("single-root", "roots", "shared"),
) -> tuple[dict[str, Any], dict[str, Any]]:
    manifest = json.loads((INPUTS / "manifest.json").read_text())
    manifest["variants"] = [v for v in manifest["variants"] if v["name"] in variants]
    files = resolve_files([str(INPUTS / v["file"]) for v in manifest["variants"]], ROOT)
    request = parse_target(str(ROOT))
    requests = tuple(
        BenchmarkRequest(EndpointRequest(request, treatment, memory_limit_bytes=memory_limit_bytes), files)
        for treatment in treatments
    )
    store = ReportStore(report_path or output / "optimizer.jsonl")
    console = Console(stderr=True)
    targets = resolve_requests(requests, store, samples, timeout, False, ROOT, ROOT, console)
    plans = plan_collection(store, requests, targets, samples, timeout, False)
    collect(store, plans, requests, targets, timeout, console)
    subprocess.run(
        ["cargo", "build", "--locked", "--release", "-p", "lmfao-extract"],
        cwd=ROOT,
        check=True,
        stdout=sys.stderr,
    )
    extractor = extractor_path("release")
    target = targets[request]
    report: dict[str, Any] = {
        "optimizer": {},
        "extractor_path": str(extractor),
        "extractor_sha256": sha256_file(extractor),
        "graph_collection": {},
        "graph_comparisons": {},
        "binary_sha256": {mode: target.binary_sha256_for(mode) for mode in treatments},
        "binary_paths": {mode: str(target.binary_path_for(mode)) for mode in treatments},
        "optimizer_report": str(store.path),
        "optimizer_memory_limit_bytes": memory_limit_bytes,
        "timing_scope": "Optimizer process wall time includes startup, parsing/frontend, "
        "graph construction and rewriting. "
        "Ruleset work is engine-reported exclusive work, not rewrite-loop wall time; "
        "the native reference has no such breakdown. "
        "Graph collection is a separate rerun, including export; extraction and C++ execution are excluded.",
    }
    graphs = {}
    checker = None
    if len(treatments) == 2:
        binary = target.binary_path_for("slotted")
        assert binary is not None
        checker = binary.with_name("egraph-isomorphism")
        subprocess.run(
            ["cargo", "build", "--locked", "--release", "-p", "egraph-isomorphism"],
            cwd=ROOT,
            check=True,
            stdout=sys.stderr,
        )
    for variant, file in zip(manifest["variants"], files, strict=True):
        for treatment in treatments:
            label = f"{variant['name']}-{treatment}"
            endpoint = BenchmarkEndpoint(
                target.row, target.binary_sha256_for(treatment), treatment, memory_limit_bytes=memory_limit_bytes
            )
            selection = select_observations(store, endpoint, file, samples, timeout)
            rows = [row.record for row in selection.rows]
            report["optimizer"][label] = summarize_optimizer(
                rows, variant["rewrite_round_budget"], samples, selection.issue
            )
            report["optimizer"][label]["input_sha256"] = file.for_binary(
                "slotted-reference" if treatment == "slotted-ref-multi" else "egglog-experimental"
            ).sha256
            write_json(output / "optimizer-summary.json", report)
            if selection.issue is not None:
                continue
            binary = target.binary_path_for(treatment)
            assert binary is not None
            console.print(f"Exporting {label}")
            start = time.perf_counter()
            try:
                graphs[label] = export_graph(
                    binary,
                    file,
                    treatment,
                    output / f"{label}-graph.json",
                    manifest["export_names"],
                    timeout,
                    memory_limit_bytes,
                )
                issue = None
            except (subprocess.SubprocessError, ValueError, OSError) as error:
                issue = str(error)
                console.print(f"  graph unavailable: {issue}", markup=False)
            report["graph_collection"][label] = {"seconds": time.perf_counter() - start, "issue": issue}
        labels = [f"{variant['name']}-{t}" for t in TREATMENTS]
        if all(label in graphs for label in labels):
            assert checker is not None
            # Full graph comparison is a diagnostic, separate from measured runs.
            try:
                result = subprocess.run(
                    [
                        str(checker),
                        *(str(output / f"{label}-graph.json") for label in labels),
                        "--search-limit",
                        "100000",
                    ],
                    capture_output=True,
                    text=True,
                    timeout=timeout,
                )
                verdict = json.loads(result.stdout)
            except subprocess.TimeoutExpired:
                verdict = {"status": "inconclusive", "reason": "graph comparison exceeded timeout"}
            write_json(output / f"{variant['name']}-isomorphism.json", verdict)
            report["graph_comparisons"][variant["name"]] = {
                key: verdict[key] for key in ("status", "reason") if key in verdict
            }
            if verdict["status"] in ("different", "invalid"):
                raise ValueError(f"{variant['name']}: {verdict}")
        else:
            report["graph_comparisons"][variant["name"]] = {"status": "inconclusive", "reason": "missing graph"}
        write_json(output / "optimizer-summary.json", report)
    return graphs, report
