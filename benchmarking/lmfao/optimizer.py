"""Collect LMFAO rewrite timings through the shared benchmark/cache machinery."""

from __future__ import annotations

import json
import os
import subprocess
import sys
from collections.abc import Iterable
from pathlib import Path
from typing import Any

from rich.console import Console
from scipy import stats

from benchmarking.collection import BenchmarkRequest, collect, plan_collection, resolve_requests
from benchmarking.engines import Treatment
from benchmarking.models import BenchmarkEndpoint, EndpointRequest, FileSpec, ResolvedTarget, TargetRequest
from benchmarking.reports.analysis import _sample_estimate
from benchmarking.reports.store import ReportRecord, ReportStore, select_observations
from benchmarking.targets import parse_target, sha256_file
from benchmarking.workloads import resolve_files

ROOT = Path(__file__).resolve().parents[2]
MODES: dict[str, Treatment] = {"slotted": "slotted", "debruijn": "off"}


def extractor_path(profile: str) -> Path:
    target = Path(os.environ.get("CARGO_TARGET_DIR", "target"))
    executable = "lmfao-extract.exe" if os.name == "nt" else "lmfao-extract"
    return ROOT / target / profile / executable


def write_json(path: Path, value: Any) -> None:
    path.write_text(json.dumps(value, indent=2) + "\n")


def seconds_summary(values: Iterable[float]) -> dict[str, Any] | None:
    samples = list(values)
    if not samples:
        return None
    estimate = _sample_estimate(
        samples, None, float(stats.t.ppf(0.975, len(samples) - 1)) if len(samples) > 1 else None
    )
    return {
        "values": samples,
        "mean": estimate.estimate._asdict(),
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


def optimizer_inputs(output: Path, rewrite_rounds: int) -> dict[str, FileSpec]:
    """Resolve the checked-in inputs through the normal workload harness."""
    from .program import benchmark_input

    output.mkdir(parents=True, exist_ok=True)
    return {mode: resolve_files([str(benchmark_input(mode, output, rewrite_rounds))], ROOT)[0] for mode in MODES}


def optimizer_requests(
    files: dict[str, FileSpec], target: TargetRequest, memory_limit_bytes: int | None
) -> tuple[BenchmarkRequest, ...]:
    return tuple(
        BenchmarkRequest(EndpointRequest(target, treatment, memory_limit_bytes=memory_limit_bytes), (files[mode],))
        for mode, treatment in MODES.items()
    )


def collect_optimizers(
    output: Path,
    samples: int,
    timeout: int,
    report_path: Path | None,
    memory_limit_bytes: int | None,
    *,
    rewrite_rounds: int,
) -> tuple[dict[str, Any], dict[str, Any]]:
    """Measure LMFAO rewriting through the shared benchmark collector."""
    request = parse_target(str(ROOT))
    files = optimizer_inputs(output, rewrite_rounds)
    requests = optimizer_requests(files, request, memory_limit_bytes)
    store = ReportStore(report_path or output / "optimizer.jsonl")
    console = Console(stderr=True)
    targets = resolve_requests(requests, store, samples, timeout, False, ROOT, ROOT, console)
    pending = plan_collection(store, requests, targets, samples, timeout, False)
    collect(store, pending, requests, targets, timeout, console)
    return optimizer_report(
        output, store, targets[request], files, samples, timeout, memory_limit_bytes, rewrite_rounds
    )


def optimizer_report(
    output: Path,
    store: ReportStore,
    target: ResolvedTarget,
    files: dict[str, FileSpec],
    samples: int,
    timeout: int,
    memory_limit_bytes: int | None,
    rewrite_rounds: int,
) -> tuple[dict[str, Any], dict[str, Any]]:
    """Read the shared collection and build the extractor for plan generation."""
    subprocess.run(
        ["cargo", "build", "--locked", "--release", "-p", "lmfao-extract"],
        cwd=ROOT,
        check=True,
        stdout=sys.stderr,
    )
    report: dict[str, Any] = {
        "rewrite_round_budget": rewrite_rounds,
        "optimizer": {},
        "extractor_path": str(extractor_path("release")),
        "extractor_sha256": sha256_file(extractor_path("release")),
        "binary_paths": {t: str(target.binary_path_for(t)) for t in MODES.values()},
        "binary_sha256": {t: target.binary_sha256_for(t) for t in MODES.values()},
        "optimizer_report": str(store.path),
        "optimizer_memory_limit_bytes": memory_limit_bytes,
    }
    successful = {}
    for mode, treatment in MODES.items():
        label = f"{mode}"
        endpoint = BenchmarkEndpoint(
            target.row, target.binary_sha256_for(treatment), treatment, memory_limit_bytes=memory_limit_bytes
        )
        selection = select_observations(store, endpoint, files[mode], samples, timeout)
        rows = [row.record for row in selection.rows]
        result = summarize_optimizer(rows, rewrite_rounds, samples, selection.issue)
        memory = [r["max_rss_bytes"] for r in rows if r["status"] == "success" and r["max_rss_bytes"] is not None]
        result.update(
            input_sha256=files[mode].sha256,
            peak_rss_mib=seconds_summary(v / 1024**2 for v in memory),
        )
        report["optimizer"][label] = result
        if selection.issue is None and all(r["status"] == "success" for r in rows) and len(rows) == samples:
            successful[label] = {"treatment": treatment}
    write_json(output / "optimizer-summary.json", report)
    return successful, report
