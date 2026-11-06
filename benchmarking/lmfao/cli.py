"""Compare egraph logical optimization with the original LMFAO C++ pipeline."""

from __future__ import annotations

import argparse
import json
import math
import os
import subprocess
import sys
import time
from collections.abc import Sequence
from pathlib import Path
from typing import Any

from benchmarking.config import DEFAULT_MEMORY_LIMIT_BYTES, DEFAULT_TIMEOUT_SEC
from benchmarking.native_memory import add_memory_limit_options
from benchmarking.targets import sha256_file
from benchmarks.reproduction.lmfao.prepare import verify_backend

from . import backend, model
from .data import load_data, reference_results
from .optimizer import TREATMENTS, collect_optimizers, seconds_summary, write_json
from .report import comparison_markdown, plan_text, preparation_costs


def status(message: str) -> None:
    print(message, file=sys.stderr, flush=True)


def run(args: argparse.Namespace) -> None:
    provenance = verify_backend(args.backend)
    if args.cpu is not None:
        os.sched_setaffinity(0, {args.cpu})
    out = args.output_dir
    out.mkdir(parents=True, exist_ok=True)
    documents, optimizer = collect_optimizers(
        out,
        args.samples,
        args.timeout,
        args.report,
        args.memory_limit_bytes,
        treatments=tuple(args.treatment or TREATMENTS),
        variants=tuple(args.variant or ("single-root", "roots", "shared")),
    )
    if not documents:
        raise RuntimeError("the logical experiment requires at least one successfully exported graph")
    metadata: dict[str, Any] = {
        "cpu_affinity": sorted(os.sched_getaffinity(0)),
        "backend_sha256": sha256_file(args.backend),
        "backend_provenance": provenance,
        "cxx_version": subprocess.check_output(["g++", "--version"], text=True).splitlines()[0],
        "backend_corrections": ["dependent-output.patch"],
        "dag_timeout_seconds": args.dag_timeout,
        "timing_scope": (
            "execution is whole C++ process wall time, including loading and sorting; "
            "code generation, compilation and checking excluded. "
            "Upstream computation time excludes loading and sorting"
        ),
        "lmfao_commit": model.COMMIT,
    }
    plans: dict[str, Any] = {}
    plan_summaries: dict[str, Any] = {}
    aliases: dict[str, str] = {}
    signatures: dict[str, str] = {}
    builds: dict[str, Any] = {}
    canonical = ["original"]
    controls = {f"shared-ordinary-{name}": name for name in args.binding_control or []}
    for label in ["original", *documents, *controls]:
        settings = None
        if label != "original":
            if label in controls:
                variant, treatment = "shared", "off"
            else:
                variant, treatment = label.split("-slotted", 1)
                treatment = "slotted" + treatment
            settings = {
                "variant": variant,
                "treatment": treatment,
                "binary": optimizer["binary_paths"].get(treatment),
                "extractor": optimizer["extractor_path"],
                "binding_control": controls.get(label),
                "timeout": args.timeout,
                "memory_limit_bytes": args.memory_limit_bytes,
                "dag_timeout": args.dag_timeout,
            }
        status(f"Running LMFAO frontend, logical optimizer and code generation: {label}")
        directory = out / label
        builds[label] = backend.generate(args.backend, args.data, directory, settings, timeout=args.build_timeout)
        plan = model.read_plan(directory / "plan.json")
        plan_summaries[label] = {
            "views": len(plan["views"]),
            "aggregate_columns": sum(len(v["aggregates"]) for v in plan["views"]),
            "query_roots": [o["root"] for o in plan["outputs"]],
        }
        (directory / "plan.txt").write_text(plan_text(plan))
        if label == "original":
            continue
        plans[label] = json.loads((directory / "extraction.json").read_text())
        plan_summaries[label]["structural_cost"] = plans[label]["estimated_cost"]
        signature = json.dumps(plan, sort_keys=True)
        if signature in signatures:
            aliases[label] = signatures[signature]
        else:
            signatures[signature] = label
            canonical.append(label)
    write_json(out / "identical-plans.json", aliases)
    status("Computing independent decimal answers outside pipeline timing")
    start = time.perf_counter()
    db, data_metadata = load_data(args.data)
    metadata.update(data_metadata)
    try:
        expected = reference_results(db)
    finally:
        db.close()
    metadata["validation_preparation_seconds"] = time.perf_counter() - start
    write_json(out / "metadata.json", metadata)
    validation = {}
    for label in canonical:
        status(f"Compiling {label}")
        directory = out / label
        builds[label].update(
            backend.compile(directory, flags=args.cxxflags, jobs=args.jobs, timeout=args.build_timeout)
        )
        status(f"Checking all 140 outputs for {label}")
        validation[label] = backend.validate(directory, expected, flags=args.cxxflags, timeout=args.build_timeout)
        builds[label]["executable_sha256"] = sha256_file(directory / "lmfao")
        write_json(out / "builds.json", builds)
        write_json(out / "validation.json", validation)
    # Validation is the warmup. Timed programs omit output dumping and checking.
    rows: list[dict[str, Any]] = []
    labels = list(canonical)
    with (out / "execution.jsonl").open("w") as stream:
        for repeat in range(args.samples):
            order = labels[repeat % len(labels) :] + labels[: repeat % len(labels)]
            if repeat % 2:
                order.reverse()
            for label in order:
                row = {"label": label, "repeat": repeat, **backend.execute(out / label, repeat, args.timeout)}
                rows.append(row)
                stream.write(json.dumps(row) + "\n")
                stream.flush()
                status(f"  {label}: {row['process_seconds']:.3f}s")
    report = {
        **optimizer,
        "binding_controls": controls,
        "metadata": metadata,
        "plans": plans,
        "plan_summaries": plan_summaries,
        "builds": builds,
        "validation": validation,
        "execution_aliases": aliases,
        "accounted_pipeline": preparation_costs(plans, builds, aliases),
        "execution": {
            label: {
                phase: seconds_summary(row[phase] for row in rows if row["label"] == label)
                for phase in ("process_seconds", "computation_seconds")
            }
            for label in labels
        },
        "phase_scope": (
            "Execution reports computation time separately from whole-process time including loading/sorting. "
            "accounted_pipeline separates optimization/generation and compilation, "
            "with one observation per preparation phase. Its phase sum is not a measured end-to-end runtime. "
            "Generation includes the frontend, optimizer subprocess and backend. Identical plans reuse compilation "
            "and execution observations, charged in full. "
            "Original logical optimization is included in its code-generation phase. Independent validation, "
            "isomorphism checks and tool builds are excluded for both. Separate optimizer-only benchmark "
            "samples and diagnostic graph exports are excluded; the hook reruns rewriting for the exported workload."
        ),
    }
    write_json(out / "pipeline.json", report)
    (out / "comparison.md").write_text(comparison_markdown(report))
    print(json.dumps(report, indent=2))


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--data", type=Path, required=True)
    parser.add_argument("--backend", type=Path, required=True, help="Pinned multifaq executable with optimizer bridge")
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument(
        "--treatment", choices=TREATMENTS, action="append", help="Repeat to select engines; default both"
    )
    parser.add_argument(
        "--variant",
        choices=("single-root", "roots", "shared"),
        action="append",
        help="Repeat to select variants; default all",
    )
    parser.add_argument(
        "--binding-control",
        choices=("named", "canonical"),
        action="append",
        help="Also extract and execute ordinary-egglog shared plans with literal or canonical binder names",
    )
    parser.add_argument(
        "--rounds", "--samples", dest="samples", type=int, default=5, help="Measured executions, not rewrite rounds"
    )
    parser.add_argument("--timeout-sec", "--timeout", dest="timeout", type=int, default=DEFAULT_TIMEOUT_SEC)
    parser.add_argument("--report", type=Path, help="Append-only optimizer cache; default OUTPUT/optimizer.jsonl")
    add_memory_limit_options(parser, default=DEFAULT_MEMORY_LIMIT_BYTES)
    parser.add_argument("--dag-timeout", type=float, default=30)
    parser.add_argument("--build-timeout", type=int, default=900)
    parser.add_argument("--jobs", type=int, default=4)
    parser.add_argument("--cxxflags", default=backend.FLAGS)
    parser.add_argument("--cpu", type=int)
    args = parser.parse_args(argv)
    for name in ("treatment", "variant", "binding_control"):
        values = getattr(args, name)
        if values and len(values) != len(set(values)):
            parser.error(f"duplicate --{name.replace('_', '-')} selection")
    if args.report == Path("-"):
        parser.error("--report requires a filesystem path, not '-'")
    if min(args.samples, args.timeout, args.build_timeout, args.jobs) < 1:
        parser.error("rounds, timeouts and jobs must be positive")
    if not math.isfinite(args.dag_timeout) or args.dag_timeout <= 0:
        parser.error("DAG timeout must be finite and positive")
    for name in ("output_dir", "data", "backend", "report"):
        if getattr(args, name) is not None:
            setattr(args, name, getattr(args, name).resolve())
    run(args)
    return 0
