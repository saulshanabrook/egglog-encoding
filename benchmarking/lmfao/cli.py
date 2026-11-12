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
from .optimizer import OptimizerCollection, collect_optimizers, collect_replays, seconds_summary, write_json
from .program import DEFAULT_ROUNDS, benchmark_input, plan_checks
from .report import comparison_markdown, plan_text, preparation_costs


def status(message: str) -> None:
    print(message, file=sys.stderr, flush=True)


def run(args: argparse.Namespace, *, collected: OptimizerCollection | None = None) -> dict[str, Any]:
    provenance = verify_backend(args.backend)
    if args.cpu is not None:
        if not hasattr(os, "sched_setaffinity"):
            raise ValueError("CPU affinity is not supported on this platform")
        os.sched_setaffinity(0, {args.cpu})
    out = args.output_dir
    out.mkdir(parents=True, exist_ok=True)
    collected = (
        collected
        if collected is not None
        else collect_optimizers(
            out,
            args.samples,
            args.timeout,
            args.report,
            args.memory_limit_bytes,
            rewrite_rounds=args.rewrite_rounds,
            threads=args.threads,
            policy_file=args.policy_file,
        )
    )
    documents, optimizer = collected.successful, collected.report
    metadata: dict[str, Any] = {
        "cpu_affinity": sorted(os.sched_getaffinity(0)) if hasattr(os, "sched_getaffinity") else None,
        "egraph_workers": args.threads,
        "dag_workers": 1,
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
    baselines = ["original", "paper"]
    canonical = baselines.copy()
    for label in [*baselines, *documents]:
        settings = None
        if label not in baselines:
            treatment = documents[label]["treatment"]
            settings = {
                "treatment": treatment,
                "extractor": optimizer["extractor_path"],
                "timeout": args.timeout,
                "memory_limit_bytes": args.memory_limit_bytes,
                "dag_timeout": args.dag_timeout,
                "rewrite_rounds": args.rewrite_rounds,
                "threads": args.threads,
            }
        status(f"Running LMFAO frontend, logical optimizer and code generation: {label}")
        directory = out / label
        try:
            builds[label] = backend.generate(
                args.backend,
                args.data,
                directory,
                settings,
                timeout=args.build_timeout,
                root_policy="paper" if label == "paper" else None,
            )
        except RuntimeError as error:
            if label in baselines:
                raise
            optimizer["optimizer"][label]["pipeline_issue"] = str(error)
            status(f"  {label}: plan unavailable; {error}")
            continue
        plan = model.read_plan(directory / "plan.json")
        plan_summaries[label] = {
            "views": len(plan["views"]),
            "aggregate_columns": sum(len(v["aggregates"]) for v in plan["views"]),
            "query_roots": [o["root"] for o in plan["outputs"]],
        }
        (directory / "plan.txt").write_text(plan_text(plan))
        if label in baselines:
            continue
        if label == "slotted":
            source = benchmark_input("slotted", directory, args.rewrite_rounds)
            (directory / "proof.egg").write_text(source.read_text() + plan_checks(plan))
        plans[label] = json.loads((directory / "extraction.json").read_text())
        plan_summaries[label]["structural_cost"] = plans[label]["estimated_cost"]
        signature = json.dumps(plan, sort_keys=True)
        if signature in signatures:
            aliases[label] = signatures[signature]
        else:
            signatures[signature] = label
            canonical.append(label)
    write_json(out / "identical-plans.json", aliases)
    replays = {}
    if "slotted" in plans:
        status("Replaying the selected plan with proofs off and with proof production")
        replays = collect_replays(
            collected,
            out / "slotted/proof.egg",
            args.samples,
            3 * args.timeout,
            args.memory_limit_bytes,
            args.rewrite_rounds,
            args.threads,
        )
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
        "proof_replay": replays,
        "proof_replay_timeout_seconds": 3 * args.timeout,
        "metadata": metadata,
        "plans": plans,
        "plan_summaries": plan_summaries,
        "builds": builds,
        "validation": validation,
        "execution_aliases": aliases,
        "execution_observations": rows,
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
            "Generation includes query export, frozen-input validation, optimization and code generation. "
            "Identical plans reuse compilation "
            "and execution observations, charged in full. "
            "Original logical optimization is included in its code-generation phase. Independent validation, "
            "tool builds are excluded for both. Separate optimizer-only benchmark "
            "samples are excluded; preparation reruns rewriting for the exported workload."
        ),
    }
    write_json(out / "pipeline.json", report)
    (out / "comparison.md").write_text(comparison_markdown(report))
    return report


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--data", type=Path, required=True)
    parser.add_argument("--backend", type=Path, required=True, help="Pinned multifaq executable with optimizer bridge")
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--rewrite-rounds", type=int, default=DEFAULT_ROUNDS, help="Egraph rewrite-round budget")
    parser.add_argument("--format", choices=("markdown", "json"), default="markdown", help="Final report on stdout")
    parser.add_argument(
        "--rounds", "--samples", dest="samples", type=int, default=5, help="Measured executions, not rewrite rounds"
    )
    parser.add_argument("--timeout-sec", "--timeout", dest="timeout", type=int, default=DEFAULT_TIMEOUT_SEC)
    parser.add_argument("--report", type=Path, help="Append-only optimizer cache; default OUTPUT/optimizer.jsonl")
    parser.add_argument(
        "--policy-file", type=Path, help="Campaign exclusion overlay; patterns are relative to benchmarks/"
    )
    add_memory_limit_options(parser, default=DEFAULT_MEMORY_LIMIT_BYTES)
    parser.add_argument("--dag-timeout", type=float, default=30)
    parser.add_argument("--build-timeout", type=int, default=900)
    parser.add_argument("--jobs", type=int, default=4)
    parser.add_argument("--threads", type=int, default=1, help="Egraph workers; shared DAG extraction remains serial")
    parser.add_argument("--cxxflags", default=backend.FLAGS)
    parser.add_argument("--cpu", type=int)
    args = parser.parse_args(argv)
    if args.cpu is not None and not hasattr(os, "sched_setaffinity"):
        parser.error("--cpu is not supported on this platform")
    if args.report == Path("-"):
        parser.error("--report requires a filesystem path, not '-'")
    if min(args.samples, args.rewrite_rounds, args.timeout, args.build_timeout, args.jobs, args.threads) < 1:
        parser.error("rounds, timeouts and jobs must be positive")
    if not math.isfinite(args.dag_timeout) or args.dag_timeout <= 0:
        parser.error("DAG timeout must be finite and positive")
    for name in ("output_dir", "data", "backend", "report", "policy_file"):
        if getattr(args, name) is not None:
            setattr(args, name, getattr(args, name).resolve())
    return args


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    report = run(args)
    print(json.dumps(report, indent=2) if args.format == "json" else comparison_markdown(report), end="\n")
    return 0
