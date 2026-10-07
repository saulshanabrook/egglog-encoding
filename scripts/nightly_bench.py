#!/usr/bin/env python3
"""Publish the standard nightly benchmark, including partial collection."""

from __future__ import annotations

import argparse
import html
import os
import subprocess
import sys
import tempfile
import time
from collections.abc import Sequence
from pathlib import Path

# Keep the documented direct-script invocation usable as well as python -m.
if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from rich.console import Console  # noqa: E402
from rich.text import Text  # noqa: E402

from benchmarking.benchmark import DEFAULT_ROUNDS, DEFAULT_TIMEOUT_SEC, positive_int  # noqa: E402
from benchmarking.collection import (  # noqa: E402
    build_collection_plan,
    collect_rows,
    emit_collection_plan,
    preflight_collection,
    resolve_targets,
)
from benchmarking.models import (  # noqa: E402
    BenchmarkEndpoint,
    ComparisonSpec,
    EndpointRequest,
    FileSpec,
    ResolvedTarget,
    Treatment,
)
from benchmarking.processes import COLLECTION_DEADLINE, BudgetExpired  # noqa: E402
from benchmarking.reports.grouped import grouped_report_path, write_grouped_report  # noqa: E402
from benchmarking.reports.interactive import write_interactive_report  # noqa: E402
from benchmarking.reports.store import ReportStore  # noqa: E402
from benchmarking.targets import parse_target  # noqa: E402
from benchmarking.workloads import resolve_files  # noqa: E402
from process_guard import ResourceStopped  # noqa: E402

type Target = tuple[str, str]

REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_OUTPUT_DIR = REPO_ROOT / "nightly" / "output"
REPORT_NAME = "index.jsonl"
PAGE_NAME = "index.html"
TARGETS: tuple[Target, ...] = (("branch", "."), ("main", "@origin/main"))
# Collect the headline and its ordinary-mode comparison on both checkouts first.
# Later modes share those off observations and the already-built executables.
TREATMENT_STAGES: tuple[tuple[Treatment, ...], ...] = (("off", "proofs"), ("term",), ("proof-extraction",))
DEFAULT_BUDGET_SEC = 5400
RENDER_RESERVE_SEC = 60
CARGO_BIN_DIR = Path(os.environ.get("CARGO_HOME") or Path.home() / ".cargo") / "bin"


def publish_report(
    store: ReportStore,
    resolved: dict[str, ResolvedTarget],
    files: tuple[FileSpec, ...],
    rounds: int,
    timeout_sec: int,
    page_path: Path,
    notes: Sequence[str],
) -> None:
    """Atomically publish only cached rows, choosing a valid initial comparison."""

    grouped = store.grouped_report()
    write_grouped_report(grouped, grouped_report_path(store.path))
    branch, main_target = resolved.get("branch"), resolved.get("main")
    if files and resolved:
        if branch is not None and main_target is not None and branch.binary_sha256 != main_target.binary_sha256:
            baseline = BenchmarkEndpoint(main_target, "proofs")
            candidate = BenchmarkEndpoint(branch, "proofs")
            report_notes = tuple(notes)
        else:
            target = branch or main_target or next(iter(resolved.values()))
            baseline = BenchmarkEndpoint(target, "off")
            candidate = BenchmarkEndpoint(target, "proofs")
            reason = (
                "branch and main have the same executable" if branch and main_target else "one target is unavailable"
            )
            report_notes = (*notes, f"Initial comparison uses {target.display_label} proofs / off because {reason}.")
        comparison = ComparisonSpec(baseline, candidate, files, rounds, timeout_sec, report_notes=report_notes)
        write_interactive_report(grouped, comparison, page_path)
        return
    # No binary identity exists to seed an interactive comparison.
    # Publish a status page without inventing an endpoint.
    message = "\n".join(notes) or "No benchmark targets were available."
    page = (
        "<!doctype html><html lang='en'><meta charset='utf-8'><title>Nightly benchmark</title>"
        "<h1>Nightly benchmark unavailable</h1><pre>" + html.escape(message) + "</pre></html>"
    )
    temporary: Path | None = None
    try:
        with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", dir=page_path.parent, delete=False) as handle:
            temporary = Path(handle.name)
            handle.write(page)
        os.replace(temporary, page_path)
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)


def main(argv: Sequence[str] | None = None) -> int:
    started = time.monotonic()
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output_dir", nargs="?", type=Path, default=DEFAULT_OUTPUT_DIR)
    parser.add_argument("--rounds", type=positive_int, default=DEFAULT_ROUNDS)
    parser.add_argument("--timeout-sec", type=positive_int, default=DEFAULT_TIMEOUT_SEC)
    parser.add_argument("--budget-sec", type=positive_int, default=DEFAULT_BUDGET_SEC)
    args = parser.parse_args(list(argv) if argv is not None else None)
    if args.budget_sec <= RENDER_RESERVE_SEC:
        parser.error(f"--budget-sec must exceed the {RENDER_RESERVE_SEC}-second rendering reserve")
    console = Console(stderr=True)
    output_dir = args.output_dir.expanduser().resolve()
    output_dir.mkdir(parents=True, exist_ok=True)
    report_path = output_dir / REPORT_NAME
    page_path = output_dir / PAGE_NAME
    for path in (report_path, page_path, grouped_report_path(report_path)):
        path.unlink(missing_ok=True)
    store = ReportStore(report_path)
    resolved: dict[str, ResolvedTarget] = {}
    notes: list[str] = []
    files: tuple[FileSpec, ...] = ()
    failed = False
    previous_path = os.environ.get("PATH")
    previous_guard = os.environ.get("EGGLOG_BENCH_MEMORY_GUARD")
    shims = str(CARGO_BIN_DIR)
    path = [entry for entry in os.environ.get("PATH", "").split(os.pathsep) if entry != shims]
    os.environ["PATH"] = os.pathsep.join((shims, *path))
    os.environ["EGGLOG_BENCH_MEMORY_GUARD"] = "1"
    token = COLLECTION_DEADLINE.set(started + args.budget_sec - RENDER_RESERVE_SEC)
    try:
        files = resolve_files((), REPO_ROOT, None)
        for label, source in TARGETS:
            request = parse_target(f"{label}={source}")
            endpoints = tuple(EndpointRequest(request, treatment) for stage in TREATMENT_STAGES for treatment in stage)
            try:
                resolved[label] = resolve_targets(
                    ((request, endpoints),),
                    store,
                    files,
                    args.rounds,
                    args.timeout_sec,
                    False,
                    REPO_ROOT,
                    REPO_ROOT,
                    console,
                    reuse_targets=tuple(resolved.values()),
                )[request]
            except ResourceStopped:
                raise
            except (OSError, ValueError, subprocess.CalledProcessError) as error:
                notes.append(f"{label}: target setup failed: {error}")
        for stage in TREATMENT_STAGES:
            plans = []
            for target in resolved.values():
                plan = build_collection_plan(
                    store,
                    target,
                    tuple(BenchmarkEndpoint(target, treatment) for treatment in stage),
                    files,
                    args.rounds,
                    args.timeout_sec,
                    False,
                )
                try:
                    preflight_collection(plan, args.timeout_sec)
                except ResourceStopped:
                    raise
                except (OSError, ValueError) as error:
                    notes.append(f"{target.display_label} {', '.join(stage)}: {error}")
                    continue
                plans.append(plan)
            for plan in plans:
                # Identical target executables share cache identities. Earlier
                # collection may have completed this alias's pending work.
                plan = build_collection_plan(
                    store,
                    plan.target,
                    tuple(BenchmarkEndpoint(plan.target, treatment) for treatment in stage),
                    files,
                    args.rounds,
                    args.timeout_sec,
                    False,
                )
                emit_collection_plan(console, plan)
                collect_rows(store, plan, args.timeout_sec, console)
                publish_report(store, resolved, files, args.rounds, args.timeout_sec, page_path, notes)
    except BudgetExpired as error:
        notes.append(f"Partial nightly: {error}; completed observations are retained.")
    except (ResourceStopped, OSError, ValueError, subprocess.SubprocessError) as error:
        notes.append(f"Partial nightly: collection stopped: {error}")
        failed = True
    finally:
        COLLECTION_DEADLINE.reset(token)
        for key, previous in (("PATH", previous_path), ("EGGLOG_BENCH_MEMORY_GUARD", previous_guard)):
            if previous is None:
                os.environ.pop(key, None)
            else:
                os.environ[key] = previous
        for note in notes:
            console.print(Text(note))
        publish_report(store, resolved, files, args.rounds, args.timeout_sec, page_path, notes)
        console.print(Text(f"nightly: wrote report to {page_path}"))
    return int(failed or not resolved)


if __name__ == "__main__":
    raise SystemExit(main())
