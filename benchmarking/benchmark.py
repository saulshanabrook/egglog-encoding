"""Parse and compose pair-only benchmark collection, analysis, and output.

Workload resolution belongs in :mod:`benchmarking.workloads`, execution
planning and measurement in :mod:`benchmarking.collection`, and report data
access and presentation in :mod:`benchmarking.reports`. The public script owns
benchmark/profile dispatch.
"""

from __future__ import annotations

import argparse
import subprocess
import sys
from collections.abc import Sequence
from pathlib import Path
from typing import cast

from rich.console import Console
from rich.text import Text

from .collection import (
    CollectionPlan,
    build_collection_plan,
    collect_rows,
    emit_collection_plan,
    preflight_collection,
    resolve_targets,
)
from .models import (
    BACKEND_SPECS,
    Backend,
    BenchmarkEndpoint,
    ComparisonSpec,
    DetailLevel,
    EndpointRequest,
    ResolvedTarget,
    TargetRequest,
    Treatment,
)
from .reports.interactive import interactive_report_path, open_interactive_report, write_interactive_report
from .reports.presentation import build_report_catalog
from .reports.render import render_markdown_report_document, render_rich_report_document
from .reports.store import ReportStore
from .targets import git_root_for_path, parse_target
from .workloads import resolve_files

DEFAULT_REPORT = ".reports.jsonl"
DEFAULT_ROUNDS = 6
DEFAULT_TIMEOUT_SEC = 120


def parse_benchmark_args(argv: Sequence[str]) -> argparse.Namespace:
    """Parse the public pair-only benchmark command."""

    parser = argparse.ArgumentParser(description="Collect or reuse one egglog benchmark comparison.")
    parser.add_argument("files", nargs="*", help="egglog files to benchmark")
    parser.add_argument(
        "--fact-directory",
        default=None,
        help="fact directory used by explicitly selected benchmark files",
    )
    parser.add_argument(
        "--target",
        default=".",
        help="candidate target: ., /path, @git-ref, #pr, label=source, or label=",
    )
    parser.add_argument(
        "--backend",
        choices=tuple(BACKEND_SPECS),
        default="main",
        help="candidate backend (default: main)",
    )
    parser.add_argument(
        "--treatment",
        choices=("off", "term", "proofs", "proof-extraction"),
        default="proofs",
        help="candidate treatment (default: proofs)",
    )
    parser.add_argument(
        "--compare-target",
        default=None,
        help="baseline target (default: candidate target)",
    )
    parser.add_argument(
        "--compare-backend",
        choices=tuple(BACKEND_SPECS),
        default="main",
        help="baseline backend (default: main)",
    )
    parser.add_argument(
        "--compare-treatment",
        choices=("off", "term", "proofs", "proof-extraction"),
        default="off",
        help="baseline treatment (default: off)",
    )
    parser.add_argument(
        "--detail",
        choices=("summary", "files", "phases", "rulesets"),
        default="summary",
        help="cumulative report detail (default: summary)",
    )
    parser.add_argument(
        "--report",
        default=DEFAULT_REPORT,
        help=f"append-only JSONL report/cache path (default: {DEFAULT_REPORT})",
    )
    parser.add_argument(
        "--format",
        choices=("rich", "markdown"),
        default="rich",
        help="final report format: rich to stderr, or markdown to stdout (default: rich)",
    )
    parser.add_argument(
        "--rounds",
        type=positive_int,
        default=DEFAULT_ROUNDS,
        help=f"rows required per endpoint/file result (default: {DEFAULT_ROUNDS})",
    )
    parser.add_argument(
        "--timeout-sec",
        type=positive_int,
        default=DEFAULT_TIMEOUT_SEC,
        help=f"per-process timeout in seconds (default: {DEFAULT_TIMEOUT_SEC})",
    )
    parser.add_argument(
        "--force-run",
        action="store_true",
        help="append fresh rows for both endpoints even when enough cached rows exist",
    )
    parser.add_argument(
        "--open",
        action="store_true",
        help="write an interactive HTML snapshot next to the report cache and open it",
    )
    args = parser.parse_args(argv)
    if args.report == "-":
        parser.error("--report requires a file path; '-' streaming is not supported")
    args.command = "benchmark"
    return args


def positive_int(value: str) -> int:
    """Parse a positive integer for one benchmark CLI option."""

    parsed = int(value)
    if parsed <= 0:
        raise argparse.ArgumentTypeError("must be positive")
    return parsed


def resolve_report_path(raw_path: str, invocation_cwd: Path) -> Path:
    """Resolve the required append-only report path from the invocation cwd."""

    path = Path(raw_path).expanduser()
    if not path.is_absolute():
        path = invocation_cwd / path
    return path.resolve()


def endpoint_requests(args: argparse.Namespace) -> tuple[EndpointRequest, EndpointRequest]:
    """Return validated baseline and candidate requests from parsed CLI values."""

    candidate_target = parse_target(str(args.target))
    baseline_target = parse_target(str(args.compare_target)) if args.compare_target is not None else candidate_target
    baseline = EndpointRequest(
        baseline_target,
        cast(Backend, str(args.compare_backend)),
        cast(Treatment, str(args.compare_treatment)),
    )
    candidate = EndpointRequest(
        candidate_target,
        cast(Backend, str(args.backend)),
        cast(Treatment, str(args.treatment)),
    )
    if baseline == candidate:
        raise ValueError("baseline and candidate endpoints must be different")
    return baseline, candidate


def group_endpoint_requests(
    baseline: EndpointRequest,
    candidate: EndpointRequest,
) -> tuple[tuple[TargetRequest, tuple[EndpointRequest, ...]], ...]:
    """Group endpoint requests by target while preserving baseline-first order."""

    grouped: dict[TargetRequest, list[EndpointRequest]] = {}
    for endpoint in (baseline, candidate):
        grouped.setdefault(endpoint.target, []).append(endpoint)
    return tuple((target, tuple(endpoints)) for target, endpoints in grouped.items())


def collection_plans(
    store: ReportStore,
    comparison: ComparisonSpec,
    force_run: bool,
) -> tuple[CollectionPlan, ...]:
    """Group exact endpoints by resolved target so each target is preflighted once."""

    endpoints_by_target: dict[ResolvedTarget, list[BenchmarkEndpoint]] = {}
    for endpoint in (comparison.baseline, comparison.candidate):
        endpoints_by_target.setdefault(endpoint.target, []).append(endpoint)
    return tuple(
        build_collection_plan(
            store,
            target,
            tuple(endpoints),
            comparison.files,
            comparison.rounds,
            comparison.timeout_sec,
            force_run,
        )
        for target, endpoints in endpoints_by_target.items()
    )


def main(argv: Sequence[str] | None = None) -> int:
    """Run the ordinary benchmark command."""

    raw_argv = tuple(sys.argv[1:] if argv is None else argv)
    args = parse_benchmark_args(raw_argv)
    console = Console(stderr=True)
    try:
        script_root = Path(__file__).resolve().parents[1]
        invocation_cwd = Path.cwd()
        repo_root = git_root_for_path(script_root)
        report_path = resolve_report_path(str(args.report), invocation_cwd)
        baseline_request, candidate_request = endpoint_requests(args)

        # ReportStore validates the complete existing artifact before target
        # materialization can build or run anything.
        store = ReportStore(report_path)
        files = resolve_files(args.files, invocation_cwd, args.fact_directory)
        resolved_targets = resolve_targets(
            group_endpoint_requests(baseline_request, candidate_request),
            store,
            files,
            int(args.rounds),
            int(args.timeout_sec),
            bool(args.force_run),
            invocation_cwd,
            repo_root,
            console,
        )
        comparison = ComparisonSpec(
            baseline=BenchmarkEndpoint(
                resolved_targets[baseline_request.target],
                baseline_request.backend,
                baseline_request.treatment,
            ),
            candidate=BenchmarkEndpoint(
                resolved_targets[candidate_request.target],
                candidate_request.backend,
                candidate_request.treatment,
            ),
            files=files,
            rounds=int(args.rounds),
            timeout_sec=int(args.timeout_sec),
        )
        # Preflight every fresh target before any measured observation can be
        # appended, then execute the already-validated plans in order.
        plans = collection_plans(store, comparison, bool(args.force_run))
        for plan in plans:
            preflight_collection(plan, comparison.timeout_sec)
        for plan in plans:
            emit_collection_plan(console, plan)
            collect_rows(store, plan, comparison.timeout_sec, console)

        catalog = build_report_catalog(store, comparison, cast(DetailLevel, str(args.detail)))
        if args.format == "markdown":
            rendered = render_markdown_report_document(catalog)
            sys.stdout.write(rendered + "\n")
        else:
            console.print(render_rich_report_document(catalog, console.width))
        if args.open:
            if args.format == "markdown":
                sys.stdout.flush()
            interactive_path = write_interactive_report(
                store,
                comparison,
                interactive_report_path(report_path),
            )
            console.print(f"Interactive benchmark report: {interactive_path}")
            open_interactive_report(interactive_path)
    except (OSError, ValueError, subprocess.CalledProcessError, subprocess.TimeoutExpired) as error:
        console.print(Text.assemble(("error:", "red"), " ", str(error)))
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
