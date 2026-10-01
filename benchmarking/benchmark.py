"""Parse and compose pair-only benchmark collection, analysis, and output.

Workload resolution belongs in :mod:`benchmarking.workloads`, execution
planning and measurement in :mod:`benchmarking.collection`, and report data
access and presentation in :mod:`benchmarking.reports`. The public script owns
benchmark/profile dispatch.
"""

from __future__ import annotations

import argparse
import os
import subprocess
import sys
from collections import Counter
from collections.abc import Sequence
from pathlib import Path
from typing import cast

from rich.console import Console
from rich.text import Text

from .admission import PROOF_TREATMENTS, ProofTreatment
from .baseline_selection import BASELINE_ROUNDS, run_baseline_campaign
from .collection import (
    CollectionPlan,
    build_collection_plan,
    collect_rows,
    emit_collection_plan,
    label_has_enough_rows,
    preflight_collection,
    resolve_targets,
)
from .engines import TREATMENT_SPECS, TREATMENTS, Treatment, validate_engine_workload
from .models import (
    BenchmarkEndpoint,
    ComparisonSpec,
    DetailLevel,
    EndpointRequest,
    FileSpec,
    ResolvedTarget,
    TargetRequest,
    validate_unique_file_identities,
)
from .pilot import require_suite_admission
from .reports.grouped import grouped_report_path, write_grouped_report
from .reports.interactive import interactive_report_path, open_interactive_report, write_interactive_report
from .reports.presentation import build_report_catalog
from .reports.render import render_markdown_report_document, render_rich_report_document
from .reports.store import ReportStore
from .suites import SUITE_NAMES, build_coverage, render_coverage_markdown, resolve_suite
from .targets import git_root_for_path, parse_target
from .workloads import resolve_files

DEFAULT_REPORT = ".reports.jsonl"
DEFAULT_ROUNDS = 6
DEFAULT_TIMEOUT_SEC = 1800


def parse_benchmark_args(argv: Sequence[str]) -> argparse.Namespace:
    """Parse the public pair-only benchmark command."""

    parser = argparse.ArgumentParser(description="Collect or reuse one engine benchmark comparison.")
    parser.add_argument("--disequality-encoding", choices=("nee", "ee"), default="nee")
    parser.add_argument("--compare-disequality-encoding", choices=("nee", "ee"), default="nee")
    parser.add_argument("files", nargs="*", help="workload files to benchmark")
    parser.add_argument(
        "--suite",
        choices=SUITE_NAMES,
        action="append",
        help="captured family; repeat to select a union and reuse cached observations",
    )
    parser.add_argument(
        "--baseline-window",
        action="store_true",
        help=f"select suites by {BASELINE_ROUNDS} off runs: 0.1 < mean seconds < 30 (no memory filter)",
    )
    parser.add_argument(
        "--baseline-only",
        action="store_true",
        help="with --baseline-window, finish and snapshot normal-mode selection without running proofs",
    )
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
        "--treatment",
        choices=TREATMENTS,
        default=None,
        help="candidate treatment (default: proofs, or proof-extraction for --suite)",
    )
    parser.add_argument(
        "--compare-target",
        default=None,
        help="baseline target (default: candidate target)",
    )
    parser.add_argument(
        "--compare-treatment",
        choices=TREATMENTS,
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
        default=None,
        help=f"rows required per endpoint/file result (default: {DEFAULT_ROUNDS}, or 10 for --suite)",
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
    if args.suite is not None and (args.files or args.fact_directory is not None):
        parser.error("--suite is mutually exclusive with explicit files and --fact-directory")
    if args.suite is not None and args.detail == "summary":
        args.detail = "files"
    if args.treatment is None:
        args.treatment = "proof-extraction" if args.suite is not None else "proofs"
    if args.rounds is None:
        args.rounds = BASELINE_ROUNDS if args.suite is not None else DEFAULT_ROUNDS
    if args.baseline_only and not args.baseline_window:
        parser.error("--baseline-only requires --baseline-window")
    if args.baseline_window and (
        args.suite is None
        or args.rounds != BASELINE_ROUNDS
        or args.treatment not in PROOF_TREATMENTS
        or args.compare_treatment != "off"
        or args.compare_target is not None
        or args.force_run
    ):
        parser.error(
            f"--baseline-window requires --suite, {BASELINE_ROUNDS} rounds, proofs or proof-extraction versus off, "
            "one current target, and no --force-run"
        )
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
        cast(Treatment, str(args.compare_treatment)),
        args.compare_disequality_encoding,
    )
    candidate = EndpointRequest(
        candidate_target,
        cast(Treatment, str(args.treatment)),
        args.disequality_encoding,
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
            comparison.suite_mode,
            () if force_run else tuple(file for file, _reason in comparison.validation_issues),
        )
        for target, endpoints in endpoints_by_target.items()
    )


def main(argv: Sequence[str] | None = None) -> int:
    """Run the ordinary benchmark command."""

    raw_argv = tuple(sys.argv[1:] if argv is None else argv)
    args = parse_benchmark_args(raw_argv)
    console = Console(stderr=True)
    previous_guard = os.environ.get("EGGLOG_BENCH_MEMORY_GUARD")
    if args.suite is not None:
        os.environ["EGGLOG_BENCH_MEMORY_GUARD"] = "1"
    try:
        script_root = Path(__file__).resolve().parents[1]
        invocation_cwd = Path.cwd()
        repo_root = git_root_for_path(script_root)
        report_path = resolve_report_path(str(args.report), invocation_cwd)
        baseline_request, candidate_request = endpoint_requests(args)

        if args.baseline_window and (
            candidate_request.target.is_label_lookup
            or Path(candidate_request.target.source).expanduser().resolve() != script_root
        ):
            raise ValueError("--baseline-window requires the current checkout, for example --target figures=.")

        # ReportStore validates the complete existing artifact before target
        # materialization can build or run anything.
        store = ReportStore(report_path)
        suite = (
            resolve_suite(args.suite, script_root, include_normal_only=bool(args.baseline_window))
            if args.suite is not None
            else None
        )
        files = suite.files if suite is not None else resolve_files(args.files, invocation_cwd, args.fact_directory)
        if suite is not None and not files:
            rendered = render_coverage_markdown(build_coverage(suite, script_root / "benchmarks/local/pilot.jsonl"))
            if args.format == "markdown":
                sys.stdout.write(rendered + "\n")
            else:
                console.print(Text(rendered))
            return 0
        for endpoint in (baseline_request, candidate_request):
            physical_files = tuple(file.for_engine(TREATMENT_SPECS[endpoint.treatment].engine) for file in files)
            validate_unique_file_identities(physical_files)
            for file in physical_files:
                validate_engine_workload(file, endpoint.treatment)
        request_groups = group_endpoint_requests(baseline_request, candidate_request)
        resolved_targets = resolve_targets(
            request_groups,
            store,
            files,
            int(args.rounds),
            int(args.timeout_sec),
            bool(args.force_run),
            invocation_cwd,
            repo_root,
            console,
            suite is not None,
        )
        collection_complete = False
        try:
            validation_issues: tuple[tuple[FileSpec, str], ...] = ()
            baseline_comparison: ComparisonSpec | None = None
            if args.baseline_window:
                assert suite is not None
                baseline_comparison = run_baseline_campaign(
                    suite,
                    resolved_targets[candidate_request.target],
                    store,
                    int(args.timeout_sec),
                    console,
                    baseline_only=bool(args.baseline_only),
                    treatment=cast(ProofTreatment, args.treatment),
                )
                if baseline_comparison is None:
                    collection_complete = True
                    return 0
                files = baseline_comparison.files
                validation_issues = baseline_comparison.validation_issues
            elif suite is not None:
                while True:
                    # A new binary can invalidate cached failures, changing the
                    # shared workload subset and another label's cache needs.
                    files, diagnostics, validation_issues = require_suite_admission(
                        suite,
                        tuple(resolved_targets.values()),
                        store=store,
                        timeout_sec=int(args.timeout_sec),
                        rounds=int(args.rounds),
                        force_run=bool(args.force_run),
                        treatment="proofs" if args.treatment == "proofs" else "proof-extraction",
                    )
                    if not files:
                        break
                    incomplete_labels = tuple(
                        (request, endpoints)
                        for request, endpoints in request_groups
                        if resolved_targets[request].binary_path is None
                        and (
                            args.force_run
                            or not label_has_enough_rows(
                                store,
                                resolved_targets[request],
                                endpoints,
                                files,
                                int(args.rounds),
                                int(args.timeout_sec),
                                True,
                                tuple(file for file, _reason in validation_issues),
                            )
                        )
                    )
                    if not incomplete_labels:
                        break
                    resolved_targets.update(
                        resolve_targets(
                            incomplete_labels,
                            store,
                            files,
                            int(args.rounds),
                            int(args.timeout_sec),
                            bool(args.force_run),
                            invocation_cwd,
                            repo_root,
                            console,
                        )
                    )
                if len(diagnostics) > 10:
                    unavailable = Counter(
                        (case.family, "missing" if case.id in suite.capture_errors else case.status)
                        for case in suite.cases
                        if case.status != "captured" or case.id in suite.capture_errors
                    )
                    summary = [
                        f"{family}: {count} {status} source cases" for (family, status), count in unavailable.items()
                    ]
                    rejected = len(diagnostics) - sum(unavailable.values())
                    if rejected:
                        summary.append(f"classified {rejected} captured workload outcome{'s' if rejected != 1 else ''}")
                    console.print(Text("Suite preparation: " + "; ".join(summary) + "."))
                    console.print(
                        Text("Full reasons: benchmarks/local/coverage.md (refresh with make expanded-coverage).")
                    )
                else:
                    for diagnostic in diagnostics:
                        console.print(Text(diagnostic))
            if suite is not None and not files:
                hashes: dict[str, str] = {
                    binary.engine: binary.sha256
                    for target in resolved_targets.values()
                    for binary in target.engine_binaries
                }
                if not hashes:
                    hashes = {"egglog": next(iter(resolved_targets.values())).binary_sha256}
                rendered = render_coverage_markdown(
                    build_coverage(
                        suite,
                        script_root / "benchmarks/local/pilot.jsonl",
                        hashes,
                        store.records,
                        timeout_sec=int(args.timeout_sec),
                    )
                )
                if args.format == "markdown":
                    sys.stdout.write(rendered + "\n")
                else:
                    console.print(Text(rendered))
                collection_complete = True
                return 0
            comparison = ComparisonSpec(
                baseline=BenchmarkEndpoint(
                    resolved_targets[baseline_request.target],
                    baseline_request.treatment,
                    baseline_request.disequality_encoding,
                ),
                candidate=BenchmarkEndpoint(
                    resolved_targets[candidate_request.target],
                    candidate_request.treatment,
                    candidate_request.disequality_encoding,
                ),
                files=files,
                rounds=int(args.rounds),
                timeout_sec=int(args.timeout_sec),
                suite_mode=suite is not None,
                validation_issues=validation_issues,
            )
            # Preflight every fresh target before any measured observation can be
            # appended, then execute the already-validated plans in order.
            plans = () if args.baseline_window else collection_plans(store, comparison, bool(args.force_run))
            for plan in plans:
                preflight_collection(plan, comparison.timeout_sec)
            stopped_files: set[FileSpec] = set()
            for plan in plans:
                emit_collection_plan(console, plan)
                if comparison.suite_mode:
                    collect_rows(store, plan, comparison.timeout_sec, console, stopped_files)
                else:
                    collect_rows(store, plan, comparison.timeout_sec, console)
            collection_complete = True
        finally:
            try:
                grouped = store.grouped_report()
                write_grouped_report(grouped, grouped_report_path(report_path))
            except Exception as error:
                if collection_complete:
                    raise
                console.print(Text.assemble(("error:", "red"), " could not refresh grouped report: ", str(error)))

        catalog = build_report_catalog(grouped, comparison, cast(DetailLevel, str(args.detail)))
        if args.format == "markdown":
            rendered = render_markdown_report_document(catalog)
            sys.stdout.write(rendered + "\n")
        else:
            console.print(render_rich_report_document(catalog, console.width))
        if args.open:
            if args.format == "markdown":
                sys.stdout.flush()
            interactive_path = write_interactive_report(
                grouped,
                comparison,
                interactive_report_path(report_path),
            )
            console.print(f"Interactive benchmark report: {interactive_path}")
            open_interactive_report(interactive_path)
    except (OSError, ValueError, subprocess.CalledProcessError, subprocess.TimeoutExpired) as error:
        console.print(Text.assemble(("error:", "red"), " ", str(error)))
        return 2
    finally:
        if args.suite is not None:
            if previous_guard is None:
                os.environ.pop("EGGLOG_BENCH_MEMORY_GUARD", None)
            else:
                os.environ["EGGLOG_BENCH_MEMORY_GUARD"] = previous_guard
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
