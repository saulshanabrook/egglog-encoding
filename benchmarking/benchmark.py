"""Compose ordinary benchmark collection, persistence, analysis, and output.

CLI policy belongs in :mod:`benchmarking.benchmark_config`, execution planning
and measurement in :mod:`benchmarking.collection`, report data access and
presentation in :mod:`benchmarking.reports`, and profile dispatch in
:mod:`benchmarking.cli`.
"""

from __future__ import annotations

import subprocess
import sys
from collections.abc import Sequence
from pathlib import Path

from .benchmark_config import (
    parse_backends,
    parse_benchmark_args,
    parse_treatments,
    resolve_files,
    validate_spec,
)
from .collection import (
    EstimateModel,
    build_collection_plan,
    collect_rows,
    emit_collection_plan,
    preflight_collection,
    resolve_target,
)
from .models import BenchmarkSpec, validate_unique_target_binaries
from .output import RunnerOutput
from .reports.database import ReportDatabase
from .reports.render import render_markdown_report_document, render_rich_report_document
from .reports.summary import build_report_document
from .targets import git_root_for_path, parse_target


def resolve_report_path(raw_path: str, invocation_cwd: Path) -> Path:
    """Resolve the required append-only report path from the invocation cwd."""

    path = Path(raw_path).expanduser()
    if not path.is_absolute():
        path = invocation_cwd / path
    return path.resolve()


def wait_for_duckdb_ui_exit(output: RunnerOutput) -> None:
    """Keep the transient report session alive until the user dismisses it."""

    output.console.print("DuckDB UI is active. Press Enter or Ctrl-C to close it and exit.")
    try:
        if sys.stdin.readline() == "":
            raise ValueError("DuckDB UI input closed before the session was dismissed")
    except KeyboardInterrupt:
        output.console.print()


def main(argv: Sequence[str] | None = None) -> int:
    """Run the ordinary benchmark command."""

    raw_argv = tuple(sys.argv[1:] if argv is None else argv)
    args = parse_benchmark_args(raw_argv)
    output = RunnerOutput()
    try:
        if args.duckdb_ui and not sys.stdin.isatty():
            raise ValueError("--duckdb-ui requires an interactive terminal on stdin")
        script_root = Path(__file__).resolve().parents[1]
        invocation_cwd = Path.cwd()
        repo_root = git_root_for_path(script_root)
        report_path = resolve_report_path(str(args.report), invocation_cwd)

        # ReportDatabase validates the complete existing artifact before target
        # materialization can build or run anything.
        with ReportDatabase(report_path) as database:
            backends = parse_backends(str(args.backend))
            treatments = parse_treatments(str(args.treatments))
            files = resolve_files(args.files, invocation_cwd, args.fact_directory)
            spec = BenchmarkSpec(
                files=files,
                treatments=treatments,
                rounds=args.rounds,
                timeout_sec=args.timeout_sec,
                backends=backends,
            )
            validate_spec(spec)
            target_specs = args.target if args.target is not None else ["."]
            target_requests = tuple(parse_target(raw) for raw in target_specs)
            estimate_model = EstimateModel.from_aggregates(database.successful_estimate_aggregates())
            targets = tuple(
                resolve_target(
                    request,
                    database,
                    spec,
                    args.force_run,
                    invocation_cwd,
                    repo_root,
                    output,
                )
                for request in target_requests
            )
            validate_unique_target_binaries(targets)
            # Preflight every fresh target before any measured observation can
            # be appended, then execute the already-validated plans in order.
            plans = tuple(build_collection_plan(database, target, spec, args.force_run) for target in targets)
            preflights = tuple(preflight_collection(plan, spec) for plan in plans)
            for plan, startup_warmup in zip(plans, preflights, strict=True):
                emit_collection_plan(output, plan, estimate_model)
                collect_rows(database, plan, spec, output, estimate_model, startup_warmup)

            document = build_report_document(
                database,
                targets,
                spec,
                command_argv=raw_argv if args.format == "markdown" else None,
                phase_timings=bool(args.phase_timings),
                detailed_timing=bool(args.detailed_timing),
            )
            if args.format == "markdown":
                rendered = render_markdown_report_document(document)
                sys.stdout.write(rendered + "\n")
            else:
                output.console.print(render_rich_report_document(document, output.console.width))
            if args.duckdb_ui:
                # Markdown may be redirected and block-buffered. Make the
                # completed report observable before the interactive wait.
                sys.stdout.flush()
                output.console.print(database.start_ui())
                wait_for_duckdb_ui_exit(output)
    except (FileNotFoundError, ValueError, subprocess.CalledProcessError, subprocess.TimeoutExpired) as error:
        output.print_error(error)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
