"""Define workload selection, validation, and benchmark CLI parsing.

Profiling reuses the workload and validation helpers here. Backend metadata,
capabilities, and canonical cell ordering belong in :mod:`benchmarking.models`;
execution and report presentation belong in their dedicated modules.
"""

from __future__ import annotations

import argparse
import re
from collections.abc import Sequence
from dataclasses import dataclass
from pathlib import Path
from typing import cast

from .models import (
    BACKEND_SPECS,
    DEFAULT_BACKENDS,
    Backend,
    BenchmarkSpec,
    FileSpec,
    Treatment,
    benchmark_cells,
    validate_unique_file_identities,
)
from .targets import sha256_directory, sha256_file

DEFAULT_REPORT = ".reports.jsonl"
DEFAULT_ROUNDS = 6
DEFAULT_TIMEOUT_SEC = 120
DEFAULT_TREATMENTS: tuple[Treatment, ...] = ("off", "term", "proofs")


@dataclass(frozen=True)
class WorkloadConfig:
    file: str
    fact_directory: str | None = None


DEFAULT_WORKLOADS = (
    WorkloadConfig("egglog/tests/math-microbenchmark.egg"),
    WorkloadConfig("egglog-experimental/tests/fixtures/eggcc-2mm-pass1.egg"),
    WorkloadConfig(
        "benchmarks/pointer-analysis-small.egg",
        "benchmarks/data/pointer-analysis-small",
    ),
    WorkloadConfig("egglog/tests/hardboiled_conv1d_32.egg"),
    WorkloadConfig("benchmarks/luminal-llama.egg"),
    WorkloadConfig("egglog/tests/web-demo/herbie.egg"),
)


def parse_benchmark_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Collect or reuse egglog-experimental benchmark reports.",
    )
    parser.add_argument(
        "files",
        nargs="*",
        help="egglog files to benchmark",
    )
    parser.add_argument(
        "--fact-directory",
        default=None,
        help="fact directory used by explicitly selected benchmark files",
    )
    parser.add_argument(
        "--target",
        action="append",
        default=None,
        help="target source: ., /path, @git-ref, #pr, label=source, or label=",
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
        help=f"rows required per target/file/backend/treatment result (default: {DEFAULT_ROUNDS})",
    )
    parser.add_argument(
        "--timeout-sec",
        type=positive_int,
        default=DEFAULT_TIMEOUT_SEC,
        help=f"per-process timeout in seconds (default: {DEFAULT_TIMEOUT_SEC})",
    )
    parser.add_argument(
        "--backend",
        default=",".join(DEFAULT_BACKENDS),
        help=f"comma-separated backends: {', '.join(BACKEND_SPECS)} (default: {','.join(DEFAULT_BACKENDS)})",
    )
    parser.add_argument(
        "--treatments",
        default=",".join(DEFAULT_TREATMENTS),
        help="comma-separated treatments (default: off,term,proofs)",
    )
    parser.add_argument(
        "--force-run",
        action="store_true",
        help="append fresh rows even when enough cached rows exist",
    )
    parser.add_argument(
        "--phase-timings",
        action="store_true",
        help="display the compact timing breakdown stored with selected observations",
    )
    parser.add_argument(
        "--detailed-timing",
        action="store_true",
        help="display every recorded ruleset for all selected target/file/backend/treatment results",
    )
    parser.add_argument(
        "--duckdb-ui",
        action="store_true",
        help="open the scoped report views in DuckDB's local UI (requires interactive stdin)",
    )
    args = parser.parse_args(argv)
    if args.report == "-":
        parser.error("--report requires a file path; '-' streaming is not supported")
    if args.detailed_timing:
        args.phase_timings = True
    args.command = "benchmark"
    return args


def positive_int(value: str) -> int:
    parsed = int(value)
    if parsed <= 0:
        raise argparse.ArgumentTypeError("must be positive")
    return parsed


def parse_treatments(value: str) -> tuple[Treatment, ...]:
    treatments: list[Treatment] = []
    seen: set[str] = set()
    for raw in value.split(","):
        item = raw.strip()
        if not item:
            continue
        if item not in {"off", "term", "proofs"}:
            raise ValueError(f"unknown treatment: {item}")
        if item in seen:
            raise ValueError(f"duplicate treatment: {item}")
        seen.add(item)
        treatments.append(cast(Treatment, item))
    if not treatments:
        raise ValueError("at least one treatment is required")
    return tuple(treatments)


def parse_backends(value: str) -> tuple[Backend, ...]:
    backends: list[Backend] = []
    seen: set[str] = set()
    for raw in value.split(","):
        item = raw.strip()
        if not item:
            continue
        if item not in BACKEND_SPECS:
            raise ValueError(f"unknown backend: {item}")
        if item in seen:
            raise ValueError(f"duplicate backend: {item}")
        seen.add(item)
        backends.append(item)
    if not backends:
        raise ValueError("at least one backend is required")
    return tuple(backends)


def resolve_files(
    raw_files: Sequence[str],
    invocation_cwd: Path,
    fact_directory: str | None = None,
) -> tuple[FileSpec, ...]:
    if raw_files:
        chosen = tuple(WorkloadConfig(file, fact_directory) for file in raw_files)
    else:
        if fact_directory is not None:
            raise ValueError("--fact-directory requires at least one explicit benchmark file")
        chosen = DEFAULT_WORKLOADS
    files: list[FileSpec] = []
    for workload in chosen:
        display_path = workload.file
        absolute_path = Path(display_path).expanduser()
        if not absolute_path.is_absolute():
            absolute_path = invocation_cwd / absolute_path
        absolute_path = absolute_path.resolve()
        if not absolute_path.is_file():
            raise FileNotFoundError(f"benchmark file does not exist: {display_path}")

        resolved_fact_directory: Path | None = None
        fact_directory_sha256 = ""
        if workload.fact_directory is not None:
            resolved_fact_directory = Path(workload.fact_directory).expanduser()
            if not resolved_fact_directory.is_absolute():
                resolved_fact_directory = invocation_cwd / resolved_fact_directory
            resolved_fact_directory = resolved_fact_directory.resolve()
            if not resolved_fact_directory.is_dir():
                raise FileNotFoundError(f"benchmark fact directory does not exist: {workload.fact_directory}")
            fact_directory_sha256 = sha256_directory(resolved_fact_directory)
        files.append(
            FileSpec(
                display_path=display_path,
                absolute_path=absolute_path,
                sha256=sha256_file(absolute_path),
                fact_directory=resolved_fact_directory,
                fact_directory_sha256=fact_directory_sha256,
            )
        )
    return tuple(files)


def file_contains_executable_prove_command(path: Path) -> bool:
    for line in path.read_text(encoding="utf-8").splitlines():
        stripped = line.lstrip()
        if stripped.startswith(";"):
            continue
        if re.match(r"\(prove(?:\s|\))", stripped):
            return True
    return False


def validate_spec(spec: BenchmarkSpec) -> None:
    benchmark_cells(spec)
    validate_unique_file_identities(spec.files)
    for file_spec in spec.files:
        if file_contains_executable_prove_command(file_spec.absolute_path):
            raise ValueError(
                f"{file_spec.display_path} contains an explicit prove command; "
                "benchmark files should use check so proof extraction is not included in timed runs"
            )


def parse_single_backend(value: str) -> Backend:
    backends = parse_backends(value)
    if len(backends) != 1:
        raise ValueError("profile mode requires exactly one backend")
    return backends[0]


def parse_single_treatment(value: str) -> Treatment:
    treatments = parse_treatments(value)
    if len(treatments) != 1:
        raise ValueError("profile mode requires exactly one treatment")
    return treatments[0]
