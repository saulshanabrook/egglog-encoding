#!/usr/bin/env -S uv run
from __future__ import annotations

import argparse
import hashlib
import math
import os
import re
import resource
import shutil
import subprocess
import sys
import tempfile
import time
import uuid
from collections.abc import Mapping, Sequence
from contextlib import suppress
from dataclasses import dataclass, replace
from datetime import UTC, datetime
from pathlib import Path
from typing import Any, Literal, TextIO, cast

import numpy as np
import pandas as pd
from pandera.typing import DataFrame
from rich.console import Console
from rich.progress import (
    BarColumn,
    MofNCompleteColumn,
    Progress,
    SpinnerColumn,
    TextColumn,
    TimeElapsedColumn,
)
from rich.table import Table

import samply_analysis
from analysis import (
    estimate_key_for,
    selected_rows,
    status_counts_for_rows,
)
from cli import render_report
from models import (
    BACKEND_SPECS,
    DEFAULT_BACKENDS,
    Backend,
    BenchmarkSpec,
    BuildProfile,
    EstimateKey,
    FileSpec,
    OutputFormat,
    ReportDestination,
    ResolvedTarget,
    Status,
    TargetRequest,
    TargetRow,
    Treatment,
    backend_cargo_features,
    backend_flags,
    benchmark_cells,
    build_report_selection,
)
from report import render_markdown_report
from report_frame import (
    ReportFrame,
    persisted_report_columns,
    report_columns,
    validate_report_frame,
)

DEFAULT_REPORT = ".reports.jsonl"
DEFAULT_PROFILES_DIR = ".profiles"
DEFAULT_ROUNDS = 6
DEFAULT_TIMEOUT_SEC = 120
DEFAULT_SERVE_PORT = 8000
DEFAULT_PROFILE_SECONDS = 10
DEFAULT_PROFILE_TOP = 15
MAX_PROFILE_ITERATIONS = 10_000
PROFILE_CACHE_VERSION = "v1"
PROFILE_SAMPLY_RATE_HZ = 1000
TARGET_STARTUP_WARMUP_SUBPROCESSES = 1
DEFAULT_TREATMENTS: tuple[Treatment, ...] = ("off", "term", "proofs")
DEFAULT_FILES = (
    "egglog/tests/math-microbenchmark.egg",
    "egglog/tests/web-demo/rw-analysis.egg",
    "egglog/tests/integer_math.egg",
    "egglog/tests/web-demo/resolution.egg",
    "egglog-experimental/tests/fixtures/eggcc-2mm-pass1-merge-old.egg",
)


@dataclass(frozen=True)
class TimingRow:
    wall_sec: float | None = None
    user_sec: float | None = None
    system_sec: float | None = None
    cpu_wall_ratio: float | None = None
    max_rss_bytes: int | None = None


@dataclass(frozen=True)
class ErrorRow:
    message: str
    exit_code: int | None = None
    signal: int | None = None


@dataclass(frozen=True)
class TimingResult:
    status: Status
    timing: TimingRow
    error: ErrorRow | None


@dataclass(frozen=True)
class CellPlan:
    target: ResolvedTarget
    file: FileSpec
    backend: Backend
    treatment: Treatment
    required_rows: int
    selected_cached_rows: DataFrame[ReportFrame]
    missing_observations: int
    estimate_key: EstimateKey

    @property
    def planned_processes(self) -> int:
        return self.missing_observations


@dataclass(frozen=True)
class CollectionPlan:
    target: ResolvedTarget
    cells: tuple[CellPlan, ...]

    @property
    def total_missing_observations(self) -> int:
        return sum(cell.missing_observations for cell in self.cells)

    @property
    def total_planned_processes(self) -> int:
        measured = sum(cell.planned_processes for cell in self.cells)
        if measured == 0:
            return 0
        return TARGET_STARTUP_WARMUP_SUBPROCESSES + measured


@dataclass(frozen=True)
class DurationEstimate:
    seconds: float | None
    unknown_processes: int


@dataclass(frozen=True)
class CollectionResult:
    rows: DataFrame[ReportFrame]
    fresh_rows: DataFrame[ReportFrame]


@dataclass(frozen=True)
class ProfileMode:
    iterations: int | None
    profile_seconds: int | None

    @property
    def cache_label(self) -> str:
        if self.iterations is not None:
            return f"i{self.iterations}"
        assert self.profile_seconds is not None
        return f"auto{self.profile_seconds}s"


@dataclass(frozen=True)
class ProfileRequest:
    file: FileSpec
    target_request: TargetRequest
    backend: Backend
    treatment: Treatment
    timeout_sec: int
    profiles_dir: Path
    mode: ProfileMode
    open_after: bool
    force_run: bool
    top: int = DEFAULT_PROFILE_TOP
    show_summary: bool = True
    output_format: OutputFormat = "rich"


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    if argv and argv[0] == "profile":
        return parse_profile_args(argv[1:])
    return parse_benchmark_args(argv)


def parse_benchmark_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Collect or reuse egglog-experimental benchmark reports.",
    )
    parser.add_argument("files", nargs="*", help="egglog files to benchmark")
    parser.add_argument(
        "--target",
        action="append",
        default=None,
        help="target source: ., /path, @git-ref, #pr, label=source, or label=",
    )
    parser.add_argument(
        "--report",
        default=DEFAULT_REPORT,
        help=f"JSONL report/cache path, or - for stdout (default: {DEFAULT_REPORT})",
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
        help=f"rows required per cache cell (default: {DEFAULT_ROUNDS})",
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
        "--serve",
        action="store_true",
        help="serve an interactive eval-live report at http://localhost:<serve-port>",
    )
    parser.add_argument(
        "--serve-port",
        type=positive_int,
        default=DEFAULT_SERVE_PORT,
        help=f"port for the --serve eval-live server (default: {DEFAULT_SERVE_PORT})",
    )
    parser.add_argument(
        "--dump-dir",
        default=None,
        help="dump eval-live tables (JSON + LaTeX) to this directory",
    )
    args = parser.parse_args(argv)
    if args.format == "markdown" and args.report == "-":
        parser.error("--format markdown cannot be combined with --report -")
    args.command = "benchmark"
    return args


def parse_profile_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        prog=f"{Path(sys.argv[0]).name} profile",
        description="Record or reuse a cached Samply CPU profile for one egglog workload.",
    )
    parser.add_argument("file", help="egglog file to profile")
    parser.add_argument(
        "--target",
        action="append",
        default=None,
        help="target source: ., /path, @git-ref, #pr, or label=source; cache-only label= is not supported",
    )
    parser.add_argument(
        "--backend",
        default="main",
        help="single backend to profile (default: main)",
    )
    parser.add_argument(
        "--treatment",
        default="proofs",
        help="single treatment to profile (default: proofs)",
    )
    iteration_group = parser.add_mutually_exclusive_group()
    iteration_group.add_argument(
        "--iterations",
        type=positive_int,
        default=None,
        help="explicit Samply iteration count",
    )
    iteration_group.add_argument(
        "--profile-seconds",
        type=positive_int,
        default=None,
        help=f"target duration for automatic iteration selection (default: {DEFAULT_PROFILE_SECONDS})",
    )
    parser.add_argument(
        "--profiles-dir",
        default=DEFAULT_PROFILES_DIR,
        help=f"profile cache directory (default: {DEFAULT_PROFILES_DIR})",
    )
    parser.add_argument(
        "--top",
        type=positive_int,
        default=DEFAULT_PROFILE_TOP,
        help=f"application functions to show in the macOS CPU summary (default: {DEFAULT_PROFILE_TOP})",
    )
    parser.add_argument(
        "--no-summary",
        action="store_true",
        help="print only the profile artifact path",
    )
    parser.add_argument(
        "--format",
        choices=("rich", "markdown"),
        default="rich",
        help="summary format: rich to stderr, or markdown to stdout (default: rich)",
    )
    parser.add_argument(
        "--open",
        action="store_true",
        help="open the profile with samply load after recording or cache hit",
    )
    parser.add_argument(
        "--force-run",
        action="store_true",
        help="record again and atomically replace the cached profile",
    )
    parser.add_argument(
        "--timeout-sec",
        type=positive_int,
        default=DEFAULT_TIMEOUT_SEC,
        help=f"per-workload timeout in seconds for calibration and profiling watchdog (default: {DEFAULT_TIMEOUT_SEC})",
    )
    args = parser.parse_args(argv)
    args.command = "profile"
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


def resolve_profile_request(args: argparse.Namespace, invocation_cwd: Path) -> ProfileRequest:
    files = resolve_files([str(args.file)], invocation_cwd)
    backend = parse_single_backend(str(args.backend))
    treatment = parse_single_treatment(str(args.treatment))
    target_specs = args.target if args.target is not None else ["."]
    if len(target_specs) != 1:
        raise ValueError("profile mode requires exactly one target")
    if args.iterations is not None:
        mode = ProfileMode(iterations=args.iterations, profile_seconds=None)
    else:
        profile_seconds = args.profile_seconds if args.profile_seconds is not None else DEFAULT_PROFILE_SECONDS
        mode = ProfileMode(iterations=None, profile_seconds=profile_seconds)
    profiles_dir = Path(str(args.profiles_dir)).expanduser()
    if not profiles_dir.is_absolute():
        profiles_dir = invocation_cwd / profiles_dir
    request = ProfileRequest(
        file=files[0],
        target_request=parse_target(str(target_specs[0])),
        backend=backend,
        treatment=treatment,
        timeout_sec=int(args.timeout_sec),
        profiles_dir=profiles_dir,
        mode=mode,
        open_after=bool(args.open),
        force_run=bool(args.force_run),
        top=int(args.top),
        show_summary=not bool(args.no_summary),
        output_format=cast(OutputFormat, str(args.format)),
    )
    validate_spec(
        BenchmarkSpec(
            files=(request.file,),
            treatments=(request.treatment,),
            rounds=1,
            timeout_sec=request.timeout_sec,
            backends=(request.backend,),
        )
    )
    return request


def parse_target(raw: str) -> TargetRequest:
    if "=" in raw:
        label, source = raw.split("=", 1)
        if not label:
            raise ValueError(f"target label cannot be empty: {raw}")
        parse_pr_number(source)
        return TargetRequest(raw=raw, source=source, label=label)
    if parse_pr_number(raw) is not None:
        return TargetRequest(raw=raw, source=raw, label=raw)
    return TargetRequest(raw=raw, source=raw, label=None)


def parse_pr_number(source: str) -> int | None:
    if not source.startswith("#"):
        return None
    match = re.fullmatch(r"#([1-9][0-9]*)", source)
    if match is None:
        raise ValueError(f"invalid PR target {source!r}: use #<positive-number>")
    return int(match.group(1))


def parse_iso_time(value: str) -> datetime:
    normalized = value[:-1] + "+00:00" if value.endswith("Z") else value
    parsed = datetime.fromisoformat(normalized)
    if parsed.tzinfo is None:
        parsed = parsed.replace(tzinfo=UTC)
    return parsed.astimezone(UTC)


def now_iso() -> str:
    return datetime.now(UTC).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return f"sha256:{digest.hexdigest()}"


def run_text(args: Sequence[str], cwd: Path) -> str:
    completed = subprocess.run(
        list(args),
        cwd=cwd,
        check=True,
        text=True,
        capture_output=True,
    )
    return completed.stdout.strip()


def git_root_for_path(path: Path) -> Path:
    return Path(run_text(["git", "rev-parse", "--show-toplevel"], path)).resolve()


def git_sha(cwd: Path, ref: str = "HEAD") -> str:
    return run_text(["git", "rev-parse", ref], cwd)


def git_dirty(cwd: Path) -> bool:
    return bool(run_text(["git", "status", "--porcelain"], cwd))


def resolve_files(raw_files: Sequence[str], invocation_cwd: Path) -> tuple[FileSpec, ...]:
    chosen = tuple(raw_files) if raw_files else DEFAULT_FILES
    files: list[FileSpec] = []
    for display_path in chosen:
        absolute_path = Path(display_path).expanduser()
        if not absolute_path.is_absolute():
            absolute_path = invocation_cwd / absolute_path
        absolute_path = absolute_path.resolve()
        if not absolute_path.is_file():
            raise FileNotFoundError(f"benchmark file does not exist: {display_path}")
        files.append(
            FileSpec(
                display_path=display_path,
                absolute_path=absolute_path,
                sha256=sha256_file(absolute_path),
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
    for file_spec in spec.files:
        if file_contains_executable_prove_command(file_spec.absolute_path):
            raise ValueError(
                f"{file_spec.display_path} contains an explicit prove command; "
                "benchmark files should use check so proof extraction is not included in timed runs"
            )


def resolve_report_destination(raw_report: str, invocation_cwd: Path) -> ReportDestination:
    if raw_report == "-":
        return ReportDestination(path=None, stream=sys.stdout)
    path = Path(raw_report).expanduser()
    if not path.is_absolute():
        path = invocation_cwd / path
    return ReportDestination(path=path)


def empty_report_frame() -> DataFrame[ReportFrame]:
    return validate_report_frame(pd.DataFrame(columns=report_columns()))


def load_report(destination: ReportDestination) -> DataFrame[ReportFrame]:
    if destination.path is None:
        return empty_report_frame()
    path = destination.path
    if not path.exists():
        return empty_report_frame()
    if path.stat().st_size == 0:
        return empty_report_frame()
    try:
        raw = pd.read_json(path, lines=True, convert_dates=False)
    except ValueError as error:
        raise ValueError(f"invalid JSONL report {path}: {error}") from error
    if raw.empty:
        return empty_report_frame()
    raw = raw.drop(columns=["row_index"], errors="ignore").reset_index(names="row_index")
    return normalize_report_frame(raw)


def report_frame_from_records(records: Sequence[Mapping[str, Any]]) -> DataFrame[ReportFrame]:
    return normalize_report_frame(pd.DataFrame.from_records(records))


def normalize_report_frame(frame: pd.DataFrame) -> DataFrame[ReportFrame]:
    columns = report_columns()
    normalized = pd.DataFrame(columns=columns) if frame.empty else frame.copy()
    extra = sorted(set(normalized.columns) - set(columns))
    if extra:
        raise ValueError(f"unexpected report column(s): {', '.join(extra)}")
    if "backend" not in normalized.columns:
        normalized["backend"] = "main"
    for column in columns:
        if column not in normalized.columns:
            normalized[column] = pd.NA
    normalized = normalized.loc[:, columns]
    normalized["backend"] = normalized["backend"].fillna("main")
    normalized["started_at"] = pd.to_datetime(normalized["started_at"], utc=True, errors="raise")
    for column in ["wall_sec", "user_sec", "system_sec", "cpu_wall_ratio"]:
        normalized[column] = pd.to_numeric(normalized[column], errors="raise")
    for column in ["max_rss_bytes", "error_exit_code", "error_signal"]:
        normalized[column] = pd.to_numeric(normalized[column], errors="raise")
    return validate_report_frame(normalized)


def next_row_index(rows: DataFrame[ReportFrame]) -> int:
    if rows.empty:
        return 0
    return int(rows["row_index"].max()) + 1


def concat_report_frames(frames: Sequence[DataFrame[ReportFrame]]) -> DataFrame[ReportFrame]:
    non_empty = [frame for frame in frames if not frame.empty]
    if not non_empty:
        return empty_report_frame()
    return validate_report_frame(pd.concat(non_empty, ignore_index=True))


def persisted_report_frame(rows: DataFrame[ReportFrame]) -> pd.DataFrame:
    frame = rows.loc[:, persisted_report_columns()].copy()
    frame["started_at"] = frame["started_at"].map(isoformat_started_at)
    return frame.astype(object).where(pd.notna(frame), None)


def write_report_rows(handle: TextIO, rows: DataFrame[ReportFrame]) -> None:
    persisted_report_frame(rows).to_json(
        handle,
        orient="records",
        lines=True,
        double_precision=15,
    )


def append_rows(destination: ReportDestination, rows: DataFrame[ReportFrame]) -> None:
    if rows.empty:
        return
    if destination.path is None:
        stream = destination.stream if destination.stream is not None else sys.stdout
        write_report_rows(stream, rows)
        stream.flush()
        return
    destination.path.parent.mkdir(parents=True, exist_ok=True)
    with destination.path.open("a", encoding="utf-8") as handle:
        write_report_rows(handle, rows)


class EstimateModel:
    def __init__(self, samples: dict[EstimateKey, list[float]] | None = None) -> None:
        self.samples = samples or {}

    @classmethod
    def from_rows(cls, rows: DataFrame[ReportFrame]) -> EstimateModel:
        samples: dict[EstimateKey, list[float]] = {}
        successful = rows.loc[rows["status"].eq("success") & rows["wall_sec"].notna()]
        for record in successful.to_dict(orient="records"):
            key = EstimateKey(
                binary_sha256=str(record["binary_sha256"]),
                file_sha256=str(record["file_sha256"]),
                treatment=cast(Treatment, str(record["treatment"])),
                timeout_sec=int(record["timeout_sec"]),
                backend=cast(Backend, str(record["backend"])),
            )
            samples.setdefault(key, []).append(float(record["wall_sec"]))
        return cls(samples)

    def sample_count(self, key: EstimateKey) -> int:
        return len(self.samples.get(key, []))

    def process_mean(self, key: EstimateKey) -> float | None:
        samples = self.samples.get(key, [])
        if not samples:
            return None
        return float(sum(samples) / len(samples))

    def estimate_processes(self, key: EstimateKey, count: int) -> DurationEstimate:
        if count <= 0:
            return DurationEstimate(seconds=0.0, unknown_processes=0)
        mean = self.process_mean(key)
        if mean is None:
            return DurationEstimate(seconds=None, unknown_processes=count)
        return DurationEstimate(seconds=mean * count, unknown_processes=0)

    def record_process(self, key: EstimateKey, result: TimingResult) -> None:
        if result.status == "success" and result.timing.wall_sec is not None:
            self.samples.setdefault(key, []).append(result.timing.wall_sec)


class RunnerOutput:
    def __init__(self) -> None:
        self.console = Console(stderr=True)

    def build_start(self, row: TargetRow) -> None:
        self.console.print(f"[bold]Building[/bold] {display_target(row)}")

    def print_error(self, error: BaseException) -> None:
        self.console.print(f"[red]error:[/red] {error}")


def find_label_pointer(rows: DataFrame[ReportFrame], label: str) -> pd.Series[Any] | None:
    candidates = rows.loc[rows["target_label"].eq(label)]
    if candidates.empty:
        return None
    ordered = candidates.sort_values(["started_at", "row_index"], ascending=[False, False], kind="mergesort")
    return ordered.iloc[0]


def build_collection_plan(
    rows: DataFrame[ReportFrame],
    target: ResolvedTarget,
    spec: BenchmarkSpec,
    force_run: bool,
) -> CollectionPlan:
    cells: list[CellPlan] = []
    for file_spec in spec.files:
        for cell in benchmark_cells(spec):
            estimate_key = estimate_key_for(target, file_spec, cell.backend, cell.treatment, spec.timeout_sec)
            cached = selected_rows(
                rows,
                estimate_key,
                spec.rounds,
            )
            missing = spec.rounds if force_run else max(0, spec.rounds - len(cached))
            cells.append(
                CellPlan(
                    target=target,
                    file=file_spec,
                    backend=cell.backend,
                    treatment=cell.treatment,
                    required_rows=spec.rounds,
                    selected_cached_rows=cached,
                    missing_observations=missing,
                    estimate_key=estimate_key,
                )
            )
    return CollectionPlan(target=target, cells=tuple(cells))


def collection_plan_estimate(plan: CollectionPlan, estimate_model: EstimateModel) -> DurationEstimate:
    seconds = 0.0
    unknown_processes = 0
    for cell in plan.cells:
        estimate = estimate_model.estimate_processes(cell.estimate_key, cell.planned_processes)
        if estimate.seconds is None:
            unknown_processes += estimate.unknown_processes
        else:
            seconds += estimate.seconds
    if seconds == 0.0 and unknown_processes:
        return DurationEstimate(seconds=None, unknown_processes=unknown_processes)
    return DurationEstimate(seconds=seconds, unknown_processes=unknown_processes)


def sanitize_label(value: str) -> str:
    sanitized = re.sub(r"[^A-Za-z0-9_.-]+", "-", value).strip(".-")
    return sanitized or "target"


def find_worktree_for_sha(repo: Path, sha: str) -> Path | None:
    output = run_text(["git", "worktree", "list", "--porcelain"], repo)
    current_path: Path | None = None
    current_head: str | None = None
    for line in [*output.splitlines(), ""]:
        if line.startswith("worktree "):
            current_path = Path(line.removeprefix("worktree ")).resolve()
            current_head = None
        elif line.startswith("HEAD "):
            current_head = line.removeprefix("HEAD ")
        elif not line:
            if current_path is not None and current_head == sha:
                return current_path
            current_path = None
            current_head = None
    return None


def materialize_git_ref(repo: Path, ref: str, label_hint: str | None) -> tuple[Path, str]:
    sha = git_sha(repo, ref)
    existing = find_worktree_for_sha(repo, sha)
    if existing is not None:
        return (existing, sha)

    base_name = sanitize_label(label_hint or ref.replace("/", "-").replace("@", "") or sha[:12])
    worktree_root = repo / ".bench-worktrees"
    path = worktree_root / base_name
    if path.exists():
        if git_sha(path) == sha:
            return (path, sha)
        path = worktree_root / f"{base_name}-{sha[:12]}"
    path.parent.mkdir(parents=True, exist_ok=True)
    subprocess.run(
        ["git", "worktree", "add", "--detach", str(path), sha],
        cwd=repo,
        check=True,
        stdout=sys.stderr,
        stderr=sys.stderr,
    )
    return (path, sha)


def fetch_pr_ref(repo: Path, number: int) -> str:
    ref = f"refs/remotes/origin/pr/{number}"
    subprocess.run(
        ["git", "fetch", "origin", f"+refs/pull/{number}/head:{ref}"],
        cwd=repo,
        check=True,
        stdout=sys.stderr,
        stderr=sys.stderr,
    )
    return ref


def materialize_pr_target(repo: Path, source: str, label_hint: str | None) -> tuple[Path, str]:
    number = parse_pr_number(source)
    if number is None:
        raise ValueError(f"not a PR target: {source}")
    ref = fetch_pr_ref(repo, number)
    return materialize_git_ref(repo, ref, label_hint or source)


def resolve_path_target(source: str, invocation_cwd: Path) -> tuple[Path, str]:
    raw_path = Path(source).expanduser()
    if not raw_path.is_absolute():
        raw_path = invocation_cwd / raw_path
    root = git_root_for_path(raw_path.resolve())
    return (root, "HEAD")


def target_row_for_request(
    request: TargetRequest,
    checkout_path: Path,
    git_ref_value: str,
) -> TargetRow:
    return TargetRow(
        source=request.raw,
        path=str(checkout_path.resolve()),
        git_ref=git_ref_value,
        git_sha=git_sha(checkout_path),
        is_dirty=git_dirty(checkout_path),
        label=request.label,
    )


def build_target(
    row: TargetRow,
    output: RunnerOutput,
    build_profile: BuildProfile = "release",
    cargo_features: Sequence[str] = (),
) -> tuple[Path, str]:
    checkout_path = Path(row.path)
    output.build_start(row)
    if build_profile == "release":
        build_args = ["cargo", "build", "--release", "-p", "egglog-experimental"]
    else:
        build_args = ["cargo", "build", "--profile", "profiling", "-p", "egglog-experimental"]
    if cargo_features:
        build_args.extend(("--features", ",".join(cargo_features)))
    subprocess.run(
        build_args,
        cwd=checkout_path,
        check=True,
        stdout=sys.stderr,
        stderr=sys.stderr,
    )
    binary_name = "egglog-experimental.exe" if os.name == "nt" else "egglog-experimental"
    binary_path = checkout_path / "target" / build_profile / binary_name
    if not binary_path.is_file():
        raise FileNotFoundError(f"{build_profile} binary was not produced: {binary_path}")
    binary_sha256 = sha256_file(binary_path)
    return (binary_path, binary_sha256)


def materialize_target_request(request: TargetRequest, invocation_cwd: Path, repo_root: Path) -> TargetRow:
    if request.is_label_lookup:
        raise ValueError("cache-only target labels cannot be materialized without a cached report row")
    if request.source.startswith("@"):
        ref = request.source[1:]
        if not ref:
            raise ValueError(f"git target is missing a ref: {request.raw}")
        checkout_path, git_ref_value = materialize_git_ref(repo_root, ref, request.label or ref)
    elif parse_pr_number(request.source) is not None:
        checkout_path, git_ref_value = materialize_pr_target(repo_root, request.source, request.label)
    else:
        checkout_path, git_ref_value = resolve_path_target(request.source, invocation_cwd)
    return target_row_for_request(request, checkout_path, git_ref_value)


def build_resolved_target(
    request: TargetRequest,
    row: TargetRow,
    output: RunnerOutput,
    build_profile: BuildProfile,
    cargo_features: Sequence[str],
) -> ResolvedTarget:
    binary_path, binary_sha256 = build_target(row, output, build_profile, cargo_features)
    row = replace(row, is_dirty=git_dirty(Path(row.path)))
    return ResolvedTarget(request=request, row=row, binary_sha256=binary_sha256, binary_path=binary_path)


def resolve_target(
    request: TargetRequest,
    rows: DataFrame[ReportFrame],
    spec: BenchmarkSpec,
    force_run: bool,
    invocation_cwd: Path,
    repo_root: Path,
    output: RunnerOutput,
) -> ResolvedTarget:
    if request.is_label_lookup:
        assert request.label is not None
        pointer = find_label_pointer(rows, request.label)
        if pointer is None:
            raise ValueError(f"no cached rows found for label {request.label!r}")
        if not force_run and label_has_enough_rows(
            rows,
            str(pointer["binary_sha256"]),
            spec,
        ):
            return ResolvedTarget(
                request=request,
                row=target_row_from_report_row(pointer),
                binary_sha256=str(pointer["binary_sha256"]),
                binary_path=None,
            )
        if bool(pointer["target_is_dirty"]):
            raise ValueError(
                f"label {request.label!r} points to a dirty checkout; provide label=SOURCE to collect fresh rows"
            )
        checkout_path, resolved_sha = materialize_git_ref(repo_root, str(pointer["target_git_sha"]), request.label)
        row = target_row_for_request(request, checkout_path, resolved_sha)
        return build_resolved_target(request, row, output, "release", backend_cargo_features(spec.backends))

    row = materialize_target_request(request, invocation_cwd, repo_root)
    return build_resolved_target(request, row, output, "release", backend_cargo_features(spec.backends))


def resolve_profile_target(
    request: TargetRequest,
    backend: Backend,
    invocation_cwd: Path,
    repo_root: Path,
    output: RunnerOutput,
) -> ResolvedTarget:
    if request.is_label_lookup:
        raise ValueError("profile mode does not support cache-only label= targets; use label=SOURCE")
    row = materialize_target_request(request, invocation_cwd, repo_root)
    return build_resolved_target(request, row, output, "profiling", backend_cargo_features((backend,)))


def label_has_enough_rows(
    rows: DataFrame[ReportFrame],
    binary_sha256: str,
    spec: BenchmarkSpec,
) -> bool:
    for file_spec in spec.files:
        for cell in benchmark_cells(spec):
            matches = selected_rows(
                rows,
                EstimateKey(binary_sha256, file_spec.sha256, cell.treatment, spec.timeout_sec, cell.backend),
                spec.rounds,
            )
            if len(matches) < spec.rounds:
                return False
    return True


def target_row_from_report_row(row: pd.Series[Any]) -> TargetRow:
    label_value = row["target_label"]
    label = None if pd.isna(label_value) else str(label_value)
    return TargetRow(
        source=str(row["target_source"]),
        path=str(row["target_path"]),
        git_ref=str(row["target_git_ref"]),
        git_sha=str(row["target_git_sha"]),
        is_dirty=bool(row["target_is_dirty"]),
        label=label,
    )


def display_target(row: TargetRow) -> str:
    if row.label:
        return row.label
    if row.git_ref != "HEAD":
        return row.git_ref
    return f"{Path(row.path).name}@{row.git_sha[:12]}"


def clean_optional(value: Any) -> Any | None:
    if pd.isna(value):
        return None
    if isinstance(value, np.generic):
        return value.item()
    return value


def isoformat_started_at(value: Any) -> str:
    timestamp = pd.Timestamp(value)
    if timestamp.tzinfo is None:
        timestamp = timestamp.tz_localize(UTC)
    timestamp = timestamp.tz_convert(UTC)
    return timestamp.isoformat().replace("+00:00", "Z")


def treatment_flags(treatment: Treatment) -> list[str]:
    if treatment == "off":
        return []
    if treatment == "term":
        return ["--term-encoding"]
    return ["--proofs"]


def workload_command(
    binary_path: Path,
    file_spec: FileSpec,
    backend: Backend,
    treatment: Treatment,
) -> list[str]:
    return [
        str(binary_path),
        "--mode",
        "no-messages",
        "-j",
        "1",
        *backend_flags(backend),
        *treatment_flags(treatment),
        str(file_spec.absolute_path),
    ]


def run_process(
    binary_path: Path,
    checkout_path: Path,
    file_spec: FileSpec,
    backend: Backend,
    treatment: Treatment,
    timeout_sec: int,
) -> TimingResult:
    return run_command(workload_command(binary_path, file_spec, backend, treatment), checkout_path, timeout_sec)


def run_startup_warmup(binary_path: Path, checkout_path: Path, timeout_sec: int) -> TimingResult:
    return run_command([str(binary_path), "--help"], checkout_path, timeout_sec)


def profile_hash_component(value: str) -> str:
    return value.removeprefix("sha256:")


def profile_cache_path(
    profiles_dir: Path,
    binary_sha256: str,
    file_sha256: str,
    backend: Backend,
    treatment: Treatment,
    mode: ProfileMode,
) -> Path:
    return (
        profiles_dir
        / PROFILE_CACHE_VERSION
        / profile_hash_component(binary_sha256)
        / profile_hash_component(file_sha256)
        / f"{backend}-{treatment}-{mode.cache_label}.json.gz"
    )


def profile_cache_hit(path: Path) -> bool:
    return path.is_file() and path.stat().st_size > 0


def profile_display_path(path: Path, invocation_cwd: Path) -> Path:
    resolved = path.resolve()
    try:
        return resolved.relative_to(invocation_cwd.resolve())
    except ValueError:
        return resolved


def calculate_profile_iterations(
    elapsed_seconds: float,
    profile_seconds: int,
    max_iterations: int = MAX_PROFILE_ITERATIONS,
) -> tuple[int, bool]:
    if elapsed_seconds <= 0:
        return (max_iterations, True)
    uncapped = max(1, math.ceil(profile_seconds * 1.10 / elapsed_seconds))
    if uncapped > max_iterations:
        return (max_iterations, True)
    return (uncapped, False)


def profile_name(
    file_spec: FileSpec,
    backend: Backend,
    treatment: Treatment,
    mode: ProfileMode,
    iterations: int,
    binary_sha256: str,
) -> str:
    stem = Path(file_spec.display_path).stem
    file_hash = profile_hash_component(file_spec.sha256)[:8]
    binary_hash = profile_hash_component(binary_sha256)[:8]
    mode_label = mode.cache_label if mode.iterations is not None else f"auto>={mode.profile_seconds}s"
    return f"{stem} {backend}/{treatment} {mode_label} x{iterations} [bin:{binary_hash} file:{file_hash}]"


def profile_temp_path(artifact: Path) -> Path:
    base_name = artifact.name.removesuffix(".json.gz")
    return artifact.with_name(f".{base_name}.tmp-{uuid.uuid4().hex}.json.gz")


def samply_executable() -> str:
    executable = shutil.which("samply")
    if executable is None:
        raise FileNotFoundError("Install Samply with: cargo install --locked samply")
    return executable


def samply_record_command(
    samply: str,
    artifact: Path,
    name: str,
    iterations: int,
    workload: Sequence[str],
) -> list[str]:
    return [
        samply,
        "record",
        "--save-only",
        "--rate",
        str(PROFILE_SAMPLY_RATE_HZ),
        "--reuse-threads",
        "--iteration-count",
        str(iterations),
        "--profile-name",
        name,
        "--output",
        str(artifact),
        "--",
        *workload,
    ]


def profile_record_timeout(timeout_sec: int, iterations: int) -> int:
    return max(timeout_sec + 60, timeout_sec * iterations + 60)


def run_samply_record(
    *,
    artifact: Path,
    name: str,
    iterations: int,
    workload: Sequence[str],
    checkout_path: Path,
    timeout_sec: int,
) -> dict[str, Any]:
    temp_artifact = profile_temp_path(artifact)
    temp_artifact.parent.mkdir(parents=True, exist_ok=True)
    with suppress(FileNotFoundError):
        temp_artifact.unlink()
    command = samply_record_command(samply_executable(), temp_artifact, name, iterations, workload)
    env = os.environ.copy()
    env["RUST_LOG"] = "error"
    try:
        subprocess.run(
            command,
            cwd=checkout_path,
            env=env,
            check=True,
            timeout=profile_record_timeout(timeout_sec, iterations),
            stdout=sys.stderr,
            stderr=sys.stderr,
        )
        if not profile_cache_hit(temp_artifact):
            raise ValueError(f"Samply did not produce a nonempty profile artifact: {temp_artifact}")
        profile = samply_analysis.read_artifact(temp_artifact)
        artifact.parent.mkdir(parents=True, exist_ok=True)
        os.replace(temp_artifact, artifact)
        return profile
    except BaseException:
        with suppress(FileNotFoundError):
            temp_artifact.unlink()
        raise


def open_samply_profile(artifact: Path, checkout_path: Path) -> None:
    try:
        subprocess.run(
            [samply_executable(), "load", str(artifact)],
            cwd=checkout_path,
            check=True,
            stdout=sys.stderr,
            stderr=sys.stderr,
        )
    except KeyboardInterrupt:
        return


def run_command(command: Sequence[str], checkout_path: Path, timeout_sec: int) -> TimingResult:
    env = os.environ.copy()
    env["RUST_LOG"] = "error"
    start = time.perf_counter()
    with (
        tempfile.TemporaryFile(mode="w+t", encoding="utf-8", errors="replace") as stdout_file,
        tempfile.TemporaryFile(mode="w+t", encoding="utf-8", errors="replace") as stderr_file,
    ):
        process = subprocess.Popen(
            command,
            cwd=checkout_path,
            env=env,
            text=True,
            stdout=stdout_file,
            stderr=stderr_file,
        )
        try:
            return_code, usage = wait4_process(process, timeout_sec)
        except subprocess.TimeoutExpired:
            return TimingResult(
                status="timed-out",
                timing=TimingRow(),
                error=ErrorRow(message=f"timed out after {timeout_sec} seconds"),
            )
        wall_sec = time.perf_counter() - start
        timing = timing_from_usage(usage, wall_sec)
        stdout = read_tempfile(stdout_file)
        stderr = read_tempfile(stderr_file)
    if return_code == 0:
        return TimingResult(status="success", timing=timing, error=None)
    message = stderr.strip() or stdout.strip() or "process exited with non-zero status"
    exit_code = return_code if return_code >= 0 else None
    signal = -return_code if return_code < 0 else None
    return TimingResult(
        status="failure",
        timing=timing,
        error=ErrorRow(exit_code=exit_code, signal=signal, message=message[-1000:]),
    )


def wait4_process(process: subprocess.Popen[str], timeout_sec: int) -> tuple[int, resource.struct_rusage]:
    deadline = time.monotonic() + timeout_sec
    while True:
        waited_pid, status, usage = os.wait4(process.pid, os.WNOHANG)
        if waited_pid == process.pid:
            return os.waitstatus_to_exitcode(status), usage
        if time.monotonic() >= deadline:
            with suppress(ProcessLookupError):
                process.kill()
            with suppress(ChildProcessError):
                os.wait4(process.pid, 0)
            raise subprocess.TimeoutExpired(process.args, timeout_sec)
        time.sleep(min(0.05, max(0.0, deadline - time.monotonic())))


def read_tempfile(handle: TextIO) -> str:
    handle.seek(0)
    return handle.read()


def timing_from_usage(
    usage: resource.struct_rusage,
    wall_sec: float,
) -> TimingRow:
    user_sec = max(0.0, usage.ru_utime)
    system_sec = max(0.0, usage.ru_stime)
    cpu_wall_ratio = (user_sec + system_sec) / wall_sec if wall_sec > 0 else None
    return TimingRow(
        wall_sec=wall_sec,
        user_sec=user_sec,
        system_sec=system_sec,
        cpu_wall_ratio=cpu_wall_ratio,
        max_rss_bytes=ru_maxrss_to_bytes(usage.ru_maxrss),
    )


def ru_maxrss_to_bytes(ru_maxrss: int, platform: str = sys.platform) -> int | None:
    if ru_maxrss <= 0:
        return None
    if platform == "darwin":
        return ru_maxrss
    return ru_maxrss * 1024


def collection_label(
    file_spec: FileSpec,
    backend: Backend,
    treatment: Treatment,
    round_index: int,
    rounds: int,
) -> str:
    filename = Path(file_spec.display_path).name
    return f"{filename} {backend}/{treatment} {round_index + 1}/{rounds}"


def format_timing_result(result: TimingResult) -> str:
    if result.timing.wall_sec is None:
        return result.status
    return f"{result.status} {result.timing.wall_sec:.3f}s"


def format_duration(seconds: float | None) -> str:
    if seconds is None:
        return "unknown"
    if seconds < 60:
        return f"{seconds:.3f}s"
    minutes, remainder = divmod(seconds, 60)
    if minutes < 60:
        return f"{int(minutes)}m{remainder:04.1f}s"
    hours, minutes = divmod(minutes, 60)
    return f"{int(hours)}h{int(minutes):02d}m{remainder:04.1f}s"


def format_duration_estimate(estimate: DurationEstimate) -> str:
    if estimate.seconds is None:
        return f"unknown ({estimate.unknown_processes} runs)"
    if estimate.unknown_processes:
        return f"{format_duration(estimate.seconds)} + {estimate.unknown_processes} unknown"
    return format_duration(estimate.seconds)


def remaining_estimate(
    remaining_processes: dict[EstimateKey, int],
    estimate_model: EstimateModel,
) -> DurationEstimate:
    seconds = 0.0
    unknown_processes = 0
    for key, count in remaining_processes.items():
        estimate = estimate_model.estimate_processes(key, count)
        if estimate.seconds is None:
            unknown_processes += estimate.unknown_processes
        else:
            seconds += estimate.seconds
    if seconds == 0.0 and unknown_processes:
        return DurationEstimate(seconds=None, unknown_processes=unknown_processes)
    return DurationEstimate(seconds=seconds, unknown_processes=unknown_processes)


def emit_collection_plan(
    output: RunnerOutput,
    plan: CollectionPlan,
    estimate_model: EstimateModel,
) -> None:
    total_estimate = collection_plan_estimate(plan, estimate_model)
    multi_backend = len({cell.backend for cell in plan.cells}) > 1
    table = Table(title=f"{plan.target.display_label}: cache and estimate plan")
    table.add_column("File")
    if multi_backend:
        table.add_column("Backend")
    table.add_column("Treatment")
    table.add_column("Cached")
    table.add_column("Missing")
    table.add_column("Statuses")
    table.add_column("Per run")
    table.add_column("Fresh ETA")
    for cell in plan.cells:
        estimate = estimate_model.estimate_processes(cell.estimate_key, cell.planned_processes)
        process_mean = estimate_model.process_mean(cell.estimate_key)
        status_counts = status_counts_for_rows(cell.selected_cached_rows)
        statuses = ", ".join(f"{status}:{count}" for status, count in sorted(status_counts.items())) or "-"
        backend_cells = (cell.backend,) if multi_backend else ()
        table.add_row(
            cell.file.display_path,
            *backend_cells,
            cell.treatment,
            f"{len(cell.selected_cached_rows)}/{cell.required_rows}",
            str(cell.missing_observations),
            statuses,
            format_duration(process_mean),
            format_duration_estimate(estimate),
        )
    output.console.print(table)
    output.console.print(f"Estimated fresh collection time: [bold]{format_duration_estimate(total_estimate)}[/bold]")


def flat_report_record(
    *,
    row_index: int,
    started_at: str,
    target: ResolvedTarget,
    cell: CellPlan,
    spec: BenchmarkSpec,
    result: TimingResult,
) -> dict[str, Any]:
    return {
        "row_index": row_index,
        "started_at": started_at,
        "status": result.status,
        "target_label": target.row.label,
        "target_source": target.row.source,
        "target_path": target.row.path,
        "target_git_ref": target.row.git_ref,
        "target_git_sha": target.row.git_sha,
        "target_is_dirty": target.row.is_dirty,
        "binary_sha256": target.binary_sha256,
        "file_path": cell.file.display_path,
        "file_sha256": cell.file.sha256,
        "backend": cell.backend,
        "treatment": cell.treatment,
        "timeout_sec": spec.timeout_sec,
        "wall_sec": result.timing.wall_sec,
        "user_sec": result.timing.user_sec,
        "system_sec": result.timing.system_sec,
        "cpu_wall_ratio": result.timing.cpu_wall_ratio,
        "max_rss_bytes": result.timing.max_rss_bytes,
        "error_exit_code": result.error.exit_code if result.error is not None else None,
        "error_signal": result.error.signal if result.error is not None else None,
        "error_message": result.error.message if result.error is not None else None,
    }


def collect_rows(
    rows: DataFrame[ReportFrame],
    report_destination: ReportDestination,
    plan: CollectionPlan,
    spec: BenchmarkSpec,
    output: RunnerOutput,
    estimate_model: EstimateModel,
) -> CollectionResult:
    target = plan.target
    if plan.total_missing_observations == 0:
        return CollectionResult(rows=rows, fresh_rows=empty_report_frame())
    if target.binary_path is None:
        raise ValueError(f"target {target.display_label} needs fresh rows but has no build path")
    binary_path = target.binary_path
    total_observations = plan.total_missing_observations
    planned_processes = plan.total_planned_processes
    remaining_processes: dict[EstimateKey, int] = {}
    for cell in plan.cells:
        if cell.planned_processes > 0:
            remaining_processes[cell.estimate_key] = (
                remaining_processes.get(cell.estimate_key, 0) + cell.planned_processes
            )
    output.console.print(
        f"[bold]Collecting[/bold] {display_target(target.row)} "
        f"({total_observations} observations, {planned_processes} subprocesses)"
    )
    fresh_frames: list[DataFrame[ReportFrame]] = []
    next_index = next_row_index(rows)
    max_deficit = max(cell.missing_observations for cell in plan.cells)
    completed_observations = 0

    def decrement_remaining(key: EstimateKey, count: int = 1) -> None:
        current = remaining_processes.get(key, 0)
        next_count = max(0, current - count)
        if next_count:
            remaining_processes[key] = next_count
        else:
            remaining_processes.pop(key, None)

    def run_loop(progress: Progress | None = None, process_task: Any | None = None) -> None:
        nonlocal next_index, completed_observations
        for round_index in range(max_deficit):
            for cell in plan.cells:
                if round_index >= cell.missing_observations:
                    continue
                cell_file = cell.file
                cell_backend = cell.backend
                cell_treatment = cell.treatment
                cell_key = cell.estimate_key
                required_rounds = cell.missing_observations
                observation_number = completed_observations + 1
                label = collection_label(cell_file, cell_backend, cell_treatment, round_index, required_rounds)

                def update_progress(current: str, advance: int = 0) -> None:
                    if progress is None or process_task is None:
                        return
                    progress.update(
                        process_task,
                        advance=advance,
                        eta=format_duration_estimate(remaining_estimate(remaining_processes, estimate_model)),
                        current=current,
                    )

                update_progress(f"row {observation_number}/{total_observations} timed")
                started_at = now_iso()
                result = run_process(
                    binary_path,
                    Path(target.row.path),
                    cell_file,
                    cell_backend,
                    cell_treatment,
                    spec.timeout_sec,
                )
                estimate_model.record_process(cell_key, result)
                decrement_remaining(cell_key)
                update_progress(
                    f"row {observation_number}/{total_observations} timed; last {format_timing_result(result)}",
                    advance=1,
                )
                record = flat_report_record(
                    row_index=next_index,
                    started_at=started_at,
                    target=target,
                    cell=cell,
                    spec=spec,
                    result=result,
                )
                fresh_frame = report_frame_from_records([record])
                append_rows(report_destination, fresh_frame)
                fresh_frames.append(fresh_frame)
                next_index += 1
                completed_observations += 1
                assert progress is not None
                progress.console.print(f"  {label}: fresh {format_timing_result(result)}")
                update_progress(
                    f"rows {completed_observations}/{total_observations}; last {format_timing_result(result)}"
                )

    with Progress(
        SpinnerColumn(),
        TextColumn("[progress.description]{task.description}"),
        BarColumn(bar_width=10),
        MofNCompleteColumn(),
        TimeElapsedColumn(),
        TextColumn("eta"),
        TextColumn("{task.fields[eta]}"),
        TextColumn("{task.fields[current]}"),
        console=output.console,
        transient=True,
    ) as progress:
        process_task = progress.add_task(
            "runs",
            total=planned_processes,
            eta=format_duration_estimate(remaining_estimate(remaining_processes, estimate_model)),
            current=f"rows 0/{total_observations}",
        )
        progress.update(
            process_task,
            current="startup warmup",
            eta=format_duration_estimate(remaining_estimate(remaining_processes, estimate_model)),
        )
        startup_warmup = run_startup_warmup(binary_path, Path(target.row.path), spec.timeout_sec)
        progress.update(
            process_task,
            advance=TARGET_STARTUP_WARMUP_SUBPROCESSES,
            current=f"startup warmup; last {format_timing_result(startup_warmup)}",
            eta=format_duration_estimate(remaining_estimate(remaining_processes, estimate_model)),
        )
        progress.console.print(f"  startup warmup: {format_timing_result(startup_warmup)}")
        if startup_warmup.status != "success":
            message = "startup warmup did not complete successfully"
            if startup_warmup.error is not None:
                message = f"{message}: {startup_warmup.error.message}"
            raise ValueError(message)
        run_loop(progress, process_task)
    fresh_rows = concat_report_frames(fresh_frames)
    return CollectionResult(rows=concat_report_frames([rows, fresh_rows]), fresh_rows=fresh_rows)


def run_profile(args: argparse.Namespace, output: RunnerOutput, invocation_cwd: Path, repo_root: Path) -> None:
    request = resolve_profile_request(args, invocation_cwd)
    target = resolve_profile_target(request.target_request, request.backend, invocation_cwd, repo_root, output)
    if target.binary_path is None:
        raise ValueError(f"target {target.display_label} needs a profiling binary")
    checkout_path = Path(target.row.path)
    workload = workload_command(target.binary_path, request.file, request.backend, request.treatment)
    artifact = profile_cache_path(
        request.profiles_dir,
        target.binary_sha256,
        request.file.sha256,
        request.backend,
        request.treatment,
        request.mode,
    )
    profile: dict[str, Any] | None = None
    cache_status: Literal["hit", "recorded"] = "recorded"
    if profile_cache_hit(artifact) and not request.force_run:
        try:
            profile = samply_analysis.read_artifact(artifact)
        except ValueError as error:
            output.console.print(f"[yellow]warning:[/yellow] ignoring invalid profile cache entry: {error}")
        else:
            cache_status = "hit"
            output.console.print(f"[bold]Profile cache hit[/bold] {artifact}")

    if profile is None:
        iterations = request.mode.iterations
        if iterations is None:
            assert request.mode.profile_seconds is not None
            output.console.print(
                f"[bold]Calibrating[/bold] {request.file.display_path} "
                f"{request.backend}/{request.treatment} for {request.mode.profile_seconds}s"
            )
            calibration = run_command(workload, checkout_path, request.timeout_sec)
            if calibration.status != "success" or calibration.timing.wall_sec is None:
                detail = calibration.error.message if calibration.error is not None else calibration.status
                raise ValueError(f"profile calibration failed: {detail}")
            iterations, capped = calculate_profile_iterations(
                calibration.timing.wall_sec,
                request.mode.profile_seconds,
            )
            output.console.print(
                f"  calibration: {calibration.timing.wall_sec:.3f}s; recording {iterations} Samply iteration(s)"
            )
            if capped:
                output.console.print(
                    "[yellow]warning:[/yellow] maximum profile iterations reached; "
                    "the profile may be shorter than the requested duration"
                )

        assert iterations is not None
        name = profile_name(
            request.file,
            request.backend,
            request.treatment,
            request.mode,
            iterations,
            target.binary_sha256,
        )
        output.console.print(f"[bold]Recording profile[/bold] {artifact}")
        profile = run_samply_record(
            artifact=artifact,
            name=name,
            iterations=iterations,
            workload=workload,
            checkout_path=checkout_path,
            timeout_sec=request.timeout_sec,
        )
        output.console.print(f"[bold]Profile written[/bold] {artifact}")

    if request.show_summary:
        display_artifact = profile_display_path(artifact, invocation_cwd)
        summary: samply_analysis.ProfileCpuSummary | None = None
        if sys.platform == "darwin":
            try:
                summary = samply_analysis.summarize(profile, target.binary_path)
            except ValueError as error:
                output.console.print(f"[yellow]warning:[/yellow] CPU profile summary unavailable: {error}")
            if summary is not None:
                for warning in summary.warnings:
                    output.console.print(f"[yellow]warning:[/yellow] {warning}")
        else:
            output.console.print(
                "[yellow]warning:[/yellow] CPU profile summaries are currently available on macOS only; "
                "the Samply artifact was created normally."
            )
        report = samply_analysis.ProfileReport(
            artifact=display_artifact,
            cache_status=cache_status,
            workload=request.file.display_path,
            backend=request.backend,
            treatment=request.treatment,
            top=request.top,
            cpu_summary=summary,
        )
        if request.output_format == "markdown":
            rendered = samply_analysis.render_markdown(report)
            sys.stdout.write(rendered + "\n")
            sys.stdout.flush()
        else:
            samply_analysis.render_rich(output.console, report)
    else:
        sys.stdout.write(str(artifact.resolve()) + "\n")
        sys.stdout.flush()
    if request.open_after:
        open_samply_profile(artifact, checkout_path)


def main(argv: Sequence[str] | None = None) -> int:
    raw_argv = tuple(sys.argv[1:] if argv is None else argv)
    args = parse_args(raw_argv)
    output = RunnerOutput()
    try:
        script_root = Path(__file__).resolve().parent
        invocation_cwd = Path.cwd()
        repo_root = git_root_for_path(script_root)
        if args.command == "profile":
            run_profile(args, output, invocation_cwd, repo_root)
            return 0
        backends = parse_backends(args.backend)
        treatments = parse_treatments(args.treatments)
        report_destination = resolve_report_destination(args.report, invocation_cwd)
        files = resolve_files(args.files, invocation_cwd)
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
        rows = load_report(report_destination)
        estimate_model = EstimateModel.from_rows(rows)
        targets = [
            resolve_target(
                request,
                rows,
                spec,
                args.force_run,
                invocation_cwd,
                repo_root,
                output,
            )
            for request in target_requests
        ]
        for target in targets:
            plan = build_collection_plan(
                rows,
                target,
                spec,
                args.force_run,
            )
            emit_collection_plan(output, plan, estimate_model)
            collection = collect_rows(rows, report_destination, plan, spec, output, estimate_model)
            rows = collection.rows
        if args.format == "markdown":
            sys.stdout.write(render_markdown_report(report_destination, rows, targets, spec, raw_argv) + "\n")
        else:
            render_report(
                output.console,
                report_destination,
                rows,
                targets,
                spec,
            )
        if args.dump_dir is not None or args.serve:
            import web

            selection = build_report_selection(targets, spec)
            if args.dump_dir is not None:
                web.dump_report(output.console, rows, selection, Path(args.dump_dir))
            if args.serve:
                web.serve_report(output.console, rows, selection, args.serve_port)
    except (FileNotFoundError, ValueError, subprocess.CalledProcessError, subprocess.TimeoutExpired) as error:
        output.print_error(error)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
