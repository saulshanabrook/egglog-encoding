#!/usr/bin/env -S uv run
from __future__ import annotations

import argparse
import hashlib
import math
import os
import re
import resource
import shlex
import shutil
import subprocess
import sys
import tempfile
import time
import uuid
from collections.abc import Callable, Mapping, Sequence
from contextlib import suppress
from dataclasses import dataclass, replace
from datetime import UTC, datetime
from pathlib import Path
from typing import Any, Literal, TextIO, cast

import numpy as np
import pandas as pd
import pandera.pandas as pa
from pandera.typing import DataFrame, Series
from rich import box
from rich.console import Console
from rich.markup import escape
from rich.progress import (
    BarColumn,
    MofNCompleteColumn,
    Progress,
    SpinnerColumn,
    TaskID,
    TextColumn,
    TimeElapsedColumn,
)
from rich.table import Table
from rich.text import Text
from rich.tree import Tree
from scipy import stats

import samply_analysis

Status = Literal["success", "timed-out", "failure"]
Backend = str
Treatment = Literal["off", "term", "proofs"]
BuildProfile = Literal["release", "profiling"]
OutputFormat = Literal["rich", "markdown"]
TableAlignment = Literal["left", "right"]


@dataclass(frozen=True)
class BackendSpec:
    display_name: str
    treatments: tuple[Treatment, ...]
    flags: tuple[str, ...]
    cargo_features: tuple[str, ...] = ()


BACKEND_SPECS: dict[Backend, BackendSpec] = {
    "main": BackendSpec("main", ("off", "term", "proofs"), ()),
    "dd": BackendSpec("DD", ("term", "proofs"), ("--backend", "dd"), ("dd-backend",)),
}

DEFAULT_REPORT = ".reports.jsonl"
DEFAULT_PROFILES_DIR = ".profiles"
DEFAULT_ROUNDS = 6
DEFAULT_TIMEOUT_SEC = 120
DEFAULT_PROFILE_SECONDS = 10
DEFAULT_PROFILE_TOP = 15
MAX_PROFILE_ITERATIONS = 10_000
PROFILE_CACHE_VERSION = "v1"
PROFILE_SAMPLY_RATE_HZ = 1000
TARGET_STARTUP_WARMUP_SUBPROCESSES = 1
DEFAULT_BACKENDS: tuple[Backend, ...] = ("main",)
DEFAULT_TREATMENTS: tuple[Treatment, ...] = ("off", "term", "proofs")
DEFAULT_FILES = (
    "egglog/tests/math-microbenchmark-mini.egg",
    "egglog/tests/web-demo/rw-analysis.egg",
    "egglog/tests/integer_math.egg",
    "egglog/tests/web-demo/resolution.egg",
    "egglog-experimental/tests/fixtures/eggcc-2mm-pass1-merge-old.egg",
)
TARGET_WALL_TIME_CAPTION = (
    "Ratio is target / baseline. Values below 1x are faster; above 1x are slower. "
    "Wall-time change is derived from the ratio; negative is faster. Intervals are 95% CIs."
)
TARGET_PEAK_RSS_CAPTION = (
    "Ratio is target / baseline. Values below 1x use less peak RSS; above 1x use more. "
    "RSS change is derived from the ratio; negative uses less memory. Intervals are 95% CIs."
)
BACKEND_WALL_TIME_CAPTION = (
    "Ratio is candidate backend / baseline backend for the same target and treatment. "
    "Values below 1x are faster; above 1x are slower. Intervals are 95% CIs."
)
BACKEND_PEAK_RSS_CAPTION = (
    "Ratio is candidate backend / baseline backend for the same target and treatment. "
    "Values below 1x use less peak RSS; above 1x use more. Intervals are 95% CIs."
)
PROOF_OVERHEAD_CAPTION = "Within-backend proof overhead. This is not backend-vs-main performance."
RESULT_STYLES = {
    "descriptive": "dim",
    "established": "green",
    "faster": "green",
    "invalid": "bold red",
    "less": "green",
    "more": "red",
    "not established": "red",
    "point only": "dim",
    "slower": "red",
    "unclear": "yellow",
}


@dataclass(frozen=True)
class TargetRow:
    source: str
    path: str
    git_ref: str
    git_sha: str
    is_dirty: bool
    label: str | None = None


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


class ReportFrame(pa.DataFrameModel):
    class Config:
        strict = True
        coerce = True

    row_index: Series[int] = pa.Field(ge=0)
    started_at: Series[pd.Timestamp]
    status: Series[str] = pa.Field(isin=["success", "timed-out", "failure"])
    target_label: Series[str] = pa.Field(nullable=True)
    target_source: Series[str]
    target_path: Series[str]
    target_git_ref: Series[str]
    target_git_sha: Series[str]
    target_is_dirty: Series[bool]
    binary_sha256: Series[str]
    file_path: Series[str]
    file_sha256: Series[str]
    backend: Series[str] = pa.Field(isin=list(BACKEND_SPECS))
    treatment: Series[str] = pa.Field(isin=["off", "term", "proofs"])
    timeout_sec: Series[int] = pa.Field(gt=0)
    wall_sec: Series[float] = pa.Field(nullable=True, ge=0)
    user_sec: Series[float] = pa.Field(nullable=True, ge=0)
    system_sec: Series[float] = pa.Field(nullable=True, ge=0)
    cpu_wall_ratio: Series[float] = pa.Field(nullable=True, ge=0)
    max_rss_bytes: Series[int] = pa.Field(nullable=True, ge=0, coerce=True)
    error_exit_code: Series[int] = pa.Field(nullable=True, coerce=True)
    error_signal: Series[int] = pa.Field(nullable=True, coerce=True)
    error_message: Series[str] = pa.Field(nullable=True)

    @pa.dataframe_check
    def success_rows_have_wall_time(cls, frame: pd.DataFrame) -> pd.Series[Any]:  # type: ignore[misc]
        return frame["status"].ne("success") | frame["wall_sec"].notna()

    @pa.dataframe_check
    def timeout_rows_have_no_timing(cls, frame: pd.DataFrame) -> pd.Series[Any]:  # type: ignore[misc]
        timing_columns = ["wall_sec", "user_sec", "system_sec", "cpu_wall_ratio", "max_rss_bytes"]
        return frame["status"].ne("timed-out") | frame[timing_columns].isna().all(axis=1)


def report_columns() -> list[str]:
    return list(ReportFrame.to_schema().columns)


def persisted_report_columns() -> list[str]:
    return [column for column in report_columns() if column != "row_index"]


@dataclass(frozen=True)
class FileSpec:
    display_path: str
    absolute_path: Path
    sha256: str


@dataclass(frozen=True)
class BenchmarkSpec:
    files: tuple[FileSpec, ...]
    treatments: tuple[Treatment, ...]
    rounds: int
    timeout_sec: int
    backends: tuple[Backend, ...] = DEFAULT_BACKENDS


@dataclass(frozen=True)
class BenchmarkCell:
    backend: Backend
    treatment: Treatment


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


@dataclass(frozen=True)
class ReportDestination:
    path: Path | None
    stream: TextIO | None = None

    @property
    def display_path(self) -> str:
        return "-" if self.path is None else str(self.path)


@dataclass(frozen=True)
class TargetRequest:
    raw: str
    source: str
    label: str | None

    @property
    def is_label_lookup(self) -> bool:
        return self.label is not None and self.source == ""


@dataclass(frozen=True)
class ResolvedTarget:
    request: TargetRequest
    row: TargetRow
    binary_sha256: str
    binary_path: Path | None

    @property
    def display_label(self) -> str:
        if self.row.label:
            return self.row.label
        if self.row.git_ref != "HEAD":
            return self.row.git_ref
        if self.row.git_sha:
            return self.row.git_sha[:12]
        return Path(self.row.path).name


@dataclass(frozen=True)
class TimingResult:
    status: Status
    timing: TimingRow
    error: ErrorRow | None


@dataclass(frozen=True)
class EstimateKey:
    binary_sha256: str
    file_sha256: str
    treatment: Treatment
    timeout_sec: int
    backend: Backend = "main"


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
class CellSummary:
    rows: DataFrame[ReportFrame]
    samples: tuple[float, ...]
    status_counts: dict[str, int]
    mean: float | None
    ci_low: float | None
    ci_high: float | None
    issue: str | None

    @property
    def ok(self) -> bool:
        return self.issue is None and self.mean is not None


CellMap = dict[tuple[str, Backend, Treatment], CellSummary]
TargetCellMaps = dict[ResolvedTarget, CellMap]


@dataclass(frozen=True)
class CollectionResult:
    rows: DataFrame[ReportFrame]
    fresh_rows: DataFrame[ReportFrame]


@dataclass(frozen=True)
class RatioSummary:
    point: float | None
    ci_low: float | None
    ci_high: float | None
    issue: str | None

    @property
    def ok(self) -> bool:
        return self.issue is None and self.point is not None


@dataclass(frozen=True)
class ReportTableData:
    title: str
    headers: tuple[str, ...]
    rows: tuple[tuple[str, ...], ...]
    caption: str | None = None
    alignments: tuple[TableAlignment, ...] | None = None


@dataclass(frozen=True)
class MetricSpec:
    title: str
    caption: str
    file_count_heading: str
    format_total: Callable[[float | None], str]
    format_change: Callable[[RatioSummary], str]
    format_result: Callable[[RatioSummary], str]
    omit_without_samples: bool = False


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


def backend_spec(backend: Backend) -> BackendSpec:
    try:
        return BACKEND_SPECS[backend]
    except KeyError as error:
        raise ValueError(f"unknown backend: {backend}") from error


def backend_supports_treatment(backend: Backend, treatment: Treatment) -> bool:
    return treatment in backend_spec(backend).treatments


def supported_treatments(backend: Backend) -> tuple[Treatment, ...]:
    return backend_spec(backend).treatments


def backend_cargo_features(backends: Sequence[Backend]) -> tuple[str, ...]:
    return tuple(dict.fromkeys(feature for backend in backends for feature in backend_spec(backend).cargo_features))


def backend_treatment_cells(
    backends: Sequence[Backend],
    treatments: Sequence[Treatment],
) -> tuple[BenchmarkCell, ...]:
    cells: list[BenchmarkCell] = []
    requested = ",".join(treatments)
    for backend in backends:
        backend_cells = tuple(
            BenchmarkCell(backend, treatment)
            for treatment in treatments
            if backend_supports_treatment(backend, treatment)
        )
        if not backend_cells:
            supported = ",".join(supported_treatments(backend))
            raise ValueError(
                f"backend {backend} has no supported treatments in requested set {requested}; "
                f"supported treatments: {supported}"
            )
        cells.extend(backend_cells)
    return tuple(cells)


def benchmark_cells(spec: BenchmarkSpec) -> tuple[BenchmarkCell, ...]:
    return backend_treatment_cells(spec.backends, spec.treatments)


def backend_has_treatment(spec: BenchmarkSpec, backend: Backend, treatment: Treatment) -> bool:
    return any(cell.backend == backend and cell.treatment == treatment for cell in benchmark_cells(spec))


def shared_backend_treatments(
    spec: BenchmarkSpec,
    baseline_backend: Backend,
    candidate_backend: Backend,
) -> tuple[Treatment, ...]:
    return tuple(
        treatment
        for treatment in spec.treatments
        if backend_supports_treatment(baseline_backend, treatment)
        and backend_supports_treatment(candidate_backend, treatment)
    )


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


def validate_report_frame(frame: pd.DataFrame) -> DataFrame[ReportFrame]:
    return DataFrame[ReportFrame](ReportFrame.validate(frame, lazy=True))


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


def selected_rows(
    rows: DataFrame[ReportFrame],
    key: EstimateKey,
    rounds: int,
) -> DataFrame[ReportFrame]:
    matches = rows.loc[
        rows["binary_sha256"].eq(key.binary_sha256)
        & rows["file_sha256"].eq(key.file_sha256)
        & rows["backend"].eq(key.backend)
        & rows["treatment"].eq(key.treatment)
        & rows["timeout_sec"].eq(key.timeout_sec)
    ]
    latest = matches.sort_values(["started_at", "row_index"], ascending=[False, False], kind="mergesort").head(rounds)
    selected = latest.sort_values(["started_at", "row_index"], kind="mergesort")
    return validate_report_frame(selected.reset_index(drop=True))


def status_counts_for_rows(rows: DataFrame[ReportFrame]) -> dict[str, int]:
    return {str(status): int(count) for status, count in rows["status"].value_counts().sort_index().items()}


def estimate_key_for(
    target: ResolvedTarget,
    file_spec: FileSpec,
    backend: Backend,
    treatment: Treatment,
    timeout_sec: int,
) -> EstimateKey:
    return EstimateKey(
        binary_sha256=target.binary_sha256,
        file_sha256=file_spec.sha256,
        treatment=treatment,
        timeout_sec=timeout_sec,
        backend=backend,
    )


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


def backend_flags(backend: Backend) -> list[str]:
    return list(backend_spec(backend).flags)


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
    table = Table(title=f"{plan.target.display_label}: cache and estimate plan")
    table.add_column("File", overflow="fold")
    table.add_column("Cell", no_wrap=True)
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
        table.add_row(
            cell.file.display_path,
            f"{cell.backend}/{cell.treatment}",
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

    def run_loop(progress: Progress, process_task: TaskID) -> None:
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


def summarize_cell(rows: DataFrame[ReportFrame], rounds: int) -> CellSummary:
    return summarize_metric_cell(rows, rounds, "wall_sec", "missing wall_sec")


def summarize_rss_cell(rows: DataFrame[ReportFrame], rounds: int) -> CellSummary:
    return summarize_metric_cell(rows, rounds, "max_rss_bytes", "missing max_rss_bytes")


def summarize_metric_cell(
    rows: DataFrame[ReportFrame],
    rounds: int,
    column: str,
    missing_issue: str,
) -> CellSummary:
    status_counts = status_counts_for_rows(rows)
    if len(rows) < rounds:
        return CellSummary(
            rows=rows,
            samples=(),
            status_counts=status_counts,
            mean=None,
            ci_low=None,
            ci_high=None,
            issue=f"missing {rounds - len(rows)} row(s)",
        )
    if status_counts.get("failure", 0):
        return CellSummary(rows, (), status_counts, None, None, None, "failure row selected")
    if status_counts.get("timed-out", 0):
        return CellSummary(rows, (), status_counts, None, None, None, "timeout row selected")
    samples = tuple(float(value) for value in rows.loc[rows[column].notna(), column].tolist())
    if len(samples) != len(rows):
        return CellSummary(rows, (), status_counts, None, None, None, missing_issue)
    mean, ci_low, ci_high = mean_interval(samples)
    return CellSummary(rows, samples, status_counts, mean, ci_low, ci_high, None)


def mean_interval(samples: Sequence[float]) -> tuple[float, float | None, float | None]:
    mean = float(np.mean(samples))
    if len(samples) < 2:
        return (mean, None, None)
    variance = float(np.var(samples, ddof=1))
    t_critical = float(stats.t.ppf(0.975, len(samples) - 1))
    half_width = t_critical * math.sqrt(variance / len(samples))
    return (mean, mean - half_width, mean + half_width)


def ratio_summary(
    baseline: CellSummary,
    candidate: CellSummary,
) -> RatioSummary:
    if not baseline.ok:
        return RatioSummary(None, None, None, baseline.issue or "baseline unavailable")
    if not candidate.ok:
        return RatioSummary(None, None, None, candidate.issue or "candidate unavailable")
    return ratio_from_samples(baseline.samples, candidate.samples)


def ratio_from_samples(
    baseline_samples: Sequence[float],
    candidate_samples: Sequence[float],
) -> RatioSummary:
    if len(baseline_samples) != len(candidate_samples):
        return RatioSummary(None, None, None, "sample counts differ")
    if len(baseline_samples) < 1:
        return RatioSummary(None, None, None, "no samples")
    baseline_mean = float(np.mean(baseline_samples))
    candidate_mean = float(np.mean(candidate_samples))
    if baseline_mean <= 0:
        return RatioSummary(None, None, None, "baseline mean is not positive")
    point = candidate_mean / baseline_mean
    if len(baseline_samples) < 2:
        return RatioSummary(point, None, None, "CI undefined for n < 2")
    n = len(baseline_samples)
    var_baseline_mean = float(np.var(baseline_samples, ddof=1)) / n
    var_candidate_mean = float(np.var(candidate_samples, ddof=1)) / n
    interval = fieller_interval(
        baseline_mean,
        candidate_mean,
        var_baseline_mean,
        var_candidate_mean,
        df=n - 1,
    )
    if interval is None:
        return RatioSummary(point, None, None, "Fieller interval undefined")
    return RatioSummary(point, interval[0], interval[1], None)


def fieller_interval(
    baseline_mean: float,
    candidate_mean: float,
    baseline_mean_variance: float,
    candidate_mean_variance: float,
    df: int,
) -> tuple[float, float] | None:
    if baseline_mean <= 0 or df <= 0:
        return None
    t_critical = float(stats.t.ppf(0.975, df))
    a = baseline_mean**2 - t_critical**2 * baseline_mean_variance
    d = candidate_mean**2 - t_critical**2 * candidate_mean_variance
    radicand = (baseline_mean * candidate_mean) ** 2 - a * d
    if a <= 0 or radicand < 0:
        return None
    center = baseline_mean * candidate_mean / a
    half_width = math.sqrt(radicand) / a
    return (center - half_width, center + half_width)


def suite_ratio(
    file_cells: Sequence[tuple[CellSummary, CellSummary]],
) -> RatioSummary:
    if not file_cells:
        return RatioSummary(None, None, None, "no files")
    for baseline, candidate in file_cells:
        if not baseline.ok:
            return RatioSummary(None, None, None, baseline.issue or "baseline unavailable")
        if not candidate.ok:
            return RatioSummary(None, None, None, candidate.issue or "candidate unavailable")
    sample_count = len(file_cells[0][0].samples)
    if sample_count < 1:
        return RatioSummary(None, None, None, "no samples")
    if any(len(b.samples) != sample_count or len(c.samples) != sample_count for b, c in file_cells):
        return RatioSummary(None, None, None, "sample counts differ")

    baseline_means = [float(np.mean(b.samples)) for b, _ in file_cells]
    candidate_means = [float(np.mean(c.samples)) for _, c in file_cells]
    baseline_sum = float(sum(baseline_means))
    candidate_sum = float(sum(candidate_means))
    if baseline_sum <= 0:
        return RatioSummary(None, None, None, "baseline mean is not positive")
    point = candidate_sum / baseline_sum
    if sample_count < 2:
        return RatioSummary(point, None, None, "CI undefined for n < 2")

    baseline_variance = sum(float(np.var(b.samples, ddof=1)) / sample_count for b, _ in file_cells)
    candidate_variance = sum(float(np.var(c.samples, ddof=1)) / sample_count for _, c in file_cells)
    interval = fieller_interval(
        baseline_sum,
        candidate_sum,
        baseline_variance,
        candidate_variance,
        df=sample_count - 1,
    )
    if interval is None:
        return RatioSummary(point, None, None, "Fieller interval undefined")
    return RatioSummary(point, interval[0], interval[1], None)


def geometric_mean_ratio(file_cells: Sequence[tuple[CellSummary, CellSummary]]) -> RatioSummary:
    ratios: list[float] = []
    for baseline, candidate in file_cells:
        if not baseline.ok:
            return RatioSummary(None, None, None, baseline.issue or "baseline unavailable")
        if not candidate.ok:
            return RatioSummary(None, None, None, candidate.issue or "candidate unavailable")
        if baseline.mean is None or candidate.mean is None or baseline.mean <= 0:
            return RatioSummary(None, None, None, "mean unavailable")
        ratios.append(candidate.mean / baseline.mean)
    if not ratios:
        return RatioSummary(None, None, None, "no files")
    return RatioSummary(float(math.exp(sum(math.log(value) for value in ratios) / len(ratios))), None, None, None)


def target_cell_summaries(
    rows: DataFrame[ReportFrame],
    target: ResolvedTarget,
    spec: BenchmarkSpec,
    backends: Sequence[Backend] | None = None,
    treatments: Sequence[Treatment] | None = None,
) -> CellMap:
    chosen_backends = spec.backends if backends is None else backends
    chosen_treatments = spec.treatments if treatments is None else treatments
    return {
        (file_spec.sha256, cell.backend, cell.treatment): summarize_cell(
            selected_rows(
                rows,
                estimate_key_for(target, file_spec, cell.backend, cell.treatment, spec.timeout_sec),
                spec.rounds,
            ),
            spec.rounds,
        )
        for file_spec in spec.files
        for cell in backend_treatment_cells(chosen_backends, chosen_treatments)
    }


def target_rss_cell_summaries(
    rows: DataFrame[ReportFrame],
    target: ResolvedTarget,
    spec: BenchmarkSpec,
    backends: Sequence[Backend] | None = None,
    treatments: Sequence[Treatment] | None = None,
) -> CellMap:
    chosen_backends = spec.backends if backends is None else backends
    chosen_treatments = spec.treatments if treatments is None else treatments
    return {
        (file_spec.sha256, cell.backend, cell.treatment): summarize_rss_cell(
            selected_rows(
                rows,
                estimate_key_for(target, file_spec, cell.backend, cell.treatment, spec.timeout_sec),
                spec.rounds,
            ),
            spec.rounds,
        )
        for file_spec in spec.files
        for cell in backend_treatment_cells(chosen_backends, chosen_treatments)
    }


def target_suite_treatment_ratio(
    baseline_cells: CellMap,
    candidate_cells: CellMap,
    spec: BenchmarkSpec,
    treatment: Treatment,
    backend: Backend = "main",
) -> RatioSummary:
    return suite_ratio(
        [
            (
                baseline_cells[(file_spec.sha256, backend, treatment)],
                candidate_cells[(file_spec.sha256, backend, treatment)],
            )
            for file_spec in spec.files
        ]
    )


def treatment_file_cells(
    cell_map: CellMap,
    spec: BenchmarkSpec,
    backend: Backend,
    baseline_treatment: Treatment,
    candidate_treatment: Treatment,
) -> list[tuple[FileSpec, CellSummary, CellSummary]]:
    return [
        (
            file_spec,
            cell_map[(file_spec.sha256, backend, baseline_treatment)],
            cell_map[(file_spec.sha256, backend, candidate_treatment)],
        )
        for file_spec in spec.files
    ]


def target_treatment_file_cells(
    baseline_cells: CellMap,
    candidate_cells: CellMap,
    spec: BenchmarkSpec,
    backend: Backend,
    treatment: Treatment,
) -> list[tuple[FileSpec, CellSummary, CellSummary]]:
    return [
        (
            file_spec,
            baseline_cells[(file_spec.sha256, backend, treatment)],
            candidate_cells[(file_spec.sha256, backend, treatment)],
        )
        for file_spec in spec.files
    ]


def backend_treatment_file_cells(
    cell_map: CellMap,
    spec: BenchmarkSpec,
    baseline_backend: Backend,
    candidate_backend: Backend,
    treatment: Treatment,
) -> list[tuple[FileSpec, CellSummary, CellSummary]]:
    return [
        (
            file_spec,
            cell_map[(file_spec.sha256, baseline_backend, treatment)],
            cell_map[(file_spec.sha256, candidate_backend, treatment)],
        )
        for file_spec in spec.files
    ]


def ratio_pairs(file_cells: Sequence[tuple[FileSpec, CellSummary, CellSummary]]) -> list[tuple[FileSpec, RatioSummary]]:
    return [(file_spec, ratio_summary(baseline, candidate)) for file_spec, baseline, candidate in file_cells]


def summary_pairs(
    file_cells: Sequence[tuple[FileSpec, CellSummary, CellSummary]],
) -> list[tuple[CellSummary, CellSummary]]:
    return [(baseline, candidate) for _, baseline, candidate in file_cells]


def worst_file_ratio(ratios: Sequence[tuple[FileSpec, RatioSummary]]) -> tuple[FileSpec | None, RatioSummary]:
    if not ratios:
        return (None, RatioSummary(None, None, None, "no files"))
    invalid = [(file_spec, ratio) for file_spec, ratio in ratios if ratio.point is None]
    if invalid:
        return invalid[0]
    valid = [(file_spec, ratio) for file_spec, ratio in ratios if ratio.point is not None]
    return max(valid, key=lambda item: item[1].point or 0.0)


def best_file_ratio(ratios: Sequence[tuple[FileSpec, RatioSummary]]) -> tuple[FileSpec | None, RatioSummary]:
    if not ratios:
        return (None, RatioSummary(None, None, None, "no files"))
    valid = [(file_spec, ratio) for file_spec, ratio in ratios if ratio.point is not None]
    if valid:
        return min(valid, key=lambda item: item[1].point or math.inf)
    return ratios[0]


def count_better_files(ratios: Sequence[tuple[FileSpec, RatioSummary]]) -> tuple[int, int]:
    valid = [ratio for _, ratio in ratios if ratio.point is not None]
    better = sum(1 for ratio in valid if ratio.ci_high is not None and ratio.ci_high < 1.0)
    return (better, len(valid))


def format_better_file_count(count: tuple[int, int]) -> str:
    better, total = count
    if total == 0:
        return "-"
    return f"{better}/{total}"


def suite_total_mean(cells: Sequence[CellSummary]) -> float | None:
    total = 0.0
    for cell in cells:
        if not cell.ok or cell.mean is None:
            return None
        total += cell.mean
    return total


def format_estimate_or_interval(
    point: float | None,
    low: float | None,
    high: float | None,
    suffix: str,
    digits: int,
) -> str:
    if point is None:
        return "-"
    point_text = f"{point:.{digits}f}{suffix}"
    if low is None or high is None:
        return point_text
    return f"[{low:.{digits}f}{suffix}, {high:.{digits}f}{suffix}]"


def format_seconds_summary(summary: CellSummary) -> str:
    return format_estimate_or_interval(summary.mean, summary.ci_low, summary.ci_high, "s", 4)


def format_seconds_value(value: float | None) -> str:
    return "-" if value is None else f"{value:.4f}s"


def format_bytes(value: float | None) -> str:
    if value is None:
        return "-"
    units = ("B", "KiB", "MiB", "GiB")
    amount = float(value)
    unit = units[0]
    for unit in units:
        if amount < 1024 or unit == units[-1]:
            break
        amount /= 1024
    if unit == "B":
        return f"{int(amount)} B"
    return f"{amount:.1f} {unit}"


def format_bytes_summary(summary: CellSummary) -> str:
    if summary.mean is None:
        return "-"
    point_text = format_bytes(summary.mean)
    if summary.ci_low is None or summary.ci_high is None:
        return point_text
    return f"[{format_bytes(summary.ci_low)}, {format_bytes(summary.ci_high)}]"


def format_ratio_summary(summary: RatioSummary) -> str:
    return format_estimate_or_interval(summary.point, summary.ci_low, summary.ci_high, "x", 3)


def format_wall_time_change(summary: RatioSummary) -> str:
    return format_percent_change(summary)


def format_percent_change(summary: RatioSummary) -> str:
    point = None if summary.point is None else (summary.point - 1.0) * 100.0
    low = None if summary.ci_low is None else (summary.ci_low - 1.0) * 100.0
    high = None if summary.ci_high is None else (summary.ci_high - 1.0) * 100.0
    return format_estimate_or_interval(point, low, high, "%", 1)


def result_style(status: str) -> str:
    return RESULT_STYLES.get(status, "")


def styled_status(status: str, text: str | None = None) -> Text:
    return Text(text or status, style=result_style(status))


def comparison_result(summary: RatioSummary) -> str:
    if summary.point is None:
        return "invalid"
    if summary.ci_low is None or summary.ci_high is None:
        return "point only"
    if summary.ci_high < 1:
        return "faster"
    if summary.ci_low > 1:
        return "slower"
    return "unclear"


def format_comparison_result(summary: RatioSummary) -> Text:
    result = comparison_result(summary)
    if result == "invalid" and summary.issue is not None:
        return styled_status(result, f"invalid: {summary.issue}")
    return styled_status(result)


def comparison_result_text(summary: RatioSummary) -> str:
    return format_comparison_result(summary).plain


def lower_is_better_result(summary: RatioSummary) -> str:
    if summary.point is None:
        return "invalid"
    if summary.ci_low is None or summary.ci_high is None:
        return "point only"
    if summary.ci_high < 1:
        return "less"
    if summary.ci_low > 1:
        return "more"
    return "unclear"


def format_lower_is_better_result(summary: RatioSummary) -> Text:
    result = lower_is_better_result(summary)
    if result == "invalid" and summary.issue is not None:
        return styled_status(result, f"invalid: {summary.issue}")
    return styled_status(result)


def lower_is_better_result_text(summary: RatioSummary) -> str:
    return format_lower_is_better_result(summary).plain


def proof_gate_result(summary: RatioSummary) -> tuple[str, str]:
    if summary.point is None:
        return ("invalid", f"invalid: {summary.issue or 'unavailable'}")
    if summary.ci_high is None:
        return ("point only", "point only")
    if summary.ci_high < 2:
        return ("established", "<2x established")
    return ("not established", "<2x not established")


def format_proof_gate_result(summary: RatioSummary) -> Text:
    status, text = proof_gate_result(summary)
    return styled_status(status, text)


def proof_gate_result_text(summary: RatioSummary) -> str:
    return proof_gate_result(summary)[1]


def report_row(*values: object) -> tuple[str, ...]:
    return tuple(str(value) for value in values)


def report_table(title: str, *, caption: str | None = None, show_lines: bool = False) -> Table:
    return Table(
        title=title,
        title_style="bold",
        caption=caption,
        caption_style="dim",
        caption_justify="left",
        header_style="bold",
        box=box.SIMPLE_HEAVY,
        show_lines=show_lines,
    )


def rich_result_cell(value: str) -> str | Text:
    if value.startswith("invalid:"):
        return styled_status("invalid", value)
    if value == "<2x established":
        return styled_status("established", value)
    if value == "<2x not established":
        return styled_status("not established", value)
    if value in RESULT_STYLES:
        return styled_status(value)
    return value


def render_rich_table(table_data: ReportTableData) -> Table:
    table = report_table(table_data.title, caption=table_data.caption)
    alignments = table_data.alignments or tuple("left" for _ in table_data.headers)
    for header, alignment in zip(table_data.headers, alignments, strict=True):
        table.add_column(header, no_wrap=alignment == "right", justify="right" if alignment == "right" else "left")
    result_columns = {"Result", "Best result"}
    for row in table_data.rows:
        values: list[str | Text] = []
        for header, value in zip(table_data.headers, row, strict=True):
            values.append(rich_result_cell(value) if header in result_columns else value)
        table.add_row(*values)
    return table


def markdown_escape_cell(value: object) -> str:
    text = str(value)
    return text.replace("\\", "\\\\").replace("|", "\\|").replace("\r\n", "\n").replace("\n", "<br>")


def render_markdown_table(table_data: ReportTableData, *, heading_level: int = 3) -> str:
    alignments = table_data.alignments or tuple("left" for _ in table_data.headers)
    separator_cells = tuple("---:" if alignment == "right" else "---" for alignment in alignments)
    lines = [
        f"{'#' * heading_level} {table_data.title}",
        "",
        "| " + " | ".join(markdown_escape_cell(header) for header in table_data.headers) + " |",
        "| " + " | ".join(separator_cells) + " |",
    ]
    for row in table_data.rows:
        lines.append("| " + " | ".join(markdown_escape_cell(value) for value in row) + " |")
    if table_data.caption:
        lines.extend(["", f"*{markdown_escape_cell(table_data.caption)}*"])
    return "\n".join(lines)


def benchmark_command_block(argv: Sequence[str]) -> str:
    return "```shell\n$ " + shlex.join(["./bench.py", *argv]) + "\n```"


def cell_label(spec: BenchmarkSpec, backend: Backend, treatment: Treatment) -> str:
    if len(spec.backends) == 1:
        return treatment
    return f"{backend}/{treatment}"


def backend_metric_label(spec: BenchmarkSpec, backend: Backend, label: str) -> str:
    if len(spec.backends) == 1:
        return label
    return f"{backend} {label}"


def render_report(
    console: Console,
    report_destination: ReportDestination,
    rows: DataFrame[ReportFrame],
    targets: Sequence[ResolvedTarget],
    spec: BenchmarkSpec,
) -> None:
    console.rule("[bold]Benchmark report[/bold]")
    console.print(f"Report: [bold]{escape(report_destination.display_path)}[/bold]")
    console.print(f"Selected rows per cell: [bold]{spec.rounds}[/bold]")

    render_targets_tree(console, targets)

    cell_maps = {target: target_cell_summaries(rows, target, spec) for target in targets}
    rss_cell_maps = {target: target_rss_cell_summaries(rows, target, spec) for target in targets}
    if len(targets) > 1:
        render_per_file_wall_time_change(console, cell_maps, targets, spec)
        render_per_file_peak_rss_change(console, rss_cell_maps, targets, spec)
    if len(spec.backends) > 1:
        render_per_file_backend_wall_time_change(console, cell_maps, targets, spec)
        render_per_file_backend_peak_rss_change(console, rss_cell_maps, targets, spec)

    for target in targets:
        render_target_diagnostics(console, cell_maps[target], rss_cell_maps[target], target, spec)

    render_benchmark_summary(console, cell_maps, rss_cell_maps, targets, spec)


def render_markdown_report(
    report_destination: ReportDestination,
    rows: DataFrame[ReportFrame],
    targets: Sequence[ResolvedTarget],
    spec: BenchmarkSpec,
    command_argv: Sequence[str] | None = None,
) -> str:
    cell_maps = {target: target_cell_summaries(rows, target, spec) for target in targets}
    rss_cell_maps = {target: target_rss_cell_summaries(rows, target, spec) for target in targets}
    parts = []
    if command_argv is not None:
        parts.append(benchmark_command_block(command_argv))
    parts.extend(
        [
            "# Benchmark Report",
            f"- Report: `{report_destination.display_path}`\n- Selected rows per cell: `{spec.rounds}`",
            render_markdown_table(targets_table_data(targets), heading_level=2),
        ]
    )

    comparison_tables: list[ReportTableData] = []
    if len(targets) > 1:
        comparison_tables.extend(per_file_wall_time_change_tables(cell_maps, targets, spec))
        comparison_tables.extend(per_file_peak_rss_change_tables(rss_cell_maps, targets, spec))
    if len(spec.backends) > 1:
        comparison_tables.extend(per_file_backend_wall_time_change_tables(cell_maps, targets, spec))
        comparison_tables.extend(per_file_backend_peak_rss_change_tables(rss_cell_maps, targets, spec))
    if comparison_tables:
        parts.append("## Comparisons")
        parts.extend(render_markdown_table(table_data) for table_data in comparison_tables)

    diagnostic_tables: list[ReportTableData] = []
    for target in targets:
        overhead = overhead_ratios_table_data(cell_maps[target], target, spec)
        if overhead is not None:
            diagnostic_tables.append(overhead)
        diagnostic_tables.append(target_wall_time_table_data(cell_maps[target], target, spec))
        peak_rss = target_peak_rss_table_data(rss_cell_maps[target], target, spec)
        if peak_rss is not None:
            diagnostic_tables.append(peak_rss)
    if diagnostic_tables:
        parts.append("## Target Diagnostics")
        parts.extend(render_markdown_table(table_data) for table_data in diagnostic_tables)

    summary_tables: list[ReportTableData] = list(backend_summary_tables(cell_maps, rss_cell_maps, targets, spec))
    if len(targets) == 1:
        summary_tables.append(
            single_target_summary_table_data(cell_maps[targets[0]], rss_cell_maps[targets[0]], targets[0], spec)
        )
    else:
        summary_tables.extend(multi_target_summary_tables(cell_maps, rss_cell_maps, targets, spec))
    parts.append("## Benchmark Summary")
    parts.extend(render_markdown_table(table_data) for table_data in summary_tables)
    return "\n\n".join(part.strip() for part in parts if part.strip())


def render_targets_tree(console: Console, targets: Sequence[ResolvedTarget]) -> None:
    tree = Tree("[bold]Targets[/bold]", guide_style="dim")
    for index, target in enumerate(targets):
        role = "target"
        if len(targets) > 1:
            role = "baseline" if index == 0 else "candidate"
        dirty = "dirty" if target.row.is_dirty else "clean"
        binary = target.binary_sha256.removeprefix("sha256:")[:12]
        branch = tree.add(f"[bold]{role}[/bold] {escape(target.display_label)}")
        branch.add(f"source: {escape(target.row.source)}")
        branch.add(f"git: {target.row.git_sha[:12]} ({dirty})")
        if target.row.git_ref != "HEAD":
            branch.add(f"ref: {escape(target.row.git_ref)}")
        branch.add(f"binary: {binary}")
        branch.add(f"path: {escape(target.row.path)}")
    console.print(tree)


def targets_table_data(targets: Sequence[ResolvedTarget]) -> ReportTableData:
    rows: list[tuple[str, ...]] = []
    for index, target in enumerate(targets):
        role = "target"
        if len(targets) > 1:
            role = "baseline" if index == 0 else "candidate"
        git = target.row.git_sha[:12]
        if target.row.git_ref != "HEAD":
            git = f"{git} ({target.row.git_ref})"
        rows.append(
            report_row(
                role,
                target.display_label,
                git,
                "yes" if target.row.is_dirty else "no",
                target.binary_sha256.removeprefix("sha256:")[:12],
                target.row.path,
            )
        )
    return ReportTableData(
        title="Targets",
        headers=("Role", "Label", "Git", "Dirty", "Binary", "Path"),
        rows=tuple(rows),
    )


def per_file_wall_time_change_tables(
    cell_maps: TargetCellMaps,
    targets: Sequence[ResolvedTarget],
    spec: BenchmarkSpec,
) -> tuple[ReportTableData, ...]:
    baseline = targets[0]
    cells = benchmark_cells(spec)
    tables: list[ReportTableData] = []
    for target in targets[1:]:
        rows: list[tuple[str, ...]] = []
        for file_spec in spec.files:
            for cell_index, cell in enumerate(cells):
                ratio = ratio_summary(
                    cell_maps[baseline][(file_spec.sha256, cell.backend, cell.treatment)],
                    cell_maps[target][(file_spec.sha256, cell.backend, cell.treatment)],
                )
                rows.append(
                    report_row(
                        file_spec.display_path if cell_index == 0 else "",
                        cell.backend,
                        cell.treatment,
                        format_ratio_summary(ratio),
                        format_wall_time_change(ratio),
                        comparison_result_text(ratio),
                    )
                )
        tables.append(
            ReportTableData(
                title=f"Per-file wall-time change vs {baseline.display_label}: {target.display_label}",
                headers=("File", "Backend", "Treatment", "Time ratio", "Wall-time change", "Result"),
                rows=tuple(rows),
                caption=TARGET_WALL_TIME_CAPTION,
                alignments=("left", "left", "left", "right", "right", "left"),
            )
        )
    return tuple(tables)


def render_per_file_wall_time_change(
    console: Console,
    cell_maps: TargetCellMaps,
    targets: Sequence[ResolvedTarget],
    spec: BenchmarkSpec,
) -> None:
    for table_data in per_file_wall_time_change_tables(cell_maps, targets, spec):
        console.print(render_rich_table(table_data))


def per_file_peak_rss_change_tables(
    rss_cell_maps: TargetCellMaps,
    targets: Sequence[ResolvedTarget],
    spec: BenchmarkSpec,
) -> tuple[ReportTableData, ...]:
    baseline = targets[0]
    baseline_has_rss = any(cell.samples for cell in rss_cell_maps[baseline].values())
    cells = benchmark_cells(spec)
    tables: list[ReportTableData] = []
    for target in targets[1:]:
        if not baseline_has_rss and not any(cell.samples for cell in rss_cell_maps[target].values()):
            continue
        rows: list[tuple[str, ...]] = []
        for file_spec in spec.files:
            for cell_index, cell in enumerate(cells):
                ratio = ratio_summary(
                    rss_cell_maps[baseline][(file_spec.sha256, cell.backend, cell.treatment)],
                    rss_cell_maps[target][(file_spec.sha256, cell.backend, cell.treatment)],
                )
                rows.append(
                    report_row(
                        file_spec.display_path if cell_index == 0 else "",
                        cell.backend,
                        cell.treatment,
                        format_ratio_summary(ratio),
                        format_percent_change(ratio),
                        lower_is_better_result_text(ratio),
                    )
                )
        tables.append(
            ReportTableData(
                title=f"Per-file peak RSS change vs {baseline.display_label}: {target.display_label}",
                headers=("File", "Backend", "Treatment", "RSS ratio", "RSS change", "Result"),
                rows=tuple(rows),
                caption=TARGET_PEAK_RSS_CAPTION,
                alignments=("left", "left", "left", "right", "right", "left"),
            )
        )
    return tuple(tables)


def render_per_file_peak_rss_change(
    console: Console,
    rss_cell_maps: TargetCellMaps,
    targets: Sequence[ResolvedTarget],
    spec: BenchmarkSpec,
) -> None:
    for table_data in per_file_peak_rss_change_tables(rss_cell_maps, targets, spec):
        console.print(render_rich_table(table_data))


def per_file_backend_wall_time_change_tables(
    cell_maps: TargetCellMaps,
    targets: Sequence[ResolvedTarget],
    spec: BenchmarkSpec,
) -> tuple[ReportTableData, ...]:
    baseline_backend = spec.backends[0]
    tables: list[ReportTableData] = []
    for target in targets:
        for backend in spec.backends[1:]:
            shared_treatments = shared_backend_treatments(spec, baseline_backend, backend)
            if not shared_treatments:
                continue
            rows: list[tuple[str, ...]] = []
            for file_spec in spec.files:
                for treatment_index, treatment in enumerate(shared_treatments):
                    ratio = ratio_summary(
                        cell_maps[target][(file_spec.sha256, baseline_backend, treatment)],
                        cell_maps[target][(file_spec.sha256, backend, treatment)],
                    )
                    rows.append(
                        report_row(
                            file_spec.display_path if treatment_index == 0 else "",
                            treatment,
                            format_ratio_summary(ratio),
                            format_wall_time_change(ratio),
                            comparison_result_text(ratio),
                        )
                    )
            tables.append(
                ReportTableData(
                    title=f"Per-file backend wall-time change vs {baseline_backend}: {target.display_label} {backend}",
                    headers=("File", "Treatment", "Time ratio", "Wall-time change", "Result"),
                    rows=tuple(rows),
                    caption=BACKEND_WALL_TIME_CAPTION,
                    alignments=("left", "left", "right", "right", "left"),
                )
            )
    return tuple(tables)


def render_per_file_backend_wall_time_change(
    console: Console,
    cell_maps: TargetCellMaps,
    targets: Sequence[ResolvedTarget],
    spec: BenchmarkSpec,
) -> None:
    for table_data in per_file_backend_wall_time_change_tables(cell_maps, targets, spec):
        console.print(render_rich_table(table_data))


def per_file_backend_peak_rss_change_tables(
    rss_cell_maps: TargetCellMaps,
    targets: Sequence[ResolvedTarget],
    spec: BenchmarkSpec,
) -> tuple[ReportTableData, ...]:
    baseline_backend = spec.backends[0]
    baseline_has_rss = {
        target: any(cell.samples for key, cell in rss_cell_maps[target].items() if key[1] == baseline_backend)
        for target in targets
    }
    tables: list[ReportTableData] = []
    for target in targets:
        for backend in spec.backends[1:]:
            shared_treatments = shared_backend_treatments(spec, baseline_backend, backend)
            if not shared_treatments:
                continue
            candidate_has_rss = any(cell.samples for key, cell in rss_cell_maps[target].items() if key[1] == backend)
            if not baseline_has_rss[target] and not candidate_has_rss:
                continue
            rows: list[tuple[str, ...]] = []
            for file_spec in spec.files:
                for treatment_index, treatment in enumerate(shared_treatments):
                    ratio = ratio_summary(
                        rss_cell_maps[target][(file_spec.sha256, baseline_backend, treatment)],
                        rss_cell_maps[target][(file_spec.sha256, backend, treatment)],
                    )
                    rows.append(
                        report_row(
                            file_spec.display_path if treatment_index == 0 else "",
                            treatment,
                            format_ratio_summary(ratio),
                            format_percent_change(ratio),
                            lower_is_better_result_text(ratio),
                        )
                    )
            tables.append(
                ReportTableData(
                    title=f"Per-file backend peak RSS change vs {baseline_backend}: {target.display_label} {backend}",
                    headers=("File", "Treatment", "RSS ratio", "RSS change", "Result"),
                    rows=tuple(rows),
                    caption=BACKEND_PEAK_RSS_CAPTION,
                    alignments=("left", "left", "right", "right", "left"),
                )
            )
    return tuple(tables)


def render_per_file_backend_peak_rss_change(
    console: Console,
    rss_cell_maps: TargetCellMaps,
    targets: Sequence[ResolvedTarget],
    spec: BenchmarkSpec,
) -> None:
    for table_data in per_file_backend_peak_rss_change_tables(rss_cell_maps, targets, spec):
        console.print(render_rich_table(table_data))


def render_benchmark_summary(
    console: Console,
    cell_maps: TargetCellMaps,
    rss_cell_maps: TargetCellMaps,
    targets: Sequence[ResolvedTarget],
    spec: BenchmarkSpec,
) -> None:
    console.rule("[bold]Benchmark summary[/bold]")
    render_backend_summary(console, cell_maps, rss_cell_maps, targets, spec)
    if len(targets) == 1:
        render_single_target_summary(console, cell_maps[targets[0]], rss_cell_maps[targets[0]], targets[0], spec)
    else:
        render_multi_target_summary(console, cell_maps, rss_cell_maps, targets, spec)


def single_target_summary_table_data(
    cell_map: CellMap,
    rss_cell_map: CellMap,
    target: ResolvedTarget,
    spec: BenchmarkSpec,
) -> ReportTableData:
    rows: list[tuple[str, ...]] = []
    for backend in spec.backends:
        has_off_proofs = backend_has_treatment(spec, backend, "off") and backend_has_treatment(spec, backend, "proofs")
        has_term_proofs = backend_has_treatment(spec, backend, "term") and backend_has_treatment(
            spec, backend, "proofs"
        )
        if has_off_proofs:
            rows.extend(
                within_target_wall_summary_rows(
                    cell_map,
                    spec,
                    backend,
                    "off",
                    "proofs",
                    backend_metric_label(spec, backend, "wall proofs/off"),
                )
            )
            rows.append(
                within_target_rss_summary_row(
                    rss_cell_map,
                    spec,
                    backend,
                    "off",
                    "proofs",
                    backend_metric_label(spec, backend, "peak RSS proofs/off"),
                )
            )
        elif has_term_proofs:
            rows.extend(
                within_target_wall_summary_rows(
                    cell_map,
                    spec,
                    backend,
                    "term",
                    "proofs",
                    backend_metric_label(spec, backend, "wall proofs/term"),
                )
            )
        else:
            rows.append(
                report_row(
                    backend_metric_label(spec, backend, "no proof baseline"),
                    "-",
                    "-",
                    "-",
                    "-",
                    "select off and proofs",
                )
            )
        if has_term_proofs:
            rows.append(
                within_target_rss_summary_row(
                    rss_cell_map,
                    spec,
                    backend,
                    "term",
                    "proofs",
                    backend_metric_label(spec, backend, "peak RSS proofs/term"),
                )
            )
    return ReportTableData(
        title=f"{target.display_label}: proof overhead summary",
        headers=("Metric", "Ratio", "Change", "Worst file", "Worst ratio", "Result"),
        rows=tuple(rows),
        caption=PROOF_OVERHEAD_CAPTION,
        alignments=("left", "right", "right", "left", "right", "left"),
    )


def render_single_target_summary(
    console: Console,
    cell_map: CellMap,
    rss_cell_map: CellMap,
    target: ResolvedTarget,
    spec: BenchmarkSpec,
) -> None:
    console.print(render_rich_table(single_target_summary_table_data(cell_map, rss_cell_map, target, spec)))


def within_target_wall_summary_rows(
    cell_map: CellMap,
    spec: BenchmarkSpec,
    backend: Backend,
    baseline_treatment: Treatment,
    candidate_treatment: Treatment,
    label: str,
) -> tuple[tuple[str, ...], tuple[str, ...]]:
    file_cells = treatment_file_cells(cell_map, spec, backend, baseline_treatment, candidate_treatment)
    pairs = summary_pairs(file_cells)
    summary = suite_ratio(pairs)
    geometric = geometric_mean_ratio(pairs)
    worst_file, worst = worst_file_ratio(ratio_pairs(file_cells))
    result = (
        proof_gate_result_text(summary)
        if baseline_treatment == "off" and candidate_treatment == "proofs"
        else comparison_result_text(summary)
    )
    return (
        report_row(
            label,
            format_ratio_summary(summary),
            format_percent_change(summary),
            format_worst_file(worst_file),
            format_ratio_summary(worst),
            result,
        ),
        report_row(
            f"{label} geomean",
            format_ratio_summary(geometric),
            format_percent_change(geometric),
            "-",
            "-",
            "descriptive",
        ),
    )


def within_target_rss_summary_row(
    rss_cell_map: CellMap,
    spec: BenchmarkSpec,
    backend: Backend,
    baseline_treatment: Treatment,
    candidate_treatment: Treatment,
    label: str,
) -> tuple[str, ...]:
    file_cells = treatment_file_cells(rss_cell_map, spec, backend, baseline_treatment, candidate_treatment)
    pairs = summary_pairs(file_cells)
    summary = suite_ratio(pairs)
    worst_file, worst = worst_file_ratio(ratio_pairs(file_cells))
    return report_row(
        label,
        format_ratio_summary(summary),
        format_percent_change(summary),
        format_worst_file(worst_file),
        format_ratio_summary(worst),
        lower_is_better_result_text(summary),
    )


def multi_target_summary_tables(
    cell_maps: TargetCellMaps,
    rss_cell_maps: TargetCellMaps,
    targets: Sequence[ResolvedTarget],
    spec: BenchmarkSpec,
) -> tuple[ReportTableData, ReportTableData]:
    baseline = targets[0]
    cells = benchmark_cells(spec)
    wall_rows: list[tuple[str, ...]] = []
    for target in targets[1:]:
        for cell in cells:
            file_cells = target_treatment_file_cells(
                cell_maps[baseline], cell_maps[target], spec, cell.backend, cell.treatment
            )
            pairs = summary_pairs(file_cells)
            suite = suite_ratio(pairs)
            geometric = geometric_mean_ratio(pairs)
            worst_file, worst = worst_file_ratio(ratio_pairs(file_cells))
            wall_rows.append(
                report_row(
                    target.display_label,
                    cell.backend,
                    cell.treatment,
                    format_wall_time_change(suite),
                    format_ratio_summary(geometric),
                    format_worst_file(worst_file),
                    format_ratio_summary(worst),
                    comparison_result_text(suite),
                )
            )

    rss_rows: list[tuple[str, ...]] = []
    for target in targets[1:]:
        for cell in cells:
            file_cells = target_treatment_file_cells(
                rss_cell_maps[baseline],
                rss_cell_maps[target],
                spec,
                cell.backend,
                cell.treatment,
            )
            pairs = summary_pairs(file_cells)
            summary = suite_ratio(pairs)
            geometric = geometric_mean_ratio(pairs)
            worst_file, worst = worst_file_ratio(ratio_pairs(file_cells))
            rss_rows.append(
                report_row(
                    target.display_label,
                    cell.backend,
                    cell.treatment,
                    format_percent_change(summary),
                    format_ratio_summary(geometric),
                    format_worst_file(worst_file),
                    format_ratio_summary(worst),
                    lower_is_better_result_text(summary),
                )
            )
    return (
        ReportTableData(
            title=f"Wall-time summary vs {baseline.display_label}",
            headers=(
                "Target",
                "Backend",
                "Treatment",
                "Wall-time change",
                "Geomean",
                "Worst file",
                "Worst ratio",
                "Result",
            ),
            rows=tuple(wall_rows),
            caption=TARGET_WALL_TIME_CAPTION,
            alignments=("left", "left", "left", "right", "right", "left", "right", "left"),
        ),
        ReportTableData(
            title=f"Peak RSS summary vs {baseline.display_label}",
            headers=("Target", "Backend", "Treatment", "RSS change", "Geomean", "Worst file", "Worst ratio", "Result"),
            rows=tuple(rss_rows),
            caption=TARGET_PEAK_RSS_CAPTION,
            alignments=("left", "left", "left", "right", "right", "left", "right", "left"),
        ),
    )


def render_multi_target_summary(
    console: Console,
    cell_maps: TargetCellMaps,
    rss_cell_maps: TargetCellMaps,
    targets: Sequence[ResolvedTarget],
    spec: BenchmarkSpec,
) -> None:
    for table_data in multi_target_summary_tables(cell_maps, rss_cell_maps, targets, spec):
        console.print(render_rich_table(table_data))


def display_backend(backend: Backend) -> str:
    return backend_spec(backend).display_name


def backend_summary_table(
    cell_maps: TargetCellMaps,
    targets: Sequence[ResolvedTarget],
    spec: BenchmarkSpec,
    metric: MetricSpec,
) -> ReportTableData:
    baseline_backend = spec.backends[0]
    baseline_name = display_backend(baseline_backend)
    include_target = len(targets) > 1
    if len(spec.backends) == 2:
        candidate_name = display_backend(spec.backends[1])
        title = f"{candidate_name} vs {baseline_name} {metric.title}"
    else:
        candidate_name = "Candidate"
        title = f"Backend {metric.title} summary vs {baseline_name}"
    ratio_heading = f"{candidate_name}/{baseline_name}"
    candidate_total_heading = f"{candidate_name} total"
    headers: list[str] = []
    if include_target:
        headers.append("Target")
    headers.extend(
        [
            "Backend",
            "Mode",
            f"{baseline_name} total",
            candidate_total_heading,
            ratio_heading,
            "Change",
            "File geomean",
            metric.file_count_heading,
            "Best file",
            "Best ratio",
            "Best result",
        ]
    )
    rows: list[tuple[str, ...]] = []
    for target in targets:
        for backend in spec.backends[1:]:
            for treatment in shared_backend_treatments(spec, baseline_backend, backend):
                file_cells = backend_treatment_file_cells(
                    cell_maps[target],
                    spec,
                    baseline_backend,
                    backend,
                    treatment,
                )
                pairs = summary_pairs(file_cells)
                summary = suite_ratio(pairs)
                geometric = geometric_mean_ratio(pairs)
                ratios = ratio_pairs(file_cells)
                best_file, best = best_file_ratio(ratios)
                row_values: list[object] = []
                if include_target:
                    row_values.append(target.display_label)
                row_values.extend(
                    [
                        backend,
                        treatment,
                        metric.format_total(suite_total_mean([baseline for baseline, _ in pairs])),
                        metric.format_total(suite_total_mean([candidate for _, candidate in pairs])),
                        format_ratio_summary(summary),
                        metric.format_change(summary),
                        format_ratio_summary(geometric),
                        format_better_file_count(count_better_files(ratios)),
                        format_worst_file(best_file),
                        format_ratio_summary(best),
                        metric.format_result(best),
                    ]
                )
                rows.append(report_row(*row_values))
    right_aligned = {
        f"{baseline_name} total",
        candidate_total_heading,
        ratio_heading,
        "Change",
        "File geomean",
        metric.file_count_heading,
        "Best ratio",
    }
    return ReportTableData(
        title=title,
        headers=tuple(headers),
        rows=tuple(rows),
        caption=metric.caption,
        alignments=tuple("right" if header in right_aligned else "left" for header in headers),
    )


def backend_summary_tables(
    cell_maps: TargetCellMaps,
    rss_cell_maps: TargetCellMaps,
    targets: Sequence[ResolvedTarget],
    spec: BenchmarkSpec,
) -> tuple[ReportTableData, ...]:
    if len(spec.backends) <= 1:
        return ()
    metrics = (
        (
            cell_maps,
            MetricSpec(
                title="wall time",
                caption=BACKEND_WALL_TIME_CAPTION,
                file_count_heading="Faster files",
                format_total=format_seconds_value,
                format_change=format_wall_time_change,
                format_result=comparison_result_text,
            ),
        ),
        (
            rss_cell_maps,
            MetricSpec(
                title="peak RSS",
                caption=BACKEND_PEAK_RSS_CAPTION,
                file_count_heading="Lower-RSS files",
                format_total=format_bytes,
                format_change=format_percent_change,
                format_result=lower_is_better_result_text,
                omit_without_samples=True,
            ),
        ),
    )
    return tuple(
        backend_summary_table(metric_cell_maps, targets, spec, metric)
        for metric_cell_maps, metric in metrics
        if not metric.omit_without_samples
        or any(cell.samples for target in targets for cell in metric_cell_maps[target].values())
    )


def render_backend_summary(
    console: Console,
    cell_maps: TargetCellMaps,
    rss_cell_maps: TargetCellMaps,
    targets: Sequence[ResolvedTarget],
    spec: BenchmarkSpec,
) -> None:
    for table_data in backend_summary_tables(cell_maps, rss_cell_maps, targets, spec):
        console.print(render_rich_table(table_data))


def format_worst_file(file_spec: FileSpec | None) -> str:
    return "-" if file_spec is None else file_spec.display_path


def render_target_diagnostics(
    console: Console,
    cell_map: CellMap,
    rss_cell_map: CellMap,
    target: ResolvedTarget,
    spec: BenchmarkSpec,
) -> None:
    render_overhead_ratios(console, cell_map, target, spec)
    console.print(render_rich_table(target_wall_time_table_data(cell_map, target, spec)))
    render_peak_rss_diagnostics(console, rss_cell_map, target, spec)


def target_wall_time_table_data(cell_map: CellMap, target: ResolvedTarget, spec: BenchmarkSpec) -> ReportTableData:
    cells = benchmark_cells(spec)
    headers = ["File", *(cell_label(spec, cell.backend, cell.treatment) for cell in cells)]
    rows_with_issue: list[tuple[list[str], str]] = []
    has_mean_issues = False
    for file_spec in spec.files:
        issue_parts: list[str] = []
        row_values = [file_spec.display_path]
        for cell in cells:
            summary = cell_map[(file_spec.sha256, cell.backend, cell.treatment)]
            row_values.append(format_seconds_summary(summary))
            if summary.issue is not None:
                issue_parts.append(f"{cell_label(spec, cell.backend, cell.treatment)}: {summary.issue}")
        issue_text = "; ".join(issue_parts)
        has_mean_issues = has_mean_issues or bool(issue_text)
        rows_with_issue.append((row_values, issue_text))
    if has_mean_issues:
        headers.append("Issue")
    rows: list[tuple[str, ...]] = []
    for row_values, issue_text in rows_with_issue:
        if has_mean_issues:
            row_values.append(issue_text)
        rows.append(tuple(row_values))
    return ReportTableData(
        title=f"{target.display_label}: per-file wall time",
        headers=tuple(headers),
        rows=tuple(rows),
        caption="Within-target wall-time estimates. These are not target-vs-baseline ratios.",
        alignments=tuple(
            "left" if index == 0 or header == "Issue" else "right" for index, header in enumerate(headers)
        ),
    )


def render_overhead_ratios(
    console: Console,
    cell_map: CellMap,
    target: ResolvedTarget,
    spec: BenchmarkSpec,
) -> None:
    table_data = overhead_ratios_table_data(cell_map, target, spec)
    if table_data is not None:
        console.print(render_rich_table(table_data))


def overhead_ratios_table_data(
    cell_map: CellMap, target: ResolvedTarget, spec: BenchmarkSpec
) -> ReportTableData | None:
    ratio_columns = {backend: ratio_specs_for_backend(spec, backend) for backend in spec.backends}
    if not any(ratio_columns.values()):
        return None
    headers = ["File"]
    for backend in spec.backends:
        for _, _, ratio_name in ratio_columns[backend]:
            headers.append(backend_metric_label(spec, backend, ratio_name))
    rows: list[tuple[str, ...]] = []
    for file_spec in spec.files:
        row_values = [file_spec.display_path]
        for backend in spec.backends:
            for baseline_treatment, candidate_treatment, _ in ratio_columns[backend]:
                ratio = ratio_summary(
                    cell_map[(file_spec.sha256, backend, baseline_treatment)],
                    cell_map[(file_spec.sha256, backend, candidate_treatment)],
                )
                row_values.append(format_ratio_summary(ratio))
        rows.append(tuple(row_values))
    return ReportTableData(
        title=f"{target.display_label}: overhead ratios",
        headers=tuple(headers),
        rows=tuple(rows),
        caption="Within-target treatment ratios. These are not target-vs-baseline wall-time change.",
        alignments=tuple("left" if index == 0 else "right" for index, _ in enumerate(headers)),
    )


def render_peak_rss_diagnostics(
    console: Console,
    rss_cell_map: CellMap,
    target: ResolvedTarget,
    spec: BenchmarkSpec,
) -> None:
    table_data = target_peak_rss_table_data(rss_cell_map, target, spec)
    if table_data is not None:
        console.print(render_rich_table(table_data))


def target_peak_rss_table_data(
    rss_cell_map: CellMap,
    target: ResolvedTarget,
    spec: BenchmarkSpec,
) -> ReportTableData | None:
    if not any(cell.samples for cell in rss_cell_map.values()):
        return None
    cells = benchmark_cells(spec)
    headers = ["File", *(cell_label(spec, cell.backend, cell.treatment) for cell in cells)]
    rss_rows: list[tuple[list[str], str]] = []
    has_rss_issues = False
    for file_spec in spec.files:
        issue_parts: list[str] = []
        row_values = [file_spec.display_path]
        for cell in cells:
            summary = rss_cell_map[(file_spec.sha256, cell.backend, cell.treatment)]
            row_values.append(format_bytes_summary(summary))
            if summary.issue is not None:
                issue_parts.append(f"{cell_label(spec, cell.backend, cell.treatment)}: {summary.issue}")
        issue_text = "; ".join(issue_parts)
        has_rss_issues = has_rss_issues or bool(issue_text)
        rss_rows.append((row_values, issue_text))
    if has_rss_issues:
        headers.append("Issue")
    rows: list[tuple[str, ...]] = []
    for row_values, issue_text in rss_rows:
        if has_rss_issues:
            row_values.append(issue_text)
        rows.append(tuple(row_values))
    return ReportTableData(
        title=f"{target.display_label}: per-file peak RSS",
        headers=tuple(headers),
        rows=tuple(rows),
        caption="Within-target peak resident set size estimates. These are separate from wall-time ratios.",
        alignments=tuple(
            "left" if index == 0 or header == "Issue" else "right" for index, header in enumerate(headers)
        ),
    )


def ratio_specs(treatments: Sequence[Treatment]) -> tuple[tuple[Treatment, Treatment, str], ...]:
    specs: list[tuple[Treatment, Treatment, str]] = []
    if "off" in treatments and "term" in treatments:
        specs.append(("off", "term", "term/off"))
    if "off" in treatments and "proofs" in treatments:
        specs.append(("off", "proofs", "proofs/off"))
    if "term" in treatments and "proofs" in treatments:
        specs.append(("term", "proofs", "proofs/term"))
    return tuple(specs)


def ratio_specs_for_backend(
    spec: BenchmarkSpec,
    backend: Backend,
) -> tuple[tuple[Treatment, Treatment, str], ...]:
    return tuple(
        ratio_spec
        for ratio_spec in ratio_specs(spec.treatments)
        if backend_has_treatment(spec, backend, ratio_spec[0]) and backend_has_treatment(spec, backend, ratio_spec[1])
    )


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
    except (FileNotFoundError, ValueError, subprocess.CalledProcessError, subprocess.TimeoutExpired) as error:
        output.print_error(error)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
