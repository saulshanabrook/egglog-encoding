#!/usr/bin/env -S uv run
from __future__ import annotations

import argparse
import hashlib
import math
import os
import re
import resource
import subprocess
import sys
import time
from collections.abc import Callable, Mapping, Sequence
from dataclasses import dataclass, replace
from datetime import UTC, datetime
from pathlib import Path
from typing import Any, Literal, TextIO, cast

import numpy as np
import pandas as pd
import pandera.pandas as pa
from pandera.typing import DataFrame, Series
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
from scipy import stats

Status = Literal["success", "timed-out", "failure"]
Treatment = Literal["off", "term", "proofs"]

DEFAULT_REPORT = ".reports.jsonl"
DEFAULT_ROUNDS = 6
DEFAULT_WARMUP = 1
DEFAULT_TIMEOUT_SEC = 120
DEFAULT_TREATMENTS: tuple[Treatment, ...] = ("off", "term", "proofs")
DEFAULT_FILES = (
    "egglog/tests/math-microbenchmark.egg",
    "egglog/tests/web-demo/rw-analysis.egg",
    "egglog/tests/integer_math.egg",
    "egglog/tests/web-demo/resolution.egg",
)


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
    treatment: Series[str] = pa.Field(isin=["off", "term", "proofs"])
    warmup_rounds: Series[int] = pa.Field(ge=0)
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
    warmup_rounds: int
    timeout_sec: int


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
    warmup_rounds: int
    timeout_sec: int


@dataclass(frozen=True)
class CellPlan:
    target: ResolvedTarget
    file: FileSpec
    treatment: Treatment
    required_rows: int
    selected_cached_rows: DataFrame[ReportFrame]
    missing_observations: int
    estimate_key: EstimateKey

    @property
    def planned_processes(self) -> int:
        return self.missing_observations * (self.estimate_key.warmup_rounds + 1)


@dataclass(frozen=True)
class CollectionPlan:
    target: ResolvedTarget
    cells: tuple[CellPlan, ...]

    @property
    def total_missing_observations(self) -> int:
        return sum(cell.missing_observations for cell in self.cells)

    @property
    def total_planned_processes(self) -> int:
        return sum(cell.planned_processes for cell in self.cells)


@dataclass(frozen=True)
class DurationEstimate:
    seconds: float | None
    unknown_processes: int


@dataclass(frozen=True)
class SelectedObservation:
    target: ResolvedTarget
    file: FileSpec
    treatment: Treatment
    row: pd.Series[Any]
    origin: str


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


CellMap = dict[tuple[str, Treatment], CellSummary]


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


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Collect or reuse egglog-experimental benchmark reports.",
    )
    parser.add_argument("files", nargs="*", help="egglog files to benchmark")
    parser.add_argument(
        "--target",
        action="append",
        default=None,
        help="target source: ., /path, @git-ref, label=source, or label=",
    )
    parser.add_argument(
        "--report",
        default=DEFAULT_REPORT,
        help=f"JSONL report/cache path, or - for stdout (default: {DEFAULT_REPORT})",
    )
    parser.add_argument(
        "--rounds",
        type=positive_int,
        default=DEFAULT_ROUNDS,
        help=f"rows required per cache cell (default: {DEFAULT_ROUNDS})",
    )
    parser.add_argument(
        "--warmup",
        type=nonnegative_int,
        default=DEFAULT_WARMUP,
        help=f"untimed warmup runs per cell (default: {DEFAULT_WARMUP})",
    )
    parser.add_argument(
        "--timeout-sec",
        type=positive_int,
        default=DEFAULT_TIMEOUT_SEC,
        help=f"per-process timeout in seconds (default: {DEFAULT_TIMEOUT_SEC})",
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
    return parser.parse_args(argv)


def positive_int(value: str) -> int:
    parsed = int(value)
    if parsed <= 0:
        raise argparse.ArgumentTypeError("must be positive")
    return parsed


def nonnegative_int(value: str) -> int:
    parsed = int(value)
    if parsed < 0:
        raise argparse.ArgumentTypeError("must be non-negative")
    return parsed


def parse_treatments(value: str) -> tuple[Treatment, ...]:
    treatments: list[Treatment] = []
    for raw in value.split(","):
        item = raw.strip()
        if not item:
            continue
        if item not in {"off", "term", "proofs"}:
            raise ValueError(f"unknown treatment: {item}")
        treatments.append(cast(Treatment, item))
    if not treatments:
        raise ValueError("at least one treatment is required")
    return tuple(treatments)


def parse_target(raw: str) -> TargetRequest:
    if "=" in raw:
        label, source = raw.split("=", 1)
        if not label:
            raise ValueError(f"target label cannot be empty: {raw}")
        return TargetRequest(raw=raw, source=source, label=label)
    return TargetRequest(raw=raw, source=raw, label=None)


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
    for column in columns:
        if column not in normalized.columns:
            normalized[column] = pd.NA
    normalized = normalized.loc[:, columns]
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
                warmup_rounds=int(record["warmup_rounds"]),
                timeout_sec=int(record["timeout_sec"]),
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
        & rows["treatment"].eq(key.treatment)
        & rows["warmup_rounds"].eq(key.warmup_rounds)
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
    treatment: Treatment,
    warmup_rounds: int,
    timeout_sec: int,
) -> EstimateKey:
    return EstimateKey(
        binary_sha256=target.binary_sha256,
        file_sha256=file_spec.sha256,
        treatment=treatment,
        warmup_rounds=warmup_rounds,
        timeout_sec=timeout_sec,
    )


def build_collection_plan(
    rows: DataFrame[ReportFrame],
    target: ResolvedTarget,
    spec: BenchmarkSpec,
    force_run: bool,
) -> CollectionPlan:
    cells: list[CellPlan] = []
    for file_spec in spec.files:
        for treatment in spec.treatments:
            estimate_key = estimate_key_for(target, file_spec, treatment, spec.warmup_rounds, spec.timeout_sec)
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
                    treatment=treatment,
                    required_rows=spec.rounds,
                    selected_cached_rows=cached,
                    missing_observations=missing,
                    estimate_key=estimate_key,
                )
            )
    return CollectionPlan(target=target, cells=tuple(cells))


def selected_observations(
    rows: DataFrame[ReportFrame],
    targets: Sequence[ResolvedTarget],
    spec: BenchmarkSpec,
    fresh_indices: set[int],
) -> tuple[SelectedObservation, ...]:
    observations: list[SelectedObservation] = []
    for target in targets:
        for file_spec in spec.files:
            for treatment in spec.treatments:
                selected = selected_rows(
                    rows,
                    estimate_key_for(target, file_spec, treatment, spec.warmup_rounds, spec.timeout_sec),
                    spec.rounds,
                )
                for _, item in selected.iterrows():
                    observations.append(
                        SelectedObservation(
                            target=target,
                            file=file_spec,
                            treatment=treatment,
                            row=item,
                            origin="fresh" if int(item["row_index"]) in fresh_indices else "cache",
                        )
                    )
    return tuple(observations)


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
    )
    return (path, sha)


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


def build_target(row: TargetRow, output: RunnerOutput) -> tuple[Path, str]:
    checkout_path = Path(row.path)
    output.build_start(row)
    subprocess.run(
        ["cargo", "build", "--release", "-p", "egglog-experimental"],
        cwd=checkout_path,
        check=True,
        stdout=sys.stderr,
        stderr=sys.stderr,
    )
    binary_name = "egglog-experimental.exe" if os.name == "nt" else "egglog-experimental"
    binary_path = checkout_path / "target" / "release" / binary_name
    if not binary_path.is_file():
        raise FileNotFoundError(f"release binary was not produced: {binary_path}")
    binary_sha256 = sha256_file(binary_path)
    return (binary_path, binary_sha256)


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
        binary_path, binary_sha256 = build_target(row, output)
        row = replace(row, is_dirty=git_dirty(checkout_path))
        return ResolvedTarget(request=request, row=row, binary_sha256=binary_sha256, binary_path=binary_path)

    if request.source.startswith("@"):
        ref = request.source[1:]
        if not ref:
            raise ValueError(f"git target is missing a ref: {request.raw}")
        checkout_path, resolved_sha = materialize_git_ref(repo_root, ref, request.label or ref)
        row = target_row_for_request(request, checkout_path, resolved_sha)
    else:
        checkout_path, git_ref_value = resolve_path_target(request.source, invocation_cwd)
        row = target_row_for_request(request, checkout_path, git_ref_value)

    binary_path, binary_sha256 = build_target(row, output)
    row = replace(row, is_dirty=git_dirty(Path(row.path)))
    return ResolvedTarget(request=request, row=row, binary_sha256=binary_sha256, binary_path=binary_path)


def label_has_enough_rows(
    rows: DataFrame[ReportFrame],
    binary_sha256: str,
    spec: BenchmarkSpec,
) -> bool:
    for file_spec in spec.files:
        for treatment in spec.treatments:
            matches = selected_rows(
                rows,
                EstimateKey(binary_sha256, file_spec.sha256, treatment, spec.warmup_rounds, spec.timeout_sec),
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


def run_process(
    binary_path: Path,
    checkout_path: Path,
    file_spec: FileSpec,
    treatment: Treatment,
    timeout_sec: int,
) -> TimingResult:
    command = [
        str(binary_path),
        "--mode",
        "no-messages",
        "-j",
        "1",
        *treatment_flags(treatment),
        str(file_spec.absolute_path),
    ]
    env = os.environ.copy()
    env["RUST_LOG"] = "error"
    before = resource.getrusage(resource.RUSAGE_CHILDREN)
    start = time.perf_counter()
    try:
        completed = subprocess.run(
            command,
            cwd=checkout_path,
            env=env,
            text=True,
            capture_output=True,
            timeout=timeout_sec,
        )
    except subprocess.TimeoutExpired:
        return TimingResult(
            status="timed-out",
            timing=TimingRow(),
            error=ErrorRow(message=f"timed out after {timeout_sec} seconds"),
        )
    wall_sec = time.perf_counter() - start
    after = resource.getrusage(resource.RUSAGE_CHILDREN)
    timing = timing_from_usage(before, after, wall_sec)
    if completed.returncode == 0:
        return TimingResult(status="success", timing=timing, error=None)
    message = completed.stderr.strip() or completed.stdout.strip() or "process exited with non-zero status"
    return TimingResult(
        status="failure",
        timing=timing,
        error=ErrorRow(exit_code=completed.returncode, message=message[-1000:]),
    )


def timing_from_usage(
    before: resource.struct_rusage,
    after: resource.struct_rusage,
    wall_sec: float,
) -> TimingRow:
    user_sec = max(0.0, after.ru_utime - before.ru_utime)
    system_sec = max(0.0, after.ru_stime - before.ru_stime)
    cpu_wall_ratio = (user_sec + system_sec) / wall_sec if wall_sec > 0 else None
    max_rss_bytes = rss_to_bytes(after.ru_maxrss)
    return TimingRow(
        wall_sec=wall_sec,
        user_sec=user_sec,
        system_sec=system_sec,
        cpu_wall_ratio=cpu_wall_ratio,
        max_rss_bytes=max_rss_bytes,
    )


def rss_to_bytes(raw_rss: int) -> int | None:
    if raw_rss <= 0:
        return None
    if sys.platform == "darwin":
        return raw_rss
    return raw_rss * 1024


def collection_label(
    file_spec: FileSpec,
    treatment: Treatment,
    round_index: int,
    rounds: int,
) -> str:
    filename = Path(file_spec.display_path).name
    return f"{filename} {treatment} {round_index + 1}/{rounds}"


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
    table.add_column("File")
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
        table.add_row(
            cell.file.display_path,
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
        "treatment": cell.treatment,
        "warmup_rounds": spec.warmup_rounds,
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
                cell_treatment = cell.treatment
                cell_key = cell.estimate_key
                required_rounds = cell.missing_observations
                observation_number = completed_observations + 1
                label = collection_label(cell_file, cell_treatment, round_index, required_rounds)
                completed_processes = 0

                def update_progress(current: str, advance: int = 0) -> None:
                    if progress is None or process_task is None:
                        return
                    progress.update(
                        process_task,
                        advance=advance,
                        eta=format_duration_estimate(remaining_estimate(remaining_processes, estimate_model)),
                        current=current,
                    )

                def on_process_start(
                    phase: str,
                    observation_number: int = observation_number,
                ) -> None:
                    update_progress(f"row {observation_number}/{total_observations} {phase}")

                def on_process_complete(
                    phase: str,
                    process_result: TimingResult,
                    cell_key: EstimateKey = cell_key,
                    observation_number: int = observation_number,
                ) -> None:
                    nonlocal completed_processes
                    completed_processes += 1
                    estimate_model.record_process(cell_key, process_result)
                    decrement_remaining(cell_key)
                    update_progress(
                        f"row {observation_number}/{total_observations} {phase}; "
                        f"last {format_timing_result(process_result)}",
                        advance=1,
                    )

                started_at = now_iso()
                result = run_with_warmup(
                    binary_path,
                    Path(target.row.path),
                    cell_file,
                    cell_treatment,
                    spec.warmup_rounds,
                    spec.timeout_sec,
                    on_process_start,
                    on_process_complete,
                )
                skipped_processes = spec.warmup_rounds + 1 - completed_processes
                if skipped_processes > 0:
                    decrement_remaining(cell_key, skipped_processes)
                    update_progress(
                        f"row {observation_number}/{total_observations}; warmup stopped early",
                        advance=skipped_processes,
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
        transient=False,
    ) as progress:
        process_task = progress.add_task(
            "runs",
            total=planned_processes,
            eta=format_duration_estimate(remaining_estimate(remaining_processes, estimate_model)),
            current=f"rows 0/{total_observations}",
        )
        run_loop(progress, process_task)
    fresh_rows = concat_report_frames(fresh_frames)
    return CollectionResult(rows=concat_report_frames([rows, fresh_rows]), fresh_rows=fresh_rows)


def run_with_warmup(
    binary_path: Path,
    checkout_path: Path,
    file_spec: FileSpec,
    treatment: Treatment,
    warmup_rounds: int,
    timeout_sec: int,
    on_process_start: Callable[[str], None] | None = None,
    on_process_complete: Callable[[str, TimingResult], None] | None = None,
) -> TimingResult:
    for warmup_index in range(warmup_rounds):
        if on_process_start is not None:
            on_process_start(f"warmup {warmup_index + 1}/{warmup_rounds}")
        warmup = run_process(binary_path, checkout_path, file_spec, treatment, timeout_sec)
        if on_process_complete is not None:
            on_process_complete(f"warmup {warmup_index + 1}/{warmup_rounds}", warmup)
        if warmup.status != "success":
            message = "warmup did not complete successfully"
            if warmup.error is not None:
                message = f"{message}: {warmup.error.message}"
            return TimingResult(
                status=warmup.status,
                timing=TimingRow(),
                error=ErrorRow(
                    exit_code=warmup.error.exit_code if warmup.error is not None else None,
                    signal=warmup.error.signal if warmup.error is not None else None,
                    message=message,
                ),
            )
    if on_process_start is not None:
        on_process_start("timed")
    result = run_process(binary_path, checkout_path, file_spec, treatment, timeout_sec)
    if on_process_complete is not None:
        on_process_complete("timed", result)
    return result


def summarize_cell(rows: DataFrame[ReportFrame], rounds: int) -> CellSummary:
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
    samples = tuple(float(value) for value in rows.loc[rows["wall_sec"].notna(), "wall_sec"].tolist())
    if len(samples) != len(rows):
        return CellSummary(rows, (), status_counts, None, None, None, "missing wall_sec")
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
    treatments: Sequence[Treatment] | None = None,
) -> CellMap:
    chosen_treatments = spec.treatments if treatments is None else treatments
    return {
        (file_spec.sha256, treatment): summarize_cell(
            selected_rows(
                rows,
                estimate_key_for(target, file_spec, treatment, spec.warmup_rounds, spec.timeout_sec),
                spec.rounds,
            ),
            spec.rounds,
        )
        for file_spec in spec.files
        for treatment in chosen_treatments
    }


def proof_cells_from_summaries(
    cell_map: CellMap,
    spec: BenchmarkSpec,
    treatments: Sequence[Treatment] | None = None,
) -> list[tuple[CellSummary, CellSummary]]:
    chosen_treatments = spec.treatments if treatments is None else treatments
    if "off" not in chosen_treatments or "proofs" not in chosen_treatments:
        return []
    return [(cell_map[(file_spec.sha256, "off")], cell_map[(file_spec.sha256, "proofs")]) for file_spec in spec.files]


def target_proof_summary(
    rows: DataFrame[ReportFrame],
    target: ResolvedTarget,
    spec: BenchmarkSpec,
) -> RatioSummary:
    cell_map = target_cell_summaries(rows, target, spec, ("off", "proofs"))
    return suite_ratio(proof_cells_from_summaries(cell_map, spec, ("off", "proofs")))


def format_seconds(value: float | None) -> str:
    if value is None:
        return "-"
    return f"{value:.4f}s"


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


def format_ratio(value: float | None) -> str:
    if value is None:
        return "-"
    return f"{value:.3f}x"


def format_ratio_summary(summary: RatioSummary) -> str:
    return format_estimate_or_interval(summary.point, summary.ci_low, summary.ci_high, "x", 3)


def render_selected_observations(
    console: Console,
    observations: Sequence[SelectedObservation],
) -> None:
    table = Table(title="Selected observations")
    table.add_column("Target")
    table.add_column("File")
    table.add_column("Treatment")
    table.add_column("Origin")
    table.add_column("Row")
    table.add_column("Started")
    table.add_column("Status")
    table.add_column("Wall")
    for observation in observations:
        table.add_row(
            observation.target.display_label,
            observation.file.display_path,
            observation.treatment,
            observation.origin,
            str(int(observation.row["row_index"])),
            isoformat_started_at(observation.row["started_at"]),
            str(observation.row["status"]),
            format_seconds(cast(float | None, clean_optional(observation.row["wall_sec"]))),
        )
    console.print(table)


def render_report(
    console: Console,
    report_destination: ReportDestination,
    rows: DataFrame[ReportFrame],
    targets: Sequence[ResolvedTarget],
    spec: BenchmarkSpec,
    fresh_indices: set[int],
) -> None:
    console.rule("[bold]Benchmark report[/bold]")
    console.print(f"Report: [bold]{report_destination.display_path}[/bold]")
    console.print(f"Selected rows per cell: [bold]{spec.rounds}[/bold]")

    target_table = Table(title="Targets")
    target_table.add_column("Label")
    target_table.add_column("Git")
    target_table.add_column("Dirty")
    target_table.add_column("Binary")
    target_table.add_column("Path")
    for target in targets:
        target_table.add_row(
            target.display_label,
            target.row.git_sha[:12],
            "yes" if target.row.is_dirty else "no",
            target.binary_sha256.removeprefix("sha256:")[:12],
            target.row.path,
        )
    console.print(target_table)
    render_selected_observations(
        console,
        selected_observations(rows, targets, spec, fresh_indices),
    )

    for target in targets:
        cell_map = target_cell_summaries(rows, target, spec)

        means_table = Table(title=f"{target.display_label}: per-file wall time")
        means_table.add_column("File")
        for treatment in spec.treatments:
            means_table.add_column(treatment, no_wrap=True)
        means_rows: list[tuple[list[str], str]] = []
        has_mean_issues = False
        for file_spec in spec.files:
            issue_parts: list[str] = []
            row_values = [file_spec.display_path]
            for treatment in spec.treatments:
                cell = cell_map[(file_spec.sha256, treatment)]
                row_values.append(format_seconds_summary(cell))
                if cell.issue is not None:
                    issue_parts.append(f"{treatment}: {cell.issue}")
            issue_text = "; ".join(issue_parts)
            has_mean_issues = has_mean_issues or bool(issue_text)
            means_rows.append((row_values, issue_text))
        if has_mean_issues:
            means_table.add_column("Issue")
        for row_values, issue_text in means_rows:
            if has_mean_issues:
                row_values.append(issue_text)
            means_table.add_row(*row_values)
        console.print(means_table)

        ratio_columns = ratio_specs(spec.treatments)
        if ratio_columns:
            ratio_table = Table(title=f"{target.display_label}: overhead ratios")
            ratio_table.add_column("File")
            for _, _, ratio_name in ratio_columns:
                ratio_table.add_column(ratio_name, no_wrap=True)
            for file_spec in spec.files:
                row_values = [file_spec.display_path]
                for baseline_treatment, candidate_treatment, _ in ratio_columns:
                    ratio = ratio_summary(
                        cell_map[(file_spec.sha256, baseline_treatment)],
                        cell_map[(file_spec.sha256, candidate_treatment)],
                    )
                    row_values.append(format_ratio_summary(ratio))
                ratio_table.add_row(*row_values)
            console.print(ratio_table)

        proof_cells = proof_cells_from_summaries(cell_map, spec)
        if proof_cells:
            suite = suite_ratio(proof_cells)
            geometric = geometric_mean_ratio(proof_cells)
            summary_table = Table(title=f"{target.display_label}: suite summary")
            summary_table.add_column("Metric")
            summary_table.add_column("Estimate", no_wrap=True)
            summary_table.add_row(
                "total suite time ratio (proofs/off, gate)",
                format_ratio_summary(suite),
            )
            summary_table.add_row(
                "equal-file geometric mean ratio (proofs/off)",
                format_ratio_summary(geometric),
            )
            console.print(summary_table)

    if len(targets) > 1:
        render_multi_target_summary(console, rows, targets, spec)


def ratio_specs(treatments: Sequence[Treatment]) -> tuple[tuple[Treatment, Treatment, str], ...]:
    specs: list[tuple[Treatment, Treatment, str]] = []
    if "off" in treatments and "term" in treatments:
        specs.append(("off", "term", "term/off"))
    if "off" in treatments and "proofs" in treatments:
        specs.append(("off", "proofs", "proofs/off"))
    if "term" in treatments and "proofs" in treatments:
        specs.append(("term", "proofs", "proofs/term"))
    return tuple(specs)


def render_multi_target_summary(
    console: Console,
    rows: DataFrame[ReportFrame],
    targets: Sequence[ResolvedTarget],
    spec: BenchmarkSpec,
) -> None:
    if "off" not in spec.treatments or "proofs" not in spec.treatments:
        return

    proof_summaries = [(target, target_proof_summary(rows, target, spec)) for target in targets]

    baseline_target, baseline_summary = proof_summaries[0]
    table = Table(title="Target comparison")
    table.add_column("Target")
    table.add_column("suite proofs/off")
    table.add_column(f"change vs {baseline_target.display_label}")
    for target, summary in proof_summaries:
        if target == baseline_target or not summary.ok or not baseline_summary.ok:
            change = "-"
        else:
            assert summary.point is not None
            assert baseline_summary.point is not None
            change = format_ratio(summary.point / baseline_summary.point)
        table.add_row(target.display_label, format_ratio(summary.point), change)
    console.print(table)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    output = RunnerOutput()
    try:
        script_root = Path(__file__).resolve().parent
        treatments = parse_treatments(args.treatments)
        invocation_cwd = Path.cwd()
        repo_root = git_root_for_path(script_root)
        report_destination = resolve_report_destination(args.report, invocation_cwd)
        files = resolve_files(args.files, invocation_cwd)
        spec = BenchmarkSpec(
            files=files,
            treatments=treatments,
            rounds=args.rounds,
            warmup_rounds=args.warmup,
            timeout_sec=args.timeout_sec,
        )
        target_specs = args.target if args.target is not None else ["."]
        target_requests = tuple(parse_target(raw) for raw in target_specs)
        rows = load_report(report_destination)
        estimate_model = EstimateModel.from_rows(rows)
        fresh_indices: set[int] = set()
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
            fresh_indices.update(int(value) for value in collection.fresh_rows["row_index"].tolist())
        render_report(
            output.console,
            report_destination,
            rows,
            targets,
            spec,
            fresh_indices,
        )
    except (FileNotFoundError, ValueError, subprocess.CalledProcessError) as error:
        output.print_error(error)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
