"""Plan and collect ordinary benchmark observations.

This module owns cache-aware target resolution and execution plans, subprocess
progress, same-run timing-summary capture, and construction of persisted
records. Generic target parsing, checkout materialization, builds, and command
construction belong in :mod:`benchmarking.targets`. Report loading,
compatibility gating, selection, statistics, and rendering belong in
:mod:`benchmarking.reports`.
"""

from __future__ import annotations

import json
import tempfile
from collections import Counter
from dataclasses import dataclass
from datetime import UTC, datetime
from pathlib import Path
from typing import cast

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

from .models import (
    Backend,
    BenchmarkSpec,
    EstimateKey,
    FileSpec,
    ResolvedTarget,
    Status,
    TargetRequest,
    Treatment,
    backend_cargo_features,
    benchmark_cells,
)
from .output import RunnerOutput, display_target
from .processes import TimingResult, run_command
from .reports.database import ReportDatabase
from .reports.records import (
    TIMING_SUMMARY_SCHEMA_VERSION,
    ReportRecord,
    TimingSummaryRecord,
)
from .reports.results import EstimateAggregate
from .targets import (
    build_resolved_target,
    materialize_git_ref,
    materialize_target_request,
    target_row_for_request,
    workload_command,
)

TARGET_STARTUP_WARMUP_SUBPROCESSES = 1


@dataclass(frozen=True)
class CellPlan:
    """Cached and missing observations for one benchmark result."""

    file: FileSpec
    backend: Backend
    treatment: Treatment
    required_rows: int
    cached_statuses: tuple[Status, ...]
    missing_observations: int
    estimate_key: EstimateKey

    @property
    def planned_processes(self) -> int:
        return self.missing_observations


@dataclass(frozen=True)
class CollectionPlan:
    """All benchmark results collected for one resolved target."""

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
    """Estimated known duration plus a count of processes with no estimate."""

    seconds: float | None
    unknown_processes: int


@dataclass(frozen=True)
class ProcessObservation:
    """Ordinary process result and timing summary emitted by that same process."""

    result: TimingResult
    timing_summary: TimingSummaryRecord | None


class EstimateModel:
    """Exact-cell duration estimates updated as successful runs finish."""

    def __init__(self, totals: dict[EstimateKey, tuple[int, float]] | None = None) -> None:
        self.totals = totals or {}

    @classmethod
    def from_aggregates(cls, aggregates: tuple[EstimateAggregate, ...]) -> EstimateModel:
        return cls({aggregate.key: (aggregate.sample_count, aggregate.total_wall_sec) for aggregate in aggregates})

    def process_mean(self, key: EstimateKey) -> float | None:
        aggregate = self.totals.get(key)
        if aggregate is None:
            return None
        sample_count, total_wall_sec = aggregate
        return total_wall_sec / sample_count

    def estimate_processes(self, key: EstimateKey, count: int) -> DurationEstimate:
        if count <= 0:
            return DurationEstimate(seconds=0.0, unknown_processes=0)
        mean = self.process_mean(key)
        if mean is None:
            return DurationEstimate(seconds=None, unknown_processes=count)
        return DurationEstimate(seconds=mean * count, unknown_processes=0)

    def record_process(self, key: EstimateKey, result: TimingResult) -> None:
        if result.status == "success" and result.timing.wall_sec is not None:
            sample_count, total_wall_sec = self.totals.get(key, (0, 0.0))
            self.totals[key] = (sample_count + 1, total_wall_sec + result.timing.wall_sec)


def _now_iso() -> str:
    """Return a stable UTC timestamp for one newly collected observation."""

    return datetime.now(UTC).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def build_collection_plan(
    database: ReportDatabase,
    target: ResolvedTarget,
    spec: BenchmarkSpec,
    force_run: bool,
) -> CollectionPlan:
    """Select cached observations and determine the fresh work for a target."""

    requests = tuple(
        (
            file_spec,
            cell.backend,
            cell.treatment,
            EstimateKey.for_cell(target, file_spec, cell.backend, cell.treatment, spec.timeout_sec),
        )
        for file_spec in spec.files
        for cell in benchmark_cells(spec)
    )
    selected = database.selected_statuses_for_keys(tuple(request[3] for request in requests), spec.rounds)
    cells: list[CellPlan] = []
    for file_spec, backend, treatment, estimate_key in requests:
        cached = selected[estimate_key]
        missing = spec.rounds if force_run else max(0, spec.rounds - len(cached))
        cells.append(
            CellPlan(
                file=file_spec,
                backend=backend,
                treatment=treatment,
                required_rows=spec.rounds,
                cached_statuses=cached,
                missing_observations=missing,
                estimate_key=estimate_key,
            )
        )
    return CollectionPlan(target=target, cells=tuple(cells))


def collection_plan_estimate(plan: CollectionPlan, estimate_model: EstimateModel) -> DurationEstimate:
    """Estimate all measured subprocesses in a collection plan."""

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


def resolve_target(
    request: TargetRequest,
    database: ReportDatabase,
    spec: BenchmarkSpec,
    force_run: bool,
    invocation_cwd: Path,
    repo_root: Path,
    output: RunnerOutput,
) -> ResolvedTarget:
    """Resolve a target, reusing a cache-only label when its scope is complete."""

    if request.is_label_lookup:
        assert request.label is not None
        pointer = database.find_label_pointer(request.label)
        if pointer is None:
            raise ValueError(f"no cached rows found for label {request.label!r}")
        cached_target = ResolvedTarget(
            request=request,
            row=pointer.row,
            binary_sha256=pointer.binary_sha256,
            binary_path=None,
        )
        if not force_run and label_has_enough_rows(database, pointer.binary_sha256, spec):
            return cached_target
        if pointer.row.is_dirty:
            raise ValueError(
                f"label {request.label!r} points to a dirty checkout; provide label=SOURCE to collect fresh rows"
            )
        checkout_path, resolved_sha = materialize_git_ref(repo_root, pointer.row.git_sha, request.label)
        row = target_row_for_request(request, checkout_path, resolved_sha)
        return build_resolved_target(request, row, output, "release", backend_cargo_features(spec.backends))

    row = materialize_target_request(request, invocation_cwd, repo_root)
    return build_resolved_target(request, row, output, "release", backend_cargo_features(spec.backends))


def label_has_enough_rows(database: ReportDatabase, binary_sha256: str, spec: BenchmarkSpec) -> bool:
    """Return whether every requested result has enough rows for a cached label."""

    keys = tuple(
        EstimateKey(
            binary_sha256,
            file_spec.sha256,
            cell.treatment,
            spec.timeout_sec,
            cell.backend,
            file_spec.fact_directory_sha256,
        )
        for file_spec in spec.files
        for cell in benchmark_cells(spec)
    )
    selected = database.selected_statuses_for_keys(keys, spec.rounds)
    return all(len(selected[key]) >= spec.rounds for key in keys)


def run_process(
    binary_path: Path,
    checkout_path: Path,
    file_spec: FileSpec,
    backend: Backend,
    treatment: Treatment,
    timeout_sec: int,
) -> ProcessObservation:
    """Run one measured workload and read the summary it emitted on success."""

    with tempfile.TemporaryDirectory(prefix="egglog-benchmark-") as directory:
        summary_path = Path(directory) / "timing-summary.json"
        workload = workload_command(binary_path, file_spec, backend, treatment)
        command = [workload[0], "--timing-summary", str(summary_path), *workload[1:]]
        result = run_command(command, checkout_path, timeout_sec)
        if result.status != "success":
            return ProcessObservation(result=result, timing_summary=None)
        if not summary_path.is_file():
            raise ValueError(
                "successful benchmark process did not produce --timing-summary output; "
                "the selected target does not support the required benchmark interface"
            )
        try:
            raw_summary = json.loads(summary_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as error:
            raise ValueError(f"invalid timing summary from successful benchmark process: {error}") from error
        summary = cast(TimingSummaryRecord, raw_summary)
        try:
            summary_version = summary["schema_version"]
        except (KeyError, TypeError) as error:
            raise ValueError("timing summary is missing schema_version") from error
        if summary_version != TIMING_SUMMARY_SCHEMA_VERSION:
            raise ValueError(
                "unsupported timing summary schema_version "
                f"{summary_version!r}; expected {TIMING_SUMMARY_SCHEMA_VERSION}"
            )
        return ProcessObservation(result=result, timing_summary=summary)


def run_startup_warmup(binary_path: Path, checkout_path: Path, timeout_sec: int) -> TimingResult:
    """Warm the executable and preflight the required timing-summary flag."""

    return run_command(
        [str(binary_path), "--help"],
        checkout_path,
        timeout_sec,
        required_output="--timing-summary",
    )


def preflight_collection(plan: CollectionPlan, spec: BenchmarkSpec) -> TimingResult | None:
    """Check one potentially fresh target before any timed collection begins.

    The successful result is reused as that target's single startup warmup.
    A plan that is already fully cached needs neither a binary nor a preflight.
    """

    if plan.total_missing_observations == 0:
        return None
    target = plan.target
    if target.binary_path is None:
        raise ValueError(f"target {target.display_label} needs fresh rows but has no build path")
    startup_warmup = run_startup_warmup(target.binary_path, Path(target.row.path), spec.timeout_sec)
    if startup_warmup.status != "success":
        message = f"target {target.display_label} startup warmup did not complete successfully"
        if startup_warmup.error is not None:
            message = f"{message}: {startup_warmup.error.message}"
        raise ValueError(message)
    return startup_warmup


def collection_label(
    file_spec: FileSpec,
    backend: Backend,
    treatment: Treatment,
    round_index: int,
    rounds: int,
) -> str:
    """Return a concise progress label for one measured observation."""

    filename = Path(file_spec.display_path).name
    return f"{filename} {backend}/{treatment} {round_index + 1}/{rounds}"


def format_timing_result(result: TimingResult) -> str:
    """Format one subprocess result for operational progress output."""

    if result.timing.wall_sec is None:
        return result.status
    return f"{result.status} {result.timing.wall_sec:.3f}s"


def format_duration(seconds: float | None) -> str:
    """Format an estimated duration without implying unknown precision."""

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
    """Format known and unknown parts of a collection estimate."""

    if estimate.seconds is None:
        return f"unknown ({estimate.unknown_processes} runs)"
    if estimate.unknown_processes:
        return f"{format_duration(estimate.seconds)} + {estimate.unknown_processes} unknown"
    return format_duration(estimate.seconds)


def remaining_estimate(
    remaining_processes: dict[EstimateKey, int],
    estimate_model: EstimateModel,
) -> DurationEstimate:
    """Estimate subprocesses still pending in the current target plan."""

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
    """Render cache sufficiency and exact-cell estimates to stderr."""

    total_estimate = collection_plan_estimate(plan, estimate_model)
    table = Table(title=Text(f"{plan.target.display_label}: cache and estimate plan", style="bold"))
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
        status_counts = Counter(cell.cached_statuses)
        statuses = ", ".join(f"{status}:{count}" for status, count in sorted(status_counts.items())) or "-"
        table.add_row(
            Text(cell.file.display_path),
            Text(f"{cell.backend}/{cell.treatment}"),
            Text(f"{len(cell.cached_statuses)}/{cell.required_rows}"),
            Text(str(cell.missing_observations)),
            Text(statuses),
            Text(format_duration(process_mean)),
            Text(format_duration_estimate(estimate)),
        )
    output.console.print(table)
    output.console.print(
        Text.assemble("Estimated fresh collection time: ", (format_duration_estimate(total_estimate), "bold"))
    )


def flat_report_record(
    *,
    started_at: str,
    target: ResolvedTarget,
    cell: CellPlan,
    spec: BenchmarkSpec,
    observation: ProcessObservation,
) -> ReportRecord:
    """Construct the complete persisted record for one observation."""

    result = observation.result
    return {
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
        "fact_directory_path": (str(cell.file.fact_directory) if cell.file.fact_directory is not None else None),
        "fact_directory_sha256": cell.file.fact_directory_sha256,
        "backend": cell.backend,
        "treatment": cell.treatment,
        "timeout_sec": spec.timeout_sec,
        "wall_sec": result.timing.wall_sec,
        "max_rss_bytes": result.timing.max_rss_bytes,
        "error_exit_code": result.error.exit_code if result.error is not None else None,
        "error_signal": result.error.signal if result.error is not None else None,
        "error_message": result.error.message if result.error is not None else None,
        "timing_summary": observation.timing_summary,
    }


def collect_rows(
    database: ReportDatabase,
    plan: CollectionPlan,
    spec: BenchmarkSpec,
    output: RunnerOutput,
    estimate_model: EstimateModel,
    startup_warmup: TimingResult | None,
) -> None:
    """Run and append every missing observation after successful preflight."""

    target = plan.target
    if plan.total_missing_observations == 0:
        return
    if target.binary_path is None:
        raise ValueError(f"target {target.display_label} needs fresh rows but has no build path")
    if startup_warmup is None or startup_warmup.status != "success":
        raise ValueError(f"target {target.display_label} collection was not successfully preflighted")
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
        Text.assemble(
            ("Collecting", "bold"),
            " ",
            display_target(target.row),
            f" ({total_observations} observations, {planned_processes} subprocesses)",
        )
    )
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
        nonlocal completed_observations
        for round_index in range(max_deficit):
            for cell in plan.cells:
                if round_index >= cell.missing_observations:
                    continue
                cell_key = cell.estimate_key
                observation_number = completed_observations + 1
                label = collection_label(
                    cell.file,
                    cell.backend,
                    cell.treatment,
                    round_index,
                    cell.missing_observations,
                )

                def update_progress(current: str, advance: int = 0) -> None:
                    progress.update(
                        process_task,
                        advance=advance,
                        eta=format_duration_estimate(remaining_estimate(remaining_processes, estimate_model)),
                        current=current,
                    )

                update_progress(f"row {observation_number}/{total_observations} timed")
                started_at = _now_iso()
                observation = run_process(
                    binary_path,
                    Path(target.row.path),
                    cell.file,
                    cell.backend,
                    cell.treatment,
                    spec.timeout_sec,
                )
                estimate_model.record_process(cell_key, observation.result)
                decrement_remaining(cell_key)
                update_progress(
                    "row "
                    f"{observation_number}/{total_observations} timed; "
                    f"last {format_timing_result(observation.result)}",
                    advance=1,
                )
                record = flat_report_record(
                    started_at=started_at,
                    target=target,
                    cell=cell,
                    spec=spec,
                    observation=observation,
                )
                database.append(record)
                completed_observations += 1
                progress.console.print(Text(f"  {label}: fresh {format_timing_result(observation.result)}"))
                update_progress(
                    f"rows {completed_observations}/{total_observations}; "
                    f"last {format_timing_result(observation.result)}"
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
        progress.update(
            process_task,
            advance=TARGET_STARTUP_WARMUP_SUBPROCESSES,
            current=f"startup warmup; last {format_timing_result(startup_warmup)}",
            eta=format_duration_estimate(remaining_estimate(remaining_processes, estimate_model)),
        )
        progress.console.print(Text(f"  startup warmup: {format_timing_result(startup_warmup)}"))
        run_loop(progress, process_task)
