"""Plan and collect ordinary benchmark observations.

This module owns cache-aware target resolution and execution plans, subprocess
progress, same-run timing-summary capture, and construction of persisted
records. Generic target parsing, checkout materialization, builds, and command
construction belong in :mod:`benchmarking.targets`. Report loading, cache
selection, statistics, and rendering belong in :mod:`benchmarking.reports`.
"""

from __future__ import annotations

import tempfile
from collections import Counter
from collections.abc import Iterable
from dataclasses import dataclass, replace
from datetime import UTC, datetime
from pathlib import Path

from rich.progress import (
    BarColumn,
    MofNCompleteColumn,
    Progress,
    TextColumn,
    TimeElapsedColumn,
)
from rich.table import Column
from rich.text import Text

from .models import (
    Backend,
    BenchmarkEndpoint,
    EndpointRequest,
    EstimateKey,
    FileSpec,
    ResolvedTarget,
    Status,
    TargetRequest,
    TargetRow,
    Treatment,
    backend_cargo_features,
)
from .output import RunnerOutput
from .processes import TimingResult, run_command
from .reports.records import (
    REPORT_SCHEMA_VERSION,
    ReportRecord,
    TimingSummaryRecord,
    parse_timing_summary,
)
from .reports.store import EstimateAggregate, ReportStore
from .targets import (
    build_resolved_target,
    materialize_git_ref,
    materialize_target_request,
    target_row_for_request,
    workload_command,
)
from .workloads import require_workload_unchanged


@dataclass(frozen=True)
class BenchmarkRunPlan:
    """Cached and missing observations for one endpoint/file result."""

    file: FileSpec
    backend: Backend
    treatment: Treatment
    required_rows: int
    cached_statuses: tuple[Status, ...]
    missing_observations: int
    estimate_key: EstimateKey


@dataclass(frozen=True)
class CollectionPlan:
    """All benchmark results collected for one resolved target."""

    target: ResolvedTarget
    runs: tuple[BenchmarkRunPlan, ...]

    @property
    def total_missing_observations(self) -> int:
        return sum(run.missing_observations for run in self.runs)


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


@dataclass(frozen=True)
class _PendingTarget:
    """One materialized target awaiting a checkout-wide feature build."""

    request: TargetRequest
    row: TargetRow
    endpoint_requests: tuple[EndpointRequest, ...]


class EstimateModel:
    """Exact-result duration estimates updated as successful runs finish."""

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
    store: ReportStore,
    target: ResolvedTarget,
    endpoints: tuple[BenchmarkEndpoint, ...],
    files: tuple[FileSpec, ...],
    rounds: int,
    timeout_sec: int,
    force_run: bool,
) -> CollectionPlan:
    """Select cached observations for the exact endpoints using this binary."""

    endpoint_by_identity = {endpoint.cache_identity: endpoint for endpoint in endpoints}
    if len(endpoint_by_identity) != len(endpoints):
        raise ValueError("collection endpoints must not contain duplicate cache identities")
    if any(endpoint.target != target for endpoint in endpoints):
        raise ValueError("collection endpoints must use the plan target")

    requests = tuple(
        (
            file_spec,
            endpoint.backend,
            endpoint.treatment,
            EstimateKey.for_endpoint(endpoint, file_spec, timeout_sec),
        )
        for file_spec in files
        for endpoint in endpoints
    )
    selected = store.selected_statuses_for_keys(tuple(request[3] for request in requests), rounds)
    runs: list[BenchmarkRunPlan] = []
    for file_spec, backend, treatment, estimate_key in requests:
        cached = selected[estimate_key]
        missing = rounds if force_run else max(0, rounds - len(cached))
        runs.append(
            BenchmarkRunPlan(
                file=file_spec,
                backend=backend,
                treatment=treatment,
                required_rows=rounds,
                cached_statuses=cached,
                missing_observations=missing,
                estimate_key=estimate_key,
            )
        )
    return CollectionPlan(target=target, runs=tuple(runs))


def collection_plan_estimate(plan: CollectionPlan, estimate_model: EstimateModel) -> DurationEstimate:
    """Estimate all measured subprocesses in a collection plan."""

    return _combined_estimate(
        ((run.estimate_key, run.missing_observations) for run in plan.runs),
        estimate_model,
    )


def _combined_estimate(
    processes: Iterable[tuple[EstimateKey, int]],
    estimate_model: EstimateModel,
) -> DurationEstimate:
    """Combine exact-key estimates without hiding how unknown runs propagate."""

    seconds = 0.0
    unknown_processes = 0
    for key, count in processes:
        estimate = estimate_model.estimate_processes(key, count)
        if estimate.seconds is None:
            unknown_processes += estimate.unknown_processes
        else:
            seconds += estimate.seconds
    if seconds == 0.0 and unknown_processes:
        return DurationEstimate(seconds=None, unknown_processes=unknown_processes)
    return DurationEstimate(seconds=seconds, unknown_processes=unknown_processes)


def resolve_targets(
    request_groups: tuple[tuple[TargetRequest, tuple[EndpointRequest, ...]], ...],
    store: ReportStore,
    files: tuple[FileSpec, ...],
    rounds: int,
    timeout_sec: int,
    force_run: bool,
    invocation_cwd: Path,
    repo_root: Path,
    output: RunnerOutput,
) -> dict[TargetRequest, ResolvedTarget]:
    """Resolve every request, then build once per canonical checkout path.

    Materializing all requests before building prevents distinct aliases for the
    same checkout from overwriting one another's feature-specific executable.
    Each alias retains its own request and row provenance while sharing the
    executable path and hash produced from the union of required backends.
    """

    resolved: dict[TargetRequest, ResolvedTarget] = {}
    pending_by_checkout: dict[Path, list[_PendingTarget]] = {}
    for request, endpoint_requests in request_groups:
        target = _resolve_or_materialize_target(
            request,
            store,
            endpoint_requests,
            files,
            rounds,
            timeout_sec,
            force_run,
            invocation_cwd,
            repo_root,
        )
        if isinstance(target, ResolvedTarget):
            resolved[request] = target
        else:
            checkout_path = Path(target.row.path).resolve()
            pending_by_checkout.setdefault(checkout_path, []).append(target)

    for checkout_path, pending_targets in pending_by_checkout.items():
        git_shas = {target.row.git_sha for target in pending_targets}
        if len(git_shas) != 1:
            raise ValueError(f"target selectors resolved checkout {checkout_path} at different git commits")
        backends = tuple(endpoint.backend for target in pending_targets for endpoint in target.endpoint_requests)
        representative = pending_targets[0]
        built = build_resolved_target(
            representative.request,
            representative.row,
            output,
            "release",
            backend_cargo_features(backends),
        )
        for target in pending_targets:
            resolved[target.request] = ResolvedTarget(
                request=target.request,
                row=replace(target.row, is_dirty=built.row.is_dirty),
                binary_sha256=built.binary_sha256,
                binary_path=built.binary_path,
            )

    return {request: resolved[request] for request, _endpoint_requests in request_groups}


def _resolve_or_materialize_target(
    request: TargetRequest,
    store: ReportStore,
    endpoint_requests: tuple[EndpointRequest, ...],
    files: tuple[FileSpec, ...],
    rounds: int,
    timeout_sec: int,
    force_run: bool,
    invocation_cwd: Path,
    repo_root: Path,
) -> ResolvedTarget | _PendingTarget:
    """Reuse one complete cache label or materialize a target for later build."""

    if not endpoint_requests or any(endpoint.target != request for endpoint in endpoint_requests):
        raise ValueError("target resolution requires its exact endpoint requests")
    if request.is_label_lookup:
        assert request.label is not None
        pointer = store.find_label_pointer(request.label)
        if pointer is None:
            raise ValueError(f"no cached rows found for label {request.label!r}")
        cached_target = ResolvedTarget(
            request=request,
            row=pointer.row,
            binary_sha256=pointer.binary_sha256,
            binary_path=None,
        )
        if not force_run and label_has_enough_rows(
            store,
            pointer.binary_sha256,
            endpoint_requests,
            files,
            rounds,
            timeout_sec,
        ):
            return cached_target
        if pointer.row.is_dirty:
            raise ValueError(
                f"label {request.label!r} points to a dirty checkout; provide label=SOURCE to collect fresh rows"
            )
        checkout_path, resolved_sha = materialize_git_ref(repo_root, pointer.row.git_sha, request.label)
        row = target_row_for_request(request, checkout_path, resolved_sha)
        return _PendingTarget(request, row, endpoint_requests)

    row = materialize_target_request(request, invocation_cwd, repo_root)
    return _PendingTarget(request, row, endpoint_requests)


def label_has_enough_rows(
    store: ReportStore,
    binary_sha256: str,
    endpoint_requests: tuple[EndpointRequest, ...],
    files: tuple[FileSpec, ...],
    rounds: int,
    timeout_sec: int,
) -> bool:
    """Return whether every exact endpoint/file result has enough cached rows."""

    keys = tuple(
        EstimateKey(
            binary_sha256,
            file_spec.sha256,
            endpoint.treatment,
            timeout_sec,
            endpoint.backend,
            file_spec.fact_directory_sha256,
        )
        for file_spec in files
        for endpoint in endpoint_requests
    )
    selected = store.selected_statuses_for_keys(keys, rounds)
    return all(len(selected[key]) >= rounds for key in keys)


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
        require_workload_unchanged(file_spec)
        if result.status != "success":
            return ProcessObservation(result=result, timing_summary=None)
        if not summary_path.is_file():
            raise ValueError(
                "successful benchmark process did not produce --timing-summary output; "
                "the selected target does not support the required benchmark interface"
            )
        try:
            summary = parse_timing_summary(summary_path.read_bytes())
        except (OSError, ValueError, KeyError, TypeError) as error:
            raise ValueError(f"invalid timing summary from successful benchmark process: {error}") from error
        return ProcessObservation(result=result, timing_summary=summary)


def run_preflight(binary_path: Path, checkout_path: Path, timeout_sec: int) -> TimingResult:
    """Run an untimed ``--help`` capability preflight for the timing-summary interface."""

    return run_command(
        [str(binary_path), "--help"],
        checkout_path,
        timeout_sec,
        required_output="--timing-summary",
    )


def preflight_collection(plan: CollectionPlan, timeout_sec: int) -> None:
    """Check one potentially fresh target before any timed collection begins.

    A plan that is already fully cached needs neither a binary nor a preflight.
    """

    if plan.total_missing_observations == 0:
        return
    target = plan.target
    if target.binary_path is None:
        raise ValueError(f"target {target.display_label} needs fresh rows but has no build path")
    result = run_preflight(target.binary_path, Path(target.row.path), timeout_sec)
    if result.status != "success":
        message = f"target {target.display_label} preflight failed"
        if result.error is not None:
            message = f"{message}: {result.error.message}"
        raise ValueError(message)


def collection_label(
    file_spec: FileSpec,
    backend: Backend,
    treatment: Treatment,
    round_index: int,
    rounds: int,
) -> str:
    """Return a concise progress label for one measured observation."""

    filename = Path(file_spec.display_path).name
    return f"{filename} · {backend}/{treatment} · {round_index + 1}/{rounds}"


def format_timing_result(result: TimingResult) -> str:
    """Format one subprocess result for operational progress output."""

    if result.status == "timed-out":
        return result.error.message if result.error is not None else "timed out"
    elapsed = "" if result.timing.wall_sec is None else f" after {result.timing.wall_sec:.3f}s"
    if result.status == "failure":
        detail = "" if result.error is None else f": {' '.join(result.error.message.splitlines())}"
        return f"failed{elapsed}{detail}"
    return f"succeeded{elapsed}"


def format_duration(seconds: float | None) -> str:
    """Format one coarse planning duration without benchmark-like precision."""

    if seconds is None:
        return "unknown"
    if seconds < 1:
        return "<1s"
    rounded_seconds = round(seconds)
    if rounded_seconds < 60:
        return f"~{rounded_seconds}s"
    minutes, remainder = divmod(rounded_seconds, 60)
    if minutes < 60:
        return f"~{minutes}m{remainder:02d}s"
    hours, minutes = divmod(minutes, 60)
    return f"~{hours}h{minutes:02d}m"


def format_duration_estimate(estimate: DurationEstimate) -> str:
    """Format known and unknown parts of a collection estimate."""

    if estimate.seconds is None:
        return f"unknown ({_run_count(estimate.unknown_processes, 'unestimated run')})"
    if estimate.unknown_processes:
        if estimate.seconds < 1:
            lower_bound = f"{estimate.seconds:.1f}s"
        else:
            lower_bound = format_duration(estimate.seconds).removeprefix("~")
        return f"at least {lower_bound}; {_run_count(estimate.unknown_processes, 'unestimated run')}"
    return format_duration(estimate.seconds)


def _format_progress_estimate(estimate: DurationEstimate) -> str:
    """Keep the live ETA honest without crowding out the current workload."""

    if estimate.seconds is None:
        return "unknown"
    if estimate.unknown_processes:
        known = format_duration(estimate.seconds).removeprefix("~")
        return f"≥{known} ({estimate.unknown_processes} unknown)"
    return format_duration(estimate.seconds)


def _run_count(count: int, singular: str) -> str:
    """Pluralize one operational run count."""

    return f"{count} {singular if count == 1 else singular + 's'}"


def _status_counts_text(status_counts: Counter[Status]) -> str:
    """Format result counts in stable, natural-language order."""

    parts: list[str] = []
    if status_counts["success"]:
        parts.append(f"{status_counts['success']} successful")
    if status_counts["failure"]:
        parts.append(f"{status_counts['failure']} failed")
    if status_counts["timed-out"]:
        parts.append(f"{status_counts['timed-out']} timed out")
    return ", ".join(parts)


def remaining_estimate(
    remaining_processes: dict[EstimateKey, int],
    estimate_model: EstimateModel,
) -> DurationEstimate:
    """Estimate subprocesses still pending in the current target plan."""

    return _combined_estimate(remaining_processes.items(), estimate_model)


def emit_collection_plan(
    output: RunnerOutput,
    plan: CollectionPlan,
    estimate_model: EstimateModel,
) -> None:
    """Render one compact cache and collection summary to stderr."""

    cached_statuses = Counter(status for run in plan.runs for status in run.cached_statuses)
    cached = cached_statuses.total()
    required = sum(run.required_rows for run in plan.runs)
    missing = plan.total_missing_observations
    total_estimate = collection_plan_estimate(plan, estimate_model)
    cached_issues: Counter[Status] = Counter()
    for status in ("failure", "timed-out"):
        if cached_statuses[status]:
            cached_issues[status] = cached_statuses[status]
    cache_text = f"{cached}/{required} runs cached"
    if cached_issues:
        cache_text += f" ({_status_counts_text(cached_issues)})"
    action_text = (
        "nothing to collect"
        if missing == 0
        else f"collecting {missing} fresh · ETA {format_duration_estimate(total_estimate)}"
    )
    output.console.print(Text(f"{plan.target.display_label}: {cache_text} · {action_text}"))


def flat_report_record(
    *,
    started_at: str,
    target: ResolvedTarget,
    run: BenchmarkRunPlan,
    timeout_sec: int,
    observation: ProcessObservation,
) -> ReportRecord:
    """Construct the complete persisted record for one observation."""

    result = observation.result
    return {
        "report_schema_version": REPORT_SCHEMA_VERSION,
        "started_at": started_at,
        "status": result.status,
        "target_label": target.row.label,
        "target_source": target.row.source,
        "target_path": target.row.path,
        "target_git_ref": target.row.git_ref,
        "target_git_sha": target.row.git_sha,
        "target_is_dirty": target.row.is_dirty,
        "binary_sha256": target.binary_sha256,
        "file_path": run.file.display_path,
        "file_sha256": run.file.sha256,
        "fact_directory_path": (str(run.file.fact_directory) if run.file.fact_directory is not None else None),
        "fact_directory_sha256": run.file.fact_directory_sha256,
        "backend": run.backend,
        "treatment": run.treatment,
        "timeout_sec": timeout_sec,
        "wall_sec": result.timing.wall_sec,
        "max_rss_bytes": result.timing.max_rss_bytes,
        "error_exit_code": result.error.exit_code if result.error is not None else None,
        "error_signal": result.error.signal if result.error is not None else None,
        "error_message": result.error.message if result.error is not None else None,
        "timing_summary": observation.timing_summary,
    }


def collect_rows(
    store: ReportStore,
    plan: CollectionPlan,
    timeout_sec: int,
    output: RunnerOutput,
    estimate_model: EstimateModel,
) -> None:
    """Run and append every missing observation after caller preflight."""

    target = plan.target
    if plan.total_missing_observations == 0:
        return
    if target.binary_path is None:
        raise ValueError(f"target {target.display_label} needs fresh rows but has no build path")
    binary_path = target.binary_path
    total_observations = plan.total_missing_observations
    remaining_processes: dict[EstimateKey, int] = {}
    for run in plan.runs:
        if run.missing_observations > 0:
            remaining_processes[run.estimate_key] = (
                remaining_processes.get(run.estimate_key, 0) + run.missing_observations
            )
    max_deficit = max(run.missing_observations for run in plan.runs)
    completed_observations = 0
    result_counts: Counter[Status] = Counter()

    with Progress(
        TextColumn(
            "{task.fields[current]}",
            table_column=Column(ratio=1, no_wrap=True, overflow="ellipsis"),
        ),
        BarColumn(
            bar_width=10,
            complete_style="cyan",
            finished_style="cyan",
            pulse_style="cyan",
            table_column=Column(no_wrap=True),
        ),
        MofNCompleteColumn(table_column=Column(no_wrap=True)),
        TimeElapsedColumn(table_column=Column(no_wrap=True)),
        TextColumn("ETA {task.fields[eta]}", table_column=Column(no_wrap=True)),
        console=output.console,
        transient=True,
        disable=not output.console.is_terminal,
    ) as progress:
        process_task = progress.add_task(
            "Collecting",
            total=total_observations,
            eta=_format_progress_estimate(remaining_estimate(remaining_processes, estimate_model)),
            current="starting",
        )
        for round_index in range(max_deficit):
            for run in plan.runs:
                if round_index >= run.missing_observations:
                    continue
                run_key = run.estimate_key
                observation_number = completed_observations + 1
                label = collection_label(
                    run.file,
                    run.backend,
                    run.treatment,
                    round_index,
                    run.missing_observations,
                )
                progress.update(
                    process_task,
                    eta=_format_progress_estimate(remaining_estimate(remaining_processes, estimate_model)),
                    current=label,
                )
                started_at = _now_iso()
                observation = run_process(
                    binary_path,
                    Path(target.row.path),
                    run.file,
                    run.backend,
                    run.treatment,
                    timeout_sec,
                )
                store.append(
                    flat_report_record(
                        started_at=started_at,
                        target=target,
                        run=run,
                        timeout_sec=timeout_sec,
                        observation=observation,
                    )
                )
                estimate_model.record_process(run_key, observation.result)
                remaining_for_key = remaining_processes[run_key] - 1
                if remaining_for_key:
                    remaining_processes[run_key] = remaining_for_key
                else:
                    del remaining_processes[run_key]
                completed_observations += 1
                result_counts[observation.result.status] += 1
                progress.update(
                    process_task,
                    advance=1,
                    eta=_format_progress_estimate(remaining_estimate(remaining_processes, estimate_model)),
                    current=label,
                )
                if not output.console.is_terminal or observation.result.status != "success":
                    progress.console.print(
                        Text(
                            f"  [{observation_number}/{total_observations}] {label}: "
                            f"{format_timing_result(observation.result)}"
                        )
                    )
    output.console.print(
        Text(
            f"{target.display_label}: collected {total_observations} fresh runs · {_status_counts_text(result_counts)}"
        )
    )
