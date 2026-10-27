"""Resolve, merge, and collect benchmark observations for every command.

This module owns cache-aware target resolution and execution plans, subprocess
progress, same-run timing-summary capture, and construction of persisted
records. Generic target parsing, checkout materialization, builds, and command
construction belong in :mod:`benchmarking.targets`. Report loading, cache
selection, statistics, and rendering belong in :mod:`benchmarking.reports`.
"""

from __future__ import annotations

import os
import tempfile
from collections import Counter
from collections.abc import Mapping
from dataclasses import dataclass, replace
from datetime import UTC, datetime, timedelta
from math import ceil, isfinite
from pathlib import Path

from rich.console import Console
from rich.progress import (
    BarColumn,
    MofNCompleteColumn,
    Progress,
    ProgressColumn,
    Task,
    TextColumn,
    TimeElapsedColumn,
)
from rich.table import Column
from rich.text import Text

from .engines import MATH_WORKLOAD_ARGUMENTS, TREATMENT_SPECS, Engine, validate_engine_workload
from .models import (
    BenchmarkEndpoint,
    DisequalityEncoding,
    EndpointRequest,
    EngineBinary,
    FileSpec,
    ResolvedTarget,
    Status,
    TargetRequest,
    TargetRow,
    Treatment,
    validate_unique_file_identities,
)
from .processes import TimingResult, run_command
from .reports.grouped import grouped_report_path, write_grouped_report
from .reports.store import (
    REPORT_SCHEMA_VERSION,
    CacheKey,
    GroupedReport,
    ReportRecord,
    ReportStore,
    TimingSummaryRecord,
    parse_timing_summary,
)
from .targets import (
    build_resolved_target,
    materialize_git_ref,
    materialize_target_request,
    target_row_for_request,
    workload_command,
)
from .workloads import require_workload_unchanged


@dataclass(frozen=True)
class BenchmarkRequest:
    """One endpoint and exactly the workloads requested from it."""

    endpoint: EndpointRequest
    files: tuple[FileSpec, ...]


@dataclass(frozen=True)
class BenchmarkRunPlan:
    """Cached and missing observations for one endpoint/file result."""

    file: FileSpec
    treatment: Treatment
    required_rows: int
    cached_statuses: tuple[Status, ...]
    missing_observations: int
    disequality_encoding: DisequalityEncoding = "nee"


@dataclass(frozen=True)
class CollectionPlan:
    """All benchmark results collected for one resolved target."""

    target: ResolvedTarget
    runs: tuple[BenchmarkRunPlan, ...]

    @property
    def total_missing_observations(self) -> int:
        return sum(run.missing_observations for run in self.runs)


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


def _now_iso() -> str:
    """Return a stable UTC timestamp for one newly collected observation."""

    return datetime.now(UTC).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def resolve_requests(
    requests: tuple[BenchmarkRequest, ...],
    store: ReportStore,
    rounds: int,
    timeout_sec: int,
    force_run: bool,
    invocation_cwd: Path,
    repo_root: Path,
    console: Console,
) -> dict[TargetRequest, ResolvedTarget]:
    """Validate exact workload scopes, then resolve and build each target once."""

    if not requests or rounds < 1 or timeout_sec < 1:
        raise ValueError("collection requires requests and positive rounds and timeout")
    endpoints_by_target: dict[TargetRequest, list[EndpointRequest]] = {}
    files_by_endpoint: dict[EndpointRequest, dict[tuple[str, str], FileSpec]] = {}
    all_files: dict[tuple[str, str], FileSpec] = {}
    for request in requests:
        if not request.files:
            raise ValueError("benchmark request requires at least one file")
        validate_unique_file_identities(request.files)
        engine = TREATMENT_SPECS[request.endpoint.treatment].engine
        physical_files = tuple(file.for_engine(engine) for file in request.files)
        validate_unique_file_identities(physical_files)
        for file in physical_files:
            validate_engine_workload(file, request.endpoint.treatment)
        endpoints = endpoints_by_target.setdefault(request.endpoint.target, [])
        if request.endpoint not in endpoints:
            endpoints.append(request.endpoint)
        selected_files = files_by_endpoint.setdefault(request.endpoint, {})
        for file in request.files:
            identity = (file.sha256, file.fact_directory_sha256)
            selected_files.setdefault(identity, file)
            all_files.setdefault(identity, file)
    return resolve_targets(
        tuple((target, tuple(endpoints)) for target, endpoints in endpoints_by_target.items()),
        store,
        tuple(all_files.values()),
        rounds,
        timeout_sec,
        force_run,
        invocation_cwd,
        repo_root,
        console,
        files_by_endpoint={endpoint: tuple(files.values()) for endpoint, files in files_by_endpoint.items()},
    )


def plan_collection(
    store: ReportStore,
    requests: tuple[BenchmarkRequest, ...],
    resolved_targets: Mapping[TargetRequest, ResolvedTarget],
    rounds: int,
    timeout_sec: int,
    force_run: bool,
) -> tuple[CollectionPlan, ...]:
    """Select each exact cache identity once, preserving scope execution order."""

    scopes: dict[tuple[ResolvedTarget, tuple[FileSpec, ...]], list[BenchmarkEndpoint]] = {}
    for request in requests:
        target = resolved_targets[request.endpoint.target]
        endpoint = BenchmarkEndpoint(target, request.endpoint.treatment, request.endpoint.disequality_encoding)
        endpoints = scopes.setdefault((target, request.files), [])
        if endpoint not in endpoints:
            endpoints.append(endpoint)

    cells: dict[CacheKey, tuple[BenchmarkEndpoint, FileSpec]] = {}
    for (_target, files), endpoints in scopes.items():
        for file in files:
            for endpoint in endpoints:
                physical_file = file.for_engine(TREATMENT_SPECS[endpoint.treatment].engine)
                key = CacheKey.for_endpoint(endpoint, file)
                cells.setdefault(key, (endpoint, physical_file))
    if not cells:
        return ()

    selected = store.selected_statuses_for_keys(tuple(cells), rounds, timeout_sec)
    runs_by_target: dict[ResolvedTarget, list[BenchmarkRunPlan]] = {}
    for key, (endpoint, file) in cells.items():
        cached = selected[key]
        missing = rounds if force_run else max(0, rounds - len(cached))
        if not force_run and any(status != "success" for status in cached):
            missing = 0
        runs_by_target.setdefault(endpoint.target, []).append(
            BenchmarkRunPlan(
                file=file,
                treatment=endpoint.treatment,
                required_rows=rounds,
                cached_statuses=cached,
                missing_observations=missing,
                disequality_encoding=key.disequality_encoding,
            )
        )
    return tuple(CollectionPlan(target, tuple(runs)) for target, runs in runs_by_target.items())


def current_label_bindings(
    requests: tuple[BenchmarkRequest, ...],
    resolved_targets: Mapping[TargetRequest, ResolvedTarget],
) -> dict[tuple[str, Engine], str]:
    """Bind only requested engines and reject ambiguous aliases before collection."""

    label_bindings: dict[tuple[str, Engine], str] = {}
    for request in requests:
        target = resolved_targets[request.endpoint.target]
        if target.row.label is None:
            continue
        identity = (target.row.label, TREATMENT_SPECS[request.endpoint.treatment].engine)
        binary_sha256 = target.binary_sha256_for(request.endpoint.treatment)
        if identity in label_bindings and label_bindings[identity] != binary_sha256:
            raise ValueError(f"label {identity[0]!r} resolves to different {identity[1]} binaries")
        label_bindings[identity] = binary_sha256
    return label_bindings


def collect(
    store: ReportStore,
    plans: tuple[CollectionPlan, ...],
    requests: tuple[BenchmarkRequest, ...],
    resolved_targets: Mapping[TargetRequest, ResolvedTarget],
    timeout_sec: int,
    console: Console,
) -> GroupedReport:
    """Preflight all targets, collect once, and refresh their current grouped labels."""

    label_bindings = current_label_bindings(requests, resolved_targets)
    complete = False
    try:
        for plan in plans:
            preflight_collection(plan, timeout_sec)
        for plan in plans:
            emit_collection_plan(console, plan)
        collect_rows(store, plans, timeout_sec, console)
        complete = True
    finally:
        try:
            grouped = store.grouped_report(label_bindings)
            write_grouped_report(grouped, grouped_report_path(store.path))
        except Exception as error:
            if complete:
                raise
            console.print(Text.assemble(("error:", "red"), " could not refresh grouped report: ", str(error)))
    return grouped


def resolve_targets(
    request_groups: tuple[tuple[TargetRequest, tuple[EndpointRequest, ...]], ...],
    store: ReportStore,
    files: tuple[FileSpec, ...],
    rounds: int,
    timeout_sec: int,
    force_run: bool,
    invocation_cwd: Path,
    repo_root: Path,
    console: Console,
    *,
    files_by_endpoint: Mapping[EndpointRequest, tuple[FileSpec, ...]] | None = None,
) -> dict[TargetRequest, ResolvedTarget]:
    """Resolve every request, then build once per canonical checkout path.

    Materializing all requests before building prevents distinct aliases for the
    same checkout from rebuilding the same executable. Each alias retains its
    own request and row provenance while sharing the executable path and hash.
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
            files_by_endpoint,
        )
        if isinstance(target, ResolvedTarget):
            resolved[request] = target
        else:
            checkout_path = Path(target.row.path).resolve()
            pending_by_checkout.setdefault(checkout_path, []).append(target)

    cargo_checkouts = {
        checkout_path
        for checkout_path, pending_targets in pending_by_checkout.items()
        if any(
            TREATMENT_SPECS[endpoint.treatment].engine in ("egglog", "egg")
            for target in pending_targets
            for endpoint in target.endpoint_requests
        )
    }
    if len(cargo_checkouts) > 1:
        configured_target_dir = Path(os.environ.get("CARGO_TARGET_DIR", "target"))
        effective_target_dirs = {
            (
                configured_target_dir if configured_target_dir.is_absolute() else checkout_path / configured_target_dir
            ).resolve()
            for checkout_path in cargo_checkouts
        }
        if len(effective_target_dirs) != len(cargo_checkouts):
            raise ValueError(
                "multiple checkouts cannot share one CARGO_TARGET_DIR during collection; "
                "build and freeze distinct endpoint binaries first"
            )

    for checkout_path, pending_targets in pending_by_checkout.items():
        git_shas = {target.row.git_sha for target in pending_targets}
        if len(git_shas) != 1:
            raise ValueError(f"target selectors resolved checkout {checkout_path} at different git commits")
        engines = tuple(
            dict.fromkeys(
                TREATMENT_SPECS[endpoint.treatment].engine
                for target in pending_targets
                for endpoint in target.endpoint_requests
            )
        )
        representative = pending_targets[0]
        built = build_resolved_target(
            representative.request,
            representative.row,
            console,
            "release",
            engines,
        )
        for target in pending_targets:
            resolved[target.request] = ResolvedTarget(
                request=target.request,
                row=replace(target.row, is_dirty=built.row.is_dirty),
                binary_sha256=built.binary_sha256,
                binary_path=built.binary_path,
                engine_binaries=built.engine_binaries,
                primary_engine=built.primary_engine,
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
    files_by_endpoint: Mapping[EndpointRequest, tuple[FileSpec, ...]] | None = None,
) -> ResolvedTarget | _PendingTarget:
    """Reuse one complete cache label or materialize a target for later build."""

    if not endpoint_requests or any(endpoint.target != request for endpoint in endpoint_requests):
        raise ValueError("target resolution requires its exact endpoint requests")
    if request.is_label_lookup:
        assert request.label is not None
        required_engines = tuple(
            dict.fromkeys(TREATMENT_SPECS[endpoint.treatment].engine for endpoint in endpoint_requests)
        )
        engine_pointers = tuple(
            (engine, store.find_label_pointer(request.label, engine)) for engine in required_engines
        )
        pointers = tuple(pointer for _engine, pointer in engine_pointers if pointer is not None)
        if len(pointers) == len(engine_pointers) and all(pointer.row == pointers[0].row for pointer in pointers):
            binaries = tuple(
                EngineBinary(engine, pointer.binary_sha256, None)
                for engine, pointer in engine_pointers
                if pointer is not None
            )
            cached_target = ResolvedTarget(
                request=request,
                row=pointers[0].row,
                binary_sha256=binaries[0].sha256,
                binary_path=None,
                engine_binaries=binaries,
                primary_engine=binaries[0].engine,
            )
            if not force_run and label_has_enough_rows(
                store,
                cached_target,
                endpoint_requests,
                files,
                rounds,
                timeout_sec,
                files_by_endpoint=files_by_endpoint,
            ):
                return cached_target
        pointer = store.find_label_pointer(request.label)
        if pointer is None:
            raise ValueError(f"no cached rows found for label {request.label!r}")
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
    target: ResolvedTarget,
    endpoint_requests: tuple[EndpointRequest, ...],
    files: tuple[FileSpec, ...],
    rounds: int,
    timeout_sec: int,
    *,
    files_by_endpoint: Mapping[EndpointRequest, tuple[FileSpec, ...]] | None = None,
) -> bool:
    """Return whether every exact endpoint/file result has enough cached rows."""

    keys = tuple(
        CacheKey(
            target.binary_sha256_for(endpoint.treatment),
            file_spec.sha256,
            endpoint.treatment,
            file_spec.fact_directory_sha256,
            endpoint.disequality_encoding,
        )
        for endpoint in endpoint_requests
        for logical_file in (files_by_endpoint[endpoint] if files_by_endpoint is not None else files)
        for file_spec in (logical_file.for_engine(TREATMENT_SPECS[endpoint.treatment].engine),)
    )
    selected = store.selected_statuses_for_keys(keys, rounds, timeout_sec)
    return all(any(status != "success" for status in selected[key]) or len(selected[key]) >= rounds for key in keys)


def run_process(
    binary_path: Path,
    checkout_path: Path,
    file_spec: FileSpec,
    treatment: Treatment,
    timeout_sec: int,
    disequality_encoding: DisequalityEncoding = "nee",
) -> ProcessObservation:
    """Run one measured workload and read the summary it emitted on success."""

    with tempfile.TemporaryDirectory(prefix="egglog-benchmark-") as directory:
        summary_path = Path(directory) / "timing-summary.json"
        workload = workload_command(binary_path, file_spec, treatment, disequality_encoding)
        if not TREATMENT_SPECS[treatment].timing_summary:
            result = run_command(workload, checkout_path, timeout_sec)
            require_workload_unchanged(file_spec)
            return ProcessObservation(result=result, timing_summary=None)
        command = [workload[0], "--timing-summary", str(summary_path), *workload[1:]]
        result = run_command(command, checkout_path, timeout_sec, native_limit=True)
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


def run_preflight(
    binary_path: Path,
    checkout_path: Path,
    timeout_sec: int,
    required_outputs: tuple[str, ...] = ("--timing-summary", "--memory-limit-bytes"),
) -> TimingResult:
    """Run one untimed ``--help`` capability preflight."""

    return run_command(
        [str(binary_path), "--help"],
        checkout_path,
        timeout_sec,
        required_output=required_outputs,
        native_limit=True,
    )


def preflight_collection(plan: CollectionPlan, timeout_sec: int) -> None:
    """Check one potentially fresh target before any timed collection begins.

    A plan that is already fully cached needs neither a binary nor a preflight.
    """

    if plan.total_missing_observations == 0:
        return
    target = plan.target
    missing = tuple(run for run in plan.runs if run.missing_observations > 0)
    for engine in dict.fromkeys(TREATMENT_SPECS[run.treatment].engine for run in missing):
        engine_runs = tuple(run for run in missing if TREATMENT_SPECS[run.treatment].engine == engine)
        binary_path = target.binary_path_for(engine_runs[0].treatment)
        if binary_path is None:
            raise ValueError(f"target {target.display_label} needs a fresh {engine} binary")
        if engine not in ("egglog", "egg"):
            continue
        required_outputs = ["--timing-summary", "--memory-limit-bytes"]
        if engine == "egglog":
            if any(run.disequality_encoding != "nee" for run in engine_runs):
                required_outputs.append("--disequality-encoding")
            required_outputs.extend(
                flag for run in engine_runs for flag in TREATMENT_SPECS[run.treatment].flags if flag.startswith("--")
            )
        else:
            required_outputs.extend(
                flag
                for run in engine_runs
                for flag in MATH_WORKLOAD_ARGUMENTS.get(run.file.sha256, ())
                if flag.startswith("--")
            )
        result = run_preflight(
            binary_path,
            Path(target.row.path),
            timeout_sec,
            tuple(dict.fromkeys(required_outputs)),
        )
        if result.status != "success":
            message = f"target {target.display_label} {engine} preflight failed"
            if result.error is not None:
                message = f"{message}: {result.error.message}"
            raise ValueError(message)


def collection_label(
    file_spec: FileSpec,
    treatment: Treatment,
    round_index: int,
    rounds: int,
    disequality_encoding: DisequalityEncoding = "nee",
) -> str:
    """Return a concise progress label for one measured observation."""

    filename = Path(file_spec.display_path).name
    encoding = f"/{disequality_encoding}" if disequality_encoding != "nee" else ""
    return f"{filename} · {treatment}{encoding} · {round_index + 1}/{rounds}"


def format_timing_result(result: TimingResult) -> str:
    """Format one subprocess result for operational progress output."""

    if result.status == "timed-out":
        return result.error.message if result.error is not None else "timed out"
    elapsed = "" if result.timing.wall_sec is None else f" after {result.timing.wall_sec:.3f}s"
    if result.status == "failure":
        detail = "" if result.error is None else f": {' '.join(result.error.message.splitlines())}"
        return f"failed{elapsed}{detail}"
    return f"succeeded{elapsed}"


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


def emit_collection_plan(console: Console, plan: CollectionPlan) -> None:
    """Render one compact cache and collection summary to stderr."""

    cached_statuses = Counter(status for run in plan.runs for status in run.cached_statuses)
    cached = cached_statuses.total()
    required = sum(run.required_rows for run in plan.runs)
    missing = plan.total_missing_observations
    cached_issues: Counter[Status] = Counter()
    for status in ("failure", "timed-out"):
        if cached_statuses[status]:
            cached_issues[status] = cached_statuses[status]
    cache_text = f"{cached}/{required} runs cached"
    if cached_issues:
        cache_text += f" ({_status_counts_text(cached_issues)})"
    action_text = "nothing to collect" if missing == 0 else f"collecting {missing} fresh"
    console.print(Text(f"{plan.target.display_label}: {cache_text} · {action_text}"))


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
    record: ReportRecord = {
        "report_schema_version": REPORT_SCHEMA_VERSION,
        "started_at": started_at,
        "status": result.status,
        "target_label": target.row.label,
        "target_source": target.row.source,
        "target_path": target.row.path,
        "target_git_ref": target.row.git_ref,
        "target_git_sha": target.row.git_sha,
        "target_is_dirty": target.row.is_dirty,
        "binary_sha256": target.binary_sha256_for(run.treatment),
        "file_path": run.file.display_path,
        "file_sha256": run.file.sha256,
        "fact_directory_path": (str(run.file.fact_directory) if run.file.fact_directory is not None else None),
        "fact_directory_sha256": run.file.fact_directory_sha256,
        "treatment": run.treatment,
        "disequality_encoding": run.disequality_encoding,
        "timeout_sec": timeout_sec,
        "wall_sec": result.timing.wall_sec,
        "max_rss_bytes": result.timing.max_rss_bytes,
        "error_exit_code": result.error.exit_code if result.error is not None else None,
        "error_signal": result.error.signal if result.error is not None else None,
        "error_message": result.error.message if result.error is not None else None,
        "timing_summary": observation.timing_summary,
    }
    if result.error is not None and result.error.memory_limit_bytes is not None:
        record["error_memory_limit_bytes"] = result.error.memory_limit_bytes
    return record


class CollectionETAColumn(ProgressColumn):
    """Estimate the whole missing plan, refining a rough one-second fallback.

    Exact successful cached/live durations predict each condition. Unseen
    conditions use the mean known duration until they finish once themselves.
    Cached work never advances the progress clock or completed counter.
    """

    def __init__(
        self, store: ReportStore, runs: tuple[tuple[ResolvedTarget, BenchmarkRunPlan], ...], timeout_sec: int
    ) -> None:
        super().__init__(table_column=Column(no_wrap=True))
        self.remaining: dict[CacheKey, int] = {}
        self.durations: dict[CacheKey, list[float]] = {}
        self.active: tuple[CacheKey, float] | None = None
        for target, run in runs:
            key = CacheKey.for_endpoint(BenchmarkEndpoint(target, run.treatment, run.disequality_encoding), run.file)
            self.remaining[key] = run.missing_observations
            self.durations[key] = [
                wall
                for row in store.latest_records(key, run.required_rows, timeout_sec)
                if row.record["status"] == "success"
                and (wall := row.record["wall_sec"]) is not None
                and isfinite(wall)
                and wall > 0
            ]

    def complete(self, key: CacheKey, result: TimingResult) -> None:
        self.remaining[key] = self.remaining[key] - 1 if result.status == "success" else 0
        wall = result.timing.wall_sec
        if result.status == "success" and wall is not None and isfinite(wall) and wall > 0:
            self.durations[key].append(wall)
        self.active = None

    def render(self, task: Task) -> Text:
        means = {key: sum(values) / len(values) for key, values in self.durations.items() if values}
        fallback = sum(means.values()) / len(means) if means else 1.0
        seconds = sum(count * means.get(key, fallback) for key, count in self.remaining.items())
        active = self.active
        if active is not None:
            key, started = active
            seconds -= min(max(0.0, (task.elapsed or 0.0) - started), means.get(key, fallback))
        return Text(f"ETA ~{timedelta(seconds=ceil(max(0.0, seconds)))}")


def collect_rows(
    store: ReportStore,
    plan: CollectionPlan | tuple[CollectionPlan, ...],
    timeout_sec: int,
    console: Console,
) -> None:
    """Run and append every missing observation after caller preflight."""

    plans = (plan,) if isinstance(plan, CollectionPlan) else plan
    runs = tuple((item.target, run) for item in plans for run in item.runs)
    total_observations = sum(run.missing_observations for _target, run in runs)
    if total_observations == 0:
        return
    max_deficit = max(run.missing_observations for _target, run in runs)
    completed_observations = 0
    result_counts: Counter[Status] = Counter()
    stopped: set[CacheKey] = set()
    estimate = CollectionETAColumn(store, runs, timeout_sec)

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
        estimate,
        console=console,
        transient=True,
        disable=not console.is_terminal,
    ) as progress:
        process_task = progress.add_task(
            "Collecting",
            total=total_observations,
            current="starting",
        )
        for round_index in range(max_deficit):
            for target, run in runs:
                key = CacheKey.for_endpoint(
                    BenchmarkEndpoint(target, run.treatment, run.disequality_encoding), run.file
                )
                if round_index >= run.missing_observations or key in stopped:
                    continue
                observation_number = completed_observations + 1
                label = collection_label(
                    run.file,
                    run.treatment,
                    round_index,
                    run.missing_observations,
                    run.disequality_encoding,
                )
                if len(plans) > 1:
                    label = f"{target.display_label} · {label}"
                estimate.active = (key, progress.tasks[0].elapsed or 0.0)
                progress.update(
                    process_task,
                    current=label,
                )
                started_at = _now_iso()
                binary_path = target.binary_path_for(run.treatment)
                if binary_path is None:
                    raise ValueError(
                        f"target {target.display_label} needs a fresh {TREATMENT_SPECS[run.treatment].engine} binary"
                    )
                observation = run_process(
                    binary_path,
                    Path(target.row.path),
                    run.file,
                    run.treatment,
                    timeout_sec,
                    run.disequality_encoding,
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
                if observation.result.stop_collection:
                    assert observation.result.error is not None
                    raise ValueError(
                        f"{observation.result.error.message}; the failed observation was retained; "
                        "collection stopped before launching another workload"
                    )
                completed_observations += 1
                result_counts[observation.result.status] += 1
                if observation.result.status != "success":
                    stopped.add(key)
                    total_observations -= run.missing_observations - round_index - 1
                estimate.complete(key, observation.result)
                progress.update(
                    process_task,
                    advance=1,
                    total=total_observations,
                    current=label,
                )
                if not console.is_terminal or observation.result.status != "success":
                    progress.console.print(
                        Text(
                            f"  [{observation_number}/{total_observations}] {label}: "
                            f"{format_timing_result(observation.result)} · {estimate.render(progress.tasks[0])}"
                        )
                    )
    target_label = plans[0].target.display_label if len(plans) == 1 else f"{len(plans)} targets"
    console.print(
        Text(f"{target_label}: collected {completed_observations} fresh runs · {_status_counts_text(result_counts)}")
    )
