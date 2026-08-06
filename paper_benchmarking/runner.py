"""Compose deterministic run manifests and execute adapter-defined process lanes."""

from __future__ import annotations

import csv
import io
import math
import os
from collections.abc import Callable, Mapping, Sequence
from dataclasses import dataclass, replace
from datetime import UTC, datetime
from pathlib import Path

from .artifact import ArtifactCache, verify_artifact_cache
from .models import CommandSpec, Evaluation, Preset, ProcessLane, ProcessOutcome, ProcessPhase
from .processes import ProcessExecutor, SubprocessExecutor
from .provenance import (
    collect_machine_context,
    collect_repository_context,
    command_environment_record,
    command_record,
    effective_environment,
    executable_record,
    invocation_environment,
    isoformat_utc,
    lane_input_records,
    runtime_provenance_record,
)
from .results import ResultStore, render_markdown_summary

RUN_MANIFEST_SCHEMA_VERSION = 1
RUN_RECORD_SCHEMA_VERSION = 1


@dataclass(frozen=True)
class RunResult:
    """Completed lane-run artifact and command exit status."""

    result_dir: Path
    summary: str
    success: bool
    infrastructure_error: bool


def build_run_manifest(
    *,
    run_id: str,
    preset: Preset,
    evaluations: Sequence[Evaluation],
    lanes: Sequence[ProcessLane],
    artifact: ArtifactCache,
    invocation_argv: Sequence[str],
    invocation_cwd: Path,
    environment: Mapping[str, str],
    created_at: datetime,
    machine: Mapping[str, object],
    repository: Mapping[str, object],
) -> dict[str, object]:
    """Build the immutable run plan from fully injected provenance values."""

    lane_records: list[dict[str, object]] = []
    for lane in lanes:
        lane_records.append(
            {
                "build": [command_record(command, environment) for command in lane.build],
                "evaluation": lane.evaluation,
                "inputs": lane_input_records(lane),
                "name": lane.name,
                "observations": [command_record(command, environment) for command in lane.observations],
                "prepare": [command_record(command, environment) for command in lane.prepare],
                "validate": [command_record(command, environment) for command in lane.validate],
                "versions": dict(lane.versions),
            }
        )
    return {
        "artifact": artifact.to_record(),
        "created_at": isoformat_utc(created_at),
        "invocation": {
            "argv": list(invocation_argv),
            "cwd": str(invocation_cwd.resolve(strict=False)),
            "env": invocation_environment(environment),
        },
        "lanes": lane_records,
        "machine": dict(machine),
        "repository": dict(repository),
        "run_id": run_id,
        "schema_version": RUN_MANIFEST_SCHEMA_VERSION,
        "selection": {"evaluations": list(evaluations), "preset": preset},
        "versions": {
            "harness_schema_version": RUN_MANIFEST_SCHEMA_VERSION,
            "python": machine.get("python_version"),
        },
    }


def run_lanes(
    lanes: Sequence[ProcessLane],
    *,
    run_id: str,
    preset: Preset,
    evaluations: Sequence[Evaluation],
    artifact: ArtifactCache,
    results_root: Path,
    invocation_argv: Sequence[str],
    invocation_cwd: Path,
    repo_root: Path,
    executor: ProcessExecutor | None = None,
    environment: Mapping[str, str] | None = None,
    created_at: datetime | None = None,
    machine: Mapping[str, object] | None = None,
    repository: Mapping[str, object] | None = None,
    report: Callable[[str], None] | None = None,
) -> RunResult:
    """Run hooks and observations in lane order and persist every outcome."""

    if not lanes:
        raise ValueError("paper benchmark run requires at least one process lane")
    _validate_lane_selection(lanes, evaluations)
    _validate_paths(lanes, artifact, repo_root, results_root)
    base_environment = dict(os.environ if environment is None else environment)
    started_at = created_at or datetime.now(UTC)
    machine_record = dict(machine) if machine is not None else collect_machine_context()
    repository_record = dict(repository) if repository is not None else collect_repository_context(repo_root)
    manifest = build_run_manifest(
        run_id=run_id,
        preset=preset,
        evaluations=evaluations,
        lanes=lanes,
        artifact=artifact,
        invocation_argv=invocation_argv,
        invocation_cwd=invocation_cwd,
        environment=base_environment,
        created_at=started_at,
        machine=machine_record,
        repository=repository_record,
    )
    store = ResultStore.create(results_root, run_id)
    store.write_manifest(manifest)
    store.write_status("running")
    process_executor = executor or SubprocessExecutor()
    emit = report or (lambda _message: None)
    records: list[dict[str, object]] = []
    sequence = 1

    input_snapshots = {(lane.evaluation, lane.name): lane_input_records(lane) for lane in lanes}
    try:
        for lane in lanes:
            emit(f"Running {lane.evaluation}/{lane.name} build and preparation")
            hooks_succeeded = True
            hook_groups: tuple[tuple[ProcessPhase, tuple[CommandSpec, ...]], ...] = (
                ("build", lane.build),
                ("prepare", lane.prepare),
            )
            for phase, commands in hook_groups:
                for command in commands:
                    record = _run_process(
                        store,
                        process_executor,
                        lane,
                        command,
                        phase,
                        None,
                        sequence,
                        base_environment,
                    )
                    sequence += 1
                    records.append(record)
                    store.append(record)
                    if record["status"] != "success":
                        hooks_succeeded = False
                        break
                if not hooks_succeeded:
                    break
            if not hooks_succeeded:
                emit(f"Skipping timed observations for {lane.evaluation}/{lane.name} after hook failure")
                continue

            expected_inputs = input_snapshots[(lane.evaluation, lane.name)]
            for round_number, command in enumerate(lane.observations, start=1):
                if lane_input_records(lane) != expected_inputs:
                    raise ValueError(f"paper lane inputs changed before {lane.evaluation}/{lane.name} observation")
                emit(f"Running {lane.evaluation}/{lane.name} observation {round_number}/{len(lane.observations)}")
                record = _run_process(
                    store,
                    process_executor,
                    lane,
                    command,
                    "observation",
                    round_number,
                    sequence,
                    base_environment,
                )
                sequence += 1
                records.append(record)
                store.append(record)

            for command in lane.validate:
                if lane_input_records(lane) != expected_inputs:
                    raise ValueError(f"paper lane inputs changed before {lane.evaluation}/{lane.name} validation")
                emit(f"Validating {lane.evaluation}/{lane.name} after timed observations")
                record = _run_process(
                    store,
                    process_executor,
                    lane,
                    command,
                    "validate",
                    None,
                    sequence,
                    base_environment,
                )
                sequence += 1
                records.append(record)
                store.append(record)

        verify_artifact_cache(artifact.root, expected_sha256=artifact.archive_sha256)
        summary = render_markdown_summary(manifest, records)
        store.write_summary(summary)
        success = bool(records) and all(record["status"] == "success" for record in records)
        infrastructure_error = any(record["status"] == "infrastructure-error" for record in records)
        store.write_status("completed", success=success)
    except BaseException as error:
        store.write_status("failed", success=False, error=str(error))
        raise
    emit(f"Paper results: {store.path}")
    return RunResult(store.path, summary, success, infrastructure_error)


def _run_process(
    store: ResultStore,
    executor: ProcessExecutor,
    lane: ProcessLane,
    command: CommandSpec,
    phase: ProcessPhase,
    round_number: int | None,
    sequence: int,
    base_environment: Mapping[str, str],
) -> dict[str, object]:
    log_stem = f"{sequence:04d}-{lane.evaluation}-{lane.name}-{phase}-{command.label}"
    stdout_path = store.logs_path / f"{log_stem}.stdout.log"
    stderr_path = store.logs_path / f"{log_stem}.stderr.log"
    stdout_path.touch(exist_ok=False)
    stderr_path.touch(exist_ok=False)
    environment = effective_environment(command, base_environment)
    executable = executable_record(command, environment)
    try:
        runtime = runtime_provenance_record(command, environment)
    except (OSError, ValueError) as error:
        timestamp = isoformat_utc(datetime.now(UTC))
        stderr_path.write_text(f"{error}\n", encoding="utf-8")
        runtime = {"artifacts": [], "error": str(error), "executables": []}
        outcome = ProcessOutcome(
            status="infrastructure-error",
            started_at=timestamp,
            finished_at=timestamp,
            wall_sec=None,
            error_message=str(error),
        )
    else:
        outcome = executor.run(
            command,
            environment=environment,
            stdout_path=stdout_path,
            stderr_path=stderr_path,
        )
    if outcome.status == "success":
        mismatch = _output_mismatch(command, stdout_path, stderr_path)
        if mismatch is not None:
            outcome = replace(outcome, status="failure", exit_code=0, error_message=mismatch)
    _validate_outcome(outcome)
    return {
        "argv": list(command.argv),
        "command_label": command.label,
        "cwd": str(command.cwd.resolve(strict=False)),
        "env": command_environment_record(command, base_environment),
        "error_message": outcome.error_message,
        "evaluation": lane.evaluation,
        "executable": executable,
        "exit_code": outcome.exit_code,
        "finished_at": outcome.finished_at,
        "lane": lane.name,
        "phase": phase,
        "round": round_number,
        "runtime": runtime,
        "run_id": store.run_id,
        "schema_version": RUN_RECORD_SCHEMA_VERSION,
        "sequence": sequence,
        "signal": outcome.signal,
        "started_at": outcome.started_at,
        "status": outcome.status,
        "stderr_log": str(stderr_path.relative_to(store.path)),
        "stdout_log": str(stdout_path.relative_to(store.path)),
        "timeout_sec": command.timeout_sec,
        "wall_sec": outcome.wall_sec,
    }


def _validate_outcome(outcome: ProcessOutcome) -> None:
    finite_wall = outcome.wall_sec is not None and math.isfinite(outcome.wall_sec) and outcome.wall_sec >= 0
    if outcome.status == "success":
        if not finite_wall or any(
            value is not None for value in (outcome.exit_code, outcome.signal, outcome.error_message)
        ):
            raise ValueError("successful paper process has contradictory outcome fields")
    elif outcome.status == "failure":
        if not finite_wall or (outcome.exit_code is None) == (outcome.signal is None):
            raise ValueError("failed paper process must have finite timing and exactly one termination code")
        if not outcome.error_message:
            raise ValueError("failed paper process is missing an error message")
    elif outcome.status in {"timed-out", "infrastructure-error"}:
        if outcome.wall_sec is not None or outcome.exit_code is not None or outcome.signal is not None:
            raise ValueError(f"{outcome.status} paper process must not become a timing sample")
        if not outcome.error_message:
            raise ValueError(f"{outcome.status} paper process is missing an error message")


def _output_mismatch(command: CommandSpec, stdout_path: Path, stderr_path: Path) -> str | None:
    del stderr_path
    stdout = stdout_path.read_text(encoding="utf-8", errors="replace")
    stdout_lines = tuple(stdout.splitlines())
    if command.expected_stdout_csv_record is not None:
        if not stdout_lines:
            return "stdout did not contain an artifact CSV record"
        try:
            rows = list(csv.reader(io.StringIO(stdout_lines[-1]), strict=True))
        except csv.Error as error:
            return f"stdout was not valid CSV: {error}"
        if len(rows) != 1 or len(rows[0]) != 4:
            return "stdout did not contain exactly one four-field artifact CSV record"
        benchmark, engine, duration_text, size_text = rows[0]
        try:
            duration_ns = int(duration_text)
            size = int(size_text)
        except ValueError:
            return "stdout artifact CSV duration or size was not an integer"
        expected_benchmark, expected_engine, expected_size = command.expected_stdout_csv_record
        if duration_ns < 0 or (benchmark, engine, size) != (
            expected_benchmark,
            expected_engine,
            expected_size,
        ):
            return "stdout artifact CSV record did not match the exact lane oracle"
        stdout_lines = stdout_lines[:-1]
    if command.expected_stdout_lines is not None and stdout_lines != command.expected_stdout_lines:
        return "stdout did not exactly match the adapter's expected lines"
    return None


def _validate_lane_selection(lanes: Sequence[ProcessLane], evaluations: Sequence[Evaluation]) -> None:
    if not evaluations or len(set(evaluations)) != len(evaluations):
        raise ValueError("paper benchmark evaluations must be nonempty and unique")
    selected = set(evaluations)
    lane_evaluations = {lane.evaluation for lane in lanes}
    if lane_evaluations != selected:
        raise ValueError(
            "paper process lanes do not match selected evaluations: "
            f"selected={','.join(evaluations)} lanes={','.join(sorted(lane_evaluations))}"
        )
    identities = [(lane.evaluation, lane.name) for lane in lanes]
    if len(set(identities)) != len(identities):
        raise ValueError("paper benchmark process lanes must have unique evaluation/name identities")


def _validate_paths(
    lanes: Sequence[ProcessLane],
    artifact: ArtifactCache,
    repo_root: Path,
    results_root: Path,
) -> None:
    repository = repo_root.resolve(strict=True)
    artifact_root = artifact.artifact_root.resolve(strict=True)
    results = results_root.expanduser().resolve(strict=False)
    cache_root = artifact.root.resolve(strict=True)
    if results == cache_root or results.is_relative_to(cache_root) or cache_root.is_relative_to(results):
        raise ValueError("paper result and artifact cache directories must be disjoint")
    allowed_roots = (repository, artifact_root)
    for lane in lanes:
        for command in (*lane.build, *lane.prepare, *lane.observations, *lane.validate):
            if not any(command.cwd.is_relative_to(root) for root in allowed_roots):
                raise ValueError(f"paper command cwd is outside the repository and artifact: {command.cwd}")
            for path in command.runtime_artifacts:
                if not any(path.is_relative_to(root) for root in allowed_roots):
                    raise ValueError(f"paper runtime artifact is outside the repository and artifact: {path}")
        for path in lane.input_paths:
            resolved = path.resolve(strict=True)
            if not any(resolved.is_relative_to(root) for root in allowed_roots):
                raise ValueError(f"paper lane input is outside the repository and artifact: {path}")
