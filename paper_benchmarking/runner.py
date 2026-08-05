"""Compose deterministic run manifests and execute adapter-defined process lanes."""

from __future__ import annotations

import os
from collections.abc import Callable, Mapping, Sequence
from dataclasses import dataclass
from datetime import UTC, datetime
from pathlib import Path

from .artifact import ArtifactCache
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
    process_executor = executor or SubprocessExecutor()
    emit = report or (lambda _message: None)
    records: list[dict[str, object]] = []
    sequence = 1

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

        for round_number, command in enumerate(lane.observations, start=1):
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

    summary = render_markdown_summary(manifest, records)
    store.write_summary(summary)
    success = bool(records) and all(record["status"] == "success" for record in records)
    emit(f"Paper results: {store.path}")
    return RunResult(store.path, summary, success)


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
    outcome = executor.run(
        command,
        environment=environment,
        stdout_path=stdout_path,
        stderr_path=stderr_path,
    )
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
        "max_rss_bytes": outcome.max_rss_bytes,
        "phase": phase,
        "round": round_number,
        "run_id": store.run_id,
        "schema_version": RUN_RECORD_SCHEMA_VERSION,
        "sequence": sequence,
        "signal": outcome.signal,
        "started_at": outcome.started_at,
        "status": outcome.status,
        "stderr_log": str(stderr_path.relative_to(store.path)),
        "stdout_log": str(stdout_path.relative_to(store.path)),
        "timed_observation": phase == "observation",
        "timeout_sec": command.timeout_sec,
        "wall_sec": outcome.wall_sec,
    }


def _validate_outcome(outcome: ProcessOutcome) -> None:
    if outcome.status == "timed-out" and (outcome.wall_sec is not None or outcome.max_rss_bytes is not None):
        raise ValueError("timed-out paper process must not become a finite timing sample")
    if outcome.status == "success" and outcome.wall_sec is None:
        raise ValueError("successful paper process is missing wall time")


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
