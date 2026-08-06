"""Test process-lane hooks, status rows, logs, timeouts, wall time, and provenance."""

from __future__ import annotations

import json
import os
import sys
import time
from collections.abc import Mapping
from datetime import UTC, datetime
from pathlib import Path

import pytest

from paper_benchmarking.hashing import sha256_file
from paper_benchmarking.models import CommandSpec, ProcessLane, ProcessOutcome, ProcessStatus
from paper_benchmarking.processes import ProcessExecutor, SubprocessExecutor
from paper_benchmarking.provenance import resolve_executable
from paper_benchmarking.results import read_run_records
from paper_benchmarking.runner import run_lanes

from .paper_fixtures import fake_artifact_cache

FIXED_MACHINE = {"machine": "test", "system": "TestOS"}
FIXED_REPOSITORY = {"git_sha": "1" * 40, "is_dirty": False, "root": "/repo", "status": []}


def test_local_lane_records_success_failure_timeout_and_logs(tmp_path: Path) -> None:
    input_path = tmp_path / "input.txt"
    input_path.write_text("input\n", encoding="utf-8")
    python = sys.executable
    lane = ProcessLane(
        evaluation="math",
        name="fake-local",
        build=(
            CommandSpec(
                label="build",
                argv=(python, "-c", "print('build stdout')"),
                cwd=tmp_path,
                timeout_sec=2,
            ),
        ),
        prepare=(
            CommandSpec(
                label="prepare",
                argv=(python, "-c", "import sys; print('prepare stderr', file=sys.stderr)"),
                cwd=tmp_path,
                timeout_sec=2,
            ),
        ),
        observations=(
            CommandSpec(
                label="success",
                argv=(python, "-c", "import sys; print('child stdout'); print('child stderr', file=sys.stderr)"),
                cwd=tmp_path,
                timeout_sec=2,
                env={"PAPER_FAKE": "yes"},
            ),
            CommandSpec(
                label="failure",
                argv=(python, "-c", "import sys; print('failed locally', file=sys.stderr); raise SystemExit(7)"),
                cwd=tmp_path,
                timeout_sec=2,
            ),
            CommandSpec(
                label="timeout",
                argv=(python, "-c", "import time; time.sleep(2)"),
                cwd=tmp_path,
                timeout_sec=0.05,
            ),
        ),
        input_paths=(input_path,),
        versions={"fake-python": "test"},
    )

    result = run_lanes(
        (lane,),
        run_id="status-run",
        preset="quick",
        evaluations=("math",),
        artifact=fake_artifact_cache(tmp_path / "artifact-cache"),
        results_root=tmp_path / "results",
        invocation_argv=("paper_bench.py", "run", "quick", "math"),
        invocation_cwd=tmp_path,
        repo_root=tmp_path,
        environment=os.environ,
        created_at=datetime(2026, 8, 5, 12, 0, tzinfo=UTC),
        machine=FIXED_MACHINE,
        repository=FIXED_REPOSITORY,
    )

    assert not result.success
    rows = read_run_records(result.result_dir / "runs.jsonl")
    assert [(row["phase"], row["status"]) for row in rows] == [
        ("build", "success"),
        ("prepare", "success"),
        ("observation", "success"),
        ("observation", "failure"),
        ("observation", "timed-out"),
    ]
    assert [row["round"] for row in rows] == [None, None, 1, 2, 3]
    assert rows[2]["wall_sec"] is not None
    assert rows[3]["exit_code"] == 7
    assert rows[3]["wall_sec"] is not None
    assert rows[4]["wall_sec"] is None
    assert rows[4]["status"] == "timed-out"
    assert rows[2]["env"]["PAPER_FAKE"] == "yes"
    assert rows[2]["argv"] == list(lane.observations[0].argv)
    assert rows[2]["cwd"] == str(tmp_path)
    assert rows[2]["executable"]["sha256"] == sha256_file(Path(python).resolve())
    assert "child stdout" in (result.result_dir / rows[2]["stdout_log"]).read_text(encoding="utf-8")
    assert "child stderr" in (result.result_dir / rows[2]["stderr_log"]).read_text(encoding="utf-8")
    assert "Timed out |" in result.summary
    assert "| 1 | 1 | 1 |" in result.summary
    assert result.summary == (result.result_dir / "summary.md").read_text(encoding="utf-8")
    assert json.loads((result.result_dir / "status.json").read_text(encoding="utf-8")) == {
        "error": None,
        "run_id": "status-run",
        "state": "completed",
        "success": False,
    }


class RecordingExecutor(ProcessExecutor):
    """Return injected hook outcomes without starting child processes."""

    def __init__(self) -> None:
        self.labels: list[str] = []

    def run(
        self,
        command: CommandSpec,
        *,
        environment: Mapping[str, str],
        stdout_path: Path,
        stderr_path: Path,
    ) -> ProcessOutcome:
        del environment
        self.labels.append(command.label)
        stdout_path.write_text(f"{command.label}\n", encoding="utf-8")
        stderr_path.write_text("", encoding="utf-8")
        status: ProcessStatus = "failure" if command.label == "prepare" else "success"
        return ProcessOutcome(
            status=status,
            started_at="2026-08-05T12:00:00.000000Z",
            finished_at="2026-08-05T12:00:01.000000Z",
            wall_sec=1.0,
            exit_code=1 if status == "failure" else None,
            error_message="prepare failed" if status == "failure" else None,
        )


def test_injected_prepare_failure_blocks_timed_observations(tmp_path: Path) -> None:
    def command(label: str) -> CommandSpec:
        return CommandSpec(
            label=label,
            argv=(sys.executable, "-c", "pass"),
            cwd=tmp_path,
            timeout_sec=1,
        )

    lane = ProcessLane(
        evaluation="pointer",
        name="fake-injected",
        build=(command("build"),),
        prepare=(command("prepare"),),
        observations=(command("observe"),),
    )
    executor = RecordingExecutor()

    result = run_lanes(
        (lane,),
        run_id="hook-run",
        preset="representative",
        evaluations=("pointer",),
        artifact=fake_artifact_cache(tmp_path / "artifact-cache"),
        results_root=tmp_path / "results",
        invocation_argv=("paper_bench.py", "run", "representative", "pointer"),
        invocation_cwd=tmp_path,
        repo_root=tmp_path,
        executor=executor,
        environment={"PATH": os.environ["PATH"]},
        machine=FIXED_MACHINE,
        repository=FIXED_REPOSITORY,
    )

    assert not result.success
    assert executor.labels == ["build", "prepare"]
    rows = read_run_records(result.result_dir / "runs.jsonl")
    assert [row["phase"] for row in rows] == ["build", "prepare"]


def test_validation_hook_runs_after_timed_observations(tmp_path: Path) -> None:
    def command(label: str) -> CommandSpec:
        return CommandSpec(label=label, argv=(sys.executable, "-c", "pass"), cwd=tmp_path, timeout_sec=1)

    lane = ProcessLane(
        evaluation="math",
        name="post-validation",
        observations=(command("observe"),),
        validate=(command("validate"),),
    )
    executor = RecordingExecutor()

    result = run_lanes(
        (lane,),
        run_id="post-validation-run",
        preset="quick",
        evaluations=("math",),
        artifact=fake_artifact_cache(tmp_path / "artifact-cache"),
        results_root=tmp_path / "results",
        invocation_argv=("paper_bench.py", "run", "quick", "math"),
        invocation_cwd=tmp_path,
        repo_root=tmp_path,
        executor=executor,
        environment={"PATH": os.environ["PATH"]},
        machine=FIXED_MACHINE,
        repository=FIXED_REPOSITORY,
    )

    assert result.success
    assert executor.labels == ["observe", "validate"]
    rows = read_run_records(result.result_dir / "runs.jsonl")
    assert [row["phase"] for row in rows] == ["observation", "validate"]


def test_child_environment_excludes_unapproved_inherited_values(tmp_path: Path) -> None:
    lane = ProcessLane(
        evaluation="math",
        name="environment",
        observations=(
            CommandSpec(
                label="inspect",
                argv=(
                    sys.executable,
                    "-c",
                    ("import os; print(os.environ.get('PAPER_EXPLICIT')); print('PAPER_SECRET' in os.environ)"),
                ),
                cwd=tmp_path,
                timeout_sec=2,
                env={"PAPER_EXPLICIT": "yes"},
                expected_stdout_lines=("yes", "False"),
            ),
        ),
    )

    result = run_lanes(
        (lane,),
        run_id="environment-run",
        preset="quick",
        evaluations=("math",),
        artifact=fake_artifact_cache(tmp_path / "artifact-cache"),
        results_root=tmp_path / "results",
        invocation_argv=("paper_bench.py", "run", "quick", "math"),
        invocation_cwd=tmp_path,
        repo_root=tmp_path,
        environment={"PATH": os.environ["PATH"], "PAPER_SECRET": "must-not-leak"},
        machine=FIXED_MACHINE,
        repository=FIXED_REPOSITORY,
    )

    assert result.success


def test_exact_output_expectation_failure_is_not_a_timing_success(tmp_path: Path) -> None:
    lane = ProcessLane(
        evaluation="math",
        name="output-gate",
        observations=(
            CommandSpec(
                label="wrong",
                argv=(sys.executable, "-c", "print(1)"),
                cwd=tmp_path,
                timeout_sec=2,
                expected_stdout_lines=("2",),
            ),
        ),
    )

    result = run_lanes(
        (lane,),
        run_id="output-gate-run",
        preset="quick",
        evaluations=("math",),
        artifact=fake_artifact_cache(tmp_path / "artifact-cache"),
        results_root=tmp_path / "results",
        invocation_argv=("paper_bench.py", "run", "quick", "math"),
        invocation_cwd=tmp_path,
        repo_root=tmp_path,
        machine=FIXED_MACHINE,
        repository=FIXED_REPOSITORY,
    )

    assert not result.success
    (row,) = read_run_records(result.result_dir / "runs.jsonl")
    assert row["status"] == "failure"
    assert row["exit_code"] == 0
    assert "did not exactly match" in row["error_message"]


def test_csv_output_expectation_requires_one_exact_artifact_record(tmp_path: Path) -> None:
    lane = ProcessLane(
        evaluation="math",
        name="csv-output-gate",
        observations=(
            CommandSpec(
                label="right",
                argv=(sys.executable, "-c", "print('math-run-10,Eqlog,1234,21052')"),
                cwd=tmp_path,
                timeout_sec=2,
                expected_stdout_csv_record=("math-run-10", "Eqlog", 21_052),
            ),
            CommandSpec(
                label="extra",
                argv=(sys.executable, "-c", "print('math-run-10,Eqlog,1234,21052\\nextra')"),
                cwd=tmp_path,
                timeout_sec=2,
                expected_stdout_csv_record=("math-run-10", "Eqlog", 21_052),
            ),
        ),
    )

    result = run_lanes(
        (lane,),
        run_id="csv-output-gate-run",
        preset="quick",
        evaluations=("math",),
        artifact=fake_artifact_cache(tmp_path / "artifact-cache"),
        results_root=tmp_path / "results",
        invocation_argv=("paper_bench.py", "run", "quick", "math"),
        invocation_cwd=tmp_path,
        repo_root=tmp_path,
        machine=FIXED_MACHINE,
        repository=FIXED_REPOSITORY,
    )

    assert not result.success
    rows = read_run_records(result.result_dir / "runs.jsonl")
    assert [row["status"] for row in rows] == ["success", "failure"]
    assert "exactly one four-field" in rows[1]["error_message"]


def test_run_record_hashes_declared_nested_runtime(tmp_path: Path) -> None:
    runtime_artifact = tmp_path / "generated.bin"
    runtime_artifact.write_bytes(b"generated runtime\n")
    lane = ProcessLane(
        evaluation="math",
        name="runtime-provenance",
        observations=(
            CommandSpec(
                label="run",
                argv=(sys.executable, "-c", "pass"),
                cwd=tmp_path,
                timeout_sec=2,
                runtime_executables=(sys.executable,),
                runtime_artifacts=(runtime_artifact,),
            ),
        ),
    )

    result = run_lanes(
        (lane,),
        run_id="runtime-provenance-run",
        preset="quick",
        evaluations=("math",),
        artifact=fake_artifact_cache(tmp_path / "artifact-cache"),
        results_root=tmp_path / "results",
        invocation_argv=("paper_bench.py", "run", "quick", "math"),
        invocation_cwd=tmp_path,
        repo_root=tmp_path,
        machine=FIXED_MACHINE,
        repository=FIXED_REPOSITORY,
    )

    assert result.success
    (row,) = read_run_records(result.result_dir / "runs.jsonl")
    assert row["runtime"]["executables"][0]["sha256"] == sha256_file(Path(sys.executable))
    assert row["runtime"]["artifacts"][0]["sha256"] == sha256_file(runtime_artifact)


class NonfiniteExecutor(ProcessExecutor):
    """Return a structurally invalid success for fail-closed validation."""

    def run(
        self,
        command: CommandSpec,
        *,
        environment: Mapping[str, str],
        stdout_path: Path,
        stderr_path: Path,
    ) -> ProcessOutcome:
        del command, environment
        stdout_path.write_text("", encoding="utf-8")
        stderr_path.write_text("", encoding="utf-8")
        return ProcessOutcome(
            status="success",
            started_at="2026-08-05T12:00:00.000000Z",
            finished_at="2026-08-05T12:00:01.000000Z",
            wall_sec=float("nan"),
        )


def test_nonfinite_outcome_fails_run_and_publishes_terminal_status(tmp_path: Path) -> None:
    lane = ProcessLane(
        evaluation="math",
        name="nonfinite",
        observations=(CommandSpec(label="run", argv=(sys.executable, "-c", "pass"), cwd=tmp_path, timeout_sec=1),),
    )
    results = tmp_path / "results"

    with pytest.raises(ValueError, match="contradictory outcome"):
        run_lanes(
            (lane,),
            run_id="nonfinite-run",
            preset="quick",
            evaluations=("math",),
            artifact=fake_artifact_cache(tmp_path / "artifact-cache"),
            results_root=results,
            invocation_argv=("paper_bench.py", "run", "quick", "math"),
            invocation_cwd=tmp_path,
            repo_root=tmp_path,
            executor=NonfiniteExecutor(),
            machine=FIXED_MACHINE,
            repository=FIXED_REPOSITORY,
        )

    status = json.loads((results / "nonfinite-run/status.json").read_text(encoding="utf-8"))
    assert status["state"] == "failed"
    assert status["success"] is False


def test_lane_command_cwd_must_stay_inside_repository_or_artifact(tmp_path: Path) -> None:
    repo = tmp_path / "repo"
    repo.mkdir()
    outside = tmp_path / "outside"
    outside.mkdir()
    lane = ProcessLane(
        evaluation="math",
        name="escaped",
        observations=(CommandSpec(label="run", argv=(sys.executable, "-c", "pass"), cwd=outside, timeout_sec=1),),
    )
    results = tmp_path / "results"

    with pytest.raises(ValueError, match="cwd is outside"):
        run_lanes(
            (lane,),
            run_id="escaped-run",
            preset="quick",
            evaluations=("math",),
            artifact=fake_artifact_cache(tmp_path / "artifact-cache"),
            results_root=results,
            invocation_argv=("paper_bench.py", "run", "quick", "math"),
            invocation_cwd=repo,
            repo_root=repo,
            machine=FIXED_MACHINE,
            repository=FIXED_REPOSITORY,
        )

    assert not results.exists()


def test_executor_kills_descendants_left_after_the_group_leader_exits(tmp_path: Path) -> None:
    command = CommandSpec(
        label="descendant",
        argv=(
            sys.executable,
            "-c",
            (
                "import subprocess, sys; "
                "child = subprocess.Popen([sys.executable, '-c', 'import time; time.sleep(60)']); "
                "print(child.pid, flush=True)"
            ),
        ),
        cwd=tmp_path,
        timeout_sec=2,
    )
    stdout = tmp_path / "stdout"
    stderr = tmp_path / "stderr"

    outcome = SubprocessExecutor().run(
        command,
        environment={"PATH": os.environ["PATH"]},
        stdout_path=stdout,
        stderr_path=stderr,
    )

    assert outcome.status == "success"
    child_pid = int(stdout.read_text(encoding="utf-8").strip())
    deadline = time.monotonic() + 2
    while time.monotonic() < deadline:
        try:
            os.kill(child_pid, 0)
        except ProcessLookupError:
            break
        time.sleep(0.02)
    else:
        pytest.fail(f"descendant process {child_pid} survived its paper command")


def test_executable_resolution_preserves_proxy_symlink_name(tmp_path: Path) -> None:
    proxy = tmp_path / "python-proxy"
    proxy.symlink_to(sys.executable)
    command = CommandSpec(label="proxy", argv=(proxy.name, "--version"), cwd=tmp_path, timeout_sec=1)

    assert resolve_executable(command, {"PATH": str(tmp_path)}) == proxy
