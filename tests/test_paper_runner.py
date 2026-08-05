"""Test process-lane hook boundaries, status rows, logs, timeout handling, wall, and RSS."""

from __future__ import annotations

import os
import sys
from collections.abc import Mapping
from datetime import UTC, datetime
from pathlib import Path

from paper_benchmarking.hashing import sha256_file
from paper_benchmarking.models import CommandSpec, ProcessLane, ProcessOutcome, ProcessStatus
from paper_benchmarking.processes import ProcessExecutor
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
    assert [row["timed_observation"] for row in rows] == [False, False, True, True, True]
    assert [row["round"] for row in rows] == [None, None, 1, 2, 3]
    assert rows[2]["wall_sec"] is not None
    assert rows[2]["max_rss_bytes"] is not None
    assert rows[3]["exit_code"] == 7
    assert rows[3]["wall_sec"] is not None
    assert rows[4]["wall_sec"] is None
    assert rows[4]["max_rss_bytes"] is None
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
            max_rss_bytes=1024,
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
