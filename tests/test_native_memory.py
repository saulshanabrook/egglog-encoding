"""Test controlled native launch policy and local versus invocation failures."""

from __future__ import annotations

import io
import subprocess
import sys
from pathlib import Path

import pytest
from rich.console import Console

import native_memory
from benchmarking import collection, processes
from benchmarking.reports.store import ReportStore

from .report_fixtures import make_target
from .test_collection import planned_run


def test_native_command_uses_explicit_limit_and_fixed_startup_policy() -> None:
    command, env = native_memory.native_memory_command(["engine", "--help"], {"RUST_LOG": "error"})
    assert command == ["engine", "--memory-limit-bytes=17179869184", "--help"]
    assert env == {"RUST_LOG": "error", **native_memory.NATIVE_ALLOCATOR_ENV}
    assert native_memory.native_memory_command(["engine"], {}, 123)[0] == ["engine", "--memory-limit-bytes=123"]


@pytest.mark.parametrize(("code", "controlled", "stop"), [(86, True, False), (87, True, True), (87, False, False)])
def test_native_exit_protocol_does_not_depend_on_diagnostic_text(
    tmp_path: Path, code: int, controlled: bool, stop: bool
) -> None:
    engine = tmp_path / "engine"
    engine.write_text(
        f"#!{sys.executable}\nimport sys\nprint('arbitrary diagnostic',file=sys.stderr)\nsys.exit({code})\n"
    )
    engine.chmod(0o755)
    result = processes.run_command([str(engine)], tmp_path, 5, native_limit=controlled)
    assert result.status == "failure"
    assert result.stop_collection is stop
    assert result.error is not None and result.error.exit_code == code
    assert result.error.message == "arbitrary diagnostic"
    assert result.timing.wall_sec is not None and result.timing.max_rss_bytes is not None


@pytest.mark.parametrize("code", [86, 87])
def test_native_outcome_is_retained_before_local_skip_or_invocation_stop(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, code: int
) -> None:
    run = planned_run(required=3)
    other = planned_run(filename="other.egg", required=1)
    plan = collection.CollectionPlan(make_target(binary_path=tmp_path / "engine"), (run, other))
    calls = 0

    def observe(*_args: object) -> collection.ProcessObservation:
        nonlocal calls
        calls += 1
        return collection.ProcessObservation(
            processes.TimingResult(
                "failure",
                processes.TimingRow(),
                processes.ErrorRow("native failure", exit_code=code),
                stop_collection=code == 87,
            ),
            None,
        )

    monkeypatch.setattr(collection, "run_process", observe)
    store = ReportStore(tmp_path / "report.jsonl")
    if code == 87:
        with pytest.raises(ValueError, match="failed observation was retained"):
            collection.collect_rows(store, plan, 120, Console(file=io.StringIO()))
        assert calls == store.row_count == 1
    else:
        collection.collect_rows(store, plan, 120, Console(file=io.StringIO()))
        assert calls == store.row_count == 2
    assert store.records[0]["error_exit_code"] == code


def test_older_binary_rejecting_native_option_fails_preflight(tmp_path: Path) -> None:
    engine = tmp_path / "engine"
    engine.write_text(
        f"#!{sys.executable}\nimport sys\n"
        "assert sys.argv[1] == '--memory-limit-bytes=17179869184'\n"
        "print('unsupported native option',file=sys.stderr)\nsys.exit(2)\n"
    )
    engine.chmod(0o755)
    plan = collection.CollectionPlan(make_target(binary_path=engine), (planned_run(required=1),))
    with pytest.raises(ValueError, match="preflight failed.*unsupported native option"):
        collection.preflight_collection(plan, 5)


def test_unexpected_sigkill_is_a_stop_without_an_oom_claim(tmp_path: Path) -> None:
    result = processes.run_command(
        [sys.executable, "-c", "import os,signal; os.kill(os.getpid(), signal.SIGKILL)"], tmp_path, 5
    )
    assert result.stop_collection
    assert result.error is not None and "cause unknown" in result.error.message
    assert "OOM" not in result.error.message


@pytest.mark.parametrize("exit_code", [0, 2, None])
def test_cleanup_failure_retains_attempt_before_stopping(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, exit_code: int | None
) -> None:
    cleanup = processes.terminate_process_group
    calls = 0

    def failed_cleanup(process: subprocess.Popen[str] | subprocess.Popen[bytes]) -> None:
        cleanup(process)
        raise PermissionError("process-group cleanup failed")

    def observe(*_args: object) -> collection.ProcessObservation:
        nonlocal calls
        calls += 1
        child_code = (
            "import time; time.sleep(60)" if exit_code is None else f"print('complete'); raise SystemExit({exit_code})"
        )
        result = processes.run_command([sys.executable, "-c", child_code], tmp_path, 1)
        return collection.ProcessObservation(result, None)

    monkeypatch.setattr(processes, "terminate_process_group", failed_cleanup)
    monkeypatch.setattr(collection, "run_process", observe)
    plan = collection.CollectionPlan(
        make_target(binary_path=tmp_path / "engine"),
        (planned_run(required=2), planned_run(filename="other.egg", required=1)),
    )
    store = ReportStore(tmp_path / "report.jsonl")
    with pytest.raises(ValueError, match="cleanup failed.*failed observation was retained"):
        collection.collect_rows(store, plan, 120, Console(file=io.StringIO()))
    assert calls == store.row_count == 1
    record = store.records[0]
    assert record["error_exit_code"] == exit_code
    if exit_code is None:
        assert record["status"] == "timed-out"
        assert record["wall_sec"] is None and record["max_rss_bytes"] is None
    else:
        assert record["status"] == "failure"
        assert record["wall_sec"] is not None and record["wall_sec"] > 0
        assert record["max_rss_bytes"] is not None and record["max_rss_bytes"] > 0


@pytest.mark.parametrize("stage", ["launch", "wait"])
def test_process_setup_failure_does_not_fabricate_an_observation(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, stage: str
) -> None:
    calls = 0

    def failed_wait(*_args: object) -> None:
        raise OSError("wait failed before a process outcome was available")

    def observe(*_args: object) -> collection.ProcessObservation:
        nonlocal calls
        calls += 1
        command = [str(tmp_path / "missing")] if stage == "launch" else [sys.executable, "-c", "pass"]
        return collection.ProcessObservation(processes.run_command(command, tmp_path, 5), None)

    if stage == "wait":
        monkeypatch.setattr(processes, "wait4_process", failed_wait)
    monkeypatch.setattr(collection, "run_process", observe)
    plan = collection.CollectionPlan(
        make_target(binary_path=tmp_path / "engine"),
        (planned_run(required=2), planned_run(filename="other.egg", required=1)),
    )
    store = ReportStore(tmp_path / "report.jsonl")
    with pytest.raises(OSError):
        collection.collect_rows(store, plan, 120, Console(file=io.StringIO()))
    assert calls == 1
    assert store.row_count == 0
