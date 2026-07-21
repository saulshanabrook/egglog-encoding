"""Test subprocess accounting, timeout, interruption, and process-group cleanup."""

from __future__ import annotations

import os
import resource
import signal
import subprocess
import sys
import time
from contextlib import suppress
from pathlib import Path
from typing import cast

import pytest

from benchmarking import processes

from .report_fixtures import ROOT


def test_ru_maxrss_to_bytes_normalizes_platform_units() -> None:
    assert processes.ru_maxrss_to_bytes(123, platform="darwin") == 123
    assert processes.ru_maxrss_to_bytes(123, platform="linux") == 123 * 1024
    assert processes.ru_maxrss_to_bytes(0, platform="linux") is None


def test_run_command_records_signal_separately_from_exit_code() -> None:
    result = processes.run_command(
        [sys.executable, "-c", "import os, signal; os.kill(os.getpid(), signal.SIGTERM)"],
        ROOT,
        120,
    )

    assert result.status == "failure"
    assert result.error is not None
    assert result.error.exit_code is None
    assert result.error.signal == signal.SIGTERM


def test_wait4_process_blocks_instead_of_polling(monkeypatch: pytest.MonkeyPatch) -> None:
    calls: list[tuple[int, int]] = []
    usage = resource.struct_rusage((0.0,) * 16)

    class FakeProcess:
        pid = 123
        args = ["fake"]
        returncode: int | None = None

    def fake_wait4(pid: int, options: int) -> tuple[int, int, resource.struct_rusage]:
        calls.append((pid, options))
        return pid, 0, usage

    monkeypatch.setattr(processes.os, "wait4", fake_wait4)

    return_code, returned_usage = processes.wait4_process(
        cast(subprocess.Popen[str], FakeProcess()),
        120,
    )

    assert calls == [(123, 0)]
    assert return_code == 0
    assert returned_usage is usage


def test_wait4_process_cleans_up_if_timer_start_is_interrupted(monkeypatch: pytest.MonkeyPatch) -> None:
    events: list[str] = []

    class InterruptingTimer:
        def start(self) -> None:
            events.append("start")
            raise KeyboardInterrupt

        def cancel(self) -> None:
            events.append("cancel")

        def join(self) -> None:
            events.append("join")
            raise RuntimeError("thread never started")

    class FakeProcess:
        pid = 123
        args = ["fake"]
        returncode: int | None = None

    monkeypatch.setattr(processes.threading, "Timer", lambda *_args: InterruptingTimer())

    with pytest.raises(KeyboardInterrupt):
        processes.wait4_process(cast(subprocess.Popen[str], FakeProcess()), 120)

    assert events == ["start", "cancel", "join"]


def test_run_command_timeout_kills_descendant_processes(tmp_path: Path) -> None:
    descendant_pid_path = tmp_path / "descendant.pid"
    child_code = (
        "import subprocess, sys, time; from pathlib import Path; "
        "child = subprocess.Popen([sys.executable, '-c', 'import time; time.sleep(60)']); "
        f"Path({str(descendant_pid_path)!r}).write_text(str(child.pid)); time.sleep(60)"
    )
    descendant_pid: int | None = None
    try:
        result = processes.run_command([sys.executable, "-c", child_code], ROOT, 1)
        assert result.status == "timed-out"
        descendant_pid = int(descendant_pid_path.read_text(encoding="utf-8"))
        deadline = time.monotonic() + 2
        while time.monotonic() < deadline:
            state = subprocess.run(
                ["ps", "-o", "state=", "-p", str(descendant_pid)],
                capture_output=True,
                text=True,
                check=False,
            ).stdout.strip()
            if not state or state.startswith("Z"):
                break
            time.sleep(0.01)
        else:
            pytest.fail(f"descendant process {descendant_pid} survived timeout cleanup")
    finally:
        if descendant_pid is None:
            with suppress(OSError, ValueError):
                descendant_pid = int(descendant_pid_path.read_text(encoding="utf-8"))
        if descendant_pid is not None:
            with suppress(ProcessLookupError):
                os.kill(descendant_pid, signal.SIGKILL)


def test_run_command_interrupt_cleans_up_before_propagating(monkeypatch: pytest.MonkeyPatch) -> None:
    interrupted: list[int] = []
    terminated: list[int] = []
    terminate_process_group = processes.terminate_process_group

    def interrupt(process: subprocess.Popen[str], _timeout_sec: int) -> None:
        interrupted.append(process.pid)
        raise KeyboardInterrupt

    def terminate(process: subprocess.Popen[str]) -> None:
        terminated.append(process.pid)
        terminate_process_group(process)

    monkeypatch.setattr(processes, "wait4_process", interrupt)
    monkeypatch.setattr(processes, "terminate_process_group", terminate)

    with pytest.raises(KeyboardInterrupt):
        processes.run_command([sys.executable, "-c", "import time; time.sleep(60)"], ROOT, 120)

    assert terminated == interrupted


def test_run_command_records_peak_rss() -> None:
    result = processes.run_command([sys.executable, "-c", "print('ok')"], ROOT, 120)

    assert result.status == "success"
    assert result.timing.max_rss_bytes is not None
    assert result.timing.max_rss_bytes > 0


def test_run_command_can_require_capability_output() -> None:
    present = processes.run_command(
        [sys.executable, "-c", "print('--timing-summary PATH')"],
        ROOT,
        120,
        required_output="--timing-summary",
    )
    missing = processes.run_command(
        [sys.executable, "-c", "print('usage')"],
        ROOT,
        120,
        required_output="--timing-summary",
    )
    all_present = processes.run_command(
        [sys.executable, "-c", "print('--timing-summary PATH --proof-extraction')"],
        ROOT,
        120,
        required_output=("--timing-summary", "--proof-extraction"),
    )
    extraction_missing = processes.run_command(
        [sys.executable, "-c", "print('--timing-summary PATH')"],
        ROOT,
        120,
        required_output=("--timing-summary", "--proof-extraction"),
    )

    assert present.status == "success"
    assert missing.status == "failure"
    assert missing.error is not None
    assert "did not contain" in missing.error.message
    assert all_present.status == "success"
    assert extraction_missing.status == "failure"
    assert extraction_missing.error is not None
    assert "--proof-extraction" in extraction_missing.error.message


def test_timing_from_usage_records_peak_rss() -> None:
    usage = resource.struct_rusage((1.0, 2.0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0))

    timing = processes.timing_from_usage(usage, 1.0)

    assert timing.max_rss_bytes == processes.ru_maxrss_to_bytes(3)
