"""Protect the host without fabricating observations or masking campaign stops."""

from __future__ import annotations

import os
import resource
import signal
import subprocess
import sys
import time
from contextlib import suppress
from pathlib import Path
from typing import Any

import pytest

import process_guard as memory_guard
from benchmarking import processes
from scripts import reproduction_process


@pytest.fixture
def guarded(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setenv("EGGLOG_BENCH_MEMORY_GUARD", "1")


def test_default_cap_accepts_ten_gib_but_stops_above_it(guarded: None) -> None:
    guard = memory_guard.MemoryGuard.from_environment()
    assert guard is not None
    assert guard.check(8 * 1024**3 + 1) is None
    assert guard.check(10 * 1024**3) is None
    assert "10737418240-byte safety cap" in str(guard.check(10 * 1024**3 + 1))


def test_group_rss_includes_descendants_but_not_other_groups(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(
        memory_guard.subprocess,
        "run",
        lambda *_args, **_kwargs: subprocess.CompletedProcess([], 0, "123 10\n123 20\n456 9000000\n"),
    )
    assert memory_guard.group_rss_bytes(123) == 30 * 1024


@pytest.mark.parametrize("timeouts", [1, 2, 3])
def test_transient_rss_sample_timeouts_retry_without_fabricating_zero(
    monkeypatch: pytest.MonkeyPatch, timeouts: int
) -> None:
    deadlines: list[int] = []

    def snapshot(command: list[str], *, timeout: int, **_kwargs: object) -> subprocess.CompletedProcess[str]:
        deadlines.append(timeout)
        if len(deadlines) <= timeouts:
            raise subprocess.TimeoutExpired(command, timeout)
        return subprocess.CompletedProcess(command, 0, "123 10\n123 20\n456 9000000\n")

    monkeypatch.setattr(memory_guard.subprocess, "run", snapshot)
    if timeouts == 3:
        with pytest.raises(subprocess.TimeoutExpired):
            memory_guard.group_rss_bytes(123)
    else:
        assert memory_guard.group_rss_bytes(123) == 30 * 1024
    assert deadlines == [1, 2, 4][: timeouts + 1]


@pytest.mark.parametrize("diagnostic", [False, True])
def test_live_workload_survives_one_stalled_rss_sample(
    guarded: None, monkeypatch: pytest.MonkeyPatch, tmp_path: Path, diagnostic: bool
) -> None:
    original_run = subprocess.run
    attempts = 0

    def snapshot(command: list[str], **kwargs: Any) -> subprocess.CompletedProcess[str]:
        nonlocal attempts
        if command == ["ps", "-axo", "pgid=,rss="]:
            attempts += 1
            if attempts == 1:
                raise subprocess.TimeoutExpired(command, 1)
        result: subprocess.CompletedProcess[str] = original_run(command, **kwargs)
        return result

    monkeypatch.setattr(memory_guard.subprocess, "run", snapshot)
    command = [sys.executable, "-c", "import time; time.sleep(0.2); print('completed')"]
    if diagnostic:
        result = reproduction_process.run_bounded_command(command, tmp_path, tmp_path / "recovered", timeout_sec=5)
        assert result.status == "success" and result.stdout_path.read_text() == "completed\n"
    else:
        measured = processes.run_command(command, tmp_path, 5)
        assert measured.status == "success" and not measured.resource_stopped
    assert attempts >= 2


@pytest.mark.parametrize("cause", ["cap", "monitor-error"])
def test_live_guard_stops_workload_group_and_discards_invalid_timing(
    guarded: None, monkeypatch: pytest.MonkeyPatch, tmp_path: Path, cause: str
) -> None:
    pids = tmp_path / "pids"
    code = (
        "import os,subprocess,sys,time,pathlib; "
        "child=subprocess.Popen([sys.executable,'-c','import time; time.sleep(30)']); "
        "pathlib.Path(sys.argv[1]).write_text(f'{os.getpid()} {child.pid}'); time.sleep(30)"
    )

    def rss(_group: int) -> int:
        if not pids.exists():
            return 0
        if cause == "monitor-error":
            raise OSError("ps unavailable")
        return memory_guard.GROUP_LIMIT_BYTES + 1

    monkeypatch.setattr(memory_guard, "group_rss_bytes", rss)
    try:
        result = processes.run_command([sys.executable, "-c", code, str(pids)], tmp_path, 5)
        assert result.status == "failure"
        assert result.resource_stopped
        assert result.timing == processes.TimingRow()
        assert result.error is not None
        assert {
            "cap": "safety cap",
            "monitor-error": "ps unavailable",
        }[cause] in result.error.message
        for pid in map(int, pids.read_text().split()):
            for _ in range(100):
                state = subprocess.run(
                    ["ps", "-o", "state=", "-p", str(pid)], capture_output=True, text=True, check=False
                )
                if not state.stdout.strip() or state.stdout.strip().startswith("Z"):
                    break
                time.sleep(0.01)
            else:
                pytest.fail(f"guard left process {pid} alive")
    finally:
        if pids.exists():
            for pid in map(int, pids.read_text().split()):
                with suppress(ProcessLookupError):
                    os.kill(pid, signal.SIGKILL)


def test_guard_preserves_successful_timing(guarded: None, tmp_path: Path) -> None:
    result = processes.run_command([sys.executable, "-c", "print('ok')"], tmp_path, 5)
    assert result.status == "success"
    assert result.timing.wall_sec is not None
    assert result.timing.max_rss_bytes is not None
    assert not result.resource_stopped


def test_exact_post_exit_peak_halts_when_sampling_missed_it(
    guarded: None, monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    original_wait4 = processes.wait4_process
    peak = memory_guard.GROUP_LIMIT_BYTES + 1024

    def large_recorded_peak(process: subprocess.Popen[str], timeout_sec: int) -> tuple[int, resource.struct_rusage]:
        code, usage = original_wait4(process, timeout_sec)
        values = list(usage)
        values[2] = peak if sys.platform == "darwin" else peak // 1024
        return code, resource.struct_rusage(values)

    monkeypatch.setattr(processes, "wait4_process", large_recorded_peak)
    monkeypatch.setattr(memory_guard, "group_rss_bytes", lambda _group: 0)
    result = processes.run_command([sys.executable, "-c", "pass"], tmp_path, 5)
    assert result.status == "failure"
    assert result.resource_stopped
    assert result.timing.wall_sec is None
    assert result.timing.max_rss_bytes == peak
    assert result.error is not None
    assert "detected after workload exit" in result.error.message
    assert "safety cap" in result.error.message
    assert result.error.signal is None


@pytest.mark.parametrize("enabled", [False, True])
def test_unexpected_sigkill_halts_guarded_collection_without_claiming_oom(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, enabled: bool
) -> None:
    monkeypatch.setenv("EGGLOG_BENCH_MEMORY_GUARD", "1" if enabled else "")
    command = [
        sys.executable,
        "-c",
        "import os,signal,sys; print('before kill',file=sys.stderr,flush=True); os.kill(os.getpid(),signal.SIGKILL)",
    ]
    measured = processes.run_command(command, tmp_path, 5)
    assert measured.status == "failure"
    assert measured.resource_stopped is enabled
    assert measured.error is not None and measured.error.signal == signal.SIGKILL
    assert measured.error.exit_code is None
    assert "before kill" in measured.error.message
    assert ("unexpected SIGKILL (cause unknown)" in measured.error.message) is enabled

    bounded = reproduction_process.run_bounded_command(command, tmp_path, tmp_path / "sigkill", timeout_sec=5)
    assert bounded.status == ("resource-stopped" if enabled else "failure")
    assert bounded.returncode == -signal.SIGKILL
    assert "before kill" in bounded.stderr_path.read_text()
    assert bounded.message is not None and "before kill" in bounded.message
    assert ("unexpected SIGKILL (cause unknown)" in bounded.message) is enabled


def test_bounded_diagnostic_obeys_live_rss_cap(guarded: None, monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    monkeypatch.setattr(memory_guard, "GROUP_LIMIT_BYTES", 1024)
    result = reproduction_process.run_bounded_command(
        [sys.executable, "-c", "import time; time.sleep(30)"], tmp_path, tmp_path / "guard", timeout_sec=5
    )
    assert result.status == "resource-stopped"
    assert result.message is not None and "safety cap" in result.message
    assert result.peak_rss_bytes > 1024
    assert result.stdout_path.exists() and result.stderr_path.exists()
