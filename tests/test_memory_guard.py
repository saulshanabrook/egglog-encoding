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

from benchmarking import memory_guard, processes


@pytest.fixture
def guarded(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setenv("EGGLOG_BENCH_MEMORY_GUARD", "1")
    monkeypatch.setattr(memory_guard, "host_memory", lambda: (8 * 1024**3, 1))


def test_default_cap_accepts_ten_gib_but_stops_above_it(guarded: None) -> None:
    guard = memory_guard.MemoryGuard.from_environment()
    assert guard is not None
    assert guard.check(8 * 1024**3 + 1) is None
    assert guard.check(10 * 1024**3) is None
    assert "10737418240-byte safety cap" in str(guard.check(10 * 1024**3 + 1))
    assert memory_guard.HEADROOM_BYTES == 2 * 1024**3


def test_group_rss_includes_descendants_but_not_other_groups(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(
        memory_guard.subprocess,
        "run",
        lambda *_args, **_kwargs: subprocess.CompletedProcess([], 0, "123 10\n123 20\n456 9000000\n"),
    )
    assert memory_guard.group_rss_bytes(123) == 30 * 1024


def test_macos_headroom_uses_page_size_and_distinct_counters(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(memory_guard.sys, "platform", "darwin")

    def command(args: list[str], **kwargs: Any) -> subprocess.CompletedProcess[str]:
        return subprocess.CompletedProcess(
            args,
            0,
            "1\n"
            if args[0] == "sysctl"
            else (
                "Mach Virtual Memory Statistics: (page size of 16384 bytes)\n"
                "Pages free: 10.\nPages inactive: 20.\nPages speculative: 30.\nPages purgeable: 90.\n"
            ),
        )

    monkeypatch.setattr(memory_guard.subprocess, "run", command)
    assert memory_guard.host_memory() == (60 * 16384, 1)


@pytest.mark.parametrize("headroom,pressure", [(8 * 1024**3, 2), (1024, 1)])
def test_unsafe_host_prevents_launch_without_measurement(
    guarded: None, monkeypatch: pytest.MonkeyPatch, tmp_path: Path, headroom: int, pressure: int
) -> None:
    monkeypatch.setattr(memory_guard, "host_memory", lambda: (headroom, pressure))
    monkeypatch.setattr(processes.subprocess, "Popen", lambda *_a, **_kw: pytest.fail("must not launch"))
    with pytest.raises(ValueError, match="resource guard refused to launch"):
        processes.run_command(["unused"], tmp_path, 5)
    with pytest.raises(ValueError, match="resource guard refused to launch"):
        processes.run_bounded_command(["unused"], tmp_path, tmp_path / "unused")
    assert not list(tmp_path.iterdir())


def test_unavailable_host_monitor_prevents_launch(
    guarded: None, monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    def unavailable() -> tuple[int, int]:
        raise OSError("vm_stat unavailable")

    monkeypatch.setattr(memory_guard, "host_memory", unavailable)
    with pytest.raises(ValueError, match="memory monitoring failed: vm_stat unavailable"):
        processes.run_command(["unused"], tmp_path, 5)


def test_diagnostic_warning_override_preserves_measurement_policy_and_limits(
    guarded: None, monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    monkeypatch.setattr(memory_guard, "host_memory", lambda: (8 * 1024**3, 2))
    command = [sys.executable, "-c", "print('diagnostic')"]
    result = processes.run_bounded_command(command, tmp_path, tmp_path / "warning", allow_warning_pressure=True)
    assert result.status == "success"
    assert result.stdout_path.read_text().strip() == "diagnostic"
    with pytest.raises(ValueError, match="not normal"):
        processes.run_command(command, tmp_path, 5)
    guard = memory_guard.MemoryGuard.from_environment(allow_warning_pressure=True)
    assert guard is not None
    assert "safety cap" in str(guard.check(memory_guard.GROUP_LIMIT_BYTES + 1))
    for host_state in ((8 * 1024**3, 4), (8 * 1024**3, 0), (1024, 2)):
        monkeypatch.setattr(memory_guard, "host_memory", lambda state=host_state: state)
        with pytest.raises(ValueError, match="resource guard refused to launch"):
            processes.run_bounded_command(command, tmp_path, tmp_path / "unsafe", allow_warning_pressure=True)


@pytest.mark.parametrize("cause", ["cap", "host-pressure", "monitor-error"])
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
        return memory_guard.GROUP_LIMIT_BYTES + 1 if cause == "cap" else 1

    monkeypatch.setattr(memory_guard, "group_rss_bytes", rss)
    if cause == "host-pressure":
        monkeypatch.setattr(memory_guard, "host_memory", lambda: (8 * 1024**3, 2 if pids.exists() else 1))
    try:
        result = processes.run_command([sys.executable, "-c", code, str(pids)], tmp_path, 5)
        assert result.status == "failure"
        assert result.resource_stopped
        assert result.timing == processes.TimingRow()
        assert result.error is not None
        assert {
            "cap": "safety cap",
            "host-pressure": "host memory pressure",
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
    monkeypatch.setattr(memory_guard, "host_memory", lambda: (8 * 1024**3, 1))
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

    bounded = processes.run_bounded_command(command, tmp_path, tmp_path / "sigkill", timeout_sec=5)
    assert bounded.status == ("resource-stopped" if enabled else "failure")
    assert bounded.returncode == -signal.SIGKILL
    assert "before kill" in bounded.stderr_path.read_text()
    assert bounded.message is not None and "before kill" in bounded.message
    assert ("unexpected SIGKILL (cause unknown)" in bounded.message) is enabled


def test_bounded_diagnostic_obeys_live_host_cap(guarded: None, monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    monkeypatch.setattr(memory_guard, "GROUP_LIMIT_BYTES", 1024)
    result = processes.run_bounded_command(
        [sys.executable, "-c", "import time; time.sleep(30)"], tmp_path, tmp_path / "guard", timeout_sec=5
    )
    assert result.status == "resource-stopped"
    assert result.message is not None and "safety cap" in result.message
    assert result.peak_rss_bytes > 1024
    assert result.stdout_path.exists() and result.stderr_path.exists()
