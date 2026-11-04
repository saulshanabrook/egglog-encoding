"""Memory policy and guarded subprocess integration, without campaign dependencies."""

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


def test_outer_guard_refuses_before_process_launch(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    monkeypatch.setenv("EGGLOG_BENCH_MEMORY_GUARD", "1")

    class RefusingGuard:
        @classmethod
        def from_environment(cls) -> None:
            assert os.environ["EGGLOG_BENCH_MEMORY_GUARD"] == "1"
            raise ValueError("resource guard refused to launch: unsafe host")

    monkeypatch.setattr(processes, "MemoryGuard", RefusingGuard, raising=False)
    monkeypatch.setattr(
        processes.subprocess,
        "Popen",
        lambda *args, **kwargs: pytest.fail("guard refusal must prevent process launch"),
    )
    with pytest.raises(ValueError, match="resource guard refused to launch"):
        processes.run_command([sys.executable, "-c", "pass"], tmp_path, 5)


def test_child_environment_override_does_not_activate_parent_guard(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    monkeypatch.delenv("EGGLOG_BENCH_MEMORY_GUARD", raising=False)
    parent_values = []

    class RecordingGuard:
        @classmethod
        def from_environment(cls) -> None:
            parent_values.append(os.environ.get("EGGLOG_BENCH_MEMORY_GUARD"))
            return None

    monkeypatch.setattr(processes, "MemoryGuard", RecordingGuard, raising=False)
    result = processes.run_command(
        [
            sys.executable,
            "-c",
            "import os; assert os.environ['EGGLOG_BENCH_MEMORY_GUARD'] == '1'",
        ],
        Path(tmp_path),
        5,
        env_overrides={"EGGLOG_BENCH_MEMORY_GUARD": "1"},
    )
    assert result.status == "success"
    assert parent_values == [None]


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
    assert not list(tmp_path.iterdir())


def test_unavailable_host_monitor_prevents_launch(
    guarded: None, monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    def unavailable() -> tuple[int, int]:
        raise OSError("vm_stat unavailable")

    monkeypatch.setattr(memory_guard, "host_memory", unavailable)
    with pytest.raises(ValueError, match="memory monitoring failed: vm_stat unavailable"):
        processes.run_command(["unused"], tmp_path, 5)


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


@pytest.mark.parametrize("setting", [None, "", "0", "true"])
def test_parent_guard_policy_is_explicit(monkeypatch: pytest.MonkeyPatch, setting: str | None) -> None:
    if setting is None:
        monkeypatch.delenv("EGGLOG_BENCH_MEMORY_GUARD", raising=False)
    else:
        monkeypatch.setenv("EGGLOG_BENCH_MEMORY_GUARD", setting)
    if setting in (None, ""):
        assert memory_guard.MemoryGuard.from_environment() is None
    else:
        with pytest.raises(ValueError, match="must be unset or 1"):
            memory_guard.MemoryGuard.from_environment()
