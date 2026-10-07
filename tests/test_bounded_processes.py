"""Bounded diagnostics retain logs and clean every owned process group."""

from __future__ import annotations

import os
import signal
import subprocess
import sys
import time
from pathlib import Path
from types import SimpleNamespace
from typing import Any

import pytest

from scripts import reproduction_process as processes


@pytest.mark.parametrize("mode", ["default", "sample-error", "cleanup-error", "immediate-exit", "cleanup-interrupt"])
def test_optional_descendant_hooks_always_preserve_root_cleanup(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, mode: str
) -> None:
    events: list[Any] = []
    polls = iter([0] if mode == "immediate-exit" else [None, 0])
    process = SimpleNamespace(pid=123, returncode=0, poll=lambda: next(polls), wait=lambda: events.append("wait"))
    monkeypatch.setattr(processes.subprocess, "Popen", lambda *_args, **_kwargs: process)
    exits = iter([SimpleNamespace(si_pid=123)] if mode == "immediate-exit" else [None, SimpleNamespace(si_pid=123)])
    monkeypatch.setattr(processes.os, "waitid", lambda *_: next(exits), raising=False)
    monkeypatch.setattr(processes.MemoryGuard, "from_environment", lambda **_: None)

    def default_sample(pid: int) -> int:
        events.append(("default-rss", pid))
        return 5

    monkeypatch.setattr(processes, "group_rss_bytes", default_sample)
    monkeypatch.setattr(processes.os, "killpg", lambda *args: events.append(("killpg", *args)))
    monkeypatch.setattr(processes.time, "sleep", lambda _: None)

    def sample(pid: int) -> int:
        events.append(("custom-rss", pid))
        if mode == "sample-error":
            raise RuntimeError("custom monitor failed")
        return 7

    def cleanup() -> None:
        events.append("descendant-cleanup")
        if mode == "cleanup-error":
            raise RuntimeError("custom cleanup failed")
        if mode == "cleanup-interrupt":
            raise KeyboardInterrupt

    kwargs: dict[str, Any] = {} if mode == "default" else {"sample_rss": sample, "cleanup_descendants": cleanup}
    if mode == "cleanup-interrupt":
        with pytest.raises(KeyboardInterrupt):
            processes.run_bounded_command(["never-executed"], tmp_path, tmp_path / "output", **kwargs)
    else:
        result = processes.run_bounded_command(["never-executed"], tmp_path, tmp_path / "output", **kwargs)
        if mode in {"sample-error", "cleanup-error"}:
            assert result.status == "resource-stopped" and "failed" in str(result.message)
        else:
            assert result.status == "success"
    assert events[-2:] == [("killpg", 123, signal.SIGKILL), "wait"]
    if mode == "default":
        assert events[0] == ("default-rss", 123) and "descendant-cleanup" not in events
    else:
        assert "descendant-cleanup" in events
    if mode == "immediate-exit":
        assert not any(isinstance(event, tuple) and event[0] == "custom-rss" for event in events)


@pytest.mark.parametrize("failure", [None, "waitid", "cleanup", "interrupt"])
def test_scoped_cleanup_retains_root_identity_and_stops_root_before_drain(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, failure: str | None
) -> None:
    events: list[Any] = []
    process = SimpleNamespace(
        pid=123, returncode=None, poll=lambda: pytest.fail("custom cleanup must not reap with poll")
    )

    def wait() -> int:
        events.append("wait")
        process.returncode = 7
        return 7

    process.wait = wait
    monkeypatch.setattr(processes.subprocess, "Popen", lambda *_a, **_k: process)
    monkeypatch.setattr(processes.MemoryGuard, "from_environment", lambda **_: None)
    monkeypatch.setattr(processes.os, "killpg", lambda *args: events.append(("kill", *args)))

    def waitid(kind: int, pid: int, flags: int) -> Any:
        events.append(("waitid", kind, pid, flags))
        assert flags & processes.os.WNOWAIT
        if failure == "waitid":
            raise OSError("cannot observe root")
        return SimpleNamespace(si_pid=pid)

    monkeypatch.setattr(processes.os, "waitid", waitid, raising=False)

    def cleanup() -> None:
        events.append("drain")
        if failure == "cleanup":
            raise ValueError("cleanup failed")
        if failure == "interrupt":
            raise KeyboardInterrupt

    if failure == "interrupt":
        with pytest.raises(KeyboardInterrupt):
            processes.run_bounded_command(["fake"], tmp_path, tmp_path / "run", cleanup_descendants=cleanup)
    else:
        result = processes.run_bounded_command(["fake"], tmp_path, tmp_path / "run", cleanup_descendants=cleanup)
        assert result.returncode == 7  # Actual final wait, never the waitid status.
        assert result.status == ("resource-stopped" if failure else "failure")
    assert events[1:] == [("kill", 123, signal.SIGKILL), "drain", ("kill", 123, signal.SIGKILL), "wait"]


def test_scoped_cleanup_requires_wnowait_before_spawning(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.delattr(processes.os, "WNOWAIT")
    monkeypatch.setattr(
        processes.subprocess, "Popen", lambda *_a, **_k: pytest.fail("unsupported guard must not spawn")
    )
    with pytest.raises(ValueError, match="non-consuming root exit"):
        processes.run_bounded_command(["fake"], tmp_path, tmp_path / "run", cleanup_descendants=lambda: None)


def test_default_runner_still_propagates_unexpected_monitor_bug(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    events = []
    process = SimpleNamespace(pid=123, returncode=None, poll=lambda: None, wait=lambda: events.append("wait"))
    monkeypatch.setattr(processes.subprocess, "Popen", lambda *_a, **_kw: process)
    monkeypatch.setattr(processes.MemoryGuard, "from_environment", lambda **_: SimpleNamespace(check=lambda _: None))
    monkeypatch.setattr(processes.os, "killpg", lambda *_: events.append("kill"))

    def broken(_pid: int) -> int:
        raise RuntimeError("unexpected implementation bug")

    monkeypatch.setattr(processes, "group_rss_bytes", broken)
    with pytest.raises(RuntimeError, match="unexpected implementation bug"):
        processes.run_bounded_command(["fake"], tmp_path, tmp_path / "run")
    assert events == ["kill", "wait"]


@pytest.mark.parametrize(
    "group",
    [
        "empty",
        "zombie",
        "unrelated-live",
        "live-child",
        "unknown-state",
        "malformed",
        "duplicate",
        "monitor-error",
        "root-running",
        "wrong-root",
        "linux",
    ],
)
def test_permission_error_is_waived_only_for_confirmed_exited_empty_macos_group(
    monkeypatch: pytest.MonkeyPatch, group: str
) -> None:
    monkeypatch.setattr(processes.sys, "platform", "linux" if group == "linux" else "darwin")

    def denied(*_args: Any) -> None:
        raise PermissionError(1, "Operation not permitted")

    monkeypatch.setattr(processes.os, "killpg", denied)

    def exited(_kind: int, pid: int, flags: int) -> Any:
        assert flags & processes.os.WNOWAIT
        return None if group == "root-running" else SimpleNamespace(si_pid=999 if group == "wrong-root" else pid)

    monkeypatch.setattr(processes.os, "waitid", exited, raising=False)
    snapshots = {
        "empty": "",
        "zombie": "123 123 Z\n",
        "unrelated-live": "123 123 Z+\n999 999 R\n",
        "live-child": "123 123 Z\n124 123 S\n",
        "unknown-state": "123 123 ?\n",
        "malformed": "123 123\n",
        "duplicate": "123 123 Z\n123 123 Z\n",
    }

    def snapshot(*args: Any, **kwargs: Any) -> Any:
        assert args == (["ps", "-axo", "pid=,pgid=,stat="],) and kwargs["check"] and kwargs["timeout"] == 1
        if group == "monitor-error":
            raise OSError("monitor unavailable")
        if group not in snapshots:
            pytest.fail("unconfirmed root must not waive EPERM using telemetry")
        return SimpleNamespace(stdout=snapshots[group])

    monkeypatch.setattr(processes.subprocess, "run", snapshot)
    if group in {"empty", "zombie", "unrelated-live"}:
        processes._kill_retained_root_group(123)
    else:
        with pytest.raises((PermissionError, OSError, ValueError)):
            processes._kill_retained_root_group(123)


@pytest.mark.parametrize("failed_signals", [{1}, {2}, {1, 2}])
@pytest.mark.parametrize("callback_fails", [False, True])
def test_signal_failures_cannot_skip_callback_or_wait_and_remain_failures(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, failed_signals: set[int], callback_fails: bool
) -> None:
    events: list[str] = []
    process = SimpleNamespace(pid=123, returncode=None, poll=lambda: pytest.fail("must retain root"))

    def wait() -> int:
        events.append("wait")
        process.returncode = 0
        return 0

    process.wait = wait
    monkeypatch.setattr(processes.subprocess, "Popen", lambda *_a, **_k: process)
    monkeypatch.setattr(processes.MemoryGuard, "from_environment", lambda **_: None)
    monkeypatch.setattr(processes.os, "waitid", lambda *_: SimpleNamespace(si_pid=123), raising=False)
    count = 0

    def signal_root(_pid: int) -> None:
        nonlocal count
        count += 1
        events.append(f"signal{count}")
        if count in failed_signals:
            raise PermissionError(1, f"denied phase {count}")

    monkeypatch.setattr(processes, "_kill_retained_root_group", signal_root)

    def cleanup() -> None:
        events.append("callback")
        if callback_fails:
            raise ValueError("callback failure")

    result = processes.run_bounded_command(["fake"], tmp_path, tmp_path / "run", cleanup_descendants=cleanup)
    assert events == ["signal1", "callback", "signal2", "wait"]
    assert result.status == "resource-stopped" and result.returncode == 0
    for number in failed_signals:
        assert f"denied phase {number}" in str(result.message)
    assert ("callback failure" in str(result.message)) is callback_fails


@pytest.mark.parametrize("interrupted_signal", [1, 2])
def test_signal_interruption_still_runs_callback_and_final_wait(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, interrupted_signal: int
) -> None:
    events: list[str] = []
    process = SimpleNamespace(pid=123, returncode=0, wait=lambda: events.append("wait"))
    monkeypatch.setattr(processes.subprocess, "Popen", lambda *_a, **_k: process)
    monkeypatch.setattr(processes.MemoryGuard, "from_environment", lambda **_: None)
    monkeypatch.setattr(processes.os, "waitid", lambda *_: SimpleNamespace(si_pid=123), raising=False)
    count = 0

    def signal_root(_pid: int) -> None:
        nonlocal count
        count += 1
        events.append(f"signal{count}")
        if count == interrupted_signal:
            raise KeyboardInterrupt

    monkeypatch.setattr(processes, "_kill_retained_root_group", signal_root)
    with pytest.raises(KeyboardInterrupt):
        processes.run_bounded_command(
            ["fake"], tmp_path, tmp_path / "run", cleanup_descendants=lambda: events.append("callback")
        )
    assert events == ["signal1", "callback", "signal2", "wait"]


def test_bounded_process_timeout_kills_descendants_and_retains_logs(tmp_path: Path) -> None:
    pid_path = tmp_path / "child.pid"
    command = [
        sys.executable,
        "-c",
        "import subprocess,sys,time,pathlib; "
        "p=subprocess.Popen([sys.executable,'-c','import time; time.sleep(30)']); "
        "pathlib.Path(sys.argv[1]).write_text(str(p.pid)); print('started',flush=True); time.sleep(30)",
        str(pid_path),
    ]
    result = processes.run_bounded_command(command, tmp_path, tmp_path / "timeout", timeout_sec=0.5)
    assert result.status == "timed-out"
    assert result.wall_sec < 5
    assert result.stdout_path.read_text().strip() == "started"
    pid = int(pid_path.read_text())
    for _ in range(30):
        child = subprocess.run(["ps", "-p", str(pid), "-o", "stat="], capture_output=True, text=True)
        if not child.stdout.strip() or child.stdout.strip().startswith("Z"):
            break
        time.sleep(0.01)
    else:
        os.kill(pid, 9)
        pytest.fail("bounded timeout left a descendant alive")


def test_bounded_process_enforces_small_rss_threshold(tmp_path: Path) -> None:
    result = processes.run_bounded_command(
        [sys.executable, "-c", "import time; data=bytearray(4*1024*1024); time.sleep(30)"],
        tmp_path,
        tmp_path / "memory",
        timeout_sec=5,
        memory_limit_bytes=1024,
    )
    assert result.status == "memory-limit"
    assert result.peak_rss_bytes > 1024
    assert result.wall_sec < 5


@pytest.mark.parametrize("stream", ["stdout", "stderr", "combined"])
def test_output_limit_kills_descendants_and_retains_partial_logs(tmp_path: Path, stream: str) -> None:
    pid_path = tmp_path / "child.pid"
    stdout_bytes, stderr_bytes = {"stdout": (3072, 0), "stderr": (0, 3072), "combined": (1536, 1536)}[stream]
    command = [
        sys.executable,
        "-c",
        "import os,pathlib,subprocess,sys,time; "
        "p=subprocess.Popen([sys.executable,'-c','import time; time.sleep(30)']); "
        "pathlib.Path(sys.argv[1]).write_text(str(p.pid)); "
        f"os.write(1,b'o'*{stdout_bytes}); os.write(2,b'e'*{stderr_bytes}); time.sleep(30)",
        str(pid_path),
    ]
    result = processes.run_bounded_command(
        command, tmp_path, tmp_path / "output", timeout_sec=5, output_limit_bytes=2048
    )
    assert result.status == "output-limit"
    assert result.returncode == -signal.SIGKILL
    assert result.message == "combined stdout/stderr output exceeded the 2048-byte limit"
    assert result.wall_sec < 5
    assert result.stdout_path.stat().st_size <= stdout_bytes
    assert result.stderr_path.stat().st_size <= stderr_bytes
    assert result.stdout_path.stat().st_size + result.stderr_path.stat().st_size == 2048
    pid = int(pid_path.read_text())
    for _ in range(30):
        child = subprocess.run(["ps", "-p", str(pid), "-o", "stat="], capture_output=True, text=True)
        if not child.stdout.strip() or child.stdout.strip().startswith("Z"):
            break
        time.sleep(0.01)
    else:
        os.kill(pid, signal.SIGKILL)
        pytest.fail("output limit left a descendant alive")


@pytest.mark.parametrize("output_bytes", [2048, 2049])
def test_final_output_size_is_checked_after_successful_exit(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, output_bytes: int
) -> None:
    def launch(*_args: Any, **kwargs: Any) -> Any:
        writer = os.dup(kwargs["stdout"].fileno())

        def poll() -> int:
            # Simulate output arriving after the loop's sample, just before exit.
            os.write(writer, b"x" * output_bytes)
            os.close(writer)
            return 0

        return SimpleNamespace(pid=123, returncode=0, poll=poll, wait=lambda: 0)

    monkeypatch.setattr(processes.subprocess, "Popen", launch)
    monkeypatch.setattr(processes.os, "killpg", lambda *_: None)
    result = processes.run_bounded_command(["fake"], tmp_path, tmp_path / "output", output_limit_bytes=2048)
    assert result.returncode == 0
    assert result.status == ("output-limit" if output_bytes > 2048 else "success")
    assert result.stdout_path.stat().st_size == min(output_bytes, 2048)


@pytest.mark.parametrize("stream", [1, 2])
def test_single_large_write_cannot_exceed_retained_output_limit(tmp_path: Path, stream: int) -> None:
    result = processes.run_bounded_command(
        [sys.executable, "-c", f"import os; os.write({stream}, b'x'*(8*1024*1024))"],
        tmp_path,
        tmp_path / "single-write",
        timeout_sec=5,
        output_limit_bytes=32 * 1024,
    )
    assert result.status == "output-limit"
    assert result.wall_sec < 5
    assert result.stdout_path.stat().st_size + result.stderr_path.stat().st_size == 32 * 1024


@pytest.mark.parametrize("output_limit", [32 * 1024, 3 * 1024 * 1024])
def test_simultaneous_stdout_and_stderr_are_drained_without_deadlock(tmp_path: Path, output_limit: int) -> None:
    result = processes.run_bounded_command(
        [
            sys.executable,
            "-c",
            "import os,threading; "
            "threads=[threading.Thread(target=os.write,args=(fd,b'x'*(1024*1024))) for fd in (1,2)]; "
            "[t.start() for t in threads]; [t.join() for t in threads]",
        ],
        tmp_path,
        tmp_path / "concurrent",
        timeout_sec=5,
        output_limit_bytes=output_limit,
    )
    assert result.status == ("output-limit" if output_limit < 2 * 1024 * 1024 else "success")
    assert result.stdout_path.stat().st_size + result.stderr_path.stat().st_size == min(output_limit, 2 * 1024**2)
    assert result.wall_sec < 5
    if result.status == "success":
        assert result.stdout_path.read_bytes() == result.stderr_path.read_bytes() == b"x" * (1024 * 1024)


def test_output_limit_still_runs_detached_descendant_cleanup(tmp_path: Path) -> None:
    pid_path = tmp_path / "detached.pid"
    cleaned = []

    def cleanup() -> None:
        pid = int(pid_path.read_text())
        os.killpg(pid, signal.SIGKILL)
        for _ in range(30):
            child = subprocess.run(["ps", "-p", str(pid), "-o", "stat="], capture_output=True, text=True)
            if not child.stdout.strip() or child.stdout.strip().startswith("Z"):
                break
            time.sleep(0.01)
        else:
            pytest.fail("cleanup left a detached descendant alive")
        cleaned.append(pid)

    result = processes.run_bounded_command(
        [
            sys.executable,
            "-c",
            "import os,pathlib,subprocess,sys,time; "
            "child=subprocess.Popen([sys.executable,'-c','import time; time.sleep(30)'],start_new_session=True); "
            "pathlib.Path(sys.argv[1]).write_text(str(child.pid)); os.write(1,b'x'*(1024*1024)); time.sleep(30)",
            str(pid_path),
        ],
        tmp_path,
        tmp_path / "detached",
        timeout_sec=5,
        output_limit_bytes=2048,
        cleanup_descendants=cleanup,
    )
    assert result.status == "output-limit", result.message
    assert cleaned == [int(pid_path.read_text())]
    assert result.stdout_path.stat().st_size == 2048
    assert result.wall_sec < 5


def test_capture_failure_stops_the_process_and_reports_the_error(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    def broken_selector() -> Any:
        raise OSError("cannot monitor output pipes")

    monkeypatch.setattr(processes.selectors, "DefaultSelector", broken_selector)
    result = processes.run_bounded_command(
        [sys.executable, "-c", "import time; time.sleep(30)"], tmp_path, tmp_path / "capture-error", timeout_sec=5
    )
    assert result.status == "resource-stopped"
    assert result.returncode == -signal.SIGKILL
    assert result.message == "output capture failed: cannot monitor output pipes"
    assert result.wall_sec < 5


@pytest.mark.parametrize("output_limit", [0, -1])
def test_nonpositive_output_limit_is_rejected_before_launch(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, output_limit: int
) -> None:
    monkeypatch.setattr(processes.subprocess, "Popen", lambda *_a, **_k: pytest.fail("must not launch"))
    with pytest.raises(ValueError, match="output limit must be positive"):
        processes.run_bounded_command(["fake"], tmp_path, tmp_path / "output", output_limit_bytes=output_limit)
