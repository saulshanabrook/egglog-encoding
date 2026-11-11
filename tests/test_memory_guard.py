"""Protect the host without fabricating observations or masking campaign stops."""

from __future__ import annotations

import io
import resource
import signal
import subprocess
import sys
from pathlib import Path
from typing import Any

import pytest

import process_guard as memory_guard
from benchmarking import processes
from scripts import reproduction_process


@pytest.fixture
def guarded(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setenv("EGGLOG_BENCH_MEMORY_GUARD", "1")


def test_guard_preserves_successful_timing(guarded: None, tmp_path: Path) -> None:
    result = processes.run_command([sys.executable, "-c", "print('ok')"], tmp_path, 5)
    assert result.status == "success"
    assert result.timing.wall_sec is not None
    assert result.timing.max_rss_bytes is not None
    assert not result.resource_stopped


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
    assert bounded.status == "resource-stopped"
    assert bounded.returncode == -signal.SIGKILL
    assert "before kill" in bounded.stderr_path.read_text()
    assert bounded.message is not None and "before kill" in bounded.message
    assert "unexpected SIGKILL (cause unknown)" in bounded.message


@pytest.mark.parametrize("enabled", [False, True])
def test_controlled_launch_normalizes_allocator_policy_and_limits_only_when_guarded(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, enabled: bool
) -> None:
    monkeypatch.setenv("EGGLOG_BENCH_MEMORY_GUARD", "1" if enabled else "")
    monkeypatch.setenv("MIMALLOC_DISALLOW_ARENA_ALLOC", "0")
    script = tmp_path / "engine"
    script.write_text(
        f"#!{sys.executable}\n"
        "import os,sys,json\n"
        "env={k:v for k,v in os.environ.items() if k.startswith('MIMALLOC_')}\n"
        "print(json.dumps({'args':sys.argv[1:],'env':env}))\n"
    )
    script.chmod(0o755)
    expected_flag = f"--memory-limit-bytes={memory_guard.NATIVE_LIMIT_BYTES}"
    required = [f'"{key}": "{value}"' for key, value in memory_guard.NATIVE_ALLOCATOR_ENV.items()]
    required.append(expected_flag if enabled else '"args": []')
    result = processes.run_command([str(script)], tmp_path, 5, required_output=required, native_limit=True)
    assert result.status == "success"


@pytest.mark.parametrize(
    ("code", "message", "stopped"),
    [
        (86, memory_guard.NATIVE_ALLOCATION_FAILURE, False),
        (86, "native memory limit: allocation failed under limit", True),
        (86, "native memory limit: setup failed", True),
        (2, "unexpected argument '--memory-limit-bytes=123' found", True),
        (101, "mmap failed to allocate stack: Cannot allocate memory", True),
        (101, "ordinary proof check failure", False),
    ],
)
def test_native_allocation_failure_is_local_but_setup_failures_stop_collection(
    guarded: None, tmp_path: Path, code: int, message: str, stopped: bool
) -> None:
    script = tmp_path / "engine"
    script.write_text(f"#!{sys.executable}\nimport sys\nprint({message!r},file=sys.stderr)\nsys.exit({code})\n")
    script.chmod(0o755)
    measured = processes.run_command([str(script)], tmp_path, 5, native_limit=True)
    assert measured.status == "failure" and measured.resource_stopped is stopped
    assert measured.error is not None and measured.error.message == message
    diagnostic = reproduction_process.run_bounded_command(
        [str(script)], tmp_path, tmp_path / "diagnostic", timeout_sec=5, native_limit=True
    )
    assert diagnostic.status == (
        "memory-limit"
        if message == memory_guard.NATIVE_ALLOCATION_FAILURE
        else "resource-stopped"
        if stopped
        else "failure"
    )
    assert diagnostic.message == message


def test_native_request_fails_closed_on_unsupported_platform(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(memory_guard.sys, "platform", "unsupported")
    with pytest.raises(memory_guard.ResourceStopped, match="requires macOS or Linux"):
        memory_guard.native_memory_command(["never-launched"], {}, memory_guard.NATIVE_LIMIT_BYTES)


def test_measured_allocation_failure_retains_reason_beyond_error_tail(guarded: None, tmp_path: Path) -> None:
    script = tmp_path / "engine"
    script.write_text(
        f"#!{sys.executable}\nimport sys\n"
        f"print({memory_guard.NATIVE_ALLOCATION_FAILURE!r},file=sys.stderr)\n"
        "print('extra diagnostic\\n' * 1000,file=sys.stderr)\nsys.exit(86)\n"
    )
    script.chmod(0o755)
    result = processes.run_command([str(script)], tmp_path, 5, native_limit=True)
    assert result.status == "failure" and not result.resource_stopped
    assert result.error is not None and result.error.message == memory_guard.NATIVE_ALLOCATION_FAILURE


def test_diagnostics_limit_only_controlled_native_commands(tmp_path: Path) -> None:
    script = tmp_path / "engine"
    script.write_text(f"#!{sys.executable}\nimport sys\nprint(' '.join(sys.argv[1:]))\n")
    script.chmod(0o755)
    for native in (False, True):
        result = reproduction_process.run_bounded_command(
            [str(script), "workload"],
            tmp_path,
            tmp_path / str(native),
            timeout_sec=5,
            native_limit=native,
        )
        assert result.status == "success"
        expected = f"--memory-limit-bytes={memory_guard.NATIVE_LIMIT_BYTES} workload\n" if native else "workload\n"
        assert result.stdout_path.read_text() == expected


def test_native_resource_failure_survives_backtrace_and_chunk_boundary() -> None:
    class BoundedLog(io.StringIO):
        def read(self, size: int | None = -1) -> str:
            assert size == 4096
            return super().read(size)

    log = BoundedLog("x" * 4090 + "mmap failed to allocate stack: Cannot allocate memory\n" + "trace\n" * 5000)
    assert memory_guard.native_resource_failure(101, log, True)
    assert not memory_guard.native_resource_failure(101, log, False)


@pytest.mark.parametrize("diagnostic", [False, True])
def test_process_supervision_never_polls_rss(
    guarded: None, monkeypatch: pytest.MonkeyPatch, tmp_path: Path, diagnostic: bool
) -> None:
    original_run = subprocess.run
    polls: list[list[str]] = []

    def snapshot(command: list[str], **kwargs: Any) -> subprocess.CompletedProcess[str]:
        if command[0] == "ps" and any("rss" in arg for arg in command):
            polls.append(command)
        return original_run(command, **kwargs)

    monkeypatch.setattr(memory_guard.subprocess, "run", snapshot)
    command = [sys.executable, "-c", "import time; time.sleep(0.1)"]
    if diagnostic:
        result = reproduction_process.run_bounded_command(command, tmp_path, tmp_path / "no-rss", timeout_sec=5)
        assert result.status == "success"
    else:
        measured = processes.run_command(command, tmp_path, 5)
        assert measured.status == "success"
    assert not polls


def test_peak_rss_is_preserved_as_measurement_without_a_cap(
    guarded: None, monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    original_wait4 = processes.wait4_process
    peak = 20 * 1024**3  # Synthetic wait4 evidence, never an actual allocation.

    def measured_peak(process: subprocess.Popen[str], timeout_sec: float) -> tuple[int, resource.struct_rusage]:
        code, usage = original_wait4(process, timeout_sec)
        values = list(usage)
        values[2] = peak if sys.platform == "darwin" else peak // 1024
        return code, resource.struct_rusage(values)

    monkeypatch.setattr(processes, "wait4_process", measured_peak)
    result = processes.run_command([sys.executable, "-c", "pass"], tmp_path, 5)
    assert result.status == "success" and not result.resource_stopped
    assert result.timing.max_rss_bytes == peak


@pytest.mark.parametrize("value", ["0", "true", "invalid"])
def test_native_limit_environment_is_validated(monkeypatch: pytest.MonkeyPatch, value: str) -> None:
    monkeypatch.setenv("EGGLOG_BENCH_MEMORY_GUARD", value)
    with pytest.raises(ValueError, match="must be unset or 1"):
        memory_guard.native_limit_enabled()
