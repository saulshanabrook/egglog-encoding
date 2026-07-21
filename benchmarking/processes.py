"""Execute subprocesses and define their normalized result value objects.

This module owns wall/RSS accounting and process failure details. Workload
command construction and timing-summary parsing belong to their callers;
target materialization belongs in :mod:`benchmarking.targets`.
"""

from __future__ import annotations

import os
import resource
import signal
import subprocess
import sys
import tempfile
import threading
import time
from collections.abc import Mapping, Sequence
from contextlib import suppress
from dataclasses import dataclass
from pathlib import Path
from typing import TextIO

from .models import Status


@dataclass(frozen=True)
class TimingRow:
    """Wall time and peak memory measured for one child process."""

    wall_sec: float | None = None
    max_rss_bytes: int | None = None


@dataclass(frozen=True)
class ErrorRow:
    """Normalized child-process failure details."""

    message: str
    exit_code: int | None = None
    signal: int | None = None


@dataclass(frozen=True)
class TimingResult:
    """One completed, failed, or timed-out child-process result."""

    status: Status
    timing: TimingRow
    error: ErrorRow | None


def run_command(
    command: Sequence[str],
    checkout_path: Path,
    timeout_sec: int,
    env_overrides: Mapping[str, str] | None = None,
    required_output: str | Sequence[str] | None = None,
) -> TimingResult:
    env = os.environ.copy()
    env["RUST_LOG"] = "error"
    if env_overrides is not None:
        env.update(env_overrides)
    start = time.perf_counter()
    with (
        tempfile.TemporaryFile(mode="w+t", encoding="utf-8", errors="replace") as stdout_file,
        tempfile.TemporaryFile(mode="w+t", encoding="utf-8", errors="replace") as stderr_file,
    ):
        process = subprocess.Popen(
            command,
            cwd=checkout_path,
            env=env,
            text=True,
            stdout=stdout_file,
            stderr=stderr_file,
            start_new_session=True,
        )
        try:
            return_code, usage = wait4_process(process, timeout_sec)
        except subprocess.TimeoutExpired:
            return TimingResult(
                status="timed-out",
                timing=TimingRow(),
                error=ErrorRow(message=f"timed out after {timeout_sec} seconds"),
            )
        except BaseException:
            terminate_process_group(process)
            raise
        wall_sec = time.perf_counter() - start
        timing = timing_from_usage(usage, wall_sec)
        stdout = read_tempfile(stdout_file)
        stderr = read_tempfile(stderr_file)
    if return_code == 0 and required_output is not None:
        required_outputs = (required_output,) if isinstance(required_output, str) else tuple(required_output)
        combined_output = stdout + stderr
        missing_output = next((value for value in required_outputs if value not in combined_output), None)
        if missing_output is not None:
            return TimingResult(
                status="failure",
                timing=timing,
                error=ErrorRow(message=f"successful process output did not contain {missing_output!r}"),
            )
    if return_code == 0:
        return TimingResult(status="success", timing=timing, error=None)
    message = stderr.strip() or stdout.strip() or "process exited with non-zero status"
    exit_code = return_code if return_code >= 0 else None
    signal_number = -return_code if return_code < 0 else None
    return TimingResult(
        status="failure",
        timing=timing,
        error=ErrorRow(exit_code=exit_code, signal=signal_number, message=message[-1000:]),
    )


def terminate_process_group(process: subprocess.Popen[str] | subprocess.Popen[bytes]) -> None:
    """Kill and reap a command's isolated process group after an exceptional exit."""

    with suppress(ProcessLookupError):
        os.killpg(process.pid, signal.SIGKILL)
    process.wait()


def wait4_process(process: subprocess.Popen[str], timeout_sec: int) -> tuple[int, resource.struct_rusage]:
    """Wait without adding polling delay to the measured child wall time."""

    timed_out = threading.Event()
    finished = threading.Event()

    def expire() -> None:
        if finished.is_set():
            return
        timed_out.set()
        with suppress(ProcessLookupError):
            os.killpg(process.pid, signal.SIGKILL)

    timer = threading.Timer(timeout_sec, expire)
    try:
        timer.start()
        waited_pid, status, usage = os.wait4(process.pid, 0)
    finally:
        finished.set()
        timer.cancel()
        with suppress(RuntimeError):
            timer.join()
    assert waited_pid == process.pid
    return_code = os.waitstatus_to_exitcode(status)
    process.returncode = return_code
    if timed_out.is_set():
        raise subprocess.TimeoutExpired(process.args, timeout_sec)
    return return_code, usage


def read_tempfile(handle: TextIO) -> str:
    handle.seek(0)
    return handle.read()


def timing_from_usage(
    usage: resource.struct_rusage,
    wall_sec: float,
) -> TimingRow:
    return TimingRow(
        wall_sec=wall_sec,
        max_rss_bytes=ru_maxrss_to_bytes(usage.ru_maxrss),
    )


def ru_maxrss_to_bytes(ru_maxrss: int, platform: str = sys.platform) -> int | None:
    if ru_maxrss <= 0:
        return None
    if platform == "darwin":
        return ru_maxrss
    return ru_maxrss * 1024
