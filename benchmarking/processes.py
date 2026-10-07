"""Measure benchmark subprocesses and define their normalized result values.

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

from process_guard import MemoryGuard, terminate_process_group

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
    resource_stopped: bool = False


def run_command(
    command: Sequence[str],
    checkout_path: Path,
    timeout_sec: int,
    env_overrides: Mapping[str, str] | None = None,
    required_output: str | Sequence[str] | None = None,
) -> TimingResult:
    guard = MemoryGuard.from_environment()
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
        timed_out = False
        try:
            if guard is not None:
                guard.start(process.pid)
            return_code, usage = wait4_process(process, timeout_sec)
            wall_sec = time.perf_counter() - start
        except subprocess.TimeoutExpired:
            timed_out = True
        except BaseException:
            terminate_process_group(process)
            raise
        finally:
            if guard is not None:
                try:
                    guard.close()
                finally:
                    # A child may leave descendants behind even after wait4 returns.
                    terminate_process_group(process)
        post_exit_peak: int | None = None
        if guard is not None and not timed_out and guard.reason is None:
            peak = ru_maxrss_to_bytes(usage.ru_maxrss)
            if guard.check(peak or 0) is not None:
                post_exit_peak = peak
        if guard is not None and guard.reason is not None:
            action = "detected after workload exit" if post_exit_peak is not None else "stopped workload"
            return TimingResult(
                status="failure",
                timing=TimingRow(max_rss_bytes=post_exit_peak),
                error=ErrorRow(
                    message=f"resource guard {action}: {guard.reason}",
                    signal=-process.returncode if process.returncode is not None and process.returncode < 0 else None,
                ),
                resource_stopped=True,
            )
        if timed_out:
            return TimingResult(
                status="timed-out",
                timing=TimingRow(),
                error=ErrorRow(message=f"timed out after {timeout_sec} seconds"),
            )
        timing = timing_from_usage(usage, wall_sec)
        if return_code == 0:
            if required_output is not None:
                required = (required_output,) if isinstance(required_output, str) else required_output
                missing = missing_output((stdout_file, stderr_file), required)
                if missing is not None:
                    return TimingResult(
                        status="failure",
                        timing=timing,
                        error=ErrorRow(message=f"successful process output did not contain {missing!r}"),
                    )
            return TimingResult(status="success", timing=timing, error=None)
        message = read_error_tail(stderr_file) or read_error_tail(stdout_file) or "process exited with non-zero status"
    exit_code = return_code if return_code >= 0 else None
    signal_number = -return_code if return_code < 0 else None
    unexpected_kill = guard is not None and signal_number == signal.SIGKILL
    if unexpected_kill:
        message = f"resource guard halted collection after unexpected SIGKILL (cause unknown): {message[-850:]}"
    return TimingResult(
        status="failure",
        timing=timing,
        error=ErrorRow(exit_code=exit_code, signal=signal_number, message=message[-1000:]),
        resource_stopped=unexpected_kill,
    )


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


def missing_output(handles: Sequence[TextIO], required: Sequence[str]) -> str | None:
    """Scan concatenated logs with bounded reads, including boundary matches."""

    pending = set(required) - {""}
    overlap = max(map(len, pending), default=1) - 1
    suffix = ""
    for handle in handles:
        handle.seek(0)
        while pending and (chunk := handle.read(4096)):
            text = suffix + chunk
            pending.difference_update([value for value in pending if value in text])
            suffix = text[-overlap:] if overlap else ""
    return next((value for value in required if value in pending), None)


def read_error_tail(handle: TextIO) -> str:
    """Retain only the last 1,000 stripped characters, even with long whitespace."""

    handle.seek(0)
    raw_tail = tail = ""
    started = False
    while chunk := handle.read(4096):
        if not started:
            chunk = chunk.lstrip()
            started = bool(chunk)
        if trimmed := chunk.rstrip():
            tail = (raw_tail + trimmed)[-1000:]
        raw_tail = (raw_tail + chunk)[-1000:]
    return tail


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
