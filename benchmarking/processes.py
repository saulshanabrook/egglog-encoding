"""Execute subprocesses and define their normalized result value objects.

This module owns wall/RSS accounting and process failure details. Workload
command construction and timing-summary parsing belong to their callers;
target materialization belongs in :mod:`benchmarking.targets`.
"""

from __future__ import annotations

import os
import resource
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
import time
from collections.abc import Callable, Mapping, Sequence
from contextlib import suppress
from dataclasses import dataclass
from pathlib import Path
from typing import Literal, TextIO

from .memory_guard import GROUP_LIMIT_BYTES, MemoryGuard, group_rss_bytes
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


def terminate_process_group(process: subprocess.Popen[str] | subprocess.Popen[bytes]) -> None:
    """Kill and reap a command's isolated process group after an exceptional exit."""

    try:
        with suppress(ProcessLookupError):
            os.killpg(process.pid, signal.SIGKILL)
    except PermissionError:
        # A redundant signal can race with orphan/zombie cleanup on macOS.
        # Accept it only after the owned parent exited and no live members remain.
        if process.poll() is None:
            raise
        snapshot = subprocess.run(["ps", "-axo", "pgid=,stat="], check=True, capture_output=True, text=True, timeout=1)
        states = (line.split() for line in snapshot.stdout.splitlines() if line.strip())
        if any(int(group) == process.pid and not state.startswith("Z") for group, state in states):
            raise
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


@dataclass(frozen=True)
class PilotProcessResult:
    status: Literal["success", "failure", "timed-out", "memory-limit", "resource-stopped"]
    returncode: int | None
    wall_sec: float
    peak_rss_bytes: int
    stdout_path: Path
    stderr_path: Path
    message: str | None


def _kill_retained_root_group(pid: int) -> None:
    """Signal an unreaped root group; verify macOS's zombie-only EPERM case.

    The caller must retain this child with WNOWAIT until its final wait. Never
    waive EPERM by errno alone: both child exit and absence of live group members
    must be observed successfully while the root PID is still reserved.
    """
    try:
        os.killpg(pid, signal.SIGKILL)
    except ProcessLookupError:
        return
    except PermissionError as signal_error:
        if sys.platform != "darwin":
            raise
        exited = getattr(os, "waitid")(os.P_PID, pid, os.WEXITED | os.WNOHANG | os.WNOWAIT)  # noqa: B009
        if exited is None or exited.si_pid != pid:
            raise
        snapshot = subprocess.run(
            ["ps", "-axo", "pid=,pgid=,stat="], capture_output=True, text=True, check=True, timeout=1
        )
        seen = set()
        for line in snapshot.stdout.splitlines():
            columns = line.split()
            if len(columns) != 3:
                raise ValueError("Incomplete retained-root group membership snapshot") from signal_error
            member, group = map(int, columns[:2])
            if member in seen or member < 0 or group < 0:
                raise ValueError("Ambiguous retained-root group membership snapshot") from signal_error
            seen.add(member)
            if group == pid and not columns[2].startswith("Z"):
                raise


def run_bounded_command(
    command: Sequence[str],
    cwd: Path,
    output_prefix: Path,
    *,
    timeout_sec: float = 120,
    memory_limit_bytes: int = GROUP_LIMIT_BYTES,
    require_guard: bool = False,
    disk_reserve_bytes: int = 0,
    sample_rss: Callable[[int], int] | None = None,
    cleanup_descendants: Callable[[], None] | None = None,
) -> PilotProcessResult:
    """Monitor an isolated process group's aggregate RSS and retain disk logs.

    RSS is sampled every 50 ms, so the threshold is a monitored guard rather
    than a kernel allocation limit. All surviving group members are killed
    when the parent exits, a limit is crossed, or the caller is interrupted.
    """

    if timeout_sec <= 0 or memory_limit_bytes <= 0:
        raise ValueError("bounded process timeout and memory limit must be positive")
    if cleanup_descendants is not None and not all(
        hasattr(os, name) for name in ("waitid", "P_PID", "WEXITED", "WNOHANG", "WNOWAIT")
    ):
        raise ValueError("descendant cleanup requires non-consuming root exit observation (waitid/WNOWAIT)")
    guard = MemoryGuard() if require_guard else MemoryGuard.from_environment()
    if guard is not None and (reason := guard.check(0)):
        raise ValueError(f"resource guard refused to launch a workload: {reason}")
    if disk_reserve_bytes and shutil.disk_usage(cwd).free < disk_reserve_bytes:
        raise ValueError(f"disk guard refused to launch: fewer than {disk_reserve_bytes} bytes free")
    output_prefix.parent.mkdir(parents=True, exist_ok=True)
    stdout_path = Path(str(output_prefix) + ".stdout.log")
    stderr_path = Path(str(output_prefix) + ".stderr.log")
    start = time.monotonic()
    peak_rss = 0
    status: Literal["success", "failure", "timed-out", "memory-limit", "resource-stopped"] = "success"
    message: str | None = None
    env = os.environ.copy()
    env["RUST_LOG"] = "error"
    with stdout_path.open("wb") as stdout, stderr_path.open("wb") as stderr:
        process = subprocess.Popen(command, cwd=cwd, env=env, stdout=stdout, stderr=stderr, start_new_session=True)
        try:
            while True:
                if cleanup_descendants is None:
                    if process.poll() is not None:
                        break
                else:
                    # Keep the root PID unreaped through group cleanup. A poll()
                    # here would permit PID/PGID reuse during detached drain.
                    try:
                        # Typeshed omits this macOS API; availability is checked above.
                        exited = getattr(os, "waitid")(  # noqa: B009
                            os.P_PID, process.pid, os.WEXITED | os.WNOHANG | os.WNOWAIT
                        )
                    except Exception as error:
                        status = "resource-stopped"
                        message = f"root exit monitoring failed: {error}"
                        break
                    if exited is not None and exited.si_pid == process.pid:
                        break
                # Both macOS and Linux expose RSS in KiB through ps. Monitoring
                # the session's group includes descendants spawned by a driver.
                try:
                    rss = (sample_rss or group_rss_bytes)(process.pid)
                except Exception as error:
                    if sample_rss is None and (
                        guard is None or not isinstance(error, (OSError, ValueError, subprocess.SubprocessError))
                    ):
                        raise
                    status = "resource-stopped"
                    message = f"memory monitoring failed: {error}"
                    break
                peak_rss = max(peak_rss, rss)
                if disk_reserve_bytes:
                    try:
                        free_disk = shutil.disk_usage(cwd).free
                    except OSError as error:
                        status = "resource-stopped"
                        message = f"disk monitoring failed: {error}"
                        break
                    if free_disk < disk_reserve_bytes:
                        status = "resource-stopped"
                        message = f"free disk fell below the {disk_reserve_bytes}-byte reserve"
                        break
                if guard is not None and (reason := guard.check(rss)) is not None:
                    status = "resource-stopped"
                    message = reason
                    break
                if rss > memory_limit_bytes:
                    status = "memory-limit"
                    message = f"process-group RSS exceeded {memory_limit_bytes} bytes"
                    break
                if time.monotonic() - start >= timeout_sec:
                    status = "timed-out"
                    message = f"timed out after {timeout_sec:g} seconds"
                    break
                time.sleep(min(0.05, max(0, timeout_sec - (time.monotonic() - start))))
        finally:
            if cleanup_descendants is None:
                with suppress(ProcessLookupError):
                    os.killpg(process.pid, signal.SIGKILL)
                process.wait()
            else:
                cleanup_errors = []
                try:
                    try:
                        _kill_retained_root_group(process.pid)
                    except Exception as error:
                        cleanup_errors.append(f"initial root signal failed: {type(error).__name__}: {error}")
                    finally:
                        try:
                            cleanup_descendants()
                        except Exception as error:
                            cleanup_errors.append(f"descendant cleanup failed: {type(error).__name__}: {error}")
                finally:
                    try:
                        _kill_retained_root_group(process.pid)
                    except Exception as error:
                        cleanup_errors.append(f"final root signal failed: {type(error).__name__}: {error}")
                    finally:
                        process.wait()
                if cleanup_errors:
                    status = "resource-stopped"
                    previous = f"{message}; " if message else ""
                    message = previous + "; ".join(cleanup_errors)
    if status == "success" and process.returncode != 0:
        status = "failure"
        with stderr_path.open("rb") as log:
            log.seek(max(0, stderr_path.stat().st_size - 4000))
            message = log.read().decode("utf-8", errors="replace").strip()
        message = message or f"process exited with status {process.returncode}"
        if guard is not None and process.returncode == -signal.SIGKILL:
            status = "resource-stopped"
            message = f"resource guard halted diagnostic after unexpected SIGKILL (cause unknown): {message}"
    return PilotProcessResult(
        status, process.returncode, time.monotonic() - start, peak_rss, stdout_path, stderr_path, message
    )
