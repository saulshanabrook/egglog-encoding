"""Supervise source preparation and diagnostics, retaining logs and cleaning descendants."""

from __future__ import annotations

import fcntl
import os
import shutil
import signal
import subprocess
import sys
import time
from collections.abc import Callable, Iterator, Sequence
from contextlib import contextmanager, suppress
from dataclasses import dataclass
from pathlib import Path
from typing import Literal

from process_guard import GROUP_LIMIT_BYTES, MemoryGuard, group_rss_bytes

DISK_RESERVE_BYTES = 2 * 1024**3


@contextmanager
def exclusive_job(lock_path: Path) -> Iterator[None]:
    """Serialize heavy reproduction stages across independent CLI invocations."""
    lock_path.parent.mkdir(parents=True, exist_ok=True)
    with lock_path.open("a") as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as error:
            raise ValueError("another reproduction job owns the heavy-process slot") from error
        try:
            yield
        finally:
            fcntl.flock(lock, fcntl.LOCK_UN)


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
