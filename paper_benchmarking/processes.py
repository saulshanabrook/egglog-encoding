"""Execute paper lane processes with isolated logs, timeout, wall, and RSS data."""

from __future__ import annotations

import os
import resource
import signal
import subprocess
import sys
import threading
import time
from collections.abc import Callable, Mapping
from contextlib import suppress
from datetime import UTC, datetime
from pathlib import Path
from typing import Protocol

from .models import CommandSpec, ProcessOutcome


class ProcessExecutor(Protocol):
    """Dependency-injection boundary used by the lane runner."""

    def run(
        self,
        command: CommandSpec,
        *,
        environment: Mapping[str, str],
        stdout_path: Path,
        stderr_path: Path,
    ) -> ProcessOutcome:
        """Run one command and write its complete output logs."""


class SubprocessExecutor:
    """Run commands as isolated process groups and account with ``wait4``."""

    def __init__(
        self,
        *,
        now: Callable[[], datetime] | None = None,
        timer: Callable[[], float] | None = None,
    ) -> None:
        self._now = now or (lambda: datetime.now(UTC))
        self._timer = timer or time.perf_counter

    def run(
        self,
        command: CommandSpec,
        *,
        environment: Mapping[str, str],
        stdout_path: Path,
        stderr_path: Path,
    ) -> ProcessOutcome:
        """Run one command, retaining timeouts as non-finite statuses."""

        stdout_path.parent.mkdir(parents=True, exist_ok=True)
        stderr_path.parent.mkdir(parents=True, exist_ok=True)
        started_at = self._now()
        start = self._timer()
        with (
            stdout_path.open("w", encoding="utf-8", errors="replace") as stdout,
            stderr_path.open("w", encoding="utf-8", errors="replace") as stderr,
        ):
            try:
                process = subprocess.Popen(
                    command.argv,
                    cwd=command.cwd,
                    env=dict(environment),
                    text=True,
                    stdout=stdout,
                    stderr=stderr,
                    start_new_session=True,
                )
            except OSError as error:
                stderr.write(f"{error}\n")
                finished_at = self._now()
                return ProcessOutcome(
                    status="failure",
                    started_at=_isoformat(started_at),
                    finished_at=_isoformat(finished_at),
                    wall_sec=self._timer() - start,
                    max_rss_bytes=None,
                    error_message=str(error),
                )
            try:
                return_code, usage = wait4_process(process, command.timeout_sec)
            except subprocess.TimeoutExpired:
                finished_at = self._now()
                return ProcessOutcome(
                    status="timed-out",
                    started_at=_isoformat(started_at),
                    finished_at=_isoformat(finished_at),
                    wall_sec=None,
                    max_rss_bytes=None,
                    error_message=f"timed out after {command.timeout_sec:g} seconds",
                )
            except BaseException:
                terminate_process_group(process)
                raise
            wall_sec = self._timer() - start
            finished_at = self._now()

        max_rss_bytes = ru_maxrss_to_bytes(usage.ru_maxrss)
        if return_code == 0:
            return ProcessOutcome(
                status="success",
                started_at=_isoformat(started_at),
                finished_at=_isoformat(finished_at),
                wall_sec=wall_sec,
                max_rss_bytes=max_rss_bytes,
            )
        exit_code = return_code if return_code >= 0 else None
        signal_number = -return_code if return_code < 0 else None
        message = read_log_tail(stderr_path) or read_log_tail(stdout_path) or "process exited with non-zero status"
        return ProcessOutcome(
            status="failure",
            started_at=_isoformat(started_at),
            finished_at=_isoformat(finished_at),
            wall_sec=wall_sec,
            max_rss_bytes=max_rss_bytes,
            exit_code=exit_code,
            signal=signal_number,
            error_message=message[-1000:],
        )


def wait4_process(
    process: subprocess.Popen[str],
    timeout_sec: float,
) -> tuple[int, resource.struct_rusage]:
    """Wait for one child without adding polling delay to wall time."""

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


def terminate_process_group(process: subprocess.Popen[str] | subprocess.Popen[bytes]) -> None:
    """Kill and reap an isolated process group after an exceptional exit."""

    with suppress(ProcessLookupError):
        os.killpg(process.pid, signal.SIGKILL)
    process.wait()


def ru_maxrss_to_bytes(ru_maxrss: int, platform: str = sys.platform) -> int | None:
    """Normalize macOS byte and Linux kibibyte peak-RSS units."""

    if ru_maxrss <= 0:
        return None
    if platform == "darwin":
        return ru_maxrss
    return ru_maxrss * 1024


def read_log_tail(path: Path, limit: int = 4096) -> str:
    """Read a bounded UTF-8 replacement-decoded tail from a process log."""

    with path.open("rb") as handle:
        handle.seek(0, os.SEEK_END)
        size = handle.tell()
        handle.seek(max(0, size - limit))
        return handle.read().decode("utf-8", errors="replace").strip()


def _isoformat(value: datetime) -> str:
    normalized = value.astimezone(UTC)
    return normalized.isoformat(timespec="microseconds").replace("+00:00", "Z")
