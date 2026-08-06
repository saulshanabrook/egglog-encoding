"""Execute paper lane processes with isolated logs, timeouts, and wall time."""

from __future__ import annotations

import os
import signal
import subprocess
import threading
import time
from collections.abc import Callable, Mapping
from contextlib import suppress
from datetime import UTC, datetime
from pathlib import Path
from typing import Protocol, TextIO

from .models import CommandSpec, ProcessOutcome
from .provenance import isoformat_utc, resolve_executable


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
    """Run commands as isolated process groups with blocking deadline waits."""

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
                executable = resolve_executable(command, environment)
                process = subprocess.Popen(
                    (str(executable), *command.argv[1:]),
                    cwd=command.cwd,
                    env=dict(environment),
                    stdin=subprocess.DEVNULL,
                    text=True,
                    stdout=stdout,
                    stderr=stderr,
                    start_new_session=True,
                )
            except OSError as error:
                stderr.write(f"{error}\n")
                _sync_logs(stdout, stderr)
                finished_at = self._now()
                return ProcessOutcome(
                    status="infrastructure-error",
                    started_at=isoformat_utc(started_at),
                    finished_at=isoformat_utc(finished_at),
                    wall_sec=None,
                    error_message=str(error),
                )
            try:
                return_code = wait_process(process, command.timeout_sec)
            except subprocess.TimeoutExpired:
                _sync_logs(stdout, stderr)
                finished_at = self._now()
                return ProcessOutcome(
                    status="timed-out",
                    started_at=isoformat_utc(started_at),
                    finished_at=isoformat_utc(finished_at),
                    wall_sec=None,
                    error_message=f"timed out after {command.timeout_sec:g} seconds",
                )
            except BaseException:
                terminate_process_group(process)
                raise
            kill_remaining_process_group(process.pid)
            wall_sec = self._timer() - start
            finished_at = self._now()
            _sync_logs(stdout, stderr)

        if return_code == 0:
            return ProcessOutcome(
                status="success",
                started_at=isoformat_utc(started_at),
                finished_at=isoformat_utc(finished_at),
                wall_sec=wall_sec,
            )
        exit_code = return_code if return_code >= 0 else None
        signal_number = -return_code if return_code < 0 else None
        message = read_log_tail(stderr_path) or read_log_tail(stdout_path) or "process exited with non-zero status"
        return ProcessOutcome(
            status="failure",
            started_at=isoformat_utc(started_at),
            finished_at=isoformat_utc(finished_at),
            wall_sec=wall_sec,
            exit_code=exit_code,
            signal=signal_number,
            error_message=message[-1000:],
        )


def wait_process(process: subprocess.Popen[str], timeout_sec: float) -> int:
    """Wait without polling while one lock owns deadline classification."""

    lock = threading.Lock()
    completed = False
    expired = False

    def expire() -> None:
        nonlocal expired
        with lock:
            if completed:
                return
            expired = True
            kill_remaining_process_group(process.pid)

    timer = threading.Timer(timeout_sec, expire)
    timer.start()
    try:
        waited_pid, status = os.waitpid(process.pid, 0)
        assert waited_pid == process.pid
        return_code = os.waitstatus_to_exitcode(status)
        process.returncode = return_code
        with lock:
            completed = True
    finally:
        timer.cancel()
        timer.join()
    if expired:
        raise subprocess.TimeoutExpired(process.args, timeout_sec)
    return return_code


def terminate_process_group(process: subprocess.Popen[str] | subprocess.Popen[bytes]) -> None:
    """Kill and reap an isolated process group after an exceptional exit."""

    with suppress(ProcessLookupError):
        os.killpg(process.pid, signal.SIGKILL)
    process.wait()


def kill_remaining_process_group(process_group: int) -> None:
    """Kill descendants left behind after the process-group leader exits."""

    with suppress(ProcessLookupError):
        os.killpg(process_group, signal.SIGKILL)


def read_log_tail(path: Path, limit: int = 4096) -> str:
    """Read a bounded UTF-8 replacement-decoded tail from a process log."""

    with path.open("rb") as handle:
        handle.seek(0, os.SEEK_END)
        size = handle.tell()
        handle.seek(max(0, size - limit))
        return handle.read().decode("utf-8", errors="replace").strip()


def _sync_logs(*handles: TextIO) -> None:
    for handle in handles:
        handle.flush()
        os.fsync(handle.fileno())
