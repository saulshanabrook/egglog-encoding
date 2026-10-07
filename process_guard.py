"""Memory protection and cleanup for isolated process groups.

This is an operational safeguard, not a benchmark admission policy or a hard
allocation limit. The 10 GiB process-group RSS ceiling is sampled at 100 ms.
The guard only kills the newly launched workload's isolated process group.
"""

from __future__ import annotations

import os
import signal
import subprocess
import threading
from contextlib import suppress

GROUP_LIMIT_BYTES = 10 * 1024**3


class ResourceStopped(ValueError):
    """A host-safety stop that must halt subsequent collection."""


def group_rss_bytes(process_group: int) -> int:
    """Sum resident memory for all currently visible members of one group."""

    snapshot = subprocess.run(["ps", "-axo", "pgid=,rss="], check=True, capture_output=True, text=True, timeout=1)
    return sum(
        int(fields[1]) * 1024
        for line in snapshot.stdout.splitlines()
        if len(fields := line.split()) == 2 and int(fields[0]) == process_group
    )


class MemoryGuard:
    """Supervise resident memory for a single isolated workload group."""

    def __init__(self) -> None:
        self.reason: str | None = None
        self._finished = threading.Event()
        self._thread: threading.Thread | None = None

    @classmethod
    def from_environment(cls) -> MemoryGuard | None:
        enabled = os.environ.get("EGGLOG_BENCH_MEMORY_GUARD", "")
        if enabled not in ("", "1"):
            raise ValueError("EGGLOG_BENCH_MEMORY_GUARD must be unset or 1")
        if not enabled:
            return None
        return cls()

    def check(self, rss_bytes: int) -> str | None:
        """Return a stop reason when the process-group RSS exceeds the cap."""

        if self.reason is not None:
            return self.reason
        if rss_bytes > GROUP_LIMIT_BYTES:
            self.reason = f"workload process-group RSS {rss_bytes} exceeded the {GROUP_LIMIT_BYTES}-byte safety cap"
        return self.reason

    def start(self, process_group: int) -> None:
        def monitor() -> None:
            while not self._finished.is_set():
                try:
                    reason = self.check(group_rss_bytes(process_group))
                except (OSError, ValueError, subprocess.SubprocessError) as error:
                    reason = self.reason = f"memory monitoring failed: {error}"
                if reason is not None:
                    if not self._finished.is_set():
                        with suppress(ProcessLookupError):
                            os.killpg(process_group, signal.SIGKILL)
                    return
                self._finished.wait(0.1)

        self._thread = threading.Thread(target=monitor, name="benchmark-memory-guard", daemon=True)
        self._thread.start()

    def close(self) -> None:
        """Stop monitoring and join outside the child's measured wall interval."""

        self._finished.set()
        if self._thread is not None:
            with suppress(RuntimeError):
                self._thread.join()


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
