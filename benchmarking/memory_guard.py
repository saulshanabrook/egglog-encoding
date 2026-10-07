"""Opt-in host protection for sequential benchmark campaigns.

This is an operational safeguard, not a benchmark admission policy or a hard
allocation limit. The 10 GiB ceiling leaves 6 GiB outside the workload on the
16 GiB evaluation Mac; host pressure and headroom can stop it earlier.
RSS is sampled at 100 ms and host state at 500 ms. The guard only kills
the newly launched workload's isolated process group.
"""

from __future__ import annotations

import os
import re
import signal
import subprocess
import sys
import threading
import time
from contextlib import suppress
from pathlib import Path

GROUP_LIMIT_BYTES = 10 * 1024**3
HEADROOM_BYTES = 2 * 1024**3


def group_rss_bytes(process_group: int) -> int:
    """Sum resident memory for all currently visible members of one group."""

    snapshot = subprocess.run(["ps", "-axo", "pgid=,rss="], check=True, capture_output=True, text=True, timeout=1)
    return sum(
        int(fields[1]) * 1024
        for line in snapshot.stdout.splitlines()
        if len(fields := line.split()) == 2 and int(fields[0]) == process_group
    )


def host_memory() -> tuple[int, int]:
    """Return headroom bytes and pressure level (1 means normal).

    macOS headroom is free + inactive + speculative pages, an intentionally
    explicit approximation of reclaimable memory, alongside the kernel's
    authoritative pressure signal. Linux provides MemAvailable directly.
    """

    if sys.platform == "darwin":
        pressure = subprocess.run(
            ["sysctl", "-n", "kern.memorystatus_vm_pressure_level"],
            check=True,
            capture_output=True,
            text=True,
            timeout=1,
        )
        snapshot = subprocess.run(["vm_stat"], check=True, capture_output=True, text=True, timeout=1)
        page_size = re.search(r"page size of (\d+) bytes", snapshot.stdout)
        if page_size is None:
            raise ValueError("vm_stat did not report its page size")
        pages = dict(re.findall(r"^(Pages (?:free|inactive|speculative)):\s+(\d+)\.", snapshot.stdout, re.M))
        if len(pages) != 3:
            raise ValueError("vm_stat did not report all headroom counters")
        return sum(map(int, pages.values())) * int(page_size[1]), int(pressure.stdout.strip())
    if sys.platform == "linux":
        available = re.search(r"^MemAvailable:\s+(\d+) kB$", Path("/proc/meminfo").read_text(), re.M)
        if available is None:
            raise ValueError("/proc/meminfo did not report MemAvailable")
        return int(available[1]) * 1024, 1
    raise ValueError(f"memory guard does not support {sys.platform}")


class MemoryGuard:
    """Check host readiness, then supervise a single isolated workload group."""

    def __init__(self) -> None:
        self.reason: str | None = None
        self._last_host_check = float("-inf")
        self._finished = threading.Event()
        self._thread: threading.Thread | None = None

    @classmethod
    def from_environment(cls) -> MemoryGuard | None:
        enabled = os.environ.get("EGGLOG_BENCH_MEMORY_GUARD", "")
        if enabled not in ("", "1"):
            raise ValueError("EGGLOG_BENCH_MEMORY_GUARD must be unset or 1")
        if not enabled:
            return None
        guard = cls()
        reason = guard.check(0)
        if reason is not None:
            raise ValueError(f"resource guard refused to launch a workload: {reason}")
        return guard

    def check(self, rss_bytes: int) -> str | None:
        """Return a stop reason; monitoring errors also stop work safely."""

        if self.reason is not None:
            return self.reason
        if rss_bytes > GROUP_LIMIT_BYTES:
            self.reason = f"workload process-group RSS {rss_bytes} exceeded the {GROUP_LIMIT_BYTES}-byte safety cap"
        elif time.monotonic() - self._last_host_check >= 0.5:
            try:
                headroom, pressure = host_memory()
                if pressure != 1:
                    self.reason = f"host memory pressure is not normal (kernel level {pressure})"
                elif headroom < HEADROOM_BYTES:
                    self.reason = f"host memory headroom {headroom} is below the {HEADROOM_BYTES}-byte reserve"
                self._last_host_check = time.monotonic()
            except (OSError, ValueError, subprocess.SubprocessError) as error:
                self.reason = f"memory monitoring failed: {error}"
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
