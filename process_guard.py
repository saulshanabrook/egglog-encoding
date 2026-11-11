"""Native address-space limits and cleanup for isolated process groups."""

from __future__ import annotations

import os
import signal
import subprocess
import sys
from collections.abc import Mapping, Sequence
from contextlib import suppress
from typing import TextIO

NATIVE_LIMIT_BYTES = 6 * 1024**3
NATIVE_RESOURCE_EXIT = 86
NATIVE_ALLOCATION_FAILURE = "native memory limit: allocation failed under limit; stopping workload"
NATIVE_ALLOCATOR_ENV = {
    "MIMALLOC_ARENA_RESERVE": "0",
    "MIMALLOC_DISALLOW_ARENA_ALLOC": "1",
    "MIMALLOC_RESERVE_OS_MEMORY": "0",
    "MIMALLOC_RESERVE_HUGE_OS_PAGES": "0",
}


class ResourceStopped(ValueError):
    """A host-safety stop that must halt subsequent collection."""


def native_limit_enabled() -> bool:
    """Validate the opt-in switch shared by native collection and profiling."""
    enabled = os.environ.get("EGGLOG_BENCH_MEMORY_GUARD", "")
    if enabled not in ("", "1"):
        raise ValueError("EGGLOG_BENCH_MEMORY_GUARD must be unset or 1")
    return enabled == "1"


def native_memory_command(
    command: Sequence[str], env: Mapping[str, str], limit_bytes: int | None
) -> tuple[list[str], dict[str, str]]:
    """Use one allocator policy for controlled engines, optionally limiting AS.

    Options must reach mimalloc before exec, including for unguarded timing runs:
    the cache identifies binaries, not allocator environment differences. The
    explicit CLI flag makes older controlled binaries reject guarded workloads.
    """
    if limit_bytes is not None:
        if sys.platform not in ("darwin", "linux"):
            raise ResourceStopped("resource guard refused to launch: native memory limit requires macOS or Linux")
        if not 0 < limit_bytes <= 10 * 1024**3:
            raise ValueError("native memory limit must be between 1 byte and 10 GiB")
    args = list(command)
    if limit_bytes is not None:
        args.insert(1, f"--memory-limit-bytes={limit_bytes}")
    return args, {**env, **NATIVE_ALLOCATOR_ENV}


def native_resource_failure(returncode: int, log: TextIO, limited: bool) -> bool:
    """Recognize native setup/allocation refusals without losing long backtraces.

    Stacker maps directly instead of using Rust's GlobalAlloc. Its specific mmap
    failure is a resource stop too. Scan bounded chunks across the whole log;
    the user-facing error tail can omit the original allocation failure.
    """
    if not limited:
        return False
    if returncode == NATIVE_RESOURCE_EXIT:
        return True
    pattern = {2: "--memory-limit-bytes", 101: "mmap failed to allocate stack:"}.get(returncode)
    if pattern is None:
        return False
    log.seek(0)
    suffix = ""
    while chunk := log.read(4096):
        text = suffix + chunk
        if pattern in text:
            return True
        suffix = text[-len(pattern) :]
    return False


def native_allocation_failure(returncode: int, log: TextIO) -> bool:
    """Identify the controlled allocator's exact diagnostic, not setup exit 86."""
    if returncode != NATIVE_RESOURCE_EXIT:
        return False
    log.seek(0)
    suffix = ""
    while chunk := log.read(4096):
        text = suffix + chunk
        if NATIVE_ALLOCATION_FAILURE in text:
            return True
        suffix = text[-len(NATIVE_ALLOCATION_FAILURE) :]
    return False


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
