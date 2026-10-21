"""Configure native address-space protection for the controlled executables."""

from __future__ import annotations

import sys
from collections.abc import Mapping, Sequence

NATIVE_LIMIT_BYTES = 16 * 1024**3
NATIVE_ALLOCATION_EXIT = 86
NATIVE_SETUP_EXIT = 87
NATIVE_ALLOCATOR_ENV = {
    "MIMALLOC_ARENA_RESERVE": "0",
    "MIMALLOC_DISALLOW_ARENA_ALLOC": "1",
    "MIMALLOC_RESERVE_OS_MEMORY": "0",
    "MIMALLOC_RESERVE_HUGE_OS_PAGES": "0",
}


def native_memory_command(
    command: Sequence[str], env: Mapping[str, str], limit_bytes: int | None = NATIVE_LIMIT_BYTES
) -> tuple[list[str], dict[str, str]]:
    """Pass explicit protection and the fixed startup policy before native exec.

    Only egglog-experimental and egg-math-benchmark accept this option. An older
    binary must reject it at preflight instead of silently running uncapped.
    Changed cap/environment experiments require a separate report and receipt.
    """
    args = list(command)
    if limit_bytes is not None:
        if sys.platform not in ("darwin", "linux"):
            raise ValueError("native memory limit requires macOS or Linux")
        if not 0 < limit_bytes < 2**64 - 1:
            raise ValueError("native memory limit must be a positive finite u64 integer")
        args.insert(1, f"--memory-limit-bytes={limit_bytes}")
    return args, {**env, **NATIVE_ALLOCATOR_ENV}
