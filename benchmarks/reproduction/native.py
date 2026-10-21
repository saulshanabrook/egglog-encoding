"""Interpret controlled native refusals without supervising author memory usage."""

from __future__ import annotations

from typing import TextIO

from native_memory import (
    NATIVE_ALLOCATION_EXIT as NATIVE_ALLOCATION_EXIT,
)
from native_memory import (
    NATIVE_ALLOCATOR_ENV as NATIVE_ALLOCATOR_ENV,
)
from native_memory import (
    NATIVE_LIMIT_BYTES as NATIVE_LIMIT_BYTES,
)
from native_memory import (
    NATIVE_SETUP_EXIT as NATIVE_SETUP_EXIT,
)
from native_memory import (
    native_memory_command as native_memory_command,
)

# Older validation receipts bound this exact allocator diagnostic to their logs.
NATIVE_ALLOCATION_FAILURE = "native memory limit: allocation failed under limit; stopping workload"


def native_resource_failure(returncode: int, log: TextIO, limited: bool) -> bool:
    """Recognize setup refusal, including an older executable rejecting the flag."""
    if not limited:
        return False
    if returncode == NATIVE_SETUP_EXIT:
        return True
    if returncode != 2:
        return False
    log.seek(0)
    suffix = ""
    while chunk := log.read(4096):
        text = suffix + chunk
        if "--memory-limit-bytes" in text:
            return True
        suffix = text[-32:]
    return False
