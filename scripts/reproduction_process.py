"""Serialize heavy author-source generation across invocations."""

from __future__ import annotations

import fcntl
from collections.abc import Iterator
from contextlib import contextmanager
from pathlib import Path

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
