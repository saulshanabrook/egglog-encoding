"""Own deterministic JSON document and JSON Lines serialization."""

from __future__ import annotations

import json
import os
import tempfile
from pathlib import Path
from typing import Any, cast


def serialize_json_document(value: object) -> bytes:
    """Serialize one human-readable JSON document deterministically."""

    return (json.dumps(value, allow_nan=False, ensure_ascii=True, indent=2, sort_keys=True) + "\n").encode()


def serialize_json_line(value: object) -> bytes:
    """Serialize one compact, newline-free JSON value deterministically."""

    return json.dumps(
        value,
        allow_nan=False,
        ensure_ascii=True,
        separators=(",", ":"),
        sort_keys=True,
    ).encode()


def write_json_document(path: Path, value: object) -> None:
    """Atomically write and sync one deterministic JSON document."""

    write_bytes_atomically(path, serialize_json_document(value))


def write_text_document(path: Path, value: str) -> None:
    """Atomically write and sync one UTF-8 text document."""

    write_bytes_atomically(path, value.encode())


def write_bytes_atomically(path: Path, value: bytes) -> None:
    """Atomically publish one synced byte string."""

    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary_name = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    temporary = Path(temporary_name)
    try:
        with os.fdopen(descriptor, "wb") as handle:
            handle.write(value)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, path)
        _sync_directory(path.parent)
    except BaseException:
        temporary.unlink(missing_ok=True)
        raise


def _sync_directory(path: Path) -> None:
    flags = os.O_RDONLY | getattr(os, "O_DIRECTORY", 0)
    descriptor = os.open(path, flags)
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def load_json_object(path: Path) -> dict[str, Any]:
    """Load one JSON object or reject a different top-level value."""

    value = json.loads(path.read_bytes())
    if not isinstance(value, dict):
        raise ValueError(f"expected a JSON object in {path}")
    return cast(dict[str, Any], value)
