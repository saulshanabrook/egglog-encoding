"""Own deterministic JSON document and JSON Lines serialization."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any, cast


def serialize_json_document(value: object) -> bytes:
    """Serialize one human-readable JSON document deterministically."""

    return (json.dumps(value, ensure_ascii=True, indent=2, sort_keys=True) + "\n").encode()


def serialize_json_line(value: object) -> bytes:
    """Serialize one compact, newline-free JSON value deterministically."""

    return json.dumps(value, ensure_ascii=True, separators=(",", ":"), sort_keys=True).encode()


def write_json_document(path: Path, value: object) -> None:
    """Write one deterministic JSON document."""

    path.write_bytes(serialize_json_document(value))


def load_json_object(path: Path) -> dict[str, Any]:
    """Load one JSON object or reject a different top-level value."""

    value = json.loads(path.read_bytes())
    if not isinstance(value, dict):
        raise ValueError(f"expected a JSON object in {path}")
    return cast(dict[str, Any], value)
