"""Write the shared grouped snapshot after benchmark collection."""

from __future__ import annotations

import os
import tempfile
from pathlib import Path

from .store import GroupedReport, serialize_grouped_report


def grouped_report_path(report_path: Path) -> Path:
    """Derive a distinct sibling snapshot name for any report cache path."""

    name = report_path.stem if report_path.suffix.lower() == ".jsonl" else report_path.name
    return report_path.with_name(f"{name}-grouped.json")


def write_grouped_report(report: GroupedReport, destination: Path) -> Path:
    """Atomically replace a changed snapshot, leaving unchanged bytes and mtimes alone."""

    encoded = serialize_grouped_report(report)
    if destination.is_file() and destination.read_bytes() == encoded:
        return destination
    destination.parent.mkdir(parents=True, exist_ok=True)
    temporary: Path | None = None
    try:
        with tempfile.NamedTemporaryFile(
            dir=destination.parent, prefix=f".{destination.name}.", delete=False
        ) as handle:
            temporary = Path(handle.name)
            handle.write(encoded)
        os.replace(temporary, destination)
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)
    return destination
