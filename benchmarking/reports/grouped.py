"""Write the shared grouped snapshot, including cache-only export."""

from __future__ import annotations

import argparse
import os
import sys
import tempfile
from collections.abc import Sequence
from pathlib import Path

from rich.console import Console
from rich.text import Text

from .store import GroupedReport, ReportStore, serialize_grouped_report


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


def main(argv: Sequence[str] | None = None) -> int:
    """Regenerate the grouped artifact without building, collecting, or changing JSONL."""

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report", default=".reports.jsonl", help="existing append-only JSONL report/cache path")
    args = parser.parse_args(argv)
    if args.report == "-":
        parser.error("--report requires a file path; '-' streaming is not supported")
    console = Console(stderr=True)
    try:
        path = Path(args.report).expanduser().resolve()
        if not path.is_file():
            raise FileNotFoundError(f"benchmark cache does not exist: {path}")
        report = ReportStore(path).grouped_report()
        destination = write_grouped_report(report, grouped_report_path(path))
    except (OSError, ValueError) as error:
        console.print(Text.assemble(("error:", "red"), " ", str(error)))
        return 2
    print(destination, file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
