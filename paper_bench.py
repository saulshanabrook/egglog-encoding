#!/usr/bin/env -S uv run
"""Dispatch the standalone paper artifact benchmark harness."""

from __future__ import annotations

from collections.abc import Sequence

from paper_benchmarking.cli import main as cli_main


def main(argv: Sequence[str] | None = None) -> int:
    """Dispatch the paper artifact CLI."""

    return cli_main(argv)


if __name__ == "__main__":
    raise SystemExit(main())
