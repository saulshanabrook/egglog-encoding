#!/usr/bin/env -S uv run
"""Dispatch the public benchmark and profiling CLI.

Command-specific parsing and execution belong in :mod:`benchmarking`.
"""

from __future__ import annotations

import sys
from collections.abc import Sequence


def main(argv: Sequence[str] | None = None) -> int:
    """Dispatch without eagerly importing dependencies for the other command."""

    raw_argv = tuple(sys.argv[1:] if argv is None else argv)
    if raw_argv and raw_argv[0] == "profile":
        from benchmarking.profile import main as profile_main

        return profile_main(raw_argv[1:])
    from benchmarking.benchmark import main as benchmark_main

    return benchmark_main(raw_argv)


if __name__ == "__main__":
    raise SystemExit(main())
