#!/usr/bin/env -S uv run
"""Execute the public benchmark and profiling CLI.

Command dispatch and all implementation details belong in :mod:`benchmarking`.
"""

from benchmarking.cli import main

if __name__ == "__main__":
    raise SystemExit(main())
