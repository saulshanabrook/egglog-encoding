"""Dispatch the public benchmark and profile commands with lazy imports.

Command-specific parsing and execution belong in their respective modules.
"""

from __future__ import annotations

import sys
from collections.abc import Sequence


def main(argv: Sequence[str] | None = None) -> int:
    """Dispatch the public CLI without importing benchmark dependencies eagerly."""
    raw_argv = tuple(sys.argv[1:] if argv is None else argv)
    if raw_argv and raw_argv[0] == "profile":
        from .profile import main as profile_main

        return profile_main(raw_argv[1:])
    from .benchmark import main as benchmark_main

    return benchmark_main(raw_argv)
