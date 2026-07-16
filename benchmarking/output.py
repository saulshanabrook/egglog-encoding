"""Own the shared stderr console and render target, build, and error messages.

Collection progress belongs in :mod:`benchmarking.collection`; final benchmark
and profile presentation belong in their feature-specific rendering modules.
"""

from __future__ import annotations

from pathlib import Path

from rich.console import Console
from rich.text import Text

from .models import TargetRow


def display_target(row: TargetRow) -> str:
    if row.label:
        return row.label
    if row.git_ref != "HEAD":
        return row.git_ref
    return f"{Path(row.path).name}@{row.git_sha[:12]}"


class RunnerOutput:
    def __init__(self) -> None:
        self.console = Console(stderr=True)

    def build_start(self, row: TargetRow) -> None:
        self.console.print(Text.assemble(("Building", "bold"), " ", display_target(row)))

    def print_error(self, error: BaseException) -> None:
        self.console.print(Text.assemble(("error:", "red"), " ", str(error)))
