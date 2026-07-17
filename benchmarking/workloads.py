"""Resolve and validate benchmark workload files shared by run and profile modes.

This module owns the default workload suite, invocation-relative file and fact
directory resolution, content identities, and the rule that measured inputs do
not execute ``(prove ...)``. CLI parsing and endpoint selection belong in their
respective command modules.
"""

from __future__ import annotations

import re
from collections.abc import Sequence
from dataclasses import dataclass
from pathlib import Path

from .models import FileSpec, validate_unique_file_identities
from .targets import sha256_directory, sha256_file


@dataclass(frozen=True)
class WorkloadConfig:
    """One repository-default workload and its optional fact directory."""

    file: str
    fact_directory: str | None = None


DEFAULT_WORKLOADS = (
    WorkloadConfig("egglog/tests/math-microbenchmark.egg"),
    WorkloadConfig("egglog-experimental/tests/fixtures/eggcc-2mm-pass1.egg"),
    WorkloadConfig(
        "benchmarks/pointer-analysis-small.egg",
        "benchmarks/data/pointer-analysis-small",
    ),
    WorkloadConfig("egglog/tests/hardboiled_conv1d_32.egg"),
    WorkloadConfig("benchmarks/luminal-llama.egg"),
    WorkloadConfig("egglog/tests/web-demo/herbie.egg"),
)


def resolve_files(
    raw_files: Sequence[str],
    invocation_cwd: Path,
    fact_directory: str | None = None,
) -> tuple[FileSpec, ...]:
    """Resolve selected or default workloads relative to the invocation directory."""

    if raw_files:
        chosen = tuple(WorkloadConfig(file, fact_directory) for file in raw_files)
    else:
        if fact_directory is not None:
            raise ValueError("--fact-directory requires at least one explicit benchmark file")
        chosen = DEFAULT_WORKLOADS
    files: list[FileSpec] = []
    for workload in chosen:
        display_path = workload.file
        absolute_path = Path(display_path).expanduser()
        if not absolute_path.is_absolute():
            absolute_path = invocation_cwd / absolute_path
        absolute_path = absolute_path.resolve()
        if not absolute_path.is_file():
            raise FileNotFoundError(f"benchmark file does not exist: {display_path}")

        resolved_fact_directory: Path | None = None
        fact_directory_sha256 = ""
        if workload.fact_directory is not None:
            resolved_fact_directory = Path(workload.fact_directory).expanduser()
            if not resolved_fact_directory.is_absolute():
                resolved_fact_directory = invocation_cwd / resolved_fact_directory
            resolved_fact_directory = resolved_fact_directory.resolve()
            if not resolved_fact_directory.is_dir():
                raise FileNotFoundError(f"benchmark fact directory does not exist: {workload.fact_directory}")
            fact_directory_sha256 = sha256_directory(resolved_fact_directory)
        files.append(
            FileSpec(
                display_path=display_path,
                absolute_path=absolute_path,
                sha256=sha256_file(absolute_path),
                fact_directory=resolved_fact_directory,
                fact_directory_sha256=fact_directory_sha256,
            )
        )
    resolved = tuple(files)
    validate_workloads(resolved)
    return resolved


def file_contains_executable_prove_command(path: Path) -> bool:
    """Return whether a workload contains a non-comment executable prove command."""

    for line in path.read_text(encoding="utf-8").splitlines():
        stripped = line.lstrip()
        if stripped.startswith(";"):
            continue
        if re.match(r"\(prove(?:\s|\))", stripped):
            return True
    return False


def validate_workloads(files: Sequence[FileSpec]) -> None:
    """Validate cache identity and timing-boundary invariants for workloads."""

    validate_unique_file_identities(files)
    for file_spec in files:
        if file_contains_executable_prove_command(file_spec.absolute_path):
            raise ValueError(
                f"{file_spec.display_path} contains an explicit prove command; "
                "benchmark files should use check so proof extraction is not included in timed runs"
            )
