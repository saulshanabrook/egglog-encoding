"""Resolve and validate benchmark workload files shared by run and profile modes.

This module owns the default workload suite, invocation-relative file and fact
directory resolution, content identities, and the rule that measured inputs do
not execute ``(prove ...)``. CLI parsing and endpoint selection belong in their
respective command modules.
"""

from __future__ import annotations

import hashlib
import json
from collections.abc import Iterator, Sequence
from dataclasses import dataclass
from pathlib import Path
from typing import Literal

from .models import FileSpec, validate_unique_file_identities
from .targets import sha256_directory, sha256_file


@dataclass(frozen=True)
class WorkloadConfig:
    """One repository-default workload and its optional fact directory."""

    file: str
    fact_directory: str | None = None


DEFAULT_WORKLOADS = (
    WorkloadConfig("benchmarks/math-microbenchmark/math-run-010.egg"),
    WorkloadConfig("egglog-experimental/tests/fixtures/eggcc-2mm-pass1.egg"),
    WorkloadConfig(
        "benchmarks/pointer-analysis-initdb.egg",
        "benchmarks/data/pointer-analysis-initdb",
    ),
    WorkloadConfig("egglog/tests/hardboiled_conv1d_32.egg"),
    WorkloadConfig("benchmarks/luminal-llama.egg"),
    WorkloadConfig("egglog/tests/web-demo/herbie.egg"),
)


@dataclass(frozen=True)
class _EgglogToken:
    kind: Literal["open", "close", "atom", "string"]
    value: str = ""


@dataclass(frozen=True)
class WorkloadSourceIdentity:
    """Content identity and files read by one top-level egglog workload."""

    sha256: str
    files: tuple[Path, ...]


def resolve_files(
    raw_files: Sequence[str],
    invocation_cwd: Path,
    fact_directory: str | None = None,
) -> tuple[FileSpec, ...]:
    """Resolve selected or default workloads relative to the invocation directory."""

    working_directory = invocation_cwd.resolve()
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
        source_identity = workload_source_identity(absolute_path, working_directory)

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
                sha256=source_identity.sha256,
                fact_directory=resolved_fact_directory,
                fact_directory_sha256=fact_directory_sha256,
                working_directory=working_directory,
            )
        )
    resolved = tuple(files)
    validate_workloads(resolved)
    return resolved


def _egglog_tokens(source: str) -> Iterator[_EgglogToken]:
    """Yield enough lexical structure to inspect top-level commands."""

    index = 0
    while index < len(source):
        character = source[index]
        if character.isspace():
            index += 1
            continue
        if character == ";":
            newline = source.find("\n", index)
            index = len(source) if newline == -1 else newline + 1
            continue
        if character == '"':
            start = index
            index += 1
            terminated = False
            while index < len(source):
                if source[index] == "\\":
                    index += 2
                elif source[index] == '"':
                    index += 1
                    terminated = True
                    break
                else:
                    index += 1
            if not terminated:
                raise ValueError("unterminated egglog string literal")
            yield _EgglogToken("string", source[start:index])
            continue
        if character == "(":
            yield _EgglogToken("open")
            index += 1
            continue
        if character == ")":
            yield _EgglogToken("close")
            index += 1
            continue
        end = index
        while end < len(source) and not source[end].isspace() and source[end] not in ";()":
            end += 1
        yield _EgglogToken("atom", source[index:end])
        index = end


def _top_level_commands(source: str) -> Iterator[tuple[_EgglogToken, ...]]:
    """Yield direct arguments for each top-level command."""

    depth = 0
    command: list[_EgglogToken] = []
    for token in _egglog_tokens(source):
        if token.kind == "open":
            if depth == 0:
                command = []
            depth += 1
        elif token.kind == "close":
            if depth == 0:
                continue
            depth -= 1
            if depth == 0:
                yield tuple(command)
        elif depth == 1:
            command.append(token)


def _include_paths(source: str, source_path: Path) -> tuple[str, ...]:
    includes: list[str] = []
    for command in _top_level_commands(source):
        if not command or command[0] != _EgglogToken("atom", "include"):
            continue
        if len(command) != 2 or command[1].kind != "string":
            raise ValueError(f"invalid include command in {source_path}")
        try:
            include = json.loads(command[1].value)
        except json.JSONDecodeError as error:
            raise ValueError(f"invalid include path in {source_path}: {error.msg}") from error
        if not isinstance(include, str):
            raise ValueError(f"invalid include path in {source_path}")
        includes.append(include)
    return tuple(includes)


def _workload_source_identity(
    path: Path,
    working_directory: Path,
    stack: tuple[Path, ...],
) -> WorkloadSourceIdentity:
    resolved_path = path.resolve()
    if resolved_path in stack:
        cycle = " -> ".join(str(candidate) for candidate in (*stack, resolved_path))
        raise ValueError(f"egglog include cycle: {cycle}")
    if not resolved_path.is_file():
        raise FileNotFoundError(f"included egglog file does not exist: {resolved_path}")

    source_bytes = resolved_path.read_bytes()
    source = source_bytes.decode("utf-8")
    includes = _include_paths(source, resolved_path)
    if not includes:
        return WorkloadSourceIdentity(sha256_file(resolved_path), (resolved_path,))

    digest = hashlib.sha256()
    digest.update(b"egglog-workload-includes-v1\0")
    digest.update(source_bytes)
    files: list[Path] = [resolved_path]
    for include in includes:
        include_path = Path(include).expanduser()
        if not include_path.is_absolute():
            include_path = working_directory / include_path
        child = _workload_source_identity(include_path, working_directory, (*stack, resolved_path))
        digest.update(b"\0include\0")
        digest.update(child.sha256.encode("ascii"))
        files.extend(child.files)
    return WorkloadSourceIdentity(
        f"sha256:{digest.hexdigest()}",
        tuple(dict.fromkeys(files)),
    )


def workload_source_identity(path: Path, working_directory: Path) -> WorkloadSourceIdentity:
    """Hash one file and the ordered transitive contents of its includes."""

    return _workload_source_identity(path, working_directory.resolve(), ())


def _source_contains_executable_prove_command(path: Path) -> bool:
    source = path.read_text(encoding="utf-8")
    return any(command and command[0] == _EgglogToken("atom", "prove") for command in _top_level_commands(source))


def file_contains_executable_prove_command(path: Path, working_directory: Path | None = None) -> bool:
    """Return whether a workload source closure contains a top-level ``prove``."""

    root = path.parent if working_directory is None else working_directory
    identity = workload_source_identity(path, root)
    return any(_source_contains_executable_prove_command(source_path) for source_path in identity.files)


def require_workload_unchanged(file_spec: FileSpec) -> None:
    """Reject an observation if its mutable inputs no longer match their cache identity."""

    try:
        working_directory = file_spec.working_directory or file_spec.absolute_path.parent
        file_sha256 = workload_source_identity(file_spec.absolute_path, working_directory).sha256
        if file_spec.fact_directory is None:
            fact_directory_sha256 = ""
        elif file_spec.fact_directory.is_dir():
            fact_directory_sha256 = sha256_directory(file_spec.fact_directory)
        else:
            fact_directory_sha256 = None
    except (OSError, UnicodeError, ValueError) as error:
        raise ValueError(f"workload changed during execution: {file_spec.display_path}") from error
    if file_sha256 != file_spec.sha256 or fact_directory_sha256 != file_spec.fact_directory_sha256:
        raise ValueError(f"workload changed during execution: {file_spec.display_path}")


def validate_workloads(files: Sequence[FileSpec]) -> None:
    """Validate cache identity and timing-boundary invariants for workloads."""

    validate_unique_file_identities(files)
    for file_spec in files:
        if file_contains_executable_prove_command(file_spec.absolute_path, file_spec.working_directory):
            raise ValueError(
                f"{file_spec.display_path} contains an explicit prove command; "
                "benchmark files should use check so the selected treatment controls proof extraction"
            )
