"""Collect explicit invocation, executable, repository, input, and machine provenance."""

from __future__ import annotations

import hashlib
import os
import platform
import shutil
import subprocess
from collections.abc import Mapping
from datetime import UTC, datetime
from pathlib import Path

from .hashing import hash_path, sha256_file
from .models import CommandSpec, ProcessLane

INHERITED_ENVIRONMENT_KEYS = (
    "CARGO_HOME",
    "HOME",
    "LANG",
    "LC_ALL",
    "PATH",
    "PLTUSERHOME",
    "RACKET_DIR",
    "RUSTUP_HOME",
    "RUSTUP_TOOLCHAIN",
    "SHELL",
    "TMPDIR",
    "USER",
)


def isoformat_utc(value: datetime) -> str:
    """Return one stable, timezone-aware UTC timestamp."""

    normalized = value.astimezone(UTC)
    return normalized.isoformat(timespec="microseconds").replace("+00:00", "Z")


def collect_machine_context() -> dict[str, object]:
    """Collect machine and Python version fields relevant to reproducibility."""

    return {
        "cpu_count": os.cpu_count(),
        "hostname": platform.node(),
        "machine": platform.machine(),
        "platform": platform.platform(),
        "python_implementation": platform.python_implementation(),
        "python_version": platform.python_version(),
        "release": platform.release(),
        "system": platform.system(),
    }


def collect_repository_context(repo_root: Path) -> dict[str, object]:
    """Collect the exact repository revision and porcelain dirty-state paths."""

    root = repo_root.resolve(strict=True)
    sha = _git_output(root, "rev-parse", "HEAD").strip()
    status_output = _git_output(root, "status", "--short", "--untracked-files=all")
    status = [line for line in status_output.splitlines() if line]
    tracked_patch = _git_bytes(root, "diff", "--binary", "HEAD", "--")
    untracked_output = _git_bytes(root, "ls-files", "--others", "--exclude-standard", "-z")
    untracked_paths = [path for path in untracked_output.decode().split("\0") if path]
    untracked = []
    for relative in untracked_paths:
        record = hash_path(root / relative).to_record()
        record["path"] = relative
        untracked.append(record)
    untracked_digest = hashlib.sha256(
        b"".join(
            relative.encode() + b"\0" + str(record["sha256"]).encode() + b"\0"
            for relative, record in zip(untracked_paths, untracked, strict=True)
        )
    ).hexdigest()
    return {
        "diff_sha256": hashlib.sha256(tracked_patch).hexdigest(),
        "git_sha": sha,
        "is_dirty": bool(status),
        "root": str(root),
        "status": status,
        "untracked": untracked,
        "untracked_sha256": untracked_digest,
    }


def invocation_environment(environment: Mapping[str, str]) -> dict[str, str]:
    """Capture a fixed, non-secret inherited environment subset."""

    return {key: environment[key] for key in INHERITED_ENVIRONMENT_KEYS if key in environment}


def effective_environment(command: CommandSpec, base: Mapping[str, str]) -> dict[str, str]:
    """Compose the exact environment used for one child process."""

    result = {key: base[key] for key in INHERITED_ENVIRONMENT_KEYS if key in base}
    result.update(command.env)
    if path_value := result.get("PATH"):
        result["PATH"] = os.pathsep.join(
            str((command.cwd / entry).resolve(strict=False)) if entry and not Path(entry).is_absolute() else entry
            for entry in path_value.split(os.pathsep)
        )
    return result


def command_environment_record(command: CommandSpec, base: Mapping[str, str]) -> dict[str, str]:
    """Record inherited allowlisted variables plus every explicit override."""

    return dict(sorted(effective_environment(command, base).items()))


def command_record(command: CommandSpec, base: Mapping[str, str]) -> dict[str, object]:
    """Return one command's static run-manifest record."""

    return {
        "argv": list(command.argv),
        "cwd": str(command.cwd.resolve(strict=False)),
        "env": command_environment_record(command, base),
        "expected_stdout_csv_record": (
            list(command.expected_stdout_csv_record) if command.expected_stdout_csv_record is not None else None
        ),
        "expected_stdout_lines": (
            list(command.expected_stdout_lines) if command.expected_stdout_lines is not None else None
        ),
        "label": command.label,
        "runtime_artifacts": [str(path) for path in command.runtime_artifacts],
        "runtime_executables": list(command.runtime_executables),
        "timeout_sec": command.timeout_sec,
    }


def executable_record(command: CommandSpec, environment: Mapping[str, str]) -> dict[str, object]:
    """Resolve and hash the actual executable immediately before a process."""

    requested = command.argv[0]
    try:
        resolved = resolve_executable(command, environment)
    except FileNotFoundError:
        return {"requested": requested, "resolved_path": None, "sha256": None}
    return {
        "requested": requested,
        "resolved_path": str(resolved),
        "sha256": sha256_file(resolved),
    }


def runtime_provenance_record(command: CommandSpec, environment: Mapping[str, str]) -> dict[str, object]:
    """Hash adapter-declared nested executables and generated runtime artifacts."""

    executables = [_program_record(requested, command.cwd, environment) for requested in command.runtime_executables]
    artifacts = [hash_path(path).to_record() for path in command.runtime_artifacts]
    return {"artifacts": artifacts, "executables": executables}


def resolve_executable(command: CommandSpec, environment: Mapping[str, str]) -> Path:
    """Resolve the exact absolute executable used for a command."""

    return _resolve_program(command.argv[0], command.cwd, environment)


def _program_record(requested: str, cwd: Path, environment: Mapping[str, str]) -> dict[str, object]:
    resolved = _resolve_program(requested, cwd, environment)
    return {"requested": requested, "resolved_path": str(resolved), "sha256": sha256_file(resolved)}


def _resolve_program(requested: str, cwd: Path, environment: Mapping[str, str]) -> Path:
    resolved: Path | None
    if os.sep in requested:
        executable = Path(requested)
        if not executable.is_absolute():
            executable = cwd / executable
        resolved = Path(os.path.abspath(executable))
    else:
        found = shutil.which(requested, path=environment.get("PATH"))
        resolved = Path(os.path.abspath(found)) if found is not None else None
    if resolved is None or not resolved.is_file():
        raise FileNotFoundError(f"paper command executable not found: {requested}")
    return resolved


def lane_input_records(lane: ProcessLane) -> list[dict[str, object]]:
    """Hash adapter-declared inputs before any build or preparation hook."""

    return [hash_path(path).to_record() for path in lane.input_paths]


def _git_output(root: Path, *arguments: str) -> str:
    return subprocess.run(
        ("git", "-C", str(root), *arguments),
        check=True,
        capture_output=True,
        text=True,
    ).stdout


def _git_bytes(root: Path, *arguments: str) -> bytes:
    return subprocess.run(
        ("git", "-C", str(root), *arguments),
        check=True,
        capture_output=True,
    ).stdout
