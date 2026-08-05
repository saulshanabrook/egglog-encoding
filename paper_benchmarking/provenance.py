"""Collect explicit invocation, executable, repository, input, and machine provenance."""

from __future__ import annotations

import os
import platform
import shutil
import subprocess
from collections.abc import Mapping
from datetime import UTC, datetime
from pathlib import Path

from .hashing import hash_path, sha256_file
from .models import CommandSpec, ProcessLane

RECORDED_ENVIRONMENT_KEYS = (
    "CARGO_HOME",
    "HOME",
    "LANG",
    "LC_ALL",
    "PATH",
    "PLTUSERHOME",
    "RACKET_DIR",
    "RUSTFLAGS",
    "RUSTUP_TOOLCHAIN",
    "SHELL",
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
    return {
        "git_sha": sha,
        "is_dirty": bool(status),
        "root": str(root),
        "status": status,
    }


def invocation_environment(environment: Mapping[str, str]) -> dict[str, str]:
    """Capture a fixed, non-secret inherited environment subset."""

    return {key: environment[key] for key in RECORDED_ENVIRONMENT_KEYS if key in environment}


def effective_environment(command: CommandSpec, base: Mapping[str, str]) -> dict[str, str]:
    """Compose the exact environment used for one child process."""

    result = dict(base)
    result.update(command.env)
    return result


def command_environment_record(command: CommandSpec, base: Mapping[str, str]) -> dict[str, str]:
    """Record inherited allowlisted variables plus every explicit override."""

    effective = effective_environment(command, base)
    keys = set(RECORDED_ENVIRONMENT_KEYS) | set(command.env)
    return {key: effective[key] for key in sorted(keys) if key in effective}


def command_record(command: CommandSpec, base: Mapping[str, str]) -> dict[str, object]:
    """Return one command's static run-manifest record."""

    return {
        "argv": list(command.argv),
        "cwd": str(command.cwd.resolve(strict=False)),
        "env": command_environment_record(command, base),
        "label": command.label,
        "timeout_sec": command.timeout_sec,
    }


def executable_record(command: CommandSpec, environment: Mapping[str, str]) -> dict[str, object]:
    """Resolve and hash the actual executable immediately before a process."""

    requested = command.argv[0]
    resolved: Path | None
    if os.sep in requested:
        executable = Path(requested)
        if not executable.is_absolute():
            executable = command.cwd / executable
        resolved = executable.resolve(strict=False)
    else:
        found = shutil.which(requested, path=environment.get("PATH"))
        resolved = Path(found).resolve(strict=False) if found is not None else None
    if resolved is None or not resolved.is_file():
        return {"requested": requested, "resolved_path": None, "sha256": None}
    return {
        "requested": requested,
        "resolved_path": str(resolved),
        "sha256": sha256_file(resolved),
    }


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
