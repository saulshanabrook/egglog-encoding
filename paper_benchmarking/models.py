"""Define paper harness selections, commands, lanes, and process outcomes."""

from __future__ import annotations

import math
import re
from collections.abc import Mapping
from dataclasses import dataclass, field
from pathlib import Path
from types import MappingProxyType
from typing import Literal

type Preset = Literal["quick", "representative", "artifact-full"]
type Evaluation = Literal["math", "pointer", "herbie"]
type EvaluationSelection = Literal["math", "pointer", "herbie", "all"]
type ProcessPhase = Literal["build", "prepare", "observation", "validate"]
type ProcessStatus = Literal["success", "failure", "timed-out", "infrastructure-error"]

PRESETS: tuple[Preset, ...] = ("quick", "representative", "artifact-full")
EVALUATIONS: tuple[Evaluation, ...] = ("math", "pointer", "herbie")
EVALUATION_SELECTIONS: tuple[EvaluationSelection, ...] = (*EVALUATIONS, "all")

_SAFE_LABEL = re.compile(r"[a-z0-9][a-z0-9._-]*\Z")


@dataclass(frozen=True)
class CommandSpec:
    """One exact child-process invocation declared by an evaluation adapter."""

    label: str
    argv: tuple[str, ...]
    cwd: Path
    timeout_sec: float
    env: Mapping[str, str] = field(default_factory=dict)
    expected_stdout_lines: tuple[str, ...] | None = None
    expected_stdout_csv_record: tuple[str, str, int] | None = None
    runtime_executables: tuple[str, ...] = ()
    runtime_artifacts: tuple[Path, ...] = ()

    def __post_init__(self) -> None:
        if _SAFE_LABEL.fullmatch(self.label) is None:
            raise ValueError(f"invalid process label: {self.label!r}")
        if not self.argv or not self.argv[0]:
            raise ValueError("process argv must contain a nonempty executable")
        if any("\0" in argument for argument in self.argv):
            raise ValueError("process argv must not contain NUL bytes")
        if self.timeout_sec <= 0 or not math.isfinite(self.timeout_sec):
            raise ValueError("process timeout must be positive and finite")
        object.__setattr__(self, "cwd", self.cwd.expanduser().resolve(strict=False))
        normalized_env: dict[str, str] = {}
        for key, value in sorted(self.env.items()):
            if not key or "=" in key or "\0" in key or "\0" in value:
                raise ValueError(f"invalid process environment entry: {key!r}")
            normalized_env[key] = value
        object.__setattr__(self, "env", MappingProxyType(normalized_env))
        if self.expected_stdout_lines is not None and any("\0" in value for value in self.expected_stdout_lines):
            raise ValueError("process output expectations must not contain NUL bytes")
        if self.expected_stdout_csv_record is not None:
            benchmark, engine, size = self.expected_stdout_csv_record
            if not benchmark or not engine or "\0" in benchmark or "\0" in engine or size < 0:
                raise ValueError("invalid expected stdout CSV record")
        if any(not executable or "\0" in executable for executable in self.runtime_executables):
            raise ValueError("runtime executable names must be nonempty and contain no NUL bytes")
        object.__setattr__(
            self,
            "runtime_artifacts",
            tuple(path.expanduser().absolute() for path in self.runtime_artifacts),
        )


@dataclass(frozen=True)
class ProcessLane:
    """One adapter-defined lane with untimed hooks and timed observations."""

    evaluation: Evaluation
    name: str
    observations: tuple[CommandSpec, ...]
    build: tuple[CommandSpec, ...] = ()
    prepare: tuple[CommandSpec, ...] = ()
    validate: tuple[CommandSpec, ...] = ()
    input_paths: tuple[Path, ...] = ()
    versions: Mapping[str, str] = field(default_factory=dict)

    def __post_init__(self) -> None:
        if _SAFE_LABEL.fullmatch(self.name) is None:
            raise ValueError(f"invalid lane name: {self.name!r}")
        if not self.observations:
            raise ValueError(f"paper benchmark lane {self.name!r} has no observations")
        normalized_versions: dict[str, str] = {}
        for key, value in sorted(self.versions.items()):
            if not key or "\0" in key or "\0" in value:
                raise ValueError(f"invalid lane version entry: {key!r}")
            normalized_versions[key] = value
        object.__setattr__(self, "input_paths", tuple(path.expanduser().absolute() for path in self.input_paths))
        object.__setattr__(self, "versions", MappingProxyType(normalized_versions))


@dataclass(frozen=True)
class ProcessOutcome:
    """Normalized result from one child process."""

    status: ProcessStatus
    started_at: str
    finished_at: str
    wall_sec: float | None
    exit_code: int | None = None
    signal: int | None = None
    error_message: str | None = None


def expand_evaluations(selection: EvaluationSelection) -> tuple[Evaluation, ...]:
    """Expand the public ``all`` selector in stable paper order."""

    if selection == "all":
        return EVALUATIONS
    return (selection,)
