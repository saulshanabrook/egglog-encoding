"""Define dependency-free benchmark identities and invariants.

This module owns endpoint selection, comparison scope, and the uniqueness rules
required by cache-backed statistics. Feature-local requests, subprocess
outcomes, persisted records, and derived report rows live beside their owners.
"""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass
from pathlib import Path
from typing import Literal

from .engines import TREATMENT_SPECS, Engine, Treatment

Status = Literal["success", "timed-out", "failure"]
DisequalityEncoding = Literal["nee", "ee"]
DetailLevel = Literal["summary", "files", "phases", "rulesets"]


@dataclass(frozen=True)
class TargetRow:
    source: str
    path: str
    git_ref: str
    git_sha: str
    is_dirty: bool
    label: str | None = None


@dataclass(frozen=True)
class FileSpec:
    display_path: str
    absolute_path: Path
    sha256: str
    fact_directory: Path | None = None
    fact_directory_sha256: str = ""


def validate_unique_file_identities(files: Sequence[FileSpec]) -> None:
    """Reject workloads that would select the same cached observations."""

    by_identity: dict[tuple[str, str], FileSpec] = {}
    for file in files:
        identity = (file.sha256, file.fact_directory_sha256)
        previous = by_identity.get(identity)
        if previous is not None:
            raise ValueError(
                f"benchmark files {previous.display_path!r} and {file.display_path!r} have identical "
                "file and fact-directory hashes; select each workload only once"
            )
        by_identity[identity] = file


@dataclass(frozen=True)
class TargetRequest:
    raw: str
    source: str
    label: str | None

    @property
    def is_label_lookup(self) -> bool:
        return self.label is not None and self.source == ""


@dataclass(frozen=True)
class EngineBinary:
    engine: Engine
    sha256: str
    path: Path | None


@dataclass(frozen=True)
class ResolvedTarget:
    request: TargetRequest
    row: TargetRow
    binary_sha256: str
    binary_path: Path | None
    engine_binaries: tuple[EngineBinary, ...] = ()
    primary_engine: Engine | None = None

    def binary_sha256_for(self, treatment: Treatment) -> str:
        engine = TREATMENT_SPECS[treatment].engine
        for binary in self.engine_binaries:
            if binary.engine == engine:
                return binary.sha256
        if engine == "egglog" and self.primary_engine in (None, "egglog"):
            return self.binary_sha256
        raise ValueError(f"target {self.display_label} has no {engine} binary")

    def binary_path_for(self, treatment: Treatment) -> Path | None:
        engine = TREATMENT_SPECS[treatment].engine
        for binary in self.engine_binaries:
            if binary.engine == engine:
                return binary.path
        if engine == "egglog" and self.primary_engine in (None, "egglog"):
            return self.binary_path
        raise ValueError(f"target {self.display_label} has no {engine} binary")

    @property
    def display_label(self) -> str:
        if self.row.label:
            return self.row.label
        if self.row.git_ref != "HEAD":
            return self.row.git_ref
        if self.row.git_sha:
            return self.row.git_sha[:12]
        return Path(self.row.path).name


@dataclass(frozen=True)
class EndpointRequest:
    """One unresolved target/treatment selected by the CLI."""

    target: TargetRequest
    treatment: Treatment
    disequality_encoding: DisequalityEncoding = "nee"

    def __post_init__(self) -> None:
        if TREATMENT_SPECS[self.treatment].engine == "egg" and self.disequality_encoding != "nee":
            raise ValueError("disequality encoding selection is only supported by egglog treatments")


@dataclass(frozen=True)
class BenchmarkEndpoint:
    """One resolved target/treatment addressed by benchmark cache rows."""

    target: ResolvedTarget
    treatment: Treatment
    disequality_encoding: DisequalityEncoding = "nee"

    @property
    def cache_identity(self) -> tuple[str, Treatment, DisequalityEncoding]:
        """Return the endpoint coordinates shared by all of its file keys."""

        return (self.target.binary_sha256_for(self.treatment), self.treatment, self.disequality_encoding)


@dataclass(frozen=True)
class ComparisonSpec:
    """The exact baseline/candidate pair and workloads selected for one report."""

    baseline: BenchmarkEndpoint
    candidate: BenchmarkEndpoint
    files: tuple[FileSpec, ...]
    rounds: int
    timeout_sec: int

    def __post_init__(self) -> None:
        if not self.files:
            raise ValueError("benchmark comparison requires at least one file")
        validate_unique_file_identities(self.files)
        if self.rounds < 1:
            raise ValueError("benchmark rounds must be positive")
        if self.timeout_sec < 1:
            raise ValueError("benchmark timeout must be positive")
        if self.baseline.cache_identity == self.candidate.cache_identity:
            raise ValueError("baseline and candidate endpoints must be different")
