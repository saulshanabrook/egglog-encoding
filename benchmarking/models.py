"""Define dependency-free benchmark identities, invariants, and backend metadata.

This module owns endpoint selection, comparison scope, and the uniqueness rules
required by cache-backed statistics. Feature-local requests, subprocess
outcomes, persisted records, and derived report rows live beside their owners.
"""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass
from pathlib import Path
from typing import Literal

Status = Literal["success", "timed-out", "failure"]
Backend = str
Treatment = Literal["off", "term", "proofs", "proof-testing", "causal-proof-testing"]
DetailLevel = Literal["summary", "files", "phases", "rulesets"]

TREATMENTS: tuple[Treatment, ...] = (
    "off",
    "term",
    "proofs",
    "proof-testing",
    "causal-proof-testing",
)


@dataclass(frozen=True)
class BackendSpec:
    treatments: tuple[Treatment, ...]
    flags: tuple[str, ...]
    cargo_features: tuple[str, ...] = ()


BACKEND_SPECS: dict[Backend, BackendSpec] = {
    "main": BackendSpec(TREATMENTS, ()),
    "dd": BackendSpec(("term", "proofs"), ("--backend", "dd"), ("dd-backend",)),
}


def backend_spec(backend: Backend) -> BackendSpec:
    """Return metadata for a configured backend."""

    try:
        return BACKEND_SPECS[backend]
    except KeyError as error:
        raise ValueError(f"unknown backend: {backend}") from error


def backend_cargo_features(backends: Sequence[Backend]) -> tuple[str, ...]:
    """Return deduplicated Cargo features required by ``backends``."""

    return tuple(dict.fromkeys(feature for backend in backends for feature in backend_spec(backend).cargo_features))


def validate_backend_treatment(backend: Backend, treatment: Treatment) -> None:
    """Reject one endpoint combination unsupported by its backend."""

    supported = backend_spec(backend).treatments
    if treatment not in supported:
        raise ValueError(
            f"backend {backend} does not support treatment {treatment}; supported treatments: {','.join(supported)}"
        )


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
class ResolvedTarget:
    request: TargetRequest
    row: TargetRow
    binary_sha256: str
    binary_path: Path | None

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
    """One unresolved target/backend/treatment selected by the CLI."""

    target: TargetRequest
    backend: Backend
    treatment: Treatment

    def __post_init__(self) -> None:
        validate_backend_treatment(self.backend, self.treatment)


@dataclass(frozen=True)
class BenchmarkEndpoint:
    """One resolved target/backend/treatment addressed by benchmark cache rows."""

    target: ResolvedTarget
    backend: Backend
    treatment: Treatment

    def __post_init__(self) -> None:
        validate_backend_treatment(self.backend, self.treatment)

    @property
    def cache_identity(self) -> tuple[str, Backend, Treatment]:
        """Return the endpoint coordinates shared by all of its file keys."""

        return (self.target.binary_sha256, self.backend, self.treatment)


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
