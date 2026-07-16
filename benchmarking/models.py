"""Define dependency-free benchmark identities, invariants, and backend metadata.

This module owns shared values, canonical cell ordering, and the uniqueness
rules required by cache-backed statistics. Feature-local requests, subprocess
outcomes, persisted records, and DuckDB result rows live beside their owners.
"""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass
from pathlib import Path
from typing import Literal

Status = Literal["success", "timed-out", "failure"]
Backend = str
Treatment = Literal["off", "term", "proofs"]
DEFAULT_BACKENDS: tuple[Backend, ...] = ("main",)


@dataclass(frozen=True)
class BackendSpec:
    display_name: str
    treatments: tuple[Treatment, ...]
    flags: tuple[str, ...]
    cargo_features: tuple[str, ...] = ()


BACKEND_SPECS: dict[Backend, BackendSpec] = {
    "main": BackendSpec("main", ("off", "term", "proofs"), ()),
    "dd": BackendSpec("DD", ("term", "proofs"), ("--backend", "dd"), ("dd-backend",)),
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
class BenchmarkSpec:
    files: tuple[FileSpec, ...]
    treatments: tuple[Treatment, ...]
    rounds: int
    timeout_sec: int
    backends: tuple[Backend, ...] = DEFAULT_BACKENDS


@dataclass(frozen=True)
class BenchmarkCell:
    backend: Backend
    treatment: Treatment


def backend_treatment_cells(
    backends: Sequence[Backend],
    treatments: Sequence[Treatment],
) -> tuple[BenchmarkCell, ...]:
    """Return supported cells in canonical backend-then-treatment order."""

    cells: list[BenchmarkCell] = []
    requested = ",".join(treatments)
    for backend in backends:
        supported = backend_spec(backend).treatments
        backend_cells = tuple(BenchmarkCell(backend, treatment) for treatment in treatments if treatment in supported)
        if not backend_cells:
            raise ValueError(
                f"backend {backend} has no supported treatments in requested set {requested}; "
                f"supported treatments: {','.join(supported)}"
            )
        cells.extend(backend_cells)
    return tuple(cells)


def benchmark_cells(spec: BenchmarkSpec) -> tuple[BenchmarkCell, ...]:
    """Return the canonical cells for a benchmark request."""

    return backend_treatment_cells(spec.backends, spec.treatments)


def backend_has_treatment(spec: BenchmarkSpec, backend: Backend, treatment: Treatment) -> bool:
    """Return whether a backend/treatment cell is selected by ``spec``."""

    return any(cell.backend == backend and cell.treatment == treatment for cell in benchmark_cells(spec))


def shared_backend_treatments(
    spec: BenchmarkSpec,
    baseline_backend: Backend,
    candidate_backend: Backend,
) -> tuple[Treatment, ...]:
    """Return selected treatments supported by both backends."""

    return tuple(
        treatment
        for treatment in spec.treatments
        if treatment in backend_spec(baseline_backend).treatments
        and treatment in backend_spec(candidate_backend).treatments
    )


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


def validate_unique_target_binaries(targets: Sequence[ResolvedTarget]) -> None:
    """Reject targets that would select the same cached observations."""

    by_binary: dict[str, ResolvedTarget] = {}
    for target in targets:
        previous = by_binary.get(target.binary_sha256)
        if previous is not None:
            raise ValueError(
                f"benchmark targets {previous.display_label!r} and {target.display_label!r} produced the same "
                f"binary SHA-256 ({target.binary_sha256[:12]}); select each binary only once"
            )
        by_binary[target.binary_sha256] = target


@dataclass(frozen=True)
class EstimateKey:
    binary_sha256: str
    file_sha256: str
    treatment: Treatment
    timeout_sec: int
    backend: Backend = "main"
    fact_directory_sha256: str = ""

    @classmethod
    def for_cell(
        cls,
        target: ResolvedTarget,
        file_spec: FileSpec,
        backend: Backend,
        treatment: Treatment,
        timeout_sec: int,
    ) -> EstimateKey:
        """Build the ordinary-report identity shared by collection and reporting."""
        return cls(
            binary_sha256=target.binary_sha256,
            file_sha256=file_spec.sha256,
            treatment=treatment,
            timeout_sec=timeout_sec,
            backend=backend,
            fact_directory_sha256=file_spec.fact_directory_sha256,
        )
