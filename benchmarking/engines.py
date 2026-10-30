"""Describe benchmark treatments and engine-specific workload commands."""

from __future__ import annotations

import hashlib
from dataclasses import dataclass
from pathlib import Path
from typing import Literal, Protocol

type Engine = Literal["egglog", "egg", "egg-de", "egg-ee", "egg-nee", "egg-oee"]
type Treatment = Literal[
    "off",
    "term",
    "proofs",
    "proof-extraction",
    "proof-testing",
    "egg",
    "egg-proofs",
    "egg-proof-extraction",
    "egg-proof-testing",
    "egg-de",
    "egg-ee",
    "egg-nee",
    "egg-oee",
]


class WorkloadFile(Protocol):
    @property
    def display_path(self) -> str: ...

    @property
    def absolute_path(self) -> Path: ...

    @property
    def fact_directory(self) -> Path | None: ...


@dataclass(frozen=True)
class TreatmentSpec:
    engine: Engine
    flags: tuple[str, ...]
    timing_summary: bool = True


TREATMENT_SPECS: dict[Treatment, TreatmentSpec] = {
    "off": TreatmentSpec("egglog", ()),
    "term": TreatmentSpec("egglog", ("--term-encoding",)),
    "proofs": TreatmentSpec("egglog", ("--proofs",)),
    "proof-extraction": TreatmentSpec("egglog", ("--proof-extraction",)),
    "proof-testing": TreatmentSpec("egglog", ("--proof-testing",)),
    "egg": TreatmentSpec("egg", ("--proof-mode", "off")),
    "egg-proofs": TreatmentSpec("egg", ("--proof-mode", "enabled")),
    "egg-proof-extraction": TreatmentSpec("egg", ("--proof-mode", "extract")),
    "egg-proof-testing": TreatmentSpec("egg", ("--proof-mode", "check")),
    "egg-de": TreatmentSpec("egg-de", (), timing_summary=False),
    "egg-ee": TreatmentSpec("egg-ee", (), timing_summary=False),
    "egg-nee": TreatmentSpec("egg-nee", (), timing_summary=False),
    "egg-oee": TreatmentSpec("egg-oee", (), timing_summary=False),
}
TREATMENTS = tuple(TREATMENT_SPECS)

MATH_WORKLOAD_PATH = Path("egglog-experimental/tests/math-microbenchmark-rational.egg")
MATH_WORKLOAD_SHA256 = "sha256:29e120079c588d0bf079891b393ae041ec4e1a45d369114cde3754e5c6b7878f"
# The frozen round-twelve distribution witness uses operands from the unchanged
# integration-by-parts closure; its complete input identity fixes both endpoints.
MATH12_WORKLOAD_PATH = Path("benchmarks/corpus/math/math-iteration-12.egg")
MATH12_WORKLOAD_SHA256 = "sha256:fde0b4a62c8d5904014babd00dfce11fcab429fa26125280ccd4515f9dd6915f"
MATH_WORKLOAD_ARGUMENTS: dict[str, tuple[str, ...]] = {
    MATH_WORKLOAD_SHA256: (),
    MATH12_WORKLOAD_SHA256: ("--math12",),
}
PARAMETER_WORKLOAD_PATH = Path("benchmarks/disequality/parameter-analysis.egg")


def math_workload_arguments(file_spec: WorkloadFile) -> tuple[str, ...]:
    """Derive the exact native schedule and witness from registered complete input bytes."""
    actual = "sha256:" + hashlib.sha256(file_spec.absolute_path.read_bytes()).hexdigest()
    try:
        return MATH_WORKLOAD_ARGUMENTS[actual]
    except KeyError:
        raise ValueError(
            "native egg only supports registered Math workloads (fixed Math11 and Math12); "
            f"cannot run {file_spec.display_path}"
        ) from None


def validate_engine_workload(file_spec: WorkloadFile, treatment: Treatment) -> None:
    """Reject workload features unsupported by the selected treatment engine."""

    engine = TREATMENT_SPECS[treatment].engine
    if engine == "egglog":
        return
    if file_spec.fact_directory is not None:
        raise ValueError(f"treatment {treatment} does not support --fact-directory")
    if engine != "egg":
        if file_spec.absolute_path.suffix != ".in":
            raise ValueError(f"treatment {treatment} requires a native .in workload")
        return
    math_workload_arguments(file_spec)
