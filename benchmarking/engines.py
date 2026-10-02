"""Describe benchmark treatments and engine-specific workload commands."""

from __future__ import annotations

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
PARAMETER_WORKLOAD_PATH = Path("benchmarks/disequality/parameter-analysis.egg")


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
    project_fixture = Path(__file__).resolve().parents[1] / MATH_WORKLOAD_PATH
    if file_spec.absolute_path != project_fixture.resolve():
        raise ValueError(
            f"treatment {treatment} only supports {MATH_WORKLOAD_PATH.as_posix()}; cannot run {file_spec.display_path}"
        )
