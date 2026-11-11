"""Describe benchmark treatments and engine-specific workload commands."""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Literal, Protocol

type Engine = Literal["egglog", "egg"]
type Treatment = Literal[
    "off",
    "term",
    "proofs",
    "proofs-no-generated-frontend-effects",
    "proof-extraction",
    "proof-testing",
    "egg",
    "egg-proofs",
    "egg-proof-extraction",
    "egg-proof-testing",
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


TREATMENT_SPECS: dict[Treatment, TreatmentSpec] = {
    "off": TreatmentSpec("egglog", ()),
    "term": TreatmentSpec("egglog", ("--term-encoding",)),
    "proofs": TreatmentSpec("egglog", ("--proofs",)),
    "proofs-no-generated-frontend-effects": TreatmentSpec(
        "egglog", ("--proofs", "--skip-generated-frontend-effects")
    ),
    "proof-extraction": TreatmentSpec("egglog", ("--proof-extraction",)),
    "proof-testing": TreatmentSpec("egglog", ("--proof-testing",)),
    "egg": TreatmentSpec("egg", ("--proof-mode", "off")),
    "egg-proofs": TreatmentSpec("egg", ("--proof-mode", "enabled")),
    "egg-proof-extraction": TreatmentSpec("egg", ("--proof-mode", "extract")),
    "egg-proof-testing": TreatmentSpec("egg", ("--proof-mode", "check")),
}
TREATMENTS = tuple(TREATMENT_SPECS)

MATH_WORKLOAD_PATH = Path("egglog-experimental/tests/math-microbenchmark-rational.egg")


def validate_engine_workload(file_spec: WorkloadFile, treatment: Treatment) -> None:
    """Reject workload features unsupported by the selected treatment engine."""

    if TREATMENT_SPECS[treatment].engine != "egg":
        return
    project_fixture = Path(__file__).resolve().parents[1] / MATH_WORKLOAD_PATH
    if file_spec.absolute_path != project_fixture.resolve():
        raise ValueError(
            f"treatment {treatment} only supports {MATH_WORKLOAD_PATH.as_posix()}; cannot run {file_spec.display_path}"
        )
    if file_spec.fact_directory is not None:
        raise ValueError(f"treatment {treatment} does not support --fact-directory")
