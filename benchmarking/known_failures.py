"""Checked-in benchmark exclusions shared by collection and cached reports.

Remove an entry when its failure is resolved. Explicit files and force-run do
not bypass this policy. Content identities also cover relocated input copies;
an edited workload requires its own evidence. No observations are synthesized.
"""

from __future__ import annotations

from dataclasses import dataclass

from .engines import TREATMENT_SPECS, Treatment
from .models import DisequalityEncoding, FileSpec


@dataclass(frozen=True)
class KnownFailure:
    file: str
    file_sha256: str
    treatments: tuple[Treatment, ...]
    disequality_encodings: tuple[DisequalityEncoding, ...]
    reason: str
    evidence: str
    fact_directory_sha256: str = ""


KNOWN_FAILURES = (
    KnownFailure(
        "benchmarks/disequality/parameter-analysis.egg",
        "sha256:5aa2025d8c0056378264a0609f0651af442ea958c3cd2ae1ea31f91f958961bd",
        ("proofs",),
        ("nee",),
        "parameter proof recording repeatedly failed or timed out; the nightly job reported OOM kills",
        "https://nightly.cs.washington.edu/logs/2026-10-06-000026-019413-egglog-encoding-codex_2fparam-07-streaming.log",
    ),
)


def known_failure_reason(
    file: FileSpec,
    treatment: Treatment,
    disequality_encoding: DisequalityEncoding = "nee",
) -> str | None:
    """Match an affected physical input and mode without opening files or caches."""

    physical = file.for_engine(TREATMENT_SPECS[treatment].engine)
    for failure in KNOWN_FAILURES:
        if (
            (physical.sha256, physical.fact_directory_sha256) == (failure.file_sha256, failure.fact_directory_sha256)
            and treatment in failure.treatments
            and disequality_encoding in failure.disequality_encodings
        ):
            return f"known failure: {failure.reason} ({failure.evidence})"
    return None
