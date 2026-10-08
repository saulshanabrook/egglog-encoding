"""Keep exclusions bound to the documented input and affected execution modes."""

from __future__ import annotations

import hashlib
from dataclasses import replace
from pathlib import Path

import pytest

from benchmarking.known_failures import KNOWN_FAILURES, known_failure_reason
from benchmarking.models import FileSpec, Treatment


def test_parameter_exclusion_matches_the_checked_in_input_even_when_relocated(tmp_path: Path) -> None:
    failure = KNOWN_FAILURES[0]
    original = Path(__file__).resolve().parents[1] / failure.file
    file = FileSpec("copy.egg", tmp_path / "copy.egg", "sha256:" + hashlib.sha256(original.read_bytes()).hexdigest())

    reason = known_failure_reason(file, "proofs")

    assert reason is not None
    assert failure.reason in reason
    assert failure.evidence in reason
    assert known_failure_reason(replace(file, sha256="sha256:changed"), "proofs") is None
    assert known_failure_reason(replace(file, fact_directory_sha256="sha256:facts"), "proofs") is None
    assert known_failure_reason(file, "proofs", "ee") is None
    assert not file.absolute_path.exists()


@pytest.mark.parametrize("treatment", ["off", "term", "proof-extraction", "proof-testing", "egg-proofs"])
def test_undocumented_modes_remain_eligible(treatment: Treatment) -> None:
    failure = KNOWN_FAILURES[0]
    file = FileSpec(failure.file, Path(failure.file), failure.file_sha256)

    assert known_failure_reason(file, treatment) is None
