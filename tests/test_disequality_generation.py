"""Verify artifact extraction, deterministic conversion, and fail-closed seed selection."""

from __future__ import annotations

import hashlib
import random
import subprocess
import zipfile
from pathlib import Path

import pytest

from benchmarks.disequality import generate


def test_committed_workload_identity_and_counts() -> None:
    digest = hashlib.sha256()
    equalities = disequalities = 0
    with (generate.ROOT / "benchmarks/disequality/parameter-analysis.egg").open("rb") as source:
        for line in source:
            digest.update(line)
            equalities += line.startswith(b"(union ")
            disequalities += line.startswith(b"(disequal ")
    assert (equalities, disequalities) == (100_000, 10_010)
    assert digest.hexdigest() == "88ea961380031ea7cd46f805888bdba638d3a86cb8da67191938044abdae83f3"


def test_unchanged_generator_continues_its_seeded_stream(tmp_path: Path) -> None:
    generator = tmp_path / "generator.py"
    original = (
        "from random import randint\ndef gen(depth): return str(randint(1, 5))\nfor i in range(60000): print(gen(5))\n"
    )
    generator.write_text(original)
    state = random.getstate()
    result = generate.expressions(generator, 2025, 60_004)
    expected = random.Random(2025)
    assert result == [str(expected.randint(1, 5)) for _ in range(60_004)]
    assert generate.expressions(generator, 2025, 60_004) == result
    assert generator.read_text() == original
    assert random.getstate() == state


def test_archive_member_is_verified_and_extracted_unchanged(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    content = b"# original generator\n"
    archive = tmp_path / "die-graph.zip"
    with zipfile.ZipFile(archive, "w") as output:
        output.writestr(generate.MEMBER, content)
        output.writestr("../escape.py", b"not extracted")
    monkeypatch.setattr(generate, "ARCHIVE_SHA256", hashlib.sha256(archive.read_bytes()).hexdigest())
    monkeypatch.setattr(generate, "GENERATOR_SHA256", hashlib.sha256(content).hexdigest())
    path = generate.fetch_generator(tmp_path)
    assert path.read_bytes() == content
    assert sorted(p.name for p in tmp_path.iterdir()) == ["die-graph.zip", "rand_exprs.py"]
    monkeypatch.setattr(generate, "GENERATOR_SHA256", "wrong")
    with pytest.raises(ValueError, match="generator checksum"):
        generate.fetch_generator(tmp_path)
    monkeypatch.setattr(generate, "ARCHIVE_SHA256", "wrong")
    with pytest.raises(ValueError, match="archive checksum"):
        generate.fetch_generator(tmp_path)


def test_conversion_preserves_pairs_and_order() -> None:
    source = generate.source_program(["1", "(f 2)", "(g 3 4)", "5"], 42, 1, 1)
    assert source.count("(disequal ") == 11
    assert source.count("(union ") == 1
    assert source.endswith("(disequal (N1) (f (N2)))\n(union (g (N3) (N4)) (N5))\n(check-contradiction)\n")
    assert "(disequal (N4) (N5))" in source
    with pytest.raises(ValueError, match="incorrect number"):
        generate.source_program(["1"], 42, 1, 1)


@pytest.mark.parametrize("outcomes", [[False, True], [True, False]])
def test_disagreement_never_retries(tmp_path: Path, monkeypatch: pytest.MonkeyPatch, outcomes: list[bool]) -> None:
    monkeypatch.setattr(generate, "EQUALITIES", 1)
    monkeypatch.setattr(generate, "DISEQUALITIES", 1)
    monkeypatch.setattr(generate, "expressions", lambda *_: ["1", "2", "3", "4"])
    answers = iter(outcomes)
    monkeypatch.setattr(generate, "check_candidate", lambda *_a, **_k: next(answers))
    with pytest.raises(RuntimeError, match="disagree"):
        generate.select_candidate(Path("unused"), Path("unused"), tmp_path / "out.egg", 10, 2, 1)
    assert not (tmp_path / "out.egg").exists()


def test_retry_first_success_and_proof_checks(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(generate, "EQUALITIES", 1)
    monkeypatch.setattr(generate, "DISEQUALITIES", 1)
    seeds: list[int] = []
    checked: list[tuple[str, bool]] = []

    def expressions(_generator: Path, seed: int, _count: int) -> list[str]:
        seeds.append(seed)
        return ["1", "2", "3", "4"]

    def check(_binary: Path, _candidate: Path, encoding: str, _timeout: int, *, proofs: bool = False) -> bool:
        checked.append((encoding, proofs))
        return seeds[-1] == 11

    monkeypatch.setattr(generate, "expressions", expressions)
    monkeypatch.setattr(generate, "check_candidate", check)
    output = tmp_path / "out.egg"
    assert generate.select_candidate(Path("unused"), Path("unused"), output, 10, 2, 1) == 11
    assert seeds == [10, 11]
    assert checked == [("nee", False), ("ee", False)] * 2 + [("nee", True), ("ee", True)]
    assert "; Seed: 11;" in output.read_text()
    with pytest.raises(RuntimeError, match="no contradiction"):
        generate.select_candidate(Path("unused"), Path("unused"), tmp_path / "missing.egg", 20, 1, 1)
    assert not (tmp_path / "missing.egg").exists()


@pytest.mark.parametrize("error", [RuntimeError("engine failed"), subprocess.TimeoutExpired("egglog", 1)])
def test_errors_never_retry(tmp_path: Path, monkeypatch: pytest.MonkeyPatch, error: Exception) -> None:
    monkeypatch.setattr(generate, "EQUALITIES", 1)
    monkeypatch.setattr(generate, "DISEQUALITIES", 1)
    monkeypatch.setattr(generate, "expressions", lambda *_: ["1", "2", "3", "4"])

    def fail(*_args: object, **_kwargs: object) -> bool:
        raise error

    monkeypatch.setattr(generate, "check_candidate", fail)
    with pytest.raises(type(error)):
        generate.select_candidate(Path("unused"), Path("unused"), tmp_path / "out.egg", 10, 2, 1)
    assert not (tmp_path / "out.egg").exists()


@pytest.mark.parametrize(
    "encoding,exit_code,stderr,expected",
    [
        ("nee", 0, "", True),
        ("ee", 0, "", True),
        ("nee", 1, "[ERROR] span\n    Check failed: \n    (@disequality-contradiction)\n", False),
        ("ee", 1, "[ERROR] span\n    Check failed: \n    (= (@disequality-true) (@disequality-false))\n", False),
        ("ee", 1, "Check failed: \n    (@disequality-contradiction)", None),
        ("nee", 1, "[ERROR] Unbound function", None),
        ("nee", -9, "", None),
        ("nee", 1, "Check failed: \n(other-relation)", None),
    ],
)
def test_cli_outcome_classification(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, encoding: str, exit_code: int, stderr: str, expected: bool | None
) -> None:
    candidate = tmp_path / "candidate.egg"
    candidate.write_text(generate.CHECK)
    results = iter([subprocess.CompletedProcess([], exit_code, "", stderr), subprocess.CompletedProcess([], 0, "", "")])
    monkeypatch.setattr(generate.subprocess, "run", lambda *_a, **_k: next(results))
    if expected is None:
        with pytest.raises(RuntimeError, match="candidate failed"):
            generate.check_candidate(Path("binary"), candidate, encoding, 10)
    else:
        assert generate.check_candidate(Path("binary"), candidate, encoding, 10) is expected
