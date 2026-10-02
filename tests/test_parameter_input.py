"""Keep the supplied source/input unchanged and verify one-way preparation."""

from __future__ import annotations

import hashlib

import pytest

from benchmarks.disequality.native import generate


@pytest.mark.parametrize(
    "directory,expected",
    [
        ("de", "cfa787ff01e39bd37f66763d7dd0909b7c02a184a5aeef2ecd2e8fe28bb402b9"),
        ("ee", "c5eeb9c43a58489ef24053b539c7e5597517b627ac4939cc7ee57e917bbcd7c2"),
        ("nee-no-saturation", "8856152bc715f61743cdb3732a3a354a908c15da3d8f67003817c6a6c59c0549"),
        ("nee-with-saturation", "b914e54ebcadb62b7c06c5767a1e257b3541184b78c038bd81a5b16270e68c33"),
    ],
)
def test_vendored_drivers_are_byte_identical(directory: str, expected: str) -> None:
    source = generate.INPUT.parent / "native/authors" / directory / "main.rs"
    assert hashlib.sha256(source.read_bytes()).hexdigest() == expected


def test_conversion_preserves_original_constraints_pairs_and_order() -> None:
    source = "1\n(f 2)\n(g 3 4)\n(h 5 1 2)\nunused native tail\n"
    program = generate.source_program(source, equalities=1, disequalities=1)
    assert [line for line in program.splitlines() if line.startswith("(")] == [
        "(datatype Term (N1) (N2) (N3) (N4) (N5) (f Term) (g Term Term) (h Term Term Term))",
        "(disequal (N1) (N2))",
        "(disequal (N1) (N3))",
        "(disequal (N1) (N4))",
        "(disequal (N2) (N3))",
        "(disequal (N2) (N4))",
        "(disequal (N3) (N4))",
        "(union (N1) (f (N2)))",
        "(disequal (g (N3) (N4)) (h (N5) (N1) (N2)))",
        "(check-contradiction)",
    ]
    assert hashlib.sha256(source.encode()).hexdigest() in program
    assert "unused native tail" not in program


@pytest.mark.parametrize("source", ["1\n", "1\n\n"])
def test_conversion_rejects_missing_expressions(source: str) -> None:
    with pytest.raises(ValueError, match="not enough|empty"):
        generate.source_program(source, equalities=1, disequalities=0)


def test_committed_corpus_and_translation_are_reproducible() -> None:
    native = generate.INPUT.read_bytes()
    assert hashlib.sha256(native).hexdigest() == "6e9114194d92079a14272c25c11012ddf21753f655d5d39178fbba96b150dd3d"
    assert len(native.splitlines()) == 400_000
    program = generate.OUTPUT.read_text()
    assert program == generate.source_program(native.decode())
    assert program.count("\n(union ") == 100_000
    assert program.count("\n(disequal ") == 10_006
