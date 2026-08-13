"""Validate deterministic preparation of the disequality parameter-analysis facts."""

from __future__ import annotations

import hashlib
import json
import zipfile
from pathlib import Path

import pytest

from scripts.paper_benchmarks import prepare_parameter_analysis as prepare

ROOT = Path(__file__).resolve().parents[1]


def decoded_rows(files: dict[str, bytes], name: str) -> list[tuple[int, ...]]:
    return [tuple(map(int, line.split("\t"))) for line in files[name].decode().splitlines()]


def test_fixture_materializes_occurrence_preserving_tables() -> None:
    source = (ROOT / "tests/fixtures/disequality-parameter-exprs.in").read_text(encoding="utf-8")
    files = prepare.materialized_files(source, "0.5")

    assert decoded_rows(files, "numerals.tsv") == [
        (0, 1),
        (1, 2),
        (2, 1),
        (4, 2),
        (6, 1),
        (7, 2),
        (9, 2),
        (10, 1),
        (12, 1),
        (13, 2),
        (14, 3),
        (16, 1),
        (17, 2),
        (18, 3),
    ]
    assert decoded_rows(files, "f.tsv") == [(3, 2), (5, 4)]
    assert decoded_rows(files, "g.tsv") == [(8, 6, 7), (11, 9, 10)]
    assert decoded_rows(files, "h.tsv") == [(15, 12, 13, 14), (19, 16, 17, 18)]
    assert decoded_rows(files, "pairs.tsv") == [(0, 0, 1), (1, 3, 5), (2, 8, 11), (3, 15, 19)]
    assert decoded_rows(files, "config.tsv") == [(2,)]

    manifest = json.loads(files["manifest.json"])
    assert manifest["generation"] == {
        "disequality_pairs": 2,
        "equality_pairs": 2,
        "expressions": 8,
        "node_ids": "unique per AST occurrence, allocated postorder",
        "nodes": 20,
        "pairs": 4,
        "ratio_f32": 0.5,
        "ratio_text": "0.5",
        "source_line_slots": 9,
    }
    assert manifest["artifact"]["source_sha256"] == prepare.sha256_bytes(source.encode())


@pytest.mark.parametrize(
    ("ratio", "expected"),
    (("0", 0), ("0.5", 2), ("1", 4)),
)
def test_cutoff_matches_artifact_trailing_line_semantics(ratio: str, expected: int) -> None:
    value, cutoff = prepare.disequality_cutoff(ratio, line_slots=9, pair_count=4)
    assert 0.0 <= value <= 1.0
    assert cutoff == expected


@pytest.mark.parametrize("ratio", ("-0.1", "1.1", "nan", "inf"))
def test_cutoff_rejects_invalid_ratios(ratio: str) -> None:
    with pytest.raises(ValueError, match="ratio must"):
        prepare.disequality_cutoff(ratio, line_slots=9, pair_count=4)


@pytest.mark.parametrize("source", ("6\n1\n", "(g 1)\n1\n", "(x 1)\n1\n", "1 trailing\n2\n", "1\n"))
def test_parser_rejects_malformed_inputs(source: str) -> None:
    with pytest.raises(ValueError):
        prepare.parse_source(source)


def test_source_member_selection_rejects_ambiguous_and_unsafe_paths(tmp_path: Path) -> None:
    ambiguous = tmp_path / "ambiguous.zip"
    with zipfile.ZipFile(ambiguous, "w") as archive:
        archive.writestr("first/parameter-analysis/exprs.in", "1\n2\n")
        archive.writestr("second/parameter-analysis/exprs.in", "1\n2\n")
    with pytest.raises(ValueError, match="expected one"):
        prepare.source_member_bytes(ambiguous)

    unsafe = tmp_path / "unsafe.zip"
    with zipfile.ZipFile(unsafe, "w") as archive:
        archive.writestr("../parameter-analysis/exprs.in", "1\n2\n")
    with pytest.raises(ValueError, match="unsafe archive member"):
        prepare.source_member_bytes(unsafe)


def test_generated_directory_check_is_byte_exact(tmp_path: Path) -> None:
    source = (ROOT / "tests/fixtures/disequality-parameter-exprs.in").read_text(encoding="utf-8")
    files = prepare.materialized_files(source, "0.5")
    output = tmp_path / "facts"
    prepare.write_files(output, files, force=False)
    prepare.compare_files(output, files)

    (output / "config.tsv").write_text("1\n", encoding="utf-8")
    with pytest.raises(ValueError, match="config.tsv"):
        prepare.compare_files(output, files)


def test_committed_full_corpus_matches_manifest() -> None:
    facts = ROOT / "egglog-experimental/benchmarks/disequality/parameter-analysis-facts"
    manifest = json.loads((facts / "manifest.json").read_text(encoding="utf-8"))

    assert manifest["artifact"]["source_sha256"] == prepare.SOURCE_SHA256
    assert manifest["generation"] == {
        "disequality_pairs": 15_000,
        "equality_pairs": 15_000,
        "expressions": 60_000,
        "node_ids": "unique per AST occurrence, allocated postorder",
        "nodes": 3_728_927,
        "pairs": 30_000,
        "ratio_f32": 0.5,
        "ratio_text": "0.5",
        "source_line_slots": 60_001,
    }

    for name, expected in manifest["files"].items():
        path = facts / name
        digest = hashlib.sha256()
        rows = 0
        with path.open("rb") as source:
            for line in source:
                digest.update(line)
                rows += 1
        assert path.stat().st_size == expected["bytes"]
        assert rows == expected["rows"]
        assert digest.hexdigest() == expected["sha256"]
