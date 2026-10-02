"""Explicit real-engine validation: pytest benchmarks/disequality/native/test_original.py.

This gate builds release binaries and runs normal-mode checks outside the
benchmark cache. It is intentionally outside the default tests/ discovery.
"""

import csv
import io
import subprocess
from pathlib import Path

import pytest
from rich.console import Console

from benchmarking import models, targets
from benchmarking.engines import Engine

ROOT = Path(__file__).resolve().parents[3]
CORPUS = ROOT / "benchmarks/disequality/parameter-analysis.in"
NATIVE: dict[Engine, tuple[str, int, int]] = {
    "egg-de": ("de", 1_462_208, 1_362_208),
    "egg-ee": ("ee", 1_499_310, 1_362_209),
    "egg-nee": ("nee-no-saturation", 1_472_210, 1_372_210),
    "egg-oee": ("nee-with-saturation", 1_482_201, 1_362_210),
}


@pytest.fixture(scope="session")
def binaries() -> dict[Engine, Path]:
    row = targets.target_row_for_request(models.TargetRequest(".", ".", None), ROOT, "HEAD")
    return {engine: targets.build_target(row, Console(stderr=True), engine=engine)[0] for engine in NATIVE}


@pytest.fixture(scope="session")
def egglog_binary() -> Path:
    row = targets.target_row_for_request(models.TargetRequest(".", ".", None), ROOT, "HEAD")
    return targets.build_target(row, Console(stderr=True))[0]


@pytest.mark.parametrize("engine", NATIVE)
@pytest.mark.parametrize("case", ("positive", "negative", "full"))
def test_original_native_results(engine: Engine, case: str, binaries: dict[Engine, Path], tmp_path: Path) -> None:
    if case == "full":
        source, equalities, disequalities, expected = CORPUS, 100_000, 10_000, "Y"
    else:
        source = tmp_path / "input.in"
        source.write_text("1\n2\n" if case == "positive" else "1\n1\n")
        equalities, disequalities, expected = 1, 0, "Y" if case == "positive" else "N"
    completed = subprocess.run(
        [str(binaries[engine]), str(source), str(equalities), str(disequalities)],
        check=True,
        capture_output=True,
        text=True,
        timeout=300,
    )
    rows = list(csv.DictReader(io.StringIO(completed.stdout)))
    assert len(rows) == 1, completed.stdout
    row = rows[0]
    method, nodes, classes = NATIVE[engine]
    assert row["method"] == method
    assert int(row["base"]) == equalities
    assert int(row["diseq_num"]) == disequalities
    assert row["contradiction"] == expected
    if case == "full":
        assert int(row["number_nodes"]) == nodes
        assert int(row["number_classes"]) == classes


@pytest.mark.parametrize("encoding", ("nee", "ee"))
def test_full_egglog_contradiction(encoding: str, egglog_binary: Path) -> None:
    subprocess.run(
        [
            str(egglog_binary),
            "--mode",
            "no-messages",
            "-j",
            "1",
            "--disequality-encoding",
            encoding,
            str(CORPUS.with_suffix(".egg")),
        ],
        check=True,
        capture_output=True,
        text=True,
        timeout=300,
    )
