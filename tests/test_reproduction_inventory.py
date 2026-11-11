"""Paper populations cannot shrink to only the available successful exports."""

import json
from collections import Counter
from pathlib import Path

import pytest

from scripts.reproduction_inventory import FAMILIES, expected_cases, select_cases


def test_paper_configuration_counts_and_runtime_aliases() -> None:
    root = Path(__file__).resolve().parents[1]
    cases = expected_cases(
        json.loads((root / "benchmarks/catalog.json").read_text()),
        json.loads((root / "benchmarks/reproduction/population.json").read_text()),
    )
    selected = select_cases(cases, FAMILIES, ())
    assert Counter(case["family"] for case in selected) == {
        "eggcc": 191,
        "hardboiled": 34,
        "misaal": 93,
        "churchroad": 2,
        "dialegg": 24,
        "speq": 10,
    }
    misaal = [case for case in selected if case["family"] == "misaal"]
    assert sum(len(case["paper_aliases"]) for case in misaal) == 99
    assert len([case for case in cases if case["family"] == "misaal" and case["scope"] == "artifact-extra"]) == 9
    assert len([case for case in selected if case["id"].endswith("--gurobi")]) == 94
    assert len([case for case in selected if case["id"].endswith("--no-hacker")]) == 1
    assert not any(case["family"] in {"math-growth", "luminal"} for case in cases)
    extra = "dialegg-extra-nmm-160"
    assert extra not in {case["id"] for case in selected}
    assert select_cases(cases, ("dialegg",), (extra,))[0]["id"] == extra
    with pytest.raises(ValueError, match="unknown reproduction cases"):
        select_cases(cases, ("speq",), (extra,))
