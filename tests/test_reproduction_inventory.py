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
        "hardboiled": 42,
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


def test_published_later_churchroad_cases_keep_the_separate_source_population() -> None:
    root = Path(__file__).resolve().parents[1]
    catalog = json.loads((root / "benchmarks/catalog.json").read_text())
    population = json.loads((root / "benchmarks/reproduction/population.json").read_text())
    catalog["cases"] = [case for case in catalog["cases"] if not case["id"].startswith("churchroad-later-")]
    before = expected_cases(catalog, population)
    later = [case for case in before if case["id"].startswith("churchroad-later-")]
    assert len(later) == 27
    catalog["cases"].extend({**case, "status": "captured", "workloads": ["published.egg"]} for case in later)
    after = expected_cases(catalog, population)
    assert after == before
    assert select_cases(after, FAMILIES, ()) == select_cases(before, FAMILIES, ())
    assert select_cases(after, ("churchroad",), [case["id"] for case in later]) == later
    evaluation = population["churchroad"]["later_evaluation"]
    assert all(
        case["scope"] == "artifact-extra"
        and case["repository"] == evaluation["repository"]
        and case["revision"] == evaluation["revision"]
        and case["configuration"]
        == {
            "repository": evaluation["repository"],
            "revision": evaluation["revision"],
            "top_module_name": Path(case["source"]).stem,
            "architecture": "xilinx-ultrascale-plus",
        }
        for case in later
    )
