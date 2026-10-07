"""Figure metadata projects the manifest without selecting or reading timing rows."""

import json
from dataclasses import replace
from pathlib import Path

from pytest import MonkeyPatch

from benchmarking import known_failures
from benchmarking.figure_inventory import figure_inventory, write_inventory
from benchmarking.suites import SAFETY_POLICY, VALIDATION_POLICY

from .corpus_fixtures import prepare_corpus


def test_metadata_retains_current_hashes_aliases_and_blockers_without_opening_inputs(tmp_path: Path) -> None:
    path = prepare_corpus(tmp_path)
    raw = json.loads(path.read_text())
    raw["cases"].extend(
        [
            {
                "id": "alias",
                "family": "luminal",
                "source": "author",
                "status": "ready",
                "workloads": [raw["workloads"][0]["file"]],
            },
            {
                "id": "blocked",
                "family": "eggcc",
                "source": "author",
                "status": "blocked",
                "workloads": [],
                "reason": "capture incomplete",
            },
            {
                "id": "excluded",
                "family": "speq",
                "source": "author",
                "status": "excluded",
                "workloads": [],
                "reason": "unsupported",
            },
        ]
    )
    raw["workloads"][0]["aliases"].append({"case": "alias", "order": 0})
    path.write_text(json.dumps(raw))
    (path.parent / raw["workloads"][0]["file"]).unlink()
    inventory = figure_inventory(tmp_path)
    assert inventory["expected_cases"] == 4
    assert "min_wall_sec" not in inventory and "max_wall_sec" not in inventory
    assert len(inventory["workloads"]) == 2
    workload = inventory["workloads"][0]
    assert workload["file_sha256"] == raw["workloads"][0]["sha256"]
    assert [alias["case"] for alias in workload["aliases"]] == ["case-0", "alias"]
    assert inventory["workloads"][1]["unavailable_reason"] == "capture incomplete"
    assert inventory["exclusions"][0]["reason"] == "unsupported"
    destination = tmp_path / "inventory.json"
    write_inventory(tmp_path, destination)
    before = destination.stat().st_mtime_ns
    write_inventory(tmp_path, destination)
    assert destination.stat().st_mtime_ns == before


def test_validation_failure_keys_include_timeout_encoding_binary_and_latest_outcome(tmp_path: Path) -> None:
    path = prepare_corpus(tmp_path)
    raw = json.loads(path.read_text())
    outcome = {
        "file_sha256": raw["workloads"][0]["sha256"],
        "fact_directory_sha256": "",
        "binary_sha256": "sha256:binary",
        "timeout_sec": 300,
        "disequality_encoding": "ee",
        "kind": "validation",
        "policy": VALIDATION_POLICY,
        "status": "failure",
        "reason": "strict error",
    }
    raw["outcomes"] = [
        outcome,
        {**outcome, "timeout_sec": 120, "reason": "stale"},
        {**outcome, "policy": "old", "reason": "stale"},
        {**outcome, "disequality_encoding": "nee", "reason": "nee error"},
        {**outcome, "disequality_encoding": "nee", "status": "success", "reason": None},
        {**outcome, "kind": "safety", "policy": SAFETY_POLICY, "status": "deferred", "reason": "historical cap"},
    ]
    path.write_text(json.dumps(raw))
    workload = figure_inventory(tmp_path)["workloads"][0]
    assert workload["validation_failures"] == {"sha256:binary/300/ee": "strict error"}
    assert workload["unavailable_reason"] == "historical cap"


def test_known_failures_project_only_affected_modes_without_reading_inputs(
    tmp_path: Path, monkeypatch: MonkeyPatch
) -> None:
    path = prepare_corpus(tmp_path)
    raw = json.loads(path.read_text())
    source = raw["workloads"][0]
    failure = replace(known_failures.KNOWN_FAILURES[0], file_sha256=source["sha256"])
    monkeypatch.setattr(known_failures, "KNOWN_FAILURES", (failure,))
    (path.parent / source["file"]).unlink()

    workload = figure_inventory(tmp_path)["workloads"][0]

    assert list(workload["known_failures"]) == ["proofs/nee"]
    assert failure.reason in workload["known_failures"]["proofs/nee"]
    assert workload["unavailable_reason"] == ""
    assert workload["validation_failures"] == {}


def test_source_level_exclusion_remains_visible_without_inventing_cases(tmp_path: Path) -> None:
    from benchmarking import suites

    path = prepare_corpus(tmp_path)
    raw = json.loads(path.read_text())
    raw["sources"]["speq"] = {"excluded": "reference-oriented compiler inputs are outside this comparison"}
    path.write_text(json.dumps(raw))
    inventory = figure_inventory(tmp_path)
    assert inventory["expected_cases"] == 1
    assert inventory["exclusions"] == [
        {"case": "speq", "family": "speq", "paths": [], "reason": raw["sources"]["speq"]["excluded"]}
    ]
    expanded = suites.build_coverage(suites.resolve_suite("expanded", tmp_path))
    assert expanded["expected_cases"] == 1
    assert "Excluded speq: reference-oriented" in suites.render_coverage_markdown(expanded)
    narrow = suites.build_coverage(suites.resolve_suite("eggcc", tmp_path))
    assert narrow["exclusions"] == []
