"""Prepared manifest identities, aliases, blockers, and strict outcomes stay distinct."""

from __future__ import annotations

import json
from dataclasses import replace
from pathlib import Path

import pytest

from benchmarking import suites
from benchmarking.models import BenchmarkEndpoint

from .corpus_fixtures import prepare_corpus
from .report_fixtures import make_record, make_target


def test_missing_corpus_has_actionable_preparation_command(tmp_path: Path) -> None:
    with pytest.raises(ValueError, match="make reproduce-benchmarks"):
        suites.resolve_suite("expanded", tmp_path)


def test_manifest_preserves_aliases_partial_calls_blockers_and_unknown_producer_metadata(tmp_path: Path) -> None:
    path = prepare_corpus(tmp_path, contents=("(check (= 1 1))\n", "(check (= 2 2))\n"))
    raw = json.loads(path.read_text())
    raw["cases"].extend(
        [
            {
                "id": "alias",
                "family": "luminal",
                "source": "other",
                "status": "ready",
                "workloads": [raw["workloads"][0]["file"]],
                "evidence": "logs/capture.txt",
                "future": True,
            },
            {
                "id": "partial",
                "family": "eggcc",
                "source": "partial",
                "status": "blocked",
                "workloads": [raw["workloads"][1]["file"]],
                "reason": "compiler stopped after complete call",
            },
            {
                "id": "excluded",
                "family": "speq",
                "source": "excluded",
                "status": "excluded",
                "workloads": [],
                "reason": "source incompatible",
            },
        ]
    )
    raw["workloads"][0]["aliases"].append({"case": "alias", "order": 0})
    raw["workloads"][0]["future"] = True
    raw["workloads"][1]["aliases"].append({"case": "partial", "order": 0})
    raw["preparation"] = {"engine": "sha256:engine"}
    path.write_text(json.dumps(raw))
    selected = suites.resolve_suite("expanded", tmp_path)
    assert len(selected.files) == 2
    assert selected.case_files["case-0"] == selected.case_files["alias"]
    assert selected.case_files["partial"] == selected.case_files["case-1"]
    coverage = suites.build_coverage(
        selected,
        report_records=[
            make_record(
                0,
                started_at="2026-01-01",
                file_sha256=selected.files[0].sha256,
                timeout_sec=300,
            )
        ],
    )
    rendered = suites.render_coverage_markdown(coverage)
    assert coverage["expected_cases"] == 5 and coverage["unique_workloads"] == 2
    assert "compiler stopped after complete call" in rendered and "source incompatible" in rendered
    assert "off/nee: 1 success" in rendered


def test_prepared_content_change_is_unavailable_without_replacing_manifest_identity(tmp_path: Path) -> None:
    path = prepare_corpus(tmp_path)
    manifest = suites.load_manifest(tmp_path)
    (path.parent / manifest.workloads[0].file).write_text("changed")
    selected = suites.resolve_suite("eggcc", tmp_path)
    assert not selected.files
    assert "prepared workload identity changed" in selected.capture_errors["case-0"]
    assert suites.load_manifest(tmp_path).workloads == manifest.workloads


@pytest.mark.parametrize(
    "changed",
    ["binary_sha256", "file_sha256", "fact_directory_sha256", "timeout_sec", "disequality_encoding", "policy"],
)
def test_strict_failures_match_every_validation_identity_coordinate(tmp_path: Path, changed: str) -> None:
    path = prepare_corpus(tmp_path)
    selected = suites.resolve_suite("eggcc", tmp_path)
    endpoint = BenchmarkEndpoint(make_target(), "proofs")
    outcome = {
        "file_sha256": selected.files[0].sha256,
        "fact_directory_sha256": "",
        "binary_sha256": endpoint.target.binary_sha256,
        "timeout_sec": 300,
        "disequality_encoding": "nee",
        "kind": "validation",
        "policy": suites.VALIDATION_POLICY,
        "status": "failure",
        "reason": "strict failure",
    }
    local = path.parent / ".local"
    local.mkdir()
    (local / "outcomes.json").write_text(json.dumps([outcome]))
    selected = suites.resolve_suite("eggcc", tmp_path)
    assert suites.suite_outcomes(selected, (endpoint,), 300) == (((selected.files[0], "strict failure"),), ())
    stale = dict(outcome)
    stale[changed] = 120 if changed == "timeout_sec" else "ee" if changed == "disequality_encoding" else "changed"
    selected = replace(selected, manifest=replace(selected.manifest, outcomes=(stale,)))  # type: ignore[arg-type]
    assert suites.suite_outcomes(selected, (endpoint,), 300) == ((), ())


def test_safety_deferral_is_input_bound_and_survives_binary_changes(tmp_path: Path) -> None:
    path = prepare_corpus(tmp_path)
    selected = suites.resolve_suite("expanded", tmp_path)
    outcomes = [
        {
            "file_sha256": selected.files[0].sha256,
            "fact_directory_sha256": "",
            "binary_sha256": "old binary",
            "timeout_sec": 120,
            "disequality_encoding": "nee",
            "kind": "safety",
            "policy": suites.SAFETY_POLICY,
            "status": "deferred",
            "reason": "historical cap",
        }
    ]
    local = path.parent / ".local"
    local.mkdir()
    (local / "outcomes.json").write_text(json.dumps(outcomes))
    selected = suites.resolve_suite("expanded", tmp_path)
    assert suites.suite_outcomes(selected, (BenchmarkEndpoint(make_target(), "proofs"),), 300) == (
        (),
        ((selected.files[0], "historical cap"),),
    )
    outcomes[0]["fact_directory_sha256"] = "different facts"
    (local / "outcomes.json").write_text(json.dumps(outcomes))
    assert suites.suite_outcomes(suites.resolve_suite("expanded", tmp_path), (), 300) == ((), ())


def test_partial_preparation_keeps_pending_population_visible(tmp_path: Path) -> None:
    from benchmarking.figure_inventory import figure_inventory

    path = prepare_corpus(tmp_path)
    raw = json.loads(path.read_text())
    raw["cases"].append(
        {"id": "pending", "family": "eggcc", "source": "author/pending", "status": "pending", "workloads": []}
    )
    path.write_text(json.dumps(raw))
    selected = suites.resolve_suite("expanded", tmp_path)
    assert len(selected.files) == 1
    assert "pending" in suites.render_coverage_markdown(suites.build_coverage(selected))
    inventory = figure_inventory(tmp_path)
    assert inventory["expected_cases"] == 2
    assert inventory["workloads"][1]["id"] == "pending"
    assert inventory["workloads"][1]["unavailable_reason"]
