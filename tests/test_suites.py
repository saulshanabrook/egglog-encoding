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


@pytest.mark.parametrize("prior_cap", [False, True])
@pytest.mark.parametrize(
    "active_reason",
    [
        "native memory limit: allocation failed under limit",
        "native memory limit: setrlimit failed",
        "resource guard halted collection after unexpected SIGKILL (cause unknown)",
        "memory monitoring failed: ps timeout; native memory limit: allocation failed under limit",
    ],
)
def test_retired_polling_stops_do_not_hide_inputs_or_clear_native_failures(
    tmp_path: Path, prior_cap: bool, active_reason: str
) -> None:
    from benchmarking.figure_inventory import figure_inventory

    path = prepare_corpus(tmp_path)
    selection = suites.resolve_suite("expanded", tmp_path)
    record = {
        "file_sha256": selection.files[0].sha256,
        "fact_directory_sha256": "",
        "binary_sha256": "old binary",
        "timeout_sec": 300,
        "disequality_encoding": "nee",
        "kind": "safety",
        "policy": suites.SAFETY_POLICY,
        "status": "deferred",
        "reason": active_reason,
    }
    outcomes = [record] if prior_cap else []
    outcomes += [
        {**record, "reason": "host memory pressure is not normal (kernel level 2)"},
        {**record, "reason": "resource guard refused to launch a workload: host memory headroom below reserve"},
        {**record, "reason": "disk guard refused to launch: fewer than 2147483648 bytes free"},
        {**record, "reason": "free disk fell below the 2147483648-byte reserve"},
        {**record, "reason": "disk monitoring failed: cannot read filesystem statistics"},
        {**record, "reason": "workload process-group RSS exceeded its safety cap"},
        {**record, "reason": "process-group RSS exceeded 10737418240 bytes"},
        {**record, "reason": "memory monitoring failed: ps timeout"},
    ]
    local = path.parent / ".local"
    local.mkdir()
    evidence = json.dumps(outcomes)
    (local / "outcomes.json").write_text(evidence)
    selection = suites.resolve_suite("expanded", tmp_path)
    expected = ((selection.files[0], record["reason"]),) if prior_cap else ()
    assert suites.suite_outcomes(selection, (), 300) == ((), expected)
    assert figure_inventory(tmp_path)["workloads"][0]["unavailable_reason"] == (record["reason"] if prior_cap else "")
    assert (local / "outcomes.json").read_text() == evidence
    mixed_reason = "free disk fell below the 2147483648-byte reserve; descendant cleanup failed: still running"
    outcomes.append({**record, "reason": mixed_reason})
    (local / "outcomes.json").write_text(json.dumps(outcomes))
    selection = suites.resolve_suite("expanded", tmp_path)
    assert suites.suite_outcomes(selection, (), 300) == ((), ((selection.files[0], mixed_reason),))


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


@pytest.mark.parametrize(
    "changed",
    [None, "binary_sha256", "file_sha256", "fact_directory_sha256", "timeout_sec", "disequality_encoding", "policy"],
)
def test_preparation_memory_exclusion_matches_execution_identity(tmp_path: Path, changed: str | None) -> None:
    from process_guard import NATIVE_ALLOCATION_FAILURE, NATIVE_LIMIT_BYTES

    prepare_corpus(tmp_path)
    selection = suites.resolve_suite("eggcc", tmp_path)
    endpoint = BenchmarkEndpoint(make_target(), "proofs")
    outcome: suites.CorpusOutcome = {
        "file_sha256": selection.files[0].sha256,
        "fact_directory_sha256": "",
        "binary_sha256": endpoint.target.binary_sha256,
        "timeout_sec": 300,
        "disequality_encoding": "nee",
        "kind": "safety",
        "policy": f"native-memory-limit-v1:{NATIVE_LIMIT_BYTES}",
        "status": "deferred",
        "reason": NATIVE_ALLOCATION_FAILURE,
    }
    stale = dict(outcome)
    if changed:
        stale[changed] = 120 if changed == "timeout_sec" else "ee" if changed == "disequality_encoding" else "changed"
    selection = replace(selection, manifest=replace(selection.manifest, outcomes=(stale,)))  # type: ignore[arg-type]
    from benchmarking.reports.store import CacheKey

    assert suites.native_memory_exclusions(selection, (endpoint,), 300) == (
        {} if changed else {CacheKey.for_endpoint(endpoint, selection.files[0], 300): NATIVE_ALLOCATION_FAILURE}
    )
    if not changed:
        cleared: suites.CorpusOutcome = {**outcome, "status": "success", "reason": None}
        selection = replace(selection, manifest=replace(selection.manifest, outcomes=(outcome, cleared)))
        assert suites.native_memory_exclusions(selection, (endpoint,), 300) == {}


@pytest.mark.parametrize("cleanup_failure", [False, True])
def test_legacy_native_exhaustion_is_not_a_global_exclusion(tmp_path: Path, cleanup_failure: bool) -> None:
    from process_guard import NATIVE_ALLOCATION_FAILURE

    prepare_corpus(tmp_path)
    selection = suites.resolve_suite("eggcc", tmp_path)
    reason = NATIVE_ALLOCATION_FAILURE + ("; descendant cleanup failed" if cleanup_failure else "")
    outcome: suites.CorpusOutcome = {
        "file_sha256": selection.files[0].sha256,
        "fact_directory_sha256": "",
        "binary_sha256": "old binary",
        "timeout_sec": 300,
        "disequality_encoding": "nee",
        "kind": "safety",
        "policy": suites.SAFETY_POLICY,
        "status": "deferred",
        "reason": reason,
    }
    selection = replace(selection, manifest=replace(selection.manifest, outcomes=(outcome,)))
    assert suites.suite_outcomes(selection, (BenchmarkEndpoint(make_target(), "proofs"),), 300) == (
        (),
        ((selection.files[0], reason),) if cleanup_failure else (),
    )


@pytest.mark.parametrize("different", ["binary", "encoding"])
def test_memory_exclusion_skips_only_affected_comparison_endpoint(tmp_path: Path, different: str) -> None:
    from benchmarking import benchmark, collection, models
    from benchmarking.reports.store import ReportStore
    from process_guard import NATIVE_ALLOCATION_FAILURE, NATIVE_LIMIT_BYTES

    prepare_corpus(tmp_path)
    selection = suites.resolve_suite("eggcc", tmp_path)
    target = make_target(target_label="limited")
    baseline = BenchmarkEndpoint(target, "proofs")
    candidate = BenchmarkEndpoint(
        make_target(target_label="fresh", binary_sha256="sha256:new") if different == "binary" else target,
        "proofs",
        "ee" if different == "encoding" else "nee",
    )
    outcome: suites.CorpusOutcome = {
        "file_sha256": selection.files[0].sha256,
        "fact_directory_sha256": "",
        "binary_sha256": target.binary_sha256,
        "timeout_sec": 300,
        "disequality_encoding": "nee",
        "kind": "safety",
        "policy": f"native-memory-limit-v1:{NATIVE_LIMIT_BYTES}",
        "status": "deferred",
        "reason": NATIVE_ALLOCATION_FAILURE,
    }
    selection = replace(selection, manifest=replace(selection.manifest, outcomes=(outcome,)))
    exclusions = suites.native_memory_exclusions(selection, (baseline, candidate), 300)
    assert len(exclusions) == 1
    comparison = models.ComparisonSpec(baseline, candidate, selection.files, 3, 300, suite_mode=True)
    store = ReportStore(tmp_path / "temporary.jsonl")
    plans = benchmark.collection_plans(store, comparison, False, native_exclusions=exclusions)
    runs = [run for plan in plans for run in plan.runs]
    assert [run.missing_observations for run in runs] == [0, 3]
    assert [run.skip_reason for run in runs] == [NATIVE_ALLOCATION_FAILURE, None]
    for endpoint, complete in ((baseline, True), (candidate, False)):
        request = models.EndpointRequest(endpoint.target.request, endpoint.treatment, endpoint.disequality_encoding)
        assert (
            collection.label_has_enough_rows(
                store, endpoint.target, (request,), selection.files, 3, 300, True, native_exclusions=exclusions
            )
            is complete
        )
    assert not store.records  # Preparation exclusions do not fabricate benchmark measurements.
