"""Semantic boundaries of the offline, source-versioned SDQL composition."""

from __future__ import annotations

import json
from copy import deepcopy
from typing import Any

import pytest

from benchmarking.pilot_results import pilot_results, pilot_tex
from benchmarking.pilot_slotted_cohort import (
    BASE_BINARY,
    CORRECTED_BINARY,
    POLICY,
    SOURCE_ROLES,
    compose_slotted_source,
    runtime_source_cohorts,
)

from .test_pilot_figures import snapshot_fixture


@pytest.fixture
def packets() -> tuple[dict[str, Any], dict[str, Any], dict[str, Any], dict[str, Any]]:
    base = snapshot_fixture()
    for condition in base["conditions"]:
        condition["binary_sha256"] = BASE_BINARY
        for row in condition["observations"]:
            row["binary_sha256"] = BASE_BINARY
    template = deepcopy(base["conditions"][2])
    base["provenance"].update(binaries={"egglog-experimental": BASE_BINARY}, target={"git_sha": "old-collector"})
    native = deepcopy(template)
    native.update(id="native", treatment="slotted-ref-nested", binary_sha256="sha256:native", validation=None)
    for row in native["observations"]:
        row.update(binary_sha256="sha256:native", treatment="slotted-ref-nested")
    base["conditions"].append(native)
    native_proof = deepcopy(native)
    native_proof.update(id="native-proof", treatment="slotted-ref-nested-proofs")
    for row in native_proof["observations"]:
        row["treatment"] = "slotted-ref-nested-proofs"
    base["conditions"].append(native_proof)
    base["program_size"] = {"old": "restricted compiler counts"}
    base["translation_program_size"] = {"old": "all1016 compiler counts"}
    base["comparisons"] = [c for c in base["comparisons"] if c["experiment"] not in SOURCE_ROLES]
    replacement: dict[str, Any] = {
        **POLICY,
        "requested_threads": 4,
        "pilot_data_version": 1,
        "conditions": [],
        "provenance": {
            "target": {
                "source": "phase2=.",
                "path": "/frozen",
                "git_ref": "HEAD",
                "git_sha": "collector-only-sha",
                "is_dirty": False,
                "label": "claims-eval-slotted-alpha",
            }
        },
    }
    treatments = set(t for roles in SOURCE_ROLES.values() for t in roles.values())
    for index in range(10):
        logical = f"sha256:input{index}"
        identifiers = {}
        for treatment in sorted(treatments):
            old = deepcopy(template)
            old.update(
                id=f"old-{index}-{treatment}",
                logical_id=logical,
                file_sha256=logical,
                treatment=treatment,
                binary_sha256=BASE_BINARY,
                project="",
                validation=None,
            )
            for row in old["observations"]:
                row.update(binary_sha256=BASE_BINARY, file_sha256=logical, treatment=treatment)
            if index == 1 and treatment == "slotted":
                old["exclusion"] = {
                    "kind": "resource",
                    "reason": "retained complete BATAX2 deferral",
                    "evidence": "old receipt",
                }
                old["observations"] = []
            if index == 1 and treatment == "slotted-proof-extraction-no-aliasing":
                old["observations"][0].update(status="failure", error_message="original construction failure")
            base["conditions"].append(old)
            identifiers[treatment] = old["id"]
            new = deepcopy(old)
            new.update(id=f"new-{index}-{treatment}", binary_sha256=CORRECTED_BINARY)
            for row in new["observations"]:
                row.update(
                    status="success",
                    error_message=None,
                    binary_sha256=CORRECTED_BINARY,
                    target_label="claims-eval-slotted-alpha",
                    timeout_sec=500,
                    threads=4,
                    requested_threads=4,
                    memory_limit_bytes=POLICY["memory_limit_bytes"],
                    wall_sec=10.0,
                )
            replacement["conditions"].append(new)
        for experiment, roles in SOURCE_ROLES.items():
            comparison = {
                "scope": "composition" if experiment == "slotted-complete-proofs" else "extensions",
                "experiment": experiment,
                "logical_id": logical,
                "label": f"case{index}",
                "project": "",
                "series": experiment,
                "reference_label": "Slotted native",
                "candidate_label": "Slotted own",
                "baseline": "native-proof" if experiment == "slotted-proofs" else "native",
                "candidate": identifiers[next(iter(roles.values()))],
            }
            comparison.update({role: identifiers[treatment] for role, treatment in roles.items()})
            base["comparisons"].append(comparison)
    policy = {
        **POLICY,
        "binary_sha256": CORRECTED_BINARY,
        "target_label": "claims-eval-slotted-alpha",
        "rust_min_stack": None,
    }
    bindings = {
        "binary_sources": {CORRECTED_BINARY: "corrected-runtime-source"},
        "bindings": {CORRECTED_BINARY: {"compiled_from": "de5+bd09", "method": "runtime-closure equality"}},
    }
    return base, replacement, policy, bindings


def test_only_own_slotted_retargets_and_old_failures_native_other_ast_remain_byte_stable(packets: Any) -> None:
    base, fresh, policy, bindings = packets
    before = json.dumps(base, sort_keys=True)
    result = compose_slotted_source(base, fresh, policy, bindings)
    assert json.dumps(base, sort_keys=True) == before
    assert result["conditions"][: len(base["conditions"])] == base["conditions"]
    assert len(result["conditions"]) == len(base["conditions"]) + 40
    assert result["program_size"] == base["program_size"]
    assert result["translation_program_size"] == base["translation_program_size"]
    assert result["provenance"]["binaries"] == base["provenance"]["binaries"]
    assert result["provenance"]["slotted_source_cohort"]["old_count_oracles_requalified"] is False
    for old, new in zip(base["comparisons"], result["comparisons"], strict=True):
        roles = SOURCE_ROLES.get(old["experiment"], {})
        assert {k: v for k, v in old.items() if k not in roles} == {k: v for k, v in new.items() if k not in roles}
        assert all(new[role].startswith("new-") for role in roles)
    integrated = pilot_results(result, "extensions-runtime")
    assert runtime_source_cohorts(integrated)["corrected-slotted"]["binary_sha256"] == CORRECTED_BINARY


def test_new_failures_and_exclusions_never_fall_back_to_old_successes(packets: Any) -> None:
    base, fresh, policy, bindings = packets
    failed = next(c for c in fresh["conditions"] if c["id"] == "new-0-slotted-proof-extraction-no-aliasing")
    failed["observations"] = failed["observations"][:1]
    failed["observations"][0].update(status="memory-limited", error_message="new resource outcome")
    result = pilot_results(compose_slotted_source(base, fresh, policy, bindings), "applications-proof-runtime")
    row = next(
        c
        for c in result["comparisons"]
        if c["experiment"] == "slotted-proofs" and c["logical_id"] == "sha256:input0" and c["implementation"] == "ours"
    )
    assert row["state"] == "failed" and row["ours"]["binary_sha256"] == CORRECTED_BINARY
    complete = next(
        c
        for c in result["comparisons"]
        if c["experiment"] == "slotted-complete-proofs" and c["logical_id"] == "sha256:input1"
    )
    assert complete["state"] == "excluded"
    assert complete["reference"]["binary_sha256"] == complete["ours"]["binary_sha256"] == CORRECTED_BINARY
    numbers, _ = pilot_tex(result)
    assert "applications-proof-runtime/slotted-proofs/ours/input0/ours/runtime/mean" in numbers
    assert "applications-proof-runtime/slotted-proofs/reference/input0/ours/runtime/mean" in numbers


@pytest.mark.parametrize(
    "mutation", ["binary", "input", "policy", "missing", "duplicate", "exclusion", "borrowed-proof"]
)
def test_mixed_or_incomplete_replacement_contract_is_rejected(packets: Any, mutation: str) -> None:
    base, fresh, policy, bindings = packets
    c = fresh["conditions"][0]
    if mutation == "binary":
        c["observations"][0]["binary_sha256"] = BASE_BINARY
    elif mutation == "input":
        c["file_sha256"] = "sha256:changed"
    elif mutation == "policy":
        policy["rust_min_stack"] = 67108864
    elif mutation == "missing":
        fresh["conditions"].pop()
    elif mutation == "duplicate":
        fresh["conditions"].append(deepcopy(c))
    elif mutation == "exclusion":
        next(c for c in fresh["conditions"] if c["id"] == "new-1-slotted")["exclusion"] = None
    else:
        c["validation"] = {"status": "passed", "observation": {"production_binary_sha256": BASE_BINARY}}
    with pytest.raises(ValueError):
        compose_slotted_source(base, fresh, policy, bindings)


def test_importer_rejects_new_binary_outside_slotted_and_old_binary_inside_it(packets: Any) -> None:
    result = pilot_results(compose_slotted_source(*packets), "extensions-runtime")
    own = next(c for c in result["comparisons"] if c["experiment"] == "slotted")
    own["ours"]["binary_sha256"] = BASE_BINARY
    with pytest.raises(ValueError, match="unexpected candidate binary"):
        runtime_source_cohorts(result)
