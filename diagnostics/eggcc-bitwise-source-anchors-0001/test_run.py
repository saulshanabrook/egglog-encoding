"""Pure source-transformation tests; none invokes main, locks, or native processes."""

from __future__ import annotations

import copy
import hashlib
import importlib
import importlib.util
import json
import sys
from pathlib import Path
from typing import Any

import pytest

ROOT = Path("/Users/saul/p/egglog-encoding")


@pytest.fixture(scope="module")
def inputs() -> tuple[Any, str, dict, Any, Any]:
    """Load only the pinned source/evidence and the pure diagnostic definitions."""
    driver = Path(__file__).with_name("run.py")
    spec = importlib.util.spec_from_file_location("bitwise_anchor_diagnostic", driver)
    assert spec is not None and spec.loader is not None
    diagnostic = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(diagnostic)
    sys.path.insert(0, str(ROOT))
    helpers = importlib.import_module("scripts.eggcc_churchroad_complete")
    parse_forms = importlib.import_module("scripts.hardboiled_replay").egglog_forms
    previous = (
        ROOT / "benchmarks/local/reproduction/diagnostics/eggcc-bitwise-stage-boundary-0001/intent.json"
    ).read_bytes()
    assert hashlib.sha256(previous).hexdigest() == diagnostic.INTENT_SHA256
    receipt = Path(json.loads(previous)["capture"]).read_bytes()
    assert hashlib.sha256(receipt).hexdigest() == diagnostic.CAPTURE_SHA256
    replay = Path(json.loads(receipt)["sessions"][2]["replay"])
    source = replay.read_bytes()
    assert hashlib.sha256(source).hexdigest() == diagnostic.REPLAY_SHA256
    event = (replay.parent / "native-events/event-000006.json").read_bytes()
    assert hashlib.sha256(event).hexdigest() == diagnostic.GRAPH_EVENT_SHA256
    return diagnostic, source.decode(), json.loads(event)["payload"], helpers, parse_forms


def test_pinned_source_has_six_anchors_and_complete_selected_query(inputs: tuple[Any, str, dict, Any, Any]) -> None:
    diagnostic, source, payload, helpers, parse_forms = inputs
    variants, assertions = diagnostic.prepare_variants(source, payload, helpers, parse_forms)
    assert assertions["source_bindings_resolved"] == 345
    assert assertions["anchored_facts"] == 234
    assert assertions["selected_facts_preserved_byte_for_byte"] == 226
    assert assertions["other_checks_preserved_byte_for_byte"] == 5
    assert len(assertions["new_nonconstructor_tables"]) == len(assertions["new_assignments"]) == 6
    assert assertions["input_class"] != assertions["negative_control_class"]
    assert not assertions["admitted"] and not assertions["selected_targets_inserted"]
    assert all(action[0] == "set" and isinstance(action[2], str) for action in assertions["new_assignments"])
    assert sum(t[1] == "check" for _, _, t in parse_forms(variants["anchored.egg"])) == 6
    positive_checks = [t for _, _, t in parse_forms(variants["anchored.egg"]) if t[1] == "check"]
    negative_checks = [t for _, _, t in parse_forms(variants["negative-input.egg"]) if t[1] == "check"]
    assert positive_checks == negative_checks
    assert "(set (reproduction_bitwise_anchor_306) __tmp74)" in variants["negative-input.egg"]


def test_rejects_ambiguous_native_source_lookup(inputs: tuple[Any, str, dict, Any, Any]) -> None:
    diagnostic, source, payload, helpers, parse_forms = inputs
    changed = copy.deepcopy(payload)
    node = copy.deepcopy(changed["graph"]["nodes"]["function-1-InFunc"])
    node["eclass"] = "Assumption-different"
    changed["graph"]["nodes"]["diagnostic-ambiguous-row"] = node
    with pytest.raises(AssertionError, match="native source lookup is absent or ambiguous"):
        diagnostic.prepare_variants(source, changed, helpers, parse_forms)


def test_rejects_incorrect_existing_global_provenance(inputs: tuple[Any, str, dict, Any, Any]) -> None:
    diagnostic, source, payload, helpers, parse_forms = inputs
    changed = copy.deepcopy(payload)
    changed["graph"]["class_data"]["Assumption-48"]["let"] = "ANOTHER_GLOBAL"
    with pytest.raises(AssertionError):
        diagnostic.prepare_variants(source, changed, helpers, parse_forms)


def test_rejects_changed_selected_fact(inputs: tuple[Any, str, dict, Any, Any]) -> None:
    diagnostic, source, payload, helpers, parse_forms = inputs
    forms = parse_forms(source)
    start, end, _ = forms[1000]
    check = source[start:end]
    root = next(t for _, _, t in parse_forms(check[6:-1]) if t[2] == "reproduction_2_s225")
    assert root[4] == "Function" and root[5] != "reproduction_2_s0"
    original = f"reproduction_2_s225 (Function {root[5]}"
    changed = (
        source[:start]
        + check.replace(original, "reproduction_2_s225 (Function reproduction_2_s0", 1)
        + source[end:]
    )
    with pytest.raises(AssertionError):
        diagnostic.prepare_variants(changed, payload, helpers, parse_forms)
