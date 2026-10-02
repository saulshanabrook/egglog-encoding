"""Verify observer-only replay edits and preservation of capture provenance."""

from __future__ import annotations

import copy
import json
from pathlib import Path

import pytest

from benchmarking.targets import sha256_file
from scripts.eggcc_observer_compat import adapt_observers
from scripts.hardboiled_replay import egglog_forms

SOURCE = """; Preserve original comments, source declarations, schedule, and query.
(datatype BaseType (IntT))
(datatype Expr (Wrap BaseType))
(function source_table () Expr :no-merge)
(let original (Wrap (IntT)))
(ruleset original_schedule)
(run original_schedule 1)
(function reproduction_lookup_value_0 (i64 i64) BaseType :no-merge)
(function reproduction_lookup_value_1 (i64 i64) Expr :no-merge)
(ruleset reproduction_lookup_depth_0)
(ruleset reproduction_lookup_depth_1)
(rule ((= n (IntT))) ((set (reproduction_lookup_value_0 0 0) n))
 :ruleset reproduction_lookup_depth_0 :internal-include-subsumed :name "reproduction_lookup_rule_0_0")
(rule ((= n (reproduction_lookup_value_0 0 0)) (= e (Wrap n))) ((set (reproduction_lookup_value_1 0 1) e))
 :ruleset reproduction_lookup_depth_1 :internal-include-subsumed :name "reproduction_lookup_rule_0_1")
(run reproduction_lookup_depth_0 1)
(run reproduction_lookup_depth_1 1)
(check (= original (reproduction_lookup_value_1 0 1)))
"""


def test_changes_only_generated_declarations_and_is_idempotent() -> None:
    adapted, changes = adapt_observers(SOURCE)
    assert len(changes) == 2
    expected = SOURCE
    for change in changes:
        assert change["before"].startswith("(function reproduction_lookup_value_")
        expected = expected.replace(change["before"], change["after"], 1)
    assert adapted == expected
    assert "(function source_table () Expr :no-merge)" in adapted
    assert adapt_observers(adapted) == (adapted, [])
    changed_commands = {change["command"] for change in changes}
    before = egglog_forms(SOURCE)
    after = egglog_forms(adapted)
    assert all(
        left[2] == right[2]
        for i, (left, right) in enumerate(zip(before, after, strict=True))
        if i not in changed_commands
    )


def test_reconstruction_and_derived_type_observers() -> None:
    source = SOURCE.replace("reproduction_lookup_", "reconstruction_lookup_")
    assert len(adapt_observers(source)[1]) == 2
    source = """(datatype TypeList (Nil))
(datatype Type (TupleT TypeList))
(function reproduction_anchor_0 () TypeList :merge old)
(function reproduction_derived_type_0 () Type :no-merge)
(ruleset reproduction_derived_types)
(rule ((= child (reproduction_anchor_0)) (= result (TupleT child))) ((set (reproduction_derived_type_0) result))
 :ruleset reproduction_derived_types :internal-include-subsumed)
(run reproduction_derived_types 1)
(check (reproduction_derived_type_0))
"""
    adapted, changes = adapt_observers(source)
    assert len(changes) == 1
    assert "(function reproduction_derived_type_0 () Type :merge old)" in adapted


def test_literal_arguments_and_constructor_initialized_global_remain_grounded() -> None:
    source = SOURCE.replace(
        "(datatype BaseType (IntT))", "(datatype BaseType (IntT) (Named String))\n(let ROOT (IntT))"
    )
    source = source.replace("((= n (IntT)))", '((= n (Named "name")))')
    source = source.replace("(= n (reproduction_lookup_value_0 0 0))", "(= n ROOT)")
    assert len(adapt_observers(source)[1]) == 2


@pytest.mark.parametrize(
    "before,after",
    [
        ("(i64 i64) BaseType", "(String i64) BaseType"),
        ("BaseType :no-merge)", "BaseType :merge new)"),
        ("((= n (IntT)))", "((= n (unknown-operation)))"),
        ("(Wrap n)))", "(Wrap unbound)))"),
        ("(Wrap n)))", "(Wrap 0)))"),
        ("((set (reproduction_lookup_value_0 0 0) n))", "((union n (IntT)))"),
        ("(set (reproduction_lookup_value_0 0 0) n)", "(set (reproduction_lookup_value_0 request 0) n)"),
        ("(reproduction_lookup_value_0 0 0)) (= e", "(reproduction_lookup_value_0 0 99)) (= e"),
        ("((= n (IntT)))", "((= n (reproduction_lookup_value_0 0 0)))"),
        ('"reproduction_lookup_rule_0_0"', '"another_rule"'),
    ],
)
def test_rejects_changed_generated_shapes(before: str, after: str) -> None:
    assert before in SOURCE
    with pytest.raises(ValueError):
        adapt_observers(SOURCE.replace(before, after, 1))


def test_rejects_multiple_writers_and_mutating_observer_uses() -> None:
    rule = next(SOURCE[start:end] for start, end, tokens in egglog_forms(SOURCE) if tokens[1] == "rule")
    with pytest.raises(ValueError, match="more than one writer"):
        adapt_observers(SOURCE + rule)
    with pytest.raises(ValueError, match="outside a generated rule"):
        adapt_observers(SOURCE + "(set (reproduction_lookup_value_0 0 0) (IntT))")


@pytest.fixture
def publication(tmp_path: Path) -> tuple[Path, dict, Path]:
    corpus = tmp_path / "original"
    corpus.mkdir()
    path = corpus / "input.egg"
    path.write_text(SOURCE)
    identity = {"file_sha256": sha256_file(path), "facts_sha256": ""}
    aliases = [
        {"case": f"eggcc-{name}--statewalk", "order": 0, "captured_replay": "raw/source.egg"} for name in ("a", "b")
    ]
    receipt = corpus / "manifest.json"
    receipt.write_text(
        json.dumps(
            {
                "cases": [
                    {"id": f"eggcc-{name}--statewalk", "catalog_id": f"eggcc-{name}", "workloads": [path.name]}
                    for name in ("a", "b")
                ],
                "workloads": [
                    {"file": path.name, "sha256": identity["file_sha256"], "facts_sha256": "", "aliases": aliases}
                ],
            }
        )
    )
    relative = str(path.relative_to(tmp_path))
    case = {
        "family": "eggcc",
        "workloads": ["older/history.egg", relative],
        "benchmark_selection": {"workloads": [relative], "reason": "original"},
        "complete_reproduction": {
            "status": "complete",
            "scope": "standalone-workload",
            "reason": "original",
            "receipt": str(receipt.relative_to(tmp_path)),
            "receipt_sha256": sha256_file(receipt),
            "workloads": {relative: identity},
        },
    }
    return (
        tmp_path,
        {"families": [], "cases": [{**copy.deepcopy(case), "id": f"eggcc-{name}"} for name in ("a", "b")]},
        receipt,
    )
