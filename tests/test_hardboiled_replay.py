"""HardBoiled query preparation must not hide active work or accept false gates."""

import pytest

from scripts.hardboiled_replay import (
    check_observed_selections,
    egglog_forms,
    freeze_extraction_query,
    omit_unexecuted_higher_order_rules,
    omit_unexecuted_keep_best,
    require_query_controls,
)

SOURCE = """(datatype E (Seed) (Optimized String))
(let $first (Seed))
(let $second (Seed))
(ruleset keep-best)
(rule () ((keep-best "root")) :ruleset keep-best)
(run-schedule (repeat 20 (saturate (run typechecking)) (run) (run amx)))
(extract $first)
(extract $second)
"""


def test_dead_rule_guard_preserves_original_schedule_seeds_and_extraction_order() -> None:
    adapted = omit_unexecuted_keep_best(SOURCE)
    original_forms = [SOURCE[start:end] for start, end, tokens in egglog_forms(SOURCE) if tokens[1] != "rule"]
    adapted_forms = [adapted[start:end] for start, end, _ in egglog_forms(adapted)]
    assert adapted_forms == original_forms
    assert "(ruleset keep-best)" in adapted


@pytest.mark.parametrize(
    "change",
    (
        "(run keep-best)",
        "(run-schedule (run keep-best))",
        "(unstable-combined-ruleset merged keep-best)",
        '(include "external.egg")',
        '(rule () ((keep-best "other")))',
    ),
)
def test_dead_rule_guard_rejects_scheduled_or_other_references(change: str) -> None:
    with pytest.raises(ValueError, match="keep-best"):
        omit_unexecuted_keep_best(SOURCE + change)


def test_freezes_one_ordered_closed_output_without_inserting_it() -> None:
    source = omit_unexecuted_keep_best(SOURCE)
    output = '; real output containing delimiters in a literal\n(Optimized "(;\\"quoted\\")")\n(Seed)\n'
    replay, negative, query = freeze_extraction_query(source, output)
    assert query == '(check (= $first (Optimized "(;\\"quoted\\")")))'
    assert replay.count(query) == negative.count(query) == 1
    assert "(let $first (Seed))" in replay
    assert "(let $second (Seed))" in replay
    assert "(extract " not in replay
    assert "(run-schedule " in replay
    assert "(run-schedule " not in negative
    assert "(union " not in replay
    assert 'Optimized "' not in replay[: replay.index(query)]
    assert freeze_extraction_query(source, output, 1)[2] == "(check (= $second (Seed)))"


def test_actual_sidecar_checks_cover_all_roots_in_original_scope_without_seeding() -> None:
    source = "(push 1)\n(let $a (Seed))\n(extract $a)\n(pop 1)\n(let $b (Seed))\n(extract $b)\n"
    replay, selections = check_observed_selections(source, '(Optimized "actual")\n(Seed)\n')
    assert [item["root"] for item in selections] == ["$a", "$b"]
    assert selections[1]["check"] == "(check (= $b (Seed)))"  # An unchanged native result is legitimate.
    assert replay.index(selections[0]["check"]) < replay.index("(pop 1)")
    assert replay.count("(extract ") == 2
    assert [tokens for _, _, tokens in egglog_forms(replay) if tokens[1] != "check"] == [
        tokens for _, _, tokens in egglog_forms(source)
    ]
    assert replay.count('(Optimized "actual")') == 1
    assert "(union " not in replay


@pytest.mark.parametrize(
    "selected", ["(Seed)", "(Seed)\n(Seed)\n(Seed)", "(let $x (Seed))\n(Seed)", "(E $missing)\n(Seed)"]
)
def test_actual_sidecar_contract_rejects_missing_extra_or_unbound_results(selected: str) -> None:
    with pytest.raises(ValueError):
        check_observed_selections(SOURCE, selected)


@pytest.mark.parametrize(
    "output",
    (
        '(Optimized "unfinished)\n(Seed)',
        '(Optimized "x")\n',
        "unparsed diagnostic\n(Seed)\n(Seed)",
        "(let $v (Seed))\n(Seed)",
        "(Optimized $unbound)\n(Seed)",
    ),
)
def test_rejects_truncated_diagnostic_or_open_extraction_output(output: str) -> None:
    with pytest.raises(ValueError):
        freeze_extraction_query(omit_unexecuted_keep_best(SOURCE), output)


@pytest.mark.parametrize(
    ("negative", "diagnostic"),
    (
        ({"status": "success", "returncode": 0}, ""),
        ({"status": "failure", "returncode": 1}, "Parse failed:"),
        ({"status": "failure", "returncode": 101}, "Check failed:"),
        ({"status": "memory-limit", "returncode": -9}, "Check failed:"),
        ({"status": "failure", "returncode": 1, "halt": True}, "Check failed:"),
    ),
)
def test_false_negative_controls_never_admit_a_query(negative: dict, diagnostic: str) -> None:
    with pytest.raises(ValueError, match="unestablished-query"):
        require_query_controls({"status": "success", "returncode": 0}, negative, diagnostic)


def test_genuine_unestablished_query_control_passes() -> None:
    require_query_controls(
        {"status": "success", "returncode": 0},
        {"status": "failure", "returncode": 1},
        'At test.egg\n    Check failed:\n    (= $first (Optimized "x"))',
    )


HIGHER_ORDER_SOURCE = (
    SOURCE
    + """
(sort Callback (UnstableFn (E) E))
(relation callback (Callback))
(rule ((= e (Seed))) ((callback (unstable-fn "Optimized"))) :ruleset canonicalize)
(rule ((callback f) (= e (Seed))) ((union e (unstable-app f e))) :ruleset canonicalize)
"""
)


def test_higher_order_omission_preserves_every_other_form() -> None:
    adapted = omit_unexecuted_higher_order_rules(HIGHER_ORDER_SOURCE)
    expected = [
        tokens
        for _, _, tokens in egglog_forms(HIGHER_ORDER_SOURCE)
        if not {"unstable-app", "unstable-fn"}.intersection(tokens)
    ]
    assert [tokens for _, _, tokens in egglog_forms(adapted)] == expected
    assert "(sort Callback (UnstableFn (E) E))" in adapted
    assert omit_unexecuted_higher_order_rules(SOURCE) == SOURCE
    assert omit_unexecuted_higher_order_rules(adapted) == adapted


@pytest.mark.parametrize(
    "change",
    (
        "(run canonicalize)",
        "(run-schedule (run canonicalize))",
        "(unstable-combined-ruleset merged canonicalize)",
        '(include "external.egg")',
        "(push)",
        "(pop)",
        '(let f (unstable-fn "Optimized"))',
        '(rule () ((callback (unstable-fn "Optimized"))))',
        '(rule () ((callback (unstable-fn "Optimized"))) :ruleset amx)',
    ),
)
def test_higher_order_omission_rejects_active_or_external_uses(change: str) -> None:
    with pytest.raises(ValueError, match="higher-order"):
        omit_unexecuted_higher_order_rules(HIGHER_ORDER_SOURCE + change)
