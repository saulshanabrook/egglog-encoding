"""Check mechanical compatibility edits for captured Churchroad invocations."""

import pytest

from scripts.suite_capture_eggcc_churchroad import rename_churchroad_globals


def test_churchroad_globals_get_fresh_base_names_without_changing_circuit_literals() -> None:
    source = (
        '; a v0 "quoted comment"\n'
        '(let v0 (Wire "v0" 16))\n'
        '(let a (Var "a" 16))\n'
        "(union v0 a)\n"
        '(IsPort "escaped \\"a\\"" "a" (Input) v0)\n'
        "(run-schedule (saturate (seq typing misc)))\n"
    )
    query = "(check (= v0 (PrimitiveInterfaceDSP a v0)))"
    rules = "(rule ((= expr (Op2 (Mul) a b))) ((union expr (PrimitiveInterfaceDSP a b))) :ruleset mapping)"

    adapted, adapted_query, aliases = rename_churchroad_globals(source, query, rules)

    assert aliases == {"v0": "$churchroad-global-v0", "a": "$churchroad-global-a"}
    assert adapted == (
        '; a v0 "quoted comment"\n'
        '(let $churchroad-global-v0 (Wire "v0" 16))\n'
        '(let $churchroad-global-a (Var "a" 16))\n'
        "(union $churchroad-global-v0 $churchroad-global-a)\n"
        '(IsPort "escaped \\"a\\"" "a" (Input) $churchroad-global-v0)\n'
        "(run-schedule (saturate (seq typing misc)))\n"
    )
    assert adapted_query == (
        "(check (= $churchroad-global-v0 (PrimitiveInterfaceDSP $churchroad-global-a $churchroad-global-v0)))"
    )


def test_churchroad_aliases_reject_an_existing_rule_variable_base_name() -> None:
    with pytest.raises(ValueError, match="global alias prefix collides"):
        rename_churchroad_globals(
            '(let a (Var "a" 16))', "(check (= a a))", "(rule ((HasType churchroad-global-a t)) ((Known t)))"
        )
