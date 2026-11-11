"""Check mechanical compatibility edits for captured Churchroad invocations."""

import copy
import hashlib
import json
import re
from pathlib import Path
from typing import Any

import pytest

from benchmarking.pilot import PilotProcessResult
from scripts import eggcc_churchroad_complete as complete
from scripts import suite_capture_eggcc_churchroad as capture
from scripts.eggcc_churchroad_complete import (
    CaptureError,
    WitnessQuery,
    churchroad_selection_check,
    churchroad_sessions,
    eggcc_dag_lookups,
    eggcc_output_checks,
    eggcc_seed_query,
    eggcc_sessions,
    eggcc_source_anchors,
    read_events,
    tiger_selections,
)
from scripts.hardboiled_replay import egglog_forms
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


@pytest.mark.parametrize("separate_parts", [False, True])
def test_churchroad_globals_apply_only_after_binding_and_persist_across_parts(separate_parts: bool) -> None:
    prelude = "(rule ((Pair a b)) ((Seen a b)) :ruleset mapping)\n"
    bindings = '(let a (Var "a" 16))\n(let b (Var "b" 32))\n'
    mapping = (
        "; a b ?a ?b stay spelled this way in comments\n"
        '(rule ((Pair a b) (Pair ?a ?b) (Label "a b"))\n'
        "      ((Seen a b) (Seen ?a ?b)) :ruleset mapping)\n"
        "(run-schedule (saturate (seq typing transform mapping)))\n"
    )
    source = prelude + bindings + mapping
    parts = [prelude, bindings, mapping] if separate_parts else [source]
    aliases: dict[str, str] = {}
    result = ""
    for part in parts:
        adapted, _, aliases = rename_churchroad_globals(part, "", source, aliases=aliases)
        result += adapted
    assert result == (
        prelude
        + '(let $churchroad-global-a (Var "a" 16))\n(let $churchroad-global-b (Var "b" 32))\n'
        + "; a b ?a ?b stay spelled this way in comments\n"
        + '(rule ((Pair $churchroad-global-a $churchroad-global-b) (Pair ?a ?b) (Label "a b"))\n'
        + "      ((Seen $churchroad-global-a $churchroad-global-b) (Seen ?a ?b)) :ruleset mapping)\n"
        + "(run-schedule (saturate (seq typing transform mapping)))\n"
    )


def test_churchroad_global_translation_distinguishes_expression_variables_from_names() -> None:
    source = "(let + 3)\n(let mapping 7)\n(ruleset mapping)\n"
    rules = "(rule ((= n (+ mapping +))) ((Found mapping n)) :ruleset mapping)\n"
    adapted, query, _ = rename_churchroad_globals(source + rules, "(check (= (+ mapping +) 10))", source + rules)
    assert adapted == (
        "(let $churchroad-global-+ 3)\n(let $churchroad-global-mapping 7)\n(ruleset mapping)\n"
        "(rule ((= n (+ $churchroad-global-mapping $churchroad-global-+))) "
        "((Found $churchroad-global-mapping n)) :ruleset mapping)\n"
    )
    assert query == "(check (= (+ $churchroad-global-mapping $churchroad-global-+) 10))"


@pytest.mark.parametrize(
    "later",
    [
        "(push)",
        "(pop)",
        '(include "other.egg")',
        "(let a (A))",
        "(rule ((A)) ((let local a)))",
        "(run mapping 1 :until (= a (A)))",
        "(function f () Expr :merge a)",
    ],
)
def test_churchroad_unreviewed_scoping_fails_closed(later: str) -> None:
    source = "(let a (A))\n" + later
    with pytest.raises(CaptureError, match="reviewed"):
        rename_churchroad_globals(source, "", source)


@pytest.fixture
def native_eggcc() -> tuple[dict, str, str, list[dict]]:
    """A native choice of Const(2) equivalent to the seeded Const(1).

    The graph is synthetic protocol input, not a claimed compiler execution.
    The distinct source/result bodies catch accidentally checking existence only.
    """
    nodes = {
        "primitive-name": {"op": '"main"', "children": [], "eclass": "String-main"},
        "primitive-one": {"op": "1", "children": [], "eclass": "i64-1"},
        "primitive-two": {"op": "2", "children": [], "eclass": "i64-2"},
        "primitive-ctx": {"op": '"main-context"', "children": [], "eclass": "String-context"},
        "type": {"op": "IntT", "children": [], "eclass": "BaseType-1"},
        "base": {"op": "Base", "children": ["type"], "eclass": "Type-1"},
        "ctx": {"op": "InFunc", "children": ["primitive-ctx"], "eclass": "Assumption-1"},
        "int1": {"op": "Int", "children": ["primitive-one"], "eclass": "Constant-1"},
        "int2": {"op": "Int", "children": ["primitive-two"], "eclass": "Constant-2"},
        "const1": {"op": "Const", "children": ["int1", "base", "ctx"], "eclass": "Expr-body"},
        "const2": {"op": "Const", "children": ["int2", "base", "ctx"], "eclass": "Expr-body"},
        "input": {"op": "Function", "children": ["primitive-name", "base", "base", "const1"], "eclass": "Expr-root"},
        "output": {"op": "Function", "children": ["primitive-name", "base", "base", "const2"], "eclass": "Expr-root"},
    }
    selection = [
        ("primitive-name", []),
        ("type", []),
        ("base", [1]),
        ("primitive-two", []),
        ("int2", [3]),
        ("const2", [4]),
        ("output", [0, 2, 2, 5]),
    ]
    trace = "\n".join(
        [
            "; reproduction-selection-begin",
            *(
                f"; reproduction-node {node.encode().hex()}" + "".join(f" {c}" for c in children)
                for node, children in selection
            ),
            "; reproduction-selection-end",
        ]
    )
    # Tiger requests one extraction per Function row. The input/output rows are
    # two aliases of one class, so the native protocol retains two selections.
    trace += "\n" + trace
    seed = "\n".join(
        [
            "(let ty (Base (IntT)))",
            '(let ctx (InFunc "main-context"))',
            "(let one (Int 1))",
            "(let body (Const one ty ctx))",
            '(let fun (Function "main" ty ty body))',
            '(FunctionHasType "main" (Base (IntT)) (Base (IntT)))',
        ]
    )
    program = "; Program nodes\n" + seed + "\n; Loop context unions\n"
    output = "\n".join(
        [
            "(let ty (Base (IntT)))",
            "(let ctx (DumC))",
            "(let two (Int 2))",
            "(let body (Const two ty ctx))",
            '(let fun (Function "main" ty ty body))',
            "(let PROG fun)",
        ]
    )
    graph = {"nodes": nodes}
    payloads = [
        ("optimization-start", {"pass": 0, "expected_passes": 1, "cutoff": 1, "batch": ["main"], "program": program}),
        ("tiger-result", {"batch": ["main"], "program": trace, "graph": graph}),
        ("reconstruction-outputs", {"batch": ["main"], "outputs": [{"name": "main", "program": output}]}),
        ("reconstruction-complete", {"batch": ["main"]}),
        ("optimization-complete", {"pass": 0, "batch": ["main"], "typechecked": True}),
        ("parent-complete", {"outputs": [{"result": "actual compiler output"}]}),
    ]
    events = [
        {"version": 1, "sequence": i, "kind": kind, "payload": payload} for i, (kind, payload) in enumerate(payloads)
    ]
    return graph, trace, seed, events


def test_eggcc_checks_exact_seed_against_observed_selection_without_actions(native_eggcc: tuple) -> None:
    graph, trace, seed, _ = native_eggcc
    checks, roots = eggcc_output_checks(graph, trace, ["main"], seed)
    assert roots[0]["node"] == "output"
    assert "(= reproduction_0_seed4 reproduction_0_s6)" in checks
    assert "(Int 1)" in checks
    assert "(= reproduction_0_s3 2)" in checks
    assert "(let " not in checks and "(union " not in checks
    assert "DumC" not in checks and "DumT" not in checks


def test_eggcc_preserves_all_alias_root_requests_and_exact_choices(native_eggcc: tuple) -> None:
    graph, trace, seed, _ = native_eggcc
    # Equivalent root requests may choose different original terms. Retain and
    # check both, rather than deduplicating by name, class, or selected root.
    first, second = trace.split("; reproduction-selection-end", 1)
    second = second.replace(b"output".hex(), b"input".hex())
    second = second.replace(b"const2".hex(), b"const1".hex())
    second = second.replace(b"int2".hex(), b"int1".hex())
    second = second.replace(b"primitive-two".hex(), b"primitive-one".hex())
    checks, roots = eggcc_output_checks(graph, first + "; reproduction-selection-end" + second, ["main"], seed)
    assert [(root["selection"], root["name"], root["node"]) for root in roots] == [
        (0, "main", "output"),
        (1, "main", "input"),
    ]
    assert checks.count("(check\n") == 2
    assert "(= reproduction_0_seed4 reproduction_0_s6)" in checks
    assert "(= reproduction_1_seed4 reproduction_1_s6)" in checks
    assert "(= reproduction_0_s3 2)" in checks
    assert "(= reproduction_1_s3 1)" in checks
    assert "(let " not in checks and "(union " not in checks


def test_eggcc_rejects_missing_or_surplus_alias_root_requests(native_eggcc: tuple) -> None:
    graph, trace, seed, _ = native_eggcc
    single = trace.split("; reproduction-selection-end", 1)[0] + "; reproduction-selection-end\n"
    for altered in (single, trace + "\n" + single):
        with pytest.raises(CaptureError, match="root request multiplicity"):
            eggcc_output_checks(graph, altered, ["main"], seed)


def test_eggcc_rejects_opaque_transformations_and_missing_roots(native_eggcc: tuple) -> None:
    graph, trace, seed, _ = native_eggcc
    with pytest.raises(CaptureError, match="initialization"):
        eggcc_output_checks(graph, trace, ["main", "helper"], seed)
    changed = copy.deepcopy(graph)
    changed["nodes"]["const2"]["children"][0] = "int1"
    with pytest.raises(CaptureError, match="child provenance"):
        eggcc_output_checks(changed, trace, ["main"], seed)
    changed = copy.deepcopy(graph)
    changed["nodes"]["ctx"]["op"] = "DumC"
    with pytest.raises(CaptureError, match="unrepresentable original"):
        eggcc_output_checks(changed, trace, ["main"], seed)


def test_eggcc_rejects_ambiguous_named_application_roots(native_eggcc: tuple) -> None:
    graph, trace, seed, _ = native_eggcc
    graph["nodes"]["input"]["eclass"] = "Expr-unrelated"
    with pytest.raises(CaptureError, match="ambiguous original Function"):
        eggcc_output_checks(graph, trace, ["main"], seed)


def test_finite_relational_query_preserves_cycles_and_sharing() -> None:
    graph = {
        "nodes": {
            "a": {"op": "Pair", "children": ["b", "b"], "eclass": "E-0"},
            "b": {"op": "Loop", "children": ["a"], "eclass": "E-1"},
        }
    }
    query = WitnessQuery(graph, "test_")
    assert query.original("a") == query.original("a")
    assert len(query.facts) == 2
    assert "(Pair test_o1 test_o1)" in query.finish()
    assert "(Loop test_o0)" in query.finish()


def test_tiger_missing_or_non_topological_evidence_is_blocked(native_eggcc: tuple) -> None:
    _, trace, _, _ = native_eggcc
    with pytest.raises(CaptureError, match="complete original-node"):
        tiger_selections("(let output (DumC))")
    with pytest.raises(CaptureError, match="earlier selected"):
        tiger_selections(trace.replace("; reproduction-node 74797065", "; reproduction-node 74797065 99"))


def test_eggcc_sessions_keep_reconstruction_separate_and_require_full_parent(native_eggcc: tuple) -> None:
    *_, events = native_eggcc
    sessions = eggcc_sessions(events)
    assert [session["kind"] for session in sessions] == ["optimization", "reconstruction"]
    assert len(sessions[0]["roots"]) == 2  # Every native Tiger alias request.
    assert sessions[1]["roots"] == [
        {
            "name": "main",
            "output": 0,
            "event": 2,
            "program_sha256": hashlib.sha256(events[2]["payload"]["outputs"][0]["program"].encode()).hexdigest(),
        }
    ]  # The fresh graph returned one actual Function row to the host.
    assert "DumC" not in sessions[0]["checks"]
    assert "DumC" in sessions[1]["checks"]
    with pytest.raises(CaptureError, match="parent optimization"):
        eggcc_sessions(events[:-1])
    events[0]["payload"]["expected_passes"] = 3
    events[0]["payload"]["cutoff"] = 3
    with pytest.raises(CaptureError, match="only a prefix"):
        eggcc_sessions(events)


def test_eggcc_sessions_require_actual_host_reconstruction_outputs(native_eggcc: tuple) -> None:
    *_, events = native_eggcc
    events[2]["payload"]["outputs"] = []
    with pytest.raises(CaptureError, match="every requested Function"):
        eggcc_sessions(events)


@pytest.fixture
def anchorable_eggcc(native_eggcc: tuple) -> tuple[dict, str, str, list[dict]]:
    """A synthetic protocol graph with typed constructor and initializer evidence."""
    graph, trace, seed, events = native_eggcc
    graph["class_data"] = {
        node["eclass"]: {"type": node["eclass"].split("-", 1)[0]} for node in graph["nodes"].values()
    }
    source = "\n".join(
        [
            "(datatype BaseType (IntT))",
            "(datatype Type (Base BaseType))",
            "(datatype Assumption (InFunc String) (Derived Assumption))",
            "(datatype Constant (Int i64))",
            "(datatype Expr (Const Constant Type Assumption) (Function String Type Type Expr))",
            "(relation FunctionHasType (String Type Type))",
            "(ruleset initialization)",
            "(rule () (\n; Program nodes\n" + seed + "\n; Loop context unions\n) :ruleset initialization)",
            "(run initialization 1)",
        ]
    )
    events[0]["payload"]["program"] = source
    return graph, trace, seed, events


def test_eggcc_anchors_all_native_root_aliases_and_preserves_selected_facts(anchorable_eggcc: tuple) -> None:
    graph, trace, seed, events = anchorable_eggcc
    source = events[0]["payload"]["program"]
    replay, plan = eggcc_source_anchors(graph, trace, source)
    checks, roots = eggcc_output_checks(graph, trace, ["main"], seed, source_anchors=plan)
    structural, _ = eggcc_output_checks(graph, trace, ["main"], seed)
    assert len(plan["observation_tables"]) == 3
    assert {entry["binding"] for entry in plan["observation_tables"]} == {"ty", "ctx", "fun"}
    restored = replay
    for entry in plan["observation_tables"]:
        restored = restored.replace(f"(function {entry['table']} () {entry['sort']} :merge old)\n", "")
        restored = restored.replace(f"(set ({entry['table']}) {entry['binding']})\n", "")
    assert restored == source
    for old, new in zip(egglog_forms(structural), egglog_forms(checks), strict=True):
        old_facts = egglog_forms(structural[old[0] : old[1]][6:-1])
        new_facts = egglog_forms(checks[new[0] : new[1]][6:-1])
        assert [t for _, _, t in old_facts if re.fullmatch(r"reproduction_\d+_s\d+", t[2])] == [
            t for _, _, t in new_facts if re.fullmatch(r"reproduction_\d+_s\d+", t[2])
        ]
    assert len(roots) == 2 and all(root["witness"]["input"]["mode"] == "source-handle" for root in roots)
    assert all(root["witness"]["query_fact_count"] == 11 for root in roots)
    assert "(Int 1)" not in checks and "(= reproduction_0_s3 2)" in checks
    assert "(let " not in checks and "(set " not in checks and "(union " not in checks
    sessions = eggcc_sessions(events)
    assert sessions[0]["program"] == source
    assert sessions[0]["replay_program"] == replay
    assert sessions[0]["selection_lookups"]["status"] == "existing-row-dag"
    assert sessions[0]["source_anchors"] == plan
    assert plan["original_program_sha256"] == hashlib.sha256(source.encode()).hexdigest()
    assert plan["replay_program_sha256"] == hashlib.sha256(replay.encode()).hexdigest()


@pytest.mark.parametrize(
    "change",
    [
        "second-run",
        "nonempty-body",
        "extra-rule",
        "push-pop",
        "nested-push-pop",
        "nested-keep-best",
        "unknown-macro",
    ],
)
def test_eggcc_anchor_initializer_scope_falls_back_explicitly(anchorable_eggcc: tuple, change: str) -> None:
    graph, trace, seed, events = anchorable_eggcc
    source = events[0]["payload"]["program"]
    if change == "second-run":
        source += "\n(run initialization 1)"
    elif change == "nonempty-body":
        source = source.replace("(rule () (", "(rule ((= x (IntT))) (")
    elif change == "extra-rule":
        source += "\n(rule () ((IntT)) :ruleset initialization)"
    elif change == "push-pop":
        source += "\n(push)\n(pop)"
    elif change == "nested-push-pop":
        source += "\n(run-schedule (repeat 1 (push) (pop)))"
    elif change == "nested-keep-best":
        source += '\n(run-schedule (repeat 1 (keep-best "Function")))'
    else:
        source += "\n(unknown-control-macro)"
    replay, plan = eggcc_source_anchors(graph, trace, source)
    assert replay == source and plan["status"] == "structural-fallback" and plan["reason"]
    checks, roots = eggcc_output_checks(graph, trace, ["main"], seed, source_anchors=plan)
    assert checks == eggcc_output_checks(graph, trace, ["main"], seed)[0]
    assert all(root["witness"]["input"]["fallback_reason"] for root in roots)


def test_eggcc_anchor_rejects_ambiguous_constructor_rows(anchorable_eggcc: tuple) -> None:
    graph, trace, _, events = anchorable_eggcc
    graph["nodes"]["other-type"] = {"op": "IntT", "children": [], "eclass": "BaseType-other"}
    graph["class_data"]["BaseType-other"] = {"type": "BaseType"}
    with pytest.raises(CaptureError, match="ambiguous native constructor identity"):
        eggcc_source_anchors(graph, trace, events[0]["payload"]["program"])


def test_eggcc_anchor_retains_ungrounded_derived_cycle(anchorable_eggcc: tuple) -> None:
    graph, trace, seed, events = anchorable_eggcc
    graph["nodes"]["derived-ctx"] = {"op": "Derived", "children": ["derived-ctx"], "eclass": "Assumption-derived"}
    graph["class_data"]["Assumption-derived"] = {"type": "Assumption"}
    graph["nodes"]["const2"]["children"][2] = "derived-ctx"
    _, plan = eggcc_source_anchors(graph, trace, events[0]["payload"]["program"])
    checks, roots = eggcc_output_checks(graph, trace, ["main"], seed, source_anchors=plan)
    assert "Assumption-derived" not in plan["classes"]
    for start, end, _ in egglog_forms(checks):
        cyclic = [t for _, _, t in egglog_forms(checks[start:end][6:-1]) if "Derived" in t]
        assert len(cyclic) == 1 and cyclic[0][2] == cyclic[0][5]
    assert all(root["witness"]["input"]["mode"] == "source-handle" for root in roots)
    assert all(any(field["fallback_reason"] for field in root["witness"]["erased_fields"]) for root in roots)


def test_eggcc_anchor_uses_existing_global_only_with_verified_source_identity(anchorable_eggcc: tuple) -> None:
    graph, trace, _, events = anchorable_eggcc
    source = events[0]["payload"]["program"].replace(
        "(ruleset initialization)", '(let existing-context (InFunc "main-context"))\n(ruleset initialization)'
    )
    graph["class_data"]["Assumption-1"]["let"] = "existing-context"
    replay, plan = eggcc_source_anchors(graph, trace, source)
    assert plan["classes"]["Assumption-1"]["lookup"] == "existing-context"
    assert len(plan["observation_tables"]) == 2
    assert replay.count('(let existing-context (InFunc "main-context"))') == 1
    graph["class_data"]["Assumption-1"]["let"] = "unrelated-name"
    _, plan = eggcc_source_anchors(graph, trace, source)
    assert plan["classes"]["Assumption-1"]["kind"] == "initializer"
    assert len(plan["observation_tables"]) == 3


@pytest.mark.parametrize("scheduled", [False, True])
def test_eggcc_anchor_constructor_deletion_gate_tracks_combined_schedules(
    anchorable_eggcc: tuple, scheduled: bool
) -> None:
    graph, trace, seed, events = anchorable_eggcc
    source = events[0]["payload"]["program"] + (
        "\n(ruleset delete-types)\n"
        "(rule ((IntT)) ((delete (IntT))) :ruleset delete-types)\n"
        "(unstable-combined-ruleset combined-delete delete-types)\n"
    )
    if scheduled:
        source += "(run combined-delete 1)\n"
    _, plan = eggcc_source_anchors(graph, trace, source)
    checks, roots = eggcc_output_checks(graph, trace, ["main"], seed, source_anchors=plan)
    if scheduled:
        assert plan["constructor_lifetime"]["deleted_constructor_heads"] == ["IntT"]
        assert set(plan["unresolved_source_bindings"]) == {"ty", "body", "fun"}
        assert "Type-1" not in plan["classes"]
        assert all(root["witness"]["input"]["mode"] == "structural" for root in roots)
        assert "(Int 1)" in checks
    else:
        assert plan["constructor_lifetime"]["deleted_constructor_heads"] == []
        assert len(plan["observation_tables"]) == 3


def test_eggcc_anchor_allows_subsumption_and_rejects_namespace_collision(anchorable_eggcc: tuple) -> None:
    graph, trace, _, events = anchorable_eggcc
    source = events[0]["payload"]["program"] + "\n(subsume (IntT))\n"
    _, plan = eggcc_source_anchors(graph, trace, source)
    assert len(plan["observation_tables"]) == 3
    with pytest.raises(CaptureError, match="source collides"):
        eggcc_source_anchors(graph, trace, source + "(relation reproduction_anchor_0 ())")


def egglog_trees(source: str) -> list[list[Any]]:
    """Read generated syntax for independent body/action and dependency assertions."""
    trees = []
    for _, _, tokens in egglog_forms(source):
        stack: list[list[Any]] = [[]]
        for token in tokens:
            if token == "(":
                stack.append([])
            elif token == ")":
                value = stack.pop()
                stack[-1].append(value)
            else:
                stack[-1].append(token)
        assert len(stack) == 1 and len(stack[0]) == 1
        trees.append(stack[0][0])
    return trees


@pytest.fixture
def eggcc_lookup_inputs(anchorable_eggcc: tuple) -> tuple[str, dict, str, str, list[dict], dict]:
    graph, trace, seed, events = anchorable_eggcc
    source = events[0]["payload"]["program"]
    replay, anchors = eggcc_source_anchors(graph, trace, source)
    checks, roots = eggcc_output_checks(graph, trace, ["main"], seed, source_anchors=anchors)
    return replay, graph, trace, checks, roots, anchors


def test_eggcc_dag_lookups_preserve_exact_typed_constraints_and_only_observe(eggcc_lookup_inputs: tuple) -> None:
    source, graph, trace, checks, roots, anchors = eggcc_lookup_inputs
    original_roots = copy.deepcopy(roots)
    suffix, root_checks, plan = eggcc_dag_lookups(*eggcc_lookup_inputs)
    assert roots == original_roots
    assert plan["status"] == "existing-row-dag" and plan["reason"] is None
    assert plan["original_checks_sha256"] == hashlib.sha256(checks.encode()).hexdigest()
    assert plan["source_prefix_sha256"] == hashlib.sha256(source.encode()).hexdigest()
    assert plan["lookup_program_sha256"] == hashlib.sha256(suffix.encode()).hexdigest()
    assert plan["root_checks_sha256"] == hashlib.sha256(root_checks.encode()).hexdigest()
    assert plan["proof_compatibility"]["status"] == "unvalidated"
    assert plan["proof_compatibility"]["ordinary_only"] is True
    forms = egglog_trees(suffix)
    assert {form[0] for form in forms} == {"function", "ruleset", "rule", "run"}
    declarations = [form for form in forms if form[0] == "function"]
    tables = {form[3]: form[1] for form in declarations}
    assert set(tables) == {"BaseType", "Type", "Constant", "Expr"}
    assert tables == plan["tables"]
    assert all(form == ["function", form[1], ["i64", "i64"], form[3], ":no-merge"] for form in declarations)
    original_tokens = {token for _, _, tokens in egglog_forms(source) for token in tokens}
    assert not set(tables.values()) & original_tokens
    rules = [form for form in forms if form[0] == "rule"]
    assert len(rules) == 10  # Five nonliteral nodes for each of two alias-root requests.
    original_queries = egglog_trees(checks)
    selected = {
        fact[1]: fact
        for query in original_queries
        for fact in query[1:-1]
        if re.fullmatch(r"reproduction_\d+_s\d+", fact[1])
    }
    selected_constructors = {name: fact for name, fact in selected.items() if isinstance(fact[2], list)}
    assert {rule[1][-1][1]: rule[1][-1] for rule in rules} == selected_constructors
    runs = [form for form in forms if form[0] == "run"]
    assert all(len(form) == 3 and form[2] == "1" for form in runs)
    execution_order = {form[1]: index for index, form in enumerate(runs)}
    observations = {}
    rule_order = {}
    for rule in rules:
        assert ":internal-include-subsumed" in rule
        fact = rule[1][-1]
        match = re.fullmatch(r"reproduction_(\d+)_s(\d+)", fact[1])
        assert match is not None
        request, index = map(int, match.groups())
        node_id = tiger_selections(trace)[request][index][0]
        sort = graph["class_data"][graph["nodes"][node_id]["eclass"]]["type"]
        key = [tables[sort], str(request), str(index)]
        assert rule[2] == [["set", key, fact[1]]]
        assert tuple(key) not in observations
        observations[tuple(key)] = fact[1]
        rule_order[tuple(key)] = execution_order[rule[rule.index(":ruleset") + 1]]
    expected_keys = {
        (tables[sort], str(request), str(index))
        for request in range(2)
        for index, sort in ((1, "BaseType"), (2, "Type"), (4, "Constant"), (5, "Expr"), (6, "Expr"))
    }
    assert set(observations) == expected_keys
    assert plan["expected_rows"] == {
        tables[sort]: count for sort, count in {"BaseType": 2, "Type": 2, "Constant": 2, "Expr": 4}.items()
    }
    for rule in rules:
        parent_key = tuple(rule[2][0][1])
        for fact in rule[1][:-1]:
            value = fact[2]
            if isinstance(value, list) and value[0] in tables.values():
                assert observations[tuple(value)] == fact[1]
                assert rule_order[tuple(value)] < rule_order[parent_key]
    for request in range(2):
        prefix = f"reproduction_{request}_"
        by_variable = {rule[1][-1][1]: rule for rule in rules}
        literal = ["=", prefix + "s3", "2"]
        assert literal in by_variable[prefix + "s4"][1]
        root = by_variable[prefix + "s6"]
        assert root[1][-1][2] == ["Function", prefix + "s0", prefix + "s2", prefix + "s2", prefix + "s5"]
        assert sum(fact[1] == prefix + "s2" for fact in root[1][:-1]) == 1
        assert ["=", prefix + "s0", '"main"'] in root[1]
        erased_bindings = [fact for fact in original_queries[request][1:-1] if re.fullmatch(prefix + r"o\d+", fact[1])]
        assert len(erased_bindings) == 2
        assert all(fact in by_variable[prefix + "s5"][1] for fact in erased_bindings)
        root_query = egglog_trees(root_checks)[request]
        assert root_query == [
            "check",
            original_queries[request][1],
            ["=", prefix + "s6", [tables["Expr"], str(request), "6"]],
            original_queries[request][-1],
        ]
        metadata = plan["requests"][request]
        assert metadata["request"] == request and metadata["selected_nodes"] == 7
        assert metadata["selected_facts_sha256"] == original_roots[request]["witness"]["selected_facts_sha256"]
        assert metadata["root_observer"] == {"table": tables["Expr"], "key": [request, 6], "sort": "Expr"}
        before_start, before_end, _ = egglog_forms(checks)[request]
        after_start, after_end, _ = egglog_forms(root_checks)[request]
        assert metadata["original_query_sha256"] == hashlib.sha256(checks[before_start:before_end].encode()).hexdigest()
        assert metadata["root_check_sha256"] == hashlib.sha256(root_checks[after_start:after_end].encode()).hexdigest()
        request_rules = [
            suffix[start:end]
            for start, end, tokens in egglog_forms(suffix)
            if tokens[1] == "rule" and any(token.startswith(prefix + "s") for token in tokens)
        ]
        assert metadata["lookup_rules_sha256"] == hashlib.sha256("\n".join(request_rules).encode()).hexdigest()


def test_eggcc_dag_lookups_keep_distinct_indices_for_the_same_native_class(eggcc_lookup_inputs: tuple) -> None:
    source, graph, trace, checks, roots, anchors = copy.deepcopy(eggcc_lookup_inputs)
    trace = trace.replace(
        f"; reproduction-node {b'output'.hex()} 0 2 2 5",
        f"; reproduction-node {b'base'.hex()} 1\n; reproduction-node {b'output'.hex()} 0 2 6 5",
    )
    for request, root in enumerate(roots):
        prefix = f"reproduction_{request}_"
        checks = checks.replace(prefix + "s6", prefix + "s7")
        checks = checks.replace(
            f"(= {prefix}s7 (Function {prefix}s0 {prefix}s2 {prefix}s2",
            f"(= {prefix}s6 (Base {prefix}s1))\n  (= {prefix}s7 (Function {prefix}s0 {prefix}s2 {prefix}s6",
        )
        root["selected_nodes"] = 8
    suffix, _, plan = eggcc_dag_lookups(source, graph, trace, checks, roots, anchors)
    type_table = plan["tables"]["Type"]
    rules = [form for form in egglog_trees(suffix) if form[0] == "rule"]
    assert {tuple(rule[2][0][1][1:]) for rule in rules if rule[2][0][1][0] == type_table} == {
        ("0", "2"),
        ("0", "6"),
        ("1", "2"),
        ("1", "6"),
    }
    assert plan["expected_rows"][type_table] == 4
    for request in range(2):
        prefix = f"reproduction_{request}_"
        root_rule = next(rule for rule in rules if rule[1][-1][1] == prefix + "s7")
        assert ["=", prefix + "s2", [type_table, str(request), "2"]] in root_rule[1]
        assert ["=", prefix + "s6", [type_table, str(request), "6"]] in root_rule[1]


@pytest.mark.parametrize("constructor", ["Arg", "Empty"])
def test_eggcc_dag_lookups_ground_both_erased_fields_of_leaf_expressions(
    anchorable_eggcc: tuple, constructor: str
) -> None:
    graph, _, seed, events = anchorable_eggcc
    source = events[0]["payload"]["program"].replace(
        "(Function String", f"({constructor} Type Assumption) (Function String"
    )
    graph["nodes"]["const2"].update(op=constructor, children=["base", "ctx"])
    selected = [("primitive-name", []), ("type", []), ("base", [1]), ("const2", []), ("output", [0, 2, 2, 3])]
    trace = (
        "\n".join(
            [
                "; reproduction-selection-begin",
                *(
                    f"; reproduction-node {node.encode().hex()}" + "".join(f" {child}" for child in children)
                    for node, children in selected
                ),
                "; reproduction-selection-end\n",
            ]
        )
        * 2
    )
    replay, anchors = eggcc_source_anchors(graph, trace, source)
    checks, roots = eggcc_output_checks(graph, trace, ["main"], seed, source_anchors=anchors)
    suffix, _, plan = eggcc_dag_lookups(replay, graph, trace, checks, roots, anchors)
    assert plan["status"] == "existing-row-dag"
    for request, query in enumerate(egglog_trees(checks)):
        prefix = f"reproduction_{request}_"
        erased = [fact for fact in query[1:] if re.fullmatch(prefix + r"o\d+", fact[1])]
        rule = next(form for form in egglog_trees(suffix) if form[0] == "rule" and form[1][-1][1] == prefix + "s3")
        assert len(erased) == 2 and rule[1][:-1] == erased
        assert rule[1][-1] in query and rule[1][-1][2][0] == constructor


@pytest.mark.parametrize(
    "mutation",
    [
        "type",
        "fd-conflict",
        "projection",
        "retained-child",
        "literal",
        "forward",
        "cycle",
        "unknown-operator",
        "unknown-field",
        "extra-fact",
        "duplicate-variable",
        "noncanonical-selected-variable",
        "noncanonical-root-variable",
        "root-equality",
        "namespace",
    ],
)
def test_eggcc_dag_lookups_reject_changed_or_ambiguous_constraints(eggcc_lookup_inputs: tuple, mutation: str) -> None:
    source, graph, trace, checks, roots, anchors = copy.deepcopy(eggcc_lookup_inputs)
    if mutation == "type":
        graph["class_data"]["Type-1"]["type"] = "Assumption"
    elif mutation == "fd-conflict":
        graph["nodes"]["conflicting-type"] = {"op": "IntT", "children": [], "eclass": "BaseType-other"}
        graph["class_data"]["BaseType-other"] = {"type": "BaseType"}
    elif mutation == "projection":
        trace = trace.replace(f"; reproduction-node {b'const2'.hex()} 4", f"; reproduction-node {b'const2'.hex()} 4 2")
    elif mutation == "retained-child":
        graph["nodes"]["const2"]["children"][0] = "int1"
    elif mutation == "literal":
        checks = checks.replace("(= reproduction_0_s3 2)", "(= reproduction_0_s3 3)")
    elif mutation in {"forward", "cycle"}:
        child = 6 if mutation == "forward" else 4
        trace = trace.replace(f"; reproduction-node {b'int2'.hex()} 3", f"; reproduction-node {b'int2'.hex()} {child}")
    elif mutation == "unknown-operator":
        graph["nodes"]["int2"]["op"] = "MysteryInt"
        checks = checks.replace("(Int reproduction_", "(MysteryInt reproduction_")
    elif mutation == "unknown-field":
        source = source.replace("(Const Constant Type Assumption)", "(Const Constant Type Assumption Type)")
        graph["nodes"]["const2"]["children"].append("base")
    elif mutation == "extra-fact":
        checks = checks.replace("(check", "(check (= ignored 23)", 1)
    elif mutation == "duplicate-variable":
        checks = checks.replace("(check", "(check (= reproduction_0_s3 2)", 1)
    elif mutation == "noncanonical-selected-variable":
        checks = checks.replace("(= reproduction_0_s2 (Base", "(= reproduction_0_s02 (Base", 1)
    elif mutation == "noncanonical-root-variable":
        checks = checks.replace("(= reproduction_0_s6 (Function", "(= reproduction_0_s06 (Function", 1)
    elif mutation == "root-equality":
        checks = checks.replace(
            "(= reproduction_0_seed4 reproduction_0_s6)", "(= reproduction_0_seed4 reproduction_0_s5)"
        )
    else:
        source += "\n(function reproduction_lookup_value_0 () Expr :no-merge)"
    with pytest.raises(CaptureError):
        eggcc_dag_lookups(source, graph, trace, checks, roots, anchors)


def test_eggcc_dag_lookups_reject_disconnected_selected_facts(eggcc_lookup_inputs: tuple) -> None:
    source, graph, trace, checks, roots, anchors = copy.deepcopy(eggcc_lookup_inputs)
    trace = trace.replace(
        f"; reproduction-node {b'output'.hex()}",
        f"; reproduction-node {b'primitive-one'.hex()}\n; reproduction-node {b'output'.hex()}",
    )
    for request, root in enumerate(roots):
        prefix = f"reproduction_{request}_"
        checks = checks.replace(prefix + "s6", prefix + "s7")
        checks = checks.replace(f"(= {prefix}s7 (Function", f"(= {prefix}s6 1)\n  (= {prefix}s7 (Function")
        root["selected_nodes"] = 8
    with pytest.raises(CaptureError, match="disconnected"):
        eggcc_dag_lookups(source, graph, trace, checks, roots, anchors)


@pytest.mark.parametrize("missing", ["all-types", "one-type", "root-anchor", "erased-anchor"])
def test_eggcc_dag_lookup_fallback_retains_every_structural_fact(anchorable_eggcc: tuple, missing: str) -> None:
    graph, trace, seed, events = anchorable_eggcc
    source = events[0]["payload"]["program"]
    if missing == "all-types":
        graph.pop("class_data")
    elif missing == "one-type":
        graph["class_data"].pop("Type-1")
    elif missing == "root-anchor":
        source += "\n(push)\n(pop)\n"
    else:
        graph["nodes"]["derived-ctx"] = {"op": "Derived", "children": ["derived-ctx"], "eclass": "Assumption-derived"}
        graph["class_data"]["Assumption-derived"] = {"type": "Assumption"}
        graph["nodes"]["const2"]["children"][2] = "derived-ctx"
    events[0]["payload"]["program"] = source
    replay, anchors = eggcc_source_anchors(graph, trace, source)
    checks, roots = eggcc_output_checks(graph, trace, ["main"], seed, source_anchors=anchors)
    suffix, unchanged, plan = eggcc_dag_lookups(source, graph, trace, checks, roots, anchors)
    assert suffix == "" and unchanged == checks
    assert plan["status"] == "structural-fallback" and plan["reason"]
    assert egglog_trees(unchanged) == egglog_trees(checks)
    if missing == "erased-anchor":
        assert "Derived" in unchanged
    session = eggcc_sessions(events)[0]
    assert session["replay_program"] == replay
    assert session["checks"] == checks
    assert session["selection_lookups"]["status"] == "structural-fallback"


def test_eggcc_dag_session_keeps_prefix_and_binds_each_alias_contract(anchorable_eggcc: tuple) -> None:
    graph, trace, seed, events = anchorable_eggcc
    source = events[0]["payload"]["program"] + "\n(subsume (IntT))\n"
    events[0]["payload"]["program"] = source
    replay, anchors = eggcc_source_anchors(graph, trace, source)
    checks, roots = eggcc_output_checks(graph, trace, ["main"], seed, source_anchors=anchors)
    suffix, final_checks, plan = eggcc_dag_lookups(replay, graph, trace, checks, roots, anchors)
    session, reconstructed = eggcc_sessions(events)
    assert session["program"] == source
    assert session["replay_program"] == replay
    assert session["lookup_program"] == suffix
    assert session["checks"] == final_checks
    assert session["selection_lookups"] == plan
    assert "selection_lookups" not in reconstructed
    for root, original, request in zip(session["roots"], roots, plan["requests"], strict=True):
        assert root["witness"]["input"] == original["witness"]["input"]
        assert root["witness"]["selection_lookup"] == request
        assert root["witness"]["structural_query_fact_count"] == original["witness"]["query_fact_count"]
        assert root["witness"]["query_fact_count"] == 3


def test_native_event_files_must_be_contiguous_and_complete(tmp_path: Path, native_eggcc: tuple) -> None:
    *_, events = native_eggcc
    for event in events:
        (tmp_path / f"event-{event['sequence']:06}.json").write_text(json.dumps(event))
    assert read_events(tmp_path) == events
    with pytest.raises(complete.CaptureResourceError, match="materialization budget"):
        read_events(tmp_path, max_bytes=1)
    (tmp_path / "event-000002.json").unlink()
    with pytest.raises(CaptureError, match="contiguous"):
        read_events(tmp_path)


def test_seed_query_rejects_insertions_and_unbound_values() -> None:
    with pytest.raises(CaptureError, match="unsupported action"):
        eggcc_seed_query("(union (A) (B))", "q_")
    with pytest.raises(CaptureError, match="unbound"):
        eggcc_seed_query("(let x (Function name ty ty body))", "q_")


@pytest.fixture
def native_churchroad(monkeypatch: pytest.MonkeyPatch) -> list[dict]:
    graph = {
        "nodes": {
            "a": {"op": "A", "children": [], "eclass": "Expr-0"},
            "b": {"op": "B", "children": [], "eclass": "Expr-0"},
            "primitive-module": {"op": '"mul"', "children": [], "eclass": "String-0"},
            "primitive-out": {"op": '"out"', "children": [], "eclass": "String-1"},
            "primitive-alias": {"op": '"alias"', "children": [], "eclass": "String-2"},
            "direction": {"op": "Output", "children": [], "eclass": "Direction-0"},
            "port": {
                "op": "IsPort",
                "children": ["primitive-module", "primitive-out", "direction", "a"],
                "eclass": "unit-0",
            },
            "alias": {
                "op": "IsPort",
                "children": ["primitive-module", "primitive-alias", "direction", "a"],
                "eclass": "unit-0",
            },
        }
    }
    declarations = "(ruleset enumerate-modules)\n"
    monkeypatch.setattr(complete, "CHURCHROAD_MODULE_ENUM_SHA256", hashlib.sha256(declarations.encode()).hexdigest())
    payloads: list[tuple[str, dict]] = []
    for program, include in [("(datatype E (A) (B))", None), (declarations, "/p/module_enumeration_rewrites.egg")]:
        payloads.extend(
            [
                ("commands", {"program": program, "include_path": include}),
                ("commands-result", {"success": True}),
            ]
        )
    payloads.extend(
        [
            ("yosys-output", {"success": True, "stdout": "(A)"}),
            ("commands", {"program": "(A)"}),
            ("commands-result", {"success": True}),
            ("initial-roots", {"names": ["out", "alias"]}),
            ("commands", {"program": "(ruleset mapping)"}),
            ("commands-result", {"success": True}),
            ("commands", {"program": "(run mapping 1)"}),
            ("commands-result", {"success": True}),
            ("mapping-snapshot", {"graph": graph, "proposals": []}),
            (
                "final-selection",
                {
                    "graph": graph,
                    "choices": [["Expr-0", "b"]],
                    "roots": [{"name": name, "class": "Expr-0", "node": "b"} for name in ["out", "alias"]],
                },
            ),
            ("parent-complete", {"verilog": "module mul(); endmodule"}),
        ]
    )
    return [
        {"version": 1, "sequence": i, "kind": kind, "payload": payload} for i, (kind, payload) in enumerate(payloads)
    ]


def test_churchroad_keeps_one_session_and_all_aliased_output_ports(native_churchroad: list[dict]) -> None:
    sessions = churchroad_sessions(native_churchroad)
    assert len(sessions) == 1
    assert [root["name"] for root in sessions[0]["roots"]] == ["out", "alias"]
    assert '(IsPort "mul" "out" (Output) churchroad_reproduction_final_0_s0)' in sessions[0]["checks"]
    assert '(IsPort "mul" "alias" (Output) churchroad_reproduction_final_1_s0)' in sessions[0]["checks"]
    assert "(let " not in sessions[0]["checks"] and "(union " not in sessions[0]["checks"]
    assert "enumerate-modules" not in "".join(part["program"] for part in sessions[0]["parts"])


def test_complete_churchroad_replay_carries_globals_and_binds_translated_contract(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, native_churchroad: list[dict]
) -> None:
    source = "(let a (A))\n"
    rules = "(ruleset mapping)\n(rule ((= e (A)) (= e a)) ((union e a)) :ruleset mapping)"
    for event in native_churchroad:
        payload = event["payload"]
        if event["kind"] == "yosys-output":
            payload["stdout"] = source
        elif event["kind"] == "commands" and payload["program"] == "(A)":
            payload["program"] = source
        elif event["kind"] == "commands" and payload["program"] == "(ruleset mapping)":
            payload["program"] = rules
    checkout = tmp_path / "checkout"
    checkout.mkdir()
    (checkout / "source.v").write_text("retained source identity")
    binary, engine = tmp_path / "compiler", tmp_path / "engine"
    binary.write_text("native compiler identity; never executed")
    engine.write_text("replay engine identity; never executed")

    def run(command: list[str], cwd: Path, prefix: Path, **kwargs: object) -> PilotProcessResult:
        assert command[0] == "env", "offline materialization must not run the replay engine"
        directory = Path(command[1].split("=", 1)[1])
        for event in native_churchroad:
            (directory / f"event-{event['sequence']:06}.json").write_text(json.dumps(event))
        Path(command[command.index("--out-filepath") + 1]).write_text(native_churchroad[-1]["payload"]["verilog"])
        stdout, stderr = Path(str(prefix) + ".stdout.log"), Path(str(prefix) + ".stderr.log")
        stdout.write_text("source output")
        stderr.write_text("")
        return PilotProcessResult("success", 0, 0, 0, stdout, stderr, None)

    monkeypatch.setattr(capture, "run_bounded_command", run)
    record = capture.capture_complete(
        "churchroad",
        [{"id": "case", "source": "source.v"}],
        tmp_path / "attempt",
        checkout,
        binary,
        engine,
        validate_ordinary=False,
    )[0]
    assert record["status"] == "ordinary-validation-pending" and not record["workloads"]
    session = record["sessions"][0]
    original = Path(session["raw"]).read_text()
    replay = Path(session["replay"]).read_text()
    assert source in original and rules in original
    assert "(= e $churchroad-global-a)" in replay and "(union e $churchroad-global-a)" in replay
    forms = [tokens for _, _, tokens in egglog_forms(replay)]
    expected = [tokens for _, _, tokens in egglog_forms(churchroad_sessions(native_churchroad)[0]["checks"])]
    assert [check["tokens"] for check in session["output_contract"]["checks"]] == expected
    for check in session["output_contract"]["checks"]:
        assert forms[check["command"]] == check["tokens"]
        assert check["prefix_sha256"] == hashlib.sha256(json.dumps(forms[: check["command"]]).encode()).hexdigest()


def test_churchroad_intermediate_selection_is_bound_to_actual_input(native_churchroad: list[dict]) -> None:
    graph = native_churchroad[-2]["payload"]["graph"]
    query = churchroad_selection_check(graph, {"Expr-0": "b"}, "b", input_node="a")
    assert "(= churchroad_reproduction_o0 (A))" in query
    assert "(= churchroad_reproduction_s0 (B))" in query
    assert "(= churchroad_reproduction_o0 churchroad_reproduction_s0)" in query
    graph["nodes"]["b"]["eclass"] = "Expr-unrelated"
    with pytest.raises(CaptureError, match="different original eclasses"):
        churchroad_selection_check(graph, {}, "b", input_node="a")


def test_churchroad_rejects_active_custom_rules_and_missing_host_feedback(native_churchroad: list[dict]) -> None:
    changed = copy.deepcopy(native_churchroad)
    changed[10]["payload"]["program"] = "(run enumerate-modules 1)"
    with pytest.raises(CaptureError, match="active Churchroad"):
        churchroad_sessions(changed)
    changed = copy.deepcopy(native_churchroad)
    changed[5]["payload"]["program"] = "(B)"
    with pytest.raises(CaptureError, match="not fed to the next"):
        churchroad_sessions(changed)
    changed = copy.deepcopy(native_churchroad)
    changed[-2]["payload"]["roots"].pop()
    with pytest.raises(CaptureError, match="output-port aliases"):
        churchroad_sessions(changed)


@pytest.mark.parametrize(
    "parent_status", ["success", "failure", "memory-limit", "ordinary-failure", "materialization-failure"]
)
def test_complete_adapter_admits_only_full_parent_and_checked_sessions(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    anchorable_eggcc: tuple,
    parent_status: str,
) -> None:
    *_, events = anchorable_eggcc
    # Exercise the actual compatibility adapter: its six original no-merge
    # helpers must change, while the appended observer declarations must not.
    events[0]["payload"]["program"] = (
        "(sort ExprSetPrim (Set Expr))\n"
        "(datatype Pointees (NoPointees))\n"
        + "".join(f"(function {name} () i64 :no-merge)\n" for name in sorted(capture.EGGCC_HELPERS))
        + events[0]["payload"]["program"]
    )
    checkout = tmp_path / "checkout"
    checkout.mkdir()
    (checkout / "source.bril").write_text("actual input")
    binary, engine = tmp_path / "compiler", tmp_path / "engine"
    binary.write_text("instrumented binary identity")
    engine.write_text("ordinary engine identity")
    called = []

    def run(command: list[str], cwd: Path, prefix: Path, **kwargs: object) -> PilotProcessResult:
        called.append((command, kwargs))
        stdout, stderr = Path(str(prefix) + ".stdout.log"), Path(str(prefix) + ".stderr.log")
        stdout.write_text("actual compiler output\n")
        stderr.write_text("")
        status = "success"
        if command[0] == "env":
            directory = Path(command[1].split("=", 1)[1])
            for event in events:
                (directory / f"event-{event['sequence']:06}.json").write_text(json.dumps(event))
            status = parent_status if parent_status in {"success", "failure", "memory-limit"} else "success"
        else:
            # Even a first replay failure must retain all prepared sessions.
            assert len(list(prefix.parent.glob("session-*.egg"))) == 4
            program = Path(command[-1]).read_text()
            assert "(check" in program
            if parent_status == "ordinary-failure":
                status = "failure"
        return PilotProcessResult(status, 0 if status == "success" else 1, 0.01, 0, stdout, stderr, None)  # type: ignore[arg-type]

    monkeypatch.setattr(capture, "run_bounded_command", run)
    if parent_status == "materialization-failure":

        def incomplete(events: list[dict]) -> list[dict]:
            sessions = eggcc_sessions(events)
            sessions[1]["program"] = "(unterminated"
            return sessions

        monkeypatch.setattr(capture, "eggcc_sessions", incomplete)
    records = capture.capture_complete(
        "eggcc",
        [{"id": "case", "source": "source.bril"}],
        tmp_path / "attempt",
        checkout,
        binary,
        engine,
    )
    record = records[0]
    assert record["status"] == (
        "reproduced"
        if parent_status == "success"
        else "ordinary-validation-failed"
        if parent_status == "ordinary-failure"
        else "blocked"
    )
    assert len(called) == (3 if parent_status == "success" else 2 if parent_status == "ordinary-failure" else 1)
    assert all(
        options["require_guard"] is True and options["disk_reserve_bytes"] == 10 * 1024**3 for _, options in called
    )
    if parent_status in {"success", "ordinary-failure"}:
        assert len(record["workloads"]) == (2 if parent_status == "success" else 0)
        assert len(record["source_completion"]["outputs"]) == 3
        assert all(session["output_contract"]["roots"] for session in record["sessions"])
        assert record["materialization"] == {"complete": True, "expected_sessions": 2, "materialized_sessions": 2}
        session = record["sessions"][0]
        assert Path(session["raw"]).read_text() == events[0]["payload"]["program"]
        generated = eggcc_sessions(events)[0]
        prefix = capture.adapt_eggcc(generated["replay_program"], typing_oracle=False)
        materialized = Path(session["replay"]).read_text()
        assert materialized == prefix + generated["lookup_program"] + "\n" + generated["checks"]
        assert prefix.count(":merge old") == len(capture.EGGCC_HELPERS) + 3
        assert materialized.count(":no-merge") == len(session["selection_lookups"]["tables"])
        assert session["source_anchors"]["status"] == "source-anchored"
        assert len(session["source_anchors"]["observation_tables"]) == 3
        assert "replay_program" not in session and "lookup_program" not in session
        assert session["output_contract"]["roots"] == session["roots"]
        assert all(root["witness"]["query_fact_count"] == 3 for root in session["roots"])
        for check in session["output_contract"]["checks"]:
            all_tokens = [tokens for _, _, tokens in egglog_forms(materialized)]
            assert all_tokens[check["command"]] == check["tokens"]
            assert (
                check["prefix_sha256"]
                == hashlib.sha256(json.dumps(all_tokens[: check["command"]]).encode()).hexdigest()
            )
        assert session["source_anchors"]["original_program_sha256"] == session["raw_sha256"].removeprefix("sha256:")
    elif parent_status == "materialization-failure":
        assert record["source_completion"]["parent_completed"]
        assert record["materialization"] == {"complete": False, "expected_sessions": 2, "materialized_sessions": 1}
        assert not record["workloads"]
    else:
        assert not record["workloads"] and not record["source_completion"]["parent_completed"]
    assert len(record["raw_invocations"]) == 2


@pytest.mark.parametrize("capture_first", [False, True])
@pytest.mark.parametrize("replay_status", ["success", "failure"])
def test_coordinator_validates_complete_sessions_once_before_publishing(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    native_eggcc: tuple,
    capture_first: bool,
    replay_status: str,
) -> None:
    from scripts import reproduction_dispatch as dispatch
    from scripts import reproduction_validation as validation
    from scripts import suite_reproduction as coordinator

    *_, events = native_eggcc
    checkout = tmp_path / "checkout"
    checkout.mkdir()
    (checkout / "source.bril").write_text("actual source identity")
    binary, engine = tmp_path / "compiler", tmp_path / "engine"
    binary.write_text("native compiler identity")
    engine.write_text("ordinary engine identity")
    (tmp_path / "benchmarks/reproduction").mkdir(parents=True)
    (tmp_path / "benchmarks/reproduction/population.json").write_text("{}")
    (tmp_path / "benchmarks/catalog.json").write_text("{}")
    for name in coordinator.VALIDATION_SOURCES:
        path = tmp_path / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("validation implementation identity")
    storage = tmp_path / "evidence"
    storage.mkdir()
    settings = {"eggcc": {"paths": {"checkout": str(checkout), "binary": str(binary), "egglog": str(engine)}}}
    (storage / "settings.json").write_text(json.dumps(settings))
    case = {"id": "case", "family": "eggcc", "scope": "required", "source": "source.bril", "configuration": {}}
    monkeypatch.setattr(coordinator, "ROOT", tmp_path)
    monkeypatch.setattr(coordinator, "STORAGE", storage)
    monkeypatch.setattr(dispatch, "ROOT", tmp_path)
    monkeypatch.setattr(coordinator, "expected_cases", lambda *_: [case])
    monkeypatch.setattr(coordinator, "case_identity", lambda case, settings, **_: {"case": case, "settings": settings})
    monkeypatch.setattr(capture, "adapt_eggcc", lambda source, **_: source)
    called: list[list[str]] = []

    def run(
        command: list[str], cwd: Path, prefix: Path, timeout_sec: float = 300, **kwargs: object
    ) -> PilotProcessResult:
        called.append(command)
        stdout, stderr = Path(str(prefix) + ".stdout.log"), Path(str(prefix) + ".stderr.log")
        status = "success"
        if command[0] == "env":
            directory = Path(command[1].split("=", 1)[1])
            for event in events:
                (directory / f"event-{event['sequence']:06}.json").write_text(json.dumps(event))
            stdout.write_text("actual compiler output\n")
        else:
            assert command[:3] == [str(engine), "-j", "1"]
            assert "(check" in Path(command[-1]).read_text()
            stdout.write_text("")
            status = replay_status
        stderr.write_text("")
        return PilotProcessResult(status, 0 if status == "success" else 1, 0.01, 0, stdout, stderr, None)  # type: ignore[arg-type]

    monkeypatch.setattr(capture, "run_bounded_command", run)
    monkeypatch.setattr(validation, "run_complete_command", run)
    argv = ["--family", "eggcc", "--case", "case"]
    if capture_first:
        assert coordinator.main([*argv, "--stage", "capture"]) == 1
        assert len(called) == 1  # Native parent only; no premature ordinary replay.
        outcome = json.loads((storage / "index.json").read_text())["case"]
        assert outcome["status"] == "ordinary-validation-pending"
        record = json.loads(Path(outcome["capture"]).read_text())
        assert record["materialization"]["complete"] and len(record["sessions"]) == 2
        assert record["workloads"] == []
        assert all("validation" not in session for session in record["sessions"])
        assert json.loads((storage / "corpus/manifest.json").read_text())["workloads"] == []
        assert not list((storage / "corpus").glob("*.egg"))
    assert coordinator.main([*argv, "--stage", "all"]) == (0 if replay_status == "success" else 1)
    assert len(called) == (3 if replay_status == "success" else 2)
    assert len({command[-1] for command in called[1:]}) == len(called) - 1
    outcome = json.loads((storage / "index.json").read_text())["case"]
    assert outcome["capture_stage"]["status"] == "ordinary-validation-pending"
    record = json.loads(Path(outcome["capture_stage"]["capture"]).read_text())
    assert record["workloads"] == [] and all("validation" not in session for session in record["sessions"])
    manifest = json.loads((storage / "corpus/manifest.json").read_text())
    assert len(manifest["workloads"]) == (2 if replay_status == "success" else 0)
    if replay_status == "success":
        assert outcome["workloads"] == [command[-1] for command in called[1:]]
        assert all(row["output_contract_passed"] for row in outcome["validations"])
    else:
        assert outcome["workloads"] == [] and not list((storage / "corpus").glob("*.egg"))
    assert coordinator.main([*argv, "--stage", "all"]) == (0 if replay_status == "success" else 1)
    assert len(called) == (3 if replay_status == "success" else 2)  # Immutable receipts reuse both stages.
