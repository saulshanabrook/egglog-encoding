"""Check mechanical compatibility edits for captured Churchroad invocations."""

import copy
import hashlib
import json
import re
import struct
from pathlib import Path
from typing import Any

import pytest

from scripts import eggcc_churchroad_complete as complete
from scripts import suite_capture_eggcc_churchroad as capture
from scripts.eggcc_churchroad_complete import (
    CaptureError,
    WitnessQuery,
    churchroad_mapping_session,
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

# Exact pinned memory.egg block, retaining its original multiline formatting.
EXPR_SET_BLOCK = """(sort ExprSetPrim (Set Expr))
(datatype ExprSet (ES ExprSetPrim))
(constructor ExprSet-intersect (ExprSet ExprSet) ExprSet)
(rewrite (ExprSet-intersect (ES set1) (ES set2)) (ES (set-intersect set1 set2))
         :ruleset memory-helpers)
(constructor ExprSet-union (ExprSet ExprSet) ExprSet)
(rewrite (ExprSet-union (ES set1) (ES set2)) (ES (set-union set1 set2))
         :ruleset memory-helpers)
(constructor ExprSet-insert (ExprSet Expr) ExprSet)
(rewrite (ExprSet-insert (ES set1) x) (ES (set-insert set1 x))
         :ruleset memory-helpers)
(function ExprSet-length (ExprSet) i64 :no-merge)
(rule ((ES set1)) ((set (ExprSet-length (ES set1)) (set-length set1)))
      :ruleset memory-helpers)
"""


@pytest.mark.parametrize("separator", [" ", "\n  ", "\n; declaration comment\n\t"])
def test_eggcc_helper_erasure_accepts_layout_and_preserves_inactive_references(separator: str) -> None:
    prefix = "; (sort ExprSetPrim (Set Expr)) is only a comment\n(ruleset memory-helpers)\n"
    suffix = (
        f"(datatype Pointees{separator}(NoPointees))\n"
        "; (constructor CellHasValues (Expr i64) ExprSet :merge (ExprSet-intersect old new))\n"
        "; ((set (CellHasValues e cell) (ES (set-empty))))\n"
        '(let label "ExprSet ExprSetPrim ES ExprSet-length")\n'
        + "".join(f"(function {name} () i64 :no-merge)\n" for name in sorted(capture.EGGCC_HELPERS))
        + "(run-schedule (seq (saturate memory-helpers) (run hacker 1)))\n"
    )
    adapted = capture.adapt_eggcc(prefix + EXPR_SET_BLOCK + suffix, typing_oracle=False)
    assert adapted.endswith(prefix + suffix.replace(":no-merge", ":merge old"))
    assert [tokens for _, _, tokens in egglog_forms(adapted)] == [
        tokens for _, _, tokens in egglog_forms(prefix + suffix.replace(":no-merge", ":merge old"))
    ]


@pytest.mark.parametrize(
    "reference",
    [
        "(constructor Active () ExprSet)",
        "(constructor Active () ExprSetPrim)",
        "(rule ((ES x)) ((print-size)))",
        "(rule ((= a (ExprSet-intersect x y))) ((set (Active) a)))",
    ],
)
@pytest.mark.parametrize("before", [False, True])
def test_eggcc_helper_erasure_rejects_active_outside_references(reference: str, before: bool) -> None:
    source = EXPR_SET_BLOCK + "(datatype Pointees\n (NoPointees))\n"
    source = reference + "\n" + source if before else source + reference
    with pytest.raises(ValueError, match="referenced outside"):
        capture.adapt_eggcc(source, typing_oracle=False)


@pytest.mark.parametrize("change", ["changed-rule", "extra-form", "missing-form", "duplicate-start", "duplicate-end"])
def test_eggcc_helper_erasure_rejects_changed_or_ambiguous_blocks(change: str) -> None:
    source = EXPR_SET_BLOCK + "(datatype Pointees\n (NoPointees))\n"
    if change == "changed-rule":
        source = source.replace("(set-union set1 set2)", "(set-intersect set1 set2)")
    elif change == "extra-form":
        source = source.replace("(datatype Pointees", '(rule () ((panic "active")))\n(datatype Pointees')
    elif change == "missing-form":
        source = source.replace("(datatype ExprSet (ES ExprSetPrim))\n", "")
    elif change == "duplicate-start":
        source += "(sort ExprSetPrim (Set Expr))\n"
    else:
        source += "(datatype Pointees (Another))\n"
    with pytest.raises(ValueError, match="pinned"):
        capture.adapt_eggcc(source, typing_oracle=False)


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
    trace = "\n".join(
        [
            "(datatype BaseType (IntT))",
            "(datatype Type (Base BaseType))",
            "(datatype Assumption (DumC))",
            "(datatype Constant (Int i64))",
            "(datatype Expr (Const Constant Type Assumption) (Function String Type Type Expr))",
            trace,
        ]
    )
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
            "(let prim (IntT))",
            "(let ty (Base prim))",
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
    assert "DumC" in sessions[1]["lookup_program"]
    assert sessions[1]["reconstruction_lookups"]["status"] == "existing-row-dag"
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


@pytest.mark.parametrize(
    "source_literal,native_literal,grounded",
    [
        ("0.00001", "1e-5", True),
        ("1e0", "1.0", True),
        ("-0.0", "-0e0", True),
        ("0.0", "-0.0", False),
        ("1.0", "1.0000000000000002", False),
        ("1e309", "inf", False),
        ("NaN", "NaN", False),
    ],
)
def test_eggcc_source_f64_grounding_uses_finite_bits_not_spelling_or_tolerance(
    anchorable_eggcc: tuple, source_literal: str, native_literal: str, grounded: bool
) -> None:
    graph, trace, _, events = anchorable_eggcc
    source = (
        events[0]["payload"]["program"]
        .replace("(Int i64)", "(Float f64)")
        .replace("(Int 1)", f"(Float {source_literal})")
    )
    for name in ("int1", "int2"):
        graph["nodes"][name]["op"] = "Float"
    for name in ("primitive-one", "primitive-two"):
        graph["class_data"][graph["nodes"][name]["eclass"]]["type"] = "f64"
    graph["nodes"]["primitive-one"]["op"] = native_literal
    # An identical untyped/i64 spelling must never be a candidate for f64.
    graph["nodes"]["integer-alias"] = {"op": source_literal, "children": [], "eclass": "i64-alias"}
    graph["class_data"]["i64-alias"] = {"type": "i64"}
    replay, plan = eggcc_source_anchors(graph, trace, source)
    assert ("fun" not in plan["unresolved_source_bindings"]) == grounded
    assert source_literal in replay and native_literal not in replay.replace(source_literal, "")
    if grounded:
        assert plan["f64_literal_matches"] == [
            {
                "source": source_literal,
                "native": [native_literal],
                "bits": struct.pack(">d", float(source_literal)).hex(),
                "sort": "f64",
                "class": graph["nodes"]["primitive-one"]["eclass"],
            }
        ]
        assert plan["root_classes"] == {"main": "Expr-root"}
    else:
        assert plan["f64_literal_matches"] == []
        assert "f64" in plan["unresolved_source_bindings"]["one"]


def test_eggcc_source_f64_ambiguous_native_classes_keep_structural_fallback(anchorable_eggcc: tuple) -> None:
    graph, trace, _, events = anchorable_eggcc
    source = events[0]["payload"]["program"].replace("(Int i64)", "(Float f64)").replace("(Int 1)", "(Float 0.00001)")
    graph["nodes"]["int1"]["op"] = "Float"
    graph["nodes"]["primitive-one"]["op"] = "1e-5"
    graph["class_data"]["i64-1"]["type"] = "f64"
    graph["nodes"]["duplicate-f64"] = {"op": "0.00001", "children": [], "eclass": "f64-other"}
    graph["class_data"]["f64-other"] = {"type": "f64"}
    _, plan = eggcc_source_anchors(graph, trace, source)
    assert plan["f64_literal_matches"] == []
    assert plan["unresolved_source_bindings"]["one"] == "source f64 bits have no unique retained native class"
    assert "main" not in plan["root_classes"]


@pytest.fixture
def derived_tuple_eggcc(anchorable_eggcc: tuple) -> tuple:
    """An erased TupleT created after initialization with a retained TypeList child."""
    graph, trace, seed, events = anchorable_eggcc
    graph["nodes"]["type-list"] = {"op": "TNil", "children": [], "eclass": "TypeList-1"}
    graph["nodes"]["derived-type"] = {"op": "TupleT", "children": ["type-list"], "eclass": "Type-derived"}
    graph["class_data"].update({"TypeList-1": {"type": "TypeList"}, "Type-derived": {"type": "Type"}})
    graph["nodes"]["const2"]["children"][1] = "derived-type"
    new_seed = "(let types (TNil))\n" + seed
    source = (
        events[0]["payload"]["program"]
        .replace(seed, new_seed)
        .replace(
            "(datatype Type (Base BaseType))",
            "(datatype TypeList (TNil))\n(datatype Type (Base BaseType) (TupleT TypeList))",
        )
    )
    source += (
        "\n(ruleset native-types)\n(rule ((= t (TNil))) ((TupleT t)) :ruleset native-types)\n(run native-types 1)\n"
    )
    events[0]["payload"]["program"] = source
    return graph, trace, new_seed, events


def test_eggcc_derived_tuple_observes_only_existing_rows_after_original_schedule(derived_tuple_eggcc: tuple) -> None:
    graph, trace, seed, events = derived_tuple_eggcc
    source = events[0]["payload"]["program"]
    replay, anchors = eggcc_source_anchors(graph, trace, source)
    checks, roots = eggcc_output_checks(graph, trace, ["main"], seed, source_anchors=anchors)
    suffix, root_checks, plan = eggcc_dag_lookups(replay, graph, trace, checks, roots, anchors)
    derived = anchors["derived_observations"]
    assert len(derived) == 1  # Both actual aliases use the same observed erased field.
    entry = derived[0]
    assert entry["native_class"] == "Type-derived" and entry["child_class"] == "TypeList-1"
    assert anchors["classes"]["TypeList-1"]["kind"] == "initializer"
    assert plan["status"] == "existing-row-dag" and len(egglog_forms(root_checks)) == 2
    assert entry["table"] not in replay
    original = replay
    for table in anchors["observation_tables"]:
        original = original.replace(f"(function {table['table']} () {table['sort']} :merge old)\n", "")
        original = original.replace(f"(set ({table['table']}) {table['binding']})\n", "")
    assert original == source  # Every original action/rule/schedule is byte-identical.
    forms = egglog_trees(suffix)
    rule = next(form for form in forms if form[0] == "rule")
    assert rule[1] == [
        ["=", "reproduction_derived_child", [anchors["classes"]["TypeList-1"]["table"]]],
        ["=", "reproduction_derived_value", ["TupleT", "reproduction_derived_child"]],
    ]
    assert rule[2] == [["set", [entry["table"]], "reproduction_derived_value"]]
    assert ["function", entry["table"], [], "Type", ":merge", "old"] in forms
    assert ":internal-include-subsumed" in rule
    run = next(i for i, form in enumerate(forms) if form[0] == "run")
    assert forms[run] == ["run", "reproduction_derived_types", "1"]
    assert all(form[0] != "run" or i >= run for i, form in enumerate(forms))
    assert plan["derived_observations"] == derived
    prefix = "\n".join(complete._eggcc_text(form) for form in forms[: run + 1]) + "\n"
    assert plan["derived_program_sha256"] == hashlib.sha256(prefix.encode()).hexdigest()
    session = eggcc_sessions(events)[0]
    assert session["program"] == source and session["lookup_program"] == suffix
    assert session["checks"] == root_checks and session["replay_program"] == replay


@pytest.mark.parametrize("existing_rows", [[], [("other-list", "other-type")]])
def test_eggcc_missing_or_wrong_tuple_row_cannot_populate_the_observer(
    derived_tuple_eggcc: tuple, existing_rows: list[tuple[str, str]]
) -> None:
    graph, trace, seed, events = derived_tuple_eggcc
    replay, anchors = eggcc_source_anchors(graph, trace, events[0]["payload"]["program"])
    checks, roots = eggcc_output_checks(graph, trace, ["main"], seed, source_anchors=anchors)
    suffix, _, plan = eggcc_dag_lookups(replay, graph, trace, checks, roots, anchors)
    rule = next(form for form in egglog_trees(suffix) if form[0] == "rule")
    # Evaluate just the two independently asserted relational body constraints:
    # there is no constructor action/default able to fill an absent lookup.
    assert rule[1][-1] == ["=", "reproduction_derived_value", ["TupleT", "reproduction_derived_child"]]
    child = anchors["derived_observations"][0]["child_class"]
    matched = [value for key, value in existing_rows if key == child]
    assert matched == []
    assert rule[2] == [["set", [anchors["derived_observations"][0]["table"]], "reproduction_derived_value"]]
    selected = [form for form in egglog_trees(suffix) if form[0] == "rule" and "reproduction_0_s5" in str(form)]
    assert len(selected) == 2  # Const produces the body; Function subsequently consumes it.
    assert anchors["derived_observations"][0]["lookup"] in complete._eggcc_text(selected[0][1])
    assert plan["status"] == "existing-row-dag"  # Runtime check remains required; this is no admission.


@pytest.mark.parametrize("change", ["ambiguous", "wrong-sort", "unanchored-child", "other-constructor"])
def test_eggcc_derived_tuple_limitations_keep_all_structural_constraints(
    derived_tuple_eggcc: tuple, change: str
) -> None:
    graph, trace, seed, events = derived_tuple_eggcc
    if change == "ambiguous":
        graph["nodes"]["conflicting-type"] = {"op": "TupleT", "children": ["type-list"], "eclass": "Type-other"}
        graph["class_data"]["Type-other"] = {"type": "Type"}
    elif change == "wrong-sort":
        graph["class_data"]["Type-derived"]["type"] = "Assumption"
    elif change == "unanchored-child":
        events[0]["payload"]["program"] = events[0]["payload"]["program"].replace("(let types (TNil))\n", "")
        seed = seed.replace("(let types (TNil))\n", "")
    else:
        graph["nodes"]["derived-type"]["op"] = "OtherType"
    replay, anchors = eggcc_source_anchors(graph, trace, events[0]["payload"]["program"])
    checks, roots = eggcc_output_checks(graph, trace, ["main"], seed, source_anchors=anchors)
    suffix, unchanged, plan = eggcc_dag_lookups(replay, graph, trace, checks, roots, anchors)
    assert not anchors["derived_observations"] and suffix == "" and unchanged == checks
    assert plan["status"] == "structural-fallback"
    if change != "other-constructor":
        assert anchors["unresolved_erased_fields"]["derived-type"]


def test_eggcc_derived_tuple_still_runs_when_another_constraint_is_structural(derived_tuple_eggcc: tuple) -> None:
    graph, trace, seed, events = derived_tuple_eggcc
    graph["nodes"]["derived-ctx"] = {"op": "Derived", "children": ["derived-ctx"], "eclass": "Assumption-derived"}
    graph["class_data"]["Assumption-derived"] = {"type": "Assumption"}
    graph["nodes"]["const2"]["children"][2] = "derived-ctx"
    replay, anchors = eggcc_source_anchors(graph, trace, events[0]["payload"]["program"])
    checks, roots = eggcc_output_checks(graph, trace, ["main"], seed, source_anchors=anchors)
    suffix, unchanged, plan = eggcc_dag_lookups(replay, graph, trace, checks, roots, anchors)
    assert plan["status"] == "structural-fallback" and unchanged == checks
    assert "Derived" in checks and "(reproduction_derived_type_0)" in checks
    assert suffix.endswith("(run reproduction_derived_types 1)\n")
    assert "reproduction_lookup_value_" not in suffix


@pytest.mark.parametrize(
    "name", ["reproduction_derived_child", "reproduction_derived_value", "reproduction_derived_type_0"]
)
def test_eggcc_derived_observer_rejects_source_name_collisions(derived_tuple_eggcc: tuple, name: str) -> None:
    graph, trace, seed, events = derived_tuple_eggcc
    source = events[0]["payload"]["program"] + f"\n(let {name} (TNil))\n"
    replay, anchors = eggcc_source_anchors(graph, trace, source)
    checks, roots = eggcc_output_checks(graph, trace, ["main"], seed, source_anchors=anchors)
    with pytest.raises(CaptureError, match="collides with a derived"):
        eggcc_dag_lookups(replay, graph, trace, checks, roots, anchors)


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
    assert plan["proof_compatibility"]["ordinary_only"] is False
    forms = egglog_trees(suffix)
    assert {form[0] for form in forms} == {"function", "ruleset", "rule", "run"}
    declarations = [form for form in forms if form[0] == "function"]
    tables = {form[3]: form[1] for form in declarations}
    assert set(tables) == {"BaseType", "Type", "Constant", "Expr"}
    assert tables == plan["tables"]
    assert all(form == ["function", form[1], ["i64", "i64"], form[3], ":merge", "old"] for form in declarations)
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


@pytest.fixture
def native_churchroad_phase(native_churchroad: list[dict]) -> list[dict]:
    events = native_churchroad[:13]
    source = "(let a (A))\n(B)"
    events[0]["payload"]["program"] = (
        "(datatype E (A) (B) (PrimitiveInterfaceDSP E E))\n(ruleset typing)\n(ruleset transform)"
    )
    events[4]["payload"]["stdout"] = events[5]["payload"]["program"] = source
    events[8]["payload"]["program"] = (
        "(ruleset mapping)\n(rule ((= x (B))) ((union x (PrimitiveInterfaceDSP a a))) :ruleset mapping)"
    )
    events[10]["payload"]["program"] = "(run-schedule (saturate (seq typing transform mapping)))"
    graph = events[12]["payload"]["graph"]
    graph["nodes"]["a"]["eclass"] = "Expr-1"
    graph["nodes"]["proposal"] = {"op": "PrimitiveInterfaceDSP", "children": ["a", "a"], "eclass": "Expr-0"}
    events[12]["payload"]["proposals"] = ["proposal"]
    for kind, payload in [
        (
            "selection",
            {
                "snapshot": "mapping",
                "kind": "spec",
                "input": "proposal",
                "root": "b",
                "choices": [["Expr-0", "b"], ["Expr-1", "a"]],
            },
        ),
        ("synthesis-input", {"spec": "native observed specification"}),
        ("synthesis-output", {"success": False, "code": 26}),
    ]:
        events.append({"version": 1, "sequence": len(events), "kind": kind, "payload": payload})
    return events


def test_churchroad_phase_preserves_whole_state_and_checks_observed_mapping(
    native_churchroad_phase: list[dict],
) -> None:
    session = churchroad_mapping_session(native_churchroad_phase)
    commands = [event for event in native_churchroad_phase[:13] if event["kind"] == "commands"]
    assert session["program"] == "\n".join(event["payload"]["program"] for event in commands)
    assert [part["program"] for part in session["parts"]] == [
        *(event["payload"]["program"] for event in commands if event is not commands[1]),
        "",
    ]
    assert session["events"] == list(range(14))
    assert session["mapping_snapshot_event"] == 12
    assert session["roots"] == [
        {"kind": "spec", "input": "proposal", "node": "b", "class": "Expr-0", "selection_event": 13}
    ]
    assert session["checks"] == churchroad_selection_check(
        native_churchroad_phase[12]["payload"]["graph"],
        {"Expr-0": "b", "Expr-1": "a"},
        "b",
        input_node="proposal",
        prefix="churchroad_reproduction_0_",
    )
    assert all(tokens[1] == "check" for _, _, tokens in egglog_forms(session["checks"]))
    assert "PrimitiveInterfaceDSP" in session["checks"] and "(B)" in session["checks"]
    assert "(let " not in session["checks"] and "(union " not in session["checks"]


@pytest.mark.parametrize(
    "change",
    [
        "setup-only",
        "failed-import",
        "failed-saturation",
        "partial-schedule",
        "empty-proposals",
        "missing-selection",
        "late-selection",
        "unrelated-spec",
        "active-enumeration",
        "missing-call",
    ],
)
def test_churchroad_phase_rejects_incomplete_or_unobserved_results(
    native_churchroad_phase: list[dict], change: str
) -> None:
    events = native_churchroad_phase
    if change == "setup-only":
        events = events[:4]
    elif change == "failed-import":
        events[4]["payload"]["success"] = False
    elif change == "failed-saturation":
        events[11]["payload"]["success"] = False
    elif change == "partial-schedule":
        events[10]["payload"]["program"] = "(run mapping 1)"
    elif change == "empty-proposals":
        events[12]["payload"]["proposals"] = []
    elif change == "missing-selection":
        events = events[:13]
    elif change == "late-selection":
        events[13], events[14] = events[14], events[13]
    elif change == "unrelated-spec":
        events[12]["payload"]["graph"]["nodes"]["b"]["eclass"] = "unrelated"
    elif change == "active-enumeration":
        events[8]["payload"]["program"] += "\n(run enumerate-modules 1)"
    else:
        del events[8]
    with pytest.raises(CaptureError):
        churchroad_mapping_session(events)


@pytest.fixture
def native_churchroad_circuit(native_churchroad: list[dict]) -> list[dict]:
    events = native_churchroad[:13]
    events[0]["payload"]["program"] += (
        "\n(function Wire (String i64) E)\n(function PrimitiveInterfaceDSP (E E) E)"
        "\n(function PrimitiveInterfaceDSP3 (E E E) E)\n(datatype Direction (Output))"
        "\n(relation IsPort (String String Direction E))\n(ruleset typing)\n(ruleset transform)"
    )
    imported = '(let a (A))\n(IsPort "mul" "out" (Output) a)\n(let out a)\n'
    imported += '(IsPort "mul" "alias" (Output) a)\n(let alias a)'
    events[4]["payload"]["stdout"] = events[5]["payload"]["program"] = imported
    events[10]["payload"]["program"] = "(run-schedule (saturate (seq typing transform mapping)))"
    return events


def test_churchroad_circuit_extracts_all_real_outputs_without_assumptions(
    native_churchroad_circuit: list[dict], tmp_path: Path
) -> None:
    session = churchroad_mapping_session(native_churchroad_circuit, circuit_outputs=True)
    commands = [event["payload"]["program"] for event in native_churchroad_circuit if event["kind"] == "commands"]
    assert session["program"] == "\n".join(commands)
    assert [part["program"] for part in session["parts"]] == [
        commands[0],
        *commands[2:],
        "(extract out)\n(extract alias)",
    ]
    assert all(not part["checks"] for part in session["parts"])
    assert [root["name"] for root in session["roots"]] == ["out", "alias"]
    assert session["events"] == list(range(13))
    record: dict[str, Any] = {"family": "churchroad", "sessions": []}
    capture.materialize_sessions(record, [session], tmp_path)
    replay = Path(record["sessions"][0]["replay"]).read_text()
    forms = [tokens for _, _, tokens in egglog_forms(replay)]
    assert forms[-2:] == [["(", "extract", f"$churchroad-global-{name}", ")"] for name in ("out", "alias")]
    assert not any(tokens[1] in {"check", "prove", "prove-extract", "union"} for tokens in forms)
    assert {tokens[2] for tokens in forms if ":unextractable" in tokens} == set(capture.CHURCHROAD_PLACEHOLDERS)
    assert forms[-3] == egglog_forms(commands[-1])[0][2]
    assert record["sessions"][0]["output_contract"]["claims_native_selection"] is False
    assert record["sessions"][0]["output_contract"]["claims_optimality"] is False
    assert Path(record["sessions"][0]["raw"]).read_text() == "\n".join(commands)


@pytest.mark.parametrize(
    "change",
    ["setup", "failed-import", "failed-saturation", "partial-schedule", "proposals", "port", "alias", "duplicate"],
)
def test_churchroad_circuit_recovery_rejects_incomplete_or_unbound_outputs(
    native_churchroad_circuit: list[dict], change: str
) -> None:
    events = native_churchroad_circuit
    if change == "setup":
        events = events[:4]
    elif change == "failed-import":
        events[6]["payload"]["success"] = False
    elif change == "failed-saturation":
        events[11]["payload"]["success"] = False
    elif change == "partial-schedule":
        events[10]["payload"]["program"] = "(run mapping 1)"
    elif change == "proposals":
        events[12]["payload"]["proposals"] = ["proposal"]
    elif change == "port":
        del events[12]["payload"]["graph"]["nodes"]["port"]
    elif change == "alias":
        imported = events[5]["payload"]["program"].replace("(let out a)", "(let out (B))")
        events[4]["payload"]["stdout"] = events[5]["payload"]["program"] = imported
    else:
        events[7]["payload"]["names"] = ["out", "out"]
    with pytest.raises(CaptureError):
        churchroad_mapping_session(events, circuit_outputs=True)


def test_churchroad_feedback_is_preserved_for_the_extractor_to_decide(
    native_churchroad_circuit: list[dict], tmp_path: Path
) -> None:
    events = native_churchroad_circuit
    events[0]["payload"]["program"] += "\n(function Loop (E) E)"
    imported = events[5]["payload"]["program"].replace("(let a (A))", '(let a (Wire "a" 32))\n(union a (Loop a))')
    events[4]["payload"]["stdout"] = events[5]["payload"]["program"] = imported
    nodes = events[12]["payload"]["graph"]["nodes"]
    nodes["a"].update(op="Loop", children=["a"])
    del nodes["b"]
    session = churchroad_mapping_session(events, circuit_outputs=True)
    record: dict[str, Any] = {"family": "churchroad", "sessions": []}
    capture.materialize_sessions(record, [session], tmp_path)
    replay = Path(record["sessions"][0]["replay"]).read_text()
    assert '(let $churchroad-global-a (Wire "a" 32))' in replay
    assert "(union $churchroad-global-a (Loop $churchroad-global-a))" in replay
    assert "(check " not in replay


@pytest.fixture
def reconstruction_lookup_inputs() -> tuple[str, str, list[dict[str, Any]]]:
    source = "\n".join(
        [
            "(datatype Type (I64T))",
            "(datatype Expr (Num i64) (F f64) (Text String) (Flag bool) (Pair Expr Expr)"
            " (Function String Type Type Expr))",
        ]
    )
    output = "\n".join(
        [
            "(let ty (I64T))",
            "(let n (Num 7))",
            "(let shared (Pair n n))",
            "(let same (Pair n n))",
            "(let body (Pair shared same))",
            '(let function (Function "main" ty ty body))',
            "(let PROG function)",
        ]
    )
    facts, roots = eggcc_seed_query(output, "reconstruction_")
    assert roots == {"main": "reconstruction_seed5"}
    return source, "(check\n " + "\n ".join(facts) + "\n)\n", [{"name": "main", "output": 0}]


def test_reconstruction_dag_keeps_all_facts_sharing_typed_edges_and_strict_counts(
    reconstruction_lookup_inputs: tuple,
) -> None:
    source, checks, roots = reconstruction_lookup_inputs
    prior = copy.deepcopy(roots)
    suffix, terminal, plan = complete.eggcc_reconstruction_lookups(source, checks, roots)
    assert roots == prior
    assert plan["status"] == "existing-row-dag"
    assert plan["proof_compatibility"]["status"] == "unvalidated"
    assert plan["proof_compatibility"]["ordinary_only"] is False
    for field, value in (
        ("source_prefix", source),
        ("original_checks", checks),
        ("lookup_program", suffix),
        ("root_checks", terminal),
    ):
        assert plan[field + "_sha256"] == hashlib.sha256(value.encode()).hexdigest()
    forms = egglog_trees(suffix)
    assert {form[0] for form in forms} == {"function", "ruleset", "rule", "run"}
    tables = plan["tables"]
    assert plan["expected_rows"] == {tables["Type"]: 1, tables["Expr"]: 6}
    declarations = [form for form in forms if form[0] == "function"]
    assert all(form == ["function", form[1], ["i64", "i64"], form[3], ":merge", "old"] for form in declarations)
    rules = [form for form in forms if form[0] == "rule"]
    facts = egglog_trees(checks)[0][1:]
    assert [rule[1][-1] for rule in rules] == facts  # Includes the terminal alias equality.
    assert all(":internal-include-subsumed" in rule for rule in rules)
    assert all(rule[2] == [["set", rule[2][0][1], rule[1][-1][1]]] for rule in rules)
    assert {rule[2][0][1][2] for rule in rules} == {str(i) for i in range(7)}
    assert rules[2][1][:-1] == [["=", "reconstruction_seed1", [tables["Expr"], "0", "1"]]]
    assert rules[2][1][-1][2] == ["Pair", "reconstruction_seed1", "reconstruction_seed1"]
    assert rules[3][1][-1][2] == rules[2][1][-1][2]
    assert rules[2][2][0][1] != rules[3][2][0][1]  # Equal values retain both original node indices.
    assert egglog_trees(terminal) == [["check", ["=", "reconstruction_seed6", [tables["Expr"], "0", "6"]]]]
    request = plan["requests"][0]
    assert request["query_fact_count"] == 7 and request["constructor_facts"] == 6
    assert request["root_observer"] == {"table": tables["Expr"], "key": [0, 6], "sort": "Expr"}
    assert (
        request["lookup_rules_sha256"]
        == hashlib.sha256("\n".join(complete._eggcc_text(r) for r in rules).encode()).hexdigest()
    )
    order = {form[1]: i for i, form in enumerate(forms) if form[0] == "run"}
    by_key = {tuple(rule[2][0][1]): rule for rule in rules}
    for rule in rules:
        for dependency in rule[1][:-1]:
            child = by_key[tuple(dependency[2])]
            assert order[child[child.index(":ruleset") + 1]] < order[rule[rule.index(":ruleset") + 1]]


@pytest.mark.parametrize("operator,literal", [("Num", "-7"), ("F", "1.25e-4"), ("Text", '"a\\\\b"'), ("Flag", "true")])
def test_reconstruction_dag_preserves_typed_literal_spelling(
    reconstruction_lookup_inputs: tuple, operator: str, literal: str
) -> None:
    source, checks, roots = reconstruction_lookup_inputs
    checks = checks.replace("(Num 7)", f"({operator} {literal})")
    suffix, _, _ = complete.eggcc_reconstruction_lookups(source, checks, roots)
    rule = next(form for form in egglog_trees(suffix) if form[0] == "rule" and form[1][-1][1] == "reconstruction_seed1")
    assert rule[1][-1][2] == [operator, literal]


@pytest.mark.parametrize(
    "mutation",
    [
        "unknown",
        "nested",
        "wrong-sort",
        "wrong-literal-sort",
        "forward",
        "duplicate",
        "variable",
        "name",
        "root",
        "count",
        "output-order",
        "namespace",
        "schema",
    ],
)
def test_reconstruction_dag_rejects_changed_or_ungrounded_contracts(
    reconstruction_lookup_inputs: tuple, mutation: str
) -> None:
    source, checks, roots = copy.deepcopy(reconstruction_lookup_inputs)
    if mutation == "unknown":
        checks = checks.replace("(Num 7)", "(Unknown 7)")
    elif mutation == "nested":
        checks = checks.replace("(Num 7)", "(Num (Num 7))")
    elif mutation == "wrong-sort":
        checks = checks.replace("(Num 7)", "(Num reconstruction_seed0)")
    elif mutation == "wrong-literal-sort":
        checks = checks.replace("(Num 7)", "(Num 7.0)")
    elif mutation == "forward":
        checks = checks.replace(
            "(Pair reconstruction_seed1 reconstruction_seed1)", "(Pair reconstruction_seed2 reconstruction_seed1)", 1
        )
    elif mutation == "duplicate":
        checks = checks.replace("(= reconstruction_seed1", "(= reconstruction_seed0", 1)
    elif mutation == "variable":
        checks = checks.replace("(= reconstruction_seed1", "(= reconstruction_seed01", 1)
    elif mutation == "name":
        checks = checks.replace('"main"', '"other"')
    elif mutation == "root":
        checks = checks.replace(
            "(= reconstruction_seed6 reconstruction_seed5)", "(= reconstruction_seed6 reconstruction_seed4)"
        )
    elif mutation == "count":
        checks += checks
    elif mutation == "output-order":
        roots[0]["output"] = 1
    elif mutation == "namespace":
        source += "\n(function reconstruction_lookup_value_0 () Expr :no-merge)"
    else:
        source = ""
    with pytest.raises(CaptureError):
        complete.eggcc_reconstruction_lookups(source, checks, roots)


def test_reconstruction_dag_rejects_disconnected_evidence(reconstruction_lookup_inputs: tuple) -> None:
    source, checks, roots = reconstruction_lookup_inputs
    checks = checks.replace(
        "(Pair reconstruction_seed2 reconstruction_seed3)", "(Pair reconstruction_seed2 reconstruction_seed2)"
    )
    with pytest.raises(CaptureError, match="disconnected"):
        complete.eggcc_reconstruction_lookups(source, checks, roots)


def test_reconstruction_wrong_edge_stays_a_real_query_not_a_constructor_action(
    reconstruction_lookup_inputs: tuple,
) -> None:
    source, checks, roots = reconstruction_lookup_inputs
    checks = checks.replace(
        "(= reconstruction_seed3 (Pair reconstruction_seed1 reconstruction_seed1))", "(= reconstruction_seed3 (Num 8))"
    )
    changed = checks.replace(
        "(Pair reconstruction_seed2 reconstruction_seed3)", "(Pair reconstruction_seed3 reconstruction_seed2)"
    )
    suffix, _, plan = complete.eggcc_reconstruction_lookups(source, changed, roots)
    rule = next(form for form in egglog_trees(suffix) if form[0] == "rule" and form[1][-1][1] == "reconstruction_seed4")
    assert rule[1][-1][2] == ["Pair", "reconstruction_seed3", "reconstruction_seed2"]
    assert rule[2][0][2] == "reconstruction_seed4"
    assert plan["original_checks_sha256"] == hashlib.sha256(changed.encode()).hexdigest()


def test_reconstruction_dag_handles_deep_shared_ground_terms_without_recursive_expansion(
    reconstruction_lookup_inputs: tuple,
) -> None:
    source, _, roots = reconstruction_lookup_inputs
    output = ["(let ty (I64T))", "(let n0 (Num 7))"]
    output.extend(f"(let n{i} (Pair n{i - 1} n{i - 1}))" for i in range(1, 1501))
    output.extend(['(let fun (Function "main" ty ty n1500))', "(let PROG fun)"])
    facts, _ = eggcc_seed_query("\n".join(output), "reconstruction_")
    checks = "(check\n" + "\n".join(facts) + "\n)"
    suffix, terminal, plan = complete.eggcc_reconstruction_lookups(source, checks, roots)
    assert plan["requests"][0]["query_fact_count"] == 1504
    assert plan["requests"][0]["max_depth"] == 1502
    assert len([form for form in egglog_trees(suffix) if form[0] == "rule"]) == 1504
    assert len(egglog_trees(terminal)) == 1


def test_reconstruction_dag_preserves_repeated_output_requests_and_literal_aliases(
    reconstruction_lookup_inputs: tuple,
) -> None:
    source, _, _ = reconstruction_lookup_inputs
    program = "\n".join(
        [
            "(let ty (I64T))",
            "(let literal 7)",
            "(let alias literal)",
            "(let body (Num alias))",
            '(let function (Function "main" ty ty body))',
            "(let PROG function)",
        ]
    )
    facts, _ = eggcc_seed_query(program, "reconstruction_")
    check = "(check\n" + "\n".join(facts) + "\n)\n"
    roots = [{"name": "main", "output": 0}, {"name": "main", "output": 1}]
    suffix, terminal, plan = complete.eggcc_reconstruction_lookups(source, check + check, roots)
    assert len(egglog_trees(terminal)) == 2
    assert [r["query_fact_count"] for r in plan["requests"]] == [6, 6]
    assert sum(plan["expected_rows"].values()) == 10  # Literal is a body equality; aliases retain their own rows.
    rules = [form for form in egglog_trees(suffix) if form[0] == "rule"]
    aliases = [rule for rule in rules if rule[1][-1][1] == "reconstruction_seed2"]
    assert len(aliases) == 2
    assert all(
        rule[1] == [["=", "reconstruction_seed1", "7"], ["=", "reconstruction_seed2", "reconstruction_seed1"]]
        for rule in aliases
    )
    assert [rule[2][0][1][1] for rule in aliases] == ["0", "1"]
    with pytest.raises(CaptureError, match="every native output"):
        complete.eggcc_reconstruction_lookups(source, check, roots)
