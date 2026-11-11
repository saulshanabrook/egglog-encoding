"""Check mechanical compatibility edits for captured Churchroad invocations."""

import copy
import hashlib
import json
from pathlib import Path

import pytest

from benchmarking.pilot import PilotProcessResult
from scripts import eggcc_churchroad_complete as complete
from scripts import suite_capture_eggcc_churchroad as capture
from scripts.eggcc_churchroad_complete import (
    CaptureError,
    WitnessQuery,
    churchroad_selection_check,
    churchroad_sessions,
    eggcc_output_checks,
    eggcc_seed_query,
    eggcc_sessions,
    read_events,
    tiger_selections,
)
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


@pytest.mark.parametrize("parent_status", ["success", "failure", "memory-limit"])
def test_complete_adapter_admits_only_full_parent_and_checked_sessions(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    native_eggcc: tuple,
    parent_status: str,
) -> None:
    *_, events = native_eggcc
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
            status = parent_status
        else:
            program = Path(command[-1]).read_text()
            assert "(check" in program
        return PilotProcessResult(status, 0 if status == "success" else 1, 0.01, 0, stdout, stderr, None)  # type: ignore[arg-type]

    monkeypatch.setattr(capture, "run_bounded_command", run)
    monkeypatch.setattr(capture, "adapt_eggcc", lambda source, **_: source)
    records = capture.capture_complete(
        "eggcc",
        [{"id": "case", "source": "source.bril"}],
        tmp_path / "attempt",
        checkout,
        binary,
        engine,
    )
    record = records[0]
    assert record["status"] == ("reproduced" if parent_status == "success" else "blocked")
    assert len(called) == (3 if parent_status == "success" else 1)
    assert all(
        options["require_guard"] is True and options["disk_reserve_bytes"] == 10 * 1024**3 for _, options in called
    )
    if parent_status == "success":
        assert len(record["workloads"]) == 2
        assert len(record["source_completion"]["outputs"]) == 3
        assert all(session["output_contract"]["roots"] for session in record["sessions"])
    else:
        assert not record["workloads"] and not record["source_completion"]["parent_completed"]
    assert len(record["raw_invocations"]) == 2
