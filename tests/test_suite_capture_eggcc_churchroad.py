"""Check mechanical compatibility edits for captured Churchroad invocations."""

import hashlib
import json
from pathlib import Path
from typing import Any, cast

import pytest

from scripts import eggcc_churchroad_complete as complete
from scripts import suite_capture_eggcc_churchroad as capture
from scripts.eggcc_churchroad_complete import (
    CaptureError,
    CaptureResourceError,
    churchroad_mapping_session,
    eggcc_sessions,
    read_events,
)
from scripts.hardboiled_replay import egglog_forms
from scripts.reproduction_process import PilotProcessResult
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
    adapted = capture.adapt_eggcc(prefix + EXPR_SET_BLOCK + suffix)
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
        capture.adapt_eggcc(source)


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
        capture.adapt_eggcc(source)


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


def event(sequence: int, kind: str, **payload: Any) -> dict[str, Any]:
    return {"version": 1, "sequence": sequence, "kind": kind, "payload": payload}


@pytest.fixture
def eggcc_source() -> str:
    return """(datatype Expr (Const i64) (Function String Expr Expr Expr))
(ruleset transform)
(rewrite (Const 1) (Const 2) :ruleset transform)
(ruleset initialization)
(rule () (
; Program nodes
(let __tmp0 (Const 1))
(let __tmp1 (Function "main" __tmp0 __tmp0 __tmp0))
; capture-root "main" __tmp1
; Loop context unions
) :ruleset initialization)
(run initialization 1)
(run-schedule (saturate transform))
"""


def test_eggcc_replays_each_completed_call_using_original_roots(eggcc_source: str) -> None:
    events = [event(i, "optimization-complete", program=eggcc_source, batch=["main"], **{"pass": i}) for i in range(2)]
    sessions = eggcc_sessions(events)
    assert len(sessions) == 2
    for session in sessions:
        replay = session["replay_program"]
        assert session["program"] == eggcc_source
        assert session["roots"] == [{"name": "main", "binding": "__tmp1", "table": "reproduction_root_0"}]
        assert session["extracts"] == "(extract (reproduction_root_0))"
        assert replay.count("(Function ") == eggcc_source.count("(Function ")
        assert (
            replay.replace("(function reproduction_root_0 () Expr :merge old)\n", "").replace(
                "(set (reproduction_root_0) __tmp1)\n", ""
            )
            == eggcc_source
        )
        assert session["kind"] == "optimization"
    # A parent marker does not create a reconstruction or setup workload.
    assert eggcc_sessions(events + [event(2, "parent-complete")]) == sessions


@pytest.mark.parametrize(
    "old,new,reason",
    [
        ('; capture-root "main" __tmp1', '; capture-root "other" __tmp1', "batch"),
        ('; capture-root "main" __tmp1', '; capture-root "main" __tmp0', "Function binding"),
        ('; capture-root "main" __tmp1', "", "batch"),
        ("(run initialization 1)", "(run initialization 2)", "exactly once"),
        ("(run-schedule (saturate transform))", "", "optimization schedule"),
        ("(run-schedule (saturate transform))", "(run initialization 1)", "exactly once"),
        ("__tmp1", "reproduction_root_0", "collides"),
    ],
)
def test_eggcc_rejects_changed_root_or_initialization_boundaries(
    eggcc_source: str, old: str, new: str, reason: str
) -> None:
    with pytest.raises(CaptureError, match=reason):
        eggcc_sessions(
            [event(0, "optimization-complete", program=eggcc_source.replace(old, new), batch=["main"], **{"pass": 0})]
        )


def test_materialization_retains_completed_eggcc_call_after_later_parent_failure(
    eggcc_source: str, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    native = tmp_path / "native-events"
    native.mkdir()
    (native / "event-000000.json").write_text(
        json.dumps(event(0, "optimization-complete", program=eggcc_source, batch=["main"], **{"pass": 0}))
    )
    # Atomic publication keeps an interrupted later write outside the event inventory.
    (native / "event-000001.json.pending").write_text('{"incomplete":')
    monkeypatch.setattr(capture, "adapt_eggcc", lambda source, **_: source)
    record = {"family": "eggcc", "process": {"status": "failure"}, "sessions": []}
    result = capture.materialize_complete_events(record, tmp_path)
    assert result["status"] == "ordinary-validation-pending", result
    assert result["source_completion"]["status"] == "complete"
    assert result["source_completion"]["parent_completed"] is False
    assert result["materialization"] == {"expected_sessions": 1, "materialized_sessions": 1, "complete": True}
    assert result["process"]["status"] == "failure"
    contract = result["sessions"][0]["output_contract"]
    assert contract["kind"] == "eggcc-root-extract"
    assert contract["claims_native_selection"] is contract["claims_effect_linearity"] is False


@pytest.fixture
def churchroad_events(monkeypatch: pytest.MonkeyPatch) -> list[dict[str, Any]]:
    enum = "(ruleset enumerate-modules)"
    monkeypatch.setattr(complete, "CHURCHROAD_MODULE_ENUM_SHA256", hashlib.sha256(enum.encode()).hexdigest())
    programs = [
        "(sort Expr)\n(function Wire (String i64) Expr)\n(function PrimitiveInterfaceDSP (Expr Expr) Expr)\n"
        "(function PrimitiveInterfaceDSP3 (Expr Expr Expr) Expr)\n(function Const (i64) Expr)\n"
        "(datatype Direction (Input) (Output))\n(relation IsPort (String String Direction Expr))\n"
        "(ruleset typing)\n(ruleset transform)\n(ruleset mapping)",
        enum,
        '(let v0 (Wire "out" 1))\n(IsPort "top" "out" (Output) v0)\n(let out v0)',
        '(rewrite (Wire "out" 1) (Const 1) :ruleset mapping)',
        "(run-schedule (saturate (seq typing transform mapping)))",
    ]
    events = []
    for index, program in enumerate(programs):
        events.append(
            event(
                2 * index,
                "commands",
                program=program,
                include_path="/src/module_enumeration_rewrites.egg" if index == 1 else None,
            )
        )
        events.append(event(2 * index + 1, "commands-result", success=True, output=""))
    events.append(event(10, "mapping-complete", outputs=["out"]))
    return events


def test_churchroad_keeps_persistent_mapping_and_extracts_original_port(
    churchroad_events: list[dict[str, Any]], tmp_path: Path
) -> None:
    session = churchroad_mapping_session(churchroad_events)
    assert len(session["parts"]) == 4
    assert "enumerate-modules" in session["program"]
    assert not any("enumerate-modules" in part for part in session["parts"])
    record: dict[str, Any] = {"family": "churchroad", "sessions": []}
    capture.materialize_sessions(record, [session], tmp_path)
    materialized = record["sessions"][0]
    replay = Path(materialized["replay"]).read_text()
    assert replay.count("(run-schedule") == 1
    assert replay.endswith("(extract $churchroad-global-out)\n")
    assert "(let $churchroad-global-out $churchroad-global-v0)" in replay
    assert replay.count(":unextractable") == 3
    assert materialized["output_contract"]["claims_native_selection"] is False
    assert record["materialization"]["complete"] is True


@pytest.mark.parametrize("fault", ["incomplete", "failed-call", "wrong-schedule", "active-enumeration", "missing-root"])
def test_churchroad_rejects_partial_or_changed_mapping(churchroad_events: list[dict[str, Any]], fault: str) -> None:
    if fault == "incomplete":
        churchroad_events.pop()
    elif fault == "failed-call":
        churchroad_events[5]["payload"]["success"] = False
    elif fault == "wrong-schedule":
        churchroad_events[8]["payload"]["program"] = "(run mapping 1)"
    elif fault == "active-enumeration":
        churchroad_events[6]["payload"]["program"] += "\n(run enumerate-modules 1)"
    else:
        churchroad_events[4]["payload"]["program"] = '(IsPort "top" "out" (Output) v0)'
    with pytest.raises(CaptureError):
        churchroad_mapping_session(churchroad_events)


def test_native_events_require_bounded_contiguous_complete_json(tmp_path: Path) -> None:
    path = tmp_path / "event-000000.json"
    path.write_text(json.dumps(event(0, "optimization-complete")))
    assert len(read_events(tmp_path)) == 1
    with pytest.raises(CaptureResourceError):
        read_events(tmp_path, max_bytes=1)
    path.write_text(json.dumps(event(1, "optimization-complete")))
    with pytest.raises(CaptureError, match="contiguous"):
        read_events(tmp_path)
    path.write_text('{"partial":')
    with pytest.raises(CaptureError, match="incomplete"):
        read_events(tmp_path)


@pytest.mark.parametrize(
    "parent_status,completed,materialization_status",
    [
        ("success", True, "success"),
        ("failure", True, "success"),
        ("timed-out", True, "success"),
        ("timed-out", False, "success"),
        ("resource-stopped", True, "success"),
        ("memory-limit", True, "success"),
        ("cancelled", True, "success"),
        ("interrupted", True, "success"),
        ("timed-out", True, "resource-stopped"),
        ("timed-out", True, "memory-limit"),
        ("timed-out", True, "cancelled"),
        ("timed-out", True, "interrupted"),
    ],
)
def test_capture_complete_retains_calls_after_timeout_but_halts_on_safety_or_cancellation(
    eggcc_source: str,
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    parent_status: str,
    completed: bool,
    materialization_status: str,
) -> None:
    for name in ("first", "second", "engine", "compiler"):
        (tmp_path / name).write_text("fixture identity")
    launches: list[str] = []

    def run(command: list[str], _cwd: Path, prefix: Path, **options: Any) -> PilotProcessResult:
        assert options == {"timeout_sec": 7, "require_guard": True}
        launches.append(prefix.name)
        stdout, stderr = prefix.with_suffix(".stdout"), prefix.with_suffix(".stderr")
        stdout.write_text("")
        stderr.write_text("retained native diagnostics")
        if prefix.name == "native":
            if completed:
                (prefix.parent / "native-events/event-000000.json").write_text(
                    json.dumps(event(0, "optimization-complete", program=eggcc_source, batch=["main"], **{"pass": 0}))
                )
            status = parent_status
        else:
            assert prefix.name == "materialize"
            if materialization_status == "success":
                request = Path(command[-1])
                record = capture.materialize_complete_events(json.loads(request.read_text()), request.parent)
                (request.parent / "materialized.json").write_text(json.dumps(record))
            status = materialization_status
        # Include cancellation statuses understood by the capture coordinator.
        return PilotProcessResult(
            cast(Any, status), 0 if status == "success" else 1, 0.1, 1024, stdout, stderr, "parent outcome"
        )

    monkeypatch.setattr(capture, "run_bounded_command", run)
    monkeypatch.setattr(capture, "adapt_eggcc", lambda source: source)
    records = capture.capture_complete(
        "eggcc",
        [{"id": name, "source": name} for name in ("first", "second")],
        tmp_path / "captures",
        tmp_path,
        tmp_path / "compiler",
        tmp_path / "engine",
        timeout_sec=7,
    )
    parent_halted = parent_status in {"resource-stopped", "memory-limit", "cancelled", "interrupted"}
    halted = parent_halted or materialization_status != "success"
    assert launches == (["native"] if parent_halted else ["native", "materialize"] * (1 if halted else 2))
    assert len(records) == (1 if halted else 2)
    for record in records:
        assert record["process"]["status"] == parent_status
        assert record["process"]["message"] == "parent outcome"
        assert record["status"] == (
            parent_status
            if parent_halted
            else materialization_status
            if halted
            else "ordinary-validation-pending"
            if completed
            else "blocked"
        )
        assert len(record["sessions"]) == (0 if halted or not completed else 1)
        if completed and not halted:
            assert record["source_completion"]["status"] == "complete"
            assert record["source_completion"]["parent_completed"] is False
        assert json.loads((tmp_path / "captures" / record["id"] / "capture.json").read_text()) == json.loads(
            json.dumps(record, default=str)
        )
