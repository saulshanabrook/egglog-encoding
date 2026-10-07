"""Complete source and exact native outputs are independent admission gates."""

from __future__ import annotations

import copy
from pathlib import Path
from typing import Any

import pytest

from benchmarking.targets import sha256_file
from scripts import reproduction_validation as validation
from scripts.hardboiled_replay import egglog_forms
from scripts.reproduction_process import PilotProcessResult


@pytest.fixture
def example(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> tuple[dict[str, Any], Path, list[list[str]]]:
    engine = tmp_path / "engine"
    engine.write_text("test executable identity")
    replay = tmp_path / "replay.egg"
    replay.write_text("(datatype E (A) (B))\n(let $root (A))\n(extract $root)\n")
    capture: dict[str, Any] = {
        "status": "reproduced",
        "source_completion": {"status": "complete"},
        "materialization": {"complete": True, "expected_sessions": 1, "materialized_sessions": 1},
        "invocations": [
            {
                "replay": str(replay),
                "replay_sha256": sha256_file(replay),
                "output_contract": {"kind": "ordinary-best-extract", "expected_terms": [egglog_forms("(A)")[0][2]]},
            }
        ],
        "workloads": [str(replay)],
    }
    launches: list[list[str]] = []

    def run(command: list[str], cwd: Path, prefix: Path, timeout_sec: float) -> PilotProcessResult:
        launches.append(command)
        stdout, stderr = prefix.with_suffix(".stdout"), prefix.with_suffix(".stderr")
        stdout.write_text("(A)\n")
        stderr.write_text("")
        return PilotProcessResult("success", 0, 0.01, 1024, stdout, stderr, None)

    monkeypatch.setattr(validation, "run_complete_command", run)
    return capture, engine, launches


def test_all_native_output_terms_must_match(example: tuple, tmp_path: Path) -> None:
    capture, engine, launches = example
    assert validation.validate_capture(capture, engine, tmp_path / "ok")["status"] == "success"
    capture["invocations"][0]["output_contract"]["expected_terms"] = [egglog_forms("(B)")[0][2]]
    failure = validation.validate_capture(capture, engine, tmp_path / "wrong")
    assert failure["status"] == "blocked"
    assert "differs" in failure["reason"]
    assert not failure["workloads"]
    assert len(launches) == 2


@pytest.mark.parametrize("terminal_status", ["failure", "output-limit"])
def test_resume_reuses_completed_diagnostics_and_retries_interrupted_and_unattempted_calls(
    example: tuple, tmp_path: Path, monkeypatch: pytest.MonkeyPatch, terminal_status: str
) -> None:
    capture, engine, launches = example
    first = capture["invocations"][0]
    capture["invocations"] = []
    for index in range(4):
        replay = tmp_path / f"input-{index}.egg"
        replay.write_text(Path(first["replay"]).read_text() + f"; call {index}\n")
        capture["invocations"].append({**first, "replay": str(replay), "replay_sha256": sha256_file(replay)})
    capture["materialization"].update(expected_sessions=4, materialized_sessions=4)
    statuses = iter(["success", terminal_status, "memory-limit", "success", "success"])
    reason = "ordinary extraction failed" if terminal_status == "failure" else "diagnostic output exceeded limit"

    def run(command: list[str], cwd: Path, prefix: Path, timeout_sec: float) -> PilotProcessResult:
        launches.append(command)
        stdout, stderr = prefix.with_suffix(".stdout"), prefix.with_suffix(".stderr")
        stdout.write_text("(A)\n")
        stderr.write_text("")
        status = next(statuses)
        return PilotProcessResult(
            status,  # type: ignore[arg-type]
            0,
            0.01,
            1024,
            stdout,
            stderr,
            reason if status == terminal_status else None,
        )

    monkeypatch.setattr(validation, "run_complete_command", run)
    interrupted = validation.validate_capture(capture, engine, tmp_path / "interrupted")
    assert interrupted["status"] == "memory-limit" and len(launches) == 3
    resumed = validation.validate_capture(capture, engine, tmp_path / "resumed", previous=interrupted)
    assert len(launches) == 5
    assert [Path(command[-1]).name for command in launches] == [
        "input-0.egg",
        "input-1.egg",
        "input-2.egg",
        "input-2.egg",
        "input-3.egg",
    ]
    assert resumed["status"] == terminal_status and resumed["reason"] == reason
    assert len(resumed["workloads"]) == 3
    assert resumed["validations"][1] == interrupted["validations"][1]


@pytest.mark.parametrize("changed", ["engine", "replay", "contract", "timeout", "validator", "stdout"])
def test_resume_requires_exact_validation_and_output_identities(example: tuple, tmp_path: Path, changed: str) -> None:
    capture, engine, launches = example
    previous = validation.validate_capture(capture, engine, tmp_path / "first")
    timeout = 300
    if changed == "engine":
        engine.write_text("new binary")
    elif changed == "replay":
        replay = Path(capture["invocations"][0]["replay"])
        replay.write_text(replay.read_text() + "; changed input\n")
        capture["invocations"][0]["replay_sha256"] = sha256_file(replay)
    elif changed == "contract":
        capture["invocations"][0]["output_contract"]["expected_terms"] = [egglog_forms("(B)")[0][2]]
    elif changed == "timeout":
        timeout = 301
    elif changed == "validator":
        previous["validations"][0]["identity"]["validation_sha256"] = "old validator"
    else:
        Path(previous["validations"][0]["stdout_path"]).write_text("modified evidence")
    validation.validate_capture(capture, engine, tmp_path / "second", timeout_sec=timeout, previous=previous)
    assert len(launches) == 2


EGGCC_SOURCE = """(datatype Type (UnitT))
(datatype Expr (A) (Function String Type Type Expr))
(ruleset init)
(function reproduction_root_0 () Expr :merge old)
(rule () ((let name "main") (let t (UnitT)) (let body (A))
          (let original (Function name t t body))
          (set (reproduction_root_0) original)) :ruleset init)
(run init 1)
(run 1)
(extract (reproduction_root_0))
"""
EGGCC_ROOTS = [{"name": "main", "binding": "original", "table": "reproduction_root_0"}]


def test_eggcc_extract_uses_original_value_without_native_selection_claim(example: tuple, tmp_path: Path) -> None:
    capture, engine, _ = example
    session = capture["invocations"][0]
    replay = Path(session["replay"])
    replay.write_text(EGGCC_SOURCE)
    contract = validation.eggcc_root_contract(EGGCC_SOURCE, EGGCC_ROOTS)
    assert contract["claims_native_selection"] is False and contract["claims_effect_linearity"] is False
    session.update(replay_sha256=sha256_file(replay), output_contract=contract)
    checked = validation.validate_capture(capture, engine, tmp_path / "eggcc")
    assert checked["status"] == "success" and checked["workloads"] == [str(replay)]


@pytest.mark.parametrize(
    ("old", "new"),
    [
        ('(let name "main")', '(let name "different")'),
        ("(set (reproduction_root_0) original)", "(set (reproduction_root_0) body)"),
        ("(set (reproduction_root_0) original)", "(set (reproduction_root_0) (Function name t t body))"),
        ("(rule ()", "(rule ((= body (A)))"),
        ("(extract (reproduction_root_0))", "(extract (A))"),
        ("(extract (reproduction_root_0))", ""),
    ],
)
def test_eggcc_contract_rejects_new_assumptions_and_changed_roots(old: str, new: str) -> None:
    with pytest.raises(ValueError, match="Eggcc"):
        validation.eggcc_root_contract(EGGCC_SOURCE.replace(old, new), EGGCC_ROOTS)


def test_eggcc_contract_binds_schedule_and_extraction_boundary(example: tuple, tmp_path: Path) -> None:
    capture, engine, launches = example
    session = capture["invocations"][0]
    replay = Path(session["replay"])
    contract = validation.eggcc_root_contract(EGGCC_SOURCE, EGGCC_ROOTS)
    replay.write_text(EGGCC_SOURCE.replace("(run 1)", "(run 2)"))
    session.update(replay_sha256=sha256_file(replay), output_contract=contract)
    result = validation.validate_capture(capture, engine, tmp_path / "changed-eggcc")
    assert result["status"] == "blocked" and not launches


@pytest.fixture
def circuit_example(
    example: tuple, monkeypatch: pytest.MonkeyPatch
) -> tuple[dict[str, Any], Path, list[list[str]], list[str]]:
    capture, engine, launches = example
    session = capture["invocations"][0]
    source = (
        "(datatype E (A) (B))\n"
        "(constructor Wire (String i64) E :unextractable)\n"
        "(constructor PrimitiveInterfaceDSP (E E) E :unextractable)\n"
        "(constructor PrimitiveInterfaceDSP3 (E E E) E :unextractable)\n"
        "(datatype Direction (Output))\n(relation IsPort (String String Direction E))\n"
        '(let $a (A))\n(IsPort "mul" "out" (Output) $a)\n(let $out $a)\n'
        '(let $b (B))\n(IsPort "mul" "other" (Output) $b)\n(let $other $b)\n'
        "(ruleset mapping)\n(run-schedule (saturate mapping))\n(extract $out)\n(extract $other)\n"
    )
    roots = [{"module": "mul", "name": name, "replay_alias": f"${name}"} for name in ("out", "other")]
    replay = Path(session["replay"])
    replay.write_text(source)
    session.update(
        replay_sha256=sha256_file(replay), output_contract=validation.churchroad_circuit_contract(source, roots)
    )
    outputs = ["(A)\n(B)\n"]

    def run(command: list[str], cwd: Path, prefix: Path, timeout_sec: float) -> PilotProcessResult:
        launches.append(command)
        stdout, stderr = prefix.with_suffix(".stdout"), prefix.with_suffix(".stderr")
        stdout.write_text(outputs[0])
        stderr.write_text("")
        return PilotProcessResult("success", 0, 0.01, 1024, stdout, stderr, None)

    monkeypatch.setattr(validation, "run_complete_command", run)
    return capture, engine, launches, outputs


def test_circuit_extraction_accepts_unchanged_outputs_without_expected_terms(
    circuit_example: tuple, tmp_path: Path
) -> None:
    capture, engine, launches, _ = circuit_example
    contract = capture["invocations"][0]["output_contract"]
    assert "expected_terms" not in contract
    assert contract["claims_native_selection"] is False and contract["claims_optimality"] is False
    result = validation.validate_capture(capture, engine, tmp_path / "circuits")
    assert result["status"] == "success" and len(launches) == 1
    circuits = result["validations"][0]["extracted_circuits"]
    assert [item["root"]["name"] for item in circuits] == ["out", "other"]
    assert [item["term"] for item in circuits] == [["(", "A", ")"], ["(", "B", ")"]]


def test_circuit_contract_cannot_drop_an_output_even_with_a_new_contract(circuit_example: tuple) -> None:
    capture, _, _, _ = circuit_example
    session = capture["invocations"][0]
    source = Path(session["replay"]).read_text().replace("(extract $other)", "")
    with pytest.raises(ValueError, match="every original output port"):
        validation.churchroad_circuit_contract(source, session["output_contract"]["roots"][:1])


@pytest.mark.parametrize("change", ["missing", "swap", "move", "state", "policy", "alias", "port", "check", "proof"])
def test_circuit_extraction_contract_binds_all_outputs_and_prior_state(
    circuit_example: tuple, tmp_path: Path, change: str
) -> None:
    capture, engine, launches, _ = circuit_example
    session = capture["invocations"][0]
    replay = Path(session["replay"])
    source = replay.read_text()
    if change == "missing":
        source = source.replace("(extract $other)", "")
    elif change == "swap":
        source = source.replace("(extract $out)\n(extract $other)", "(extract $other)\n(extract $out)")
    elif change == "move":
        source = source.replace("(extract $out)", "(extract $out)\n(union $a $b)")
    elif change == "state":
        source = source.replace("(let $a (A))", "(let $a (B))")
    elif change == "policy":
        source = source.replace(" :unextractable", "", 1)
    elif change == "alias":
        source = source.replace("(let $out $a)", "(let $out $b)")
    elif change == "port":
        source = source.replace('"out" (Output)', '"out" (Input)')
    elif change == "check":
        source = source.replace("(extract $out)", "(check (= $out (A)))\n(extract $out)")
    else:
        source = source.replace("(extract $out)", "(prove-extract $out)")
    replay.write_text(source)
    session["replay_sha256"] = sha256_file(replay)
    result = validation.validate_capture(capture, engine, tmp_path / "changed")
    assert result["status"] == "blocked" and not result["workloads"]
    assert not launches


@pytest.mark.parametrize(
    "output",
    [
        "(A)",
        '(Wire "out" 32)\n(B)',
        '(Op2 (Mul) (A) (Wire "hidden" 32))\n(B)',
        "(PrimitiveInterfaceDSP (A) (A))\n(B)",
        "(PrimitiveInterfaceDSP3 (A) (A) (A))\n(B)",
        "(A)\n(extract $other)",
    ],
)
def test_circuit_extraction_rejects_missing_outputs_and_nested_placeholders(
    circuit_example: tuple, tmp_path: Path, output: str
) -> None:
    capture, engine, launches, outputs = circuit_example
    outputs[0] = output
    result = validation.validate_capture(capture, engine, tmp_path / "invalid-output")
    assert result["status"] == "blocked" and not result["workloads"]
    assert len(launches) == 1


def test_changed_input_and_failed_parent_do_not_launch(example: tuple, tmp_path: Path) -> None:
    capture, engine, launches = example
    capture["source_completion"]["status"] = "failed"
    assert validation.validate_capture(capture, engine, tmp_path / "parent")["status"] == "blocked"
    capture["source_completion"]["status"] = "complete"
    Path(capture["invocations"][0]["replay"]).write_text("(extract (B))")
    failure = validation.validate_capture(capture, engine, tmp_path / "changed")
    assert "identity changed" in failure["reason"]
    assert not launches


def test_custom_selection_requires_its_query_and_all_outputs(example: tuple, tmp_path: Path) -> None:
    capture, engine, launches = example
    session = capture["invocations"][0]
    session.pop("output_contract")
    session.update(root_count=1, selections=[{"check": "(check (= $root (B)))"}])
    assert validation.validate_capture(capture, engine, tmp_path / "missing")["status"] == "blocked"
    assert not launches
    # Existing proof/query semantics, not this Python gate, decide whether the
    # selected B actually equals root. The test double only covers gate routing.
    replay = Path(session["replay"])
    replay.write_text(replay.read_text() + "(check (= $root (B)))\n")
    session["replay_sha256"] = sha256_file(replay)
    session["output_contract"] = validation.native_check_contract(
        replay.read_text(), [(3, session["selections"][0]["check"])], session["selections"]
    )
    assert validation.validate_capture(capture, engine, tmp_path / "present")["status"] == "success"


@pytest.mark.parametrize("status", ["blocked", "failure", "running"])
def test_completed_parent_with_partial_materialization_cannot_be_promoted(
    example: tuple, tmp_path: Path, status: str
) -> None:
    capture, engine, launches = example
    capture["status"] = status
    # A valid first session remains diagnostic even if it passes in isolation.
    capture["materialization"] = {"complete": False, "expected_sessions": 2, "materialized_sessions": 1}
    result = validation.validate_capture(capture, engine, tmp_path / "prefix")
    assert result["status"] == "blocked"
    assert "blocked or incomplete" in result["reason"]
    assert not launches and not result["workloads"]


@pytest.mark.parametrize(
    "marker",
    [
        None,
        {"complete": False},
        {
            "complete": True,
            "expected_sessions": 2,
            "materialized_sessions": 1,
        },
    ],
)
def test_terminal_materialization_marker_and_full_session_count_are_required(
    example: tuple, tmp_path: Path, marker: dict | None
) -> None:
    capture, engine, launches = example
    capture["status"] = "ordinary-validation-pending"
    capture["materialization"] = marker or {}
    result = validation.validate_capture(capture, engine, tmp_path / "incomplete")
    assert result["status"] == "blocked" and "every native session" in result["reason"]
    assert not launches


def test_complete_materialization_can_retry_failed_ordinary_validation(example: tuple, tmp_path: Path) -> None:
    capture, engine, launches = example
    capture["status"] = "ordinary-validation-failed"
    result = validation.validate_capture(capture, engine, tmp_path / "retry")
    assert result["status"] == "success" and len(launches) == 1


@pytest.mark.parametrize("change", ["hash", "missing", "reorder", "move", "state"])
def test_custom_native_checks_are_exact_ordered_and_bound_to_graph_state(
    example: tuple, tmp_path: Path, change: str
) -> None:
    capture, engine, launches = example
    session = capture["invocations"][0]
    replay = Path(session["replay"])
    source = "(datatype E (A) (B))\n(let $a (A))\n(let $b (B))\n(check (= $a (A)))\n(check (= $b (B)))\n"
    contract = validation.native_check_contract(
        source,
        [(3, "(check (= $a (A)))"), (4, "(check (= $b (B)))")],
        [{"name": "a"}, {"name": "b"}],
    )
    if change == "hash":
        contract["check_sha256"] = "wrong"
    elif change == "missing":
        source = source.replace("(check (= $b (B)))", "(check (= $a $a))")
    elif change == "reorder":
        contract["checks"].reverse()
    elif change == "move":
        source = source.replace("(check (= $a (A)))", "(union $a $b)\n(check (= $a (A)))")
    else:
        source = source.replace("(let $b (B))", "(let $b (A))")
    replay.write_text(source)
    session.update(replay_sha256=sha256_file(replay), output_contract=contract)
    result = validation.validate_capture(capture, engine, tmp_path / "changed-contract")
    assert result["status"] == "blocked", result
    assert not launches and not result["workloads"]


def test_equal_checks_at_distinct_boundaries_are_not_deduplicated() -> None:
    check = "(check (= $a (A)))"
    source = f"(let $a (A))\n{check}\n(run 1)\n{check}"
    contract = validation.native_check_contract(source, [(1, check), (3, check)], [{"name": "a"}] * 2)
    assert [record["command"] for record in contract["checks"]] == [1, 3]
    assert contract["checks"][0]["prefix_sha256"] != contract["checks"][1]["prefix_sha256"]


def test_native_selection_contract_cannot_skip_one_requested_root(example: tuple, tmp_path: Path) -> None:
    capture, engine, launches = example
    session = capture["invocations"][0]
    replay = Path(session["replay"])
    source = replay.read_text() + "(check (= $root (A)))\n(extract $root)\n"
    replay.write_text(source)
    selections = [{"check": "(check (= $root (A)))"}] * 2
    session.update(
        root_count=2,
        selections=selections,
        replay_sha256=sha256_file(replay),
        output_contract=validation.native_check_contract(source, [(3, selections[0]["check"])], selections),
    )
    result = validation.validate_capture(copy.deepcopy(capture), engine, tmp_path / "missing-root")
    assert result["status"] == "blocked" and not launches


STATIC_SOURCE = """(datatype E (Value i64) (Add E E :cost 10))
(let $a (Value 1))
(let $b (Value 2))
(let $root (Add $a $b))
(rewrite (Add a b) (Add b a))
(run 2)
(extract $root 0)
"""
NATIVE_TERM = "(Add (Value 2) (Value 1))"
REPLAY_TERM = "(Add (Value 1) (Value 2))"


def test_static_tie_queries_preserve_every_original_command_and_request() -> None:
    # Repeated roots at different states must retain distinct checks, not be deduplicated.
    original = STATIC_SOURCE + "(run 1)\n(extract $root)\n"
    terms = [egglog_forms(NATIVE_TERM)[0][2]] * 2
    source, contract = validation.materialize_static_native_contract(original, terms, [14, 14])
    retained = [tokens for _, _, tokens in egglog_forms(source) if tokens[1] != "check"]
    assert retained == [tokens for _, _, tokens in egglog_forms(original)]
    assert [root["extract_request"][-2] for root in contract["membership"]["roots"]] == ["0", "$root"]
    assert len(contract["membership"]["checks"]) == 2
    assert contract["cost_model"]["constructors"]["Add"] == {"inputs": ["E", "E"], "output": "E", "cost": 10}
    observed = validation.validate_static_native_output(
        source,
        contract,
        REPLAY_TERM + "\n" + NATIVE_TERM,
        "Best cost for the extract root: 14\nBest cost for the extract root: 14\n",
    )
    assert observed == {"native_costs": [14, 14], "replay_costs": [14, 14], "exact_terms": False}


@pytest.mark.parametrize(
    "stderr", ["", "Best cost for the extract root: 13", "Best cost for the extract root: 14\n" * 2]
)
def test_static_tie_requires_all_numeric_replay_cost_logs(stderr: str) -> None:
    source, contract = validation.materialize_static_native_contract(
        STATIC_SOURCE, [egglog_forms(NATIVE_TERM)[0][2]], [14]
    )
    with pytest.raises(ValueError, match="cost logs"):
        validation.validate_static_native_output(source, contract, REPLAY_TERM, stderr)


@pytest.mark.parametrize(
    "change",
    [
        lambda source: source.replace(":cost 10", ":cost 11"),
        lambda source: source.replace("(run 2)", "(run 2)\n(unstable-cost (Add $a $b) 1)"),
        lambda source: source.replace("(run 2)", "(run 2)\n(set-cost (Add $a $b) 1)"),
        lambda source: "(push 1)\n" + source,
        lambda source: source.replace("$root 0)", "$root 2)"),
        lambda source: source.replace(":cost 10", ":cost -1"),
    ],
)
def test_unsupported_or_changed_costs_and_variants_never_get_tie_exemption(change: Any) -> None:
    with pytest.raises(ValueError):
        validation.materialize_static_native_contract(change(STATIC_SOURCE), [egglog_forms(NATIVE_TERM)[0][2]], [14])


@pytest.mark.parametrize("term", ['(Add (Value "wrong-sort") (Value 1))', "(Add (vec-of (Value 1)) (Value 2))"])
def test_static_output_cost_is_typed_and_rejects_containers(term: str) -> None:
    with pytest.raises(ValueError, match="primitive|container"):
        validation.static_extract_model(STATIC_SOURCE, [egglog_forms(term)[0][2]])


def test_static_contract_admission_uses_query_failure_not_term_rewriting(
    example: tuple, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    capture, engine, _ = example
    session = capture["invocations"][0]
    replay = Path(session["replay"])
    # Same static cost as the native term, but Value 999 was never inserted.
    fabricated = NATIVE_TERM.replace("Value 2", "Value 999")
    source, contract = validation.materialize_static_native_contract(
        STATIC_SOURCE, [egglog_forms(fabricated)[0][2]], [14]
    )
    replay.write_text(source)
    session.update(replay_sha256=sha256_file(replay), output_contract=contract)
    assert sum("999" in tokens for _, _, tokens in egglog_forms(source)) == 1
    assert "999" not in STATIC_SOURCE

    def run(command: list[str], cwd: Path, prefix: Path, timeout: float) -> PilotProcessResult:
        assert command[:2] == ["env", "RUST_LOG=egglog::extract=debug"]
        out, err = prefix.with_suffix(".stdout"), prefix.with_suffix(".stderr")
        out.write_text("")
        err.write_text("Check failed")
        return PilotProcessResult("failure", 1, 0.0, 0, out, err, "Check failed")

    monkeypatch.setattr(validation, "run_complete_command", run)
    result = validation.validate_capture(capture, engine, tmp_path / "negative")
    assert result["status"] == "failure" and not result["workloads"]
    assert result["reason"] == "Check failed"


def test_static_contract_cannot_move_native_check_past_an_action(example: tuple, tmp_path: Path) -> None:
    capture, engine, launches = example
    session = capture["invocations"][0]
    source, contract = validation.materialize_static_native_contract(
        STATIC_SOURCE, [egglog_forms(NATIVE_TERM)[0][2]], [14]
    )
    source = source.replace("(extract $root 0)", "(run 1)\n(extract $root 0)")
    replay = Path(session["replay"])
    replay.write_text(source)
    session.update(replay_sha256=sha256_file(replay), output_contract=contract)
    result = validation.validate_capture(capture, engine, tmp_path / "moved")
    assert result["status"] == "blocked" and not launches


def test_static_model_binds_unselected_competing_constructor_costs() -> None:
    source = "(datatype E (A :cost 1) (B :cost 2))\n(let $root (A))\n(union $root (B))\n(extract $root)"
    terms = [egglog_forms("(A)")[0][2]]
    changed = source.replace("B :cost 2", "B :cost 1")
    assert validation.static_extract_model(source, terms) != validation.static_extract_model(changed, terms)
    materialized, contract = validation.materialize_static_native_contract(source, terms, [1])
    with pytest.raises(ValueError, match="contract"):
        validation.validate_static_native_output(
            materialized.replace("B :cost 2", "B :cost 1"), contract, "(B)", "Best cost for the extract root: 1"
        )


@pytest.mark.parametrize("failed_index", [0, 1])
def test_independent_successes_survive_another_calls_output_failure(
    example: tuple, tmp_path: Path, failed_index: int
) -> None:
    capture, engine, launches = example
    original = capture["invocations"][0]
    other = copy.deepcopy(original)
    other_path = tmp_path / "other.egg"
    other_path.write_text(Path(original["replay"]).read_text())
    other.update(replay=str(other_path), replay_sha256=sha256_file(other_path))
    capture["invocations"].append(other)
    capture["materialization"].update(expected_sessions=2, materialized_sessions=2)
    capture["invocations"][failed_index]["output_contract"]["expected_terms"] = [egglog_forms("(B)")[0][2]]
    result = validation.validate_capture(capture, engine, tmp_path / "checked")
    assert result["status"] == "blocked" and "differs" in result["reason"]
    assert result["workloads"] == [capture["invocations"][1 - failed_index]["replay"]]
    assert len(launches) == 2
