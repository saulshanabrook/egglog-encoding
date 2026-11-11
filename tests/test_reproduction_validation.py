"""Complete source and exact native outputs are independent admission gates."""

from __future__ import annotations

import copy
from pathlib import Path
from typing import Any

import pytest

from benchmarking.pilot import PilotProcessResult
from benchmarking.targets import sha256_file
from scripts import reproduction_validation as validation
from scripts.hardboiled_replay import egglog_forms
from scripts.suite_reproduction import capture_outcome


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


@pytest.mark.parametrize("stop", ["timed-out", "resource-stopped", "memory-limit"])
def test_nested_safety_stop_cannot_be_hidden_by_parent_status(stop: str) -> None:
    assert capture_outcome({"status": "blocked", "sessions": [{"validation": {"status": stop}}]}) == stop


def test_reproduced_requires_successful_source_completion() -> None:
    with pytest.raises(ValueError, match="successful source"):
        capture_outcome(
            {"status": "reproduced", "workloads": ["prefix.egg"], "source_completion": {"status": "failed"}}
        )
