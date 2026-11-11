"""Complete source and exact native outputs are independent admission gates."""

from __future__ import annotations

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
    assert validation.validate_capture(capture, engine, tmp_path / "present")["status"] == "success"


@pytest.mark.parametrize("stop", ["timed-out", "resource-stopped", "memory-limit"])
def test_nested_safety_stop_cannot_be_hidden_by_parent_status(stop: str) -> None:
    assert capture_outcome({"status": "blocked", "sessions": [{"validation": {"status": stop}}]}) == stop


def test_reproduced_requires_successful_source_completion() -> None:
    with pytest.raises(ValueError, match="successful source"):
        capture_outcome(
            {"status": "reproduced", "workloads": ["prefix.egg"], "source_completion": {"status": "failed"}}
        )
