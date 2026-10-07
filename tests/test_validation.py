"""Strict checks record identity-bound outcomes without measured samples."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest

from benchmarking import suites
from scripts import reproduction_process as processes
from scripts import validate_benchmarks as validation

from .corpus_fixtures import prepare_corpus


@pytest.mark.parametrize("status", ["success", "failure", "timed-out", "resource-stopped", "memory-limit"])
def test_strict_outcomes_are_separate_and_safety_stops_halt_before_next_workload(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    status: str,
) -> None:
    path = prepare_corpus(tmp_path, contents=("(check (= 1 1))\n", "(check (= 2 2))\n"))
    binary = tmp_path / "engine"
    binary.write_bytes(b"engine")
    monkeypatch.setattr(validation, "__file__", str(tmp_path / "scripts/validate_benchmarks.py"))
    commands: list[list[str]] = []

    def run(command: list[str], cwd: Path, prefix: Path, **kwargs: Any) -> processes.PilotProcessResult:
        commands.append(command)
        assert kwargs == {"timeout_sec": 300, "require_guard": True}
        return processes.PilotProcessResult(status, 0, 0.5, 100, prefix, prefix, "diagnostic result")  # type: ignore[arg-type]

    monkeypatch.setattr(validation, "run_bounded_command", run)
    code = validation.main(["--binary", str(binary), "--disequality-encoding", "ee"])
    assert code == (0 if status == "success" else 1)
    safety = status in ("resource-stopped", "memory-limit")
    assert len(commands) == (1 if safety else 2)
    assert all("--proof-testing" in command and "--disequality-encoding" in command for command in commands)
    outcomes = json.loads(path.read_text())["outcomes"]
    assert len(outcomes) == len(commands)
    assert outcomes[0]["kind"] == ("safety" if safety else "validation")
    assert outcomes[0]["disequality_encoding"] == "ee"
    assert not list(tmp_path.rglob("*.jsonl"))
    if status == "success":
        assert outcomes[0]["reason"] is None


def test_preflight_safety_refusal_is_retained_without_fabricating_measurement(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    path = prepare_corpus(tmp_path)
    binary = tmp_path / "engine"
    binary.write_bytes(b"engine")
    monkeypatch.setattr(validation, "__file__", str(tmp_path / "scripts/validate_benchmarks.py"))

    def refuse(*args: Any, **kwargs: Any) -> Any:
        raise ValueError("resource guard refused to launch a workload: host pressure")

    monkeypatch.setattr(validation, "run_bounded_command", refuse)
    assert validation.main(["--binary", str(binary)]) == 1
    outcome = json.loads(path.read_text())["outcomes"][0]
    assert outcome["kind"] == "safety" and outcome["status"] == "deferred"
    assert "host pressure" in outcome["reason"]
    assert not list(tmp_path.rglob("*.jsonl"))


def test_mutation_during_validation_cannot_record_success(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    path = prepare_corpus(tmp_path)
    binary = tmp_path / "engine"
    binary.write_bytes(b"engine")
    monkeypatch.setattr(validation, "__file__", str(tmp_path / "scripts/validate_benchmarks.py"))

    def run(command: list[str], cwd: Path, prefix: Path, **kwargs: Any) -> processes.PilotProcessResult:
        Path(command[-1]).write_text("changed")
        return processes.PilotProcessResult("success", 0, 0.1, 100, prefix, prefix, None)

    monkeypatch.setattr(validation, "run_bounded_command", run)
    assert validation.main(["--binary", str(binary)]) == 2
    assert json.loads(path.read_text())["outcomes"] == []


def test_atomic_outcome_write_preserves_metadata_and_unchanged_timestamp(tmp_path: Path) -> None:
    path = prepare_corpus(tmp_path)
    raw = json.loads(path.read_text())
    raw["preparation"] = {"recipe": "pinned"}
    path.write_text(json.dumps(raw))
    outcome: suites.CorpusOutcome = {
        "file_sha256": raw["workloads"][0]["sha256"],
        "fact_directory_sha256": "",
        "binary_sha256": "sha256:bin",
        "timeout_sec": 300,
        "disequality_encoding": "nee",
        "kind": "validation",
        "policy": suites.VALIDATION_POLICY,
        "status": "failure",
        "reason": "invalid proof",
    }
    validation.record_outcome(path, outcome)
    before = path.stat().st_mtime_ns
    validation.record_outcome(path, outcome)
    assert before == path.stat().st_mtime_ns
    assert json.loads(path.read_text())["preparation"] == raw["preparation"]
    assert not list(path.parent.glob(".validation-*"))


def test_recorded_safety_deferral_prevents_relaunch_on_changed_binary(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    path = prepare_corpus(tmp_path)
    raw = json.loads(path.read_text())
    raw["outcomes"] = [
        {
            "file_sha256": raw["workloads"][0]["sha256"],
            "fact_directory_sha256": "",
            "binary_sha256": "old binary",
            "timeout_sec": 120,
            "disequality_encoding": "nee",
            "kind": "safety",
            "policy": suites.SAFETY_POLICY,
            "status": "deferred",
            "reason": "old cap",
        }
    ]
    path.write_text(json.dumps(raw))
    binary = tmp_path / "new-engine"
    binary.write_bytes(b"new engine")
    monkeypatch.setattr(validation, "__file__", str(tmp_path / "scripts/validate_benchmarks.py"))
    monkeypatch.setattr(
        validation, "run_bounded_command", lambda *_a, **_k: pytest.fail("known unsafe input must defer")
    )
    before = path.read_bytes()
    assert validation.main(["--binary", str(binary)]) == 1
    assert path.read_bytes() == before


def test_pending_population_without_reason_is_incomplete_and_needs_no_build(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: Any,
) -> None:
    path = prepare_corpus(tmp_path)
    raw = json.loads(path.read_text())
    raw["cases"][0].update(status="pending", workloads=[])
    raw["workloads"] = []
    path.write_text(json.dumps(raw))
    monkeypatch.setattr(validation, "__file__", str(tmp_path / "scripts/validate_benchmarks.py"))
    monkeypatch.setattr(validation, "build_target", lambda *_a, **_k: pytest.fail("pending sources need preparation"))
    assert validation.main([]) == 1
    assert "case-0: pending" in capsys.readouterr().err
