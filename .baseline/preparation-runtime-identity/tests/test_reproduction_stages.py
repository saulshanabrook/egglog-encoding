"""Stage reuse requires current inputs and intact outputs, including failures."""

from __future__ import annotations

from pathlib import Path
from typing import Any

import pytest

from scripts.reproduction_process import exclusive_job
from scripts.reproduction_stages import run_stage


def test_resume_invalidates_changed_inputs_and_output(tmp_path: Path) -> None:
    launches = 0

    def execute(attempt: Path) -> dict[str, Any]:
        nonlocal launches
        launches += 1
        output = attempt / "case.egg"
        output.write_text(f"; attempt {launches}\n(check (= 1 1))\n")
        return {"status": "success", "artifacts": [str(output)]}

    first = run_stage(tmp_path, "case", "capture", {"source": "a"}, execute)
    assert launches == 1
    assert run_stage(tmp_path, "case", "capture", {"source": "a"}, execute) == first
    assert launches == 1
    output = Path(next(iter(first["artifacts"])))
    output.write_text("changed")
    second = run_stage(tmp_path, "case", "capture", {"source": "a"}, execute)
    assert second["attempt"] != first["attempt"]
    assert launches == 2
    run_stage(tmp_path, "case", "capture", {"source": "b"}, execute)
    assert launches == 3


def test_failures_are_retained_without_blind_retries(tmp_path: Path) -> None:
    launches = 0

    def execute(attempt: Path) -> dict[str, Any]:
        nonlocal launches
        launches += 1
        return {"status": "blocked", "reason": "exact missing dependency", "artifacts": []}

    first = run_stage(tmp_path, "case", "capture", {}, execute)
    assert run_stage(tmp_path, "case", "capture", {}, execute) == first
    assert launches == 1
    second = run_stage(tmp_path, "case", "capture", {}, execute, retry=True)
    assert launches == 2
    assert second["attempt"] != first["attempt"]
    assert len(list(tmp_path.glob("case/capture/*/attempt-*/stage.json"))) == 2


def test_no_completion_without_actual_outputs(tmp_path: Path) -> None:
    result = run_stage(tmp_path, "case", "capture", {}, lambda _: {"status": "success", "artifacts": []})
    assert result["status"] == "blocked"
    assert "outputs" in result["reason"]


def test_interrupt_retains_evidence_and_releases_lock(tmp_path: Path) -> None:
    def execute(_: Path) -> dict[str, Any]:
        raise KeyboardInterrupt

    with pytest.raises(KeyboardInterrupt):
        run_stage(tmp_path, "case", "capture", {}, execute)
    assert '"status": "interrupted"' in next(tmp_path.glob("case/capture/*/attempt-*/stage.json")).read_text()
    with exclusive_job(tmp_path / ".heavy-job.lock"):
        pass


def test_competing_reproduction_is_refused(tmp_path: Path) -> None:
    with exclusive_job(tmp_path / ".heavy-job.lock"), pytest.raises(ValueError, match="another reproduction"):
        run_stage(tmp_path, "case", "capture", {}, lambda _: pytest.fail("must not launch"))


def test_safety_stop_remains_an_explicit_outcome(tmp_path: Path) -> None:
    result = run_stage(
        tmp_path,
        "case",
        "capture",
        {},
        lambda _: {"status": "resource-stopped", "reason": "host reserve", "artifacts": []},
    )
    assert result["status"] == "resource-stopped"
    assert result["reason"] == "host reserve"
