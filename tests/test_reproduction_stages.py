"""Stage reuse requires current inputs and intact outputs, including failures."""

from __future__ import annotations

import json
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


@pytest.mark.parametrize("change", ["bytes", "add", "remove", "empty-directory", "symlink-target"])
def test_runtime_directory_changes_invalidate_reuse(tmp_path: Path, change: str) -> None:
    runtime = tmp_path / "runtime"
    runtime.mkdir()
    library = runtime / "library"
    library.write_text("original library")
    external = tmp_path / "external"
    external.mkdir()
    (external / "module").write_text("original external module")
    (runtime / "linked-modules").symlink_to(external, target_is_directory=True)
    launches = 0

    def execute(attempt: Path) -> dict[str, Any]:
        nonlocal launches
        launches += 1
        receipt = attempt / "native-completion.json"
        receipt.write_text("{}")
        return {"status": "success", "artifacts": [str(receipt)], "artifact_directories": [str(runtime)]}

    first = run_stage(tmp_path / "stages", "case", "prepare", {}, execute)
    saved = (Path(first["attempt"]) / "stage.json").read_bytes()
    assert run_stage(tmp_path / "stages", "case", "prepare", {}, execute) == first
    if change == "bytes":
        library.write_text("changed library")
    elif change == "add":
        (runtime / "new-library").write_text("new")
    elif change == "remove":
        library.unlink()
    elif change == "empty-directory":
        (runtime / "new-directory").mkdir()
    else:
        (external / "module").write_text("changed external module")
    second = run_stage(tmp_path / "stages", "case", "prepare", {}, execute)
    assert launches == 2 and second["status"] == "success"
    assert second["artifact_directories"] != first["artifact_directories"]
    assert second["attempt"] != first["attempt"]
    assert (Path(first["attempt"]) / "stage.json").read_bytes() == saved


def test_transient_tree_files_are_ignored_and_symlink_cycles_are_rejected(tmp_path: Path) -> None:
    runtime = tmp_path / "runtime"
    runtime.mkdir()
    receipt = tmp_path / "completion.json"
    receipt.write_text("{}")

    def execute(_: Path) -> dict[str, Any]:
        return {"status": "success", "artifacts": [str(receipt)], "artifact_directories": [str(runtime)]}

    first = run_stage(tmp_path / "stages", "case", "prepare", {}, execute)
    for name in (".git", "__pycache__"):
        (runtime / name).mkdir()
        (runtime / name / "transient").write_text("transient")
    assert run_stage(tmp_path / "stages", "case", "prepare", {}, execute) == first
    (runtime / "cycle").symlink_to(runtime, target_is_directory=True)
    second = run_stage(tmp_path / "stages", "case", "prepare", {}, execute)
    assert second["status"] == "blocked"
    assert "cycle" in second["reason"]


def test_legacy_file_only_receipt_remains_reusable(tmp_path: Path) -> None:
    artifact = tmp_path / "actual-output"
    artifact.write_text("retained bytes")
    first = run_stage(
        tmp_path / "stages", "case", "capture", {}, lambda _: {"status": "success", "artifacts": [str(artifact)]}
    )
    del first["artifact_directories"]
    receipt = Path(first["attempt"]) / "stage.json"
    receipt.write_text(json.dumps(first))
    assert (
        run_stage(
            tmp_path / "stages", "case", "capture", {}, lambda _: pytest.fail("legacy receipt must remain readable")
        )
        == first
    )
