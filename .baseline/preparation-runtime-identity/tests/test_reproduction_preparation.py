"""Preparation must preserve source-build failures and stop on resource refusal."""

from __future__ import annotations

import json
from pathlib import Path

import pytest

from scripts import reproduction_preparation as preparation
from scripts import reproduction_prepare_hardboiled as hardboiled


def test_guard_refusal_remains_a_safety_stop(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    engine = tmp_path / "engine"
    engine.write_text("unused engine fixture")

    def refused(output: Path, llvm: Path) -> Path:
        steps = output / "steps"
        steps.mkdir()
        (steps / "001-compile.result.json").write_text(
            json.dumps({"status": "launch-refused", "reason": "disk guard refused to launch: fewer than 10 GiB free"})
        )
        raise ValueError("disk guard refused to launch: fewer than 10 GiB free")

    monkeypatch.setattr(hardboiled, "prepare", refused)
    result = preparation.prepare_family("hardboiled", tmp_path, engine)
    assert result["status"] == "resource-stopped"
    assert any(path.endswith("001-compile.result.json") for path in result["artifacts"])


def test_missing_engine_stops_before_dependency_build(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(hardboiled, "prepare", lambda *_: pytest.fail("unreplayable corpus must not start builds"))
    result = preparation.prepare_family("hardboiled", tmp_path, tmp_path / "missing-engine")
    assert result["status"] == "preparation-blocked"
    assert "engine is missing" in result["reason"]
