"""The reproduction CLI resumes acquisition without touching timed observations."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest

from scripts import suite_reproduction as reproduction


@pytest.fixture
def coordinator(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> tuple[Path, list[str]]:
    (tmp_path / "benchmarks/reproduction").mkdir(parents=True)
    (tmp_path / "benchmarks/reproduction/population.json").write_text("{}")
    (tmp_path / "benchmarks/catalog.json").write_text("{}")
    cache = tmp_path / ".reports.jsonl"
    cache.write_text("untouched performance cache\n")
    storage = tmp_path / "evidence"
    storage.mkdir()
    (storage / "settings.json").write_text(json.dumps({"eggcc": {"paths": {}, "revision": "one"}}))
    cases = [
        {"id": name, "family": "eggcc", "scope": "required", "source": name, "configuration": {}}
        for name in ["one", "two"]
    ]
    monkeypatch.setattr(reproduction, "ROOT", tmp_path)
    monkeypatch.setattr(reproduction, "STORAGE", storage)
    monkeypatch.setattr(reproduction, "expected_cases", lambda *_: cases)
    monkeypatch.setattr(reproduction, "case_identity", lambda case, settings: {"case": case, "settings": settings})
    launched: list[str] = []

    def capture(case: dict[str, Any], settings: dict[str, Any], output: Path) -> dict[str, Any]:
        launched.append(case["id"])
        output.mkdir()
        replay = output / "full.egg"
        replay.write_text("(check (= 1 1))")
        return {"status": "reproduced", "source_completion": {"status": "success"}, "workloads": [str(replay)]}

    monkeypatch.setattr(reproduction, "capture_case", capture)
    return storage, launched


def test_cached_and_changed_revision_selection(coordinator: tuple, tmp_path: Path) -> None:
    storage, launched = coordinator
    assert reproduction.main(["--family", "eggcc", "--family", "eggcc", "--stage", "capture"]) == 0
    assert launched == ["one", "two"]
    assert reproduction.main(["--family", "eggcc", "--stage", "capture"]) == 0
    assert launched == ["one", "two"]
    settings = storage / "settings.json"
    settings.write_text(json.dumps({"eggcc": {"paths": {}, "revision": "two"}}))
    assert reproduction.main(["--family", "eggcc", "--case", "one", "--stage", "capture"]) == 0
    assert launched == ["one", "two", "one"]
    assert (tmp_path / ".reports.jsonl").read_text() == "untouched performance cache\n"


def test_nested_safety_stop_halts_and_remains_cached(coordinator: tuple, monkeypatch: pytest.MonkeyPatch) -> None:
    storage, launched = coordinator

    def capture(case: dict, settings: dict, output: Path) -> dict:
        launched.append(case["id"])
        return {"status": "blocked", "source_completion": {"status": "memory-limit"}, "workloads": []}

    monkeypatch.setattr(reproduction, "capture_case", capture)
    assert reproduction.main(["--family", "eggcc", "--stage", "capture"]) == 2
    assert launched == ["one"]
    assert reproduction.main(["--family", "eggcc", "--stage", "capture"]) == 2
    assert launched == ["one"]
    report = json.loads((storage / "report.json").read_text())
    assert [case["outcome"]["status"] for case in report["cases"]] == ["memory-limit", "pending"]


def test_failed_parent_never_promotes_prefix(coordinator: tuple, monkeypatch: pytest.MonkeyPatch) -> None:
    storage, launched = coordinator

    def capture(case: dict, settings: dict, output: Path) -> dict:
        launched.append(case["id"])
        return {
            "status": "blocked",
            "source_completion": {"status": "failed"},
            "reason": "compiler failed after export",
        }

    monkeypatch.setattr(reproduction, "capture_case", capture)
    assert reproduction.main(["--family", "eggcc"]) == 1
    assert reproduction.main(["--family", "eggcc"]) == 1
    assert launched == ["one", "two"]
    assert "compiler failed after export" in (storage / "REPORT.md").read_text()
