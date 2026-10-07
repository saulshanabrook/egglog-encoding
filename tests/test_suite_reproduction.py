"""Fresh author inputs, stable aliases, and explicit interrupted preparation."""

from __future__ import annotations

import hashlib
import io
import json
from collections import Counter
from pathlib import Path
from typing import Any

import pytest

from scripts import dialegg_capture
from scripts import suite_reproduction as reproduction
from scripts.reproduction_inventory import expected_cases, select_cases
from scripts.reproduction_process import PilotProcessResult


def test_full_source_population_and_stable_selection() -> None:
    cases = expected_cases()
    assert Counter(row["family"] for row in cases) == {
        "math-growth": 1,
        "luminal": 7,
        "eggcc": 191,
        "hardboiled": 42,
        "misaal": 102,
        "churchroad": 29,
        "dialegg": 25,
    }
    selected = select_cases(cases, ["dialegg", "eggcc", "eggcc"], [])
    assert selected == [row for row in cases if row["family"] in {"eggcc", "dialegg"}]
    assert any(row["id"] == "dialegg-extra-nmm-160" for row in selected)
    assert {tuple(row["configuration"]["native_options"]) for row in selected if row["family"] == "eggcc"} >= {
        (),
        ("--with-context",),
        ("--with-context", "--no-hacker-rules"),
        ("--tiger-ilp", "--ilp-solver", "gurobi"),
    }
    with pytest.raises(ValueError, match="unknown"):
        select_cases(cases, ["hardboiled"], ["not-an-input"])


@pytest.fixture
def repository(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> dict[str, Any]:
    (tmp_path / "process_guard.py").write_text("# shared process guard\n")
    (tmp_path / "scripts").mkdir()
    (tmp_path / "scripts/hardboiled_generator.py").write_text("# generation identity\n")
    (tmp_path / "benchmarks").mkdir()
    (tmp_path / "benchmarks/sources.json").write_text(json.dumps({"hardboiled": {"revision": "pinned"}}))
    engine = tmp_path / "engine"
    engine.write_text("engine identity")
    cases = [{"id": name, "family": "hardboiled", "source": name + ".egg", "configuration": {}} for name in ("a", "b")]
    state: dict[str, Any] = {
        "root": tmp_path,
        "engine": engine,
        "cases": cases,
        "captures": [],
        "runs": [],
        "status": "success",
    }
    monkeypatch.setattr(reproduction, "ROOT", tmp_path)
    monkeypatch.setattr(reproduction, "expected_cases", lambda _: cases)

    def capture(case: dict[str, Any], recipe: dict[str, Any], output: Path) -> tuple[Path, list[str]]:
        assert output.is_dir()  # coordinator owns the attempt directory
        state["captures"].append(case["id"])
        path = output / "replay.egg"
        path.write_text("(datatype E (A))\n(let root (A))\n(extract root)\n")
        return path, ["original source query"]

    def run(command: list[str], cwd: Path, prefix: Path, timeout_sec: float) -> PilotProcessResult:
        state["runs"].append(command)
        stdout, stderr = prefix.with_suffix(".out"), prefix.with_suffix(".err")
        stdout.write_text("(A)\n")
        stderr.write_text("")
        return PilotProcessResult(
            state["status"], 0, 0.1, 10, stdout, stderr, "observed failure" if state["status"] != "success" else None
        )

    monkeypatch.setattr(reproduction, "capture_source_file", capture)
    monkeypatch.setattr(dialegg_capture, "run_complete_command", run)
    return state


def test_publish_deduplicates_aliases_and_unchanged_regeneration_launches_nothing(repository: dict[str, Any]) -> None:
    output = repository["root"] / "corpus"
    first = reproduction.reproduce(output, ["hardboiled"], [], repository["engine"])
    assert len(first["workloads"]) == 1
    assert first["workloads"][0]["aliases"] == [{"case": "a", "order": 0}, {"case": "b", "order": 0}]
    before = (output / "manifest.json").stat().st_mtime_ns
    second = reproduction.reproduce(output, ["hardboiled"], [], repository["engine"])
    assert first == second
    assert repository["captures"] == ["a", "b"] and len(repository["runs"]) == 2
    assert (output / "manifest.json").stat().st_mtime_ns == before


def test_new_engine_revalidates_without_regenerating_or_deleting_old_bytes(repository: dict[str, Any]) -> None:
    output = repository["root"] / "corpus"
    first = reproduction.reproduce(output, ["hardboiled"], [], repository["engine"])
    old_file = output / first["workloads"][0]["file"]
    repository["engine"].write_text("changed engine")
    reproduction.reproduce(output, ["hardboiled"], ["a"], repository["engine"])
    assert old_file.is_file()
    assert repository["captures"] == ["a", "b"]
    assert len(repository["runs"]) == 3
    reproduction.reproduce(output, ["hardboiled"], [], repository["engine"])
    assert len(repository["runs"]) == 4  # the unselected case still needs the new engine
    assert repository["captures"] == ["a", "b"]


@pytest.mark.parametrize("parent_status", ["failure", "timed-out"])
def test_native_capture_revalidates_without_regenerating_and_retains_parent_outcome(
    repository: dict[str, Any], monkeypatch: pytest.MonkeyPatch, parent_status: str
) -> None:
    from scripts import reproduction_validation

    root, engine = repository["root"], repository["engine"]
    (root / "benchmarks/sources.json").write_text(json.dumps({"eggcc": {"revision": "pinned"}}))
    for case in repository["cases"]:
        case["family"] = "eggcc"
    events: list[str] = []

    def prepare(*_: Any, **__: Any) -> dict[str, Any]:
        events.append("prepare")
        return {"status": "success", "settings": {}}

    def capture(case: dict[str, Any], settings: Any, directory: Path, *_: Any) -> dict[str, Any]:
        events.append("capture " + case["id"])
        directory.mkdir()
        replay = directory / "call.egg"
        replay.write_text("(datatype E (A))\n(let root (A))\n(extract root)\n")
        return {
            "status": "ordinary-validation-pending",
            "process": {"status": parent_status},
            "sessions": [{"replay": str(replay), "source_order": 1}],
        }

    def validate(captured: dict[str, Any], *_: Any, **__: Any) -> dict[str, Any]:
        events.append("validate")
        return {"status": "success", "workloads": [captured["sessions"][0]["replay"]]}

    monkeypatch.setattr(reproduction, "prepare_family", prepare)
    monkeypatch.setattr(reproduction, "capture_case", capture)
    monkeypatch.setattr(reproduction_validation, "validate_capture", validate)
    output = root / "corpus"
    reproduction.reproduce(output, ["eggcc"], [], engine)
    engine.write_text("new engine")
    manifest = reproduction.reproduce(output, ["eggcc"], [], engine)
    assert events == ["prepare", "capture a", "validate", "capture b", "validate", "validate", "validate"]
    outcome = "timed out" if parent_status == "timed-out" else "failed"
    assert all(case["status"] == "ready" and outcome in case["reason"] for case in manifest["cases"])
    assert manifest["workloads"][0]["aliases"] == [{"case": "a", "order": 1}, {"case": "b", "order": 1}]


def test_other_family_and_unrelated_scripts_do_not_regenerate(repository: dict[str, Any]) -> None:
    root = repository["root"]
    output = root / "corpus"
    reproduction.reproduce(output, ["hardboiled"], [], repository["engine"])
    (root / "scripts/misaal_generator.py").write_text("# another family\n")
    (root / "scripts/nightly.py").write_text("# unrelated command\n")
    reproduction.reproduce(output, ["hardboiled"], [], repository["engine"])
    assert repository["captures"] == ["a", "b"] and len(repository["runs"]) == 2


@pytest.mark.parametrize("relative", ["scripts/paper_benchmarks/materialize.py", "process_guard.py"])
def test_shared_adapter_changes_generation_identity(repository: dict[str, Any], relative: str) -> None:
    adapter = repository["root"] / relative
    adapter.parent.mkdir(exist_ok=True)
    adapter.write_text("# initial syntax adapter\n")
    before = reproduction.generation_identity("dialegg", {"revision": "pin"})
    adapter.write_text("# changed syntax adapter\n")
    assert reproduction.generation_identity("dialegg", {"revision": "pin"}) != before


@pytest.mark.parametrize("initial_status", ["success", "timed-out"])
def test_changed_capture_is_not_revalidated_as_new_input(repository: dict[str, Any], initial_status: str) -> None:
    root = repository["root"]
    output = root / "corpus"
    repository["status"] = initial_status
    manifest = reproduction.reproduce(output, ["hardboiled"], [], repository["engine"])
    capture = root / manifest["cases"][0]["capture"]
    capture.write_text(capture.read_text() + " ")
    repository["engine"].write_text("new engine")
    changed = reproduction.reproduce(output, ["hardboiled"], ["a"], repository["engine"])
    assert changed["cases"][0]["reason"] == "retained source capture changed"
    assert repository["captures"] == ["a", "b"] and len(repository["runs"]) == 2


def test_failed_ordinary_replay_can_be_revalidated_without_source_generation(repository: dict[str, Any]) -> None:
    output = repository["root"] / "corpus"
    repository["status"] = "timed-out"
    reproduction.reproduce(output, ["hardboiled"], [], repository["engine"])
    repository["status"] = "success"
    manifest = reproduction.reproduce(output, ["hardboiled"], [], repository["engine"])
    assert all(case["status"] == "ready" for case in manifest["cases"])
    assert repository["captures"] == ["a", "b"] and len(repository["runs"]) == 4


def test_safety_stop_retains_reason_and_leaves_later_cases_pending(repository: dict[str, Any]) -> None:
    repository["status"] = "memory-limit"
    output = repository["root"] / "corpus"
    with pytest.raises(RuntimeError, match="later cases remain pending"):
        reproduction.reproduce(output, ["hardboiled"], [], repository["engine"])
    saved = json.loads((output / "manifest.json").read_text())
    assert saved["cases"][0]["status"] == "blocked" and "memory-limit" in saved["cases"][0]["reason"]
    assert saved["cases"][0]["evidence"]
    assert saved["cases"][1]["status"] == "pending"
    assert len(repository["runs"]) == 1


def test_timeout_remains_an_outcome_and_other_cases_continue(repository: dict[str, Any]) -> None:
    repository["status"] = "timed-out"
    manifest = reproduction.reproduce(repository["root"] / "corpus", ["hardboiled"], [], repository["engine"])
    assert all(row["status"] == "blocked" and "timed-out" in row["reason"] for row in manifest["cases"])
    assert len(repository["runs"]) == 2


def test_outcome_history_survives_interrupted_regeneration(tmp_path: Path) -> None:
    manifest = {
        "workloads": [{"sha256": "input", "facts_sha256": "facts"}],
        "outcomes": [
            {"file_sha256": "input", "fact_directory_sha256": "facts", "status": "failure"},
            {"file_sha256": "input", "fact_directory_sha256": "old", "status": "success"},
        ],
    }
    reproduction.write_manifest(tmp_path, manifest)
    assert json.loads((tmp_path / "manifest.json").read_text())["outcomes"] == manifest["outcomes"]
    manifest["workloads"] = []
    reproduction.write_manifest(tmp_path, manifest)
    assert len(json.loads((tmp_path / "manifest.json").read_text())["outcomes"]) == 2


def test_published_input_download_uses_pinned_source_and_existing_attempt(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    from scripts import reproduction_published as published

    data = b"(datatype E (A))\n(extract (A))\n"
    entry = {
        "file": "test.egg",
        "size_bytes": len(data),
        "sha256": hashlib.sha256(data).hexdigest(),
        "git_blob": hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest(),
        "extracts": 1,
    }
    urls = []

    def fetch(url: str, **_: Any) -> io.BytesIO:
        urls.append(url)
        return io.BytesIO(data)

    monkeypatch.setattr(reproduction.urllib.request, "urlopen", fetch)
    monkeypatch.setattr(published, "published_entries", lambda _: {"case": entry})
    replay, _ = reproduction.capture_source_file(
        {"id": "case", "family": "hardboiled", "source": "inputs/test.egg"},
        {"repository": "https://github.com/author/repo", "revision": "pin"},
        tmp_path,
    )
    assert urls == ["https://raw.githubusercontent.com/author/repo/pin/inputs/test.egg"]
    assert replay.read_bytes() == data and (tmp_path / "source.egg").read_bytes() == data


def test_alias_pruning_removes_old_calls_without_losing_other_source_aliases(tmp_path: Path) -> None:
    manifest: dict[str, Any] = {
        "cases": [{"id": "a", "workloads": []}, {"id": "b", "workloads": ["shared.egg"]}],
        "workloads": [
            {
                "file": "shared.egg",
                "sha256": "s",
                "facts_sha256": "",
                "aliases": [{"case": "a", "order": 1}, {"case": "b", "order": 0}],
            },
            {"file": "old.egg", "sha256": "o", "facts_sha256": "", "aliases": [{"case": "a", "order": 0}]},
        ],
        "outcomes": [],
    }
    reproduction.write_manifest(tmp_path, manifest)
    assert [row["file"] for row in manifest["workloads"]] == ["shared.egg"]
    assert manifest["workloads"][0]["aliases"] == [{"case": "b", "order": 0}]


def test_same_regenerated_bytes_preserve_strict_outcomes(repository: dict[str, Any]) -> None:
    output = repository["root"] / "corpus"
    first = reproduction.reproduce(output, ["hardboiled"], [], repository["engine"])
    first["outcomes"] = [
        {"file_sha256": first["workloads"][0]["sha256"], "fact_directory_sha256": "", "status": "failure"}
    ]
    reproduction.write_manifest(output, first)
    (repository["root"] / "scripts/hardboiled_generator.py").write_text("# changed adapter, same output bytes\n")
    second = reproduction.reproduce(output, ["hardboiled"], [], repository["engine"])
    assert second["outcomes"] == first["outcomes"]
    assert json.loads((output / "manifest.json").read_text())["outcomes"] == first["outcomes"]


def test_changing_a_source_repair_fixture_invalidates_preparation(repository: dict[str, Any]) -> None:
    fixture = repository["root"] / "benchmarks/reproduction/patches/hardboiled-repair.diff"
    fixture.parent.mkdir(parents=True)
    fixture.write_text("original source repair")
    output = repository["root"] / "corpus"
    reproduction.reproduce(output, ["hardboiled"], [], repository["engine"])
    fixture.write_text("changed source repair")
    reproduction.reproduce(output, ["hardboiled"], [], repository["engine"])
    assert repository["captures"] == ["a", "b", "a", "b"]


@pytest.mark.parametrize("family", ["eggcc", "dialegg", "churchroad", "misaal"])
@pytest.mark.parametrize("field", ["repository", "revision"])
def test_native_recipe_cannot_claim_a_different_source_pin(tmp_path: Path, family: str, field: str) -> None:
    recipe = json.loads((reproduction.ROOT / "benchmarks/sources.json").read_text())[family]
    recipe[field] = "different-source"
    with pytest.raises(ValueError, match="source adapter pin"):
        reproduction.prepare_family(family, tmp_path / "build", tmp_path / "engine", recipe)
    assert not (tmp_path / "build").exists()


def test_dialegg_cases_follow_recipe_populations() -> None:
    sources = json.loads((reproduction.ROOT / "benchmarks/sources.json").read_text())
    sources["dialegg"]["timer_programs"] = ["new-program"]
    cases = [row for row in expected_cases(sources) if row["family"] == "dialegg"]
    assert any(row["id"] == "dialegg-timer-new-program" for row in cases)
    assert not any(row["id"] == "dialegg-timer-polynomial" for row in cases)
