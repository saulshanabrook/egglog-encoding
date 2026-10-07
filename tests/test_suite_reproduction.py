"""Fresh author inputs, stable aliases, and explicit interrupted preparation."""

from __future__ import annotations

import hashlib
import io
import json
import shutil
from collections import Counter
from pathlib import Path
from typing import Any

import pytest

from benchmarking import suites
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


@pytest.mark.parametrize("parent_status", ["failure", "timed-out", "output-limit"])
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
    assert events == ["prepare", "capture a", "validate", "capture b", "validate"]
    assert len(repository["runs"]) == 2
    outcome = {"timed-out": "timed out", "output-limit": "hit output limit"}.get(parent_status, "failed")
    assert all(case["status"] == "ready" and outcome in case["reason"] for case in manifest["cases"])
    assert manifest["workloads"][0]["aliases"] == [{"case": "a", "order": 1}, {"case": "b", "order": 1}]
    for case in manifest["cases"]:
        case["validation"]["validation_sha256"] = "old admission checks"
    reproduction.write_manifest(output, manifest)
    reproduction.reproduce(output, ["eggcc"], [], engine)
    assert events == ["prepare", "capture a", "validate", "capture b", "validate", "validate", "validate"]
    assert len(repository["runs"]) == 2


def test_partial_native_capture_resumes_remaining_calls_without_losing_failed_evidence(
    repository: dict[str, Any], monkeypatch: pytest.MonkeyPatch
) -> None:
    from scripts import reproduction_validation
    from scripts.hardboiled_replay import egglog_forms
    from scripts.source_tools import sha256_file

    root, engine = repository["root"], repository["engine"]
    (root / "benchmarks/sources.json").write_text(json.dumps({"eggcc": {"revision": "pinned"}}))
    repository["cases"][:] = [dict(repository["cases"][0], family="eggcc")]
    events: list[str] = []

    def capture(case: dict[str, Any], settings: Any, directory: Path, *_: Any) -> dict[str, Any]:
        events.append("capture")
        directory.mkdir()
        sessions = []
        for index in range(3):
            replay = directory / f"call-{index}.egg"
            replay.write_text(f"; call {index}\n(datatype E (A))\n(extract (A))\n")
            sessions.append(
                {
                    "replay": str(replay),
                    "replay_sha256": sha256_file(replay),
                    "output_contract": {"kind": "ordinary-best-extract", "expected_terms": [egglog_forms("(A)")[0][2]]},
                }
            )
        return {
            "status": "ordinary-validation-pending",
            "source_completion": {"status": "complete"},
            "materialization": {"complete": True, "expected_sessions": 3, "materialized_sessions": 3},
            "sessions": sessions,
        }

    statuses = iter(["success", "failure", "memory-limit", "success"])

    def run(command: list[str], cwd: Path, prefix: Path, timeout_sec: float) -> PilotProcessResult:
        events.append(Path(command[-1]).name)
        stdout, stderr = prefix.with_suffix(".out"), prefix.with_suffix(".err")
        stdout.write_text("(A)\n")
        stderr.write_text("")
        status = next(statuses)
        return PilotProcessResult(
            status,  # type: ignore[arg-type]
            0,
            0.1,
            10,
            stdout,
            stderr,
            "retained ordinary failure" if status == "failure" else "RSS limit" if status == "memory-limit" else None,
        )

    monkeypatch.setattr(reproduction, "prepare_family", lambda *a, **k: {"status": "success", "settings": {}})
    monkeypatch.setattr(reproduction, "capture_case", capture)
    monkeypatch.setattr(reproduction_validation, "run_complete_command", run)
    output = root / "corpus"
    with pytest.raises(RuntimeError, match="RSS limit"):
        reproduction.reproduce(output, ["eggcc"], [], engine)
    state = json.loads((output / ".local/preparation.json").read_text())["manifest"]
    assert len(state["cases"][0]["workloads"]) == 1 and "validation" not in state["cases"][0]
    resumed = reproduction.reproduce(output, ["eggcc"], [], engine)
    assert events == ["capture", "call-0.egg", "call-1.egg", "call-2.egg", "call-2.egg"]
    assert len(resumed["cases"][0]["workloads"]) == 2
    assert resumed["cases"][0]["reason"] == "retained ordinary failure"
    reproduction.reproduce(output, ["eggcc"], [], engine)
    assert len(events) == 5


def test_gurobi_blocker_does_not_prepare_native_compiler(
    repository: dict[str, Any], monkeypatch: pytest.MonkeyPatch
) -> None:
    from scripts.reproduction_prepare_eggcc import GUROBI_BLOCKER

    root = repository["root"]
    (root / "benchmarks/sources.json").write_text(json.dumps({"eggcc": {"revision": "pinned"}}))
    repository["cases"][:] = [
        dict(repository["cases"][0], family="eggcc", configuration=GUROBI_BLOCKER["configuration"])
    ]
    monkeypatch.setattr(
        reproduction, "prepare_family", lambda *a, **k: pytest.fail("blocked configuration must not build")
    )
    result = reproduction.reproduce(root / "corpus", ["eggcc"], [], repository["engine"])
    assert result["cases"][0]["reason"] == GUROBI_BLOCKER["reason"]
    assert not repository["runs"]


@pytest.mark.parametrize("changed", [None, "binary", "source", "runtime", "settings"])
def test_eggcc_preparation_reuses_only_unchanged_environment(
    repository: dict[str, Any], monkeypatch: pytest.MonkeyPatch, changed: str | None
) -> None:
    root, engine = repository["root"], repository["engine"]
    recipe = {"revision": "pinned", "programs": ["program.egg"]}
    (root / "benchmarks/sources.json").write_text(json.dumps({"eggcc": recipe}))
    for case in repository["cases"]:
        case["family"] = "eggcc"
    checkout = root / "prepared"
    checkout.mkdir()
    for name in ("binary", "program.egg", "tiger"):
        (checkout / name).write_text(name)
    settings = {
        "paths": {"checkout": str(checkout), "binary": str(checkout / "binary"), "egglog": str(engine)},
        "identity_paths": [str(checkout / "tiger")],
        "configuration_blockers": [],
    }
    prepares = []

    def prepare(*args: Any, **kwargs: Any) -> dict[str, Any]:
        prepares.append("prepare")
        return {"status": "success", "settings": settings}

    monkeypatch.setattr(reproduction, "prepare_family", prepare)
    monkeypatch.setattr(reproduction, "capture_case", lambda *a, **k: {"status": "blocked", "reason": "source failure"})
    output = root / "corpus"
    first = reproduction.reproduce(output, ["eggcc"], ["a"], engine)
    if changed in {"binary", "source", "runtime"}:
        (checkout / {"binary": "binary", "source": "program.egg", "runtime": "tiger"}[changed]).write_text("changed")
    elif changed == "settings":
        first["environments"]["eggcc"]["settings"]["configuration_blockers"] = [{"reason": "changed"}]
        reproduction.write_manifest(output, first)
        settings["configuration_blockers"] = []
    engine.write_text("different replay engine")
    reproduction.reproduce(output, ["eggcc"], ["b"], engine)
    assert len(prepares) == (1 if changed is None else 2)


def test_other_family_and_unrelated_scripts_do_not_regenerate(repository: dict[str, Any]) -> None:
    root = repository["root"]
    output = root / "corpus"
    reproduction.reproduce(output, ["hardboiled"], [], repository["engine"])
    (root / "scripts/misaal_generator.py").write_text("# another family\n")
    (root / "scripts/nightly.py").write_text("# unrelated command\n")
    reproduction.reproduce(output, ["hardboiled"], [], repository["engine"])
    assert repository["captures"] == ["a", "b"] and len(repository["runs"]) == 2


def test_shared_adapter_changes_generation_identity(repository: dict[str, Any]) -> None:
    relative = "scripts/paper_benchmarks/materialize.py"
    adapter = repository["root"] / relative
    adapter.parent.mkdir(exist_ok=True)
    adapter.write_text("# initial syntax adapter\n")
    before = reproduction.generation_identity("dialegg", {"revision": "pin"})
    adapter.write_text("# changed syntax adapter\n")
    assert reproduction.generation_identity("dialegg", {"revision": "pin"}) != before


def test_orchestration_changes_preserve_generation_identity(repository: dict[str, Any]) -> None:
    root = repository["root"]
    coordinator = root / "scripts/suite_reproduction.py"
    coordinator.write_text("def capture_case():\n    return 'source'\ndef reproduce():\n    return 'old'\n")
    before = reproduction.generation_identity("eggcc", {"revision": "pin"})
    coordinator.write_text(coordinator.read_text().replace("'old'", "'resumed'"))
    (root / "process_guard.py").write_text("# RSS-only guard\n")
    assert reproduction.generation_identity("eggcc", {"revision": "pin"}) == before
    coordinator.write_text(coordinator.read_text().replace("'source'", "'different source'"))
    assert reproduction.generation_identity("eggcc", {"revision": "pin"}) != before


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
    if initial_status == "success":
        assert changed["cases"][0]["revalidation"]["status"] == "success"
        assert len(repository["runs"]) == 3
    else:
        assert changed["cases"][0]["reason"] == "retained source capture changed"
        assert len(repository["runs"]) == 2
    assert repository["captures"] == ["a", "b"]


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
    assert "evidence" not in saved["cases"][0]
    local = json.loads((output / ".local/preparation.json").read_text())["manifest"]
    assert local["cases"][0]["evidence"]
    assert saved["cases"][1]["status"] == "pending"
    assert len(repository["runs"]) == 1


def test_timeout_remains_an_outcome_and_other_cases_continue(repository: dict[str, Any]) -> None:
    repository["status"] = "timed-out"
    manifest = reproduction.reproduce(repository["root"] / "corpus", ["hardboiled"], [], repository["engine"])
    assert all(row["status"] == "blocked" and "timed-out" in row["reason"] for row in manifest["cases"])
    assert len(repository["runs"]) == 2


@pytest.mark.parametrize("prepared", [False, True])
def test_output_limit_is_retained_and_does_not_stop_other_cases(repository: dict[str, Any], prepared: bool) -> None:
    output, engine = repository["root"] / "corpus", repository["engine"]
    if prepared:
        reproduction.reproduce(output, ["hardboiled"], [], engine)
        engine.write_text("changed engine")
    repository["status"] = "output-limit"
    stopped = reproduction.reproduce(output, ["hardboiled"], [], engine)
    launches = len(repository["runs"])
    assert launches == (4 if prepared else 2)
    if prepared:
        assert all(case["revalidation"]["status"] == "output-limit" for case in stopped["cases"])
    else:
        assert all("output-limit" in case["reason"] for case in stopped["cases"])
    reproduction.reproduce(output, ["hardboiled"], [], engine)
    assert len(repository["runs"]) == launches
    engine.write_text("another engine")
    repository["status"] = "success"
    reproduction.reproduce(output, ["hardboiled"], [], engine)
    assert len(repository["runs"]) == launches + 2
    assert repository["captures"] == ["a", "b"]


def test_native_output_limit_without_complete_calls_is_not_recaptured(
    repository: dict[str, Any], monkeypatch: pytest.MonkeyPatch
) -> None:
    root, engine = repository["root"], repository["engine"]
    (root / "benchmarks/sources.json").write_text(json.dumps({"eggcc": {"revision": "pinned"}}))
    for case in repository["cases"]:
        case["family"] = "eggcc"
    captured: list[str] = []

    def capture(case: dict[str, Any], *_: Any) -> dict[str, Any]:
        captured.append(case["id"])
        return {"status": "blocked", "process": {"status": "output-limit"}, "reason": "no completed calls"}

    monkeypatch.setattr(reproduction, "prepare_family", lambda *a, **k: {"status": "success", "settings": {}})
    monkeypatch.setattr(reproduction, "capture_case", capture)
    first = reproduction.reproduce(root / "corpus", ["eggcc"], [], engine)
    assert all(case["reason"] == "no completed calls" for case in first["cases"])
    reproduction.reproduce(root / "corpus", ["eggcc"], [], engine)
    assert captured == ["a", "b"]


def test_outcome_history_survives_interrupted_regeneration(tmp_path: Path) -> None:
    local = tmp_path / ".local"
    local.mkdir()
    outcomes = [{"file_sha256": "input", "status": "failure"}, {"file_sha256": "old", "status": "success"}]
    history = local / "outcomes.json"
    history.write_text(json.dumps(outcomes))
    manifest = {"workloads": [{"sha256": "input", "facts_sha256": "facts"}], "outcomes": []}
    reproduction.write_manifest(tmp_path, manifest)
    before = history.stat().st_mtime_ns
    manifest["workloads"] = []
    reproduction.write_manifest(tmp_path, manifest)
    assert json.loads(history.read_text()) == outcomes and history.stat().st_mtime_ns == before
    assert "outcomes" not in json.loads((tmp_path / "manifest.json").read_text())


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
    (output / ".local/outcomes.json").write_text(json.dumps(first["outcomes"]))
    (repository["root"] / "scripts/hardboiled_generator.py").write_text("# changed adapter, same output bytes\n")
    second = reproduction.reproduce(output, ["hardboiled"], [], repository["engine"])
    assert second["outcomes"] == first["outcomes"]
    assert json.loads((output / ".local/outcomes.json").read_text()) == first["outcomes"]


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


def test_portable_manifest_excludes_local_state_and_keeps_recipe_and_aliases(repository: dict[str, Any]) -> None:
    output = repository["root"] / suites.MANIFEST_RELATIVE_PATH.parent
    result = reproduction.reproduce(output, ["hardboiled"], [], repository["engine"])
    public = json.loads((output / "manifest.json").read_text())
    assert set(public) == {"sources", "preparation", "cases", "workloads"}
    assert public["preparation"] == result["preparation"]
    assert public["workloads"] == result["workloads"]
    assert all(set(case) == {"id", "family", "source", "status", "workloads", "reason"} for case in public["cases"])
    assert str(repository["root"]) not in json.dumps(public)
    state = json.loads((output / ".local/preparation.json").read_text())
    assert state["manifest_sha256"] == hashlib.sha256((output / "manifest.json").read_bytes()).hexdigest()
    assert state["manifest"]["cases"][0]["capture"]
    assert state["manifest"]["cases"][0]["validation"]


@pytest.mark.parametrize("blocker", [None, "parent failed after one complete call", "failure at /private/source/build"])
def test_fresh_clone_resolves_and_revalidates_frozen_programs_without_author_sources(
    repository: dict[str, Any], monkeypatch: pytest.MonkeyPatch, blocker: str | None
) -> None:
    original_root = repository["root"]
    output = original_root / suites.MANIFEST_RELATIVE_PATH.parent
    result = reproduction.reproduce(output, ["hardboiled"], [], repository["engine"])
    if blocker:
        result["cases"][0].update(status="blocked", reason=blocker, portable_reason=blocker)
        reproduction.write_manifest(output, result)
    clone = original_root / "clone"
    cloned_output = clone / suites.MANIFEST_RELATIVE_PATH.parent
    shutil.copytree(output, cloned_output, ignore=shutil.ignore_patterns(".local"))
    for path in ("process_guard.py", "benchmarks/sources.json", "engine"):
        shutil.copyfile(original_root / path, clone / path)
    shutil.copytree(original_root / "scripts", clone / "scripts")
    path = cloned_output / "manifest.json"
    original, before = path.read_bytes(), path.stat().st_mtime_ns
    assert not (cloned_output / ".local").exists()
    selected = suites.resolve_suite("expanded", clone)
    assert len(selected.files) == 1 and len(selected.cases) == 2 and selected.manifest.outcomes == ()
    assert not selected.capture_errors
    monkeypatch.setattr(reproduction, "ROOT", clone)
    checked = reproduction.reproduce(cloned_output, ["hardboiled"], [], clone / "engine")
    assert path.read_bytes() == original and path.stat().st_mtime_ns == before
    assert repository["captures"] == ["a", "b"] and len(repository["runs"]) == 4
    assert all(case["revalidation"]["status"] == "success" for case in checked["cases"])
    assert all(str(cloned_output) in command[-1] for command in repository["runs"][-2:])
    assert checked["cases"][0]["status"] == ("blocked" if blocker else "ready")
    reproduction.reproduce(cloned_output, ["hardboiled"], [], clone / "engine")
    assert len(repository["runs"]) == 4


def test_local_resume_state_cannot_override_changed_tracked_manifest(repository: dict[str, Any]) -> None:
    output = repository["root"] / "corpus"
    reproduction.reproduce(output, ["hardboiled"], [], repository["engine"])
    path = output / "manifest.json"
    raw = json.loads(path.read_text())
    raw["cases"][0]["reason"] = "updated upstream source provenance"
    path.write_text(json.dumps(raw, indent=2) + "\n")
    before = path.read_bytes()
    result = reproduction.reproduce(output, ["hardboiled"], ["a"], repository["engine"])
    assert result["cases"][0]["reason"] == raw["cases"][0]["reason"]
    assert path.read_bytes() == before
    assert repository["captures"] == ["a", "b"] and len(repository["runs"]) == 3


def test_frozen_manifest_recipe_change_regenerates_without_local_state(repository: dict[str, Any]) -> None:
    root = repository["root"]
    output = root / "corpus"
    reproduction.reproduce(output, ["hardboiled"], [], repository["engine"])
    shutil.rmtree(output / ".local")
    (root / "scripts/hardboiled_generator.py").write_text("# updated generator\n")
    reproduction.reproduce(output, ["hardboiled"], [], repository["engine"])
    assert repository["captures"] == ["a", "b", "a", "b"]


def test_failed_frozen_revalidation_preserves_tracked_inputs_and_prior_engine_success(
    repository: dict[str, Any],
) -> None:
    output = repository["root"] / "corpus"
    engine = repository["engine"]
    reproduction.reproduce(output, ["hardboiled"], [], engine)
    path = output / "manifest.json"
    original, before = path.read_bytes(), path.stat().st_mtime_ns
    engine.write_text("engine B")
    repository["status"] = "failure"
    failed = reproduction.reproduce(output, ["hardboiled"], [], engine)
    assert all(case["revalidation"]["status"] == "failure" and case["workloads"] for case in failed["cases"])
    assert path.read_bytes() == original and path.stat().st_mtime_ns == before
    engine.write_text("engine identity")
    reused = reproduction.reproduce(output, ["hardboiled"], [], engine)
    assert all("revalidation" not in case for case in reused["cases"])
    assert repository["captures"] == ["a", "b"] and len(repository["runs"]) == 4


@pytest.mark.parametrize("refuse", [False, True])
def test_frozen_revalidation_safety_stop_preserves_inputs_and_halts_later_cases(
    repository: dict[str, Any], monkeypatch: pytest.MonkeyPatch, refuse: bool
) -> None:
    output = repository["root"] / suites.MANIFEST_RELATIVE_PATH.parent
    engine = repository["engine"]
    reproduction.reproduce(output, ["hardboiled"], [], engine)
    path = output / "manifest.json"
    original, before = path.read_bytes(), path.stat().st_mtime_ns
    engine.write_text("new engine")
    repository["status"] = "memory-limit"
    if refuse:

        def refused(*_: Any, **__: Any) -> Any:
            raise ValueError("resource guard refused to launch a workload: host pressure")

        monkeypatch.setattr(dialegg_capture, "run_complete_command", refused)
    with pytest.raises(RuntimeError, match="later cases remain pending"):
        reproduction.reproduce(output, ["hardboiled"], [], engine)
    assert len(repository["runs"]) == (2 if refuse else 3)
    assert path.read_bytes() == original and path.stat().st_mtime_ns == before
    selected = suites.resolve_suite("expanded", repository["root"])
    assert len(selected.manifest.outcomes) == 1
    assert selected.manifest.outcomes[0]["kind"] == "safety"
    assert suites.suite_outcomes(selected, (), 300)[1]


@pytest.mark.parametrize(
    ("reason", "expected"),
    [
        ("Gurobi requires gurobi_cl and a usable license", "Gurobi requires gurobi_cl and a usable license"),
        ("Missing host prerequisites: yosys, make", "Missing host prerequisites: yosys, make"),
        ("native output contract changed", "native output contract changed"),
        ("build-generator: failure; see /private/local/build.result.json", "build-generator: failure"),
        (
            "missing LLVM18/MLIR frontend prerequisite: /opt/llvm/lib/libMLIR.dylib",
            "missing LLVM18/MLIR frontend prerequisite: libMLIR.dylib",
        ),
        ("failed in /private/local/work", "fallback"),
        ("error\ncompiler diagnostics", "fallback"),
    ],
)
def test_portable_reasons_preserve_blockers_without_diagnostic_paths(reason: str, expected: str) -> None:
    assert reproduction.portable_reason(reason, "fallback") == expected
