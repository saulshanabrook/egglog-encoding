"""Public preparation retains export dependencies and never starts LLVM lowering."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest

from scripts import misaal_reproduction as capture
from scripts import reproduction_misaal_export as export
from scripts import reproduction_preparation as preparation
from scripts import reproduction_prepare_hardboiled as hardboiled
from scripts import reproduction_prepare_misaal as misaal
from scripts.reproduction_stages import run_stage


@pytest.fixture
def export_family(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> dict[str, Any]:
    monkeypatch.setattr(preparation, "ROOT", tmp_path)
    for name in ("benchmarks/catalog.json", "benchmarks/reproduction/population.json"):
        path = tmp_path / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("{}")
    templates = tmp_path / "templates"
    templates.mkdir()
    checkout = tmp_path / "source"
    checkout.mkdir()
    engine = tmp_path / "engine"
    engine.write_text("replay engine")
    cases = [
        {
            "id": f"misaal-{target}-one",
            "family": "misaal",
            "source": f"benchmarks/{target}/halide/one",
            "configuration": {"target": target},
            "scope": "required",
        }
        for target in ("x86", "arm", "hexagon")
    ]
    state: dict[str, Any] = {
        "cases": cases,
        "engine": engine,
        "calls": [],
        "failure": None,
        "stop": None,
        "frontend_stop": None,
        "root": tmp_path,
        "templates": templates,
        "mutation": None,
    }
    policy = {
        "pattern_deduplication": "exact-render-last-v1",
        "literal_width_guard": "preserved fixture",
        "racket_runtime": {"path": "retained seal"},
        "environment": {"HYDRIDE_DISTRIBUTE_LOOK_AHEAD": "1"},
    }
    for case in cases:
        request = {
            "case_id": case["id"],
            "source": case["source"],
            "configuration": case["configuration"],
            "revision": "a" * 40,
            "checkout": str(checkout),
            **policy,
        }
        (templates / f"{case['id']}.json").write_text(json.dumps(request))
    monkeypatch.setattr(preparation, "expected_cases", lambda *_: cases)
    monkeypatch.setattr(capture, "verified_request", lambda path: json.loads(path.read_text()))
    monkeypatch.setattr(export, "verified_export_template", lambda path: json.loads(path.read_text()))
    monkeypatch.setattr(misaal, "prepare", lambda *_: pytest.fail("legacy native preparer must never run"))

    def frontend(output: Path, template: Path) -> dict:
        state["calls"].append("frontend")
        output.mkdir()
        result = {"status": state["frontend_stop"] or "success", "checkout": str(output / "compiled-source")}
        (output / "frontend.json").write_text(json.dumps(result))
        return result

    monkeypatch.setattr(export, "prepare_export_frontend", frontend)
    monkeypatch.setattr(export, "verified_frontend", lambda path: json.loads(path.read_text()))

    def generator(output: Path, template: Path, frontend: Path) -> dict:
        case_id = template.stem
        state["calls"].append(case_id)
        output.mkdir(parents=True)
        status = (
            state["stop"]
            if case_id == cases[1]["id"] and state["stop"]
            else "failed"
            if state["failure"] == case_id
            else "success"
        )
        result = {"status": status, "reason": "retained generator failure"}
        (output / "generator.json").write_text(json.dumps(result))
        request = json.loads(template.read_text())
        request.update(egglog_export="egglog-only-v1", expected_generator_outputs=[])
        for key in ("backend", "python", "generator", "library"):
            path = output / key
            path.write_text(key)
            request[key] = str(path)
        request["identity_paths"] = [str(checkout)]
        if state["mutation"]:
            request[state["mutation"]] = "changed"
        (output / "capture-request.json").write_text(json.dumps(request))
        return result

    monkeypatch.setattr(export, "prepare_export_generator", generator)
    state["settings"] = {"paths": {"requests": str(templates)}, "revision": "a" * 40, "timeout_sec": 900}
    return state


def test_export_prepares_all_original_targets_and_preserves_source_policies(export_family: dict) -> None:
    state = export_family
    result = preparation.prepare_family("misaal", state["root"], state["engine"], settings=state["settings"])
    assert result["status"] == "success"
    assert state["calls"] == ["frontend", *[case["id"] for case in state["cases"]]]
    config = json.loads(Path(result["settings"]).read_text())["misaal"]
    assert config["egglog_export"] == "egglog-only-v1" and config["timeout_sec"] == 900
    assert config["paths"]["checkout"] == str(state["root"] / "source")
    for case in state["cases"]:
        old = json.loads((state["templates"] / f"{case['id']}.json").read_text())
        new = json.loads((Path(config["paths"]["requests"]) / f"{case['id']}.json").read_text())
        assert all(
            new[key] == old[key]
            for key in ("pattern_deduplication", "literal_width_guard", "racket_runtime", "environment")
        )
        assert "egglog_export" not in old
    assert config["configuration_blockers"] == []


def test_existing_exact_blocker_remains_and_does_not_build_that_case(export_family: dict) -> None:
    state = export_family
    case = state["cases"][1]
    blocker = {
        "case_ids": [case["id"]],
        "configuration": case["configuration"],
        "reason": "missing original rule",
        "evidence": ["original diagnosis"],
    }
    state["settings"]["configuration_blockers"] = [blocker]
    result = preparation.prepare_family("misaal", state["root"], state["engine"], settings=state["settings"])
    assert result["status"] == "success" and case["id"] not in state["calls"]
    assert json.loads(Path(result["settings"]).read_text())["misaal"]["configuration_blockers"] == [blocker]
    assert set(result["cases"]) == {case["id"] for case in state["cases"]}


@pytest.mark.parametrize("missing", [False, True])
def test_no_retained_templates_never_falls_back_to_native(export_family: dict, missing: bool) -> None:
    state = export_family
    settings = state["settings"] if missing else {}
    if missing:
        settings["paths"]["requests"] = "absent"
    result = preparation.prepare_family("misaal", state["root"], state["engine"], settings=settings)
    assert result["status"] == "preparation-blocked" and not state["calls"]


@pytest.mark.parametrize("status", ["memory-limit", "resource-stopped", "timed-out"])
def test_generator_guard_stop_prevents_later_cases_and_settings(export_family: dict, status: str) -> None:
    state = export_family
    state["stop"] = status
    result = preparation.prepare_family("misaal", state["root"], state["engine"], settings=state["settings"])
    assert result["status"] == status
    assert state["calls"] == ["frontend", state["cases"][0]["id"], state["cases"][1]["id"]]
    assert not (state["root"] / "settings.json").exists()


def test_failed_generator_blocks_only_its_exact_case(export_family: dict) -> None:
    state = export_family
    state["failure"] = state["cases"][1]["id"]
    result = preparation.prepare_family("misaal", state["root"], state["engine"], settings=state["settings"])
    config = json.loads(Path(result["settings"]).read_text())["misaal"]
    assert result["status"] == "success" and len(state["calls"]) == 4
    assert config["configuration_blockers"][0]["case_ids"] == [state["failure"]]


@pytest.mark.parametrize("field", ["case_id", "source", "configuration", "egglog_export"])
def test_prepared_request_cannot_change_case_or_policy(export_family: dict, field: str) -> None:
    state = export_family
    state["mutation"] = field
    result = preparation.prepare_family("misaal", state["root"], state["engine"], settings=state["settings"])
    assert result["status"] == "preparation-blocked" and "settings" not in result


def test_verified_frontend_can_be_reused_without_rebuilding(export_family: dict) -> None:
    state = export_family
    receipt = state["root"] / "retained-frontend.json"
    receipt.write_text(json.dumps({"status": "success", "checkout": str(state["root"] / "source")}))
    state["settings"]["export_frontend"] = str(receipt)
    result = preparation.prepare_family("misaal", state["root"], state["engine"], settings=state["settings"])
    assert result["status"] == "success" and "frontend" not in state["calls"]


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


@pytest.mark.parametrize("change", ["identity-file", "deleted-identity-file", "runtime-member", "header", "binary"])
def test_preparation_reuse_binds_runtime_dependencies(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, change: str
) -> None:
    engine = tmp_path / "engine"
    engine.write_text("ordinary engine")
    dependency = tmp_path / "external-llvm.dylib"
    dependency.write_text("original external LLVM")
    runtime = tmp_path / "racket-runtime"
    runtime.mkdir()
    (runtime / "existing-module").write_text("existing")
    launches = 0
    prepared_paths: dict[str, Path] = {}

    def prepare(output: Path, llvm: Path) -> Path:
        nonlocal launches
        launches += 1
        checkout = output / "sources"
        checkout.mkdir()
        build = output / "halide-build"
        include = build / "include"
        include.mkdir(parents=True)
        (include / "Halide.h").write_text("original header")
        binary = build / "native-optimizer"
        binary.write_text("actual native binary fixture")
        # Disposables stay outside the declared runtime identity.
        (build / "unused.o").write_text("object file")
        prepared_paths.update(header=include / "Halide.h", binary=binary)
        path = output / "settings.json"
        path.write_text(
            json.dumps(
                {
                    "hardboiled": {
                        "paths": {"checkout": str(checkout), "build": str(build), "binary": str(binary)},
                        "identity_paths": [str(dependency), str(runtime), str(include)],
                    }
                }
            )
        )
        return path

    monkeypatch.setattr(hardboiled, "prepare", prepare)

    def execute(attempt: Path) -> dict:
        return preparation.prepare_family("hardboiled", attempt, engine)

    first = run_stage(tmp_path / "stages", "hardboiled", "prepare", {}, execute)
    assert first["status"] == "success"
    assert str(dependency) in first["artifacts"]
    assert str(runtime) in first["artifact_directories"]
    assert str(prepared_paths["binary"]) in first["artifacts"]
    assert str(prepared_paths["header"].parent) in first["artifact_directories"]
    assert all(not path.endswith("unused.o") for path in first["artifacts"])
    saved = (Path(first["attempt"]) / "stage.json").read_bytes()
    assert run_stage(tmp_path / "stages", "hardboiled", "prepare", {}, execute) == first
    if change == "identity-file":
        dependency.write_text("changed external LLVM")
    elif change == "deleted-identity-file":
        dependency.unlink()
    elif change == "runtime-member":
        (runtime / "new-module").write_text("new module")
    else:
        prepared_paths[change].write_text("changed native prerequisite")
    second = run_stage(tmp_path / "stages", "hardboiled", "prepare", {}, execute)
    assert launches == 2 and second["attempt"] != first["attempt"]
    assert second["status"] == ("blocked" if change == "deleted-identity-file" else "success")
    if change == "deleted-identity-file":
        assert "runtime dependency is missing" in second["reason"]
    assert (Path(first["attempt"]) / "stage.json").read_bytes() == saved


def test_frontend_guard_stop_never_builds_generators_or_publishes_settings(export_family: dict) -> None:
    state = export_family
    state["frontend_stop"] = "memory-limit"
    result = preparation.prepare_family("misaal", state["root"], state["engine"], settings=state["settings"])
    assert result["status"] == "memory-limit" and state["calls"] == ["frontend"]
    assert not (state["root"] / "settings.json").exists()


def test_template_change_during_preparation_cannot_publish_that_case(
    export_family: dict, monkeypatch: pytest.MonkeyPatch
) -> None:
    state = export_family
    original = export.prepare_export_generator
    first = state["cases"][0]["id"]

    def changed(output: Path, template: Path, frontend: Path) -> dict:
        result = original(output, template, frontend)
        if template.stem == first:
            template.write_text(template.read_text() + " ")
        return result

    monkeypatch.setattr(export, "prepare_export_generator", changed)
    result = preparation.prepare_family("misaal", state["root"], state["engine"], settings=state["settings"])
    assert result["status"] == "success"
    config = json.loads(Path(result["settings"]).read_text())["misaal"]
    assert not (Path(config["paths"]["requests"]) / f"{first}.json").exists()
    assert config["configuration_blockers"][0]["reason"] == "retained template changed during export preparation"
