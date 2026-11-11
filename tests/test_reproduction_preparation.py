"""Preparation must preserve source-build failures and stop on resource refusal."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest

from scripts import reproduction_preparation as preparation
from scripts import reproduction_prepare_hardboiled as hardboiled
from scripts import reproduction_prepare_misaal as misaal
from scripts import reproduction_prepare_misaal_arm as misaal_arm
from scripts import reproduction_prepare_misaal_cases as misaal_cases
from scripts import reproduction_prepare_misaal_hvx as misaal_hvx
from scripts.reproduction_stages import run_stage


@pytest.fixture
def misaal_orchestration(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> dict[str, Any]:
    monkeypatch.setattr(preparation, "ROOT", tmp_path)
    for name in ("benchmarks/catalog.json", "benchmarks/reproduction/population.json"):
        path = tmp_path / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("{}")
    cases = [
        {
            "id": f"{target}-{name}",
            "family": "misaal",
            "source": f"benchmarks/{target}/halide/{name}",
            "configuration": {"target": target},
            "paper_aliases": [f"paper-{name}"],
            "scope": "required",
        }
        for target, name in (("x86", "ready"), ("x86", "failed"), ("arm", "ready"), ("hexagon", "ready"))
    ]
    monkeypatch.setattr(preparation, "expected_cases", lambda *_: cases)
    engine = tmp_path / "engine"
    engine.write_text("ordinary engine")
    llvm = tmp_path / "llvm"
    (llvm / "lib").mkdir(parents=True)
    (llvm / "lib/libLLVM.dylib").write_text("LLVM runtime")
    monkeypatch.setattr(misaal, "LLVM12", llvm)
    state: dict[str, Any] = {
        "engine": engine,
        "root": tmp_path,
        "cases": cases,
        "calls": [],
        "outputs": {},
        "stop_target": None,
        "stop_status": "memory-limit",
        "exception_target": None,
        "native_failure": False,
        "all_failed": False,
        "tamper_request": None,
    }

    def native(output: Path) -> Path:
        state["calls"].append("native")
        if state["native_failure"]:
            (output / "steps").mkdir()
            (output / "steps/001-build.result.json").write_text(json.dumps({"status": state["stop_status"]}))
            raise RuntimeError("actual shared dependency failed")
        checkout = output / "checkout"
        checkout.mkdir()
        (checkout / "rules").write_text("original source rules")
        (output / "python/lib").mkdir(parents=True)
        for name in ("library", "legalizer", "backend", "python", "llvm_as"):
            path = output / "target" / name
            path.parent.mkdir(exist_ok=True)
            path.write_text(name)
            state["outputs"][name] = str(path)
        cmake = output / "cmake"
        cmake.write_text("pinned CMake executable fixture")
        (output / "halide-build").mkdir()
        (output / "halide-build/CMakeCache.txt").write_text(f"CMAKE_COMMAND:INTERNAL={cmake}\n")
        (output / "boost_1_81_0").mkdir()
        path = output / "request.json"
        path.write_text(
            json.dumps(
                {
                    "checkout": str(checkout),
                    "preparation": str(output),
                    "revision": misaal.MISAAL_REVISION,
                    **state["outputs"],
                }
            )
        )
        return path

    def build(target: str, output: Path, request: Path, **kwargs: Any) -> dict[str, Any]:
        state["calls"].append(target)
        selected = [case for case in cases if case["configuration"] == {"target": target}]
        assert kwargs["case_ids"] == [case["id"] for case in selected]
        if target != "x86":
            assert kwargs["cmake"] == tmp_path / "environment/cmake"
            assert kwargs["boost_include"] == tmp_path / "environment/boost_1_81_0"
        if state["exception_target"] == target:
            raise ValueError(f"{target} original semantic dependency missing")
        output.mkdir()
        requests = output / "requests"
        requests.mkdir()
        identity = output / "identity.json"
        identity.write_text(f"original {target} preparation identity")
        legalizer = output / f"{target}-legalizer.so"
        legalizer.write_text(f"native {target} legalizer fixture")
        rows = {}
        for case in selected:
            failed = case["id"] == "x86-failed" or state["all_failed"]
            row = {
                **case,
                "status": "blocked" if failed else "prepared",
                "request": None,
                "reason": "compiler rejected original source" if failed else None,
            }
            if not failed:
                path = requests / f"{case['id']}.json"
                path.write_text(
                    json.dumps(
                        {**case, "case_id": case["id"], "legalizer": str(legalizer), "identity_paths": [str(identity)]}
                    )
                )
                row.update(request=str(path), request_sha256=misaal.sha256_file(path))
                if state["tamper_request"] == case["id"]:
                    path.write_text(path.read_text() + " ")
            rows[case["id"]] = row
            (output / f"case-{case['id']}.json").write_text(json.dumps(row))
        settings = output / "settings.json"
        settings.write_text(
            json.dumps({"misaal": {"paths": {"requests": str(requests)}, "identity_paths": [str(identity)]}})
        )
        outcome = {
            "status": "blocked" if any(r["status"] == "blocked" for r in rows.values()) else "success",
            "settings": str(settings),
            "cases": rows,
        }
        if state["stop_target"] == target:
            # A source helper can wrap the real guard outcome as a generic blocker.
            (output / "steps").mkdir()
            (output / "steps/001-build.result.json").write_text(json.dumps({"status": state["stop_status"]}))
            outcome["status"] = "blocked"
        return outcome

    monkeypatch.setattr(misaal, "prepare", native)
    monkeypatch.setattr(misaal_cases, "prepare_misaal_cases", lambda *a, **kw: build("x86", *a, **kw))
    monkeypatch.setattr(misaal_arm, "prepare_misaal_arm", lambda *a, **kw: build("arm", *a, **kw))
    monkeypatch.setattr(misaal_hvx, "prepare_misaal_hvx", lambda *a, **kw: build("hexagon", *a, **kw))
    for module in (misaal, misaal_cases, misaal_arm, misaal_hvx):
        monkeypatch.setattr(
            module, "exclusive_job", lambda *_: pytest.fail("only the coordinator may acquire the slot")
        )
    return state


def test_misaal_merges_all_original_targets_and_preserves_failed_cases(misaal_orchestration: dict[str, Any]) -> None:
    state = misaal_orchestration
    result = preparation.prepare_family("misaal", state["root"], state["engine"])
    assert state["calls"] == ["native", "x86", "arm", "hexagon"]
    assert result["status"] == "success" and result["generator_preparation_status"] == "blocked"
    settings = json.loads(Path(result["settings"]).read_text())["misaal"]
    assert settings["configuration_blockers"][0]["case_ids"] == ["x86-failed"]
    assert settings["configuration_blockers"][0]["reason"] == "compiler rejected original source"
    assert set(state["outputs"].values()) <= set(result["artifacts"])
    assert str(state["root"] / "environment/python/lib") in result["artifact_directories"]
    assert set(result["cases"]) == {case["id"] for case in state["cases"]}
    requests = Path(settings["paths"]["requests"])
    assert {path.stem for path in requests.glob("*.json")} == {"x86-ready", "arm-ready", "hexagon-ready"}
    for row in result["cases"].values():
        if row["status"] == "prepared":
            assert Path(row["request"]).read_bytes() == Path(row["published_request"]).read_bytes()
            assert row["paper_aliases"] == ["paper-ready"]
    for relative in ("generators", "arm", "hvx"):
        original = json.loads((state["root"] / relative / "settings.json").read_text())["misaal"]
        assert "configuration_blockers" not in original
    assert settings["timeout_sec"] == 300


@pytest.mark.parametrize("status", ["resource-stopped", "memory-limit", "timed-out", "launch-refused"])
@pytest.mark.parametrize("target", ["x86", "arm", "hexagon"])
def test_misaal_guard_stop_prevents_later_targets_and_settings(
    misaal_orchestration: dict[str, Any],
    target: str,
    status: str,
) -> None:
    state = misaal_orchestration
    state.update(stop_target=target, stop_status=status)
    result = preparation.prepare_family("misaal", state["root"], state["engine"])
    order = ["native", "x86", "arm", "hexagon"]
    assert state["calls"] == order[: order.index(target) + 1]
    assert result["status"] == ("resource-stopped" if status == "launch-refused" else status)
    assert not (state["root"] / "settings.json").exists()
    assert not (state["root"] / "requests").exists()
    assert set(result["cases"]) == {case["id"] for case in state["cases"]}


def test_misaal_target_dependency_failure_blocks_only_that_target(misaal_orchestration: dict[str, Any]) -> None:
    state = misaal_orchestration
    state["exception_target"] = "arm"
    result = preparation.prepare_family("misaal", state["root"], state["engine"])
    assert result["status"] == "success"
    assert state["calls"] == ["native", "x86", "arm", "hexagon"]
    settings = json.loads(Path(result["settings"]).read_text())["misaal"]
    blockers = {item["case_ids"][0]: item for item in settings["configuration_blockers"]}
    assert set(blockers) == {"x86-failed", "arm-ready"}
    assert "semantic dependency missing" in blockers["arm-ready"]["reason"]
    assert Path(blockers["arm-ready"]["evidence"][0]).is_file()


def test_misaal_shared_failure_accounts_for_every_target_without_launch(misaal_orchestration: dict[str, Any]) -> None:
    state = misaal_orchestration
    state["native_failure"] = True
    result = preparation.prepare_family("misaal", state["root"], state["engine"])
    assert state["calls"] == ["native"]
    assert result["status"] == "memory-limit"
    assert all(row["status"] == "not-reached" and row["request"] is None for row in result["cases"].values())
    assert not (state["root"] / "settings.json").exists()


def test_misaal_no_successful_requests_cannot_publish_settings(misaal_orchestration: dict[str, Any]) -> None:
    state = misaal_orchestration
    state["all_failed"] = True
    result = preparation.prepare_family("misaal", state["root"], state["engine"])
    assert state["calls"] == ["native", "x86", "arm", "hexagon"]
    assert result["status"] == "preparation-blocked"
    assert len(result["cases"]) == 4
    assert not (state["root"] / "settings.json").exists()


def test_misaal_changed_request_is_blocked_without_losing_other_targets(misaal_orchestration: dict[str, Any]) -> None:
    state = misaal_orchestration
    state["tamper_request"] = "arm-ready"
    result = preparation.prepare_family("misaal", state["root"], state["engine"])
    assert result["status"] == "success"
    assert result["cases"]["arm-ready"]["status"] == "blocked"
    assert result["cases"]["arm-ready"]["request"] is None
    assert "bytes changed" in result["cases"]["arm-ready"]["reason"]
    assert not (state["root"] / "requests/arm-ready.json").exists()
    assert (state["root"] / "requests/hexagon-ready.json").is_file()


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
