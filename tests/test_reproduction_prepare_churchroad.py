"""Frontend-only source preparation; native jobs are simulated, with guards intact."""

import json
from pathlib import Path
from typing import Any

import pytest

from scripts import reproduction_prepare_churchroad as preparation
from scripts import source_tools
from scripts.reproduction_process import PilotProcessResult


@pytest.fixture
def pipeline(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> tuple[Path, Path, dict[str, Any], list[dict[str, Any]]]:
    monkeypatch.setattr(preparation, "ROOT", tmp_path)
    monkeypatch.setattr(preparation.shutil, "which", lambda _: "/host/tool")
    engine = tmp_path / "engine"
    engine.write_text("ordinary runtime")
    output = tmp_path / "benchmarks/local/reproduction/churchroad"
    patch = tmp_path / "benchmarks/reproduction/patches/churchroad-capture.diff"
    patch.parent.mkdir(parents=True)
    patch.write_text("checked patch")
    state: dict[str, Any] = {}
    launches: list[dict[str, Any]] = []

    def acquire(preparer: source_tools.Preparation, name: str, url: str, revision: str) -> Path:
        path = preparer.directory / "sources" / name
        path.mkdir(parents=True)
        if name == "churchroad":
            (path / "yosys-plugin").mkdir()
        launches.append({"name": "acquire", "source": name, "url": url, "revision": revision})
        return path

    def apply(self: source_tools.Preparation, checkout: Path, patch: Path) -> None:
        assert checkout.is_relative_to(self.directory / "sources")
        launches.append({"name": "patch", "source": checkout.name, "patch": patch.name})

    def run(command: list[str], cwd: Path, prefix: Path, **options: Any) -> PilotProcessResult:
        name = prefix.name.split("-", 1)[1]
        launches.append({"name": name, "command": command, "options": options})
        stdout, stderr = prefix.with_suffix(".stdout.log"), prefix.with_suffix(".stderr.log")
        stdout.write_text("")
        stderr.write_text("")
        if name == state.get("stop"):
            return PilotProcessResult("memory-limit", None, 0, 0, stdout, stderr, "cap")
        if name == "yosys-install":
            (output / "prefix/bin").mkdir(parents=True)
            for tool in ("yosys", "yosys-config"):
                (output / "prefix/bin" / tool).write_text("native tool")
        elif name == "churchroad-plugin" and not state.get("omit_plugin"):
            Path(command[-2]).write_text("native ABI-matched plugin")
        elif name == "yosys-passes" and state.get("missing_pass"):
            stdout.write_text("No such command or cell type: write_churchroad")
        elif name == "churchroad-lock":
            (cwd / "Cargo.lock").write_text("resolved dependencies")
        elif name == "churchroad-build":
            binary = output / "build/cargo/debug/churchroad"
            binary.parent.mkdir(parents=True)
            binary.write_text("compiler")
            if state.get("lock_changed"):
                (cwd / "Cargo.lock").write_text("drift")
        return PilotProcessResult("success", 0, 0, 0, stdout, stderr, None)

    monkeypatch.setattr(preparation, "acquire_source", acquire)
    monkeypatch.setattr(preparation.Preparation, "apply_patch", apply)
    monkeypatch.setattr(source_tools, "run_bounded_command", run)
    return output, engine, state, launches


@pytest.mark.parametrize("system", ["Darwin", "Linux"])
def test_preparation_builds_only_frontend_and_mapping_dependencies(
    pipeline: tuple, monkeypatch: pytest.MonkeyPatch, system: str
) -> None:
    output, engine, _, launches = pipeline
    monkeypatch.setattr(preparation.platform, "system", lambda: system)
    result = preparation.prepare_churchroad(output, engine)
    assert result["status"] == "success", result
    assert [(row["source"], row["revision"]) for row in launches if row["name"] == "acquire"] == [
        (name, revision) for name, (_, revision) in preparation.REVISIONS.items()
    ]
    assert set(preparation.REVISIONS) == {"churchroad", "yosys"}
    jobs = {row["name"]: row for row in launches if "command" in row}
    assert all(row["options"]["require_guard"] for row in jobs.values())
    assert jobs["yosys-configure"]["command"][-1] == ("config-clang" if system == "Darwin" else "config-gcc")
    assert jobs["yosys-passes"]["command"][-1] == "help write_churchroad; help read_verilog; help prep"
    assert not any(arg.startswith("CARGO_HOME=") for row in jobs.values() for arg in row["command"])
    assert "--locked" in jobs["churchroad-build"]["command"]
    script = Path(result["binary"]).read_text()
    assert script.startswith("#!/bin/sh\nexec env ")
    assert "LAKEROAD" not in script and '"$@"' in script
    settings = json.loads(Path(result["settings"]).read_text())["churchroad"]
    assert settings["paths"]["binary"] == result["binary"]


@pytest.mark.parametrize(
    "fault,reason",
    [
        ({"missing_pass": True}, "required frontend pass"),
        ({"omit_plugin": True}, "omitted"),
        ({"lock_changed": True}, "lockfile"),
    ],
)
def test_incomplete_frontend_is_never_published(pipeline: tuple, fault: dict, reason: str) -> None:
    output, engine, state, _ = pipeline
    state.update(fault)
    result = preparation.prepare_churchroad(output, engine)
    assert result["status"] == "blocked" and reason in result["reason"]
    assert not (output / "settings.json").exists()


def test_resource_stop_preserves_receipt_and_stops_next_job(pipeline: tuple) -> None:
    output, engine, state, launches = pipeline
    state["stop"] = "yosys-build"
    result = preparation.prepare_churchroad(output, engine)
    assert result["status"] == "memory-limit"
    assert launches[-1]["name"] == "yosys-build"
    assert json.loads((output / "preparation.json").read_text())["status"] == "memory-limit"
    assert not (output / "settings.json").exists()


def test_missing_host_tool_never_launches_preparation(pipeline: tuple, monkeypatch: pytest.MonkeyPatch) -> None:
    output, engine, _, launches = pipeline
    monkeypatch.setattr(preparation.shutil, "which", lambda _: None)
    result = preparation.prepare_churchroad(output, engine)
    assert result["status"] == "blocked" and "Missing host prerequisites" in result["reason"]
    assert not launches
