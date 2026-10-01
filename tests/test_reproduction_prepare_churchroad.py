"""Preparation protocol tests; no downloads, compilers, solvers or native jobs run."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest

from benchmarking.pilot import PilotProcessResult
from scripts import reproduction_prepare_churchroad as preparation


@pytest.fixture
def pipeline(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> tuple[Path, Path, dict, list[dict]]:
    monkeypatch.setattr(preparation, "ROOT", tmp_path)
    implementation = tmp_path / "scripts/eggcc_churchroad_complete.py"
    implementation.parent.mkdir()
    implementation.write_text("capture source identity")
    host_tool = tmp_path / "host-tool"
    host_tool.write_text("fake host executable, never run")
    host_tool.chmod(0o755)
    monkeypatch.setattr(preparation.shutil, "which", lambda name: None if name == "z3" else str(host_tool))
    engine = tmp_path / "engine"
    engine.write_text("ordinary engine")
    output = tmp_path / "benchmarks/local/reproduction/churchroad-test"
    state: dict[str, Any] = {}
    launches: list[dict] = []

    def run(command: list[str], cwd: Path, prefix: Path, **options: Any) -> PilotProcessResult:
        name = prefix.name.split("-", 1)[1]
        assert cwd.is_dir(), (name, cwd)
        # Read the durable intent before simulating the child result.
        receipt = json.loads((output / "preparation.json").read_text())
        assert receipt["steps"][-1]["name"] == name and receipt["steps"][-1]["status"] == "running"
        launches.append({"name": name, "command": command, "options": options})
        stdout, stderr = prefix.with_suffix(".stdout.log"), prefix.with_suffix(".stderr.log")
        stdout.write_text("")
        stderr.write_text("")
        if name == state.get("guard"):
            raise ValueError("disk guard refused to launch: fewer than 10 GiB free")
        if name == state.get("stop"):
            return PilotProcessResult("memory-limit", None, 0, 0, stdout, stderr, "memory cap")
        if name == "racket-version":
            stdout.write_text(state.get("racket_version", "9.2"))
        elif name == "racket-runtime-paths":
            runtime = tmp_path / "host-racket-pkgs"
            runtime.mkdir()
            (runtime / "info.rkt").write_text("host runtime package identity")
            stdout.write_text(json.dumps([str(runtime)]))
        elif name.endswith("-init"):
            Path(command[-1]).mkdir()
        elif name.endswith("-checkout"):
            (cwd / "README").write_text("pinned public source fixture")
            if cwd.name == "lakeroad" and not state.get("missing_model"):
                model = cwd / "racket/generated/xilinx-ultrascale-plus-dsp48e2.rkt"
                model.parent.mkdir(parents=True)
                model.write_text("public generated primitive model")
                (cwd / "racket/architecture-description.rkt").write_text(
                    "runtime synthesis definition\n"
                    '(module+ test\n  (test-case "Construct smaller DSP from larger DSP"\n'
                    "                  others ...)))\n          #t]\n"
                    '  (test-case "Construct a LUT5 on Lattice from LUT4s and a MUX2."\n'
                    "remaining runtime definition\n"
                    + ("                  others ...)))\n          #t]" if state.get("changed_lakeroad_test") else "")
                )
            if cwd.name == "churchroad":
                (cwd / "yosys-plugin").mkdir()
                (cwd / "Cargo.toml").write_text("original pinned manifest\n")
        elif name.endswith("-revision") and name != "rust-version":
            revision = preparation.REVISIONS[cwd.name][1]
            stdout.write_text("wrong" if state.get("bad_revision") == cwd.name else revision)
        elif name == "python-environment":
            (Path(command[-1]) / "bin").mkdir(parents=True)
        elif name == "python-tools-download":
            for package in ("meson", "ninja"):
                (output / "evidence/python-wheels" / f"{package}-fixture.whl").write_text(package)
        elif name == "bitwuzla-configure" and not state.get("missing_meson_build"):
            build = Path(next(arg.split("=", 1)[1] for arg in command if arg.startswith("--build-dir=")))
            build.mkdir(parents=True)
            (build / "build.ninja").write_text("configured build")
        elif name == "bitwuzla-install":
            (output / "prefix/bin/bitwuzla").write_text("real solver would be built here")
        elif name == "racket-setup":
            packages = output / "racket-user/9.2/pkgs"
            packages.mkdir(parents=True)
            (packages / "resolved-dependency.rkt").write_text("resolved package source")
        elif name == "yosys-install":
            for tool in ("yosys", "yosys-config"):
                (output / "prefix/bin" / tool).write_text("full native tool")
        elif name == "churchroad-plugin":
            Path(command[-2]).write_text("plugin ABI fixture")
        elif name == "yosys-passes" and state.get("missing_pass"):
            stdout.write_text("No such command or cell type: write_btor")
        elif name == "churchroad-lock":
            (cwd / "Cargo.lock").write_text("frozen real dependency resolution would be retained here")
        elif name == "churchroad-build":
            target = Path(next(arg.split("=", 1)[1] for arg in command if arg.startswith("CARGO_TARGET_DIR=")))
            (target / "debug").mkdir(parents=True)
            (target / "debug/churchroad").write_text("native observed driver")
        return PilotProcessResult("success", 0, 0, 0, stdout, stderr, None)

    monkeypatch.setattr(preparation, "run_bounded_command", run)
    monkeypatch.setattr(preparation, "patched_churchroad_sources", lambda _: {"Cargo.toml": "patched manifest\n"})
    return output, engine, state, launches


@pytest.mark.parametrize("system", ["Linux", "Darwin"])
def test_preparation_pins_real_dependencies_and_serial_portable_builds(
    pipeline: tuple, monkeypatch: pytest.MonkeyPatch, system: str
) -> None:
    output, engine, _, launches = pipeline
    monkeypatch.setattr(preparation.platform, "system", lambda: system)
    result = preparation.prepare_churchroad(output, engine)
    assert result["status"] == "success", result["reason"]
    assert result["device_execution"] is result["benchmark_execution"] is False
    assert all(row["options"]["require_guard"] and row["options"]["allow_warning_pressure"] for row in launches)
    assert all(row["options"]["disk_reserve_bytes"] == 2 * 1024**3 for row in launches)
    commands = {row["name"]: row["command"] for row in launches}
    for name, (repo, revision) in preparation.REVISIONS.items():
        assert commands[name + "-fetch"][-3:] == ["--depth=1", f"https://github.com/{repo}.git", revision]
    assert "SMALL=1" not in str(commands) and "--recursive" not in str(commands)
    assert "--simulate" not in str(commands) and "dynamic_lookup" not in str(commands)
    assert commands["yosys-configure"][-1] == ("config-clang" if system == "Darwin" else "config-gcc")
    assert commands["yosys-build"][-4:] == ["-j1", f"PREFIX={output / 'prefix'}", "ENABLE_ABC=0", "ENABLE_TCL=0"]
    assert commands["churchroad-plugin"][-4] == str(output / "prefix/bin/yosys-config")
    assert commands["churchroad-plugin"][-3] == "--build"
    assert "--locked" in commands["churchroad-build"] and "-j1" in commands["churchroad-build"]
    assert commands["racket-setup"][-7:] == ["setup", "--jobs", "1", "--no-docs", "--pkgs", "rosette", "yaml"]
    assert "--no-index" in commands["python-tools-install"]
    assert "--only-binary=:all:" in commands["python-tools-download"]
    assert commands["python-tools-download"][-2:] == [
        f"meson=={preparation.MESON_VERSION}",
        f"ninja=={preparation.NINJA_VERSION}",
    ]
    assert commands["ninja-version"][-2] == str(output / "python/bin/ninja")
    assert result["python_build_wheels"]["ninja-fixture.whl"]["sha256"]
    assert "bitwuzla-smoke" in commands and "lakeroad-compile" in commands
    settings = json.loads(Path(result["settings"]).read_text())["churchroad"]
    assert settings["paths"]["checkout"] == str(output / "sources/churchroad")
    launcher = Path(settings["paths"]["binary"])
    script = launcher.read_text()
    assert f"PATH={output}/prefix/bin:" in script
    assert f"PLTUSERHOME={output}/racket-user" in script
    assert f"LAKEROAD_DIR={output}/sources/lakeroad" in script
    assert '"$@"' in script
    assert str(output / "racket-user") in settings["identity_paths"]
    assert str(output / "sources/lakeroad") in settings["identity_paths"]
    assert result["racket_runtime_paths"][0] in settings["identity_paths"]
    assert (output / "evidence/churchroad-Cargo.lock").is_file()
    compatibility = result["lakeroad_compatibility"]
    assert compatibility["original_sha256"] != compatibility["patched_sha256"]
    patch_lines = Path(compatibility["patch"]).read_text().splitlines()
    assert [line for line in patch_lines if line.startswith("+") and not line.startswith("+++")] == [
        "+                  other-outputs ...)))"
    ]
    assert json.loads((output / "preparation.json").read_text())["status"] == "success"


@pytest.mark.parametrize(
    "fault,reason,last",
    [
        ({"missing_model": True}, "public generated DSP48E2", "yaml-revision"),
        ({"changed_lakeroad_test": True}, "compatibility patch no longer matches", "yaml-revision"),
        ({"bad_revision": "lakeroad"}, "checkout resolved", "lakeroad-revision"),
        ({"racket_version": "8.0"}, "Racket >=8.1", "racket-version"),
        ({"missing_meson_build": True}, "without a Meson build", "bitwuzla-configure"),
        ({"missing_pass": True}, "lacks a required synthesis pass", "yosys-passes"),
    ],
)
def test_dependency_gate_failure_never_publishes_canary_settings(
    pipeline: tuple, fault: dict, reason: str, last: str
) -> None:
    output, engine, state, launches = pipeline
    state.update(fault)
    result = preparation.prepare_churchroad(output, engine)
    assert result["status"] == "blocked" and reason in result["reason"]
    assert launches[-1]["name"] == last
    assert not (output / "settings.json").exists()
    assert (output / "preparation.json").is_file()


@pytest.mark.parametrize("kind,status", [("guard", "resource-stopped"), ("stop", "memory-limit")])
def test_guard_failure_retains_receipt_and_stops_before_next_job(pipeline: tuple, kind: str, status: str) -> None:
    output, engine, state, launches = pipeline
    state[kind] = "bitwuzla-build"
    result = preparation.prepare_churchroad(output, engine)
    assert result["status"] == status
    assert launches[-1]["name"] == "bitwuzla-build"
    receipt = json.loads((output / "preparation.json").read_text())
    assert receipt["steps"][-1]["status"] == status
    assert not (output / "settings.json").exists()


def test_missing_host_tool_is_actionable_and_does_not_start_preparation(
    pipeline: tuple, monkeypatch: pytest.MonkeyPatch
) -> None:
    output, engine, _, launches = pipeline
    monkeypatch.setattr(preparation.shutil, "which", lambda _: None)
    result = preparation.prepare_churchroad(output, engine)
    assert result["status"] == "blocked" and "Missing host prerequisites" in result["reason"]
    assert not launches


def test_ninja_is_prepared_without_a_host_installation(pipeline: tuple, monkeypatch: pytest.MonkeyPatch) -> None:
    output, engine, _, launches = pipeline
    host_tool = str(output.parents[3] / "host-tool")
    monkeypatch.setattr(preparation.shutil, "which", lambda name: None if name in {"ninja", "z3"} else host_tool)
    result = preparation.prepare_churchroad(output, engine)
    assert result["status"] == "success", result["reason"]
    assert "ninja" not in result["host_tools"]
    names = [row["name"] for row in launches]
    assert names.index("python-tools-install") < names.index("ninja-version") < names.index("bitwuzla-build")


def test_preparation_rejects_shared_or_unsafe_destination_before_launch(pipeline: tuple, tmp_path: Path) -> None:
    output, engine, _, launches = pipeline
    with pytest.raises(ValueError, match="must remain below"):
        preparation.prepare_churchroad(tmp_path / "outside", engine)
    with pytest.raises(ValueError, match="without spaces"):
        preparation.prepare_churchroad(output.parent / "unsafe space", engine)
    output.mkdir(parents=True)
    (output / "preserved").write_text("earlier attempt")
    with pytest.raises(ValueError, match="immutable"):
        preparation.prepare_churchroad(output, engine)
    assert (output / "preserved").read_text() == "earlier attempt" and not launches
