"""Pinned compiler preparation, with no downloads or native jobs in these tests."""

import hashlib
import json
from pathlib import Path
from typing import Any

import pytest

from benchmarking.processes import PilotProcessResult
from scripts import reproduction_prepare_eggcc as preparation
from scripts import source_tools


@pytest.fixture
def pipeline(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> tuple[Path, Path, Path, dict[str, Any], list[dict[str, Any]]]:
    monkeypatch.setattr(preparation, "ROOT", tmp_path)
    monkeypatch.setattr(preparation.platform, "system", lambda: "Darwin")
    monkeypatch.setattr(preparation.platform, "machine", lambda: "arm64")
    engine = tmp_path / "engine"
    engine.write_bytes(b"ordinary runtime")
    output = tmp_path / "benchmarks/local/reproduction/eggcc"
    build = tmp_path / "target/compatible"
    build.mkdir(parents=True)
    (build / "retained-cache").write_bytes(b"reuse")
    state: dict[str, Any] = {}
    commands: list[dict[str, Any]] = []
    for relative in [
        preparation.REPAIR_FIXTURE,
        "benchmarks/reproduction/patches/eggcc-build.diff",
        "benchmarks/reproduction/patches/eggcc-capture.diff",
    ]:
        path = tmp_path / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(b"checked patch")
    lock = b"original lock"
    monkeypatch.setattr(preparation, "LOCK_SHA256", hashlib.sha256(lock).hexdigest())
    monkeypatch.setattr(preparation, "CORE_PINS", {"Cargo.lock": hashlib.sha256(lock).hexdigest()})

    def acquire(preparer: source_tools.Preparation, name: str, url: str, revision: str) -> Path:
        source = preparer.directory / "sources" / name
        source.mkdir(parents=True)
        (source / "Cargo.lock").write_bytes(b"drift" if state.get("drift") == name else lock)
        commands.append({"name": "acquire", "source": name, "revision": revision, "url": url})
        return source

    def patch(self: source_tools.Preparation, checkout: Path, patch: Path) -> None:
        assert checkout.is_relative_to(self.directory / "sources")
        commands.append({"name": "patch", "patch": patch.name, "source": checkout.name})

    def run(command: list[str], cwd: Path, prefix: Path, **options: Any) -> PilotProcessResult:
        name = prefix.name.split("-", 1)[1]
        commands.append({"name": name, "command": command, "options": options})
        stdout, stderr = prefix.with_suffix(".stdout.log"), prefix.with_suffix(".stderr.log")
        stdout.write_text("")
        stderr.write_text("")
        if name == state.get("stop"):
            return PilotProcessResult("memory-limit", None, 0, 0, stdout, stderr, "cap")
        if name == "llvm-version":
            stdout.write_text("18.1.8")
        elif name == "rust-version":
            stdout.write_text("rustc 1.88.0\nhost: aarch64-apple-darwin")
        elif name == "core-regression":
            stdout.write_text(f"test result: ok. {state.get('regression_passes', 1)} passed; 0 failed;")
        elif name == "build":
            (build / "debug").mkdir()
            (build / "debug/eggcc").write_bytes(b"compiler")
            if not state.get("omit_tiger"):
                tiger = cwd / "target/debug/tiger"
                tiger.parent.mkdir(parents=True)
                tiger.write_bytes(b"native Tiger")
        return PilotProcessResult("success", 0, 0, 0, stdout, stderr, None)

    monkeypatch.setattr(preparation, "acquire_source", acquire)
    monkeypatch.setattr(preparation.Preparation, "apply_patch", patch)
    monkeypatch.setattr(source_tools, "run_bounded_command", run)
    return output, engine, build, state, commands


def test_prepares_original_compiler_and_tiger_with_checked_patches_and_normal_cache(pipeline: tuple) -> None:
    output, engine, build, _, launches = pipeline
    result = preparation.prepare_eggcc(output, engine, build_root=build)
    assert result["status"] == "success", result
    assert (build / "retained-cache").read_bytes() == b"reuse"
    acquisitions = [row for row in launches if row["name"] == "acquire"]
    assert [(row["source"], row["revision"]) for row in acquisitions] == [
        ("eggcc", preparation.REVISION),
        ("egglog-core", preparation.CORE_REVISION),
    ]
    assert [(row["source"], row["patch"]) for row in launches if row["name"] == "patch"] == [
        ("egglog-core", "eggcc-core-row-order.patch"),
        ("eggcc", "eggcc-build.diff"),
        ("eggcc", "eggcc-capture.diff"),
    ]
    jobs = [row for row in launches if "command" in row]
    assert all(row["options"]["require_guard"] for row in jobs)
    assert not any(arg.startswith("CARGO_HOME=") for row in jobs for arg in row["command"])
    assert jobs[-2]["name"] == "core-regression" and jobs[-1]["name"] == "build"
    settings = json.loads(Path(result["settings"]).read_text())["eggcc"]
    assert result["tiger"] in settings["identity_paths"]
    assert settings["configuration_blockers"][0]["extractor_substitution"] is False


@pytest.mark.parametrize(
    "fault,reason",
    [
        ({"omit_tiger": True}, "omitted"),
        ({"regression_passes": 0}, "exactly one"),
        ({"regression_passes": 2}, "exactly one"),
        ({"drift": "eggcc"}, "lockfile changed"),
        ({"drift": "egglog-core"}, "core repair source changed"),
    ],
)
def test_preparation_never_publishes_incomplete_products(pipeline: tuple, fault: dict, reason: str) -> None:
    output, engine, build, state, _ = pipeline
    state.update(fault)
    result = preparation.prepare_eggcc(output, engine, build_root=build)
    assert result["status"] == "blocked" and reason in result["reason"]
    assert not (output / "settings.json").exists()


def test_memory_stop_retains_evidence_and_does_not_build(pipeline: tuple) -> None:
    output, engine, build, state, launches = pipeline
    state["stop"] = "core-regression"
    result = preparation.prepare_eggcc(output, engine, build_root=build)
    assert result["status"] == "memory-limit"
    assert launches[-1]["name"] == "core-regression"
    assert not (output / "settings.json").exists()


def test_sources_must_be_fresh_and_durable(pipeline: tuple, tmp_path: Path) -> None:
    output, engine, build, _, _ = pipeline
    with pytest.raises(ValueError, match="must remain below"):
        preparation.prepare_eggcc(tmp_path / "other", engine, build_root=build)
    output.mkdir(parents=True)
    with pytest.raises(ValueError, match="fresh output"):
        preparation.prepare_eggcc(output, engine, build_root=build)
