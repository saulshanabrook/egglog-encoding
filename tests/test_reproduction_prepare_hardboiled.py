"""Fail-closed prerequisite tests; no native builds, generators or downloads."""

import json
from pathlib import Path

import pytest

from scripts import reproduction_prepare_hardboiled as preparation


def test_llvm_preflight_rejects_missing_gpu_backend(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    def step(self: preparation.Preparation, name: str, command: list[str], **kwargs: object) -> str:
        return "18.1.8\n" if name == "llvm-version" else "WebAssembly X86 ARM AArch64\n"

    monkeypatch.setattr(preparation.Preparation, "step", step)
    with pytest.raises(ValueError, match="NVPTX"):
        preparation.inspect_llvm(preparation.Preparation(tmp_path), tmp_path / "llvm")
    assert not (tmp_path / "sources").exists()


def test_llvm_preflight_rejects_unreviewed_version(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(preparation.Preparation, "step", lambda *_args, **_kwargs: "19.1.5\n")
    with pytest.raises(ValueError, match="inspected LLVM 18.1.8"):
        preparation.inspect_llvm(preparation.Preparation(tmp_path), tmp_path / "llvm")


def test_checkout_must_match_exact_pin(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    commands: list[list[str]] = []

    def step(self: preparation.Preparation, name: str, command: list[str], **kwargs: object) -> str:
        commands.append(command)
        return "0" * 40

    monkeypatch.setattr(preparation.Preparation, "step", step)
    with pytest.raises(ValueError, match="revision differs"):
        preparation.acquire_source(
            preparation.Preparation(tmp_path), "source", "https://example.test/source.git", "1" * 40
        )
    assert commands[-2] == ["git", "checkout", "--detach", "1" * 40]
    assert commands[-1] == ["git", "rev-parse", "HEAD"]


def test_preparation_builds_pinned_tools_and_stops_before_canaries(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    (tmp_path / "benchmarks").mkdir()
    catalog = json.loads(json.dumps({"cases": [{"id": key, **case} for key, case in preparation.CANARIES.items()]}))
    (tmp_path / "benchmarks/catalog.json").write_text(json.dumps(catalog))
    monkeypatch.setattr(preparation, "ROOT", tmp_path)
    monkeypatch.setattr(preparation.platform, "system", lambda: "Darwin")
    monkeypatch.setattr(preparation.platform, "machine", lambda: "arm64")
    # These stand for existing coordinator support files, not source dependencies.
    for name in ("reproduction_prepare_hardboiled.py", "reproduction_prepare_misaal.py", "reproduction_process.py"):
        file = tmp_path / "scripts" / name
        file.parent.mkdir(exist_ok=True)
        file.write_text("support")
    for name in ("pilot.py", "memory_guard.py"):
        file = tmp_path / "benchmarking" / name
        file.parent.mkdir(exist_ok=True)
        file.write_text("support")
    directory = tmp_path / "attempt"
    directory.mkdir()
    monkeypatch.setattr(preparation, "inspect_llvm", lambda *_: {"files": {}})
    commands: list[tuple[str, list[str], dict[str, object]]] = []

    def step(self: preparation.Preparation, name: str, command: list[str], **kwargs: object) -> str:
        commands.append((name, command, kwargs))
        if name.endswith("-clone"):
            Path(command[-1]).mkdir()
        elif name == "HardBoiled-head":
            checkout = directory / "sources/HardBoiled"
            for case in preparation.CANARIES.values():
                source = checkout / str(case["source"])
                source.parent.mkdir(parents=True, exist_ok=True)
                source.write_text("original source")
            return preparation.HARDBOILED_REVISION
        elif name == "sidecar-head":
            (directory / "sources/sidecar/Cargo.toml").write_text('[package]\nname = "sidecar"\n')
            return preparation.SIDECAR_REVISION
        elif name == "sidecar-egglog-gitlink":
            return f"160000 commit {preparation.EGGLOG_REVISION}\tegglog\n"
        elif name == "sidecar-egglog-head":
            return preparation.EGGLOG_REVISION
        elif name == "rust-version":
            return "rustc 1.92.0\nhost: aarch64-apple-darwin\n"
        elif name in ("rustc-path", "cargo-path"):
            executable = directory / name
            executable.write_bytes(b"native rust executable")
            return str(executable)
        elif name == "sidecar-build":
            assert (
                (directory / "sources/sidecar/Cargo.toml").read_text().endswith('\n[workspace]\nexclude = ["egglog"]\n')
            )
            binary = directory / "sidecar-target/debug/egglog-halide-sidecar"
            binary.parent.mkdir(parents=True)
            binary.write_bytes(b"original sidecar")
        elif name == "halide-configure":
            build = directory / "halide-build"
            build.mkdir()
            (build / "CMakeCache.txt").write_text("configured")
            (build / "compile_commands.json").write_text(
                json.dumps(
                    [
                        {
                            "file": "ExtractTileOperations.cpp",
                            "command": "clang++ -DWITH_X86 -DWITH_WEBASSEMBLY -DWITH_NVPTX",
                        }
                    ]
                )
            )
        elif name == "halide-build":
            for relative in ("src/libHalide.dylib", "include/Halide.h"):
                file = directory / "halide-build" / relative
                file.parent.mkdir(exist_ok=True)
                file.write_bytes(b"built compiler")
        return ""

    monkeypatch.setattr(preparation.Preparation, "step", step)
    settings = preparation.prepare(directory, tmp_path / "llvm")
    requests = json.loads((directory / "canaries.json").read_text())
    assert len(requests) == 2
    assert all(request["status"] == "prepared-not-run" and not request["device_execution"] for request in requests)
    assert json.loads(settings.read_text())["hardboiled"]["revision"] == preparation.HARDBOILED_REVISION
    assert json.loads(settings.read_text())["hardboiled"]["paths"]["egglog"] == str(
        tmp_path / "target/release/egglog-experimental"
    )
    assert str(directory / "halide-build/include") in json.loads(settings.read_text())["hardboiled"]["identity_paths"]
    by_name = {name: (command, kwargs) for name, command, kwargs in commands}
    assert by_name["halide-build"][0][-2:] == ["--parallel", "1"]
    assert by_name["halide-build"][1]["timeout"] == 1800
    assert "--locked" in by_name["sidecar-build"][0] and "--jobs" in by_name["sidecar-build"][0]
    assert "-DHalide_WASM_BACKEND=OFF" in by_name["halide-configure"][0]
    assert "-DWITH_SERIALIZATION=OFF" in by_name["halide-configure"][0]
    assert by_name["sidecar-submodule"][0][2] == "url.https://github.com/.insteadOf=git@github.com:"
    assert all("generator" not in name and "capture" not in name for name, _, _ in commands)
    # A settings file cannot be emitted for a changed graph-generating parameter.
    settings.unlink()
    catalog["cases"][1]["configuration"]["M"] = 2048
    (tmp_path / "benchmarks/catalog.json").write_text(json.dumps(catalog))
    with pytest.raises(ValueError, match="catalog source/configuration changed"):
        preparation.write_canary_settings(
            directory,
            directory / "sources/HardBoiled",
            directory / "halide-build",
            directory / "sidecar-target/debug/egglog-halide-sidecar",
            tmp_path / "llvm",
        )
    assert not settings.exists()


def test_missing_library_cannot_create_settings(tmp_path: Path) -> None:
    with pytest.raises(ValueError, match="missing nonempty built prerequisite"):
        preparation.write_canary_settings(
            tmp_path, tmp_path / "source", tmp_path / "build", tmp_path / "sidecar", tmp_path / "llvm"
        )
    assert not (tmp_path / "settings.json").exists()
