"""DialEgg prerequisite contracts without executing native compilers or workloads."""

import hashlib
import io
import json
import tarfile
from pathlib import Path

import pytest

from scripts import reproduction_prepare_dialegg as preparation


def backend_archive(path: Path, manifest: bytes, lock: bytes) -> None:
    """Make controlled pinned-workspace fixture bytes."""
    with tarfile.open(path, "w:gz") as archive:
        for name, content in {"Cargo.toml": manifest, "Cargo.lock": lock}.items():
            member = tarfile.TarInfo(f"egg-smol-{preparation.BACKEND_REVISION}/{name}")
            member.size = len(content)
            archive.addfile(member, io.BytesIO(content))


def test_original_workspace_is_not_appended(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    manifest = b'[package]\nname = "egglog"\n[workspace]\nmembers = ["web-demo"]\n'
    lock = b"original lock"
    archive = tmp_path / "source.tar.gz"
    backend_archive(archive, manifest, lock)
    monkeypatch.setattr(preparation, "BACKEND_ARCHIVE_SHA256", preparation.sha256_file(archive))
    monkeypatch.setattr(preparation, "BACKEND_MANIFEST_SHA256", hashlib.sha256(manifest).hexdigest())
    monkeypatch.setattr(preparation, "BACKEND_LOCK_SHA256", hashlib.sha256(lock).hexdigest())
    source = tmp_path / "source"
    files = preparation.unpack_backend(archive, source)
    assert (source / "Cargo.toml").read_bytes() == manifest
    assert files["Cargo.toml"] == preparation.BACKEND_MANIFEST_SHA256
    assert (source / "Cargo.lock").read_bytes() == lock


def test_unpinned_archive_is_not_extracted(tmp_path: Path) -> None:
    archive = tmp_path / "source.tar.gz"
    archive.write_bytes(b"different archive")
    with pytest.raises(ValueError, match="archive differs"):
        preparation.unpack_backend(archive, tmp_path / "source")
    assert not (tmp_path / "source").exists()


def test_linked_dependencies_handle_cycles_and_dyld_cache(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    attempt = preparation.Preparation(tmp_path)
    llvm = tmp_path / "llvm"
    library = llvm / "lib/libMLIR.dylib"
    library.parent.mkdir(parents=True)
    library.write_bytes(b"dynamic library")
    binary = tmp_path / "backend"
    binary.write_bytes(b"native binary")
    commands = []

    def step(self: preparation.Preparation, name: str, command: list[str], **kwargs: object) -> str:
        commands.append(command)
        return (
            f"{command[-1]}:\n\t@rpath/libMLIR.dylib (compatibility version 0.0.0)\n"
            "\t/usr/lib/libSystem.B.dylib (compatibility version 1.0.0)\n"
        )

    monkeypatch.setattr(preparation.Preparation, "step", step)
    result = preparation.linked_libraries(attempt, [binary], llvm)
    assert result == {
        "files": {str(library): preparation.sha256_file(library)},
        "system_install_names": ["/usr/lib/libSystem.B.dylib"],
    }
    assert len(commands) == 2
    library.unlink()
    with pytest.raises(ValueError, match="unresolved native dependency"):
        preparation.linked_libraries(attempt, [binary], llvm)


@pytest.mark.parametrize("missing_backend", [False, True])
def test_source_build_settings_use_real_original_backend(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, missing_backend: bool
) -> None:
    monkeypatch.setattr(preparation, "ROOT", tmp_path)
    monkeypatch.setattr(preparation.platform, "system", lambda: "Darwin")
    monkeypatch.setattr(preparation.platform, "machine", lambda: "arm64")
    llvm = tmp_path / "llvm"
    monkeypatch.setattr(preparation, "LLVM", llvm)
    for relative in (
        "llvm/bin/clang++",
        "llvm/bin/llvm-config",
        "llvm/lib/libMLIROptLib.a",
        "llvm/lib/libMLIR.dylib",
        "llvm/lib/libLLVM.dylib",
        "llvm/include/mlir/IR/MLIRContext.h",
        "llvm/lib/cmake/llvm/LLVMConfig.cmake",
        "llvm/lib/cmake/mlir/MLIRConfig.cmake",
        "scripts/reproduction_prepare_dialegg.py",
        "scripts/source_tools.py",
        "scripts/reproduction_prepare_misaal.py",
        "scripts/reproduction_process.py",
        "scripts/dialegg_capture.py",
        "scripts/dialegg_compat.py",
        "benchmarking/processes.py",
        "benchmarking/memory_guard.py",
    ):
        path = tmp_path / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(b"prerequisite")
    engine = tmp_path / "engine"
    engine.write_bytes(b"ordinary engine")
    tool = tmp_path / "native-tool"
    tool.write_bytes(b"tool")
    monkeypatch.setattr(preparation.shutil, "which", lambda _: str(tool))
    archive = tmp_path / "source.tar.gz"
    manifest = b'[package]\nname = "egglog"\n[workspace]\n'
    lock = b"original lock"
    backend_archive(archive, manifest, lock)
    monkeypatch.setattr(preparation, "BACKEND_ARCHIVE_SHA256", preparation.sha256_file(archive))
    monkeypatch.setattr(preparation, "BACKEND_MANIFEST_SHA256", hashlib.sha256(manifest).hexdigest())
    monkeypatch.setattr(preparation, "BACKEND_LOCK_SHA256", hashlib.sha256(lock).hexdigest())
    output = tmp_path / "benchmarks/local/reproduction/attempt"
    build = tmp_path / "target/backend"
    commands: list[tuple[str, list[str]]] = []

    def step(self: preparation.Preparation, name: str, command: list[str], **kwargs: object) -> str:
        commands.append((name, command))
        if name == "llvm-version":
            return "18.1.8\n"
        if name == "rust-version":
            return "rustc 1.88.0\nhost: aarch64-apple-darwin\n"
        if name in ("rustc-path", "cargo-path"):
            return str(tool)
        if name == "backend-download":
            Path(command[command.index("--output") + 1]).write_bytes(archive.read_bytes())
        if name == "backend-build" and not missing_backend:
            binary = build / "debug/egglog"
            binary.parent.mkdir(parents=True)
            binary.write_bytes(b"original cost-action engine")
        return ""

    def acquire(self: preparation.Preparation, name: str, url: str, revision: str) -> Path:
        assert url == "https://github.com/AzizZayed/dialegg-cgo-artifact.git"
        assert revision == preparation.DIALEGG_REVISION
        source = output / "sources" / name
        (source / "src").mkdir(parents=True)
        for name in ("base.egg", "EqualitySaturationPass.cpp", "Egglog.cpp"):
            (source / "src" / name).write_bytes(b"original frontend")
        return source

    monkeypatch.setattr(preparation.Preparation, "step", step)
    monkeypatch.setattr(preparation, "acquire_source", acquire)
    monkeypatch.setattr(preparation, "linked_libraries", lambda *_: {"files": {}, "system_install_names": []})

    def no_lock(*_: object) -> None:
        pytest.fail("callable API must not take a nested heavy-job lock")

    monkeypatch.setattr(preparation, "exclusive_job", no_lock)
    result = preparation.prepare_dialegg(output, engine, build_root=build)
    assert (output / "sources/cost-action-egglog/Cargo.toml").read_bytes() == manifest
    assert result["source_patches"] == []
    command = dict(commands)["backend-build"]
    assert command[-7:] == ["cargo", "+1.88.0", "build", "--locked", "-j1", "--bin", "egglog"]
    assert "CARGO_PROFILE_DEV_DEBUG=0" in command and "CARGO_INCREMENTAL=0" in command
    assert all("clang++" not in command[0] and "--run-mode" not in command for _, command in commands)
    if missing_backend:
        assert result["status"] == "blocked" and "omitted" in result["reason"]
        assert not (output / "settings.json").exists()
    else:
        assert result["status"] == "success"
        settings = json.loads((output / "settings.json").read_text())["dialegg"]
        assert settings["paths"] == {
            "dialegg_source": str(output / "sources/dialegg"),
            "llvm18_prefix": str(llvm),
            "native_egglog": str(build / "debug/egglog"),
            "egglog": str(engine),
        }
        assert settings["backend_revision"] == preparation.BACKEND_REVISION
