"""Durable Eggcc preparation contracts without native builds or downloads."""

import io
import json
import tarfile
from pathlib import Path

import pytest

from scripts import reproduction_prepare_eggcc as preparation


def source_archive(path: Path, files: dict[str, bytes]) -> None:
    """Create controlled original-source bytes for acquisition safety tests."""
    with tarfile.open(path, "w:gz") as archive:
        for name, data in files.items():
            member = tarfile.TarInfo(f"eggcc-{preparation.REVISION}/{name}")
            member.size = len(data)
            member.mode = 0o644
            archive.addfile(member, io.BytesIO(data))


def test_archive_hash_is_required_before_extracting(tmp_path: Path) -> None:
    archive = tmp_path / "source.tar.gz"
    source_archive(archive, {"Cargo.lock": b"lock"})
    checkout = tmp_path / "checkout"
    with pytest.raises(ValueError, match="archive differs"):
        preparation.unpack_source(archive, checkout)
    assert not checkout.exists()


def test_archive_traversal_is_rejected(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    archive = tmp_path / "source.tar.gz"
    source_archive(archive, {"../../outside": b"bad"})
    monkeypatch.setattr(preparation, "ARCHIVE_SHA256", preparation.sha256_file(archive))
    with pytest.raises(ValueError, match="member path"):
        preparation.unpack_source(archive, tmp_path / "checkout")
    assert not (tmp_path / "outside").exists()


def test_preparation_requires_durable_fresh_inputs(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(preparation, "ROOT", tmp_path)
    engine = tmp_path / "engine"
    engine.write_bytes(b"engine")
    with pytest.raises(ValueError, match="source and evidence must remain"):
        preparation.prepare_eggcc(tmp_path / "target/attempt", engine)
    output = tmp_path / "benchmarks/local/reproduction/attempt"
    output.mkdir(parents=True)
    with pytest.raises(ValueError, match="fresh output and build"):
        preparation.prepare_eggcc(output, engine)


@pytest.mark.parametrize("omit_tiger", [False, True])
def test_preparation_builds_actual_source_and_keeps_gurobi_blocked(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, omit_tiger: bool
) -> None:
    monkeypatch.setattr(preparation, "ROOT", tmp_path)
    monkeypatch.setattr(preparation.platform, "system", lambda: "Darwin")
    monkeypatch.setattr(preparation.platform, "machine", lambda: "arm64")
    engine = tmp_path / "engine"
    engine.write_bytes(b"ordinary engine")
    llvm = tmp_path / "llvm"
    monkeypatch.setattr(preparation, "LLVM", llvm)
    for relative in (
        "scripts/reproduction_prepare_eggcc.py",
        "scripts/reproduction_prepare_misaal.py",
        "scripts/eggcc_churchroad_complete.py",
        "scripts/reproduction_process.py",
        "benchmarking/pilot.py",
        "benchmarking/memory_guard.py",
        "llvm/bin/llvm-config",
        "llvm/lib/libLLVM.dylib",
    ):
        file = tmp_path / relative
        file.parent.mkdir(parents=True, exist_ok=True)
        file.write_bytes(b"dependency")
    tool = tmp_path / "native-tool"
    tool.write_bytes(b"native tool")
    monkeypatch.setattr(preparation.shutil, "which", lambda _: str(tool))
    archive = tmp_path / "original.tar.gz"
    lock = b"pinned dependencies"
    source_archive(
        archive,
        {
            "Cargo.toml": b'[package]\nname = "eggcc"\n',
            "Cargo.lock": lock,
            "src/main.rs": b"original compiler",
            "benchmarks/fact.bril": b"original benchmark",
        },
    )
    monkeypatch.setattr(preparation, "ARCHIVE_SHA256", preparation.sha256_file(archive))
    import hashlib

    monkeypatch.setattr(preparation, "LOCK_SHA256", hashlib.sha256(lock).hexdigest())
    monkeypatch.setattr(
        preparation, "patched_eggcc_sources", lambda _: {"src/main.rs": "original compiler\nobservation"}
    )
    commands: list[tuple[str, list[str]]] = []
    output = tmp_path / "benchmarks/local/reproduction/attempt"
    build = tmp_path / "target/disposable-eggcc"

    def step(self: preparation.Preparation, name: str, command: list[str], **kwargs: object) -> str:
        commands.append((name, command))
        if name == "llvm-version":
            return "18.1.8\n"
        if name == "rust-version":
            return "rustc 1.88.0\nhost: aarch64-apple-darwin\n"
        if name in ("rustc-path", "cargo-path"):
            return str(tool)
        if name == "download-source":
            Path(command[command.index("--output") + 1]).write_bytes(archive.read_bytes())
        if name == "build":
            binary = build / "debug/eggcc"
            binary.parent.mkdir(parents=True)
            binary.write_bytes(b"built compiler")
            if not omit_tiger:
                tiger = output / "sources/eggcc/target/debug/tiger"
                tiger.parent.mkdir(parents=True)
                tiger.write_bytes(b"built native Tiger")
        return ""

    monkeypatch.setattr(preparation.Preparation, "step", step)

    def no_nested_lock(*_: object) -> None:
        pytest.fail("in-process preparation must use the coordinator's existing job slot")

    monkeypatch.setattr(preparation, "exclusive_job", no_nested_lock)
    result = preparation.prepare_eggcc(output, engine, build_root=build)
    assert result["configuration_blockers"][0]["configuration"] == {
        "native_options": ["--tiger-ilp", "--ilp-solver", "gurobi"]
    }
    assert result["configuration_blockers"][0]["status"] == "blocked"
    assert not result["configuration_blockers"][0]["extractor_substitution"]
    assert (output / "sources/eggcc/benchmarks/fact.bril").read_bytes() == b"original benchmark"
    assert (output / "original-source.json").is_file()
    assert (output / "prepared-source.json").is_file()
    assert (output / "patches/workspace-isolation.patch").is_file()
    build_command = dict(commands)["build"]
    assert build_command[-7:] == ["cargo", "+1.88.0", "build", "--locked", "-j1", "--bin", "eggcc"]
    for flag in (
        "CARGO_PROFILE_DEV_DEBUG=0",
        "CARGO_INCREMENTAL=0",
        "RUSTC_WRAPPER=",
        "LIBRARY_PATH=/opt/homebrew/lib",
    ):
        assert flag in build_command
    assert all("gurobi" not in command and "--run-mode" not in command for _, command in commands)
    if omit_tiger:
        assert result["status"] == "blocked" and "native executable" in result["reason"]
        assert not (output / "settings.json").exists()
    else:
        assert result["status"] == "success"
        settings = json.loads((output / "settings.json").read_text())["eggcc"]
        assert settings["paths"]["checkout"] == str(output / "sources/eggcc")
        assert settings["paths"]["binary"] == str(build / "debug/eggcc")
        assert settings["configuration_blockers"] == result["configuration_blockers"]
