"""Preparation safety and receipt contracts; these never build native tools."""

import io
import json
import tarfile
from dataclasses import replace
from pathlib import Path
from typing import Any, Literal

import pytest

from benchmarking.processes import PilotProcessResult
from scripts import reproduction_prepare_misaal as preparation
from scripts import source_tools


def test_raw_hash_matches_capture_protocol(tmp_path: Path) -> None:
    source = tmp_path / "input"
    source.write_bytes(b"abc")
    assert preparation.sha256_file(source) == "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"


def test_guarded_failure_retains_request_and_stops(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    def fail(command: list[str], cwd: Path, prefix: Path, **kwargs: object) -> PilotProcessResult:
        assert command == ["a-compiler"]
        assert cwd == tmp_path
        assert kwargs == {
            "timeout_sec": 1800,
            "memory_limit_bytes": 10 * 1024**3,
            "allow_warning_pressure": False,
            "require_guard": True,
            "disk_reserve_bytes": 2 * 1024**3,
        }
        return PilotProcessResult("memory-limit", -9, 1.0, 6 * 1024**3, prefix, prefix, "over cap")

    monkeypatch.setattr(source_tools, "run_bounded_command", fail)
    attempt = preparation.Preparation(tmp_path)
    with pytest.raises(RuntimeError, match="memory-limit"):
        attempt.step("build", ["a-compiler"], timeout=1800)
    assert (tmp_path / "steps/001-build.request.json").is_file()
    assert '"status": "memory-limit"' in (tmp_path / "steps/001-build.result.json").read_text()


def test_receipt_cannot_replace_previous_evidence(tmp_path: Path) -> None:
    receipt = tmp_path / "receipt.json"
    preparation.write_json(receipt, {"status": "failure"})
    with pytest.raises(FileExistsError):
        preparation.write_json(receipt, {"status": "success"})
    assert '"failure"' in receipt.read_text()


BackendFixture = tuple[list[Any], dict[str, Path]]


@pytest.fixture
def optimized_backend_build(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> BackendFixture:
    """Exercise real receipt assembly with native/download work replaced by guarded fixtures."""
    files = {
        "Cargo.lock": b"locked graph",
        "Cargo.toml": b'[package]\nname="egglog"\n',
        "build.rs": b"fn main() {}\n",
        "src/main.rs": b"fn main() {}\n",
    }
    archive = io.BytesIO()
    with tarfile.open(fileobj=archive, mode="w:gz") as tree:
        for name, data in files.items():
            member = tarfile.TarInfo(f"egglog-{preparation.EGGLOG_REVISION}/{name}")
            member.size = len(data)
            tree.addfile(member, io.BytesIO(data))
    archive_bytes = archive.getvalue()
    monkeypatch.setattr(preparation, "EGGLOG_ARCHIVE_SHA256", preparation.hashlib.sha256(archive_bytes).hexdigest())
    monkeypatch.setattr(preparation, "EGGLOG_LOCK_SHA256", preparation.hashlib.sha256(files["Cargo.lock"]).hexdigest())
    tools = {}
    for name in ("rustc", "cargo"):
        tools[name] = tmp_path / name
        tools[name].write_text(f"{name} tool fixture")
        tools[name].chmod(0o700)
    commands = []

    def run(command: list[str], cwd: Path, prefix: Path, **kwargs: object) -> PilotProcessResult:
        name = prefix.name.partition("-")[2]
        commands.append((name, command, cwd, kwargs))
        stdout = prefix.with_suffix(".stdout.log")
        stderr = prefix.with_suffix(".stderr.log")
        text = ""
        if name == "backend-download":
            (prefix.parent.parent / "egglog.tar.gz").write_bytes(archive_bytes)
        elif name == "backend-rust":
            text = "rustc 1.91.0 (test)\nhost: aarch64-apple-darwin\n"
        elif name in {"backend-rustc-path", "backend-cargo-path"}:
            text = str(tools[command[-1]])
        elif name == "backend-build":
            target = Path(
                next(arg.removeprefix("CARGO_TARGET_DIR=") for arg in command if arg.startswith("CARGO_TARGET_DIR="))
            )
            binary = target / "debug/egglog"
            binary.parent.mkdir()
            binary.write_text("optimized backend executable fixture")
            binary.chmod(0o700)
        else:
            pytest.fail(f"backend-only preparation reached unrelated work: {name}")
        stdout.write_text(text)
        stderr.write_text("")
        return PilotProcessResult("success", 0, 0.1, 1024, stdout, stderr, None)

    monkeypatch.setattr(source_tools, "run_bounded_command", run)
    return commands, tools


def test_optimized_backend_fixed_profile_and_verified_receipt(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, optimized_backend_build: BackendFixture
) -> None:
    for key in [
        "RUSTFLAGS",
        "CARGO_ENCODED_RUSTFLAGS",
        "CARGO_PROFILE_DEV_DEBUG_ASSERTIONS",
        "CARGO_PROFILE_DEV_BUILD_OVERRIDE_OPT_LEVEL",
        "CARGO_BUILD_TARGET",
        "CARGO_TARGET_DIR",
        "RUSTC",
        "RUSTC_WRAPPER",
        "RUSTC_WORKSPACE_WRAPPER",
        "RUSTC_BOOTSTRAP",
    ]:
        monkeypatch.setenv(key, "must-not-leak")
    directory = tmp_path / "attempt"
    directory.mkdir()
    backend = preparation.build_backend(preparation.Preparation(directory))
    record = json.loads((directory / "backend.json").read_text())
    assert record["profile"] == preparation.BACKEND_PROFILE
    assert record["source_files"]["Cargo.lock"] == preparation.EGGLOG_LOCK_SHA256
    assert preparation.verified_backend_receipt(directory / "backend.json") == backend
    name, command, cwd, guard = optimized_backend_build[0][-1]
    assert name == "backend-build" and cwd == directory / f"egglog-{preparation.EGGLOG_REVISION}"
    assert command[-9:] == [
        str(optimized_backend_build[1]["cargo"]),
        "build",
        "--profile",
        "dev",
        "--locked",
        "--jobs",
        "1",
        "--bin",
        "egglog",
    ]
    assert f"RUSTC={optimized_backend_build[1]['rustc']}" in command
    assert optimized_backend_build[0][-2][1] == [str(optimized_backend_build[1]["rustc"]), "--version", "--verbose"]
    assert "CARGO_PROFILE_DEV_DEBUG_ASSERTIONS=true" in command
    assert "CARGO_PROFILE_DEV_OVERFLOW_CHECKS=true" in command
    assert "CARGO_PROFILE_DEV_OPT_LEVEL=3" in command
    assert "RUSTC_WRAPPER=" in command and "RUSTC_WORKSPACE_WRAPPER=" in command
    assert f"CARGO_HOME={directory / 'backend-cargo-home'}" in command
    for key in record["environment_unset"]:
        assert ["-u", key] in [command[i : i + 2] for i in range(len(command) - 1)]
    assert "must-not-leak" not in " ".join(command)
    assert guard["timeout_sec"] == 600 and guard["memory_limit_bytes"] == 10 * 1024**3
    assert guard["require_guard"] is True
    assert guard["disk_reserve_bytes"] == 2 * 1024**3
    assert guard["allow_warning_pressure"] is False
    assert set(record["guard_sources"]) == set(preparation.BACKEND_GUARD_SOURCES)
    assert not (directory / "sources/MISAAL").exists()
    assert not (directory / "halide-build").exists()


@pytest.mark.parametrize(
    "mutation",
    [
        "profile",
        "source",
        "extra-source",
        "lock",
        "archive",
        "binary",
        "tool",
        "request",
        "result",
        "stdout",
        "config",
        "snapshot",
    ],
)
def test_optimized_backend_receipt_rejects_drift(
    tmp_path: Path, optimized_backend_build: BackendFixture, mutation: str
) -> None:
    directory = tmp_path / "attempt"
    directory.mkdir()
    backend = preparation.build_backend(preparation.Preparation(directory))
    path = directory / "backend.json"
    record = json.loads(path.read_text())
    if mutation == "profile":
        record["profile"]["debug_assertions"] = False
        path.write_text(json.dumps(record))
    elif mutation in {"source", "extra-source", "lock"}:
        relative = {"source": "src/main.rs", "extra-source": "extra.rs", "lock": "Cargo.lock"}[mutation]
        (directory / f"egglog-{preparation.EGGLOG_REVISION}" / relative).write_text("changed")
    elif mutation == "archive":
        (directory / "egglog.tar.gz").write_bytes(b"changed")
    elif mutation == "binary":
        backend.write_text("changed")
    elif mutation == "tool":
        optimized_backend_build[1]["rustc"].write_text("changed")
    elif mutation in {"request", "result", "stdout"}:
        key = "build_request" if mutation == "request" else "build_result"
        target = directory / record[key]
        if mutation == "stdout":
            target = Path(json.loads(target.read_text())["stdout_path"])
        target.write_text("changed")
    elif mutation == "config":
        (directory / "backend-cargo-home/config.toml").write_text("[profile.dev]\ndebug-assertions=false\n")
    else:
        (directory / "backend-preparer.py").write_text("changed")
    with pytest.raises(ValueError):
        preparation.verified_backend_receipt(path)


def test_optimized_backend_refuses_parent_cargo_semantics_before_build(
    tmp_path: Path, optimized_backend_build: BackendFixture
) -> None:
    config = tmp_path / ".cargo/config.toml"
    config.parent.mkdir()
    config.write_text("[profile.dev.package.egglog]\nopt-level=0\n")
    directory = tmp_path / "attempt"
    directory.mkdir()
    with pytest.raises(ValueError, match="unreviewed Cargo configuration"):
        preparation.build_backend(preparation.Preparation(directory))
    assert "backend-build" not in [x[0] for x in optimized_backend_build[0]]
    assert not (directory / "backend.json").exists()


@pytest.mark.parametrize("status", ["failure", "timed-out", "memory-limit", "resource-stopped", "launch-refused"])
def test_optimized_backend_failed_build_retains_guard_receipts_without_publication(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    optimized_backend_build: BackendFixture,
    status: Literal["failure", "timed-out", "memory-limit", "resource-stopped", "launch-refused"],
) -> None:
    original = source_tools.run_bounded_command

    def run(command: list[str], cwd: Path, prefix: Path, **kwargs: Any) -> PilotProcessResult:
        if prefix.name.endswith("-backend-build") and status == "launch-refused":
            raise ValueError("resource guard refused to launch a workload: host reserve")
        result = original(command, cwd, prefix, **kwargs)
        if prefix.name.endswith("-backend-build"):
            assert status != "launch-refused"
            return replace(result, status=status, returncode=-9, message="fixture safety stop")
        return result

    monkeypatch.setattr(source_tools, "run_bounded_command", run)
    directory = tmp_path / "attempt"
    directory.mkdir()
    with pytest.raises((RuntimeError, ValueError)):
        preparation.build_backend(preparation.Preparation(directory))
    (result_path,) = (directory / "steps").glob("*-backend-build.result.json")
    assert json.loads(result_path.read_text())["status"] == status
    assert not (directory / "backend.json").exists()
    assert not (directory / "capture-request.json").exists()


@pytest.mark.parametrize("target", ["source", "toolchain", "configuration"])
def test_optimized_backend_rejects_changes_during_build(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, optimized_backend_build: BackendFixture, target: str
) -> None:
    original = source_tools.run_bounded_command

    def run(command: list[str], cwd: Path, prefix: Path, **kwargs: Any) -> PilotProcessResult:
        result = original(command, cwd, prefix, **kwargs)
        if prefix.name.endswith("-backend-build"):
            path = {
                "source": cwd / "src/main.rs",
                "toolchain": optimized_backend_build[1]["rustc"],
                "configuration": prefix.parent.parent / "backend-cargo-home/config.toml",
            }[target]
            path.write_text("changed during compilation")
        return result

    monkeypatch.setattr(source_tools, "run_bounded_command", run)
    directory = tmp_path / "attempt"
    directory.mkdir()
    with pytest.raises(ValueError):
        preparation.build_backend(preparation.Preparation(directory))
    assert not (directory / "backend.json").exists()


@pytest.mark.parametrize(
    "mutation", ["unsafe-guard", "failed-result", "wrong-toolchain", "wrong-rust", "unbound-log", "guard-code"]
)
def test_optimized_backend_verifies_receipt_contract_beyond_file_hashes(
    tmp_path: Path, optimized_backend_build: BackendFixture, mutation: str
) -> None:
    directory = tmp_path / "attempt"
    directory.mkdir()
    preparation.build_backend(preparation.Preparation(directory))
    receipt = directory / "backend.json"
    record = json.loads(receipt.read_text())
    if mutation in {"unsafe-guard", "failed-result", "unbound-log", "wrong-toolchain", "wrong-rust"}:
        if mutation == "unsafe-guard":
            path = directory / record["build_request"]
        elif mutation == "wrong-toolchain":
            (path,) = (directory / "steps").glob("*-backend-rustc-path.request.json")
        elif mutation == "wrong-rust":
            (path,) = (directory / "steps").glob("*-backend-rust.request.json")
        else:
            path = directory / record["build_result"]
        payload = json.loads(path.read_text())
        if mutation == "unsafe-guard":
            payload["require_guard"] = False
        elif mutation == "failed-result":
            payload["returncode"] = 1
        elif mutation in {"wrong-toolchain", "wrong-rust"}:
            payload["command"] = ["unrelated", "tool"]
        else:
            record["evidence"].pop(str(Path(payload["stderr_path"]).relative_to(directory)))
        path.write_text(json.dumps(payload))
        record["evidence"][str(path.relative_to(directory))] = preparation.sha256_file(path)
    else:
        record["guard_sources"]["benchmarking/memory_guard.py"] = "changed"
    receipt.write_text(json.dumps(record))
    with pytest.raises(ValueError):
        preparation.verified_backend_receipt(receipt)


@pytest.mark.parametrize("name", ["backend-target", "backend-cargo-home", "egglog.tar.gz"])
def test_optimized_backend_requires_fresh_paths_before_download(
    tmp_path: Path, optimized_backend_build: BackendFixture, name: str
) -> None:
    (tmp_path / name).symlink_to(tmp_path / "absent-target")
    with pytest.raises(ValueError, match="requires fresh"):
        preparation.build_backend(preparation.Preparation(tmp_path))
    assert not optimized_backend_build[0]


@pytest.mark.parametrize("mode", ["empty", "disabled-wrapper", "absolute-wrapper", "symlink"])
def test_optimized_backend_ancestor_config_is_narrowly_reviewed(
    tmp_path: Path, optimized_backend_build: BackendFixture, mode: str
) -> None:
    config = tmp_path / ".cargo/config"
    config.parent.mkdir()
    if mode == "symlink":
        config.symlink_to(tmp_path / "absent-config")
    else:
        wrapper = "/opt/homebrew/opt/kache/bin/kache" if mode == "absolute-wrapper" else "kache"
        config.write_text(f'[build]\nrustc-wrapper = "{wrapper}"\n' if mode != "empty" else "")
    directory = tmp_path / "attempt"
    directory.mkdir()
    if mode == "symlink":
        with pytest.raises(ValueError, match="symlinked Cargo configuration"):
            preparation.build_backend(preparation.Preparation(directory))
    else:
        preparation.build_backend(preparation.Preparation(directory))
        record = json.loads((directory / "backend.json").read_text())
        assert record["cargo_configs"][str(config)] == preparation.sha256_file(config)


def test_versioned_patch_applies_exact_bytes_and_rejects_drift_and_external_source(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    import subprocess

    # Replace only the resource monitor; execute both git commands for real.
    def execute(command: list[str], cwd: Path, prefix: Path, **kwargs: Any) -> PilotProcessResult:
        out, err = prefix.with_suffix(".stdout"), prefix.with_suffix(".stderr")
        with out.open("wb") as stdout, err.open("wb") as stderr:
            result = subprocess.run(command, cwd=cwd, stdout=stdout, stderr=stderr, check=False)
        return PilotProcessResult(
            "success" if result.returncode == 0 else "failure", result.returncode, 0, 0, out, err, None
        )

    monkeypatch.setattr(source_tools, "run_bounded_command", execute)
    patch = tmp_path / "repair.diff"
    patch.write_text("--- a/source.txt\n+++ b/source.txt\n@@ -1,3 +1,3 @@\n context\n-old\n+repaired\n tail\n")
    digest = preparation.sha256_file(patch)
    for changed in (False, True):
        attempt_dir = tmp_path / str(changed)
        checkout = attempt_dir / "sources/author"
        checkout.mkdir(parents=True)
        source = checkout / "source.txt"
        original = "context\n" + ("unexpected" if changed else "old") + "\ntail\n"
        source.write_text(original)
        attempt = preparation.Preparation(attempt_dir)
        if changed:
            with pytest.raises(RuntimeError, match="repair-check: failure"):
                attempt.apply_patch(checkout, patch)
            assert source.read_text() == original
            assert len(list(attempt.logs.glob("*.request.json"))) == 1
        else:
            attempt.apply_patch(checkout, patch)
            assert source.read_bytes() == b"context\nrepaired\ntail\n"
            assert len(list(attempt.logs.glob("*.request.json"))) == 2
        retained = attempt_dir / "patches/repair.diff"
        assert retained.read_bytes() == patch.read_bytes()
        assert json.loads(retained.with_suffix(".json").read_text())["patch_sha256"] == digest
        with pytest.raises(ValueError, match="outside this preparation"):
            attempt.apply_patch(tmp_path, patch)
