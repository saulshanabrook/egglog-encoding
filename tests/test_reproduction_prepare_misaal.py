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


@pytest.mark.parametrize("changed_lock", [False, True])
def test_backend_build_uses_verified_original_source_and_rejects_lock_changes(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, changed_lock: bool
) -> None:
    archive = tmp_path / "egglog.tar.gz"
    lock = b"original locked dependency graph"
    with tarfile.open(archive, "w:gz") as tree:
        member = tarfile.TarInfo(f"egglog-{preparation.EGGLOG_REVISION}/Cargo.lock")
        member.size = len(lock)
        tree.addfile(member, io.BytesIO(lock))
    monkeypatch.setattr(preparation, "EGGLOG_ARCHIVE_SHA256", preparation.sha256_file(archive))
    monkeypatch.setattr(preparation, "EGGLOG_LOCK_SHA256", preparation.hashlib.sha256(lock).hexdigest())
    commands = []

    def step(self: preparation.Preparation, name: str, command: list[str], **kwargs: object) -> str:
        commands.append(command)
        if name == "backend-rust":
            return "rustc 1.91.0 (test)\nhost: aarch64-apple-darwin\n"
        if name == "backend-build":
            source = Path(str(kwargs["cwd"]))
            assert (source / "Cargo.lock").read_bytes() == lock
            binary = source / "target/debug/egglog"
            binary.parent.mkdir(parents=True)
            binary.write_text("native executable fixture")
            binary.chmod(0o700)
            if changed_lock:
                (source / "Cargo.lock").write_text("changed dependency graph")
        return ""

    monkeypatch.setattr(preparation.Preparation, "step", step)
    attempt = preparation.Preparation(tmp_path)
    if changed_lock:
        with pytest.raises(ValueError, match="changed the dependency lock"):
            preparation.build_backend(attempt)
        assert not (tmp_path / "backend.json").exists()
    else:
        binary = preparation.build_backend(attempt)
        assert json.loads((tmp_path / "backend.json").read_text())["sha256"] == preparation.sha256_file(binary)
    build = commands[-1]
    assert build[-8:] == ["cargo", "+1.91.0", "build", "--locked", "--jobs", "1", "--bin", "egglog"]


def test_backend_source_mismatch_stops_before_build(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    (tmp_path / "egglog.tar.gz").write_bytes(b"unverified source")
    commands = []

    def step(self: preparation.Preparation, name: str, command: list[str], **kwargs: object) -> str:
        commands.append(name)
        return ""

    monkeypatch.setattr(preparation.Preparation, "step", step)
    with pytest.raises(ValueError, match="archive differs"):
        preparation.build_backend(preparation.Preparation(tmp_path))
    assert commands == ["backend-download"]


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


def test_patch_requires_exact_context_and_owned_source(tmp_path: Path) -> None:
    attempt = preparation.Preparation(tmp_path)
    source = tmp_path / "sources/CMakeLists.txt"
    source.parent.mkdir()
    source.write_text("old\n")
    attempt.patch(source, [("old\n", "new\n")], "build-only")
    assert source.read_text() == "new\n"
    assert "-old\n+new\n" in (tmp_path / "patches/build-only.patch").read_text()
    with pytest.raises(ValueError, match="exactly one context"):
        attempt.patch(source, [("old\n", "invented\n")], "invalid")
    assert not (tmp_path / "patches/invalid.patch").exists()
    with pytest.raises(ValueError, match="outside"):
        attempt.patch(tmp_path / "outside", [("old", "new")], "outside")


def test_receipt_cannot_replace_previous_evidence(tmp_path: Path) -> None:
    receipt = tmp_path / "receipt.json"
    preparation.write_json(receipt, {"status": "failure"})
    with pytest.raises(FileExistsError):
        preparation.write_json(receipt, {"status": "success"})
    assert '"failure"' in receipt.read_text()


def test_cache_override_preserves_default_names(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    attempt = preparation.Preparation(tmp_path)
    modules = {"Halide": "halide", "x86": "x86", "ARM": "ARM", "HVX": "hvx"}
    for module, stem in modules.items():
        source = tmp_path / f"sources/MISAAL/lib/patterns/{module}.py"
        source.parent.mkdir(parents=True, exist_ok=True)
        source.write_text(
            'import os\nMISAAL_ROOT = "/source"\n'
            f'pickle_file_name = MISAAL_ROOT + "/lib/patterns/{stem}.pickle"\n'
            f'abstract_pickle_file_name = MISAAL_ROOT + "/lib/patterns/{stem}_abstract.pickle"\n'
        )
    preparation.patch_pattern_cache(attempt)
    for override in (None, "/attempt/pattern-cache"):
        if override is None:
            monkeypatch.delenv("MISAAL_PATTERN_CACHE_DIR", raising=False)
        else:
            monkeypatch.setenv("MISAAL_PATTERN_CACHE_DIR", override)
        for module, stem in modules.items():
            namespace: dict[str, object] = {}
            source = tmp_path / f"sources/MISAAL/lib/patterns/{module}.py"
            exec(compile(source.read_text(), str(source), "exec"), namespace)
            cache = override or "/source/lib/patterns"
            assert namespace["pickle_file_name"] == f"{cache}/{stem}.pickle"
            assert namespace["abstract_pickle_file_name"] == f"{cache}/{stem}_abstract.pickle"


INLINER_CONTEXT = """    if (!CF) return;

    // Map Arguments in the VMAP
    for (unsigned i = 0; i < CI->getNumOperands(); i++) {
        llvm::Value *ActualParam = CI->getArgOperand(i);

        llvm::Value *FormalParam = llvm::dyn_cast<llvm::Argument>((CF->arg_begin() + i));

        VMap[FormalParam] = ActualParam;
    }
"""


@pytest.mark.parametrize("drift", [False, True])
def test_wrapper_inliner_patch_is_narrow_and_rejects_context_drift(tmp_path: Path, drift: bool) -> None:
    attempt = preparation.Preparation(tmp_path)
    source = tmp_path / "sources/MISAAL/frontends/halide/src/CodeGen_LLVM.cpp"
    source.parent.mkdir(parents=True)
    original = "// retained prefix\n" + INLINER_CONTEXT + "// retained cloning/remapping body\n"
    if drift:
        original = original.replace("VMap[FormalParam]", "VMap[changed]")
    source.write_text(original)
    digest = preparation.sha256_file(source)
    if drift:
        with pytest.raises(ValueError, match="exactly one context"):
            preparation.patch_wrapper_inliner(attempt)
        assert source.read_text() == original
        assert not (tmp_path / "patches").exists()
        return
    preparation.patch_wrapper_inliner(attempt)
    changed = source.read_text()
    assert "i < CI->getNumOperands()" not in changed
    assert "i < CI->arg_size()" in changed
    assert "!CF->isVarArg() && CI->arg_size() == CF->arg_size()" in changed
    assert changed.startswith("// retained prefix\n") and changed.endswith("// retained cloning/remapping body\n")
    patch = tmp_path / "patches/halide-wrapper-inliner-arguments.patch"
    assert "-    for (unsigned i = 0; i < CI->getNumOperands(); i++)" in patch.read_text()
    assert json.loads(patch.with_suffix(".before.json").read_text())["sha256"] == digest
    assert json.loads(patch.with_suffix(".after.json").read_text())["sha256"] == preparation.sha256_file(source)
    assert not list(attempt.logs.iterdir())


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
    backend = preparation.build_backend(preparation.Preparation(directory), optimized_dev=True)
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
    backend = preparation.build_backend(preparation.Preparation(directory), optimized_dev=True)
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
        preparation.build_backend(preparation.Preparation(directory), optimized_dev=True)
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
        preparation.build_backend(preparation.Preparation(directory), optimized_dev=True)
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
        preparation.build_backend(preparation.Preparation(directory), optimized_dev=True)
    assert not (directory / "backend.json").exists()


@pytest.mark.parametrize(
    "mutation", ["unsafe-guard", "failed-result", "wrong-toolchain", "wrong-rust", "unbound-log", "guard-code"]
)
def test_optimized_backend_verifies_receipt_contract_beyond_file_hashes(
    tmp_path: Path, optimized_backend_build: BackendFixture, mutation: str
) -> None:
    directory = tmp_path / "attempt"
    directory.mkdir()
    preparation.build_backend(preparation.Preparation(directory), optimized_dev=True)
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
        preparation.build_backend(preparation.Preparation(tmp_path), optimized_dev=True)
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
            preparation.build_backend(preparation.Preparation(directory), optimized_dev=True)
    else:
        preparation.build_backend(preparation.Preparation(directory), optimized_dev=True)
        record = json.loads((directory / "backend.json").read_text())
        assert record["cargo_configs"][str(config)] == preparation.sha256_file(config)
