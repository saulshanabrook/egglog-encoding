"""Preparation safety and receipt contracts; these never build native tools."""

import io
import json
import subprocess
import sys
import tarfile
from contextlib import nullcontext
from dataclasses import replace
from pathlib import Path
from typing import Any, Literal

import pytest

from benchmarking.pilot import PilotProcessResult
from scripts import reproduction_prepare_misaal as preparation


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
            "memory_limit_bytes": 5 * 1024**3,
            "allow_warning_pressure": True,
            "require_guard": True,
            "disk_reserve_bytes": 2 * 1024**3,
        }
        return PilotProcessResult("memory-limit", -9, 1.0, 6 * 1024**3, prefix, prefix, "over cap")

    monkeypatch.setattr(preparation, "run_bounded_command", fail)
    attempt = preparation.Preparation(tmp_path)
    with pytest.raises(RuntimeError, match="memory-limit"):
        attempt.step("build", ["a-compiler"], timeout=1800)
    assert (tmp_path / "steps/001-build.request.json").is_file()
    assert '"status": "memory-limit"' in (tmp_path / "steps/001-build.result.json").read_text()


def test_source_environment_discards_ambient_paths_and_preserves_setup_paths(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    misaal = tmp_path / "sources/MISAAL"
    misaal.mkdir(parents=True)
    python = tmp_path / "python/bin/python"
    python.parent.mkdir(parents=True)
    python.symlink_to(sys.executable)
    paths = {
        "PYTHONPATH": f"{misaal}/lib",
        "DYLD_LIBRARY_PATH": f"{misaal}/Hydride/distrib/lib",
        "LD_LIBRARY_PATH": f"{misaal}/Hydride/legalizers",
    }
    controls = {
        "MISAAL_SRC": str(misaal),
        "MISAAL_ROOT_DIR": str(misaal),
        "HYDRIDE_DIR": str(misaal / "Hydride"),
        "HYDRIDE_ROOT": str(misaal / "Hydride"),
    }
    (misaal / "setup.sh").write_text(
        "\n".join(
            [f'export {key}="{value}:${key}"' for key, value in paths.items()]
            + [f'export {key}="{value}"' for key, value in controls.items()]
        )
        + "\n"
    )
    for key in paths:
        monkeypatch.setenv(key, f"/old-artifact/{key}:/old-tool/{key}")

    class ReachedImports(Exception):
        pass

    def run(command: list[str], cwd: Path, prefix: Path, **kwargs: object) -> PilotProcessResult:
        name = prefix.name.partition("-")[2]
        if name == "rose-imports":
            raise ReachedImports
        assert name in {
            "legalizer-load",
            "python-environment",
            "python-dependencies",
            "python-freeze",
            "source-environment",
        }
        output = (
            subprocess.check_output(command, cwd=cwd, text=True, timeout=10)
            if name == "source-environment"
            else "x86-hydride-legalize"
        )
        stdout = prefix.with_suffix(".stdout.log")
        stderr = prefix.with_suffix(".stderr.log")
        stdout.write_text(output)
        stderr.write_text("")
        return PilotProcessResult("success", 0, 0.0, 0, stdout, stderr, None)

    monkeypatch.setattr(preparation, "run_bounded_command", run)
    attempt = preparation.Preparation(tmp_path)
    with pytest.raises(ReachedImports):
        preparation.finish_native(attempt, tmp_path / "backend")
    captured = json.loads((attempt.logs / "005-source-environment.stdout.log").read_text())
    assert captured == {**{key: f"{value}:" for key, value in paths.items()}, **controls}
    request = json.loads((attempt.logs / "005-source-environment.request.json").read_text())
    assert request["command"][:8] == [
        "/usr/bin/env",
        "-u",
        "PYTHONPATH",
        "-u",
        "DYLD_LIBRARY_PATH",
        "-u",
        "LD_LIBRARY_PATH",
        "/bin/bash",
    ]
    imports = json.loads((attempt.logs / "006-rose-imports.request.json").read_text())
    assert all(f"{key}={value}" in imports["command"] for key, value in captured.items())


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


def test_wide_constant_repair_preserves_all_decimal_values(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    backend = tmp_path / "backend"
    backend.write_bytes(b"pinned backend")
    monkeypatch.setattr(preparation, "EGGLOG_SHA256", preparation.sha256_file(backend))
    (tmp_path / "identity.json").write_text(
        json.dumps(
            {
                "misaal_revision": preparation.MISAAL_REVISION,
                "hydride_revision": preparation.HYDRIDE_REVISION,
            }
        )
    )
    steps = tmp_path / "steps"
    steps.mkdir()
    stderr = steps / "018-legalizer-build.stderr.log"
    stderr.write_text("integer literal is too large to be represented in any integer type")
    (steps / "018-legalizer-build.result.json").write_text(
        json.dumps(
            {
                "status": "failure",
                "stderr_path": str(stderr),
            }
        )
    )
    source = (
        tmp_path
        / "sources/MISAAL/Hydride/codegen-generator/tools/low-level-codegen/InstSelectors/x86/x86LegalizerAllArgs.cpp"
    )
    source.parent.mkdir(parents=True)
    values = [2**width - 1 for width in (128, 256, 512)] * 4
    source.write_text("\n".join(f"isAMatch(CI, 3, {value})" for value in values) + "\nisAMatch(CI, 3, 12)\n")
    commands: list[list[str]] = []

    def step(self: preparation.Preparation, name: str, command: list[str]) -> str:
        commands.append(command)
        return ""

    monkeypatch.setattr(preparation.Preparation, "step", step)
    monkeypatch.setattr(preparation, "finish_native", lambda *_: tmp_path / "request.json")
    preparation.repair_wide_literals(tmp_path, backend)
    assert source.read_text().splitlines() == [
        *(f'isAMatch(CI, 3, int512_t("{value}"))' for value in values),
        "isAMatch(CI, 3, 12)",
    ]
    assert len(commands) == 1 and commands[0][-2:] == ["--parallel", "1"]
    assert (tmp_path / "patches/legalizer-exact-wide-constants.patch").is_file()


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


def test_fresh_wide_constant_patch_rejects_changed_upstream(tmp_path: Path) -> None:
    attempt = preparation.Preparation(tmp_path)
    source = (
        tmp_path
        / "sources/MISAAL/Hydride/codegen-generator/tools/low-level-codegen/InstSelectors/x86/x86LegalizerAllArgs.cpp"
    )
    source.parent.mkdir(parents=True)
    value = 2**128 - 1
    original = f"isAMatch(CI, 3, {value})\n" * 11
    source.write_text(original)
    with pytest.raises(ValueError, match="expected the 12 observed oversized literals, found 11"):
        preparation.patch_wide_literals(attempt)
    assert source.read_text() == original
    assert not (tmp_path / "patches/legalizer-exact-wide-constants.patch").exists()
    source.write_text(original + f"isAMatch(CI, 3, {value})\n")
    preparation.patch_wide_literals(attempt)
    assert source.read_text() == f'isAMatch(CI, 3, int512_t("{value}"))\n' * 12
    assert not list((tmp_path / "steps").iterdir())


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


@pytest.mark.parametrize("selector_drift", [False, True])
def test_fresh_preparation_repairs_sources_before_native_builds(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, selector_drift: bool
) -> None:
    backend = tmp_path / "backend"
    backend.write_text("test backend")
    monkeypatch.setattr(preparation, "EGGLOG_SHA256", preparation.sha256_file(backend))
    monkeypatch.setattr(preparation.platform, "system", lambda: "Darwin")
    monkeypatch.setattr(preparation.platform, "machine", lambda: "arm64")
    boost = tmp_path / "boost_1_81_0.tar.bz2"
    boost.write_bytes(b"test boost")
    monkeypatch.setattr(preparation, "BOOST_SHA256", preparation.sha256_file(boost))
    legalizer_source = tmp_path / "sources/MISAAL/Hydride/codegen-generator/tools/low-level-codegen"
    selector = legalizer_source / "InstSelectors/x86/x86LegalizerAllArgs.cpp"
    matching_branch = (
        "class X86Legalizer : public Legalizer {\npublic:\n"
        "virtual bool legalize(Instruction *I) {\n"
        "  if (matches(I)) {\n"
        "    InstToInstMap[I] = replacement;\n"
        "    ToBeRemoved.insert(I);\n"
        "    return true;\n"
        "  }\n"
    )
    tail = "\n    \n}\n    \n\n};\n\n\nbool X86LegalizationPass::runOnFunction(Function &F) {\n"
    if selector_drift:
        tail = tail.replace("};", "}; // changed upstream")
    pass_body = "  Legalizer *L = new X86Legalizer();\n  return L->legalize(F);\n}\n"
    value = 2**128 - 1
    original = matching_branch + f"  isAMatch(CI, 3, {value});\n" * 12 + tail + pass_body
    calls = []

    def literal_repair(attempt: preparation.Preparation) -> None:
        # This test isolates ordering from the separate source-pinned literal
        # materializer tests. It must run before wide/SIMD/no-match changes.
        assert attempt.directory == tmp_path
        assert selector.read_text() == original
        calls.append("literal-repair")

    monkeypatch.setattr(preparation, "patch_selector_literals", literal_repair)

    class ReachedLegalizerBuild(Exception):
        pass

    def step(self: preparation.Preparation, name: str, command: list[str], **kwargs: object) -> str:
        calls.append(name)
        if name == "misaal-clone":
            frontend = tmp_path / "sources/MISAAL/frontends/halide"
            (frontend / "src").mkdir(parents=True)
            (frontend / "dependencies/llvm").mkdir(parents=True)
            (frontend / "src/CodeGen_LLVM.cpp").write_text(INLINER_CONTEXT)
            (frontend / "src/CMakeLists.txt").write_text("    HydrideCodeGen.cpp\n")
            (frontend / "dependencies/llvm/CMakeLists.txt").write_text("if (${OPTION} OR Halide_SHARED_LLVM)\n")
        if name == "hydride-clone":
            selector.parent.mkdir(parents=True)
            selector.write_text(original)
            (legalizer_source / "CMakeLists.txt").write_text(
                "add_library(x86LegalizerAllArgs SHARED ${x86_legalizer})\n"
            )
        if name == "misaal-head":
            return preparation.MISAAL_REVISION
        if name == "hydride-head":
            return preparation.HYDRIDE_REVISION
        if name == "halide-configure":
            source = tmp_path / "sources/MISAAL/frontends/halide/src/CodeGen_LLVM.cpp"
            assert "i < CI->arg_size()" in source.read_text()
            assert (tmp_path / "patches/halide-wrapper-inliner-arguments.after.json").is_file()
            assert not any(arg.startswith("-DCMAKE_CXX_FLAGS_RELEASE=") for arg in command)
        if name == "legalizer-configure":
            assert "-DCMAKE_CXX_FLAGS_RELEASE=-O0 -DNDEBUG" in command
            assert f"-DCMAKE_CXX_FLAGS=-I{tmp_path}/boost_1_81_0" in command
        if name == "legalizer-build":
            assert command[-2:] == ["--parallel", "1"]
            raise ReachedLegalizerBuild
        return ""

    monkeypatch.setattr(preparation.Preparation, "step", step)
    if selector_drift:
        with pytest.raises(ValueError, match="legalizer-no-match-return expected exactly one context"):
            preparation.prepare(tmp_path, backend)
        assert calls[-1] == "literal-repair"
        assert not (tmp_path / "patches/legalizer-no-match-return.patch").exists()
        return
    with pytest.raises(ReachedLegalizerBuild):
        preparation.prepare(tmp_path, backend)
    assert calls[-1] == "legalizer-build"
    expected = original.replace(f"isAMatch(CI, 3, {value})", f'isAMatch(CI, 3, int512_t("{value}"))')
    expected = expected.replace(
        pass_body, pass_body.replace("  return L->legalize(F);", "  L->bitsimd = false;\n  return L->legalize(F);")
    )
    expected = expected.replace(tail, tail.replace("\n}\n", "\n  return false;\n}\n", 1))
    assert selector.read_text() == expected
    assert selector.read_text().startswith(matching_branch)
    patch = (tmp_path / "patches/legalizer-no-match-return.patch").read_text()
    assert [line for line in patch.splitlines() if line.startswith("+") and not line.startswith("+++")] == [
        "+  return false;"
    ]


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

    monkeypatch.setattr(preparation, "run_bounded_command", run)
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
    assert guard["timeout_sec"] == 600 and guard["memory_limit_bytes"] == 5 * 1024**3
    assert guard["require_guard"] is True
    assert guard["disk_reserve_bytes"] == 2 * 1024**3
    assert guard["allow_warning_pressure"] is True
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


def test_full_prepare_accepts_only_receipted_optimized_backend_before_other_work(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, optimized_backend_build: BackendFixture
) -> None:
    old = tmp_path / "backend-only"
    old.mkdir()
    backend = preparation.build_backend(preparation.Preparation(old), optimized_dev=True)
    receipt = old / "backend.json"
    monkeypatch.setattr(preparation.platform, "system", lambda: "Darwin")
    monkeypatch.setattr(preparation.platform, "machine", lambda: "arm64")
    fresh = tmp_path / "full"
    fresh.mkdir()
    with pytest.raises(ValueError, match="retained original Egglog binary"):
        preparation.prepare(fresh, backend)
    assert not (fresh / "steps").exists()

    class ReachedLLVM(Exception):
        pass

    def step(self: preparation.Preparation, name: str, command: list[str], **kwargs: object) -> str:
        assert name == "llvm-version"
        identity = json.loads((fresh / "identity.json").read_text())
        assert identity["backend"] == str(backend)
        assert identity["backend_preparation"] == {
            "receipt": str(receipt),
            "sha256": preparation.sha256_file(receipt),
            "contract": preparation.OPTIMIZED_BACKEND,
        }
        raise ReachedLLVM

    monkeypatch.setattr(preparation.Preparation, "step", step)
    with pytest.raises(ReachedLLVM):
        preparation.prepare(fresh, backend_receipt=receipt)


@pytest.mark.parametrize("status", ["failure", "timed-out", "memory-limit", "resource-stopped", "launch-refused"])
def test_optimized_backend_failed_build_retains_guard_receipts_without_publication(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    optimized_backend_build: BackendFixture,
    status: Literal["failure", "timed-out", "memory-limit", "resource-stopped", "launch-refused"],
) -> None:
    original = preparation.run_bounded_command

    def run(command: list[str], cwd: Path, prefix: Path, **kwargs: Any) -> PilotProcessResult:
        if prefix.name.endswith("-backend-build") and status == "launch-refused":
            raise ValueError("resource guard refused to launch a workload: host reserve")
        result = original(command, cwd, prefix, **kwargs)
        if prefix.name.endswith("-backend-build"):
            assert status != "launch-refused"
            return replace(result, status=status, returncode=-9, message="fixture safety stop")
        return result

    monkeypatch.setattr(preparation, "run_bounded_command", run)
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
    original = preparation.run_bounded_command

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

    monkeypatch.setattr(preparation, "run_bounded_command", run)
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


@pytest.mark.parametrize("mode", ["empty", "disabled-wrapper", "symlink"])
def test_optimized_backend_ancestor_config_is_narrowly_reviewed(
    tmp_path: Path, optimized_backend_build: BackendFixture, mode: str
) -> None:
    config = tmp_path / ".cargo/config"
    config.parent.mkdir()
    if mode == "symlink":
        config.symlink_to(tmp_path / "absent-config")
    else:
        config.write_text('[build]\nrustc-wrapper = "kache"\n' if mode == "disabled-wrapper" else "")
    directory = tmp_path / "attempt"
    directory.mkdir()
    if mode == "symlink":
        with pytest.raises(ValueError, match="symlinked Cargo configuration"):
            preparation.build_backend(preparation.Preparation(directory), optimized_dev=True)
    else:
        preparation.build_backend(preparation.Preparation(directory), optimized_dev=True)
        record = json.loads((directory / "backend.json").read_text())
        assert record["cargo_configs"][str(config)] == preparation.sha256_file(config)


def test_backend_only_cli_publishes_guarded_backend_and_no_native_preparation(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, optimized_backend_build: BackendFixture
) -> None:
    lock = tmp_path / "heavy.lock"
    calls = []

    def exclusive(path: Path) -> nullcontext[None]:
        calls.append(path)
        return nullcontext()

    monkeypatch.setattr(preparation, "exclusive_job", exclusive)
    monkeypatch.setattr(
        sys,
        "argv",
        ["prepare-misaal", "--optimized-backend-only", "--storage", str(tmp_path / "attempts"), "--lock", str(lock)],
    )
    preparation.main()
    assert calls == [lock]
    (summary_path,) = (tmp_path / "attempts").glob("*/summary.json")
    summary = json.loads(summary_path.read_text())
    assert summary["status"] == "backend-ready"
    assert summary["backend_receipt_sha256"] == preparation.sha256_file(Path(summary["backend_receipt"]))
    assert preparation.verified_backend_receipt(Path(summary["backend_receipt"])) == Path(summary["backend"])
    assert not (summary_path.parent / "capture-request.json").exists()
    assert not (summary_path.parent / "sources").exists()
    assert not (summary_path.parent / "halide-build").exists()


@pytest.mark.parametrize(
    "options",
    [
        ["--optimized-backend-only", "--backend", "old"],
        ["--optimized-backend-only", "--backend-receipt", "receipt"],
        ["--backend", "old", "--backend-receipt", "receipt"],
        ["--optimized-backend-only", "--repair-wide-literals", "old"],
        ["--backend-receipt", "receipt", "--repair-wide-literals", "old"],
    ],
)
def test_backend_cli_conflicts_refuse_before_taking_lock(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, options: list[str]
) -> None:
    def lock(_: Path) -> None:
        pytest.fail("incompatible backend modes reached the heavy-job lock")

    monkeypatch.setattr(preparation, "exclusive_job", lock)
    monkeypatch.setattr(sys, "argv", ["prepare-misaal", "--storage", str(tmp_path), *options])
    with pytest.raises(SystemExit, match="2"):
        preparation.main()
    assert not list(tmp_path.iterdir())


@pytest.mark.parametrize("changed_receipt", [False, True])
def test_finished_request_retains_and_rechecks_optimized_backend_provenance(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, optimized_backend_build: BackendFixture, changed_receipt: bool
) -> None:
    backend_attempt = tmp_path / "backend-only"
    backend_attempt.mkdir()
    backend = preparation.build_backend(preparation.Preparation(backend_attempt), optimized_dev=True)
    receipt = backend_attempt / "backend.json"
    provenance = {
        "receipt": str(receipt),
        "sha256": preparation.sha256_file(receipt),
        "contract": preparation.OPTIMIZED_BACKEND,
    }
    directory = tmp_path / "full"
    directory.mkdir()
    (directory / "identity.json").write_text(json.dumps({"backend_preparation": provenance}))
    misaal = directory / "sources/MISAAL"
    for relative in [
        "lib/compiler/EggLogCompiler.py",
        "lib/compiler/HydrideCompiler.py",
        "lib/patterns/x86.py",
        "lib/patterns/PatternUtils.py",
        "lib/patterns/Halide.py",
        "lib/patterns/ARM.py",
        "lib/patterns/HVX.py",
        "frontends/halide/src/CodeGen_LLVM.cpp",
        "frontends/halide/src/Rosette.cpp",
        "frontends/halide/src/misaal.cpp",
        "frontends/halide/src/misaal.h",
        "benchmarks/x86/halide/blur3x3/src/blur3x3_generator.cpp",
        "Hydride/codegen-generator/tools/low-level-codegen/RoseLowLevelCodeGen.py",
        "Hydride/codegen-generator/tools/low-level-codegen/InstSelectors/x86/x86LegalizerAllArgs.cpp",
        "Hydride/codegen-generator/tools/low-level-codegen/InstSelectors/x86/RoseX86LegalizerGen.py",
        "Hydride/code-synthesizer/dsl-ir/x86SemanticsAllArgs.py",
        "Hydride/codegen-generator/tools/low-level-codegen/wrappers/x86_wrappers.c.ll",
    ]:
        path = misaal / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("native source fixture")
    llvm = directory / "llvm"
    monkeypatch.setattr(preparation, "LLVM12", llvm)
    for path in [
        directory / "halide-build/src/libHalide.dylib",
        directory / "legalizers-build/libx86LegalizerAllArgs.so",
        directory / "python/bin/python",
        directory / "blur3x3_generator",
        llvm / "bin/llvm-as",
    ]:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("native product fixture")

    def step(self: preparation.Preparation, name: str, command: list[str], **kwargs: Any) -> str:
        if name == "legalizer-load":
            return "x86-hydride-legalize"
        return "{}" if name == "source-environment" else ""

    monkeypatch.setattr(preparation.Preparation, "step", step)
    monkeypatch.setattr(preparation, "patch_pattern_cache", lambda _: None)
    attempt = preparation.Preparation(directory)
    if changed_receipt:
        receipt.write_text(receipt.read_text() + "\n")
        with pytest.raises(ValueError, match="provenance changed"):
            preparation.finish_native(attempt, backend)
        assert not (directory / "capture-request.json").exists()
        return
    request = json.loads(preparation.finish_native(attempt, backend).read_text())
    assert request["backend_preparation"] == provenance
    assert request["backend"] == str(backend)
    assert request["backend_sha256"] == preparation.sha256_file(backend)
    assert str(receipt) in request["identity_paths"]
    assert str(backend_attempt / f"egglog-{preparation.EGGLOG_REVISION}") in request["identity_paths"]
    assert str(optimized_backend_build[1]["rustc"]) in request["identity_paths"]
    assert str(optimized_backend_build[1]["cargo"]) in request["identity_paths"]
