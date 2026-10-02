"""Durable Eggcc preparation contracts without native builds or downloads."""

import hashlib
import io
import json
import tarfile
import tomllib
from pathlib import Path

import pytest

from scripts import reproduction_prepare_eggcc as preparation


def original_lock() -> bytes:
    return (
        "version = 4\n\n"
        + "".join(
            f'[[package]]\nname = "{name}"\nversion = "2.0.0"\nsource = "{preparation.CORE_SOURCE}"\n\n'
            for name in sorted(preparation.CORE_PACKAGES)
        )
        + '[[package]]\nname = "unrelated"\nversion = "1.2.3"\n'
    ).encode()


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


@pytest.mark.parametrize(
    "omit_tiger,continuation,regression_passes",
    [(False, False, 1), (True, False, 1), (False, True, 1), (False, False, 0), (False, False, 2)],
)
def test_preparation_builds_actual_source_and_keeps_gurobi_blocked(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    omit_tiger: bool,
    continuation: bool,
    regression_passes: int,
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
        "benchmarking/processes.py",
        "benchmarking/memory_guard.py",
        preparation.REPAIR_FIXTURE,
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
    lock = original_lock()
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
    monkeypatch.setattr(preparation, "LOCK_SHA256", hashlib.sha256(lock).hexdigest())
    monkeypatch.setattr(
        preparation, "patched_eggcc_sources", lambda _: {"src/main.rs": "original compiler\nobservation"}
    )
    commands: list[tuple[str, list[str]]] = []
    output = tmp_path / "benchmarks/local/reproduction/attempt"
    build = tmp_path / "target/disposable-eggcc"
    monkeypatch.setenv("CARGO_HOME", str(tmp_path / "empty-cache"))
    monkeypatch.setenv("CARGO_PROFILE_DEV_OPT_LEVEL", "0")
    monkeypatch.setenv("CARGO_PROFILE_DEV_DEBUG_ASSERTIONS", "false")
    monkeypatch.setenv("CARGO_PROFILE_DEV_OVERFLOW_CHECKS", "false")
    core_lock = b"version = 4\npackage = []\n"
    monkeypatch.setattr(preparation, "CORE_PINS", {"Cargo.lock": hashlib.sha256(core_lock).hexdigest()})

    def core_source(preparer: preparation.Preparation, *_: object, **__: object) -> tuple[Path, dict[str, object]]:
        core = preparer.directory / "sources/egglog-core"
        core.mkdir()
        (core / "Cargo.lock").write_bytes(core_lock)
        receipt: dict[str, object] = {"prepared_files": preparation.CORE_PINS}
        preparation.write_json(preparer.directory / "core-repair.json", receipt)
        return core, receipt

    monkeypatch.setattr(preparation, "prepare_core", core_source)

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
            binary.parent.mkdir(parents=True, exist_ok=True)
            binary.write_bytes(b"built compiler")
            if not omit_tiger:
                tiger = output / "sources/eggcc/target/debug/tiger"
                tiger.parent.mkdir(parents=True)
                tiger.write_bytes(b"built native Tiger")
        if name == "core-regression":
            return f"test result: ok. {regression_passes} passed; 0 failed; 0 ignored\n"
        if name == "clone-target":
            import shutil

            shutil.copytree(command[-2], command[-1])
        return ""

    monkeypatch.setattr(preparation.Preparation, "step", step)

    def no_nested_lock(*_: object) -> None:
        pytest.fail("in-process preparation must use the coordinator's existing job slot")

    monkeypatch.setattr(preparation, "exclusive_job", no_nested_lock)
    previous = None
    previous_hashes: dict[Path, str] = {}
    if continuation:
        previous = tmp_path / "benchmarks/local/reproduction/previous"
        old_source = previous / "sources/eggcc"
        old_source.mkdir(parents=True)
        (old_source / "Cargo.lock").write_bytes(lock)
        (old_source / "source.rs").write_bytes(b"original prepared source")
        (previous / f"eggcc-{preparation.REVISION}.tar.gz").write_bytes(archive.read_bytes())
        old_binary = previous / "cargo-target/debug/eggcc"
        old_binary.parent.mkdir(parents=True)
        old_binary.write_bytes(b"old compiler, preserved")
        products = {str(old_binary): preparation.sha256_file(old_binary)}
        preparation.write_json(previous / "build-products.json", products)
        preparation.write_json(
            previous / "prepared-source.json",
            {name: preparation.sha256_file(old_source / name) for name in ("Cargo.lock", "source.rs")},
        )
        preparation.write_json(
            previous / "preparation.json",
            {
                "status": "success",
                "revision": preparation.REVISION,
                "checkout": str(old_source),
                "build_root": str(previous / "cargo-target"),
                "binary": str(old_binary),
                "artifacts": products,
            },
        )
        previous_hashes = {path: preparation.sha256_file(path) for path in previous.rglob("*") if path.is_file()}
    result = preparation.prepare_eggcc(output, engine, build_root=build, continue_from=previous)
    assert all(preparation.sha256_file(path) == digest for path, digest in previous_hashes.items())
    if continuation:
        assert previous is not None
        assert "download-source" not in dict(commands)
        assert dict(commands)["clone-target"] == ["/bin/cp", "-cR", str(previous / "cargo-target"), str(build)]
    assert result["configuration_blockers"][0]["configuration"] == {
        "native_options": ["--tiger-ilp", "--ilp-solver", "gurobi"]
    }
    assert result["configuration_blockers"][0]["status"] == "blocked"
    assert not result["configuration_blockers"][0]["extractor_substitution"]
    assert (output / "sources/eggcc/benchmarks/fact.bril").read_bytes() == b"original benchmark"
    assert (output / "original-source.json").is_file()
    assert (output / "prepared-source.json").is_file()
    assert (output / "patches/workspace-isolation.patch").is_file()
    assert result["build_profile"] == {
        "name": "dev",
        "opt_level": 3,
        "debug": 0,
        "debug_assertions": True,
        "overflow_checks": True,
        "incremental": False,
        "cargo_jobs": 1,
    }
    assert json.loads((output / "preparation.json").read_text())["build_profile"] == result["build_profile"]
    regression = dict(commands)["core-regression"]
    assert regression[regression.index("test") + 1 : regression.index("test") + 3] == ["--profile", "dev"]
    assert regression[-2:] == ["--", "--exact"]
    assert preparation.REGRESSION in regression
    for flag in (
        "CARGO_PROFILE_DEV_DEBUG=0",
        "CARGO_PROFILE_DEV_OPT_LEVEL=3",
        "CARGO_PROFILE_DEV_DEBUG_ASSERTIONS=true",
        "CARGO_PROFILE_DEV_OVERFLOW_CHECKS=true",
        "CARGO_INCREMENTAL=0",
    ):
        assert regression.count(flag) == 1
    if regression_passes != 1:
        assert result["status"] == "blocked" and "exactly one passing test" in result["reason"]
        assert "build" not in dict(commands)
        assert not (output / "settings.json").exists()
        return
    build_command = dict(commands)["build"]
    assert build_command[-9:] == ["cargo", "+1.88.0", "build", "--profile", "dev", "--locked", "-j1", "--bin", "eggcc"]
    assert build_command[: build_command.index("cargo")] == regression[: regression.index("cargo")]
    for flag in (
        "CARGO_PROFILE_DEV_DEBUG=0",
        "CARGO_INCREMENTAL=0",
        "RUSTC_WRAPPER=",
        "LIBRARY_PATH=/opt/homebrew/lib",
    ):
        assert flag in build_command
    assert all("gurobi" not in command and "--run-mode" not in command for _, command in commands)
    assert f"CARGO_HOME={output / 'cargo-home'}" in build_command
    assert [name for name, _ in commands].index("core-regression") < [name for name, _ in commands].index("build")
    assert preparation.repaired_lock(lock.decode()) == (output / "Cargo.lock").read_text()
    assert all(
        f'{name} = {{ path = "../egglog-core' in (output / "sources/eggcc/Cargo.toml").read_text()
        for name in ("egglog", "egglog-ast", "egglog-reports")
    )
    if omit_tiger:
        assert result["status"] == "blocked" and "native executable" in result["reason"]
        assert not (output / "settings.json").exists()
    else:
        assert result["status"] == "success"
        settings = json.loads((output / "settings.json").read_text())["eggcc"]
        assert settings["paths"]["checkout"] == str(output / "sources/eggcc")
        assert settings["paths"]["binary"] == str(build / "debug/eggcc")
        assert settings["configuration_blockers"] == result["configuration_blockers"]


def test_lock_changes_only_exact_core_identities() -> None:
    source = original_lock().decode()
    derived = preparation.repaired_lock(source)
    assert derived == source.replace(f'source = "{preparation.CORE_SOURCE}"\n', "")
    assert tomllib.loads(derived)["package"][-1] == {"name": "unrelated", "version": "1.2.3"}
    for wrong in (
        source.replace("egglog-ast", "other"),
        source.replace("2.0.0", "2.0.1", 1),
        source.replace(preparation.CORE_REVISION, "0" * 40),
    ):
        with pytest.raises(ValueError, match="core"):
            preparation.repaired_lock(wrong)


def test_upstream_fixture_and_regression_are_exact() -> None:
    path = preparation.ROOT / preparation.REPAIR_FIXTURE
    assert preparation.sha256_file(path) == preparation.REPAIR_SHA256
    patch = path.read_text()
    assert f"From {preparation.REPAIR_REVISION} " in patch
    assert "fn " + preparation.REGRESSION.split("::")[-1] + "()" in patch
    production = patch.split("diff --git a/core-relations/src/hash_index/tests.rs")[0]
    added = [line for line in production.splitlines() if line.startswith("+") and not line.startswith("+++")]
    assert len(added) == 5
    assert "+                group.sort_unstable_by_key(|&(_, row)| row);" in added
    assert "             pairs.dedup();" in production
    assert "+    assert_eq!(row_ids, expected);" in patch


def test_cache_seed_is_private_checked_and_bounded(tmp_path: Path) -> None:
    output, cache = tmp_path / "output", tmp_path / "old-cache"
    output.mkdir()
    preparer = preparation.Preparation(output)
    source = cache / "registry/cache/index.crates.io-test/tiny-1.0.0.crate"
    source.parent.mkdir(parents=True)
    source.write_bytes(b"pinned archive")
    index = cache / "registry/index/index.crates.io-test"
    (index / ".cache/ti/ny").mkdir(parents=True)
    (index / ".cache/ti/ny/tiny").write_bytes(b"index")
    (index / "config.json").write_text("{}")
    lock = tmp_path / "Cargo.lock"
    lock.write_text(
        '[[package]]\nname="tiny"\nversion="1.0.0"\n'
        'source="registry+https://github.com/rust-lang/crates.io-index"\n'
        f'checksum="{preparation.sha256_file(source)}"\n'
    )
    home = preparation.seed_cargo_cache(preparer, cache, [lock, lock], timeout_sec=60)
    copied = home / source.relative_to(cache)
    assert copied.read_bytes() == source.read_bytes()
    assert copied.stat().st_ino != source.stat().st_ino
    assert not (home / "config.toml").exists()
    copied.write_bytes(b"new cache writes cannot alter old bytes")
    assert source.read_bytes() == b"pinned archive"
    source.write_bytes(b"changed archive")
    other = tmp_path / "other"
    other.mkdir()
    with pytest.raises(ValueError, match="locked checksum"):
        preparation.seed_cargo_cache(preparation.Preparation(other), cache, [lock], timeout_sec=60)


def test_continuation_pins_source_products_and_original_archive(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    previous = tmp_path / "previous"
    checkout = previous / "sources/eggcc"
    checkout.mkdir(parents=True)
    (checkout / "Cargo.lock").write_bytes(original_lock())
    (checkout / "source.rs").write_bytes(b"instrumented source")
    archive = previous / f"eggcc-{preparation.REVISION}.tar.gz"
    archive.write_bytes(b"pinned archive")
    monkeypatch.setattr(preparation, "ARCHIVE_SHA256", preparation.sha256_file(archive))
    monkeypatch.setattr(preparation, "LOCK_SHA256", preparation.sha256_file(checkout / "Cargo.lock"))
    binary = previous / "target/debug/eggcc"
    binary.parent.mkdir(parents=True)
    binary.write_bytes(b"original binary")
    products = {str(binary): preparation.sha256_file(binary)}
    receipt = {"status": "success", "revision": preparation.REVISION, "checkout": str(checkout), "artifacts": products}
    preparation.write_json(previous / "preparation.json", receipt)
    preparation.write_json(previous / "build-products.json", products)
    preparation.write_json(
        previous / "prepared-source.json",
        {name: preparation.sha256_file(checkout / name) for name in ("Cargo.lock", "source.rs")},
    )
    assert preparation.verify_continuation(previous) == receipt
    (checkout / "source.rs").write_bytes(b"drift")
    with pytest.raises(ValueError, match="prepared source changed"):
        preparation.verify_continuation(previous)
    (checkout / "source.rs").write_bytes(b"instrumented source")
    binary.write_bytes(b"drift")
    with pytest.raises(ValueError, match="build product changed"):
        preparation.verify_continuation(previous)


@pytest.mark.parametrize("failure", ["source-pin", "unexpected-file", "none"])
def test_core_acquisition_pins_revision_and_limits_patch_files(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, failure: str
) -> None:
    output = tmp_path / "output"
    output.mkdir()
    preparer = preparation.Preparation(output)
    fixture = tmp_path / preparation.REPAIR_FIXTURE
    fixture.parent.mkdir(parents=True)
    fixture.write_bytes(b"controlled patch")
    monkeypatch.setattr(preparation, "ROOT", tmp_path)
    monkeypatch.setattr(preparation, "REPAIR_SHA256", preparation.sha256_file(fixture))
    originals = {
        "Cargo.lock": b"original lock",
        "core-relations/src/hash_index/mod.rs": b"original code",
        "core-relations/src/hash_index/tests.rs": b"original tests",
        "unrelated.rs": b"unchanged",
    }
    pins = {name: hashlib.sha256(data).hexdigest() for name, data in originals.items() if name != "unrelated.rs"}
    monkeypatch.setattr(preparation, "CORE_PINS", pins)
    commands: list[str] = []

    def step(self: preparation.Preparation, name: str, command: list[str], **kwargs: object) -> str:
        commands.append(name)
        core = output / "sources/egglog-core"
        if name == "core-checkout":
            for relative, data in originals.items():
                path = core / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(data)
            if failure == "source-pin":
                (core / "Cargo.lock").write_bytes(b"drift")
        if name == "core-revision":
            return preparation.CORE_REVISION
        if name == "core-files":
            return "\n".join(originals)
        if name == "core-patch":
            for relative in list(pins)[1:]:
                (core / relative).write_bytes(originals[relative] + b" exact upstream patch")
            if failure == "unexpected-file":
                (core / "unrelated.rs").write_bytes(b"unexpected change")
        return ""

    monkeypatch.setattr(preparation.Preparation, "step", step)
    if failure != "none":
        with pytest.raises(ValueError, match="source pin|unexpected source"):
            preparation.prepare_core(preparer, tmp_path / "empty-cache", timeout_sec=60)
        assert not (output / "core-repair.json").exists()
        if failure == "source-pin":
            assert "core-patch" not in commands
    else:
        core, receipt = preparation.prepare_core(preparer, tmp_path / "empty-cache", timeout_sec=60)
        assert receipt["base_revision"] == preparation.CORE_REVISION
        assert receipt["upstream_commit"] == preparation.REPAIR_REVISION
        assert receipt["original_files"]["Cargo.lock"] == receipt["prepared_files"]["Cargo.lock"]
        assert (core / "unrelated.rs").read_bytes() == originals["unrelated.rs"]
        assert commands.index("core-patch-check") < commands.index("core-patch")


def test_cache_refuses_borrowed_git_store(tmp_path: Path) -> None:
    cache, output = tmp_path / "cache", tmp_path / "output"
    output.mkdir()
    alternates = cache / "git/db/egg-smol-65fdca4a5529f39b/objects/info/alternates"
    alternates.parent.mkdir(parents=True)
    alternates.write_text("/old/cache/objects")
    with pytest.raises(ValueError, match="borrow"):
        preparation.seed_cargo_cache(preparation.Preparation(output), cache, [], timeout_sec=60)
