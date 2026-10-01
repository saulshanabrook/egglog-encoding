"""No-network/no-native tests of source identity, isolation, and candidate gates."""

from __future__ import annotations

import hashlib
import io
import json
import stat
import zipfile
from pathlib import Path
from typing import Any

import pytest

from benchmarking.pilot import PilotProcessResult
from scripts import reproduction_prepare_misaal_racket as prep


@pytest.fixture
def tree() -> tuple[dict[str, Any], str, bytes]:
    data = b"#lang info\n"
    blob = hashlib.sha1(f"blob {len(data)}\0".encode() + data).hexdigest()
    body = b"100644 info.rkt\0" + bytes.fromhex(blob)
    digest = hashlib.sha1(f"tree {len(body)}\0".encode() + body).hexdigest()
    return (
        {
            "truncated": False,
            "tree": [{"path": "info.rkt", "mode": "100644", "type": "blob", "size": len(data), "sha": blob}],
        },
        digest,
        data,
    )


def test_git_tree_pin_and_complete_blob_identity(tree: tuple[dict[str, Any], str, bytes]) -> None:
    metadata, digest, _ = tree
    assert prep.verify_tree(metadata, digest) == metadata["tree"]
    with pytest.raises(ValueError, match="pinned Git identity"):
        prep.verify_tree(metadata, "0" * 40)


@pytest.mark.parametrize(
    ("change", "message"),
    [
        ({"path": "../outside"}, "unsafe"),
        ({"path": "dir/info.rkt"}, "omits a parent"),
        ({"mode": "120000"}, "symlink"),
        ({"size": prep.MAX_FILE_BYTES + 1}, "byte bound"),
        ({"sha": "not-a-hash"}, "invalid Git"),
    ],
)
def test_tree_rejects_untrusted_paths_and_members(
    tree: tuple[dict[str, Any], str, bytes], change: dict[str, Any], message: str
) -> None:
    metadata, digest, _ = tree
    metadata["tree"][0].update(change)
    with pytest.raises(ValueError, match=message):
        prep.verify_tree(metadata, digest)


def test_acquisition_rejects_changed_blob_before_install(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, tree: tuple[dict[str, Any], str, bytes]
) -> None:
    metadata, digest, _ = tree
    monkeypatch.setattr(prep, "PACKAGES", {"package": (digest, "https://source/tree", "https://source/raw/")})
    monkeypatch.setattr(
        prep, "fetch_bytes", lambda url, limit: json.dumps(metadata).encode() if url.endswith("tree") else b"bad"
    )
    with pytest.raises(ValueError, match="blob differs"):
        prep.acquire_packages(tmp_path / "sources")
    assert not (tmp_path / "sources/package/info.rkt").exists()
    assert not (tmp_path / "sources/package.json").exists()


@pytest.mark.parametrize("redirect", [False, True])
def test_download_bounds_and_redirect_origin(monkeypatch: pytest.MonkeyPatch, redirect: bool) -> None:
    class Response(io.BytesIO):
        url = "https://other/file" if redirect else "https://source/file"

    monkeypatch.setattr(prep.urllib.request, "urlopen", lambda *a, **kw: Response(b"12345"))
    with pytest.raises(ValueError, match="origin" if redirect else "byte bound"):
        prep.fetch_bytes("https://source/file", 4)


@pytest.mark.parametrize("kind", ["traversal", "symlink", "extra"])
def test_z3_archive_refuses_unexpected_members(tmp_path: Path, monkeypatch: pytest.MonkeyPatch, kind: str) -> None:
    archive = tmp_path / "solver.zip"
    member = zipfile.ZipInfo("../z3" if kind == "traversal" else "z3")
    member.external_attr = ((stat.S_IFLNK if kind == "symlink" else stat.S_IFREG) | 0o755) << 16
    with zipfile.ZipFile(archive, "w") as bundle:
        bundle.writestr(member, b"binary")
        if kind == "extra":
            bundle.writestr("other", b"extra")
    monkeypatch.setattr(prep, "Z3_ARCHIVE_BYTES", archive.stat().st_size)
    monkeypatch.setattr(prep, "Z3_ARCHIVE_SHA256", prep.sha256_file(archive))
    monkeypatch.setattr(prep, "Z3_BYTES", 6)
    with pytest.raises(ValueError, match="member"):
        prep.unpack_z3(archive, tmp_path / "bin/z3")
    assert not (tmp_path / "bin/z3").exists()


def test_unpinned_archive_is_rejected_before_unzip(tmp_path: Path) -> None:
    archive = tmp_path / "not-the-archive"
    archive.write_bytes(b"not zip bytes")
    with pytest.raises(ValueError, match="pinned bytes"):
        prep.unpack_z3(archive, tmp_path / "z3")


def test_scan_keeps_unreviewed_detachment_as_a_stop(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(prep, "PACKAGES", {"rosette": ()})
    server = tmp_path / "rosette/rosette/solver/smt/server.rkt"
    server.parent.mkdir(parents=True)
    server.write_text("(subprocess #f #f #f solver)\n")
    monkeypatch.setattr(prep, "SERVER_SHA256", prep.sha256_file(server))
    (tmp_path / "rosette/new.rkt").write_text("(subprocess-group-enabled #t)\n")
    scan = prep.audit_sources(tmp_path)
    assert scan["status"] == "review-required"
    assert scan["files_scanned"] == 2
    assert scan["findings"][0]["path"] == "rosette/new.rkt"


@pytest.fixture
def original(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> Path:
    checkout = tmp_path / "checkout"
    sources = {}
    for name in (
        "lib/compiler/EggLogCompiler.py",
        "lib/compiler/HydrideCompiler.py",
        "lib/utils/DSLInstructionUtils.py",
    ):
        source = checkout / name
        source.parent.mkdir(parents=True, exist_ok=True)
        source.write_text(f"# original {name}\n")
        sources[name] = prep.sha256_file(source)
    monkeypatch.setattr(prep, "DSL_UTILS_SHA256", sources["lib/utils/DSLInstructionUtils.py"])
    request: dict[str, Any] = {
        "case_id": "misaal-original",
        "checkout": str(checkout),
        "revision": prep.MISAAL_REVISION,
        "hydride_revision": prep.HYDRIDE_REVISION,
        "source_hashes": sources,
        "environment": {
            "PATH": "/original/native/bin:/usr/bin",
            "PYTHONPATH": "/original/python",
            "HL_OPTION": "original",
        },
        "expected_generator_outputs": ["original.ll"],
    }
    for name in ("backend", "llvm_as", "python", "generator", "library", "legalizer"):
        binary = tmp_path / name
        binary.write_text(f"original {name}\n")
        binary.chmod(0o700)
        request[name] = str(binary)
        request[f"{name}_sha256"] = prep.sha256_file(binary)
    request["generator_command"] = [request["generator"], "{output}"]
    path = tmp_path / "original.json"
    path.write_text(json.dumps(request))
    return path


@pytest.fixture
def runtime(tmp_path: Path) -> Path:
    path = tmp_path / "runtime.json"
    path.write_text(
        json.dumps(
            {
                "status": "source-api-blocked",
                "pgid_observation": {"status": "observed-same-group", "cleanup": {"status": "drained"}},
                "gates": {
                    "imports": {"status": "success"},
                    "tiny_solver": {"status": "success"},
                    "source_four_args": {"status": "success"},
                    "captured_five_args": {"status": "expected-api-failure"},
                },
            }
        )
    )
    return path


def test_candidate_preserves_original_and_cannot_be_used_as_a_request(
    original: Path, runtime: Path, tmp_path: Path
) -> None:
    before = original.read_bytes()
    environment = {"PLTADDONDIR": "/isolated/addon", "PATH": f"{prep.RACKET.parent}:/isolated/bin"}
    artifact = prep.candidate_request(original, runtime, environment)
    assert original.read_bytes() == before
    assert artifact["promoted"] is False and artifact["workflow_ready"] is False
    candidate = artifact["candidate_request"]
    for key, value in json.loads(before).items():
        if key not in ("environment", "environment_unset", "source_hashes"):
            assert candidate[key] == value
    assert candidate["environment"]["PYTHONPATH"] == "/original/python"
    assert candidate["racket"] == str(prep.RACKET)
    assert candidate["racket_group_containment"] == "misaal-racket-lease-v1"
    path = tmp_path / "blocked.candidate.json"
    path.write_text(json.dumps(artifact))
    with pytest.raises(KeyError):
        prep.verified_request(path)


@pytest.mark.parametrize("missing", ["tiny_solver", "source_four_args", "captured_five_args"])
def test_import_only_or_partial_evidence_never_produces_candidate(original: Path, runtime: Path, missing: str) -> None:
    data = json.loads(runtime.read_text())
    del data["gates"][missing]
    runtime.write_text(json.dumps(data))
    with pytest.raises(ValueError, match="separate real"):
        prep.candidate_request(original, runtime, {})


def test_changed_native_product_blocks_augmentation(original: Path, runtime: Path) -> None:
    native = Path(json.loads(original.read_text())["backend"])
    native.write_text("changed")
    with pytest.raises(ValueError, match="backend identity changed"):
        prep.candidate_request(original, runtime, {})


@pytest.mark.parametrize("tamper", [False, True])
def test_runtime_publication_preserves_native_requests_and_rejects_late_stale_input(
    original: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch, tamper: bool
) -> None:
    from scripts import reproduction_misaal_patterns as patterns
    from scripts import reproduction_misaal_runtime as runtime_verifier

    original_bytes = original.read_bytes()
    request = json.loads(original_bytes)
    pins = {}
    for name in patterns.PARAMETER_ABI_SOURCE_SHA256:
        source = Path(request["checkout"]) / name
        source.parent.mkdir(parents=True, exist_ok=True)
        source.write_text("reviewed ABI source fixture")
        pins[name] = prep.sha256_file(source)
    monkeypatch.setattr(patterns, "PARAMETER_ABI_SOURCE_SHA256", pins)
    other = tmp_path / "other.json"
    other_request = {**request, "case_id": "misaal-other"}
    if tamper:
        other_request["backend_sha256"] = "0" * 64
    other.write_text(json.dumps(other_request))
    seal = tmp_path / "seal.json"
    seal.write_text(
        json.dumps(
            {
                "source": {"checkout": request["checkout"], "revision": request["revision"]},
                "code_trees": {"addon": {"path": "/isolated/addon"}},
                "environment": {"PLTADDONDIR": "/isolated/addon", "PATH": "/solver/bin:/racket/bin:/usr/bin"},
                "required_unset": ["PLTCOLLECTS", "PLTCONFIGDIR"],
                "racket_group_containment": "misaal-racket-lease-v1",
                "executables": {"racket": {"path": "/racket/bin/racket", "sha256": "racket-digest"}},
            }
        )
    )
    checks = []
    monkeypatch.setattr(runtime_verifier, "verify_runtime", lambda value: checks.append(value))
    output = tmp_path / "published"
    if tamper:
        with pytest.raises(ValueError, match="backend identity changed"):
            prep.augment_requests([original, other], seal, output)
        assert not output.exists()
    else:
        published = prep.augment_requests([original, other], seal, output)
        assert set(published) == {"misaal-original", "misaal-other"}
        assert len(checks) == 1
        for case_id, path in published.items():
            augmented = json.loads(path.read_text())
            for key in ("backend", "generator", "library", "legalizer", "llvm_as", "python"):
                assert augmented[key] == request[key]
                assert augmented[f"{key}_sha256"] == request[f"{key}_sha256"]
            assert augmented["case_id"] == case_id
            assert augmented["environment"]["PATH"] == "/solver/bin:/racket/bin:/original/native/bin:/usr/bin"
            assert augmented["environment"]["PYTHONPATH"] == request["environment"]["PYTHONPATH"]
            assert augmented["identity_paths"] == [str(seal), "/isolated/addon"]
            assert augmented["parameter_abi"] == patterns.PARAMETER_ABI_CONTRACT
            assert augmented["source_hashes"] == {**request["source_hashes"], **pins}
        assert (output / "publication.json").is_file()
    assert original.read_bytes() == original_bytes


@pytest.mark.parametrize("phase", ["packages", "abi"])
@pytest.mark.parametrize("status", ["memory-limit", "resource-stopped"])
def test_complete_runtime_recipe_stops_before_publication_on_nested_safety_failure(
    original: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch, phase: str, status: str
) -> None:
    from scripts import reproduction_misaal_abi_gate as gate
    from scripts import reproduction_misaal_runtime as runtime
    from scripts.reproduction_prepare_misaal import Preparation

    calls = []
    monkeypatch.setattr(prep, "exclusive_job", lambda *_: pytest.fail("coordinator already owns the lock"))
    monkeypatch.setattr(Preparation, "step", lambda *_a, **_kw: calls.append("download"))
    monkeypatch.setattr(runtime, "seal_runtime", lambda *_a, **_kw: pytest.fail("cannot seal a failed gate"))
    monkeypatch.setattr(prep, "augment_requests", lambda *_a, **_kw: pytest.fail("cannot publish failed inputs"))

    def packages(output: Path, *args: Any, **kwargs: Any) -> dict[str, Any]:
        assert kwargs["lock_owned"]
        calls.append("packages")
        output.mkdir()
        (output / "runtime.json").write_text(
            json.dumps({"status": status if phase == "packages" else "source-api-blocked"})
        )
        if phase == "packages":
            raise RuntimeError("package guard stopped")
        return {}

    def gates(_runtime: Path, _checkout: Path, output: Path, *, lock_owned: bool) -> dict[str, Any]:
        assert lock_owned
        calls.append("abi")
        output.mkdir()
        (output / "result.json").write_text(json.dumps({"status": "failure", "process": {"status": status}}))
        raise ValueError("source API diagnostic stopped")

    monkeypatch.setattr(prep, "prepare", packages)
    monkeypatch.setattr(gate, "run_gates", gates)
    output = tmp_path / "complete-runtime"
    result = prep.prepare_source_runtime(output, [original], lock_owned=True)
    assert result["status"] == status and result["requests"] == {}
    assert calls == (["download", "packages"] if phase == "packages" else ["download", "packages", "abi"])
    assert not (output / "requests").exists()
    assert json.loads((output / "result.json").read_text()) == result


@pytest.mark.parametrize("status", [None, "failure", "unverified"])
def test_incomplete_solver_cleanup_blocks_candidate(original: Path, runtime: Path, status: str | None) -> None:
    data = json.loads(runtime.read_text())
    if status is None:
        del data["pgid_observation"]["cleanup"]
    else:
        data["pgid_observation"]["cleanup"]["status"] = status
    runtime.write_text(json.dumps(data))
    with pytest.raises(ValueError, match="drain evidence"):
        prep.candidate_request(original, runtime, {})


@pytest.fixture
def preparation_inputs(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> tuple[Path, Path, Path]:
    monkeypatch.setattr(prep, "ROOT", tmp_path)
    racket = tmp_path / "racket"
    racket.write_bytes(b"racket")
    racket.with_name("raco").write_bytes(b"raco")
    monkeypatch.setattr(prep, "RACKET", racket)
    monkeypatch.setattr(prep, "RACKET_SHA256", prep.sha256_file(racket))
    monkeypatch.setattr(prep, "RACO_SHA256", prep.sha256_file(racket.with_name("raco")))
    archive = tmp_path / "archive"
    archive.write_bytes(b"archive")
    monkeypatch.setattr(prep, "Z3_ARCHIVE_BYTES", 7)
    monkeypatch.setattr(prep, "Z3_ARCHIVE_SHA256", prep.sha256_file(archive))
    captured = tmp_path / "captured.rkt"
    captured.write_text("#lang rosette\n(original-five-argument-call)\n")
    return tmp_path / "benchmarks/local/reproduction/attempt", archive, captured


@pytest.mark.parametrize("status", ["memory-limit", "resource-stopped"])
def test_guard_failure_is_retained_and_no_later_command_runs(
    monkeypatch: pytest.MonkeyPatch, original: Path, preparation_inputs: tuple[Path, Path, Path], status: str
) -> None:
    output, archive, captured = preparation_inputs
    calls = []

    def run(command: list[str], cwd: Path, prefix: Path, **kwargs: Any) -> PilotProcessResult:
        calls.append(command)
        assert kwargs["require_guard"] is True
        assert kwargs["allow_warning_pressure"] is False
        assert kwargs["memory_limit_bytes"] == 5 * 1024**3
        assert kwargs["disk_reserve_bytes"] == prep.DISK_RESERVE_BYTES
        stdout, stderr = prefix.with_suffix(".stdout.log"), prefix.with_suffix(".stderr.log")
        stdout.write_text("")
        stderr.write_text("stopped")
        return PilotProcessResult(status, -9, 0.1, 10, stdout, stderr, "guard stop")  # type: ignore[arg-type]

    monkeypatch.setattr(prep, "run_bounded_command", run)
    with pytest.raises(RuntimeError, match=status):
        prep.prepare(output, [original], archive, captured, prep.sha256_file(captured))
    assert len(calls) == 1
    receipt = json.loads((output / "runtime.json").read_text())
    assert receipt["status"] == status and receipt["gates"] == {}
    assert not list((output / "candidates").iterdir())
    assert len(list((output / "steps").glob("*.result.json"))) == 1


def test_native_environment_is_empty_except_for_explicit_isolated_values(
    monkeypatch: pytest.MonkeyPatch, original: Path, preparation_inputs: tuple[Path, Path, Path]
) -> None:
    output, archive, captured = preparation_inputs
    monkeypatch.setenv("PLTCOLLECTS", "/ambient/collections")
    monkeypatch.setenv("PLTCONFIGDIR", "/ambient/config")
    monkeypatch.setattr(prep, "audit_sources", lambda path: {"status": "no-escape-patterns-found"})
    monkeypatch.setattr(prep, "unpack_z3", lambda path, destination: {"path": str(destination), "sha256": "pinned"})
    calls = []

    def run(command: list[str], cwd: Path, prefix: Path, **kwargs: Any) -> PilotProcessResult:
        calls.append(command)
        stdout, stderr = prefix.with_suffix(".stdout.log"), prefix.with_suffix(".stderr.log")
        stdout.write_text("unexpected version\n")
        stderr.write_text("")
        return PilotProcessResult("success", 0, 0.1, 10, stdout, stderr, None)

    monkeypatch.setattr(prep, "run_bounded_command", run)
    with pytest.raises(ValueError, match="unexpected Racket version"):
        prep.prepare(output, [original], archive, captured, prep.sha256_file(captured))
    assert len(calls) == 2
    command = calls[1]
    assert command[:2] == ["/usr/bin/env", "-i"]
    assert command[-2:] == [str(prep.RACKET), "--version"]
    environment = dict(item.split("=", 1) for item in command[2:-2])
    assert environment == {
        "PLTUSERHOME": str(output / "user"),
        "PLTADDONDIR": str(output / "addon"),
        "TMPDIR": str(output / "tmp"),
        "HYDRIDE_ROOT": str(Path(json.loads(original.read_text())["checkout"]) / "Hydride"),
        "MISAAL_Z3_PATH": str(output / "bin/z3"),
        "PATH": f"{output / 'bin'}:{prep.RACKET.parent}:/usr/bin:/bin:/usr/sbin:/sbin",
    }
    assert not list((output / "candidates").iterdir())


@pytest.mark.parametrize(
    ("scenario", "error_text", "cleanup_status"),
    [
        ("same-group", None, "drained"),
        ("detached", "detached", "drained"),
        ("telemetry-failure", "observation failed", "unverified"),
        ("missing-solver", "pinned solver was not observed", "unverified"),
        ("drain-failure", "did not drain", "failure"),
        ("cleanup-telemetry-failure", "drain telemetry failed", "failure"),
        ("release-timeout", "timed out", "failure"),
    ],
)
def test_live_solver_is_released_and_drain_is_checked_on_every_outcome(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    scenario: str,
    error_text: str | None,
    cleanup_status: str,
) -> None:
    events = []

    class Process:
        pid = 1234
        returncode: int | None = None
        stdout = io.StringIO("MISAAL_TINY_SOLVER_OK\n")

        def poll(self) -> int | None:
            return self.returncode

        def communicate(self, data: str, *, timeout: int) -> tuple[str, None]:
            assert self.poll() is None
            assert data == "\n" and timeout == 10
            events.append("release-live-racket")
            if scenario == "release-timeout":
                raise prep.subprocess.TimeoutExpired("racket", timeout)
            self.returncode = 0
            return "", None

        def kill(self) -> None:
            raise AssertionError("killing the held parent skips its solver-shutdown")

    process = Process()
    group = prep.os.getpgrp()
    child_group = group + 1 if scenario == "detached" else group
    initial = f"1234 1 {group} /Applications/Racket v9.2/bin/racket\n"
    if scenario != "missing-solver":
        initial += f"1235 1234 {child_group} /isolated/bin/z3\n"
    snapshots = 0

    def inspect_processes(command: list[str], **kwargs: Any) -> prep.subprocess.CompletedProcess[str]:
        nonlocal snapshots
        assert command == ["/bin/ps", "-axo", "pid=,ppid=,pgid=,comm=", "-ww"]
        assert kwargs == {"check": True, "capture_output": True, "text": True, "timeout": 1}
        snapshots += 1
        if snapshots == 1:
            assert process.poll() is None
            if scenario == "telemetry-failure":
                raise OSError("observation failed")
            return prep.subprocess.CompletedProcess(command, 0, initial)
        assert events == ["release-live-racket"]
        if scenario == "cleanup-telemetry-failure":
            raise OSError("drain telemetry failed")
        remaining = f"1235 1 {child_group} /isolated/bin/z3\n" if scenario == "drain-failure" else ""
        return prep.subprocess.CompletedProcess(command, 0, remaining)

    monkeypatch.setattr(prep.subprocess, "Popen", lambda *a, **kw: process)
    monkeypatch.setattr(prep.subprocess, "run", inspect_processes)
    monkeypatch.setattr(prep.time, "sleep", lambda seconds: None)
    receipt = tmp_path / "pgids.json"
    if error_text is None:
        prep.observe_solver(prep.RACKET, tmp_path / "smoke", Path("/isolated/bin/z3"), receipt)
    else:
        with pytest.raises((ValueError, OSError, prep.subprocess.TimeoutExpired), match=error_text):
            prep.observe_solver(prep.RACKET, tmp_path / "smoke", Path("/isolated/bin/z3"), receipt)
    record = json.loads(receipt.read_text())
    assert events == ["release-live-racket"]
    assert record["status"] == ("observed-same-group" if error_text is None else "failure")
    assert record["cleanup"]["status"] == cleanup_status
    assert record["cleanup"]["release"] == ("attempted" if scenario == "release-timeout" else "sent")
    if scenario == "detached":
        assert record["reason"] == "Racket or solver detached from the guarded process group"
        assert record["cleanup"]["snapshots"] == [{"remaining": []}]
    if scenario == "drain-failure":
        assert snapshots == 11 and len(record["cleanup"]["snapshots"]) == 10
