"""SpEQ preparation contracts; mocked native commands and in-memory archive bytes."""

from __future__ import annotations

import hashlib
import importlib.metadata
import io
import json
import sys
import tarfile
from pathlib import Path
from types import ModuleType
from typing import Any, Literal

import pytest

from benchmarking.pilot import PilotProcessResult
from scripts import reproduction_prepare_speq as preparation


def archive_bytes(members: list[tuple[str, bytes, bytes]]) -> bytes:
    """Produce a tiny compressed archive including controlled invalid member kinds."""
    stream = io.BytesIO()
    with tarfile.open(fileobj=stream, mode="w:gz") as archive:
        for name, data, kind in members:
            info = tarfile.TarInfo(name)
            info.type = kind
            info.size = len(data) if kind == tarfile.REGTYPE else 0
            archive.addfile(info, io.BytesIO(data) if kind == tarfile.REGTYPE else None)
    return stream.getvalue()


@pytest.mark.parametrize("fault", [None, "checksum", "duplicate", "symlink", "unsafe", "missing", "member-hash"])
def test_archive_acquisition_requires_whole_archive_and_root_dockerfile(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, fault: str | None
) -> None:
    dockerfile, parser = b"FROM original\n", b"original parser\n"
    members = [
        ("lleq-artifact/parseIR.py", parser, tarfile.REGTYPE),
        ("lleq-artifact/Dockerfile", dockerfile, tarfile.REGTYPE),
        ("lleq-artifact/unused/large-tool", b"do not retain", tarfile.REGTYPE),
    ]
    if fault == "duplicate":
        members.append(members[1])
    elif fault == "symlink":
        members[1] = (members[1][0], b"", tarfile.SYMTYPE)
    elif fault == "unsafe":
        members.append(("lleq-artifact/../../escape", b"unsafe", tarfile.REGTYPE))
    elif fault == "missing":
        del members[1]
    data = archive_bytes(members)
    digest = hashlib.md5(data).hexdigest()
    monkeypatch.setattr(preparation, "ARCHIVE_BYTES", len(data))
    monkeypatch.setattr(preparation, "DOCKERFILE_BYTES", len(dockerfile))
    monkeypatch.setattr(preparation.record_speq, "SPEQ_ARCHIVE_MD5", "wrong" if fault == "checksum" else digest)
    monkeypatch.setattr(
        preparation,
        "ARTIFACT_HASHES",
        {"parseIR.py": "wrong" if fault == "member-hash" else hashlib.sha256(parser).hexdigest()},
    )
    metadata = {"files": [{"checksum": "md5:" + preparation.record_speq.SPEQ_ARCHIVE_MD5, "size": len(data)}]}
    requests = []

    def open_url(url: str, **_: Any) -> io.BytesIO:
        requests.append(url)
        return io.BytesIO(data if url.endswith("/content") else json.dumps(metadata).encode())

    monkeypatch.setattr(preparation.urllib.request, "urlopen", open_url)
    output = tmp_path / "acquisition"
    if fault:
        with pytest.raises(ValueError):
            preparation.acquire_artifact(output)
        assert not (output / "artifact-receipt.json").exists()
        return
    result = preparation.acquire_artifact(output)
    assert result["full_archive_index_examined"] and result["computed_archive_md5"] == digest
    assert result["compressed_bytes_read"] == len(data) and result["member_count"] == 3
    assert (output / "artifact/Dockerfile").read_bytes() == dockerfile
    assert not (output / "artifact/unused").exists()
    assert len((output / "members.jsonl").read_text().splitlines()) == 3
    assert len(requests) == 2
    with pytest.raises(FileExistsError):
        preparation.acquire_artifact(output)


@pytest.fixture
def pipeline(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> tuple[dict, dict, list]:
    monkeypatch.setattr(preparation, "ROOT", tmp_path)
    for relative in ("scripts/paper_benchmarks/record_speq.py", "scripts/paper_benchmarks/speq_rev_plugin.cpp"):
        path = tmp_path / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("implementation fixture")
    engine = tmp_path / "engine"
    engine.write_text("ordinary engine")
    llvm = tmp_path / "llvm/bin"
    llvm.mkdir(parents=True)
    for name in ("llvm-config", "clang", "clang++", "opt", "uv"):
        (llvm / name).write_text("native tool " + name)
    library = tmp_path / "llvm/libLLVM"
    library.write_text("LLVM library")
    monkeypatch.setattr(preparation.shutil, "which", lambda name: str(llvm / name))
    artifact = tmp_path / "cached-artifact"
    hashes = {name: hashlib.sha256(name.encode()).hexdigest() for name in preparation.ARTIFACT_HASHES}
    monkeypatch.setattr(preparation, "ARTIFACT_HASHES", hashes)
    for relative in hashes:
        target = artifact / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(relative)
    dockerfile = b"FROM original\n"
    (artifact / "Dockerfile").write_bytes(dockerfile)
    monkeypatch.setattr(preparation, "DOCKERFILE_BYTES", len(dockerfile))
    archive_receipt = tmp_path / "artifact-receipt.json"
    member_index = tmp_path / "members.jsonl"
    member_index.write_text(
        "".join(
            json.dumps({"name": "lleq-artifact/" + name, "size": (artifact / name).stat().st_size, "type": "0"}) + "\n"
            for name in [*hashes, "Dockerfile"]
        )
    )
    archive_receipt.write_text(
        json.dumps(
            {
                "computed_archive_md5": preparation.record_speq.SPEQ_ARCHIVE_MD5,
                "compressed_bytes_read": preparation.ARCHIVE_BYTES,
                "full_archive_index_examined": True,
                "selected": {**hashes, "Dockerfile": hashlib.sha256(dockerfile).hexdigest()},
                "member_index_sha256": preparation.sha256_file(member_index),
                "member_count": len(hashes) + 1,
            }
        )
    )
    lleq = tmp_path / "cached-lleq"
    rev_hashes = {name: hashlib.sha256(name.encode()).hexdigest() for name in preparation.REV_HASHES}
    monkeypatch.setattr(preparation, "REV_HASHES", rev_hashes)
    for relative in rev_hashes:
        target = lleq / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(relative)
    reference_hashes = {
        name: hashlib.sha256(name.encode()).hexdigest() for name in preparation.record_speq.REFERENCE_FIR_SHA256
    }
    monkeypatch.setattr(preparation.record_speq, "REFERENCE_FIR_SHA256", reference_hashes)
    monkeypatch.setattr(preparation.record_speq, "adapt_parse_ir", lambda source: "adapted " + source)
    output = tmp_path / "benchmarks/local/reproduction/speq-preparation"
    arguments = {
        "output": output,
        "engine": engine,
        "llvm_config": llvm / "llvm-config",
        "artifact_source": artifact,
        "artifact_receipt": archive_receipt,
        "lleq_source": lleq,
    }
    state: dict[str, Any] = {}
    launches: list[dict] = []

    def run(command: list[str], cwd: Path, prefix: Path, **options: Any) -> PilotProcessResult:
        name = prefix.name.split("-", 1)[1]
        receipt = json.loads((output / "preparation.json").read_text())
        assert receipt["steps"][-1]["name"] == name and receipt["steps"][-1]["status"] == "running"
        launches.append({"name": name, "command": command, "options": options})
        stdout, stderr = prefix.with_suffix(".stdout.log"), prefix.with_suffix(".stderr.log")
        stdout.write_text("")
        stderr.write_text("")
        if state.get("guard") == name:
            raise ValueError("disk guard refused to launch")
        if state.get("stop") == name:
            return PilotProcessResult("memory-limit", None, 0, 0, stdout, stderr, "memory cap")
        if name == "llvm-version":
            stdout.write_text(state.get("version", preparation.LLVM_VERSION))
        elif name == "llvm-bindir":
            stdout.write_text(str(llvm))
        elif name == "llvm-libraries":
            stdout.write_text(str(library))
        elif name == "clang-version":
            stdout.write_text("clang version " + state.get("clang_version", preparation.LLVM_VERSION))
        elif name == "opt-version":
            stdout.write_text("LLVM version " + preparation.LLVM_VERSION)
        elif name == "python-environment":
            (output / "python/bin").mkdir(parents=True)
            (output / "python/bin/python").write_text("isolated python binary")
            (output / "python-runtimes").mkdir()
        elif name == "python-lock":
            Path(command[-1]).write_text("resolved==1 --hash=sha256:retained\n")
        elif name == "python-download":
            (output / "evidence/wheels/resolved.whl").write_text("retained wheel")
        elif name == "python-import":
            stdout.write_text('{"egglog":"13.2.0"}')
        elif name == "rev-build":
            Path(command[-1]).write_text("real shared plugin would be here")
        elif name.startswith("reference-"):
            Path(command[-1]).write_text("bad" if state.get("bad_reference") else name.removeprefix("reference-"))
        return PilotProcessResult("success", 0, 0, 0, stdout, stderr, None)

    monkeypatch.setattr(preparation, "run_bounded_command", run)
    return arguments, state, launches


def test_preparation_freezes_sources_tools_and_unchanged_reference_outputs(pipeline: tuple) -> None:
    arguments, _, launches = pipeline
    result = preparation.prepare_speq(**arguments)
    assert result["status"] == "success", result["reason"]
    assert result["device_execution"] is result["benchmark_execution"] is False
    assert result["missing_paper_inputs"] == ["speq-tpal", "speq-tsvc2"]
    commands = {row["name"]: row["command"] for row in launches}
    assert all(row["options"]["require_guard"] and row["options"]["allow_warning_pressure"] for row in launches)
    assert all(row["options"]["disk_reserve_bytes"] == 10 * 1024**3 for row in launches)
    assert "--generate-hashes" in commands["python-lock"]
    assert "--require-hashes" in commands["python-download"] and "--no-index" in commands["python-install"]
    assert "build_rev_plugin" in " ".join(commands["rev-build"])
    custom_header = "llvm/include/llvm/Analysis/MemorySSA.h"
    assert (arguments["output"] / "sources/lleq" / custom_header).read_bytes() == (
        arguments["lleq_source"] / custom_header
    ).read_bytes()
    assert len([name for name in commands if name.startswith("reference-")]) == 4
    assert "--complete" not in str(commands) and "-D_FORTIFY_SOURCE" not in str(commands)
    settings = json.loads(Path(result["settings"]).read_text())["speq"]
    assert settings["frontend_flags"] == ["-D_FORTIFY_SOURCE=0", "-DPOLYBENCH_USE_C99_PROTO"]
    assert settings["phi_polarity_repair"] is True
    assert Path(settings["paths"]["speq_artifact"]).is_relative_to(arguments["output"])
    assert "speq_rev_plugin.cpp" in str(settings["identity_paths"])
    assert result["python_wheels"]["resolved.whl"]
    assert (arguments["artifact_source"] / "parseIR.py").read_text() == "parseIR.py"
    assert (arguments["output"] / "sources/artifact/requirements.txt").read_text() == "requirements.txt"
    assert result["artifact_provenance"]["dockerfile"]["status"] == "retained"
    assert (arguments["output"] / "sources/artifact/Dockerfile").read_bytes() == (
        arguments["artifact_source"] / "Dockerfile"
    ).read_bytes()


@pytest.mark.parametrize("benchmark", list(preparation.record_speq.COMPLETE_APPLICATION_C_SHA256))
def test_published_settings_route_each_original_c_parent_to_a_fresh_phi_build(
    pipeline: tuple, tmp_path: Path, monkeypatch: pytest.MonkeyPatch, benchmark: str
) -> None:
    from scripts import dialegg_speq_complete as complete
    from scripts.reproduction_dispatch import capture_case

    arguments, _, launches = pipeline
    result = preparation.prepare_speq(**arguments)
    settings = json.loads(Path(result["settings"]).read_text())["speq"]
    prepared_plugin = Path(settings["paths"]["speq_rev_plugin"])
    original_plugin = prepared_plugin.read_bytes()
    assert "repair_phi_polarity" not in next(row["command"][-4] for row in launches if row["name"] == "rev-build")
    calls = []

    def build(lleq: Path, llvm: Path, output: Path, *, repair_phi_polarity: bool) -> tuple[Path, Path, str]:
        assert repair_phi_polarity and lleq == Path(settings["paths"]["speq_lleq"])
        assert llvm == Path(settings["paths"]["llvm17_config"])
        assert output != prepared_plugin
        calls.append("fresh-phi-build")
        output.write_text("mock fresh PHI plugin; no native build")
        receipt = output.parent / "phi-repair/diagnostic.json"
        receipt.parent.mkdir()
        receipt.write_text(json.dumps({"status": "mocked-source-repair"}))
        return llvm.parent / "opt", output, preparation.LLVM_VERSION

    def application(*args: Any, **kwargs: Any) -> None:
        assert args[3] == benchmark
        assert kwargs == {"complete": True, "frontend_flags": settings["frontend_flags"]}
        calls.append("original-c-frontend")
        raise ValueError("mock stop after fresh PHI build")

    def run(command: list[str], cwd: Path, prefix: Path, timeout: float) -> PilotProcessResult:
        assert "--repair-phi-polarity" in command and "--rev-plugin" not in command
        args = preparation.record_speq.parse_args(command[2:])
        assert args.complete and args.benchmark == [benchmark] and args.rev_plugin is None
        with pytest.raises(ValueError, match="mock stop after fresh PHI build"):
            preparation.record_speq.record_complete(args, args.artifact, "unused parser", [benchmark])
        stdout, stderr = prefix.with_suffix(".out"), prefix.with_suffix(".err")
        stdout.write_text("")
        stderr.write_text("mock stop after fresh PHI build")
        return PilotProcessResult("failure", 1, 0, 0, stdout, stderr, stderr.read_text())

    monkeypatch.setenv("EGGLOG_BENCH_MEMORY_GUARD", "1")
    monkeypatch.setattr(preparation.record_speq, "build_rev_plugin", build)
    monkeypatch.setattr(preparation.record_speq, "application_fir", application)
    monkeypatch.setattr(complete, "run_complete_command", run)
    case_id = "speq-" + benchmark
    captured = capture_case({"family": "speq", "id": case_id}, settings, tmp_path / "capture")
    assert calls == ["fresh-phi-build", "original-c-frontend"]
    assert captured["omitted_prebuilt_rev_plugin"]["path"] == str(prepared_plugin)
    assert captured["source"]["phi_polarity_repair"] is True
    assert captured["source"]["phi_repair_evidence"]["source_patch"] == {"status": "mocked-source-repair"}
    assert not captured["source_complete"] and captured["workloads"] == []
    assert prepared_plugin.read_bytes() == original_plugin


@pytest.mark.parametrize("installed", ["80.9.0", "84.0.0", None])
def test_pkg_resources_dependency_and_executed_import_contract(
    pipeline: tuple, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str], installed: str | None
) -> None:
    arguments, _, launches = pipeline
    result = preparation.prepare_speq(**arguments)
    assert result["status"] == "success"
    assert result["setuptools_version"] == "80.9.0"
    requirements = arguments["output"] / "evidence/requirements.in"
    assert requirements.read_text().splitlines() == [
        "egglog==13.2.0",
        "lark==1.1.7",
        "z3-solver==4.12.2.0",
        "setuptools==80.9.0",
    ]
    commands = {row["name"]: row["command"] for row in launches}
    lock = arguments["output"] / "evidence/requirements.lock"
    assert commands["python-lock"][-3:] == [str(requirements), "--output-file", str(lock)]
    assert commands["python-download"][-2:] == commands["python-install"][-2:] == ["-r", str(lock)]
    assert "--require-hashes" in commands["python-download"] and "--require-hashes" in commands["python-install"]

    # Execute the actual probe text with controlled imports, without loading Z3
    # or any native tool. It must fail before parser import for a missing API or
    # wrong provider version, even if egglog itself would import successfully.
    resources = ModuleType("pkg_resources")
    resources.__file__ = str(arguments["output"] / "python/lib/pkg_resources/__init__.py")
    monkeypatch.setitem(sys.modules, "pkg_resources", resources if installed else None)
    monkeypatch.setattr(importlib.metadata, "version", lambda name: installed if name == "setuptools" else "13.2.0")
    imported: list[Path] = []
    monkeypatch.setattr(preparation.record_speq, "import_parse_ir", imported.append)
    probe = commands["python-import"]
    monkeypatch.setattr(sys, "argv", ["-c", probe[-1]])
    if installed != "80.9.0":
        with pytest.raises(AssertionError if installed else ModuleNotFoundError):
            exec(probe[-2], {})
        assert not imported
    else:
        exec(probe[-2], {})
        observed = json.loads(capsys.readouterr().out)
        assert observed["setuptools"] == "80.9.0" and observed["pkg_resources"] == resources.__file__
        assert imported == [Path(probe[-1])]


def test_verified_historical_inputs_prepare_without_unretained_dockerfile(
    pipeline: tuple, monkeypatch: pytest.MonkeyPatch
) -> None:
    arguments, _, launches = pipeline
    receipt_path = arguments["artifact_receipt"]
    receipt = json.loads(receipt_path.read_text())
    del receipt["selected"]["Dockerfile"]
    receipt["mapping_files"] = receipt.pop("selected")
    receipt["member_index"] = "/removed/acquisition/evidence/speq-artifact-members.jsonl"
    receipt["member_index_sha256"] = receipt["member_index_sha256"].removeprefix("sha256:")
    receipt_path.write_text(json.dumps(receipt))
    original_receipt = receipt_path.read_bytes()
    member_index = receipt_path.with_name("speq-artifact-members.jsonl")
    receipt_path.with_name("members.jsonl").rename(member_index)
    (arguments["artifact_source"] / "Dockerfile").unlink()
    monkeypatch.setattr(
        preparation.urllib.request, "urlopen", lambda *args, **kwargs: pytest.fail("unexpected network")
    )

    result = preparation.prepare_speq(**arguments)

    assert result["status"] == "success", result["reason"]
    assert len(result["artifact_members"]) == 20
    assert set(result["artifact_members"]) == set(preparation.ARTIFACT_HASHES)
    provenance = result["artifact_provenance"]
    assert provenance["dockerfile"] == {
        "status": "not-retained",
        "archive_member": "lleq-artifact/Dockerfile",
        "size": preparation.DOCKERFILE_BYTES,
        "sha256": None,
        "used_by_native_preparation": False,
        "reason": "historical extraction omitted this unused provenance file",
    }
    assert Path(provenance["receipt"]).read_bytes() == receipt_path.read_bytes() == original_receipt
    assert Path(provenance["member_index"]).read_bytes() == member_index.read_bytes()
    assert Path(provenance["member_index"]).name == Path(receipt["member_index"]).name
    assert provenance["member_index_sha256"] == hashlib.sha256(member_index.read_bytes()).hexdigest()
    assert not (arguments["output"] / "sources/artifact/Dockerfile").exists()
    assert not any(row["name"] in ("artifact-acquisition", "rev-source-MemorySSA.h") for row in launches)
    assert any(row["name"] == "python-environment" for row in launches)
    assert any(row["name"] == "rev-build" for row in launches)
    assert len([row for row in launches if row["name"].startswith("reference-")]) == 4
    # Changing the old cache afterwards cannot change this preparation's inputs.
    (arguments["artifact_source"] / "parseIR.py").write_text("later cache edit")
    assert (arguments["output"] / "sources/artifact/parseIR.py").read_text() == "parseIR.py"
    settings = json.loads(Path(result["settings"]).read_text())["speq"]
    assert str(arguments["artifact_source"]) not in str(settings)


@pytest.mark.parametrize(
    "fault", ["version", "clang_version", "dockerfile", "archive-receipt", "source", "rev-source", "bad_reference"]
)
def test_dependency_gate_never_publishes_settings(pipeline: tuple, fault: str) -> None:
    arguments, state, _ = pipeline
    if fault == "version":
        state["version"] = "18.1.8"
    elif fault == "clang_version":
        state["clang_version"] = "18.1.8"
    elif fault == "dockerfile":
        (arguments["artifact_source"] / "Dockerfile").unlink()
    elif fault == "archive-receipt":
        receipt = json.loads(arguments["artifact_receipt"].read_text())
        receipt["full_archive_index_examined"] = False
        arguments["artifact_receipt"].write_text(json.dumps(receipt))
    elif fault == "source":
        (arguments["artifact_source"] / "parseIR.py").write_text("changed")
    elif fault == "rev-source":
        (arguments["lleq_source"] / "llvm/lib/Analysis/REVPass.cpp").write_text("changed")
    else:
        state["bad_reference"] = True
    result = preparation.prepare_speq(**arguments)
    assert result["status"] == "blocked" and result["reason"]
    if fault == "dockerfile":
        assert "Dockerfile and archive receipt disagree" in result["reason"]
    assert not (arguments["output"] / "settings.json").exists()


@pytest.mark.parametrize(
    "fault",
    [
        "archive-length",
        "archive-md5",
        "missing-index",
        "changed-index",
        "member-count",
        "missing-dockerfile-index",
        "duplicate-dockerfile-index",
        "nonregular-dockerfile-index",
        "dockerfile-unrecorded",
        "dockerfile-hash",
        "dockerfile-size",
        "missing-source",
        "oversized-source",
        "repinned-source",
    ],
)
def test_source_reuse_requires_complete_archive_evidence_and_independent_pins(pipeline: tuple, fault: str) -> None:
    arguments, _, launches = pipeline
    receipt_path = arguments["artifact_receipt"]
    receipt = json.loads(receipt_path.read_text())
    index = receipt_path.with_name("members.jsonl")
    dockerfile = arguments["artifact_source"] / "Dockerfile"
    if fault == "archive-length":
        receipt["compressed_bytes_read"] -= 1
    elif fault == "archive-md5":
        receipt["computed_archive_md5"] = "0" * 32
    elif fault == "missing-index":
        index.unlink()
    elif fault == "changed-index":
        index.write_bytes(index.read_bytes().replace(b"Dockerfile", b"Other-file"))
    elif fault == "member-count":
        receipt["member_count"] -= 1
    elif fault.endswith("-dockerfile-index"):
        members = [json.loads(line) for line in index.read_text().splitlines()]
        if fault == "missing-dockerfile-index":
            members.pop()
        elif fault == "duplicate-dockerfile-index":
            members.append(members[-1])
        else:
            members[-1]["type"] = "2"
        index.write_text("".join(json.dumps(member) + "\n" for member in members))
        receipt["member_count"] = len(members)
        receipt["member_index_sha256"] = preparation.sha256_file(index)
    elif fault == "dockerfile-unrecorded":
        del receipt["selected"]["Dockerfile"]
    elif fault == "dockerfile-hash":
        dockerfile.write_bytes(b"X" * preparation.DOCKERFILE_BYTES)
    elif fault == "dockerfile-size":
        dockerfile.write_bytes(b"FROM too short\nextra")
        receipt["selected"]["Dockerfile"] = hashlib.sha256(dockerfile.read_bytes()).hexdigest()
    elif fault == "missing-source":
        (arguments["artifact_source"] / "parseIR.py").unlink()
    elif fault == "oversized-source":
        (arguments["artifact_source"] / "parseIR.py").write_bytes(b"X" * 1_000_001)
    else:
        source = arguments["artifact_source"] / "parseIR.py"
        source.write_text("changed source with a matching but untrusted receipt entry")
        receipt["selected"]["parseIR.py"] = hashlib.sha256(source.read_bytes()).hexdigest()
    receipt_path.write_text(json.dumps(receipt))

    result = preparation.prepare_speq(**arguments)

    assert result["status"] == "blocked" and result["reason"]
    assert not any(row["name"] == "python-environment" for row in launches)
    assert not (arguments["output"] / "settings.json").exists()


@pytest.mark.parametrize("kind,status", [("guard", "resource-stopped"), ("stop", "memory-limit")])
def test_guard_stops_before_dependent_native_steps(pipeline: tuple, kind: str, status: str) -> None:
    arguments, state, launches = pipeline
    state[kind] = "rev-build"
    result = preparation.prepare_speq(**arguments)
    assert result["status"] == status and launches[-1]["name"] == "rev-build"
    assert not (arguments["output"] / "settings.json").exists()


def test_retained_preparation_cannot_be_overwritten(pipeline: tuple) -> None:
    arguments, _, launches = pipeline
    arguments["output"].mkdir(parents=True)
    (arguments["output"] / "evidence").write_text("preserved")
    with pytest.raises(ValueError, match="fresh directory"):
        preparation.prepare_speq(**arguments)
    assert not launches and (arguments["output"] / "evidence").read_text() == "preserved"


@pytest.mark.parametrize("fault", ["missing", "changed"])
def test_custom_memoryssa_header_is_required_before_any_plugin_build(pipeline: tuple, fault: str) -> None:
    arguments, _, launches = pipeline
    header = arguments["lleq_source"] / "llvm/include/llvm/Analysis/MemorySSA.h"
    if fault == "missing":
        header.unlink()
    else:
        header.write_text("stock LLVM header lacks the artifact's public memory version ID")
    result = preparation.prepare_speq(**arguments)
    assert result["status"] == "blocked" and "MemorySSA.h" in result["reason"]
    assert not any(row["name"] == "rev-build" for row in launches)
    assert not (arguments["output"] / "settings.json").exists()


@pytest.mark.parametrize("fault", [None, "failure", "memory-limit", "resource-stopped", "timed-out"])
def test_c99_preparation_publishes_only_after_guarded_fresh_gates(
    pipeline: tuple,
    monkeypatch: pytest.MonkeyPatch,
    fault: Literal["failure", "memory-limit", "resource-stopped", "timed-out"] | None,
) -> None:
    arguments, state, launches = pipeline
    gate_module = ModuleType("scripts.speq_c99_gates")

    def gates(source: Path, artifact: Path, llvm: Path, output: Path, step: Any) -> dict:
        assert source == arguments["output"] / "sources/lleq"
        assert artifact == arguments["output"] / "sources/artifact"
        step("c99-probe", ["mock-native-only"])
        if fault == "failure":
            raise ValueError("mock invalid fixture/comparison")
        output.mkdir()
        evidence = output / "result.json"
        evidence.write_text("mock fresh source/tool gates")
        return {
            "status": "success",
            "contract": "polybench-gemm-address-v1",
            "artifacts": {str(evidence): preparation.sha256_file(evidence)},
        }

    gate_module.run_gates = gates  # type: ignore[attr-defined]
    monkeypatch.setitem(sys.modules, "scripts.speq_c99_gates", gate_module)
    if fault in {"memory-limit", "resource-stopped", "timed-out"}:
        original = preparation.run_bounded_command

        def stopped(command: list[str], cwd: Path, prefix: Path, **kwargs: Any) -> PilotProcessResult:
            result = original(command, cwd, prefix, **kwargs)
            if prefix.name.endswith("c99-probe"):
                assert fault is not None
                return PilotProcessResult(fault, None, 0, 0, result.stdout_path, result.stderr_path, "mock stop")
            return result

        monkeypatch.setattr(preparation, "run_bounded_command", stopped)
    result = preparation.prepare_speq(**arguments, c99_frontend_repair="polybench-gemm-address-v1")
    launch = next(row for row in launches if row["name"] == "c99-probe")
    assert launch["options"]["memory_limit_bytes"] == 5 * 1024**3
    assert launch["options"]["require_guard"] and launch["options"]["disk_reserve_bytes"] == 10 * 1024**3
    if fault:
        assert result["status"] == ("blocked" if fault == "failure" else fault)
        assert not (arguments["output"] / "settings.json").exists()
        assert launches[-1]["name"] == "c99-probe"
    else:
        settings = json.loads(Path(result["settings"]).read_text())["speq"]
        assert settings["c99_frontend_repair"] == "polybench-gemm-address-v1"
        assert settings["phi_polarity_repair"] is True
        assert str(arguments["output"] / "c99-gates") in settings["identity_paths"]


def test_public_family_preparation_requests_the_reviewed_c99_gates(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    from scripts.reproduction_preparation import prepare_family

    engine = tmp_path / "ordinary"
    engine.write_text("mock ordinary engine")
    calls = []

    def prepare(output: Path, selected_engine: Path, **kwargs: Any) -> dict[str, Any]:
        calls.append((output, selected_engine, kwargs))
        output.mkdir()
        settings = output / "settings.json"
        settings.write_text(json.dumps({"speq": {"paths": {"egglog": str(selected_engine)}}}))
        return {"status": "success", "settings": str(settings)}

    monkeypatch.setattr(preparation, "prepare_speq", prepare)
    result = prepare_family("speq", tmp_path, engine)
    assert result["status"] == "success"
    assert calls == [
        (
            tmp_path / "environment",
            engine,
            {
                "llvm_config": Path("/opt/homebrew/opt/llvm@17/bin/llvm-config"),
                "acquire_archive": True,
                "c99_frontend_repair": "polybench-gemm-address-v1",
            },
        )
    ]
