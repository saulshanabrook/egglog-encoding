"""SpEQ preparation contracts; mocked native commands and in-memory archive bytes."""

from __future__ import annotations

import hashlib
import io
import json
import tarfile
from pathlib import Path
from typing import Any

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
    archive_receipt.write_text(
        json.dumps(
            {
                "computed_archive_md5": preparation.record_speq.SPEQ_ARCHIVE_MD5,
                "compressed_bytes_read": preparation.ARCHIVE_BYTES,
                "full_archive_index_examined": True,
                "selected": {**hashes, "Dockerfile": hashlib.sha256(dockerfile).hexdigest()},
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
    assert settings["frontend_flags"] == []
    assert Path(settings["paths"]["speq_artifact"]).is_relative_to(arguments["output"])
    assert "speq_rev_plugin.cpp" in str(settings["identity_paths"])
    assert result["python_wheels"]["resolved.whl"]
    assert (arguments["artifact_source"] / "parseIR.py").read_text() == "parseIR.py"
    assert (arguments["output"] / "sources/artifact/requirements.txt").read_text() == "requirements.txt"


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
        assert "--acquire-archive" in result["reason"]
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
