"""Capture boundaries preserve independent calls and verified artifact inputs."""

from __future__ import annotations

import hashlib
import io
import json
import subprocess
import tarfile
from dataclasses import asdict
from pathlib import Path
from typing import Any, Literal

import pytest

from benchmarking.pilot import PilotProcessResult
from scripts import suite_capture_dialegg_speq as capture
from scripts.paper_benchmarks import record_speq


@pytest.mark.parametrize("chunks", ([], ["first FIR\n"], ["first FIR\n", "second FIR\n"]))
def test_speq_source_frontend_retains_all_chunks_and_rejects_changed_invocation_count(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, chunks: list[str]
) -> None:
    source = tmp_path / "artifact/benchmarks/spmv_npb.c"
    source.parent.mkdir(parents=True)
    source.write_text("void spmv_npb(void) {}\n")
    monkeypatch.setattr(record_speq, "APPLICATION_C_SHA256", {"spmv_npb": record_speq.sha256_text(source.read_text())})
    commands = []

    def run(command: list[str], **kwargs: Any) -> subprocess.CompletedProcess[str]:
        commands.append(command)
        Path(command[-1]).write_text("; native LLVM output\n")
        if command[0].endswith("/opt"):
            kwargs["stderr"].write("".join(f"REV Start\n{chunk}REV End\n" for chunk in chunks).encode())
        return subprocess.CompletedProcess(command, 0)

    monkeypatch.setattr(record_speq.subprocess, "run", run)
    evidence = tmp_path / "evidence"
    arguments = (source.parent.parent, tmp_path / "llvm/bin/opt", tmp_path / "rev.dylib", "spmv_npb", evidence)
    if len(chunks) == 1:
        assert record_speq.application_fir(*arguments) == chunks[0]
    else:
        with pytest.raises(ValueError, match=f"got {len(chunks)}; all chunks retained"):
            record_speq.application_fir(*arguments)
    manifest = json.loads((evidence / "manifest.json").read_text())
    assert len(manifest["chunks"]) == len(chunks)
    assert [Path(chunk["path"]).read_text() for chunk in manifest["chunks"]] == chunks
    assert commands[0][1:7] == ["-S", "-emit-llvm", "-O0", "-Xclang", "-disable-O0-optnone", "-fno-discard-value-names"]
    assert "-enable-load-in-loop-pre=false" in commands[1]
    assert "-passes=mem2reg,loop-rotate,instcombine,simplifycfg,loop-simplify,gvn,lcssa,print<revpass>" in commands[1]
    with pytest.raises(FileExistsError):
        record_speq.application_fir(*arguments)


def test_speq_source_hash_drift_blocks_frontend_before_launch(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    source = tmp_path / "benchmarks/spmv_npb.c"
    source.parent.mkdir()
    source.write_text("changed source")

    def unexpected_run(*args: Any, **kwargs: Any) -> None:
        raise AssertionError("changed C input must not launch the compiler")

    monkeypatch.setattr(record_speq.subprocess, "run", unexpected_run)
    with pytest.raises(ValueError, match="unexpected source"):
        record_speq.application_fir(tmp_path, tmp_path / "opt", tmp_path / "plugin", "spmv_npb", tmp_path / "evidence")


def test_speq_frontend_failure_preserves_command_and_diagnostics(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    source = tmp_path / "benchmarks/spmv_npb.c"
    source.parent.mkdir()
    source.write_text("void spmv_npb(void) {}")
    monkeypatch.setattr(record_speq, "APPLICATION_C_SHA256", {"spmv_npb": record_speq.sha256_text(source.read_text())})

    def fail(command: list[str], **kwargs: Any) -> subprocess.CompletedProcess[str]:
        kwargs["stderr"].write(b"original compiler diagnostic\n")
        return subprocess.CompletedProcess(command, 1)

    monkeypatch.setattr(record_speq.subprocess, "run", fail)
    evidence = tmp_path / "evidence"
    with pytest.raises(ValueError, match="frontend command failed"):
        record_speq.application_fir(tmp_path, tmp_path / "opt", tmp_path / "plugin", "spmv_npb", evidence)
    manifest = json.loads((evidence / "manifest.json").read_text())
    assert manifest["chunks"] == []
    assert len(manifest["commands"]) == 1
    assert manifest["commands"][0]["returncode"] == 1
    assert (evidence / "frontend-0.stderr.log").read_text() == "original compiler diagnostic\n"


def test_dialegg_modernization_preserves_schedule_lookup_merges_and_extraction_order() -> None:
    source = """(include "src/base.egg")
(function linalg_matmul (Op Op Op Type) Op)
(function nrows (Type) i64)
(let op0 (Value 0 (I32)))
(let op1 (Value 1 (I32)))
(rule ((= a (nrows t))) ((unstable-cost (linalg_matmul x y z t) a)))
(run-schedule (saturate rules))
(extract op1)
(extract op0)
"""
    modern = capture.modernize_dialegg_invocation(source, "(function type-of (Op) Type :merge old)")
    assert '(include "src/base.egg")' not in modern
    assert "(function type-of (Op) Type :merge old)" in modern
    assert "(function nrows (Type) i64 :merge old)" in modern
    assert "(with-dynamic-cost (constructor linalg_matmul (Op Op Op Type) Op))" in modern
    assert modern.endswith("(run-schedule (saturate rules))\n(extract $op1)\n(extract $op0)\n")
    assert "(set-cost (linalg_matmul x y z t) a)" in modern
    with pytest.raises(ValueError, match="expected exactly one shared prelude"):
        capture.modernize_dialegg_invocation(source + '(include "src/base.egg")', "")


def test_frozen_shape_oracle_is_appended_only_to_its_exact_original_invocation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    source = '(include "src/base.egg")\n(let op0 (Value 0 (I64)))\n(run-schedule (saturate rules))\n'
    prelude = "(function type-of (Op) Type :merge old)"
    unchanged = capture.modernize_dialegg_invocation(source, prelude)
    check = "(check (= (nrows (type-of $op0)) 100))"
    meaning = "source tensor row count"
    monkeypatch.setattr(
        capture, "DIALEGG_SHAPE_QUERIES", {hashlib.sha256(source.encode()).hexdigest(): (check, meaning)}
    )
    assert capture.modernize_dialegg_invocation(source, prelude) == (
        unchanged + f"\n;; Diagnostic query: {meaning}.\n{check}\n"
    )
    assert "(check " not in capture.modernize_dialegg_invocation(source + "; changed source\n", prelude)


@pytest.mark.parametrize("complete_index", (False, True))
def test_stream_saves_only_verified_required_members(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, complete_index: bool
) -> None:
    parse_ir = b"pinned parseIR"
    run_benchmark = b"pinned benchmark"
    archive_data = io.BytesIO()
    with tarfile.open(fileobj=archive_data, mode="w:gz") as archive:
        for name, data in (
            ("large-unused", b"x" * 100_000),
            ("parseIR.py", parse_ir),
            ("run_benchmark.py", run_benchmark),
            ("benchmarks/tpal.c", b"benchmark input"),
        ):
            member = tarfile.TarInfo("lleq-artifact/" + name)
            member.size = len(data)
            archive.addfile(member, io.BytesIO(data))
    compressed = archive_data.getvalue()
    monkeypatch.setattr(capture.record_speq, "SPEQ_ARCHIVE_MD5", hashlib.md5(compressed).hexdigest())
    metadata = {
        "files": [
            {
                "checksum": "md5:" + capture.record_speq.SPEQ_ARCHIVE_MD5,
                "size": len(compressed),
                "links": {"self": "https://example.invalid/artifact"},
            }
        ]
    }

    class Response(io.BytesIO):
        status = 206
        headers = {"Content-Range": f"bytes 0-{len(compressed) - 1}/{len(compressed)}"}

    responses = iter(
        [Response(json.dumps(metadata).encode())]
        + ([Response(compressed[:-1])] if complete_index else [])
        + [Response(compressed)]
    )

    def open_response(*_args: Any, **_kwargs: Any) -> Response:
        return next(responses)

    monkeypatch.setattr(capture, "STORAGE", tmp_path)
    monkeypatch.setattr(capture.record_speq, "PARSE_IR_SHA256", hashlib.sha256(parse_ir).hexdigest())
    monkeypatch.setattr(capture.record_speq, "RUN_BENCHMARK_SHA256", hashlib.sha256(run_benchmark).hexdigest())
    monkeypatch.setattr(capture.record_speq, "REFERENCE_ANALYSIS_SHA256", {})
    monkeypatch.setattr(capture.record_speq, "APPLICATION_C_SHA256", {})
    monkeypatch.setattr(capture.urllib.request, "urlopen", open_response)
    monkeypatch.setattr(capture.time, "sleep", lambda _seconds: None)
    evidence = capture.stream_speq_artifact(None, complete_index=complete_index)
    assert not evidence["missing"]
    assert evidence["compressed_bytes_read"] <= len(compressed)
    assert sorted(path.name for path in (tmp_path / "sources/speq/artifact").iterdir()) == (
        ["benchmarks", "parseIR.py", "run_benchmark.py"] if complete_index else ["parseIR.py", "run_benchmark.py"]
    )
    assert evidence["full_archive_index_examined"] == complete_index
    if complete_index:
        assert evidence["computed_archive_md5"] == hashlib.md5(compressed).hexdigest()
        assert evidence["member_count"] == 4
        index = [json.loads(line) for line in Path(evidence["member_index"]).read_text().splitlines()]
        assert index[-1]["name"] == "lleq-artifact/benchmarks/tpal.c"
        assert evidence["mapping_files"]["benchmarks/tpal.c"] == hashlib.sha256(b"benchmark input").hexdigest()
    assert (tmp_path / "sources/speq/artifact/parseIR.py").read_bytes() == parse_ir
    assert capture.stream_speq_artifact(None)["reused_verified_members"]
    (tmp_path / "sources/speq/artifact/parseIR.py").write_bytes(b"changed")
    with pytest.raises(ValueError, match="cached artifact member digest mismatch"):
        capture.stream_speq_artifact(None)


def test_oracle_gate_discards_seeded_equalities_and_rejects_unrelated_failures(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    source = (
        "(let $x (Seed))\n(run-schedule (saturate rules)) ; source schedule\n"
        "(check (= $x (Seed)))\n(check (= $x (Derived)))\n"
    )

    def run(command: list[str], cwd: Path, prefix: Path) -> PilotProcessResult:
        program = Path(command[1]).read_text()
        assert "(run-schedule" not in program
        is_seeded = program.endswith("(check (= $x (Seed)))\n")
        stdout = prefix.with_suffix(".out")
        stderr = prefix.with_suffix(".err")
        stdout.write_text("")
        stderr.write_text("" if is_seeded else "    Check failed: (= $x (Derived))\n")
        return PilotProcessResult(
            "success" if is_seeded else "failure", 0 if is_seeded else 1, 0, 0, stdout, stderr, None
        )

    monkeypatch.setattr(capture, "run_bounded_command", run)
    filtered, evidence = capture.retain_derived_oracles(source, tmp_path / "egglog", tmp_path / "oracles")
    assert evidence["retained_checks"] == 1
    assert "(check (= $x (Seed)))" not in filtered
    assert "(check (= $x (Derived)))" in filtered
    assert "(run-schedule (saturate rules))" in filtered

    def parse_error(command: list[str], cwd: Path, prefix: Path) -> PilotProcessResult:
        stdout = prefix.with_suffix(".out")
        stderr = prefix.with_suffix(".err")
        stdout.write_text("")
        stderr.write_text("Parse error: malformed Check failed: string\n")
        return PilotProcessResult("failure", 1, 0, 0, stdout, stderr, "parse error")

    monkeypatch.setattr(capture, "run_bounded_command", parse_error)
    with pytest.raises(ValueError, match="without an ordinary Check failed diagnostic"):
        capture.retain_derived_oracles(source, tmp_path / "egglog", tmp_path / "parse-error")


def test_paper_reconciliation_requires_complete_verified_index(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(capture, "STORAGE", tmp_path)
    mapping_name = "figures/table3/draw_table3.py"
    mapping = tmp_path / "sources/speq/artifact" / mapping_name
    mapping.parent.mkdir(parents=True)
    mapping.write_text("names = {'tpal_spmv': 'TPAL', 'tsvc': 'TSVC2'}\nbenchmarks = []\n")
    evidence_dir = tmp_path / "evidence"
    evidence_dir.mkdir()
    index = evidence_dir / "speq-artifact-members.jsonl"
    index.write_text(json.dumps({"name": "lleq-artifact/README.md"}) + "\n")
    metadata = {
        "full_archive_index_examined": False,
        "computed_archive_md5": capture.record_speq.SPEQ_ARCHIVE_MD5,
        "mapping_files": {mapping_name: hashlib.sha256(mapping.read_bytes()).hexdigest()},
        "member_index_sha256": hashlib.sha256(index.read_bytes()).hexdigest(),
        "member_count": 1,
    }
    manifest = evidence_dir / "speq-artifact-index.json"
    manifest.write_text(json.dumps(metadata))
    assert "absent" not in capture.reconcile_speq_paper_cases()["speq-tpal"]["reason"]
    metadata["full_archive_index_examined"] = True
    manifest.write_text(json.dumps(metadata))
    cases = capture.reconcile_speq_paper_cases()
    assert cases["speq-tpal"]["artifact_name"] == "tpal_spmv"
    assert "absent" in cases["speq-tsvc2"]["reason"]
    assert cases["speq-tsvc2"]["present_artifact_members"] == []
    index.write_text(index.read_text() + json.dumps({"name": "lleq-artifact/benchmarks/tsvc.c"}) + "\n")
    with pytest.raises(ValueError, match="index changed"):
        capture.reconcile_speq_paper_cases()
    metadata["member_index_sha256"] = hashlib.sha256(index.read_bytes()).hexdigest()
    metadata["member_count"] = 2
    manifest.write_text(json.dumps(metadata))
    present = capture.reconcile_speq_paper_cases()["speq-tsvc2"]
    assert present["present_artifact_members"] == ["benchmarks/tsvc.c"]
    assert "absent" not in present["reason"]


@pytest.mark.parametrize("status", ("resource-stopped", "memory-limit"))
@pytest.mark.parametrize("stop_at", range(4))
def test_dialegg_build_safety_stop_retains_evidence_and_skips_remaining_builds_and_cases(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    status: Literal["resource-stopped", "memory-limit"],
    stop_at: int,
) -> None:
    monkeypatch.setattr(capture, "ROOT", tmp_path)
    monkeypatch.setattr(capture, "STORAGE", tmp_path / "storage")
    source = capture.STORAGE / "sources/dialegg/src"
    source.mkdir(parents=True)
    (source / "Egglog.cpp").write_text("// cached source\n")
    (source / "EqualitySaturationPass.cpp").write_text(
        "std::ofstream eggFileOut(opsEggFilePath);\neggFileOut.close();\n"
        "runEgglog(egglog.eggifiedBlock, blockName); // Run egglog on the block\n"
    )
    calls: list[dict[str, Any]] = []

    def run(command: list[str], cwd: Path, prefix: Path) -> PilotProcessResult:
        assert len(calls) <= stop_at, "a build ran after the safety stop"
        prefix.parent.mkdir(parents=True, exist_ok=True)
        stdout, stderr = prefix.with_suffix(".out"), prefix.with_suffix(".err")
        stdout.write_text("compiler progress\n")
        stderr.write_text("compiler diagnostics\n")
        stopped = len(calls) == stop_at
        process = PilotProcessResult(
            status if stopped else "success",
            -9 if stopped else 0,
            0.5,
            1234,
            stdout,
            stderr,
            "build resource guard" if stopped else None,
        )
        calls.append({"command": command, **asdict(process)})
        return process

    monkeypatch.setattr(capture, "run_bounded_command", run)
    result = capture.capture_dialegg(tmp_path / "llvm", tmp_path / "missing-engine")
    assert len(calls) == stop_at + 1
    assert result["preparation"]["builds"] == calls
    assert result["operational_stop"] == calls[-1]
    assert result["cases"] == {}
    assert calls[-1]["stderr_path"].read_text() == "compiler diagnostics\n"
    assert not (capture.STORAGE / "evidence/capture").exists()


@pytest.mark.parametrize("status", ("resource-stopped", "memory-limit"))
@pytest.mark.parametrize("stage", ("frontend", "extraction", "query", "oracle"))
def test_dialegg_safety_stop_preserves_prior_captures_and_never_launches_another_invocation(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    status: Literal["resource-stopped", "memory-limit"],
    stage: str,
) -> None:
    monkeypatch.setattr(capture, "ROOT", tmp_path)
    monkeypatch.setattr(capture, "STORAGE", tmp_path / "storage")
    monkeypatch.setattr(capture, "DIALEGG_INPUTS", {name: f"{name}.mlir" for name in ("first", "stopped", "pending")})
    monkeypatch.setenv("DIALEGG_CAPTURE_DIR", "original-capture-directory")
    source = capture.STORAGE / "sources/dialegg"
    (source / "src").mkdir(parents=True)
    base = "(function type-of (Op) Type)\n(function dims (Type) IntVec)\n"
    (source / "src/base.egg").write_text(base)
    monkeypatch.setattr(capture.materialize, "DIALEGG_BASE_SHA256", hashlib.sha256(base.encode()).hexdigest())
    for name in capture.DIALEGG_INPUTS:
        (source / f"{name}.mlir").write_text(f"source {name}\n")
    binary = tmp_path / "egglog"
    binary.write_text("mock engine, never executed\n")
    monkeypatch.setattr(capture, "prepare_dialegg", lambda _prefix: (tmp_path / "frontend", {"builds": []}))
    raw = '(include "src/base.egg")\n(let op0 (Seed))\n(let op1 (Seed))\n(run-schedule (saturate rules))\n'
    extracted_raw = raw + "(extract op0)\n(extract op1)\n"
    monkeypatch.setattr(
        capture,
        "DIALEGG_SHAPE_QUERIES",
        {hashlib.sha256(raw.encode()).hexdigest(): ("(check (= (nrows (type-of $op0)) 100))", "source row count")},
    )
    stopped: PilotProcessResult | None = None
    calls: list[Path] = []

    def run(command: list[str], cwd: Path, prefix: Path) -> PilotProcessResult:
        nonlocal stopped
        assert stopped is None, "an invocation ran after the safety stop"
        calls.append(prefix)
        case = "stopped" if "stopped" in prefix.parts else "first"
        if prefix.name == "capture":
            directory = Path(capture.os.environ["DIALEGG_CAPTURE_DIR"])
            count = 1 if case == "first" else 3
            for index in range(count):
                text = raw if stage in ("query", "oracle") and index == 1 else extracted_raw
                (directory / f"invocation-{index}.egg").write_text(text)
        stdout, stderr = prefix.with_suffix(".out"), prefix.with_suffix(".err")
        stdout.write_text("(Derived)\n(Derived)\n" if prefix.name.endswith("-extract") else "")
        negative = prefix.name.startswith("no-schedule-")
        stderr.write_text("    Check failed: original query\n" if negative else "retained diagnostics\n")
        stop_here = case == "stopped" and (
            (stage == "frontend" and prefix.name == "capture")
            or (
                stage in ("extraction", "query")
                and prefix.name == f"invocation-1-{'extract' if stage == 'extraction' else 'query'}"
            )
            or (stage == "oracle" and prefix.parent.name == "invocation-1-oracles" and prefix.name == "no-schedule-0")
        )
        process = PilotProcessResult(
            status if stop_here else "failure" if negative else "success",
            -9 if stop_here else 1 if negative else 0,
            0.5,
            1234,
            stdout,
            stderr,
            "capture resource guard" if stop_here else None,
        )
        if stop_here:
            stopped = process
        return process

    monkeypatch.setattr(capture, "run_bounded_command", run)
    result = capture.capture_dialegg(tmp_path / "llvm", binary)
    assert stopped is not None
    assert capture.os.environ["DIALEGG_CAPTURE_DIR"] == "original-capture-directory"
    assert list(result["cases"]) == ["first", "stopped"]
    assert result["cases"]["first"]["status"] == "captured"
    restored = (tmp_path / result["cases"]["first"]["workloads"][0]).read_text()
    assert "(extract $op0)\n(extract $op1)" in restored
    assert "(check " not in restored
    blocked = result["cases"]["stopped"]
    assert blocked["status"] == "blocked"
    assert result["operational_stop"] == {**({"derived": False} if stage == "oracle" else {}), **asdict(stopped)}
    assert stopped.stderr_path.is_file()
    if stage == "frontend":
        assert blocked["invocations"] == []
        assert len(blocked["raw_invocations"]) == 3
        assert all((tmp_path / path).read_text() == extracted_raw for path in blocked["raw_invocations"])
    else:
        assert len(blocked["invocations"]) == 2
        assert blocked["invocations"][0]["status"] == "captured"
        assert (tmp_path / blocked["workloads"][0]).is_file()
        invocation = blocked["invocations"][1]
        assert invocation["status"] == "blocked"
        assert (tmp_path / invocation["raw"]).is_file()
        assert not (capture.STORAGE / "workloads/dialegg/stopped-001.egg").exists()
        if stage == "oracle":
            checks = invocation["oracle_validation"]["negative_checks"]
            assert len(checks) == 1
            assert invocation["oracle_validation"]["retained_checks"] == 0
            assert checks[0] == result["operational_stop"]
        else:
            key = "extraction" if stage == "extraction" else "query_validation"
            assert invocation[key] == result["operational_stop"]
    assert len(calls) == {"frontend": 3, "extraction": 5, "query": 5, "oracle": 6}[stage]


def test_dialegg_oracle_rejects_a_panic_even_when_it_contains_check_failed(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    source = "(run-schedule (saturate rules))\n(check (= $x (Derived)))\n(check (= $y (Derived)))\n"
    calls: list[list[str]] = []

    def run(command: list[str], cwd: Path, prefix: Path) -> PilotProcessResult:
        calls.append(command)
        stdout, stderr = prefix.with_suffix(".out"), prefix.with_suffix(".err")
        stdout.write_text("")
        stderr.write_text("    Check failed: (= $x (Derived))\nthread panicked\n")
        return PilotProcessResult("failure", 101, 0.5, 1234, stdout, stderr, "engine panic")

    monkeypatch.setattr(capture, "run_bounded_command", run)
    with pytest.raises(ValueError, match="without an ordinary Check failed diagnostic: engine panic"):
        capture.retain_derived_oracles(source, tmp_path / "egglog", tmp_path / "oracles")
    assert len(calls) == 1
    assert not (tmp_path / "oracles/no-schedule-1.egg").exists()


@pytest.mark.parametrize("status", ("resource-stopped", "memory-limit"))
@pytest.mark.parametrize("application", (False, True))
def test_speq_recording_safety_stop_retains_partial_trace_and_skips_remaining_cases(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    status: Literal["resource-stopped", "memory-limit"],
    application: bool,
) -> None:
    monkeypatch.setattr(capture, "ROOT", tmp_path)
    monkeypatch.setattr(capture, "STORAGE", tmp_path / "storage")
    monkeypatch.setattr(capture, "SPEQ_NAMES", ("first", "stopped", "pending"))
    monkeypatch.setattr(
        capture.record_speq, "APPLICATION_C_SHA256", {"stopped": "source digest"} if application else {}
    )
    monkeypatch.setattr(capture, "fetch_verified_source", lambda _url, _path, expected: expected)
    monkeypatch.setattr(capture.record_speq, "extract_rev_test", lambda _path, name: f"FIR {name}\n")

    def unexpected_reconcile() -> None:
        raise AssertionError("paper-case reconciliation ran after the safety stop")

    monkeypatch.setattr(capture, "reconcile_speq_paper_cases", unexpected_reconcile)
    calls: list[list[str]] = []
    source_manifest = {"commands": [{"returncode": -9}], "chunks": [{"sha256": "captured FIR digest"}]}
    stopped: PilotProcessResult | None = None

    def run(command: list[str], cwd: Path, prefix: Path) -> PilotProcessResult:
        nonlocal stopped
        assert stopped is None, "a recorder ran after the safety stop"
        calls.append(command)
        name = command[command.index("--benchmark") + 1]
        assert name in ("first", "stopped")
        trace = Path(command[2])
        trace.with_name(f"{trace.stem}-000.egg").write_text(f"partial trace {name}\n")
        stdout, stderr = prefix.with_suffix(".out"), prefix.with_suffix(".err")
        stdout.write_text("recorder progress\n")
        stderr.write_text("recorder diagnostics\n")
        if name == "first":
            output = Path(command[command.index("--output") + 1])
            output.parent.mkdir(parents=True, exist_ok=True)
            output.write_text("first captured workload\n")
        elif application:
            manifest = Path(command[command.index("--source-evidence") + 1]) / name / "manifest.json"
            manifest.parent.mkdir(parents=True)
            manifest.write_text(json.dumps(source_manifest))
        process = PilotProcessResult(
            status if name == "stopped" else "success",
            -9 if name == "stopped" else 0,
            0.5,
            1234,
            stdout,
            stderr,
            "recorder resource guard" if name == "stopped" else None,
        )
        if name == "stopped":
            stopped = process
        return process

    monkeypatch.setattr(capture, "run_bounded_command", run)
    result = capture.capture_speq(tmp_path / "artifact", tmp_path / "python", tmp_path / "llvm-config", None)
    assert stopped is not None
    assert len(calls) == 2
    assert list(result["cases"]) == ["speq-first", "speq-stopped"]
    assert result["cases"]["speq-first"]["status"] == "captured"
    assert (tmp_path / result["cases"]["speq-first"]["workloads"][0]).read_text() == "first captured workload\n"
    blocked = result["cases"]["speq-stopped"]
    assert blocked["status"] == "blocked"
    assert blocked["workloads"] == []
    assert blocked["command"] == calls[-1]
    assert blocked["process"] == result["operational_stop"] == asdict(stopped)
    assert blocked["reason"] == "recorder resource guard"
    assert len(blocked["raw_invocations"]) == 1
    raw = blocked["raw_invocations"][0]
    assert (tmp_path / raw).read_text() == "partial trace stopped\n"
    assert blocked["raw_invocation_sha256"] == {raw: hashlib.sha256((tmp_path / raw).read_bytes()).hexdigest()}
    assert stopped.stderr_path.read_text() == "recorder diagnostics\n"
    if application:
        assert blocked["source_frontend"] == source_manifest
        assert blocked["fir_sha256"] == "captured FIR digest"
    else:
        assert blocked["fir_sha256"] == hashlib.sha256(b"FIR stopped\n").hexdigest()


@pytest.mark.parametrize("status", ("resource-stopped", "memory-limit"))
def test_main_all_persists_safety_stop_and_does_not_start_the_next_family(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str], status: str
) -> None:
    monkeypatch.setattr(capture, "STORAGE", tmp_path)
    monkeypatch.setattr(capture.sys, "argv", ["capture", "--family", "all"])
    result = {
        "preparation": {},
        "cases": {"dialegg-stopped": {"status": "blocked", "workloads": [], "reason": "resource guard"}},
        "operational_stop": {"status": status, "stderr_path": tmp_path / "failure.stderr.log"},
    }
    monkeypatch.setattr(capture, "capture_dialegg", lambda _prefix, _egglog: result)

    def unexpected_speq(*args: Any, **kwargs: Any) -> None:
        raise AssertionError("SpEQ started after the DialEgg safety stop")

    monkeypatch.setattr(capture, "capture_speq", unexpected_speq)
    assert capture.main() == 2
    assert json.loads((tmp_path / "evidence/dialegg-capture-results.json").read_text()) == json.loads(
        json.dumps(result, default=str)
    )
    assert not (tmp_path / "evidence/speq-capture-results.json").exists()
    assert "remaining cases are pending" in capsys.readouterr().err


def test_speq_normalization_preserves_original_extract_options_and_scope_order() -> None:
    source = """(datatype E (Seed))
(push 1)
(let $__expr_0 (Seed))
(let $speq-root-first $__expr_0)
(run 5)
(extract $speq-root-first 0)
(pop 1)
(push 1)
(let $__expr_1 (Seed))
(let $speq-root-second $__expr_1)
(run 3)
(extract $speq-root-second 2)
(pop 1)
"""
    normalized = record_speq.normalize_recording(source, ["first", "second"])
    assert "(extract $speq-root-first 0)\n(pop 1)" in normalized
    assert "(extract $speq-root-second 2)\n(pop 1)" in normalized
    assert normalized.index("(run 5)") < normalized.index("(extract $speq-root-first")
    assert normalized.index("(run 3)") < normalized.index("(extract $speq-root-second")
    assert "(check " not in normalized
    assert "$__expr_" not in normalized


def test_public_complete_cli_forwards_explicit_speq_frontend_flags(monkeypatch: pytest.MonkeyPatch) -> None:
    from scripts import dialegg_speq_complete as complete

    received = []

    def complete_args(args: Any) -> int:
        received.append(args)
        return 0

    monkeypatch.setattr(complete, "complete_capture", complete_args)
    monkeypatch.setattr(
        capture.sys,
        "argv",
        [
            "capture",
            "--complete",
            "--family",
            "speq",
            "--output",
            "/unused/fresh",
            "--egglog",
            "/unused/engine",
            "--speq-artifact",
            "/unused/artifact",
            "--speq-frontend-flag=-D_FORTIFY_SOURCE=0",
            "--speq-frontend-flag=-DPOLYBENCH_USE_C99_PROTO",
            "--speq-phi-polarity-repair",
        ],
    )
    assert capture.main() == 0
    assert received[0].speq_frontend_flag == ["-D_FORTIFY_SOURCE=0", "-DPOLYBENCH_USE_C99_PROTO"]
    assert received[0].speq_phi_polarity_repair
    monkeypatch.setattr(capture.sys, "argv", ["capture", "--speq-frontend-flag=-D_FORTIFY_SOURCE=0"])
    with pytest.raises(SystemExit):
        capture.main()


def test_public_phi_repair_switch_cannot_enter_historical_capture(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(capture.sys, "argv", ["capture", "--speq-phi-polarity-repair"])
    with pytest.raises(SystemExit):
        capture.main()
