"""MISAAL replays preserve source extraction and separate ordinary/proof validation."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path

import pytest

from scripts import suite_capture_hardboiled_misaal as capture


def test_complete_gpu_capture_keeps_parameters_outputs_and_guard_policy(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    from benchmarking import pilot

    checkout = tmp_path / "source"
    source = checkout / "apps/tensorcore_benchmarks/matmul_generator.cpp"
    source.parent.mkdir(parents=True)
    source.write_text("// original generator bytes\n")
    build = tmp_path / "halide-build"
    build.mkdir()
    library = build / "libHalide.dylib"
    library.write_text("fixture library")
    calls = []

    def run(command: list[str], cwd: Path, prefix: Path, **policy: object) -> pilot.PilotProcessResult:
        calls.append((command, policy))
        stdout, stderr = prefix.with_suffix(".stdout.log"), prefix.with_suffix(".stderr.log")
        stdout.write_text("")
        stderr.write_text("")
        if prefix.name == "generate":
            (cwd / "invocation-0000.egg").write_text("(extract root)")
            directory = cwd / "compiler-output"
            for suffix in ("a", "stmt", "h", "ll", "s"):
                (directory / f"matmul.{suffix}").write_text("native output fixture")
        return pilot.PilotProcessResult("success", 0, 0.1, 1024, stdout, stderr, None)

    monkeypatch.setattr(pilot, "run_bounded_command", run)
    result = capture.capture_hardboiled(
        checkout,
        build,
        tmp_path / "capture",
        tmp_path / "real-sidecar",
        optimization_only=True,
        library=library,
        case_records=[
            {
                "id": "hardboiled-matmul",
                "source": str(source.relative_to(checkout)),
                "configuration": {"gpu_schedule": "tensorcore", "M": 1024, "N": 1024, "K": 1024},
            }
        ],
        timeout_sec=300,
    )[0]
    assert result["optimization_complete"] is True
    assert len(result["native_outputs"]) == 5
    assert str(checkout / "tools/GenGen.cpp") in calls[0][0]
    assert "target=x86-64-linux-cuda-cuda_capability_80" in calls[1][0]
    assert "gpu_schedule=tensorcore" in calls[1][0] and "M=1024" in calls[1][0]
    for _, policy in calls:
        assert policy["timeout_sec"] == 300
        assert policy["memory_limit_bytes"] == 5 * 1024**3
        assert policy["require_guard"] and policy["allow_warning_pressure"]
        assert policy["disk_reserve_bytes"] == 10 * 1024**3


@pytest.fixture
def misaal_observation(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> tuple[Path, bytes]:
    monkeypatch.setattr(capture, "ROOT", tmp_path)
    program = tmp_path / "source/add_generated.py"
    program.parent.mkdir()
    program.write_text("original generated program\n")
    generator = program.parent / "add/src/add_generator.cpp"
    generator.parent.mkdir(parents=True)
    generator.write_text("original generator\n")
    monkeypatch.setattr(capture, "MISAAL_ADD_GENERATOR_SHA256", hashlib.sha256(generator.read_bytes()).hexdigest())
    directory = tmp_path / "raw"
    directory.mkdir()
    raw = b"; exact rules, whitespace and seeds\n(datatype E (Seed))\n(let srcexpr (Seed))\n(run 5)\n(extract srcexpr)"
    digest = hashlib.sha256(raw).hexdigest()
    monkeypatch.setattr(capture, "MISAAL_ADD_RAW_SHA256", digest)
    aliases = []
    for index in range(2):
        path = directory / f"invocation-{index:04d}.egg"
        path.write_bytes(raw)
        aliases.append({"path": str(path), "logical_invocation": index, "input_sha256": digest})
    (directory / "capture.json").write_text(
        json.dumps(
            {
                "revision": capture.PINS["misaal"],
                "program": str(program),
                "program_sha256": hashlib.sha256(program.read_bytes()).hexdigest(),
                "capture_status": "partial",
                "capture_boundary": "EggLogCompiler.execute_egglog_file (all callers)",
                "error": "original backend absent",
            }
        )
    )
    stdout = tmp_path / "compatibility.stdout.log"
    stdout.write_text("(Original result)\n")
    observations = tmp_path / "compatibility.json"
    observations.write_text(
        json.dumps(
            [
                {
                    "kind": "raw-capture",
                    "case_id": "misaal-x86-add",
                    "command": ["recorded-engine", aliases[0]["path"]],
                    "input_sha256": digest,
                    "source_aliases": aliases,
                    "process": {"status": "success", "returncode": 0, "stdout_path": str(stdout)},
                    "engine_sha256": "recorded-engine-hash",
                }
            ]
        )
    )
    return observations, raw


@pytest.fixture
def misaal_continuation(tmp_path: Path, misaal_observation: tuple[Path, bytes]) -> Path:
    directory = tmp_path / "continuation"
    current = directory / "capture"
    current.mkdir(parents=True)
    raw_path = current / "invocation-0000.egg"
    raw_path.write_bytes(misaal_observation[1])
    original = json.loads((tmp_path / "raw/capture.json").read_text())
    original["raw_invocations"] = [str(raw_path)]
    (current / "capture.json").write_text(json.dumps(original))
    result = directory / "results.json"
    result.write_text(
        json.dumps(
            {
                "status": "success",
                "returncode": 0,
                "phase": {
                    "boundary_reached": True,
                    "egglog_phase_status": "complete",
                    "failed_attempts": [],
                    "source_capture_status": "partial",
                    "llvm_legalizer_status": "intentionally-not-run",
                    "raw_invocations": [str(raw_path)],
                },
            }
        )
    )
    return result


def test_misaal_preparation_preserves_original_extract_and_both_aliases(
    tmp_path: Path, misaal_observation: tuple[Path, bytes]
) -> None:
    observations, raw = misaal_observation
    record = capture.prepare_misaal_replay(observations, tmp_path / "prepared")
    assert (tmp_path / record["candidate_replay"]).read_bytes() == raw
    assert record["extraction"] == "(extract srcexpr)"
    assert "negative_control" not in record
    assert record["workloads"] == []
    assert record["status"] == record["capture_status"] == "partial"
    assert record["capture_complete"] is False
    assert [call["index"] for call in record["invocations"]] == [0, 1]
    assert len({call["raw"] for call in record["invocations"]}) == 2
    assert len({call["sha256"] for call in record["invocations"]}) == 1
    assert record["reference_output_provenance"]["engine_sha256"] == "recorded-engine-hash"
    with pytest.raises(FileExistsError):
        capture.prepare_misaal_replay(observations, tmp_path / "prepared")


@pytest.mark.parametrize("changed", ("raw/invocation-0000.egg", "raw/invocation-0001.egg"))
def test_misaal_preparation_rejects_changed_capture_alias(
    tmp_path: Path, misaal_observation: tuple[Path, bytes], changed: str
) -> None:
    path = tmp_path / changed
    path.write_bytes(path.read_bytes() + b"changed")
    with pytest.raises(ValueError, match="differs"):
        capture.prepare_misaal_replay(misaal_observation[0], tmp_path / "prepared")
    assert not (tmp_path / "prepared").exists()


@pytest.mark.parametrize(
    ("ordinary_status", "returncode", "admitted"),
    (
        ("success", 0, True),
        ("failure", 1, False),
        ("failure", 101, False),
        ("memory-limit", -9, False),
        ("timeout", None, False),
    ),
)
def test_misaal_admission_requires_ordinary_success_and_preserves_strict_failure(
    tmp_path: Path,
    misaal_observation: tuple[Path, bytes],
    misaal_continuation: Path,
    ordinary_status: str,
    returncode: int | None,
    admitted: bool,
) -> None:
    observations, _ = misaal_observation
    candidate = capture.prepare_misaal_replay(observations, tmp_path / "candidate")
    checks = []
    for phase, path_key, hash_key, status, code, message in (
        ("ordinary-original-schedule", "candidate_replay", "replay_sha256", ordinary_status, returncode, ""),
        ("strict-proof", "candidate_replay", "replay_sha256", "failure", 101, "proof validation panic\n"),
    ):
        stdout_path = tmp_path / f"{phase}.stdout.log"
        stderr_path = tmp_path / f"{phase}.stderr.log"
        stdout_path.write_text("")
        stderr_path.write_text(message)
        checks.append(
            {
                "phase": phase,
                "command": ["stub-engine-not-executed", candidate[path_key]],
                "input_sha256": candidate[hash_key],
                "status": status,
                "returncode": code,
                "stdout_path": str(stdout_path),
                "stderr_path": str(stderr_path),
            }
        )
    validation = tmp_path / "validation.json"
    validation.write_text(
        json.dumps(
            {
                "timeout_sec": 120,
                "memory_limit_bytes": 8 * 1024**3,
                "engine_sha256": "validation-hash",
                "checks": checks,
            }
        )
    )
    record = capture.prepare_misaal_replay(observations, tmp_path / "validated", validation)
    assert record["ordinary_controls_passed"] is admitted
    assert record["strict_proof_passed"] is False
    assert bool(record["workloads"]) is admitted
    assert record["capture_complete"] is False
    assert record["status"] == record["capture_status"] == "partial"
    assert record["validation_engine_sha256"] == "validation-hash"
    assert len(record["validation_logs"]) == 4
    if admitted:
        assert record["classification"] == "partial-capture-strict-proof-failure"
        assert [call["workload"] for call in record["invocations"]] == record["workloads"] * 2
        assert "exit 101" in record["reason"]
        continued = capture.prepare_misaal_replay(observations, tmp_path / "continued", validation, misaal_continuation)
        assert continued["strict_proof_passed"] is False
        assert continued["classification"] == "partial-capture-strict-proof-failure"
        assert continued["capture_complete"] is False
        assert continued["status"] == continued["capture_status"] == "partial"
        assert continued["egglog_phase_status"] == "complete"
        assert continued["external_phases"] == {"llvm_legalizer": "intentionally-not-run"}
        assert len(continued["invocations"]) == 1
        assert continued["invocations"][0]["sha256"] == record["invocations"][0]["sha256"]
        assert [call["index"] for call in continued["historical_capture"]["invocations"]] == [0, 1]
        assert "external LLVM legalization intentionally not run" in continued["reason"]
        assert "exit 101" in continued["reason"]


@pytest.mark.parametrize("changed", ("raw", "phase-boundary", "source-identity"))
def test_misaal_continuation_rejects_changed_raw_or_incomplete_phase(
    tmp_path: Path,
    misaal_observation: tuple[Path, bytes],
    misaal_continuation: Path,
    changed: str,
) -> None:
    if changed == "raw":
        (misaal_continuation.parent / "capture/invocation-0000.egg").write_text("changed input")
    elif changed == "phase-boundary":
        result = json.loads(misaal_continuation.read_text())
        result["phase"]["boundary_reached"] = False
        misaal_continuation.write_text(json.dumps(result))
    else:
        source = misaal_continuation.parent / "capture/capture.json"
        record = json.loads(source.read_text())
        record["program_sha256"] = "changed source"
        source.write_text(json.dumps(record))
    output = tmp_path / "rejected"
    with pytest.raises(ValueError, match="differs|expected the completed"):
        capture.prepare_misaal_replay(misaal_observation[0], output, continuation=misaal_continuation)
    assert not (output / "cases.json").exists()


@pytest.fixture
def backend_capture(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> Path:
    monkeypatch.setattr(capture, "ROOT", tmp_path)
    directory = tmp_path / "backend"
    directory.mkdir()
    program = directory / "generated.py"
    program.write_text("compiler = HydrideCompiler([], run_iterations=5)\n")
    raw = (
        "; preserved declarations and rule variables\n"
        "(datatype E (SYMBV i64) (Derived E))\n"
        "(birewrite (Derived reg_0) reg_0)\n"
        "(let reg_0 (SYMBV 0))\n(let srcexpr reg_0)\n(run 5)\n(extract srcexpr)"
    )
    calls = []
    for index in range(2):
        path = directory / f"invocation-{index:04d}.egg"
        path.write_text(raw)
        path.with_suffix(".stdout.log").write_text("(Derived (SYMBV 0))\n")
        calls.append(
            {
                "index": index,
                "raw": str(path),
                "sha256": hashlib.sha256(raw.encode()).hexdigest(),
                "caller": "apply_rewrite",
                "status": "success",
                "returncode": 0,
            }
        )
    manifest = directory / "capture.json"
    manifest.write_text(
        json.dumps(
            {
                "case_id": "misaal-arm-fixture",
                "revision": capture.PINS["misaal"],
                "source_sha256": "source-hash",
                "program": str(program),
                "program_sha256": hashlib.sha256(program.read_bytes()).hexdigest(),
                "backend_sha256": "original-backend-hash",
                "egglog_phase_status": "complete",
                "source_capture_complete": False,
                "external_llvm_phase": "intentionally-not-run",
                "invocations": calls,
            }
        )
    )
    (directory / "python.result.json").write_text(json.dumps({"status": "success", "returncode": 0}))
    return manifest


def test_recorded_capture_candidates_preserve_prefix_schedule_and_alias_identity(
    backend_capture: Path, tmp_path: Path
) -> None:
    record = capture.prepare_misaal_capture(backend_capture, tmp_path / "prepared")
    first, alias = record["invocations"]
    raw = (tmp_path / first["raw"]).read_text()
    expected = (
        raw.replace("(let reg_0", "(let $reg_0")
        .replace("(let srcexpr reg_0)", "(let $srcexpr $reg_0)")
        .replace("(extract srcexpr)", "(extract $srcexpr)")
    )
    assert (tmp_path / first["candidate_replay"]).read_text() == expected
    assert "negative_control" not in first
    assert first["extraction"] == "(extract $srcexpr)"
    assert first["replay_sha256"] == alias["replay_sha256"]
    assert first["stdout_sha256"] == hashlib.sha256(b"(Derived (SYMBV 0))\n").hexdigest()
    assert record["source_capture_sha256"] == hashlib.sha256(backend_capture.read_bytes()).hexdigest()
    assert record["source_capture_complete"] is False
    assert record["workloads"] == []
    assert record["classification"] == "unvalidated-replay-preparation"
    assert len(record["invocations"]) == 2
    with pytest.raises(FileExistsError):
        capture.prepare_misaal_capture(backend_capture, tmp_path / "prepared")
    other = json.loads(backend_capture.read_text())
    other["case_id"] = "misaal-arm-another-alias"
    backend_capture.write_text(json.dumps(other))
    alias_record = capture.prepare_misaal_capture(backend_capture, tmp_path / "another-source-case")
    assert alias_record["id"] != record["id"]
    assert alias_record["invocations"][0]["replay_sha256"] == first["replay_sha256"]


@pytest.mark.parametrize("changed", ("generated.py", "invocation-0000.egg"))
def test_recorded_capture_rejects_source_or_input_identity_drift(
    backend_capture: Path, tmp_path: Path, changed: str
) -> None:
    path = backend_capture.parent / changed
    path.write_text(path.read_text() + "\n; changed\n")
    with pytest.raises(ValueError, match="changed|differs"):
        capture.prepare_misaal_capture(backend_capture, tmp_path / "rejected")
    assert not (tmp_path / "rejected").exists()


@pytest.mark.parametrize("failure", ("backend", "interrupted", "schedule", "extra-schedule"))
def test_recorded_capture_retains_partial_success_and_every_blocked_call(
    backend_capture: Path, tmp_path: Path, failure: str
) -> None:
    original = json.loads(backend_capture.read_text())
    call = original["invocations"][1]
    if failure == "backend":
        call.update(status="failure", returncode=101)
        original.update(egglog_phase_status="failed", external_llvm_phase="not-reached")
        (backend_capture.parent / "python.result.json").write_text(json.dumps({"status": "failure", "returncode": 70}))
    elif failure == "interrupted":
        call.update(status="running", returncode=None)
        original.update(egglog_phase_status="pending", external_llvm_phase="not-reached")
        (backend_capture.parent / "python.result.json").write_text(
            json.dumps({"status": "timed-out", "returncode": -9})
        )
    else:
        path = Path(call["raw"])
        raw = path.read_text()
        raw = raw.replace("(run 5)", "(run 4)") if failure == "schedule" else "(run 1)\n" + raw
        path.write_text(raw)
        call["sha256"] = hashlib.sha256(raw.encode()).hexdigest()
    backend_capture.write_text(json.dumps(original))
    record = capture.prepare_misaal_capture(backend_capture, tmp_path / "prepared")
    assert [call["preparation_status"] for call in record["invocations"]] == ["candidate", "blocked"]
    assert "reason" in record["invocations"][1]
    if failure == "interrupted":
        assert record["invocations"][1]["reason"] == "Original backend interrupted: source process timed-out"
    assert "candidate_replay" not in record["invocations"][1]
    assert record["egglog_phase_status"] == original["egglog_phase_status"]
    assert record["source_capture_complete"] is False
    assert len(list((tmp_path / "prepared").glob("*.egg"))) == 1


@pytest.mark.parametrize("caller", ("move_swizzles", "lower_swizzles"))
def test_recorded_capture_supports_source_swizzle_roots(backend_capture: Path, tmp_path: Path, caller: str) -> None:
    original = json.loads(backend_capture.read_text())
    for call in original["invocations"]:
        path = Path(call["raw"])
        raw = path.read_text().replace("srcexpr", "swizzleexpr")
        path.write_text(raw)
        call.update(caller=caller, sha256=hashlib.sha256(raw.encode()).hexdigest())
    backend_capture.write_text(json.dumps(original))
    record = capture.prepare_misaal_capture(backend_capture, tmp_path / "prepared")
    assert all(call["extraction"] == "(extract $swizzleexpr)" for call in record["invocations"])


def test_recorded_capture_retains_failure_only_population(backend_capture: Path, tmp_path: Path) -> None:
    original = json.loads(backend_capture.read_text())
    for call in original["invocations"]:
        call.update(status="timeout", returncode=None)
    original.update(egglog_phase_status="failed", external_llvm_phase="not-reached")
    backend_capture.write_text(json.dumps(original))
    record = capture.prepare_misaal_capture(backend_capture, tmp_path / "prepared")
    assert len(record["invocations"]) == 2
    assert all(call["preparation_status"] == "blocked" for call in record["invocations"])
    assert record["workloads"] == []
    assert not list((tmp_path / "prepared").glob("*.egg"))


@pytest.mark.parametrize("output", (None, "not an extracted expression\n"))
@pytest.mark.parametrize("variants", ("", " 0", " 3"))
def test_source_extract_does_not_depend_on_recorded_output_or_negative_query(
    backend_capture: Path, tmp_path: Path, output: str | None, variants: str
) -> None:
    original = json.loads(backend_capture.read_text())
    for call in original["invocations"]:
        path = Path(call["raw"])
        raw = path.read_text().replace("(extract srcexpr)", f"(extract srcexpr{variants})")
        path.write_text(raw)
        call["sha256"] = hashlib.sha256(raw.encode()).hexdigest()
        stdout = path.with_suffix(".stdout.log")
        if output is None:
            stdout.unlink()
        else:
            stdout.write_text(output)
    backend_capture.write_text(json.dumps(original))
    record = capture.prepare_misaal_capture(backend_capture, tmp_path / "prepared")
    for call in record["invocations"]:
        assert call["preparation_status"] == "candidate"
        assert call["extraction"] == f"(extract $srcexpr{variants})"
        assert "negative_control" not in call
        assert (tmp_path / call["candidate_replay"]).read_text().endswith(call["extraction"])


def test_legacy_source_extract_remains_available_without_captured_stdout(
    tmp_path: Path, misaal_observation: tuple[Path, bytes]
) -> None:
    (tmp_path / "compatibility.stdout.log").unlink()
    record = capture.prepare_misaal_replay(misaal_observation[0], tmp_path / "prepared")
    assert (tmp_path / record["candidate_replay"]).read_bytes() == misaal_observation[1]
    assert "stdout" not in record["reference_output_provenance"]


def test_hardboiled_aot_preserves_later_compilation_and_original_target(tmp_path: Path) -> None:
    source = """Target target("x86-64-linux-avx512_sapphirerapids");
    freopen("/tmp/matmul.log", "w", stderr);
    result.realize(out, target);
    result.compile_to_lowered_stmt("/tmp/matmul.html", {A, B}, HTML, target);
    """
    patched, outputs = capture.hardboiled_aot_source(source, tmp_path)
    assert outputs == [tmp_path / "realize-000.ll"]
    assert ".realize(" not in patched
    assert "result.infer_arguments(), target" in patched
    assert 'Target target("x86-64-linux-avx512_sapphirerapids")' in patched
    assert patched.index("compile_to_llvm_assembly") < patched.index("compile_to_lowered_stmt")
    assert str(tmp_path / "matmul.html") in patched
    assert str(tmp_path / "matmul.log") in patched


def test_hardboiled_aot_rejects_unrecognized_device_execution(tmp_path: Path) -> None:
    with pytest.raises(ValueError, match="boundary"):
        capture.hardboiled_aot_source("other.realize(out, target);", tmp_path)


def test_hardboiled_failed_parent_does_not_prepare_prefix(tmp_path: Path) -> None:
    receipt = tmp_path / "cases.json"
    receipt.write_text(
        json.dumps([{"id": "late-failure", "optimization_complete": False, "raw_invocations": ["absent.egg"]}])
    )
    result = capture.prepare_hardboiled_capture(receipt, tmp_path / "replays")
    assert result[0]["status"] == "blocked"
    assert result[0]["workloads"] == []
    assert not list((tmp_path / "replays").glob("*.egg"))


def test_hardboiled_preparation_binds_native_output_and_actual_selections(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    from scripts.hardboiled_replay import check_observed_selections

    raw = tmp_path / "invocation-0000.egg"
    raw.write_text("(let $a (Seed))\n(extract $a)\n(extract $a)\n")
    stdout = b"(Actual)\n(Seed)\n"
    raw.with_suffix(".stdout.log").write_bytes(stdout)
    raw.with_suffix(".json").write_text(
        json.dumps({"sha256": hashlib.sha256(raw.read_bytes()).hexdigest(), "delegate_sha256": "real-delegate"})
    )
    _, selections = check_observed_selections(raw.read_text(), stdout.decode())
    raw.with_suffix(".exit.json").write_text(
        json.dumps({"returncode": 0, "stdout_sha256": hashlib.sha256(stdout).hexdigest(), "selections": selections})
    )
    native = tmp_path / "native.ll"
    native.write_text("completed native compiler output")
    receipt = tmp_path / "cases.json"
    receipt.write_text(
        json.dumps(
            [
                {
                    "id": "complete",
                    "optimization_complete": True,
                    "generate": {"status": "success", "returncode": 0},
                    "raw_invocations": [str(raw)],
                    "native_outputs": [
                        {"path": str(native), "sha256": hashlib.sha256(native.read_bytes()).hexdigest()}
                    ],
                }
            ]
        )
    )
    monkeypatch.setattr(capture, "modernize_hardboiled", lambda source: source)
    result = capture.prepare_hardboiled_capture(receipt, tmp_path / "prepared")
    assert result[0]["status"] == "ordinary-validation-pending"
    replay = Path(result[0]["workloads"][0]).read_text()
    assert replay.count("(check ") == 2
    assert replay.count("(Actual)") == 1
    assert result[0]["source_completion"]["status"] == "success"
    assert result[0]["materialization"] == {"complete": True, "expected_sessions": 1, "materialized_sessions": 1}
    assert len(result[0]["invocations"][0]["output_contract"]["checks"]) == 2
    parent = json.loads(receipt.read_text())
    parent[0]["raw_invocations"].append(str(tmp_path / "missing-last-invocation.egg"))
    receipt.write_text(json.dumps(parent))
    partial = capture.prepare_hardboiled_capture(receipt, tmp_path / "partial")[0]
    assert partial["source_completion"]["status"] == "success" and partial["status"] == "blocked"
    assert partial["materialization"] == {"complete": False, "expected_sessions": 2, "materialized_sessions": 1}
    assert len(partial["invocations"]) == 1 and not partial["workloads"]
    native.write_text("changed after capture")
    changed = capture.prepare_hardboiled_capture(receipt, tmp_path / "changed")
    assert changed[0]["status"] == "blocked"
    assert changed[0]["workloads"] == []
