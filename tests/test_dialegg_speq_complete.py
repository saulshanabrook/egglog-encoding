"""Synthetic contract tests; these do not establish a native paper reproduction."""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
from pathlib import Path
from types import SimpleNamespace
from typing import Any

import pytest

from benchmarking.pilot import PilotProcessResult
from scripts import dialegg_speq_complete as complete
from scripts import suite_capture_dialegg_speq as capture
from scripts.paper_benchmarks import record_speq


def test_complete_population_uses_actual_runtime_and_timer_parents() -> None:
    cases = complete.complete_case_ids("dialegg")
    assert len(cases) == 24
    assert sum("-runtime-" in case for case in cases) == 15
    assert sum("-timer-" in case for case in cases) == 9
    assert len(complete.complete_case_ids("speq")) == 10
    assert "dialegg-extra-nmm-160" not in cases
    assert "dialegg-extra-nmm-160" in complete.complete_case_ids("dialegg", extras=True)
    for case in cases:
        config = complete.DIALEGG_CONFIGS[case]
        assert str(config["input"]).startswith("test/" if "-timer-" in case else "bench/")
    assert complete.DIALEGG_CONFIGS["dialegg-runtime-2mm-canonicalize-eqsat"]["passes"] == [
        "--canonicalize",
        "--eq-sat",
    ]
    assert complete.DIALEGG_CONFIGS["dialegg-runtime-2mm-eqsat-canonicalize"]["passes"] == [
        "--eq-sat",
        "--canonicalize",
    ]


def test_complete_modernization_never_adds_legacy_shape_queries(monkeypatch: pytest.MonkeyPatch) -> None:
    raw = '(include "src/base.egg")\n(run 1)\n'
    monkeypatch.setattr(
        capture,
        "DIALEGG_SHAPE_QUERIES",
        {
            hashlib.sha256(raw.encode()).hexdigest(): ("(check (= invented 1))", "legacy diagnostic"),
        },
    )
    assert capture.modernize_dialegg_invocation(raw, "", diagnostic_queries=False) == "\n(run 1)\n"
    assert complete.validate_extract_output(raw, "") == []


def test_complete_patch_preserves_native_reconstruction_and_checks_failures() -> None:
    source = """std::ofstream eggFileOut(opsEggFilePath);
eggFileOut.close();
std::string egglogCmd = "egglog " + opsEggFilePath + " > " + egglogExtractedFilename + " 2> " + egglogLogFilename;
std::system(egglogCmd.c_str());
runEgglog(egglog.eggifiedBlock, blockName); // Run egglog on the block
std::getline(file, line);
mlir::Operation* newOp = egglog.parseOperation(line, builder);
prevOp->replaceAllUsesWith(newOp);
file.close();
"""
    patched = complete.patch_dialegg_pass(source)
    assert "eggFileOut.close();\n    return;" not in patched
    assert "runEgglog(egglog.eggifiedBlock, blockName); // Run egglog on the block" in patched
    assert "egglog.parseOperation(line, builder)" in patched
    assert "prevOp->replaceAllUsesWith(newOp)" in patched
    assert "std::system(egglogCmd.c_str()) != 0" in patched
    assert "missing extraction response" in patched
    assert "extra extraction response" in patched
    assert "DIALEGG_NATIVE_EGGLOG" in patched
    with pytest.raises(ValueError, match="expected exactly one"):
        complete.patch_dialegg_pass(source.replace("std::getline(file, line);", "changed_source();"))


@pytest.mark.parametrize(
    "stdout,returncode,success",
    [
        ("(Chosen 2)\n(Chosen 1)\n", 0, True),
        ("(Chosen 2)\n", 0, False),
        ("(Chosen 2)\n(Chosen 1)\n(Extra)\n", 0, False),
        ("(Chosen\n 2)\n(Chosen 1)\n", 0, False),
        ("(Chosen 2)\n(Chosen 1)\n", 1, False),
        ("(union a b)\n(Chosen 1)\n", 0, False),
    ],
)
def test_native_delegate_preserves_real_ordered_responses_and_rejects_bad_contracts(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, stdout: str, returncode: int, success: bool
) -> None:
    raw = tmp_path / "invocation-0.egg"
    raw.write_text("(extract second)\n(extract first)\n")
    backend = tmp_path / "engine"
    backend.write_text("synthetic engine identity")

    def execute(command: list[str], **kwargs: Any) -> subprocess.CompletedProcess[Any]:
        assert command == [str(backend), str(raw)]
        assert "start_new_session" not in kwargs
        kwargs["stdout"].write(stdout.encode())
        kwargs["stderr"].write(b"retained native diagnostic\n")
        return subprocess.CompletedProcess(command, returncode)

    monkeypatch.setattr(complete.subprocess, "run", execute)
    out, err = tmp_path / "stdout", tmp_path / "stderr"
    assert complete.delegate_backend(backend, raw, out, err) == (0 if success else 1)
    manifest = json.loads(raw.with_suffix(".json").read_text())
    assert manifest["status"] == ("complete" if success else "failed")
    assert out.read_text() == stdout
    assert err.read_text() == "retained native diagnostic\n"
    assert manifest["extract_requests"] == [["(", "extract", "second", ")"], ["(", "extract", "first", ")"]]
    assert manifest["stdout_sha256"] == hashlib.sha256(stdout.encode()).hexdigest()


@pytest.mark.parametrize("chunks", [[], ["first\n"], ["first\n", "second\n", "third\n"]])
@pytest.mark.parametrize("flags", [[], ["-D_FORTIFY_SOURCE=0", "-DPOLYBENCH_USE_C99_PROTO"]])
def test_complete_frontend_returns_all_ordered_fir_regions(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, chunks: list[str], flags: list[str]
) -> None:
    source = tmp_path / "benchmarks/spmv_npb.c"
    source.parent.mkdir()
    source.write_text("original application C")
    monkeypatch.setattr(
        record_speq, "COMPLETE_APPLICATION_C_SHA256", {"spmv_npb": record_speq.sha256_text(source.read_text())}
    )

    def execute(command: list[str], **kwargs: Any) -> subprocess.CompletedProcess[Any]:
        Path(command[-1]).write_text("original native LLVM output")
        if "print<revpass>" in " ".join(command):
            kwargs["stderr"].write("".join(f"REV Start\n{chunk}REV End\n" for chunk in chunks).encode())
        return subprocess.CompletedProcess(command, 0)

    monkeypatch.setattr(record_speq.subprocess, "run", execute)
    evidence = tmp_path / "evidence"
    assert (
        record_speq.application_fir(
            tmp_path,
            tmp_path / "opt",
            tmp_path / "plugin",
            "spmv_npb",
            evidence,
            complete=True,
            frontend_flags=flags,
        )
        == chunks
    )
    manifest = json.loads((evidence / "manifest.json").read_text())
    assert [Path(row["path"]).read_text() for row in manifest["chunks"]] == chunks
    assert manifest["source_sha256"] == record_speq.sha256_text(source.read_text())
    assert manifest["frontend_flags"] == flags
    clang, opt = [row["command"] for row in manifest["commands"]]
    assert clang[7:-3] == flags
    assert opt == [
        str(tmp_path / "opt"),
        f"-load-pass-plugin={tmp_path / 'plugin'}",
        "-S",
        "-passes=mem2reg,loop-rotate,instcombine,simplifycfg,loop-simplify,gvn,lcssa,print<revpass>",
        "-enable-load-in-loop-pre=false",
        str(evidence / "input.ll"),
        "-o",
        str(evidence / "analysis.ll"),
    ]


def test_recorder_frontend_flags_require_explicit_complete_mode() -> None:
    argv = [
        "--artifact=artifact",
        "--rev-tests=REVTest.cpp",
        "--lleq=lleq",
        "--llvm-config=llvm-config",
        "--benchmark=polybench_gemm",
        "--output=out.egg",
        "--frontend-flag=-D_FORTIFY_SOURCE=0",
        "--frontend-flag=-DPOLYBENCH_USE_C99_PROTO",
    ]
    with pytest.raises(SystemExit):
        record_speq.parse_args(argv)
    assert record_speq.parse_args([*argv, "--complete"]).frontend_flag == [
        "-D_FORTIFY_SOURCE=0",
        "-DPOLYBENCH_USE_C99_PROTO",
    ]


@pytest.mark.parametrize("flags", [[], ["-D_FORTIFY_SOURCE=0", "-DPOLYBENCH_USE_C99_PROTO"]])
def test_speq_complete_preserves_opt_in_flags_in_command_and_receipt(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, flags: list[str]
) -> None:
    def run(command: list[str], cwd: Path, prefix: Path, timeout: float) -> PilotProcessResult:
        assert [arg for arg in command if arg.startswith("--frontend-flag=")] == [
            f"--frontend-flag={flag}" for flag in flags
        ]
        out, err = prefix.with_suffix(".out"), prefix.with_suffix(".err")
        out.write_text("")
        err.write_text("synthetic native failure")
        return PilotProcessResult("failure", 1, 0.0, 0, out, err, "synthetic native failure")

    monkeypatch.setattr(complete, "run_complete_command", run)
    args = argparse.Namespace(
        speq_python=tmp_path / "python",
        speq_artifact=tmp_path / "artifact",
        speq_lleq=tmp_path / "lleq",
        llvm17_config=tmp_path / "llvm-config",
        speq_rev_plugin=None,
        speq_frontend_flag=flags,
        timeout_sec=30,
    )
    case = "speq-polybench_gemm"
    row = complete.capture_complete_speq(args, [case], tmp_path)["cases"][case]
    assert row["frontend_flags"] == flags
    assert json.loads(Path(row["receipt"]).read_text())["frontend_flags"] == flags
    assert not row["source_complete"]
    assert not row["ordinary_compatible"]


@pytest.mark.parametrize("ordinary_status", ["success", "failure"])
def test_speq_complete_session_and_root_contract_survive_ordinary_failure(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, ordinary_status: str
) -> None:
    launches = []

    def run(command: list[str], cwd: Path, prefix: Path, timeout: float) -> PilotProcessResult:
        launches.append(command)
        out, err = prefix.with_suffix(".out"), prefix.with_suffix(".err")
        out.write_text("")
        err.write_text("")
        status = "success"
        if "--complete" in command:
            replay = Path(command[command.index("--output") + 1])
            replay.write_text("(let $a (A))\n(extract $a)\n(run 1)\n(extract $a)\n")
            replay.with_suffix(".manifest.json").write_text(
                json.dumps(
                    {
                        "source_complete": True,
                        "standalone_sha256": hashlib.sha256(replay.read_bytes()).hexdigest(),
                        "expected_stdout": "(A)\n(B)\n",
                        "regions": [{"cost": 1}, {"cost": 2}],
                    }
                )
            )
        else:
            status = ordinary_status
            out.write_text("(A)\n(B)\n" if status == "success" else "")
        return PilotProcessResult(status, 0 if status == "success" else 1, 0, 0, out, err, None)  # type: ignore[arg-type]

    monkeypatch.setattr(complete, "run_complete_command", run)
    args = argparse.Namespace(
        speq_python=tmp_path / "python",
        speq_artifact=tmp_path / "artifact",
        speq_lleq=tmp_path / "lleq",
        llvm17_config=tmp_path / "llvm-config",
        speq_rev_plugin=None,
        egglog=tmp_path / "engine",
        timeout_sec=30,
    )
    row = complete.capture_complete_speq(args, ["speq-polybench_gemm"], tmp_path)["cases"]["speq-polybench_gemm"]
    assert len(launches) == 2 and row["source_completion"]["status"] == "complete"
    assert row["materialization"] == {"complete": True, "expected_sessions": 1, "materialized_sessions": 1}
    assert len(row["output_contract"]["expected_terms"]) == len(row["output_contract"]["extract_requests"]) == 2
    assert row["status"] == ("reproduced" if ordinary_status == "success" else "ordinary-validation-failed")


class SyntheticBest:
    def __init__(self, index: int) -> None:
        self.cost = index + 7
        self.term = index
        self.termdag = SimpleNamespace(to_string=lambda _: f"(native-output {index})")


class SyntheticGraph:
    """Small protocol double with observable scope/schedule/extract accounting."""

    def __init__(self, fail_at: int | None = None) -> None:
        self.commands: list[Any] = []
        self.count = 0
        self.fail_at = fail_at
        self.as_egglog_string = "; synthetic recorder test double\n"

    def __enter__(self) -> SyntheticGraph:
        self.commands.append("push")
        return self

    def __exit__(self, *_args: Any) -> None:
        self.commands.append("pop")

    def let(self, name: str, value: Any) -> Any:
        self.commands.append(("let", name, value))
        return value

    def run(self, count: int, *, ruleset: str) -> None:
        self.commands.append(("run", count, ruleset))

    def _run_extract(self, value: Any) -> SyntheticBest:
        self.commands.append(("extract", value))
        if self.count == self.fail_at:
            raise RuntimeError("synthetic engine failure")
        result = SyntheticBest(self.count)
        self.count += 1
        return result

    def extract(self, value: str) -> str:
        self._run_extract(value)
        return value


@pytest.mark.parametrize("fail_at", [None, 1])
def test_speq_complete_regions_keep_skips_unmatched_results_and_native_extraction_contract(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, fail_at: int | None
) -> None:
    def parse(fir: str) -> tuple[Any, Any, Any]:
        print(f"SMT/parser outcome for {fir}")
        if fir == "setup":
            raise ValueError("unsupported setup fold")
        return (["CSR"], ["original runtime condition"], SimpleNamespace(toEgg=lambda: fir))

    monkeypatch.setattr(record_speq.importlib, "import_module", lambda _: SimpleNamespace(ExtractBest=SyntheticBest))
    parse_ir = SimpleNamespace(foldFromStr=parse, transform="transform", expand="expand")
    graph = SyntheticGraph(fail_at)
    manifest: dict[str, Any] = {"regions": []}
    args = (parse_ir, graph, ["setup", "unchanged()", "gemv(real, input)"], "spmv_npb", tmp_path, manifest)
    if fail_at is None:
        assert record_speq.record_complete_regions(*args) == ["spmv_npb-region-001", "spmv_npb-region-002"]
        assert [row["status"] for row in manifest["regions"]] == ["skipped-parse", "unmatched", "matched"]
        assert manifest["regions"][-1]["translation"] == "spmv_csr(real, input)"
        assert [row["cost"] for row in manifest["regions"] if "cost" in row] == [7, 8]
        assert manifest["expected_stdout"] == "(native-output 0)\n(native-output 1)\n"
    else:
        with pytest.raises(RuntimeError, match="synthetic engine failure"):
            record_speq.record_complete_regions(*args)
        assert graph.count == 1
        assert manifest["expected_stdout"] == "(native-output 0)\n"
    assert [command for command in graph.commands if isinstance(command, tuple) and command[0] == "run"] == [
        ("run", 5, "transform"),
        ("run", 1, "expand"),
        ("run", 3, "transform"),
        ("run", 5, "transform"),
        ("run", 1, "expand"),
        ("run", 3, "transform"),
    ]
    assert graph.commands.count("push") == graph.commands.count("pop") == 2
    assert "SMT/parser outcome for setup" in (tmp_path / "region-000/parse.stdout.log").read_text()
    assert "unsupported setup fold" in manifest["regions"][0]["reason"]


@pytest.mark.parametrize("native_status", ["failure", "resource-stopped", "timed-out"])
def test_partial_dialegg_parent_never_admits_or_replays_earlier_calls(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, native_status: str
) -> None:
    source = tmp_path / "source"
    (source / "src").mkdir(parents=True)
    (source / "src/base.egg").write_text("(function type-of (Op) Type)\n(function dims (Type) IntVec)")
    inputs = source / "bench/vector_norm"
    inputs.mkdir(parents=True)
    (inputs / "vector_norm.mlir").write_text("module {}")
    (inputs / "vector_norm.egg").write_text('(include "src/base.egg")')
    output = tmp_path / "output"
    output.mkdir()
    binary = tmp_path / "frontend/egg-opt-complete"
    binary.parent.mkdir()
    monkeypatch.setattr(complete, "prepare_complete_dialegg", lambda *_: (binary, {}))
    commands: list[list[str]] = []

    def run(command: list[str], cwd: Path, prefix: Path, **kwargs: Any) -> PilotProcessResult:
        assert not commands, "a failed parent must not launch verifier or standalone replay"
        commands.append(command)
        calls = Path(next(arg.split("=", 1)[1] for arg in command if arg.startswith("DIALEGG_CAPTURE_DIR=")))
        raw = calls / "invocation-0.egg"
        raw.write_text("(extract root)")
        raw.with_suffix(".json").write_text(json.dumps({"status": "complete", "output_terms": [["(", "Real", ")"]]}))
        out, err = prefix.with_suffix(".out"), prefix.with_suffix(".err")
        out.write_text("first block succeeded")
        err.write_text("later parent failure")
        return PilotProcessResult(native_status, 1, 0.0, 0, out, err, "later parent failure")  # type: ignore[arg-type]

    monkeypatch.setattr(complete, "run_bounded_command", run)
    args = argparse.Namespace(
        dialegg_source=source, llvm18_prefix=tmp_path, native_egglog=tmp_path / "native", timeout_sec=30
    )
    case = "dialegg-runtime-vector_norm-eqsat"
    report = complete.capture_complete_dialegg(args, [case], output)
    row = report["cases"][case]
    assert not row["source_complete"]
    assert not row["workloads"]
    assert row["invocations"][0]["native"]["status"] == "complete"
    assert (output / case / "manifest.json").is_file()
    assert bool(report.get("operational_stop")) == (native_status in complete.STOP_STATUSES)


@pytest.mark.parametrize("mismatch", [False, True])
@pytest.mark.parametrize("cost_logs", [False, True])
def test_completed_native_parent_requires_actual_replay_outputs_including_zero_root_helpers(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, mismatch: bool, cost_logs: bool
) -> None:
    source = tmp_path / "source"
    (source / "src").mkdir(parents=True)
    (source / "src/base.egg").write_text(
        "(datatype Op (Real) (Wrong))\n(function type-of (Op) Type)\n(function dims (Type) IntVec)"
    )
    inputs = source / "bench/vector_norm"
    inputs.mkdir(parents=True)
    (inputs / "vector_norm.mlir").write_text("module {}")
    (inputs / "vector_norm.egg").write_text('(include "src/base.egg")')
    output = tmp_path / "output"
    output.mkdir()
    binary = tmp_path / "frontend/egg-opt-complete"
    binary.parent.mkdir()
    monkeypatch.setattr(complete, "prepare_complete_dialegg", lambda *_: (binary, {}))
    commands: list[list[str]] = []

    def run(command: list[str], cwd: Path, prefix: Path, **kwargs: Any) -> PilotProcessResult:
        assert kwargs["require_guard"]
        assert kwargs["disk_reserve_bytes"] == 10 * 1024**3
        assert kwargs["allow_warning_pressure"] is False
        commands.append(command)
        out, err = Path(str(prefix) + ".out"), Path(str(prefix) + ".err")
        out.write_text("")
        err.write_text("")
        if any(arg.startswith("DIALEGG_CAPTURE_DIR=") for arg in command):
            calls = Path(next(arg.split("=", 1)[1] for arg in command if arg.startswith("DIALEGG_CAPTURE_DIR=")))
            for index, suffix in enumerate(("", "(extract root)\n")):
                raw = calls / f"invocation-{index}.egg"
                raw.write_text('(include "src/base.egg")\n(let root (Real))\n(union root (Wrong))\n(run 1)\n' + suffix)
                raw.with_suffix(".json").write_text(
                    json.dumps(
                        {
                            "status": "complete",
                            **({"extract_costs": [1] if index else []} if cost_logs else {}),
                            "output_count": index,
                            "extract_requests": [["(", "extract", "root", ")"]] if index else [],
                            "output_terms": [["(", "Real", ")"]] if index else [],
                        }
                    )
                )
            Path(command[-1]).write_text("module { /* optimized */ }")
        elif command[0].endswith("mlir-opt"):
            Path(command[-1]).write_text("module { /* verified */ }")
        else:
            program = Path(command[-1]).read_text()
            assert ("(check " in program) == (cost_logs and "(extract " in program)
            if "(extract " in program:
                out.write_text("(Wrong)\n" if mismatch else "(Real)\n")
                if cost_logs:
                    assert command[:2] == ["env", "RUST_LOG=egglog::extract=debug"]
                    err.write_text("Best cost for the extract root: 1\n")
        return PilotProcessResult("success", 0, 0.0, 0, out, err, None)

    monkeypatch.setattr(complete, "run_bounded_command", run)
    args = argparse.Namespace(
        dialegg_source=source,
        llvm18_prefix=tmp_path,
        native_egglog=tmp_path / "native",
        egglog=tmp_path / "replay",
        timeout_sec=30,
    )
    case = "dialegg-runtime-vector_norm-eqsat"
    row = complete.capture_complete_dialegg(args, [case], output)["cases"][case]
    assert row["source_complete"]
    assert row["source_completion"]["status"] == "complete"
    assert row["ordinary_compatible"] == (not mismatch or cost_logs)
    assert row["status"] == ("ordinary-validation-failed" if mismatch and not cost_logs else "reproduced")
    assert row["materialization"] == {"complete": True, "expected_sessions": 2, "materialized_sessions": 2}
    assert len(row["workloads"]) == (0 if mismatch and not cost_logs else 2)
    assert row["invocations"][0]["output_contract"]["zero_root_helper"]
    if cost_logs:
        assert row["invocations"][1]["cost_validation"] == {
            "native_costs": [1],
            "replay_costs": [1],
            "exact_terms": not mismatch,
        }
    assert len(commands) == 4  # parent, native MLIR verifier, both independent replays


def test_guard_preflight_refusal_is_durable_and_never_a_success(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    def refuse(*args: Any, **kwargs: Any) -> Any:
        raise ValueError("disk guard refused to launch: fewer than 10 GiB free")

    monkeypatch.setattr(complete, "run_bounded_command", refuse)
    result = complete.run_complete_command(["never-launched"], tmp_path, tmp_path / "preflight", 30)
    assert result.status == "resource-stopped"
    assert result.returncode is None
    assert "disk guard refused" in result.stderr_path.read_text()


@pytest.mark.parametrize("logged_term", ["(Chosen 2)", "(Chosen 999)"])
def test_native_cost_logs_are_enabled_and_bound_to_the_exact_response(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, logged_term: str
) -> None:
    raw, backend = tmp_path / "invocation.egg", tmp_path / "backend"
    raw.write_text("(extract root)")
    backend.write_text("synthetic engine")

    def run(command: list[str], **kwargs: Any) -> subprocess.CompletedProcess[Any]:
        assert kwargs["env"]["RUST_LOG"] == "info"
        kwargs["stdout"].write(b"(Chosen 2)\n")
        kwargs["stderr"].write(f"[INFO ] extracted with cost 2: {logged_term}\n".encode())
        return subprocess.CompletedProcess(command, 0)

    monkeypatch.setattr(complete.subprocess, "run", run)
    assert complete.delegate_backend(backend, raw, tmp_path / "stdout", tmp_path / "stderr") == 0
    manifest = json.loads(raw.with_suffix(".json").read_text())
    if logged_term == "(Chosen 2)":
        assert manifest["extract_costs"] == [2]
    else:
        assert "extract_costs" not in manifest and "cost_evidence_unavailable" in manifest


def test_recorder_phi_repair_is_explicit_complete_only_and_cannot_use_historical_plugin() -> None:
    required = [
        "--artifact=artifact",
        "--rev-tests=REVTest.cpp",
        "--lleq=lleq",
        "--llvm-config=llvm-config",
        "--benchmark=parboil_hist",
        "--output=out.egg",
    ]
    assert not record_speq.parse_args(required).repair_phi_polarity
    with pytest.raises(SystemExit):
        record_speq.parse_args([*required, "--repair-phi-polarity"])
    with pytest.raises(SystemExit):
        record_speq.parse_args([*required, "--complete", "--repair-phi-polarity", "--rev-plugin=historical.so"])
    assert record_speq.parse_args([*required, "--complete", "--repair-phi-polarity"]).repair_phi_polarity


@pytest.mark.parametrize("repair", [False, True])
def test_complete_phi_opt_in_records_fresh_build_instead_of_using_historical_plugin(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, repair: bool
) -> None:
    commands = []

    def run(command: list[str], cwd: Path, prefix: Path, timeout: float) -> PilotProcessResult:
        commands.append(command)
        out, err = prefix.with_suffix(".out"), prefix.with_suffix(".err")
        out.write_text("")
        err.write_text("synthetic native failure")
        return PilotProcessResult("failure", 1, 0.0, 0, out, err, "synthetic native failure")

    monkeypatch.setattr(complete, "run_complete_command", run)
    args = argparse.Namespace(
        speq_python=tmp_path / "python",
        speq_artifact=tmp_path / "artifact",
        speq_lleq=tmp_path / "lleq",
        llvm17_config=tmp_path / "llvm-config",
        speq_rev_plugin=tmp_path / "historical.so",
        speq_phi_polarity_repair=repair,
        timeout_sec=30,
    )
    row = complete.capture_complete_speq(args, ["speq-parboil_hist"], tmp_path)["cases"]["speq-parboil_hist"]
    assert ("--repair-phi-polarity" in commands[0]) is repair
    assert ("--rev-plugin" in commands[0]) is not repair
    assert row["phi_polarity_repair"] is repair
    if repair:
        assert row["omitted_prebuilt_rev_plugin"]["path"] == str(tmp_path / "historical.so")
    assert json.loads(Path(row["receipt"]).read_text())["phi_polarity_repair"] is repair
    assert not row["source_complete"] and not row["ordinary_compatible"]


@pytest.mark.parametrize("case", ["polybench_gemm", "parboil_hist"])
def test_c99_adapter_scopes_only_gemm_and_never_uses_prebuilt(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, case: str
) -> None:
    from scripts import speq_c99_diagnostic as c99

    commands = []

    def run(command: list[str], cwd: Path, prefix: Path, timeout: float) -> PilotProcessResult:
        commands.append(command)
        out, err = prefix.with_suffix(".out"), prefix.with_suffix(".err")
        out.write_text("")
        err.write_text("mock resource stop")
        return PilotProcessResult("memory-limit", None, 0, 0, out, err, "mock resource stop")

    monkeypatch.setattr(complete, "run_complete_command", run)
    args = argparse.Namespace(
        speq_python=tmp_path / "python",
        speq_artifact=tmp_path / "artifact",
        speq_lleq=tmp_path / "lleq",
        llvm17_config=tmp_path / "llvm-config",
        speq_rev_plugin=tmp_path / "old.so",
        speq_phi_polarity_repair=True,
        speq_c99_frontend_repair=c99.CONTRACT,
        speq_frontend_flag=list(c99.FRONTEND_FLAGS),
        timeout_sec=30,
    )
    result = complete.capture_complete_speq(args, ["speq-" + case], tmp_path)
    assert result["operational_stop"]["status"] == "memory-limit"
    assert len(commands) == 1 and "--rev-plugin" not in commands[0]
    assert ("--c99-frontend-repair" in commands[0]) is (case == "polybench_gemm")
    assert result["cases"]["speq-" + case]["workloads"] == []
    assert result["cases"]["speq-" + case]["omitted_prebuilt_rev_plugin"]["path"] == str(tmp_path / "old.so")


@pytest.mark.parametrize("kind", ["success", "baseline", "candidate", "comparison", "recognition", "omitted"])
def test_c99_recorder_compares_fresh_pair_before_unchanged_all_region_path(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, kind: str
) -> None:
    from scripts import speq_c99_diagnostic as c99

    calls = []
    plugin = tmp_path / "candidate.so"
    baseline_plugin = tmp_path / "phi.so"
    for path in (plugin, baseline_plugin):
        path.write_text("mock built plugin")
    pair = {
        "opt": str(tmp_path / "opt"),
        "candidate_plugin": str(plugin),
        "baseline_plugin": str(baseline_plugin),
        "llvm_version": "17.0.6",
    }
    monkeypatch.setattr(c99, "build_plugins", lambda *_: pair)

    def application(*args: Any, **kwargs: Any) -> list[str]:
        baseline = args[2] == baseline_plugin
        phase = "baseline" if baseline else "candidate"
        assert kwargs.get("c99_frontend_repair", False) is (not baseline)
        assert c99.ENABLE_ENV not in record_speq.os.environ
        calls.append(phase)
        if kind == phase:
            raise ValueError("mock " + phase + " failure")
        return ["empty", "unsupported original setup", "actual candidate" if not baseline else "actual baseline"]

    def compare(before: list[str], after: list[str], *args: Any) -> dict:
        calls.append("comparison")
        assert before[-1] == "actual baseline" and after[-1] == "actual candidate"
        if kind == "comparison":
            raise ValueError("mock comparison mismatch")
        return {"status": "exact-scoped-repair"}

    def references(*args: Any) -> str:
        assert c99.ENABLE_ENV not in record_speq.os.environ
        calls.append(args[-1])
        return "original reference " + str(args[-1])

    def regions(_parse: Any, _graph: Any, firs: list[str], name: str, evidence: Path, manifest: dict) -> list[str]:
        calls.append("regions")
        assert firs == ["empty", "unsupported original setup", "actual candidate"]
        manifest["regions"] = [
            {"index": 0, "status": "skipped-parse"},
            {"index": 1, "status": "skipped-parse"},
            {"index": 2, "status": "matched", "kernel": "gemm"},
        ]
        if kind == "recognition":
            del manifest["regions"][-1]["kernel"]
        if kind == "omitted":
            manifest["regions"].pop(0)
        return ["polybench_gemm-region-002"]

    graph = SimpleNamespace(as_egglog_string="(extract real-root)\n")
    monkeypatch.setattr(record_speq, "application_fir", application)
    monkeypatch.setattr(c99, "compare_frontends", compare)
    monkeypatch.setattr(record_speq, "reference_fir", references)
    monkeypatch.setattr(record_speq, "adapt_parse_ir", lambda source: source)
    monkeypatch.setattr(record_speq, "import_parse_ir", lambda _: SimpleNamespace(egraph=graph))
    monkeypatch.setattr(record_speq, "add_reference_rules", lambda *_: None)
    monkeypatch.setattr(record_speq, "record_complete_regions", regions)
    monkeypatch.setattr(record_speq, "normalize_recording", lambda source, _: source)
    args = argparse.Namespace(
        source_evidence=tmp_path / "source",
        check=False,
        rev_plugin=None,
        lleq=tmp_path / "lleq",
        llvm_config=tmp_path / "llvm-config",
        output=tmp_path / "out.egg",
        frontend_flag=list(c99.FRONTEND_FLAGS),
        repair_phi_polarity=True,
        c99_frontend_repair=c99.CONTRACT,
    )
    if kind == "success":
        assert record_speq.record_complete(args, tmp_path, "original parser", ["polybench_gemm"]) == 0
    else:
        with pytest.raises(ValueError):
            record_speq.record_complete(args, tmp_path, "original parser", ["polybench_gemm"])
    receipt = json.loads(args.output.with_suffix(".manifest.json").read_text())
    assert receipt["source_complete"] is (kind == "success")
    assert receipt["schedule"] == [5, 1, 3]
    assert c99.ENABLE_ENV not in record_speq.os.environ
    if kind in {"success", "recognition", "omitted"}:
        assert calls == ["baseline", "candidate", "comparison", *record_speq.REFERENCE_ANALYSIS_SHA256, "regions"]
    elif kind == "comparison":
        assert calls == ["baseline", "candidate", "comparison"]
    else:
        assert calls == (["baseline"] if kind == "baseline" else ["baseline", "candidate"])


@pytest.mark.parametrize("fault", [None, "no-phi", "prebuilt", "wrong-benchmark", "not-complete", "unknown-mode"])
def test_c99_mode_rejects_unproven_recorder_combinations(fault: str | None) -> None:
    from scripts.speq_c99_diagnostic import CONTRACT

    argv = [
        "--artifact=artifact",
        "--rev-tests=REVTest.cpp",
        "--lleq=lleq",
        "--llvm-config=llvm-config",
        "--benchmark=polybench_gemm",
        "--output=out.egg",
        "--complete",
        "--repair-phi-polarity",
        "--c99-frontend-repair=" + CONTRACT,
    ]
    if fault == "no-phi":
        argv.remove("--repair-phi-polarity")
    elif fault == "prebuilt":
        argv.append("--rev-plugin=arbitrary.so")
    elif fault == "wrong-benchmark":
        argv[4] = "--benchmark=parboil_hist"
    elif fault == "not-complete":
        argv.remove("--complete")
    elif fault == "unknown-mode":
        argv[-1] = "--c99-frontend-repair=broader"
    if fault:
        with pytest.raises(SystemExit):
            record_speq.parse_args(argv)
    else:
        assert record_speq.parse_args(argv).c99_frontend_repair == CONTRACT


def test_c99_environment_is_local_to_selected_analysis_not_clang_or_references(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    from scripts import speq_c99_diagnostic as c99

    source = tmp_path / "benchmarks/polybench_gemm.c"
    source.parent.mkdir()
    source.write_text("unchanged original C")
    monkeypatch.setattr(
        record_speq, "COMPLETE_APPLICATION_C_SHA256", {"polybench_gemm": record_speq.sha256_text(source.read_text())}
    )
    monkeypatch.setattr(record_speq, "APPLICATION_HEADER_SHA256", {})
    calls = []

    def run(command: list[str], **kwargs: Any) -> subprocess.CompletedProcess[Any]:
        calls.append(kwargs.get("env"))
        Path(command[-1]).write_text("unchanged IR")
        kwargs["stderr"].write(b"REV Start\nreal fir\nREV End\n" if "print<revpass>" in " ".join(command) else b"")
        return subprocess.CompletedProcess(command, 0)

    monkeypatch.setattr(record_speq.subprocess, "run", run)
    assert record_speq.application_fir(
        tmp_path,
        tmp_path / "opt",
        tmp_path / "fresh.so",
        "polybench_gemm",
        tmp_path / "enabled",
        complete=True,
        frontend_flags=c99.FRONTEND_FLAGS,
        c99_frontend_repair=True,
    ) == ["real fir\n"]
    assert calls[0] is None and calls[1] is not None and calls[1][c99.ENABLE_ENV] == "1"
    assert c99.ENABLE_ENV not in record_speq.os.environ
    monkeypatch.setenv(c99.ENABLE_ENV, "1")
    with pytest.raises(ValueError, match="disabled"):
        record_speq.reference_fir(tmp_path / "opt", tmp_path / "fresh.so", tmp_path / "reference.ll", "gemm_ref")
    assert len(calls) == 2
