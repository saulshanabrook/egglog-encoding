"""Complete native DialEgg/SpEQ parents and retain their standalone output contracts.

No source acquisition occurs here. All native work runs below the caller's guarded
process group. The small backend delegate is also used by the patched DialEgg
frontend; it never creates a detached process or substitutes extraction results.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
from dataclasses import asdict
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from benchmarking.pilot import PilotProcessResult, run_bounded_command  # noqa: E402
from scripts.hardboiled_replay import egglog_forms  # noqa: E402
from scripts.paper_benchmarks import materialize, record_speq  # noqa: E402

STOP_STATUSES = {"resource-stopped", "memory-limit", "timed-out"}
DIALEGG_CONFIGS = {
    **{
        f"dialegg-runtime-{name}-{label}": {
            "input": f"bench/{name}/{name}.mlir",
            "template": f"bench/{name}/{name}.egg",
            "passes": passes,
            "population": "paper-runtime",
        }
        for name in ("image_conversion", "vector_norm", "polynomial", "2mm", "3mm")
        for label, passes in (
            ("eqsat", ["--eq-sat"]),
            ("canonicalize-eqsat", ["--canonicalize", "--eq-sat"]),
            ("eqsat-canonicalize", ["--eq-sat", "--canonicalize"]),
        )
    },
    **{
        f"dialegg-timer-{name}": {
            "input": f"test/{name}/{name}.mlir",
            "template": f"test/{name}/{name}.egg",
            "passes": ["--eq-sat"],
            "population": "paper-timer",
        }
        for name in ("image_conversion", "vector_norm", "polynomial")
    },
    **{
        f"dialegg-timer-nmm-{size}": {
            "input": f"test/nmm/{size}mm.mlir",
            "template": "test/nmm/nmm.egg",
            "passes": ["--eq-sat"],
            "population": "paper-timer",
        }
        for size in (2, 3, 10, 20, 40, 80)
    },
    "dialegg-extra-nmm-160": {
        "input": "bench/nmm/160mm.mlir",
        "template": "bench/nmm/nmm.egg",
        "passes": ["--eq-sat"],
        "population": "artifact-extra",
    },
}
SPEQ_MISSING = {
    "speq-tpal": "Exact paper TPAL source and setup remain unresolved; no reference substitution is permitted.",
    "speq-tsvc2": "Exact paper TSVC2 source and active reduction reference/driver setup remain unresolved.",
}


def complete_case_ids(family: str, *, extras: bool = False) -> list[str]:
    """Return the required parents; artifact extras require explicit case selection."""
    cases: list[str] = []
    if family in ("all", "dialegg"):
        cases.extend(k for k, v in DIALEGG_CONFIGS.items() if extras or v["population"] != "artifact-extra")
    if family in ("all", "speq"):
        cases.extend(f"speq-{name}" for name in record_speq.EXPECTED_KERNEL)
        cases.extend(SPEQ_MISSING)
    return cases


def save_manifest(path: Path, manifest: dict[str, Any]) -> None:
    """Write an atomic receipt, retaining the last completed stage on interruption."""
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(manifest, indent=2, default=str) + "\n")
    temporary.replace(path)


def run_complete_command(command: list[str], cwd: Path, prefix: Path, timeout_sec: float) -> PilotProcessResult:
    """Retain preflight refusals as safety stops, using the same policy at every stage."""
    try:
        return run_bounded_command(
            command,
            cwd,
            prefix,
            timeout_sec=timeout_sec,
            require_guard=True,
            disk_reserve_bytes=10 * 1024**3,
            allow_warning_pressure=False,
        )
    except ValueError as error:
        if "guard refused" not in str(error):
            raise
        prefix.parent.mkdir(parents=True, exist_ok=True)
        stdout, stderr = Path(str(prefix) + ".stdout.log"), Path(str(prefix) + ".stderr.log")
        stdout.write_text("")
        stderr.write_text(str(error) + "\n")
        return PilotProcessResult("resource-stopped", None, 0, 0, stdout, stderr, str(error))


def validate_extract_output(source: str, stdout: str, *, line_protocol: bool = False) -> list[list[str]]:
    """Require one closed result per original extraction, including the zero-root case."""
    requests = [tokens for _, _, tokens in egglog_forms(source) if tokens[1] == "extract"]
    # These frontends use ordinary best extraction only. Unknown variants must not
    # silently inherit the one-result contract.
    if any(len(tokens) != 4 and not (len(tokens) == 5 and tokens[-2] == "0") for tokens in requests):
        raise ValueError("unsupported source extraction contract; expected one named root and optional zero variants")
    outputs = [tokens for _, _, tokens in egglog_forms(stdout)]
    if len(outputs) != len(requests):
        raise ValueError(f"extraction response count {len(outputs)} differs from source root count {len(requests)}")
    if line_protocol and len(stdout.splitlines()) != len(requests):
        raise ValueError("native MLIR parser requires exactly one output line per extraction root")
    forbidden = {"let", "check", "union", "rule", "rewrite", "run", "run-schedule", "extract", "include"}
    if any(tokens[1] in forbidden or any(t.startswith("$") for t in tokens) for tokens in outputs):
        raise ValueError("extraction output must contain closed terms, not commands or globals")
    return outputs


def patch_dialegg_pass(source: str) -> str:
    """Retain the whole original pass, checking the external protocol before reconstruction."""
    source = "#include <cstdlib>\n#include <stdexcept>\n" + source
    source = materialize.replace_once(
        source,
        "std::ofstream eggFileOut(opsEggFilePath);",
        """static size_t captureIndex = 0;
    const char* captureDirectory = std::getenv("DIALEGG_CAPTURE_DIR");
    if (!captureDirectory) throw std::runtime_error("DIALEGG_CAPTURE_DIR required");
    opsEggFilePath = std::string(captureDirectory) + "/invocation-" + std::to_string(captureIndex++) + ".egg";
    egglogExtractedFilename = opsEggFilePath + ".stdout";
    egglogLogFilename = opsEggFilePath + ".stderr";
    std::ofstream contextFile(opsEggFilePath + ".context");
    contextFile << blockName << "\\n";
    contextFile.close();
    std::ofstream eggFileOut(opsEggFilePath);""",
        "unique native invocation paths",
    )
    source = materialize.replace_once(
        source,
        'std::string egglogCmd = "egglog " + opsEggFilePath + " > " + egglogExtractedFilename'
        ' + " 2> " + egglogLogFilename;',
        r"""auto quote = [](const std::string& value) {
        std::string result = "'";
        for (char c: value) result += c == '\'' ? "'\\''" : std::string(1, c);
        return result + "'";
    };
    const char* python = std::getenv("DIALEGG_CAPTURE_PYTHON");
    const char* bridge = std::getenv("DIALEGG_CAPTURE_BRIDGE");
    const char* backend = std::getenv("DIALEGG_NATIVE_EGGLOG");
    if (!python || !bridge || !backend) throw std::runtime_error("complete capture delegate environment required");
    std::string egglogCmd = quote(python) + " " + quote(bridge) + " --delegate " + quote(backend)
        + " " + quote(opsEggFilePath) + " " + quote(egglogExtractedFilename) + " " + quote(egglogLogFilename);""",
        "checked backend delegate",
    )
    source = materialize.replace_once(
        source,
        "std::system(egglogCmd.c_str());",
        "if (std::system(egglogCmd.c_str()) != 0)\n"
        '        throw std::runtime_error("Egglog backend or output contract failed");',
        "backend status check",
    )
    source = materialize.replace_once(
        source,
        "std::getline(file, line);",
        'if (!std::getline(file, line) || line.empty()) throw std::runtime_error("missing extraction response");',
        "reconstruction input check",
    )
    source = materialize.replace_once(
        source,
        "file.close();",
        """std::string unexpectedOutput;
    if (std::getline(file, unexpectedOutput)) throw std::runtime_error("extra extraction response");
    file.close();""",
        "reconstruction response exhaustion",
    )
    return source


def delegate_backend(backend: Path, source: Path, stdout: Path, stderr: Path) -> int:
    """Run the real engine under the native parent's process group, preserving all bytes."""
    manifest: dict[str, Any] = {
        "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
        "backend_sha256": hashlib.sha256(backend.read_bytes()).hexdigest(),
        "command": [str(backend), str(source)],
        "cwd": str(Path.cwd()),
        "environment": {"RUST_LOG": "info"},
        "status": "running",
        "extract_requests": [tokens for _, _, tokens in egglog_forms(source.read_text()) if tokens[1] == "extract"],
    }
    receipt = source.with_suffix(".json")
    save_manifest(receipt, manifest)
    with stdout.open("wb") as out, stderr.open("wb") as err:
        process = subprocess.run(
            manifest["command"], stdout=out, stderr=err, check=False, env={**os.environ, **manifest["environment"]}
        )
    manifest.update(
        returncode=process.returncode,
        stdout_sha256=hashlib.sha256(stdout.read_bytes()).hexdigest(),
        stderr_sha256=hashlib.sha256(stderr.read_bytes()).hexdigest(),
        status="failed",
    )
    try:
        if process.returncode:
            raise ValueError(f"native backend failed with exit {process.returncode}")
        outputs = validate_extract_output(source.read_text(), stdout.read_text(), line_protocol=True)
        manifest.update(status="complete", output_terms=outputs, output_count=len(outputs))
        logged = re.findall(r"extracted with cost (\d+): ([^\n]+)", stderr.read_text())
        if len(logged) == len(outputs) and [egglog_forms(term)[0][2] for _, term in logged] == outputs:
            manifest["extract_costs"] = [int(cost) for cost, _ in logged]
        else:
            manifest["cost_evidence_unavailable"] = "native extraction cost logs missing or not bound to output terms"
    except ValueError as error:
        manifest["reason"] = str(error)
    save_manifest(receipt, manifest)
    return 0 if manifest["status"] == "complete" else 1


def prepare_complete_dialegg(
    prefix: Path, source: Path, output: Path, timeout_sec: float
) -> tuple[Path | None, dict[str, Any]]:
    """Build only a copied frontend; preserve patch/source/tool identities and each command."""
    work = output / "frontend"
    shutil.copytree(source / "src", work / "src")
    path = work / "src/EqualitySaturationPass.cpp"
    original = path.read_text()
    patched = patch_dialegg_pass(original)
    path.write_text(patched)
    evidence: dict[str, Any] = {
        "source_revision": materialize.DIALEGG_COMMIT,
        "source_files": {
            str(p.relative_to(source)): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted((source / "src").rglob("*"))
            if p.is_file()
        },
        "original_pass_sha256": hashlib.sha256(original.encode()).hexdigest(),
        "patched_pass_sha256": hashlib.sha256(patched.encode()).hexdigest(),
        "patch_implementation_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "compiler_sha256": hashlib.sha256((prefix / "bin/clang++").read_bytes()).hexdigest(),
        "builds": [],
    }
    objects = [work / f"{name}.o" for name in ("egg-opt", "EqualitySaturationPass", "Egglog")]
    binary = work / "egg-opt-complete"
    commands = [
        [
            str(prefix / "bin/clang++"),
            "-std=c++17",
            "-O0",
            "-g0",
            f"-I{prefix / 'include'}",
            "-c",
            str(work / "src" / f"{obj.stem}.cpp"),
            "-o",
            str(obj),
        ]
        for obj in objects
    ]
    commands.append(
        [
            str(prefix / "bin/clang++"),
            *map(str, objects),
            f"-L{prefix / 'lib'}",
            "-lMLIROptLib",
            "-lMLIR",
            "-lLLVM",
            f"-Wl,-rpath,{prefix / 'lib'}",
            "-o",
            str(binary),
        ]
    )
    for index, command in enumerate(commands):
        result = run_complete_command(command, work, output / f"build-{index}", timeout_sec)
        evidence["builds"].append({"command": command, **asdict(result)})
        save_manifest(output / "preparation.json", evidence)
        if result.status != "success":
            return None, evidence
    evidence["binary_sha256"] = hashlib.sha256(binary.read_bytes()).hexdigest()
    save_manifest(output / "preparation.json", evidence)
    return binary, evidence


def capture_complete_dialegg(args: argparse.Namespace, cases: list[str], output: Path) -> dict[str, Any]:
    """Require complete native reconstruction and exact standalone output agreement per parent."""
    from scripts.reproduction_validation import (
        materialize_static_native_contract,
        static_extract_model,
        validate_static_native_output,
    )
    from scripts.suite_capture_dialegg_speq import modernize_dialegg_invocation

    source = args.dialegg_source.resolve()
    binary, preparation = prepare_complete_dialegg(args.llvm18_prefix.resolve(), source, output, args.timeout_sec)
    report: dict[str, Any] = {"preparation": preparation, "cases": {}}
    if binary is None:
        failure = preparation["builds"][-1]
        report["cases"] = {
            case: {
                "status": "blocked",
                "reason": "native frontend build did not complete",
                "workloads": [],
                "source_completion": {"status": "build-failed"},
            }
            for case in cases
        }
        if failure["status"] in STOP_STATUSES:
            report["operational_stop"] = failure
        return report
    prelude = materialize.modernize_dialegg_base((source / "src/base.egg").read_text())
    for case_id in cases:
        config = DIALEGG_CONFIGS[case_id]
        case_dir = output / case_id
        calls = case_dir / "calls"
        calls.mkdir(parents=True)
        source_input = source / str(config["input"])
        template = source / str(config["template"])
        copied_input, copied_template = case_dir / "input.mlir", case_dir / "input.egg"
        shutil.copyfile(source_input, copied_input)
        shutil.copyfile(template, copied_template)
        row: dict[str, Any] = {
            **config,
            "status": "blocked",
            "source_complete": False,
            "ordinary_compatible": False,
            "proof_validation": "not-run",
            "workloads": [],
            "invocations": [],
            "reason": None,
            "receipt": str(case_dir / "manifest.json"),
            "source_completion": {"status": "pending", "device_execution": "excluded"},
            "input_sha256": hashlib.sha256(copied_input.read_bytes()).hexdigest(),
            "template_sha256": hashlib.sha256(copied_template.read_bytes()).hexdigest(),
        }
        report["cases"][case_id] = row
        optimized = case_dir / "optimized.mlir"
        command = [
            "env",
            f"DIALEGG_CAPTURE_DIR={calls}",
            f"DIALEGG_CAPTURE_PYTHON={sys.executable}",
            f"DIALEGG_CAPTURE_BRIDGE={Path(__file__).resolve()}",
            f"DIALEGG_NATIVE_EGGLOG={args.native_egglog.resolve()}",
            str(binary),
            "--mlir-disable-threading",
            *config["passes"],
            str(copied_input),
            "--egg",
            str(copied_template),
            "-o",
            str(optimized),
        ]
        result = run_complete_command(command, binary.parent, case_dir / "native", args.timeout_sec)
        row["native"] = {"command": command, **asdict(result)}
        row["source_completion"].update(status=result.status, parent=row["native"])
        raw_calls = sorted(calls.glob("invocation-*.egg"), key=lambda p: int(p.stem.rsplit("-", 1)[1]))
        for raw in raw_calls:
            receipt = raw.with_suffix(".json")
            row["invocations"].append(
                {
                    "raw": str(raw),
                    "native": json.loads(receipt.read_text()) if receipt.exists() else {"status": "incomplete"},
                }
            )
        save_manifest(case_dir / "manifest.json", row)
        if result.status in STOP_STATUSES:
            report["operational_stop"] = asdict(result)
            break
        if result.status != "success" or not optimized.is_file() or not optimized.stat().st_size:
            row["reason"] = "native optimization did not finish with nonempty MLIR"
            row["source_completion"]["status"] = "failed"
            save_manifest(case_dir / "manifest.json", row)
            continue
        if not raw_calls or any(v["native"]["status"] != "complete" for v in row["invocations"]):
            row["reason"] = "native parent did not retain a complete response for every reached Egglog call"
            row["source_completion"]["status"] = "incomplete-invocations"
            save_manifest(case_dir / "manifest.json", row)
            continue
        verified = case_dir / "verified.mlir"
        verify = [str(args.llvm18_prefix.resolve() / "bin/mlir-opt"), str(optimized), "-o", str(verified)]
        checked = run_complete_command(verify, case_dir, case_dir / "verify-mlir", args.timeout_sec)
        row["mlir_verification"] = {"command": verify, **asdict(checked)}
        row["optimized_mlir_sha256"] = hashlib.sha256(optimized.read_bytes()).hexdigest()
        row["source_complete"] = checked.status == "success" and verified.is_file() and verified.stat().st_size > 0
        row["source_completion"].update(
            status="complete" if row["source_complete"] else "verification-failed",
            output_path=str(optimized),
            output_sha256=row["optimized_mlir_sha256"],
            verifier=row["mlir_verification"],
        )
        save_manifest(case_dir / "manifest.json", row)
        if checked.status in STOP_STATUSES:
            report["operational_stop"] = asdict(checked)
            break
        if not row["source_complete"]:
            row["reason"] = "final MLIR verification did not produce a nonempty verified module"
            save_manifest(case_dir / "manifest.json", row)
            continue
        row["materialization"] = {"expected_sessions": len(raw_calls), "materialized_sessions": 0, "complete": False}
        for invocation, raw in zip(row["invocations"], raw_calls, strict=True):
            modern = modernize_dialegg_invocation(raw.read_text(), prelude, diagnostic_queries=False)
            replay = raw.with_suffix(".standalone.egg")
            invocation["output_contract"] = {
                "kind": "ordinary-best-extract",
                "extract_requests": invocation["native"]["extract_requests"],
                "expected_terms": invocation["native"]["output_terms"],
                "cost_semantics": "source constructor and dynamic costs preserved; exact native terms required",
                "zero_root_helper": not invocation["native"]["output_count"],
            }
            native = invocation["native"]
            if native["output_count"] and "extract_costs" in native:
                try:
                    original = materialize.replace_once(
                        raw.read_text(),
                        '(include "src/base.egg")',
                        (source / "src/base.egg").read_text(),
                        "base prelude",
                    )
                    # The old prelude declares lookup tables as functions without
                    # merge clauses. Exclude these declarations from constructor
                    # comparison only when they are never applied in this session.
                    lookups = {tokens[2] for _, _, tokens in egglog_forms(modern) if tokens[1] == "function"}
                    original_forms = egglog_forms(original)
                    if any(
                        left == "(" and right in lookups
                        for _, _, tokens in original_forms
                        for left, right in zip(tokens, tokens[1:], strict=False)
                    ):
                        raise ValueError("active historical lookup functions lack a verified static constructor model")
                    for start, end, tokens in reversed(original_forms):
                        if tokens[1] == "function" and tokens[2] in lookups:
                            original = original[:start] + original[end:]
                    if static_extract_model(original, native["output_terms"]) != static_extract_model(
                        modern, native["output_terms"]
                    ):
                        raise ValueError("native and modernized typed static cost models differ")
                    modern, contract = materialize_static_native_contract(
                        modern, native["output_terms"], native["extract_costs"]
                    )
                    invocation["output_contract"] = contract
                except ValueError as error:
                    # Unsupported costs/containers keep exact-output admission;
                    # they never acquire the equal-cost representative exemption.
                    invocation["static_tie_ineligible"] = str(error)
            replay.write_text(modern)
            invocation["standalone"] = str(replay)
            invocation["standalone_sha256"] = hashlib.sha256(replay.read_bytes()).hexdigest()
            row["materialization"]["materialized_sessions"] += 1
        row["materialization"]["complete"] = True
        row["status"] = "ordinary-validation-pending"
        for invocation, raw in zip(row["invocations"], raw_calls, strict=True):
            replay = Path(invocation["standalone"])
            modern = replay.read_text()
            contract = invocation["output_contract"]
            command = [str(args.egglog.resolve()), str(replay)]
            if contract["kind"] == "ordinary-best-static-native":
                command = ["env", "RUST_LOG=egglog::extract=debug", *command]
            check = run_complete_command(command, case_dir, raw.with_suffix(".replay"), args.timeout_sec)
            invocation["ordinary"] = {"command": command, **asdict(check)}
            invocation["output_matches_native"] = False
            invocation["output_contract_passed"] = False
            if check.status == "success":
                try:
                    outputs = validate_extract_output(modern, check.stdout_path.read_text())
                    invocation["output_matches_native"] = outputs == invocation["native"]["output_terms"]
                    if contract["kind"] == "ordinary-best-static-native":
                        invocation["cost_validation"] = validate_static_native_output(
                            modern, contract, check.stdout_path.read_text(), check.stderr_path.read_text()
                        )
                    elif not invocation["output_matches_native"]:
                        raise ValueError("ordinary replay extraction differs from the native engine response")
                    invocation["output_contract_passed"] = True
                except ValueError as error:
                    invocation["reason"] = str(error)
            save_manifest(case_dir / "manifest.json", row)
            if check.status in STOP_STATUSES:
                report["operational_stop"] = asdict(check)
                break
        row["ordinary_compatible"] = all(v.get("output_contract_passed") for v in row["invocations"])
        if row["ordinary_compatible"]:
            row["status"] = "reproduced"
            row["workloads"] = [v["standalone"] for v in row["invocations"]]
        else:
            row["status"] = "ordinary-validation-failed"
            row["reason"] = "at least one ordinary replay failed or differed from the native extraction output"
        save_manifest(case_dir / "manifest.json", row)
        if report.get("operational_stop"):
            break
    return report


def capture_complete_speq(args: argparse.Namespace, cases: list[str], output: Path) -> dict[str, Any]:
    """Run original C through all REV regions, then validate the whole retained session."""
    report: dict[str, Any] = {"cases": {}}
    frontend_flags = list(getattr(args, "speq_frontend_flag", []))
    repair_phi = bool(getattr(args, "speq_phi_polarity_repair", False))
    c99_mode = getattr(args, "speq_c99_frontend_repair", None)
    if c99_mode is not None:
        from scripts.speq_c99_diagnostic import CONTRACT, FRONTEND_FLAGS

        if c99_mode != CONTRACT or not repair_phi or tuple(frontend_flags) != FRONTEND_FLAGS:
            raise ValueError("C99 mode requires the named GEMM repair, PHI, and pinned frontend flags")
    for case_id in cases:
        row: dict[str, Any] = {
            "status": "blocked",
            "reason": None,
            "workloads": [],
            "source_complete": False,
            "ordinary_compatible": False,
            "proof_validation": "not-run",
            "frontend_flags": frontend_flags,
            "phi_polarity_repair": repair_phi,
            "c99_frontend_repair": c99_mode if case_id == "speq-polybench_gemm" else None,
        }
        report["cases"][case_id] = row
        if case_id in SPEQ_MISSING:
            row["reason"] = SPEQ_MISSING[case_id]
            row["source_completion"] = {"status": "missing-input", "device_execution": "excluded"}
            continue
        case_dir = output / case_id
        case_dir.mkdir()
        replay = case_dir / "standalone.egg"
        command = [
            str(args.speq_python.absolute()),
            str(ROOT / "scripts/paper_benchmarks/record_speq.py"),
            "--artifact",
            str(args.speq_artifact.resolve()),
            "--lleq",
            str(args.speq_lleq.resolve()),
            "--rev-tests",
            str(args.speq_lleq.resolve() / "llvm/unittests/Transforms/REV/REVTest.cpp"),
            "--llvm-config",
            str(args.llvm17_config.resolve()),
            "--benchmark",
            case_id.removeprefix("speq-"),
            "--complete",
            "--source-evidence",
            str(case_dir / "source"),
            "--output",
            str(replay),
        ]
        if c99_mode and case_id == "speq-polybench_gemm":
            command.extend(["--c99-frontend-repair", c99_mode])
        if repair_phi:
            command.append("--repair-phi-polarity")
            if args.speq_rev_plugin:
                row["omitted_prebuilt_rev_plugin"] = {
                    "path": str(args.speq_rev_plugin.resolve()),
                    "reason": "Source repair requires fresh plugins from the recorded patched source",
                }
        elif args.speq_rev_plugin:
            command.extend(["--rev-plugin", str(args.speq_rev_plugin.resolve())])
        command.extend(f"--frontend-flag={flag}" for flag in frontend_flags)
        native = run_complete_command(command, ROOT, case_dir / "native", args.timeout_sec)
        row["native"] = {"command": command, **asdict(native)}
        receipt = replay.with_suffix(".manifest.json")
        if receipt.is_file():
            row["source"] = json.loads(receipt.read_text())
        row["source_complete"] = native.status == "success" and row.get("source", {}).get("source_complete", False)
        row["receipt"] = str(case_dir / "manifest.json")
        row["source_completion"] = {
            "status": "complete" if row["source_complete"] else "failed",
            "parent": row["native"],
            "recorder_receipt": str(receipt),
            "device_execution": "excluded",
            "output_path": str(replay),
            "output_sha256": row.get("source", {}).get("standalone_sha256"),
        }
        row["reason"] = row.get("source", {}).get("reason") or native.message
        save_manifest(case_dir / "manifest.json", row)
        if native.status in STOP_STATUSES:
            report["operational_stop"] = asdict(native)
            break
        if not row["source_complete"]:
            continue
        expected = [tokens for _, _, tokens in egglog_forms(row["source"]["expected_stdout"])]
        row["output_contract"] = {
            "kind": "ordinary-best-extract",
            "expected_terms": expected,
            "extract_requests": [tokens for _, _, tokens in egglog_forms(replay.read_text()) if tokens[1] == "extract"],
            "native_costs": [region["cost"] for region in row["source"]["regions"] if "cost" in region],
            "cost_semantics": "original constructor costs preserved; replay CLI prints terms only",
        }
        row["materialization"] = {"expected_sessions": 1, "materialized_sessions": 1, "complete": True}
        row["status"] = "ordinary-validation-pending"
        command = [str(args.egglog.resolve()), str(replay)]
        ordinary = run_complete_command(command, case_dir, case_dir / "ordinary", args.timeout_sec)
        row["ordinary"] = {"command": command, **asdict(ordinary)}
        if ordinary.status == "success":
            try:
                outputs = validate_extract_output(replay.read_text(), ordinary.stdout_path.read_text())
                if outputs != expected:
                    raise ValueError("standalone outputs differ from native extraction responses")
                row.update(status="reproduced", ordinary_compatible=True, workloads=[str(replay)])
            except ValueError as error:
                row["reason"] = str(error)
        if row["status"] != "reproduced":
            row["status"] = "ordinary-validation-failed"
        save_manifest(case_dir / "manifest.json", row)
        if ordinary.status in STOP_STATUSES:
            report["operational_stop"] = asdict(ordinary)
            break
    return report


def complete_capture(args: argparse.Namespace) -> int:
    """Public complete-mode dispatcher; no admission by bytes or exit status alone."""
    allowed = complete_case_ids(args.family, extras=True)
    cases = args.case or complete_case_ids(args.family)
    if len(cases) != len(set(cases)) or set(cases) - set(allowed):
        raise ValueError("--case must select unique complete-mode IDs in the requested family")
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    os.environ["EGGLOG_BENCH_MEMORY_GUARD"] = "1"
    result: dict[str, Any] = {
        "mode": "complete",
        "requested_cases": cases,
        "families": {},
        "replay_engine_sha256": hashlib.sha256(args.egglog.read_bytes()).hexdigest(),
    }
    for family, capture in (("dialegg", capture_complete_dialegg), ("speq", capture_complete_speq)):
        selected = [case for case in cases if case.startswith(family + "-")]
        if not selected:
            continue
        directory = output / family
        directory.mkdir()
        result["families"][family] = capture(args, selected, directory)
        save_manifest(output / "manifest.json", result)
        if result["families"][family].get("operational_stop"):
            return 2
    success = all(v["status"] == "reproduced" for f in result["families"].values() for v in f["cases"].values())
    return 0 if success else 1


if __name__ == "__main__":
    # Direct execution is reserved for the guarded native parent's delegate.
    if len(sys.argv) != 6 or sys.argv[1] != "--delegate":
        raise SystemExit("Use scripts/suite_capture_dialegg_speq.py --complete")
    raise SystemExit(delegate_backend(*(Path(value) for value in sys.argv[2:])))
