"""Complete native DialEgg parents and retain their standalone output contracts.

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

from scripts.hardboiled_replay import egglog_forms  # noqa: E402
from scripts.paper_benchmarks import materialize  # noqa: E402
from scripts.reproduction_inventory import dialegg_configurations  # noqa: E402
from scripts.reproduction_process import PilotProcessResult, run_bounded_command  # noqa: E402
from scripts.source_tools import Preparation  # noqa: E402

STOP_STATUSES = {"resource-stopped", "memory-limit", "timed-out"}
DIALEGG_CONFIGS = dialegg_configurations(json.loads((ROOT / "benchmarks/sources.json").read_text())["dialegg"])


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
    for tokens in requests:
        arguments = tokens[2:-1]
        end = 1
        if arguments and arguments[0] == "(":
            depth = 0
            for index, token in enumerate(arguments, start=1):
                depth += (token == "(") - (token == ")")
                if depth == 0:
                    end = index
                    break
        if not arguments or arguments[end:] not in ([], ["0"]):
            raise ValueError("unsupported source extraction contract; expected one root and optional zero variants")
    outputs = [tokens for _, _, tokens in egglog_forms(stdout)]
    if len(outputs) != len(requests):
        raise ValueError(f"extraction response count {len(outputs)} differs from source root count {len(requests)}")
    if line_protocol and len(stdout.splitlines()) != len(requests):
        raise ValueError("native MLIR parser requires exactly one output line per extraction root")
    forbidden = {"let", "check", "union", "rule", "rewrite", "run", "run-schedule", "extract", "include"}
    if any(tokens[1] in forbidden or any(t.startswith("$") for t in tokens) for tokens in outputs):
        raise ValueError("extraction output must contain closed terms, not commands or globals")
    return outputs


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
    work = output / "sources/dialegg-frontend"
    shutil.copytree(source / "src", work / "src")
    path = work / "src/EqualitySaturationPass.cpp"
    original = path.read_text()
    patch = ROOT / "benchmarks/reproduction/patches/dialegg-capture.diff"
    preparation = Preparation(output, continuation=True)
    preparation.apply_patch(work, patch)
    patched = path.read_text()
    evidence: dict[str, Any] = {
        "source_revision": materialize.DIALEGG_COMMIT,
        "source_files": {
            str(p.relative_to(source)): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted((source / "src").rglob("*"))
            if p.is_file()
        },
        "original_pass_sha256": hashlib.sha256(original.encode()).hexdigest(),
        "patched_pass_sha256": hashlib.sha256(patched.encode()).hexdigest(),
        "patch_sha256": hashlib.sha256(patch.read_bytes()).hexdigest(),
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
    from scripts.dialegg_compat import modernize_dialegg_invocation
    from scripts.reproduction_validation import (
        materialize_static_native_contract,
        static_extract_model,
        validate_static_native_output,
    )

    source = args.dialegg_source.resolve()
    binary = getattr(args, "prepared_frontend", None)
    preparation: dict[str, Any] = {"binary": str(binary)}
    if binary is None:
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
        if result.status in {"resource-stopped", "memory-limit", "cancelled", "interrupted"}:
            row.update(status=result.status, reason=result.message or result.status)
            report["operational_stop"] = asdict(result)
            save_manifest(case_dir / "manifest.json", row)
            break
        if result.status != "success":
            row["parent_failure"] = row["native"]
        # Every delegate call starts a new graph. Later MLIR reconstruction or
        # code generation cannot invalidate a completed Egglog response.
        row["failed_invocations"] = [call for call in row["invocations"] if call["native"]["status"] != "complete"]
        row["invocations"] = [
            {**call, "source_order": index}
            for index, call in enumerate(row["invocations"])
            if call["native"]["status"] == "complete"
        ]
        raw_calls = [Path(call["raw"]) for call in row["invocations"]]
        if not raw_calls:
            row["reason"] = "source produced no complete Egglog response"
            save_manifest(case_dir / "manifest.json", row)
            continue
        row["source_complete"] = result.status == "success"
        row["source_completion"].update(status="complete", scope="completed-independent-egglog-calls")
        if optimized.is_file():
            row["optimized_mlir_sha256"] = hashlib.sha256(optimized.read_bytes()).hexdigest()
        row["materialization"] = {"expected_sessions": len(raw_calls), "materialized_sessions": 0, "complete": False}
        for invocation, raw in zip(row["invocations"], raw_calls, strict=True):
            modern = modernize_dialegg_invocation(raw.read_text(), prelude)
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
        if not getattr(args, "validate_ordinary", True):
            save_manifest(case_dir / "manifest.json", row)
            continue
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


if __name__ == "__main__":
    if len(sys.argv) != 6 or sys.argv[1] != "--delegate":
        raise SystemExit("Use python -m scripts.suite_reproduction")
    raise SystemExit(delegate_backend(*(Path(value) for value in sys.argv[2:])))
