"""Compile and check the exact HVX concat fragment with LLVM12, never a target kernel.

Only the CLI takes the shared heavy-job lock. The in-process API requires its
caller's exclusive slot. Every child is serial, guarded, and recorded.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shlex
from dataclasses import asdict
from pathlib import Path
from typing import Any

from benchmarking.pilot import run_bounded_command
from scripts import reproduction_misaal_hvx_lowering as lowering
from scripts.reproduction_process import DISK_RESERVE_BYTES, exclusive_job

ROOT = Path(__file__).resolve().parents[1]
SUPPORT = Path(__file__).with_name("paper_benchmarks") / "misaal_hvx_concat_harness.cpp"
COMMON_SOURCE_SHA256 = "cf595e9c1ff60c46234ba327a8ea10738b82e934b0a42f46c18fc5ab1ce79860"
ACCESSOR_START = "Value *Legalizer::getBitvectorOfRequiredType("
ACCESSOR_END = "\nstd::vector<Value *> Legalizer::getArgsAfterPermutation("
POSITIVE_MODES = ("direct", "mapped-scalar", "mapped-vector", "unrelated")
REJECTIONS = {
    **dict.fromkeys(("arity-two", "arity-four"), "MISAAL concat requires three arguments"),
    **dict.fromkeys(
        (
            "scalar-input",
            "input-lanes",
            "input-element",
            "input-integer-width",
            "input-scalable",
            "scalar-output",
            "output-lanes",
            "output-element",
            "output-scalable",
            "input-width-value",
            "output-width-value",
            "input-width-type",
            "output-width-type",
            "input-width-variable",
            "output-width-variable",
        ),
        "MISAAL concat source shape or width annotation changed",
    ),
    "mapped-width": "MISAAL concat input mapping has an incompatible width",
}


def materialize(common_source: Path, output: Path) -> dict[str, Any]:
    """Pin original mapping semantics and inject both production code fragments verbatim."""
    common_source, output = common_source.resolve(), output.resolve()
    if (
        output.exists()
        or output.is_relative_to(common_source.parent)
        or not output.is_relative_to((ROOT / "benchmarks/local/reproduction").resolve())
    ):
        raise ValueError("diagnostic requires a fresh directory below benchmarks/local/reproduction")
    original = common_source.read_bytes()
    if hashlib.sha256(original).hexdigest() != COMMON_SOURCE_SHA256:
        raise ValueError("common Legalizer.cpp differs from the pinned Hydride source")
    source = original.decode()
    if source.count(ACCESSOR_START) != 1 or source.count(ACCESSOR_END) != 1:
        raise ValueError("common mapping accessor boundary changed")
    accessor = source[source.index(ACCESSOR_START) : source.index(ACCESSOR_END)]
    fragment = lowering.concat_lowering_cpp()
    template = SUPPORT.read_text()
    cpp = template
    for marker, value in (
        ("// INSERT_EXACT_CONCAT_FRAGMENT", fragment),
        ("// INSERT_EXACT_COMMON_ACCESSOR", accessor),
    ):
        if cpp.count(marker) != 1:
            raise ValueError("diagnostic source insertion boundary changed")
        cpp = cpp.replace(marker, value)
    output.mkdir(parents=True)
    files = {
        "Legalizer.cpp.original": original,
        "common-accessor.cpp.txt": accessor.encode(),
        "concat-fragment.cpp.txt": fragment.encode(),
        "harness-template.cpp": template.encode(),
        "concat-harness.cpp": cpp.encode(),
        "lowering.py": Path(lowering.__file__).read_bytes(),
        "runner.py": Path(__file__).read_bytes(),
    }
    for name, content in files.items():
        (output / name).write_bytes(content)
    record: dict[str, Any] = {
        "status": "materialized-unrun",
        "common_source": str(common_source),
        "common_source_sha256": COMMON_SOURCE_SHA256,
        "source_parent_execution": False,
        "device_execution": False,
        "corpus_admission": False,
        "evaluation": "LLVM constant folding of exact generated IR; exhaustive inputs and per-lane oracle",
        "positive_modes": POSITIVE_MODES,
        "negative_modes": REJECTIONS,
        "files": {name: hashlib.sha256(content).hexdigest() for name, content in files.items()},
    }
    (output / "materialization.json").write_text(json.dumps(record, indent=2) + "\n")
    return record


def run_diagnostic(
    common_source: Path, llvm: Path, output: Path, *, compiler: Path = Path("/usr/bin/clang++"), timeout_sec: int = 120
) -> dict[str, Any]:
    """Compile once, run isolated positive/rejection fixtures, and retain exact guard receipts."""
    llvm, output, compiler = (path.resolve() for path in (llvm, output, compiler))
    config = llvm / "bin/llvm-config"
    if timeout_sec <= 0 or not all(os.access(path, os.X_OK) for path in (compiler, config)):
        raise ValueError("an LLVM12 installation, executable compiler and positive timeout are required")
    record = materialize(common_source, output)
    record.update(status="blocked", reason=None, steps=[], tools={}, results=[])
    steps = output / "steps"
    steps.mkdir()

    def step(name: str, command: list[str], *, rejection: str | None = None) -> str:
        """Distinguish an exact intentional rejection from crashes and every guard failure."""
        prefix = steps / f"{len(record['steps']) + 1:03}-{name}"
        request = {
            "command": command,
            "cwd": str(output),
            "timeout_sec": timeout_sec,
            "memory_limit_bytes": 5 * 1024**3,
            "allow_warning_pressure": True,
            "require_guard": True,
            "disk_reserve_bytes": DISK_RESERVE_BYTES,
            "expected_returncode": 86 if rejection else 0,
            "expected_rejection": rejection,
        }
        prefix.with_suffix(".request.json").write_text(json.dumps(request, indent=2) + "\n")
        record["steps"].append(str(prefix))
        try:
            result = run_bounded_command(
                command,
                output,
                prefix,
                timeout_sec=timeout_sec,
                memory_limit_bytes=5 * 1024**3,
                allow_warning_pressure=True,
                require_guard=True,
                disk_reserve_bytes=DISK_RESERVE_BYTES,
            )
        except (OSError, ValueError) as error:
            record["status"] = "launch-refused"
            prefix.with_suffix(".result.json").write_text(
                json.dumps({"status": "launch-refused", "reason": str(error)})
            )
            raise
        prefix.with_suffix(".result.json").write_text(json.dumps(asdict(result), indent=2, default=str) + "\n")
        if result.status not in {"success", "failure"}:
            record["status"] = result.status
            raise ValueError(f"{name}: {result.status}; native diagnostic halted")
        if rejection:
            expected = f"CONCAT_REJECT: {rejection}\n"
            if result.status != "failure" or result.returncode != 86 or expected not in result.stderr_path.read_text():
                raise ValueError(f"{name}: expected the exact source-fragment rejection, not a crash or acceptance")
        elif result.status != "success" or result.returncode != 0:
            raise ValueError(f"{name}: native diagnostic failed")
        return result.stdout_path.read_text()

    try:
        tools = [compiler, config]
        record["tools"] = {str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in tools}
        version = step("llvm-version", [str(config), "--version"]).strip()
        if re.fullmatch(r"12\.\d+\.\d+", version) is None:
            raise ValueError(f"diagnostic requires LLVM12, got {version!r}")
        record["llvm_version"] = version
        record["compiler_version"] = step("compiler-version", [str(compiler), "--version"]).strip()
        flags = shlex.split(
            step(
                "llvm-flags",
                [
                    str(config),
                    "--cxxflags",
                    "--ldflags",
                    "--link-shared",
                    "--libs",
                    "core",
                    "analysis",
                    "--system-libs",
                ],
            )
        )
        libraries = shlex.split(
            step("llvm-libraries", [str(config), "--link-shared", "--libfiles", "core", "analysis"])
        )
        if not libraries:
            raise ValueError("LLVM did not report its linked libraries")
        for path in [*(Path(name).resolve() for name in libraries), llvm / "include/llvm/Analysis/ConstantFolding.h"]:
            record["tools"][str(path)] = hashlib.sha256(path.read_bytes()).hexdigest()
        binary = output / "concat-harness"
        step(
            "compile",
            [
                str(compiler),
                *flags,
                "-std=c++14",
                "-O0",
                str(output / "concat-harness.cpp"),
                "-o",
                str(binary),
                f"-Wl,-rpath,{llvm / 'lib'}",
            ],
        )
        record["binary_sha256"] = hashlib.sha256(binary.read_bytes()).hexdigest()
        record["tools"][str(binary)] = record["binary_sha256"]
        for width in (16, 8):
            for mode in POSITIVE_MODES:
                row = json.loads(step(f"{width}-{mode}", [str(binary), mode, str(width)]))
                wanted = {
                    "mode": mode,
                    "width": width,
                    "checks": 1 if mode == "unrelated" else 1 << width,
                    "verified_ir": True,
                }
                if row != wanted:
                    raise ValueError(f"{width}-{mode}: incomplete native checks")
                record["results"].append(row)
            for mode, reason in REJECTIONS.items():
                step(f"{width}-{mode}", [str(binary), mode, str(width)], rejection=reason)
                record["results"].append({"mode": mode, "width": width, "rejection": reason})
        if any(
            hashlib.sha256(Path(name).read_bytes()).hexdigest() != digest for name, digest in record["tools"].items()
        ):
            raise ValueError("a native tool or linked LLVM dependency changed during the diagnostic")
        if any(
            hashlib.sha256((output / name).read_bytes()).hexdigest() != digest
            for name, digest in record["files"].items()
        ):
            raise ValueError("retained diagnostic sources changed during execution")
        record.update(
            status="success", exhaustive_value_cases=3 * ((1 << 16) + (1 << 8)), rejected_shapes=2 * len(REJECTIONS)
        )
    except (OSError, ValueError, KeyError) as error:
        record["reason"] = str(error)
    finally:
        record["artifacts"] = {
            str(path.relative_to(output)): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in sorted(output.rglob("*"))
            if path.is_file()
        }
        (output / "diagnostic.json").write_text(json.dumps(record, indent=2) + "\n")
    return record


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--common-source", type=Path, required=True)
    parser.add_argument("--llvm", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--compiler", type=Path, default=Path("/usr/bin/clang++"))
    parser.add_argument("--timeout-sec", type=int, default=120)
    parser.add_argument("--materialize-only", action="store_true")
    args = parser.parse_args()
    if args.materialize_only:
        record = materialize(args.common_source, args.output)
    else:
        with exclusive_job(ROOT / "benchmarks/local/reproduction/stages/.heavy-job.lock"):
            record = run_diagnostic(
                args.common_source, args.llvm, args.output, compiler=args.compiler, timeout_sec=args.timeout_sec
            )
    print(json.dumps(record, indent=2))
    return 0 if record["status"] in {"success", "materialized-unrun"} else 1


if __name__ == "__main__":
    raise SystemExit(main())
