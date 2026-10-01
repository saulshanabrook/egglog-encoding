"""Compile original MISAAL generators and emit complete-capture requests.

Reuse a verified prepared 44ff environment. This runs serial host compiler jobs
only; native optimization remains with the coordinator. The API uses its caller's
job slot, while the CLI acquires the shared lock. Pattern caches remain fresh.
"""

from __future__ import annotations

import argparse
import copy
import json
import os
import platform
import re
import shlex
from pathlib import Path
from typing import Any

from scripts.misaal_reproduction import verified_request
from scripts.reproduction_inventory import expected_cases
from scripts.reproduction_prepare_misaal import HYDRIDE_REVISION, MISAAL_REVISION, Preparation, sha256_file, write_json
from scripts.reproduction_process import exclusive_job

ROOT = Path(__file__).resolve().parents[1]
MAKEFILE_SHA256 = "6a6e3d1e5fd77e462ca1541e5fa07bb8494b0764a9df8cc4d689391468d8855e"
ARM_MAKEFILE_SHA256 = "a3e5edfe61ea0717aad9ed0d4082fcc1fb7f4aa89a5edd1479a816e670694a7d"
HVX_MAKEFILE_SHA256 = "a080e81131bd15b89fea2da1fc63fe6320a3b451c9a07273bd589177f3b43eaf"
TARGET = "host-x86-64-no_bounds_query-no_asserts"
ARM_TARGET = "arm-64-osx-arm_dot_prod-no_asserts-no_bounds_query"
HVX_TARGET = "hexagon-32-noos-no_bounds_query-no_asserts-hvx_128-hvx_v66"
DEFAULTS = {
    "HL_EXPR_DEPTH": "2",
    "HL_SYNTH_BW": "16",
    "HL_ENABLE_MISAAL": "1",
    "HL_ENABLE_HYDRIDE": "1",
    "HYDRIDE_INITIAL_HASH": "empty_hash",
    "MISAAL_DISABLE_FRONTEND_PATTERNS": "1",
}


def compile_dependencies(path: Path, checkout: Path, required: set[Path]) -> dict[str, str]:
    """Bind the compiler-observed dependency closure, including local included headers."""
    target, separator, content = path.read_text().replace("\\\n", " ").partition(":")
    if not target or not separator:
        raise ValueError("compiler did not emit a valid dependency file")
    paths = {(checkout / name).resolve() for name in shlex.split(content)}
    if not {file.resolve() for file in required}.issubset(paths):
        raise ValueError("compiler dependency file omitted an original generator input")
    return {str(file): sha256_file(file) for file in sorted(paths)}


def compile_object(
    preparation: Preparation,
    source: Path,
    directory: Path,
    flags: list[str],
    checkout: Path,
    header: Path,
    timeout_sec: int,
) -> tuple[Path, dict[str, str]]:
    """Compile one translation unit so its dependency file cannot be overwritten."""
    destination = directory / f"{source.stem}.o"
    dependencies = directory / f"{source.stem}.d"
    preparation.step(
        f"compile-{source.stem}",
        [*flags, "-c", str(source), "-MMD", "-MF", str(dependencies), "-o", str(destination)],
        cwd=checkout,
        timeout=timeout_sec,
    )
    if not destination.is_file() or not destination.stat().st_size:
        raise ValueError("successful compile omitted a native object")
    return destination, compile_dependencies(dependencies, checkout, {source, header})


def prepare_misaal_cases(
    output: Path,
    template_request: Path,
    *,
    case_ids: list[str] | None = None,
    compiler: Path = Path("/usr/bin/clang++"),
    timeout_sec: int = 120,
    target: str = "x86",
    legalizer: Path | None = None,
    hvx_selector_receipt: Path | None = None,
) -> dict[str, Any]:
    """Reuse a verified x86 environment for original generators of the selected ISA."""
    output, template_request, compiler = output.resolve(), template_request.resolve(), compiler.resolve()
    if not output.is_relative_to((ROOT / "benchmarks/local/reproduction").resolve()):
        raise ValueError("generator sources/requests/evidence must stay below benchmarks/local/reproduction")
    if output.exists():
        raise ValueError("generator preparation requires a fresh immutable attempt")
    if (platform.system(), platform.machine()) != ("Darwin", "arm64"):
        raise ValueError("this generator build recipe uses the prepared native Apple Silicon environment")
    if timeout_sec <= 0 or not os.access(compiler, os.X_OK):
        raise ValueError("a native executable compiler and positive timeout are required")
    if target not in ("x86", "arm", "hexagon") or (target != "x86" and legalizer is None):
        raise ValueError("ARM/HVX require their prepared legalizer; unsupported target recipe")
    if (target == "hexagon") != (hvx_selector_receipt is not None):
        raise ValueError("only HVX requires its successful immutable selector receipt")
    seed = verified_request(template_request)
    if seed["revision"] != MISAAL_REVISION or seed["configuration"] != {"target": "x86"}:
        raise ValueError("template must be the prepared MISAAL44ff x86 request")
    if any(seed["environment"].get(key) != value for key, value in DEFAULTS.items()):
        raise ValueError("template differs from original x86 Makefile graph-generation defaults")
    if seed.get("pattern_cache_contract", {}).get("environment") != "MISAAL_PATTERN_CACHE_DIR":
        raise ValueError("template must retain the fresh attempt-owned pattern-cache contract")
    if f"target={TARGET}" not in seed["generator_command"]:
        raise ValueError("template target differs from the original x86 Makefile")
    checkout = Path(seed["checkout"]).resolve()
    makefile = checkout / f"benchmarks/{target}/halide/Makefile"
    makefile_sha256 = {"x86": MAKEFILE_SHA256, "arm": ARM_MAKEFILE_SHA256, "hexagon": HVX_MAKEFILE_SHA256}[target]
    if sha256_file(makefile) != makefile_sha256:
        raise ValueError(f"original {target} generator Makefile changed")
    for key in ("library", "legalizer"):
        if sha256_file(Path(seed[key])) != seed[f"{key}_sha256"]:
            raise ValueError(f"prepared {key} differs from template identity")
    catalog_path, population_path = ROOT / "benchmarks/catalog.json", ROOT / "benchmarks/reproduction/population.json"
    inventory = expected_cases(json.loads(catalog_path.read_text()), json.loads(population_path.read_text()))
    cases = [case for case in inventory if case["family"] == "misaal" and case["configuration"] == {"target": target}]
    if case_ids is not None:
        if len(case_ids) != len(set(case_ids)) or set(case_ids) - {case["id"] for case in cases}:
            raise ValueError(f"case selectors must be unique inventoried {target} identities")
        cases = [case for case in cases if case["id"] in case_ids]
    if not cases:
        raise ValueError(f"no inventoried {target} generator requests selected")
    frontend = checkout / "frontends/halide"
    header = Path(seed["environment"]["HALIDE_DISTRIB"]) / "include/Halide.h"
    library = Path(seed["library"]).resolve()
    common = checkout / f"benchmarks/{target}/halide/hannk/common_halide.cpp"
    gengen = frontend / "tools/GenGen.cpp"
    legalizer = (legalizer or Path(seed["legalizer"])).resolve()
    for required in (header, common, gengen, legalizer):
        if not required.is_file() or not required.stat().st_size:
            raise ValueError(f"original generator prerequisite is missing: {required}")
    if target == "arm" and legalizer.name != "libARMLegalizer.so":
        raise ValueError("ARM request must use the prepared libARMLegalizer.so output")
    hvx_link_contract = None
    if hvx_selector_receipt is not None:
        hvx_selector_receipt = hvx_selector_receipt.resolve()
        selector = json.loads(hvx_selector_receipt.read_text())
        if (
            selector.get("status") != "success"
            or selector.get("target") != "hvx"
            or selector.get("revision") != seed["revision"]
            or selector.get("hydride_revision") != HYDRIDE_REVISION
            or seed.get("hydride_revision") != HYDRIDE_REVISION
            or selector.get("legalizer_path") != str(legalizer)
            or selector.get("legalizer_sha256") != sha256_file(legalizer)
            or legalizer.name != "libHVXLegalizer.so"
        ):
            raise ValueError("HVX selector receipt does not identify this prepared legalizer")
        wrapper = checkout / "Hydride/codegen-generator/tools/low-level-codegen/wrappers/hvx_wrappers.ll"
        if wrapper.exists() or wrapper.is_symlink():
            raise ValueError("HVX intrinsic-only request requires the exact original wrapper to be absent")
        hvx_link_contract = {
            "mode": "intrinsics-only",
            "omitted_wrapper": str(wrapper),
            "selector_preparation": str(hvx_selector_receipt),
            "selector_preparation_sha256": sha256_file(hvx_selector_receipt),
        }
    output.mkdir(parents=True)
    preparation = Preparation(output)
    requests = output / "requests"
    requests.mkdir()
    record: dict[str, Any] = {
        "status": "blocked",
        "reason": None,
        "template_request": str(template_request),
        "template_sha256": sha256_file(template_request),
        "revision": MISAAL_REVISION,
        "target": target,
        "selected_cases": cases,
        "cases": {},
        "generator_execution": False,
        "device_execution": False,
        "pattern_cache": "unchanged fresh attempt-owned directory for every complete parent",
    }
    write_json(
        output / "identity.json",
        {
            "template_sha256": sha256_file(template_request),
            "makefile_sha256": makefile_sha256,
            "compiler": str(compiler),
            "compiler_sha256": sha256_file(compiler),
            "catalog_sha256": sha256_file(catalog_path),
            "population_sha256": sha256_file(population_path),
            "shared_inputs": {str(path): sha256_file(path) for path in (header, common, gengen, library, legalizer)},
            "implementation_sha256": sha256_file(Path(__file__)),
        },
    )
    flags = [
        str(compiler),
        "--std=c++17",
        "-fno-rtti",
        "-O3",
        "-g",
        "-DLOG2VLEN=7",
        "-I",
        str(header.parent),
        "-I",
        str(frontend / "tools"),
    ]
    support = output / "support"
    support.mkdir()
    support_objects: list[Path] = []
    support_dependencies: dict[str, str] = {}
    stopped = False
    try:
        for source in (gengen, common):
            obj, dependencies = compile_object(preparation, source, support, flags, checkout, header, timeout_sec)
            support_objects.append(obj)
            support_dependencies.update(dependencies)
    except (OSError, ValueError, RuntimeError) as error:
        stopped = True
        record["reason"] = f"shared original generator support failed: {error}"
        receipts = sorted(preparation.logs.glob("*.result.json"))
        status = json.loads(receipts[-1].read_text()).get("status") if receipts else None
        if status not in (None, "success"):
            record["status"] = status
        if "guard refused" in str(error):
            record["status"] = "resource-stopped"
    record["support_steps"] = [str(path) for path in sorted(preparation.logs.glob("*.result.json"))]
    for case in cases:
        row: dict[str, Any] = {**case, "status": "not-reached", "reason": None, "request": None, "build_steps": []}
        record["cases"][case["id"]] = row
        if stopped:
            row["reason"] = "earlier guarded build stopped preparation"
            write_json(output / f"case-{case['id']}.json", row)
            continue
        previous_receipts = set(preparation.logs.glob("*.result.json"))
        try:
            name = Path(case["source"]).name
            if case["source"] != f"benchmarks/{target}/halide/{name}" or re.fullmatch(r"[A-Za-z0-9_]+", name) is None:
                raise ValueError(f"unexpected original {target} generator source path")
            source = checkout / case["source"] / "src" / f"{name}_generator.cpp"
            if not re.search(rf"HALIDE_REGISTER_GENERATOR\([^,]+,\s*{re.escape(name)}\s*\)", source.read_text()):
                raise ValueError("original generator registration differs from Makefile target")
            attempt = output / case["id"]
            attempt.mkdir()
            binary = attempt / f"{name}_generator"
            obj, dependencies = compile_object(preparation, source, attempt, flags, checkout, header, timeout_sec)
            command = [
                str(compiler),
                str(obj),
                *map(str, support_objects),
                str(library),
                f"-Wl,-rpath,{library.parent}",
                "-o",
                str(binary),
            ]
            preparation.step(f"link-{name}", command, cwd=checkout, timeout=timeout_sec)
            if not binary.is_file() or not binary.stat().st_size or not os.access(binary, os.X_OK):
                raise ValueError("successful compile omitted a native generator executable")
            dependency_hashes = {**support_dependencies, **dependencies}
            request = copy.deepcopy(seed)
            request.update(
                case_id=case["id"],
                source=case["source"],
                configuration=case["configuration"],
                paper_aliases=case["paper_aliases"],
                scope=case["scope"],
                generator=str(binary),
                generator_sha256=sha256_file(binary),
                generator_preparation=str(output),
                template_request=str(template_request),
                compile_dependencies=dependency_hashes,
                legalizer=str(legalizer),
                legalizer_sha256=sha256_file(legalizer),
            )
            request["environment"]["HYDRIDE_BENCHMARK"] = f"{name}_{target}_depth2_misaal"
            request["environment"]["LEGALIZERS_DIR"] = str(legalizer.parent)
            if target == "arm":
                # Original ARM optimization recipe leaves this unset; Rosette.cpp defaults to 2.
                request["environment"].pop("HL_EXPR_DEPTH", None)
                request["environment"].update(HYDRIDE_TARGET="arm", HYDRIDE_DISTRIBUTE_LOOK_AHEAD="1")
            output_name = name
            if target == "hexagon":
                # The generic HVX Makefile leaves all of these unset, unlike x86/ARM.
                for key in (
                    "HL_EXPR_DEPTH",
                    "HL_SYNTH_BW",
                    "HYDRIDE_INITIAL_HASH",
                    "MISAAL_DISABLE_FRONTEND_PATTERNS",
                    "HYDRIDE_DISTRIBUTE_LOOK_AHEAD",
                ):
                    request["environment"].pop(key, None)
                request["environment"].update(
                    HYDRIDE_BENCHMARK=f"{name}_hvx",
                    HYDRIDE_TARGET="hvx",
                    HL_FORCE_HEXAGON_OPT="1",
                    MISAAL_EQ_SAT_ITERS="3",
                )
                request["hvx_link_contract"] = hvx_link_contract
                if name == "fully_connected":
                    request["environment"].update(
                        HYDRIDE_BENCHMARK=f"{name}_hvx_depth2",
                        HL_EXPR_DEPTH="2",
                        HL_SYNTH_BW="16",
                        HYDRIDE_INITIAL_HASH="empty_hash",
                    )
                    request["configuration_variances"] = [
                        {
                            "make_variable": "EXPR_DEPTH",
                            "value": "2",
                            "reason": "Original HVX fully_connected exports empty HL_EXPR_DEPTH without an EXPR_DEPTH "
                            "default; Rosette.cpp reads that as -48. Explicit 2 selects the source's unset default.",
                        }
                    ]
                output_name = f"{name}_hvx128"
            request["generator_command"] = [
                str(binary),
                "-t",
                "0",
                "-o",
                "{output}",
                "-g",
                name,
                *(["output.type=uint8"] if target in ("arm", "hexagon") and name == "fully_connected" else []),
                "-e",
                "static_library,stmt,h,llvm_assembly,assembly",
                "-f",
                output_name,
                f"target={ {'x86': TARGET, 'arm': ARM_TARGET, 'hexagon': HVX_TARGET}[target] }",
            ]
            request["expected_generator_outputs"] = [
                f"{output_name}.{suffix}" for suffix in ("a", "stmt", "h", "ll", "s")
            ]
            request["source_hashes"] = {
                relative: digest
                for relative, digest in seed["source_hashes"].items()
                if not relative.endswith("_generator.cpp")
            }
            request["source_hashes"][str(makefile.relative_to(checkout))] = makefile_sha256
            for path, digest in dependency_hashes.items():
                if Path(path).is_relative_to(checkout):
                    request["source_hashes"][str(Path(path).relative_to(checkout))] = digest
            request["identity_paths"] = list(
                dict.fromkeys(
                    [
                        *seed.get("identity_paths", []),
                        *dependency_hashes,
                        str(library),
                        str(legalizer),
                        str(compiler),
                        str(checkout / "lib"),
                        str(checkout / "targets"),
                        str(checkout / "Hydride/codegen-generator"),
                        str(checkout / "Hydride/code-synthesizer"),
                        str(output / "identity.json"),
                        *([str(hvx_selector_receipt)] if hvx_selector_receipt is not None else []),
                    ]
                )
            )
            pending = attempt / "request.candidate.json"
            write_json(pending, request)
            verified_request(pending)
            published = requests / f"{case['id']}.json"
            write_json(published, request)
            row.update(
                status="prepared",
                request=str(published),
                request_sha256=sha256_file(published),
                generator_sha256=request["generator_sha256"],
                compile_dependencies=dependency_hashes,
            )
        except (OSError, ValueError, RuntimeError) as error:
            row.update(status="blocked", reason=str(error))
            receipts = sorted(set(preparation.logs.glob("*.result.json")) - previous_receipts)
            status = json.loads(receipts[-1].read_text()).get("status") if receipts else None
            if status not in (None, "success"):
                row["status"] = status
            if status not in (None, "success", "failure") or "guard refused" in str(error):
                stopped = True
                record["status"] = "resource-stopped" if "guard refused" in str(error) else status
        row["build_steps"] = [
            str(path) for path in sorted(set(preparation.logs.glob("*.result.json")) - previous_receipts)
        ]
        write_json(output / f"case-{case['id']}.json", row)
    if any(case["status"] == "prepared" for case in record["cases"].values()):
        settings_path = output / "settings.json"
        write_json(
            settings_path,
            {
                "misaal": {
                    "paths": {"requests": str(requests)},
                    "revision": MISAAL_REVISION,
                    "identity_paths": [str(output / "identity.json")],
                }
            },
        )
        record.update(settings=str(settings_path), settings_sha256=sha256_file(settings_path))
    if all(case["status"] == "prepared" for case in record["cases"].values()):
        record.update(status="success", reason="Generators prepared; complete source optimization remains unexecuted")
    elif record["status"] == "blocked":
        record["reason"] = (
            record["reason"] or "one or more generator requests could not be prepared; inspect per-case evidence"
        )
    write_json(output / "preparation.json", record)
    return record


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--template-request", type=Path, required=True)
    parser.add_argument("--case", action="append", default=None)
    parser.add_argument("--compiler", type=Path, default=Path("/usr/bin/clang++"))
    parser.add_argument("--timeout-sec", type=int, default=120)
    args = parser.parse_args()
    with exclusive_job(ROOT / "benchmarks/local/reproduction/stages/.heavy-job.lock"):
        record = prepare_misaal_cases(
            args.output, args.template_request, case_ids=args.case, compiler=args.compiler, timeout_sec=args.timeout_sec
        )
    print(json.dumps({key: record.get(key) for key in ("status", "reason", "settings")}, indent=2))
    return 0 if record["status"] == "success" else 1


if __name__ == "__main__":
    raise SystemExit(main())
