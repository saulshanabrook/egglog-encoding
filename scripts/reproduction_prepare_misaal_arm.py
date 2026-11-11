"""Prepare native ARM legalizer and original ARM generators from MISAAL44ff.

Reuse a verified prepared environment. The selector is generated from MISAAL's
actual ARM semantics and pinned Hydride raw instruction metadata/wrappers. No
optimizer or target program is executed. API uses caller's slot; CLI alone locks.
"""

from __future__ import annotations

import argparse
import ast
import copy
import json
import os
import platform
import re
import shutil
from pathlib import Path
from typing import Any

from scripts.misaal_reproduction import verified_request
from scripts.reproduction_inventory import expected_cases
from scripts.reproduction_misaal_legalizer import simd_mode_replacements
from scripts.reproduction_prepare_misaal import HYDRIDE_REVISION, MISAAL_REVISION, Preparation, sha256_file, write_json
from scripts.reproduction_prepare_misaal_cases import prepare_misaal_cases
from scripts.reproduction_process import exclusive_job

ROOT = Path(__file__).resolve().parents[1]
# SHA-256 of git-show blobs at MISAAL_REVISION / HYDRIDE_REVISION, before our
# isolated pass-mode patch. A new semantic input needs an explicit new pin.
ARM_INPUT_PINS = {
    "lib/sema/ARMSema.py": "150ce6b12702010099defdead388df1198fe0e4740b2811783b11358d9791ee9",
    "Hydride/codegen-generator/tools/low-level-codegen/InstSelectors/arm/RoseARMLegalizerGen.py": (
        "ad7cbe0e8808ff80cdbaf1374c94d28076849c30f28abe387a5d613e5b6ff8ad"
    ),
    "Hydride/codegen-generator/targets/arm/AllSema.py": (
        "e77bec7b3171ced79bea17b95ca3d74c077bc8d791cfcfb54c34b846738d71bb"
    ),
    "Hydride/codegen-generator/targets/arm/ARMSemanticGen.py": (
        "072ad64b2841c7097dffd2e18b799c77b953dbe5294ef8e69b4e9a4961f6455a"
    ),
    "Hydride/codegen-generator/targets/arm/intr.json": (
        "39d6ed68a2067de612b688911578cb10bfd0576a766ae23df36ad7daadce522f"
    ),
    "Hydride/codegen-generator/tools/low-level-codegen/InstSelectors/arm/arm_wrappers.c.ll": (
        "ae8a3379178dbfac1801eacdda0e3ba5ad9ab77794bbe3662f7db13ea7729fa9"
    ),
}


def source_assignment(path: Path, name: str) -> ast.expr:
    """Read exactly one top-level source binding without importing upstream code."""
    values = [
        node.value
        for node in ast.parse(path.read_text()).body
        if isinstance(node, ast.Assign) and any(isinstance(t, ast.Name) and t.id == name for t in node.targets)
    ]
    if len(values) != 1:
        raise ValueError(f"expected one {name} source binding in {path}")
    return values[0]


def inspect_arm_inputs(checkout: Path) -> dict[str, Any]:
    """Require raw metadata and every real wrapper referenced by frontend semantics."""
    for relative, expected in ARM_INPUT_PINS.items():
        if sha256_file(checkout / relative) != expected:
            raise ValueError(f"original pinned ARM input changed: {relative}")
    codegen = checkout / "Hydride/codegen-generator"
    selectors = codegen / "tools/low-level-codegen/InstSelectors"
    frontend = checkout / "lib/sema/ARMSema.py"
    semantics = ast.literal_eval(source_assignment(frontend, "arm_semantics"))
    groups = sorted(semantics)
    if not groups or any(re.fullmatch(r"[A-Za-z_]\w*", group) is None for group in groups):
        raise ValueError("ARM semantics must have nonempty safe selector group names")
    if len({group.capitalize() for group in groups}) != len(groups):
        raise ValueError("ARM selector generation would overwrite a group source")
    raw_file = codegen / "targets/arm/AllSema.py"
    raw_node = source_assignment(raw_file, "AllSema")
    if not isinstance(raw_node, ast.Dict):
        raise ValueError("expected the pinned literal raw instruction metadata dictionary")
    if any(key is None for key in raw_node.keys):
        raise ValueError("raw ARM metadata must not unpack another dictionary")
    raw = {
        ast.literal_eval(key): value
        for key, value in zip(raw_node.keys, raw_node.values, strict=True)
        if key is not None
    }
    instructions = {name for group in semantics.values() for name in group["target_instructions"]}
    missing = instructions - raw.keys()
    if missing:
        raise ValueError(f"ARM raw instruction metadata missing: {sorted(missing)}")
    wrappers = set()
    for name in instructions:
        call = raw[name]
        if not isinstance(call, ast.Call):
            raise ValueError(f"ARM raw metadata is not a constructor expression: {name}")
        widths = [keyword.value for keyword in call.keywords if keyword.arg == "imm_width"]
        if len(widths) != 1:
            raise ValueError(f"ARM raw immediate metadata missing or duplicated: {name}")
        width = ast.literal_eval(widths[0])
        if width is None:
            wrappers.add(f"{name}_wrapper")
        else:
            lo, hi = width
            if not isinstance(lo, int) or not isinstance(hi, int) or not 0 <= lo <= hi <= 1024:
                raise ValueError(f"unexpected ARM immediate range for {name}")
            wrappers.update(f"{name}_wrapper_{immediate}" for immediate in range(lo, hi + 1))
    wrapper_file = selectors / "arm/arm_wrappers.c.ll"
    definitions = set(re.findall(r"^define[^\n@]*@([^\s(]+)\(", wrapper_file.read_text(), re.M))
    if wrappers - definitions:
        raise ValueError(f"ARM native wrapper definitions missing: {sorted(wrappers - definitions)}")
    runtime_wrapper = codegen / "tools/low-level-codegen/wrappers/arm_wrappers.c.ll"
    if sha256_file(runtime_wrapper) != sha256_file(wrapper_file):
        raise ValueError("prepared runtime ARM wrapper differs from original native wrapper")
    inputs = [
        frontend,
        raw_file,
        codegen / "targets/arm/intr.json",
        codegen / "targets/arm/ARMSemanticGen.py",
        selectors / "arm/RoseARMLegalizerGen.py",
        selectors / "common/Legalizer.cpp",
        selectors / "common/Legalizer.h",
        selectors / "common/libpimeval.h",
        wrapper_file,
        runtime_wrapper,
    ]
    return {
        "groups": groups,
        "target_instructions": len(instructions),
        "required_wrappers": len(wrappers),
        "available_wrappers": len(definitions),
        "input_hashes": {str(path): sha256_file(path) for path in inputs},
        "semantics_source": str(frontend),
        "raw_metadata_source": str(raw_file),
        "runtime_wrapper": str(runtime_wrapper),
        "coverage_scope": "instruction and wrapper presence; native compile and lowering gates still required",
    }


def prepare_misaal_arm(
    output: Path,
    template_request: Path,
    *,
    case_ids: list[str] | None = None,
    compiler: Path = Path("/usr/bin/clang++"),
    cmake: Path | None = None,
    boost_include: Path | None = None,
    timeout_sec: int = 1800,
    generator_timeout_sec: int = 120,
) -> dict[str, Any]:
    """Build one ARM selector library, then prepare every selected original generator."""
    output, template_request, compiler = output.resolve(), template_request.resolve(), compiler.resolve()
    if not output.is_relative_to((ROOT / "benchmarks/local/reproduction").resolve()) or output.exists():
        raise ValueError("ARM preparation requires a fresh immutable directory below benchmarks/local/reproduction")
    if (platform.system(), platform.machine()) != ("Darwin", "arm64"):
        raise ValueError("this ARM recipe reuses the native Apple Silicon MISAAL environment")
    seed = verified_request(template_request)
    if seed["revision"] != MISAAL_REVISION or seed.get("hydride_revision") != HYDRIDE_REVISION:
        raise ValueError("ARM preparation requires the pinned MISAAL44ff/Hydride environment")
    if seed["configuration"] != {"target": "x86"}:
        raise ValueError("template must be the verified original x86 environment request")
    inventory = expected_cases(
        json.loads((ROOT / "benchmarks/catalog.json").read_text()),
        json.loads((ROOT / "benchmarks/reproduction/population.json").read_text()),
    )
    cases = [case for case in inventory if case["family"] == "misaal" and case["configuration"] == {"target": "arm"}]
    if case_ids is not None:
        if len(case_ids) != len(set(case_ids)) or set(case_ids) - {case["id"] for case in cases}:
            raise ValueError("ARM selectors must be unique inventoried case IDs")
        cases = [case for case in cases if case["id"] in case_ids]
    if not cases or min(timeout_sec, generator_timeout_sec) <= 0:
        raise ValueError("ARM cases and positive time limits are required")
    cmake_path = cmake or shutil.which("cmake")
    if cmake_path is None:
        raise ValueError("a prepared CMake executable is required")
    cmake = Path(cmake_path).resolve()
    if not all(os.access(path, os.X_OK) for path in (compiler, cmake)):
        raise ValueError("native compiler and CMake executables are required")
    output.mkdir(parents=True)
    preparation = Preparation(output)
    record: dict[str, Any] = {
        "status": "blocked",
        "reason": None,
        "revision": MISAAL_REVISION,
        "hydride_revision": HYDRIDE_REVISION,
        "template_request": str(template_request),
        "template_sha256": sha256_file(template_request),
        "generator_execution": False,
        "device_execution": False,
        "cases": {case["id"]: {**case, "status": "not-reached", "request": None} for case in cases},
    }
    try:
        checkout = Path(seed["checkout"]).resolve()
        codegen = checkout / "Hydride/codegen-generator"
        common = codegen / "tools/low-level-codegen/InstSelectors/common"
        inputs = inspect_arm_inputs(checkout)
        for key in ("library", "legalizer"):
            if sha256_file(Path(seed[key])) != seed[f"{key}_sha256"]:
                raise ValueError(f"prepared {key} differs from its request identity")
        boost_include = (boost_include or Path(seed["preparation"]) / "boost_1_81_0").resolve()
        boost_version = boost_include / "boost/version.hpp"
        if not re.search(r"#define\s+BOOST_VERSION\s+108100\b", boost_version.read_text()):
            raise ValueError("ARM legalizer requires the prepared Boost1.81 headers")
        llvm = Path(seed["llvm_as"]).resolve().parent.parent
        for path in (llvm / "lib/cmake/llvm/LLVMConfig.cmake", llvm / "include/llvm/IR/Function.h"):
            inputs["input_hashes"][str(path)] = sha256_file(path)
        for path in (compiler, cmake, boost_version, boost_include / "boost/multiprecision/cpp_int.hpp"):
            inputs["input_hashes"][str(path)] = sha256_file(path)
        inputs["input_hashes"][str(Path(__file__))] = sha256_file(Path(__file__))
        record["inputs"] = inputs
        write_json(output / "inputs.json", inputs)
        preparation.step(
            "verify-arm-wrappers",
            [seed["llvm_as"], inputs["runtime_wrapper"], "-o", os.devnull],
            timeout=min(timeout_sec, 120),
        )
        source = output / "sources/arm"
        source.mkdir(parents=True)
        original = codegen / "tools/low-level-codegen/InstSelectors/arm/RoseARMLegalizerGen.py"
        selector = source / original.name
        selector.write_bytes(original.read_bytes())
        replacements = simd_mode_replacements(selector.read_text(), "arm")
        if replacements:
            preparation.patch(selector, replacements, "arm-simd-pass-mode")
        generated = output / "generated"
        generated.mkdir()
        driver = output / "generate_arm.py"
        driver.write_text(
            "from RoseARMLegalizerGen import RoseInstSelectorGenerator\n"
            "from sema.ARMSema import arm_semantics\n"
            "RoseInstSelectorGenerator(arm_semantics).generateFileWithInstSelector()\n"
        )
        environment = {
            **seed["environment"],
            "HYDRIDE_ROOT": str(checkout / "Hydride"),
            "PYTHONDONTWRITEBYTECODE": "1",
            "PYTHONPATH": os.pathsep.join(
                [str(source), str(codegen / "targets/arm"), seed["environment"]["PYTHONPATH"]]
            ),
        }
        preparation.step(
            "generate-arm-selectors",
            ["/usr/bin/env", *[f"{key}={value}" for key, value in environment.items()], seed["python"], str(driver)],
            cwd=generated,
            timeout=min(timeout_sec, 600),
        )
        expected = {
            "ARMLegalizer.cpp",
            "ARMLegalizer.h",
            *[f"{group.capitalize()}Selector.cpp" for group in inputs["groups"]],
        }
        actual = {path.name for path in generated.iterdir() if path.suffix in (".h", ".cpp")}
        if actual != expected or any(not (generated / name).stat().st_size for name in expected):
            raise ValueError("ARM generation omitted or added unexpected selector sources")
        if simd_mode_replacements((generated / "ARMLegalizer.cpp").read_text(), "arm"):
            raise ValueError("generated ARM pass did not retain the SIMD mode repair")
        for group in inputs["groups"]:
            if (
                f"bool ARMLegalizer::legalize_{group}("
                not in (generated / f"{group.capitalize()}Selector.cpp").read_text()
            ):
                raise ValueError(f"generated ARM selector omitted its original group: {group}")
        record["generated_sources"] = {
            str(generated / name): sha256_file(generated / name) for name in sorted(expected)
        }
        build_source = output / "cmake"
        build_source.mkdir()
        cmake_file = build_source / "CMakeLists.txt"
        cpp_sources = [generated / name for name in sorted(expected) if name.endswith(".cpp")]
        # Reject CMake interpolation in external paths, rather than permitting executable build text.
        build_paths = [*cpp_sources, generated, common, boost_include]
        if any(any(character in str(path) for character in ('"', "$", ";", "\n", "\\")) for path in build_paths):
            raise ValueError("unsupported special character in native ARM build path")
        source_lines = "\n".join(f'  "{path}"' for path in [*cpp_sources, common / "Legalizer.cpp"])
        cmake_file.write_text(
            "cmake_minimum_required(VERSION 3.16)\nproject(MisaalARM LANGUAGES C CXX)\n"
            "find_package(LLVM 12 REQUIRED CONFIG)\nset(CMAKE_CXX_STANDARD 14)\n"
            f"add_library(ARMLegalizer SHARED\n{source_lines}\n)\n"
            "target_include_directories(ARMLegalizer PRIVATE ${LLVM_INCLUDE_DIRS}\n"
            f'  "{common}" "{generated}" "{boost_include}")\n'
            "if(NOT LLVM_ENABLE_RTTI)\n  target_compile_options(ARMLegalizer PRIVATE -fno-rtti)\nendif()\n"
            'target_link_options(ARMLegalizer PRIVATE "-undefined" "dynamic_lookup")\n'
            'set_target_properties(ARMLegalizer PROPERTIES SUFFIX ".so")\n'
        )
        record["prepared_sources"] = {str(path): sha256_file(path) for path in (selector, driver, cmake_file)}
        build = output / "legalizer-build"
        preparation.step(
            "configure-arm-legalizer",
            [
                str(cmake),
                "-S",
                str(build_source),
                "-B",
                str(build),
                "-DCMAKE_BUILD_TYPE=Release",
                f"-DCMAKE_CXX_COMPILER={compiler}",
                f"-DLLVM_DIR={llvm}/lib/cmake/llvm",
            ],
            timeout=min(timeout_sec, 120),
        )
        preparation.step(
            "build-arm-legalizer",
            [str(cmake), "--build", str(build), "--target", "ARMLegalizer", "--parallel", "1"],
            timeout=timeout_sec,
        )
        legalizer = build / "libARMLegalizer.so"
        if not legalizer.is_file() or not legalizer.stat().st_size:
            raise ValueError("native build omitted the ARM legalizer library")
        record.update(legalizer=str(legalizer), legalizer_sha256=sha256_file(legalizer))
        prepared_seed = copy.deepcopy(seed)
        prepared_seed["source_hashes"].update(
            {
                str(Path(path).relative_to(checkout)): digest
                for path, digest in inputs["input_hashes"].items()
                if Path(path).is_relative_to(checkout)
            }
        )
        prepared_seed["identity_paths"] = list(
            dict.fromkeys(
                [
                    *seed.get("identity_paths", []),
                    str(output / "inputs.json"),
                    str(source),
                    str(generated),
                    str(driver),
                    str(cmake_file),
                    str(legalizer),
                    str(codegen / "targets/arm"),
                    str(boost_include),
                ]
            )
        )
        augmented = output / "environment-template.json"
        write_json(augmented, prepared_seed)
        result = prepare_misaal_cases(
            output / "generators",
            augmented,
            case_ids=[case["id"] for case in cases],
            compiler=compiler,
            timeout_sec=generator_timeout_sec,
            target="arm",
            legalizer=legalizer,
        )
        record.update(status=result["status"], reason=result["reason"], cases=result["cases"])
        if "settings" in result:
            record.update(settings=result["settings"], settings_sha256=result["settings_sha256"])
    except (OSError, ValueError, RuntimeError, KeyError, SyntaxError, TypeError) as error:
        record["reason"] = str(error)
        receipts = sorted(preparation.logs.glob("*.result.json"))
        status = json.loads(receipts[-1].read_text()).get("status") if receipts else None
        if status not in (None, "success"):
            record["status"] = status
        if "guard refused" in str(error):
            record["status"] = "resource-stopped"
    record["steps"] = [str(path) for path in sorted(preparation.logs.glob("*.result.json"))]
    for row in record["cases"].values():
        if row["status"] == "not-reached":
            row["reason"] = record["reason"]
    write_json(output / "preparation.json", record)
    return record


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--template-request", type=Path, required=True)
    parser.add_argument("--case", action="append", default=None)
    parser.add_argument("--compiler", type=Path, default=Path("/usr/bin/clang++"))
    parser.add_argument("--cmake", type=Path)
    parser.add_argument("--boost-include", type=Path)
    parser.add_argument("--timeout-sec", type=int, default=1800)
    parser.add_argument("--generator-timeout-sec", type=int, default=120)
    args = parser.parse_args()
    with exclusive_job(ROOT / "benchmarks/local/reproduction/stages/.heavy-job.lock"):
        result = prepare_misaal_arm(
            args.output,
            args.template_request,
            case_ids=args.case,
            compiler=args.compiler,
            cmake=args.cmake,
            boost_include=args.boost_include,
            timeout_sec=args.timeout_sec,
            generator_timeout_sec=args.generator_timeout_sec,
        )
    print(json.dumps({key: result.get(key) for key in ("status", "reason", "settings")}, indent=2))
    return 0 if result["status"] == "success" else 1


if __name__ == "__main__":
    raise SystemExit(main())
