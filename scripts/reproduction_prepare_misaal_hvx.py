"""Prepare an intrinsic-only HVX selector and original host generator requests.

No target program executes. The in-process API uses its caller's guarded job
slot; only the CLI locks. All repairs apply to a private generator copy.
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
from scripts.reproduction_misaal_hvx_lowering import (
    CONCAT_WIDTHS,
    SOURCE_LOWERINGS,
    hvx_common_replacements,
    hvx_generator_replacements,
    source_lowering_cpp,
    validate_concat_semantics,
    validate_source_lowerings,
)
from scripts.reproduction_prepare_misaal import HYDRIDE_REVISION, MISAAL_REVISION, Preparation, sha256_file, write_json
from scripts.reproduction_prepare_misaal_arm import source_assignment
from scripts.reproduction_prepare_misaal_cases import prepare_misaal_cases
from scripts.reproduction_process import exclusive_job

ROOT = Path(__file__).resolve().parents[1]
# Original 44ff/beb inputs newly consumed by HVX, outside the x86 request's file pins.
HVX_SOURCE_SHA256 = {
    "lib/sema/hex_swizzles.py": "e81a883661f83667f65e296decc7f0969d4046279facb0318afc8812771ed375",
    "Hydride/codegen-generator/tools/low-level-codegen/InstSelectors/common/Legalizer.cpp": (
        "cf595e9c1ff60c46234ba327a8ea10738b82e934b0a42f46c18fc5ab1ce79860"
    ),
    "lib/sema/hexsemantics_new.py": "eef4d1fcb30db190dc1947a55040203c33aff16e7262d52b36e26fe1cc0c0b75",
    "Hydride/codegen-generator/tools/low-level-codegen/InstSelectors/hexagon/RoseHexLegalizerGen.py": (
        "659d800eef85fa85877e8181d0b75e804b144a829245aed28604a5a1b8034494"
    ),
}


def inspect_hvx_inputs(checkout: Path, llvm: Path) -> dict[str, Any]:
    """Bind actual frontend semantics and require every ordinary LLVM intrinsic."""
    for relative, expected in HVX_SOURCE_SHA256.items():
        if sha256_file(checkout / relative) != expected:
            raise ValueError(f"pinned HVX source changed: {relative}")
    codegen = checkout / "Hydride/codegen-generator"
    low = codegen / "tools/low-level-codegen"
    frontend = checkout / "lib/sema/hexsemantics_new.py"
    semantics = ast.literal_eval(source_assignment(frontend, "semantics"))
    validate_concat_semantics(semantics)
    swizzles = ast.literal_eval(source_assignment(checkout / "lib/sema/hex_swizzles.py", "hvx_swizzles"))
    validate_source_lowerings(semantics, swizzles)
    targets = [name for group in semantics.values() for name in group["target_instructions"]]
    if len(targets) != len(set(targets)):
        raise ValueError("HVX frontend contains duplicate concrete instruction names")
    if any(re.fullmatch(r"[A-Za-z_]\w*", name) is None for name in targets):
        raise ValueError("HVX instruction names must be safe C++ identifiers")
    excluded = set(CONCAT_WIDTHS) | SOURCE_LOWERINGS.keys()
    ordinary = sorted(
        name for group, value in semantics.items() if group not in excluded for name in value["target_instructions"]
    )
    constant_bits = []
    for group in semantics.values():
        for instruction in group["target_instructions"].values():
            for index, argument in enumerate(instruction["args"]):
                if "bv" in argument and instruction["arg_permute_map"][index] == -1:
                    match = re.fullmatch(r"\(bv #(x[0-9a-fA-F]+|b[01]+) (\d+)\)", argument)
                    if match is None:
                        raise ValueError("HVX selector constant differs from pinned bitvector syntax")
                    significant = int("0" + match[1], 0).bit_length()
                    if significant > min(int(match[2]), 512):
                        raise ValueError("HVX selector constant exceeds source width or common int512_t matcher")
                    constant_bits.append(significant)
    header = llvm / "include/llvm/IR/IntrinsicsHexagon.h"
    available = set(re.findall(r"\bhexagon_\w+\b", header.read_text()))
    if set(ordinary) - available:
        raise ValueError(f"HVX instructions absent from LLVM12: {sorted(set(ordinary) - available)}")
    wrapper = low / "wrappers/hvx_wrappers.ll"
    if wrapper.exists() or wrapper.is_symlink():
        raise ValueError("intrinsic-only recipe requires the original HVX wrapper to be absent")
    inputs = [
        frontend,
        checkout / "lib/sema/hex_swizzles.py",
        low / "InstSelectors/hexagon/RoseHexLegalizerGen.py",
        low / "InstSelectors/common/Legalizer.cpp",
        low / "InstSelectors/common/Legalizer.h",
        low / "InstSelectors/common/libpimeval.h",
        codegen / "tools/rosette-lifter/RosetteLifter.py",
        codegen / "codegen/llvm/RoseLLVMCodeGen.py",
        low / "RoseLowLevelCodeGen.py",
        checkout / "frontends/halide/src/misaal.cpp",
        checkout / "frontends/halide/src/Rosette.cpp",
        header,
        llvm / "lib/cmake/llvm/LLVMConfig.cmake",
    ]
    return {
        "groups": len(semantics),
        "target_instructions": len(targets),
        "ordinary_intrinsics": ordinary,
        "concat_input_widths": CONCAT_WIDTHS,
        "matched_constant_max_significant_bits": max(constant_bits, default=0),
        "omitted_wrapper": str(wrapper),
        "input_hashes": {str(path): sha256_file(path) for path in inputs},
    }


def prepare_misaal_hvx(
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
    """Build the selected selector, seal its identity, then compile host generators."""
    output, template_request, compiler = output.resolve(), template_request.resolve(), compiler.resolve()
    if output.exists() or not output.is_relative_to((ROOT / "benchmarks/local/reproduction").resolve()):
        raise ValueError("HVX preparation requires a fresh immutable directory below benchmarks/local/reproduction")
    if (platform.system(), platform.machine()) != ("Darwin", "arm64"):
        raise ValueError("this recipe reuses the native Apple Silicon MISAAL environment")
    seed = verified_request(template_request)
    if seed["revision"] != MISAAL_REVISION or seed.get("hydride_revision") != HYDRIDE_REVISION:
        raise ValueError("HVX preparation requires the pinned MISAAL44ff/Hydride environment")
    if seed["configuration"] != {"target": "x86"}:
        raise ValueError("template must be the verified original x86 environment request")
    inventory = expected_cases(
        json.loads((ROOT / "benchmarks/catalog.json").read_text()),
        json.loads((ROOT / "benchmarks/reproduction/population.json").read_text()),
    )
    cases = [
        case for case in inventory if case["family"] == "misaal" and case["configuration"] == {"target": "hexagon"}
    ]
    if case_ids is not None:
        if len(case_ids) != len(set(case_ids)) or set(case_ids) - {case["id"] for case in cases}:
            raise ValueError("HVX selectors must be unique inventoried case IDs")
        cases = [case for case in cases if case["id"] in case_ids]
    if not cases or min(timeout_sec, generator_timeout_sec) <= 0:
        raise ValueError("HVX cases and positive time limits are required")
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
        llvm = Path(seed["llvm_as"]).resolve().parent.parent
        inputs = inspect_hvx_inputs(checkout, llvm)
        for key in ("library", "legalizer"):
            if sha256_file(Path(seed[key])) != seed[f"{key}_sha256"]:
                raise ValueError(f"prepared {key} differs from its request identity")
        boost_include = (boost_include or Path(seed["preparation"]) / "boost_1_81_0").resolve()
        boost_version = boost_include / "boost/version.hpp"
        if not re.search(r"#define\s+BOOST_VERSION\s+108100\b", boost_version.read_text()):
            raise ValueError("HVX legalizer requires the prepared Boost1.81 headers")
        from scripts import reproduction_misaal_hvx_lowering

        for path in (
            compiler,
            cmake,
            boost_version,
            boost_include / "boost/multiprecision/cpp_int.hpp",
            Path(__file__),
            Path(reproduction_misaal_hvx_lowering.__file__),
        ):
            inputs["input_hashes"][str(path)] = sha256_file(path)
        record["inputs"] = inputs
        write_json(output / "inputs.json", inputs)
        source = output / "sources/hvx"
        source.mkdir(parents=True)
        private_common = output / "sources/common"
        private_common.mkdir()
        for name in ("Legalizer.cpp", "Legalizer.h", "libpimeval.h"):
            shutil.copy2(common / name, private_common / name)
        common_cpp = private_common / "Legalizer.cpp"
        preparation.patch(common_cpp, hvx_common_replacements(common_cpp.read_text()), "hvx-complete-permutations")
        selector = source / "RoseHexLegalizerGen.py"
        selector.write_bytes((codegen / "tools/low-level-codegen/InstSelectors/hexagon" / selector.name).read_bytes())
        preparation.patch(selector, hvx_generator_replacements(selector.read_text()), "hvx-source-concat-selector")
        generated = output / "generated"
        generated.mkdir()
        driver = output / "generate_hvx.py"
        driver.write_text(
            "from RoseHexLegalizerGen import RoseInstSelectorGenerator\n"
            "from sema.hexsemantics_new import semantics\n"
            f"excluded = {tuple(CONCAT_WIDTHS) + tuple(SOURCE_LOWERINGS)!r}\n"
            "RoseInstSelectorGenerator({k: v for k, v in semantics.items() if k not in excluded})"
            ".generateFileWithInstSelector()\n"
        )
        environment = {
            **seed["environment"],
            "HYDRIDE_ROOT": str(checkout / "Hydride"),
            "PYTHONDONTWRITEBYTECODE": "1",
            "PYTHONPATH": os.pathsep.join([str(source), seed["environment"]["PYTHONPATH"]]),
        }
        preparation.step(
            "generate-hvx-selector",
            ["/usr/bin/env", *[f"{key}={value}" for key, value in environment.items()], seed["python"], str(driver)],
            cwd=generated,
            timeout=min(timeout_sec, 600),
        )
        cpp = generated / "HexLegalizer.cpp"
        text = cpp.read_text()
        if {path.name for path in generated.iterdir() if path.suffix in (".h", ".cpp")} != {cpp.name}:
            raise ValueError("HVX generation added unexpected selector sources")
        actual = set(re.findall(r"Intrinsic::(hexagon_\w+)", text))
        if actual != set(inputs["ordinary_intrinsics"]):
            raise ValueError("generated HVX selector changed ordinary intrinsic coverage")
        if (
            source_lowering_cpp() not in text
            or "L->bitsimd = false;" not in text
            or "verifyFunction(F, &errs())" not in text
        ):
            raise ValueError("generated HVX selector lost source lowering, SIMD mode or pre-ADCE verification")
        from scripts.reproduction_misaal_hvx_lowering import concat_lowering_cpp

        if concat_lowering_cpp() not in text or not re.search(r"return false;\s*}\s*};", text):
            raise ValueError("generated HVX selector lost its concat lowering or final false return")
        build_source = output / "cmake"
        build_source.mkdir()
        cmake_file = build_source / "CMakeLists.txt"
        paths = [cpp, private_common, boost_include]
        if any(any(character in str(path) for character in ('"', "$", ";", "\n", "\\")) for path in paths):
            raise ValueError("unsupported special character in native HVX build path")
        cmake_file.write_text(
            "cmake_minimum_required(VERSION 3.16)\nproject(MisaalHVX LANGUAGES C CXX)\n"
            "find_package(LLVM 12 REQUIRED CONFIG)\nset(CMAKE_CXX_STANDARD 14)\n"
            f'add_library(HVXLegalizer SHARED "{cpp}" "{private_common}/Legalizer.cpp")\n'
            "target_include_directories(HVXLegalizer PRIVATE ${LLVM_INCLUDE_DIRS} "
            f'"{private_common}" "{boost_include}")\n'
            "if(NOT LLVM_ENABLE_RTTI)\n target_compile_options(HVXLegalizer PRIVATE -fno-rtti)\nendif()\n"
            'target_link_options(HVXLegalizer PRIVATE "-undefined" "dynamic_lookup")\n'
            'set_target_properties(HVXLegalizer PROPERTIES SUFFIX ".so")\n'
        )
        build = output / "legalizer-build"
        preparation.step(
            "configure-hvx-legalizer",
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
            "build-hvx-legalizer",
            [str(cmake), "--build", str(build), "--target", "HVXLegalizer", "--parallel", "1"],
            timeout=timeout_sec,
        )
        legalizer = build / "libHVXLegalizer.so"
        if not legalizer.is_file() or not legalizer.stat().st_size:
            raise ValueError("native build omitted the HVX legalizer library")
        receipt = output / "selector-preparation.json"
        write_json(
            receipt,
            {
                "status": "success",
                "target": "hvx",
                "revision": MISAAL_REVISION,
                "hydride_revision": HYDRIDE_REVISION,
                "legalizer_path": str(legalizer),
                "legalizer_sha256": sha256_file(legalizer),
                "input_hashes": inputs["input_hashes"],
                "generated_sources": {str(cpp): sha256_file(cpp)},
                "prepared_sources": {
                    str(path): sha256_file(path)
                    for path in (selector, driver, cmake_file, *sorted(private_common.iterdir()))
                },
                "lowering_contract": {
                    "ordinary_intrinsics": inputs["ordinary_intrinsics"],
                    "source_lowering_contract": "active-formals-portable-v1",
                    "source_groups": SOURCE_LOWERINGS,
                    "permutations": "complete-unique-and-type-checked",
                    "verification": "inside-selector-before-ADCE",
                    "concat_input_widths": CONCAT_WIDTHS,
                    "concat_result_width": 32,
                    "simd_mode": True,
                    "native_lowering_validation": "pending actual canary",
                },
                "steps": [str(path) for path in sorted(preparation.logs.glob("*.result.json"))],
            },
        )
        record.update(selector_preparation=str(receipt), selector_preparation_sha256=sha256_file(receipt))
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
                    str(private_common),
                    str(generated),
                    str(driver),
                    str(cmake_file),
                    str(legalizer),
                    str(receipt),
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
            target="hexagon",
            legalizer=legalizer,
            hvx_selector_receipt=receipt,
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
        result = prepare_misaal_hvx(
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
