"""Source-bound MISAAL Egglog export frontend; no generator is executed here.

The API uses its caller's job slot. The CLI takes the existing shared lock.
Only a fresh copied frontend is patched/built; retained prerequisites stay intact.
"""

from __future__ import annotations

import argparse
import json
import os
import platform
import shutil
from pathlib import Path
from typing import Any

from process_guard import GROUP_LIMIT_BYTES
from scripts.reproduction_prepare_misaal import LLVM12, MISAAL_REVISION
from scripts.reproduction_process import exclusive_job
from scripts.source_tools import Preparation, sha256_file, write_json

ROOT = Path(__file__).resolve().parents[1]
EXPORT_POLICY = "egglog-only-v1"
EXPORT_SCHEMA = "misaal-export-v1"
GUARD_SOURCES = ("process_guard.py", "scripts/reproduction_process.py")
SOURCE_SHA256 = {
    "frontends/halide/src/Module.cpp": "f754bb2f100744373276e3223200e3d76a67f9cecf9225f2afadcc6df11129a9",
    "frontends/halide/src/CodeGen_LLVM.cpp": "d74788b6e6ad003503918ea42841efffb8d0fd8d4db32dee9aa51096eb80d453",
    "frontends/halide/src/CodeGen_LLVM.h": "b41269f0ce47e1bdfd9d9fb37c672dd3d7f305afd4323058050a824a3334f1ab",
    "frontends/halide/src/CodeGen_Hexagon.cpp": "1f77a013e412dd3922d0c2c4242f71db29628df24aea5be4e56f77cec99857bf",
    "frontends/halide/src/HexagonOffload.cpp": "0056a25a8e0df8911360f40978e3724c899c90aec9a139726672b17d35914ec9",
    "frontends/halide/src/misaal.cpp": "8e39a64c506e90a531d11f56bb3321b899ecb4da057988d28a3d786bfcc4e894",
    "frontends/halide/src/Rosette.cpp": "ed4ebbed55882df1396ef233c0f2394cc1f08461341ae217344c6c3002998911",
    "lib/compiler/HydrideCompiler.py": "d1ff08a7349e8956da3f33d17e18ac149f03ac51064fcfa0b6ad40205cb04368",
    "lib/compiler/EggLogCompiler.py": "87a96401b12291e184cf7eb65efe1f481bccd6faac514c56aef0502f1cc7c479",
    "lib/compiler/Compiler.py": "d901a610725def31cfe6f41ef0d44f23d9e0409b78b7c22c80666140b783d7da",
    "lib/patterns/PatternUtils.py": "e89b1a4c9dda901f2416100dbc6b5e47554264e00eb755c52c669f48b54eb8d5",
    "lib/utils/DSLInstructionUtils.py": "e385eaa17a81bbcb8106ad33cbbe1ac2ed4307879b0f366f3b72219744b43bdb",
    "targets/halide/axioms.egg": "5c710032858d34440ad94979c8788bb96967d1d71e93e55f3ea2bad2184ab4c1",
}
EXPORT_SOURCE_SHA256 = {
    **SOURCE_SHA256,
    "frontends/halide/src/Module.cpp": "7a4cef8dc3ce9d56f418e6bfe609e8975e1850d7661642a883a2497dcb26b517",
    "frontends/halide/src/CodeGen_LLVM.cpp": "2fcddb595e52f3cfd2e1280389c804eda49b7576a6b83eb7052d643a8af0dc7b",
    "frontends/halide/src/CodeGen_Hexagon.cpp": "39eb6b45e0778dd301f849a05a7df06c661c5e567544b3a912e1f9c93884d861",
    "frontends/halide/src/misaal.cpp": "96d0fa88a670e578696bd74a99a1eb77e5bd7505d61e34fa38d2ced187b0a85f",
    "lib/compiler/EggLogCompiler.py": "5dc5c1be8df36646f7c7cbb63b9758eb217604bfdd98b4baeb4ba15ec3952b83",
    "lib/patterns/PatternUtils.py": "0ca26f6a358e5fcc4819e586aba5699b4ee02120bf19ea3a776d7399fd68dcde",
    "lib/utils/DSLInstructionUtils.py": "82ecf858a2aaa68a9885f21d01c80887bd6e2c56ef9b7f618aad2f7af193a477",
    "targets/halide/axioms.egg": "e9d5c2f49af2c58df6e15f84372c79c0a1c9b92f1f0edbd285d5b92941d77e5f",
    "frontends/halide/src/MisaalExport.h": "d9163d565ae657cfad0679ab02c1d6fae1b2b8d79aff96358d6705f11061111f",
}

PATCHES = tuple(
    ROOT / "benchmarks/reproduction/patches" / name
    for name in (
        "misaal-02-export.diff",
        "misaal-03-patterns.diff",
        "misaal-04-capture.diff",
    )
)
HEADER_PATH = "frontends/halide/src/MisaalExport.h"


def verified_export_template(path: Path) -> dict[str, Any]:
    """Verify freshly acquired source/tool identities, without historical native outputs."""
    request: dict[str, Any] = json.loads(path.read_text())
    if request["revision"] != MISAAL_REVISION:
        raise ValueError("source request revision differs from the recipe")
    checkout = Path(request["checkout"])
    for relative, digest in request["source_hashes"].items():
        if sha256_file(checkout / relative) != digest:
            raise ValueError(f"prepared source changed: {relative}")
    for key in ("backend", "python"):
        if sha256_file(Path(request[key])) != request[key + "_sha256"]:
            raise ValueError(f"prepared {key} changed")
    return request


def prepare_export_frontend(output: Path, template_request: Path, *, timeout_sec: int = 1800) -> dict[str, Any]:
    """Build the export library once, reusing verified retained toolchain inputs."""
    output, template_request = output.resolve(), template_request.resolve()
    if not output.is_relative_to((ROOT / "benchmarks/local/reproduction").resolve()) or output.exists():
        raise ValueError("export preparation requires a fresh durable attempt directory")
    if (platform.system(), platform.machine()) != ("Darwin", "arm64") or timeout_sec <= 0:
        raise ValueError("export build requires the prepared Apple Silicon toolchain and positive timeout")
    if any(key.startswith("MISAAL_EXPORT_") for key in os.environ):
        raise ValueError("export preparation refuses ambient export activation")
    seed = verified_export_template(template_request)
    if seed["revision"] != MISAAL_REVISION or "egglog_export" in seed:
        raise ValueError("export preparation requires a retained original MISAAL44ff request")
    source = Path(seed["checkout"]).resolve()
    if any(sha256_file(source / name) != digest for name, digest in SOURCE_SHA256.items()):
        raise ValueError("MISAAL export source identity changed")
    frontend = source / "frontends/halide"
    inputs = {str(p.relative_to(frontend)): sha256_file(p) for p in sorted(frontend.rglob("*")) if p.is_file()}
    tools = [Path("/usr/bin/clang"), Path("/usr/bin/clang++"), LLVM12 / "bin/llvm-config"]
    if any(not os.access(tool, os.X_OK) for tool in tools):
        raise ValueError("missing retained native frontend build tool")
    output.mkdir(parents=True)
    preparation = Preparation(output)
    checkout = output / "sources/MISAAL"
    shutil.copytree(source, checkout, ignore=shutil.ignore_patterns(".git", "__pycache__"))
    for patch in PATCHES:
        preparation.apply_patch(checkout, patch)
    after = {
        name: sha256_file(checkout / name)
        for name, digest in EXPORT_SOURCE_SHA256.items()
        if digest != SOURCE_SHA256.get(name)
    }
    if any(sha256_file(checkout / name) != digest for name, digest in EXPORT_SOURCE_SHA256.items()):
        raise ValueError("MISAAL prepared export source identity changed")
    build = output / "halide-build"
    cmake = ["uv", "tool", "run", "--from", "cmake==3.31.10", "cmake"]
    commands = {
        "export-halide-configure": [
            *cmake,
            "-S",
            str(checkout / "frontends/halide"),
            "-B",
            str(build),
            "-G",
            "Unix Makefiles",
            "-DCMAKE_BUILD_TYPE=Release",
            "-DCMAKE_C_COMPILER=/usr/bin/clang",
            "-DCMAKE_CXX_COMPILER=/usr/bin/clang++",
            f"-DLLVM_DIR={LLVM12}/lib/cmake/llvm",
            f"-DClang_DIR={LLVM12}/lib/cmake/clang",
            "-DHalide_SHARED_LLVM=ON",
            "-DTARGET_WEBASSEMBLY=OFF",
            "-DTARGET_NVPTX=OFF",
            "-DWITH_TESTS=OFF",
            "-DWITH_PYTHON_BINDINGS=OFF",
            "-DWITH_TUTORIALS=OFF",
            "-DWITH_DOCS=OFF",
            "-DWITH_UTILS=OFF",
        ],
        "export-halide-build": [*cmake, "--build", str(build), "--target", "Halide", "--parallel", "2"],
    }
    write_json(
        output / "identity.json",
        {
            "schema": "misaal-export-frontend-v1",
            "policy": EXPORT_POLICY,
            "revision": MISAAL_REVISION,
            "template_request": str(template_request),
            "template_sha256": sha256_file(template_request),
            "implementation_sha256": sha256_file(Path(__file__)),
            "patches": {patch.name: sha256_file(patch) for patch in PATCHES},
            "source_before": SOURCE_SHA256,
            "source_after": after,
            "frontend_inputs": inputs,
            "commands": commands,
            "guard_sources": {name: sha256_file(ROOT / name) for name in GUARD_SOURCES},
            "tools": {str(tool): sha256_file(tool) for tool in tools},
            "reused_backend": {"path": seed["backend"], "sha256": seed["backend_sha256"]},
            "reused_python": {"path": seed["python"], "sha256": seed["python_sha256"]},
        },
    )
    record: dict[str, Any] = {
        "schema": "misaal-export-frontend-v1",
        "policy": EXPORT_POLICY,
        "status": "failed",
        "checkout": str(checkout),
        "build": str(build),
        "source_after": after,
        "identity_sha256": sha256_file(output / "identity.json"),
        "generator_execution": False,
        "backend_build": False,
        "selector_build": False,
    }
    try:
        for name, command in commands.items():
            preparation.step(name, command, timeout=timeout_sec)
        library = build / "src/libHalide.dylib"
        header = build / "include/Halide.h"
        if any(not path.is_file() or not path.stat().st_size for path in (library, header)):
            raise ValueError("successful export build omitted library or public header")
        if any(sha256_file(checkout / relative) != digest for relative, digest in after.items()):
            raise ValueError("export source changed during build")
        record.update(
            status="success",
            library=str(library),
            library_sha256=sha256_file(library),
            header=str(header),
            header_sha256=sha256_file(header),
        )
    except (OSError, ValueError, RuntimeError) as error:
        record["reason"] = str(error)
        failures = [json.loads(path.read_text()) for path in sorted(preparation.logs.glob("*.result.json"))]
        if failures and failures[-1].get("status") in {"resource-stopped", "memory-limit", "cancelled", "interrupted"}:
            record["status"] = failures[-1]["status"]
        elif "guard refused" in str(error):
            record["status"] = "resource-stopped"
    record["evidence"] = {str(p.relative_to(output)): sha256_file(p) for p in sorted(preparation.logs.iterdir())}
    write_json(output / "frontend.json", record)
    return record


def verified_frontend(receipt: Path) -> dict[str, Any]:
    """Verify the exact patched source and guarded build producing this library."""
    if receipt.is_symlink() or receipt.name != "frontend.json":
        raise ValueError("export frontend requires its original frontend.json receipt")
    receipt = receipt.resolve()
    directory = receipt.parent
    record: dict[str, Any] = json.loads(receipt.read_text())
    identity = json.loads((directory / "identity.json").read_text())
    checkout = directory / "sources/MISAAL"
    build = directory / "halide-build"
    if (
        record.get("schema") != "misaal-export-frontend-v1"
        or record.get("policy") != EXPORT_POLICY
        or record.get("status") != "success"
        or record.get("checkout") != str(checkout)
        or record.get("build") != str(build)
        or identity.get("patches") != {patch.name: sha256_file(patch) for patch in PATCHES}
        or identity.get("source_before") != SOURCE_SHA256
        or identity.get("implementation_sha256") != sha256_file(Path(__file__))
        or record.get("identity_sha256") != sha256_file(directory / "identity.json")
        or identity.get("guard_sources") != {name: sha256_file(ROOT / name) for name in GUARD_SOURCES}
    ):
        raise ValueError("unrecognized export frontend build receipt")
    expected_after = {
        name: digest for name, digest in EXPORT_SOURCE_SHA256.items() if digest != SOURCE_SHA256.get(name)
    }
    if record.get("source_after") != expected_after or identity.get("source_after") != expected_after:
        raise ValueError("export frontend patch identity changed")
    for relative, digest in EXPORT_SOURCE_SHA256.items():
        if sha256_file(checkout / relative) != digest:
            raise ValueError(f"export source identity changed: {relative}")
    frontend = checkout / "frontends/halide"
    expected_inputs = dict(identity["frontend_inputs"])
    expected_inputs.update(
        {
            str(Path(name).relative_to("frontends/halide")): digest
            for name, digest in expected_after.items()
            if name.startswith("frontends/halide/")
        }
    )
    actual_inputs = {str(p.relative_to(frontend)): sha256_file(p) for p in sorted(frontend.rglob("*")) if p.is_file()}
    if actual_inputs != expected_inputs:
        raise ValueError("export frontend input inventory changed")
    for tool, digest in identity["tools"].items():
        if sha256_file(Path(tool)) != digest:
            raise ValueError("export build tool identity changed")
    for key, path in {"library": build / "src/libHalide.dylib", "header": build / "include/Halide.h"}.items():
        if record.get(key) != str(path) or record.get(f"{key}_sha256") != sha256_file(path):
            raise ValueError(f"export {key} identity changed")
    for relative, digest in record["evidence"].items():
        path = directory / relative
        if not path.resolve().is_relative_to(directory) or sha256_file(path) != digest:
            raise ValueError("export build evidence changed")
    for name in ("export-halide-configure", "export-halide-build"):
        matches = list((directory / "steps").glob(f"*-{name}.request.json"))
        if len(matches) != 1:
            raise ValueError("export build evidence is incomplete")
        number = int(matches[0].name.split("-", 1)[0])
        prefix = f"steps/{number:03}-{name}"
        if not {prefix + ".request.json", prefix + ".result.json"}.issubset(record["evidence"]):
            raise ValueError("export build evidence is incomplete")
        result = json.loads((directory / (prefix + ".result.json")).read_text())
        request = json.loads((directory / (prefix + ".request.json")).read_text())
        if (
            result.get("status") != "success"
            or result.get("returncode") != 0
            or request.get("require_guard") is not True
            or request.get("memory_limit_bytes") != GROUP_LIMIT_BYTES
        ):
            raise ValueError("export build did not complete under the required guard")
        if request["command"] != identity["commands"][name]:
            raise ValueError("export build command differs from its prepared recipe")
    return record


def verify_export_request(request: dict[str, Any]) -> None:
    """Reject a request without the exact frontend and linked-generator receipts."""
    if request.get("egglog_export") != EXPORT_POLICY:
        raise ValueError("unsupported MISAAL Egglog export policy")
    targets = [argument for argument in request["generator_command"] if argument.startswith("target=")]
    if len(targets) != 1 or "," in targets[0]:
        raise ValueError("export supports only the original single-target generator commands")
    provenance = request["export_preparation"]
    for key in ("frontend", "generator"):
        path = Path(provenance[key])
        if not path.is_absolute() or path.is_symlink() or sha256_file(path) != provenance[key + "_sha256"]:
            raise ValueError(f"export {key} receipt changed")
    frontend = verified_frontend(Path(provenance["frontend"]))
    receipt = Path(provenance["generator"])
    record = json.loads(receipt.read_text())
    if (
        receipt.name != "generator.json"
        or record.get("schema") != "misaal-export-generator-v1"
        or record.get("status") != "success"
        or record.get("frontend") != provenance["frontend"]
        or record.get("frontend_sha256") != provenance["frontend_sha256"]
        or record.get("implementation_sha256") != sha256_file(Path(__file__))
        or record.get("request") != {key: value for key, value in request.items() if key != "export_preparation"}
        or request.get("checkout") != frontend["checkout"]
        or request.get("library") != frontend["library"]
        or request.get("library_sha256") != frontend["library_sha256"]
    ):
        raise ValueError("export generator receipt does not bind this request and library")
    for relative, digest in EXPORT_SOURCE_SHA256.items():
        if request["source_hashes"].get(relative) != digest:
            raise ValueError("export request omitted an exact frontend/source pin")
    if sha256_file(Path(request["generator"])) != request["generator_sha256"]:
        raise ValueError("export generator binary changed")
    for path, digest in record["inputs"].items():
        if sha256_file(Path(path)) != digest:
            raise ValueError("export generator build input changed")
    for relative, digest in record["evidence"].items():
        path = receipt.parent / relative
        if not path.resolve().is_relative_to(receipt.parent) or sha256_file(path) != digest:
            raise ValueError("export generator build evidence changed")
    steps = sorted(receipt.parent.glob("steps/*.request.json"))
    if len(steps) != 4:
        raise ValueError("export generator requires three original source compiles and one link")
    for step in steps:
        result_path = step.with_name(step.name.replace(".request.json", ".result.json"))
        if not {str(step.relative_to(receipt.parent)), str(result_path.relative_to(receipt.parent))}.issubset(
            record["evidence"]
        ):
            raise ValueError("export generator evidence is incomplete")
        step_request, result = json.loads(step.read_text()), json.loads(result_path.read_text())
        if (
            result.get("status") != "success"
            or result.get("returncode") != 0
            or step_request.get("require_guard") is not True
            or step_request.get("memory_limit_bytes") != GROUP_LIMIT_BYTES
        ):
            raise ValueError("export generator build was not guarded and successful")
    link = json.loads(steps[-1].read_text())["command"]
    if link != record["link_command"] or frontend["library"] not in link or link[-2:] != ["-o", request["generator"]]:
        raise ValueError("export generator was not linked to the recorded frontend library")


def prepare_export_generator(
    output: Path, template_request: Path, frontend_receipt: Path, *, timeout_sec: int = 120
) -> dict[str, Any]:
    """Recompile small original generator sources and link the shared export library."""
    from scripts.reproduction_prepare_misaal_cases import compile_object

    output, template_request, frontend_receipt = (
        output.resolve(),
        template_request.resolve(),
        frontend_receipt.resolve(),
    )
    if output.exists() or not output.is_relative_to((ROOT / "benchmarks/local/reproduction").resolve()):
        raise ValueError("export generator requires a fresh durable attempt")
    if timeout_sec <= 0 or any(key.startswith("MISAAL_EXPORT_") for key in os.environ):
        raise ValueError("export generator requires a positive timeout and no ambient export activation")
    frontend = verified_frontend(frontend_receipt)
    seed = verified_export_template(template_request)
    if seed["revision"] != MISAAL_REVISION or seed["configuration"].get("target") not in ("x86", "arm", "hexagon"):
        raise ValueError("export generator requires an original pinned MISAAL target request")
    checkout, original = Path(frontend["checkout"]), Path(seed["checkout"])
    targets = [argument for argument in seed["generator_command"] if argument.startswith("target=")]
    if len(targets) != 1 or "," in targets[0]:
        raise ValueError("export supports only the original single-target generator commands")
    source_hashes = dict(seed["source_hashes"])
    for relative, digest in source_hashes.items():
        expected = EXPORT_SOURCE_SHA256.get(relative, digest)
        if sha256_file(checkout / relative) != expected:
            raise ValueError("retained generator request differs from copied export sources")
    source_hashes.update(EXPORT_SOURCE_SHA256)
    target = seed["configuration"]["target"]
    name = Path(seed["source"]).name
    if seed["source"] != f"benchmarks/{target}/halide/{name}" or not name.replace("_", "").isalnum():
        raise ValueError("unexpected original generator source path")
    source = checkout / seed["source"] / "src" / f"{name}_generator.cpp"
    header, library = Path(frontend["header"]), Path(frontend["library"])
    sources = [
        checkout / "frontends/halide/tools/GenGen.cpp",
        checkout / f"benchmarks/{target}/halide/hannk/common_halide.cpp",
        source,
    ]
    compiler = Path("/usr/bin/clang++")
    output.mkdir(parents=True)
    preparation = Preparation(output)
    record: dict[str, Any] = {
        "schema": "misaal-export-generator-v1",
        "status": "failed",
        "frontend": str(frontend_receipt),
        "frontend_sha256": sha256_file(frontend_receipt),
        "implementation_sha256": sha256_file(Path(__file__)),
        "template_request": str(template_request),
        "template_sha256": sha256_file(template_request),
        "generator_execution": False,
    }
    try:
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
            str(checkout / "frontends/halide/tools"),
        ]
        objects, dependencies = [], {}
        for file in sources:
            obj, inputs = compile_object(preparation, file, output, flags, checkout, header, timeout_sec)
            objects.append(obj)
            dependencies.update(inputs)
        binary = output / f"{name}_generator"
        link = [str(compiler), *map(str, objects), str(library), f"-Wl,-rpath,{library.parent}", "-o", str(binary)]
        preparation.step("link-export-generator", link, cwd=checkout, timeout=timeout_sec)
        if not binary.is_file() or not binary.stat().st_size or not os.access(binary, os.X_OK):
            raise ValueError("successful link omitted the export generator")
        request = json.loads(json.dumps(seed))
        for key in (
            "legalizer",
            "legalizer_sha256",
            "llvm_as",
            "llvm_as_sha256",
            "hvx_link_contract",
            "acquisition_tail",
            "terminal_empty_child",
        ):
            request.pop(key, None)
        request["environment"].pop("HYDRIDE_DISABLE_LLVM_OPTS", None)
        original_build = seed["environment"]["HALIDE_DISTRIB"]
        for key, value in request["environment"].items():
            request["environment"][key] = value.replace(str(original), str(checkout)).replace(
                original_build, frontend["build"]
            )
        request.update(
            egglog_export=EXPORT_POLICY,
            checkout=str(checkout),
            source_hashes=source_hashes,
            library=str(library),
            library_sha256=frontend["library_sha256"],
            generator=str(binary),
            generator_sha256=sha256_file(binary),
            expected_generator_outputs=[],
            compile_dependencies=dependencies,
            generator_preparation=str(output),
        )
        request["generator_command"][0] = str(binary)
        obsolete = {seed.get(key) for key in ("library", "legalizer", "llvm_as")}
        request["identity_paths"] = list(
            dict.fromkeys(
                [
                    *(
                        str(path).replace(str(original), str(checkout)).replace(original_build, frontend["build"])
                        for path in seed.get("identity_paths", [])
                        if path not in obsolete
                    ),
                    str(frontend_receipt),
                    str(output / "generator.json"),
                    *dependencies,
                    str(checkout / "lib"),
                    str(library),
                    str(Path(__file__)),
                ]
            )
        )
        record.update(
            status="success",
            request=request,
            link_command=link,
            inputs={
                **dependencies,
                str(compiler): sha256_file(compiler),
                str(library): sha256_file(library),
                **{str(obj): sha256_file(obj) for obj in objects},
            },
        )
    except (OSError, ValueError, RuntimeError) as error:
        record["reason"] = str(error)
        failures = [json.loads(path.read_text()) for path in sorted(preparation.logs.glob("*.result.json"))]
        if failures and failures[-1].get("status") in {"resource-stopped", "memory-limit", "cancelled", "interrupted"}:
            record["status"] = failures[-1]["status"]
        elif "guard refused" in str(error):
            record["status"] = "resource-stopped"
    record["evidence"] = {str(p.relative_to(output)): sha256_file(p) for p in sorted(preparation.logs.iterdir())}
    write_json(output / "generator.json", record)
    if record["status"] == "success":
        request = {
            **record["request"],
            "export_preparation": {
                "frontend": str(frontend_receipt),
                "frontend_sha256": sha256_file(frontend_receipt),
                "generator": str(output / "generator.json"),
                "generator_sha256": sha256_file(output / "generator.json"),
            },
        }
        verify_export_request(request)
        write_json(output / "capture-request.json", request)
    return record


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    for name in ("frontend", "generator"):
        command = commands.add_parser(name)
        command.add_argument("--output", type=Path, required=True)
        command.add_argument("--template", type=Path, required=True)
        command.add_argument("--timeout", type=int, default=1800 if name == "frontend" else 120)
        if name == "generator":
            command.add_argument("--frontend", type=Path, required=True)
    args = parser.parse_args()
    with exclusive_job(ROOT / "benchmarks/local/reproduction/stages/.heavy-job.lock"):
        if args.command == "frontend":
            record = prepare_export_frontend(args.output, args.template, timeout_sec=args.timeout)
        else:
            record = prepare_export_generator(args.output, args.template, args.frontend, timeout_sec=args.timeout)
    print(json.dumps(record, indent=2))
    return 0 if record["status"] == "success" else 1


if __name__ == "__main__":
    raise SystemExit(main())
