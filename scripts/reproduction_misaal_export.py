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

from scripts.reproduction_prepare_misaal import LLVM12, MISAAL_REVISION, Preparation, sha256_file, write_json
from scripts.reproduction_process import exclusive_job

ROOT = Path(__file__).resolve().parents[1]
EXPORT_POLICY = "egglog-only-v1"
EXPORT_SCHEMA = "misaal-export-v1"
GUARD_SOURCES = ("benchmarking/pilot.py", "benchmarking/memory_guard.py", "scripts/reproduction_process.py")
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
}
EXPORT_SOURCE_SHA256 = {
    **SOURCE_SHA256,
    "frontends/halide/src/MisaalExport.h": "d9163d565ae657cfad0679ab02c1d6fae1b2b8d79aff96358d6705f11061111f",
    "frontends/halide/src/Module.cpp": "7a4cef8dc3ce9d56f418e6bfe609e8975e1850d7661642a883a2497dcb26b517",
    "frontends/halide/src/CodeGen_LLVM.cpp": "2fcddb595e52f3cfd2e1280389c804eda49b7576a6b83eb7052d643a8af0dc7b",
    "frontends/halide/src/CodeGen_Hexagon.cpp": "39eb6b45e0778dd301f849a05a7df06c661c5e567544b3a912e1f9c93884d861",
    "frontends/halide/src/misaal.cpp": "96d0fa88a670e578696bd74a99a1eb77e5bd7505d61e34fa38d2ced187b0a85f",
}

HEADER_PATH = "frontends/halide/src/MisaalExport.h"
# C++17 inline state has one process-wide definition across the patched TUs.
# Text fields are UTF-8 byte hex; the Python reader owns strict ledger validation.
HEADER = r"""#ifndef MISAAL_EXPORT_H
#define MISAAL_EXPORT_H
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <stdexcept>
#include <string>
#include <vector>

namespace misaal_export {
inline bool enabled() {
    const char *mode = std::getenv("MISAAL_EXPORT_MODE");
    if (!mode) return false;
    if (std::strcmp(mode, "egglog-only-v1") != 0)
        throw std::runtime_error("Invalid MISAAL export mode");
    const char *path = std::getenv("MISAAL_EXPORT_EVENTS");
    if (!path || path[0] != '/')
        throw std::runtime_error("MISAAL export requires an absolute event path");
    return true;
}
inline std::string hex(const std::string &value) {
    const char *digits = "0123456789abcdef";
    std::string result;
    for (unsigned char c : value) {
        result += digits[c >> 4];
        result += digits[c & 15];
    }
    return result;
}
struct Ledger {
    std::ofstream file;
    size_t seq = 0, modules = 0, functions = 0, children = 0;
    std::vector<size_t> stack;
    long function = -1, child = -1;
    void emit(const std::string &event, const std::string &fields) {
        if (!file.is_open()) {
            const char *path = std::getenv("MISAAL_EXPORT_EVENTS");
            if (!path || std::ifstream(path).good())
                throw std::runtime_error("MISAAL event path must be fresh");
            file.open(path, std::ios::out);
        }
        file << "{\"schema\":\"misaal-export-v1\",\"seq\":" << seq++
             << ",\"event\":\"" << event << "\"" << fields << "}\n";
        file.flush();
        if (!file.good()) throw std::runtime_error("MISAAL event write failed");
    }
    void begin_module(const std::string &name, const std::string &target,
                      size_t function_count, size_t submodule_count) {
        if (function != -1 || child != -1)
            throw std::runtime_error("Overlapping MISAAL module export");
        const size_t id = modules++;
        emit("module_begin", ",\"module_id\":" + std::to_string(id) +
             ",\"parent_module_id\":" + (stack.empty() ? "null" : std::to_string(stack.back())) +
             ",\"name_hex\":\"" + hex(name) + "\",\"target_hex\":\"" + hex(target) +
             "\",\"function_count\":" + std::to_string(function_count) +
             ",\"submodule_count\":" + std::to_string(submodule_count));
        stack.push_back(id);
    }
    void end_module() {
        if (stack.empty() || function != -1 || child != -1)
            throw std::runtime_error("Unfinished MISAAL module export");
        const size_t id = stack.back();
        emit("module_end", ",\"module_id\":" + std::to_string(id));
        stack.pop_back();
        if (stack.empty())
            emit("export_complete", ",\"root_module_id\":" + std::to_string(id) +
                 ",\"module_count\":" + std::to_string(modules) +
                 ",\"function_count\":" + std::to_string(functions) +
                 ",\"child_count\":" + std::to_string(children));
    }
    void begin_function(const std::string &name) {
        if (stack.empty() || function != -1 || child != -1)
            throw std::runtime_error("Overlapping MISAAL function export");
        function = functions++;
        emit("function_begin", ",\"module_id\":" + std::to_string(stack.back()) +
             ",\"function_id\":" + std::to_string(function) + ",\"name_hex\":\"" + hex(name) + "\"");
    }
    void end_function() {
        if (stack.empty() || function == -1 || child != -1)
            throw std::runtime_error("Unfinished MISAAL function export");
        emit("function_end", ",\"module_id\":" + std::to_string(stack.back()) +
             ",\"function_id\":" + std::to_string(function));
        function = -1;
    }
    void begin_child(const std::string &script) {
        if (stack.empty() || function == -1 || child != -1)
            throw std::runtime_error("MISAAL child outside source function");
        child = children++;
        emit("child_begin", ",\"module_id\":" + std::to_string(stack.back()) +
             ",\"function_id\":" + std::to_string(function) +
             ",\"child_id\":" + std::to_string(child) + ",\"script_hex\":\"" + hex(script) + "\"");
    }
    void end_child(int status) {
        if (status != 0 || stack.empty() || function == -1 || child == -1)
            throw std::runtime_error("MISAAL source child failed");
        emit("child_end", ",\"module_id\":" + std::to_string(stack.back()) +
             ",\"function_id\":" + std::to_string(function) +
             ",\"child_id\":" + std::to_string(child) + ",\"returncode\":0");
        child = -1;
    }
};
inline Ledger ledger;
}  // namespace misaal_export
#endif
"""


def patched_sources(source: Path) -> dict[str, str]:
    """Validate the complete fixed boundary before deriving any source edits."""
    for relative, digest in SOURCE_SHA256.items():
        path = source / relative
        if not path.resolve().is_relative_to(source.resolve()) or sha256_file(path) != digest:
            raise ValueError(f"MISAAL export source identity changed: {relative}")
    if (source / HEADER_PATH).exists():
        raise ValueError("MISAAL export header already exists")
    edits: dict[str, list[tuple[str, str]]] = {
        "frontends/halide/src/Module.cpp": [
            ('#include "Module.h"', '#include "Module.h"\n#include "MisaalExport.h"\n#include "CodeGen_LLVM.h"'),
            (
                "void Module::compile(const std::map<OutputFileType, std::string> &output_files) const {\n",
                """void Module::compile(const std::map<OutputFileType, std::string> &output_files) const {
    if (misaal_export::enabled()) {
        misaal_export::ledger.begin_module(name(), target().to_string(), functions().size(), submodules().size());
        for (const auto &submodule : submodules()) {
            submodule.compile({});
        }
        llvm::LLVMContext context;
        auto codegen = Internal::CodeGen_LLVM::new_for_target(target(), context);
        codegen->compile(*this);
        misaal_export::ledger.end_module();
        return;
    }
""",
            ),
        ],
        "frontends/halide/src/CodeGen_LLVM.cpp": [
            ('#include "CodeGen_LLVM.h"', '#include "CodeGen_LLVM.h"\n#include "MisaalExport.h"'),
            (
                "std::unique_ptr<llvm::Module> CodeGen_LLVM::compile(const Module &input) {\n",
                """std::unique_ptr<llvm::Module> CodeGen_LLVM::compile(const Module &input) {
    if (misaal_export::enabled()) {
        for (const auto &f : input.functions()) {
            const auto names = get_mangled_names(f, get_target());
            misaal_export::ledger.begin_function(f.name);
            run_with_large_stack([&]() {
                compile_func(f, names.simple_name, names.extern_name);
            });
            misaal_export::ledger.end_function();
        }
        return nullptr;
    }
""",
            ),
            (
                "    // Generate the function declaration and argument unpacking code.\n    begin_func",
                "    if (!misaal_export::enabled()) {\n"
                "    // Generate the function declaration and argument unpacking code.\n    begin_func",
            ),
            (
                "    f.body.accept(this);\n\n    Stmt body = f.body;",
                "    f.body.accept(this);\n    }\n\n    Stmt body = f.body;",
            ),
            (
                "    body.accept(this);\n\n    // Clean up and return.\n    end_func(f.args);",
                "    if (misaal_export::enabled()) return;\n    body.accept(this);\n\n"
                "    // Clean up and return.\n    end_func(f.args);",
            ),
        ],
        "frontends/halide/src/CodeGen_Hexagon.cpp": [
            ('#include "CodeGen_Posix.h"', '#include "CodeGen_Posix.h"\n#include "MisaalExport.h"'),
            (
                "    CodeGen_Posix::begin_func(f.linkage, simple_name, extern_name, f.args);",
                "    if (!misaal_export::enabled()) "
                "CodeGen_Posix::begin_func(f.linkage, simple_name, extern_name, f.args);",
            ),
            (
                '    if(defer_to_llvm){\n        debug(0) << "Compiling Hexagon through LLVM!\\n";',
                "    if(defer_to_llvm){\n        if (misaal_export::enabled()) return;\n"
                '        debug(0) << "Compiling Hexagon through LLVM!\\n";',
            ),
            (
                "        body = optimize_hexagon_instructions_synthesis(body, target, this->func_value_bounds);",
                "        body = optimize_hexagon_instructions_synthesis(body, target, this->func_value_bounds);\n"
                "        if (misaal_export::enabled()) return;",
            ),
            (
                '        const char* disable_opt = getenv("HL_DISABLE_HEXAGON_OPT");',
                "        if (misaal_export::enabled()) return;\n"
                '        const char* disable_opt = getenv("HL_DISABLE_HEXAGON_OPT");',
            ),
        ],
        "frontends/halide/src/misaal.cpp": [
            ('#include "misaal.h"', '#include "misaal.h"\n#include "MisaalExport.h"'),
            (
                "        int ret_code = system(cmd.c_str());",
                "        if (misaal_export::enabled()) misaal_export::ledger.begin_child(fname);\n"
                "        int ret_code = system(cmd.c_str());\n"
                "        if (misaal_export::enabled()) misaal_export::ledger.end_child(ret_code);",
            ),
        ],
    }
    result = {HEADER_PATH: HEADER}
    for relative, replacements in edits.items():
        content = (source / relative).read_text()
        for before, after in replacements:
            if content.count(before) != 1:
                raise ValueError(f"MISAAL export patch context changed: {relative}")
            content = content.replace(before, after)
        result[relative] = content
    return result


def verified_export_template(path: Path) -> dict[str, Any]:
    """Verify retained graph/runtime inputs without requiring old native outputs."""
    from scripts.reproduction_misaal_groups import CONTRACT, SOURCE
    from scripts.reproduction_misaal_groups import SOURCE_SHA256 as GROUP_SOURCE_SHA256
    from scripts.reproduction_misaal_patterns import (
        LITERAL_WIDTH_CONTRACT,
        LITERAL_WIDTH_SOURCE_SHA256,
        PARAMETER_ABI_CONTRACT,
        PARAMETER_ABI_SOURCE_SHA256,
    )
    from scripts.reproduction_prepare_misaal import verified_backend_receipt

    request: dict[str, Any] = json.loads(path.read_text())
    if (
        request.get("revision") != MISAAL_REVISION
        or "egglog_export" in request
        or request.get("configuration") not in ({"target": "x86"}, {"target": "arm"}, {"target": "hexagon"})
    ):
        raise ValueError("export template requires an original pinned MISAAL target request")
    targets = [argument for argument in request["generator_command"] if argument.startswith("target=")]
    if len(targets) != 1 or "," in targets[0]:
        raise ValueError("export supports only the original single-target generator commands")
    checkout = Path(request["checkout"]).resolve()
    downstream = "Hydride/codegen-generator/tools/low-level-codegen/"
    obsolete_sources = {
        name
        for name in request["source_hashes"]
        if name.startswith((downstream + "InstSelectors/", downstream + "wrappers/"))
    }
    pins = {name: digest for name, digest in request["source_hashes"].items() if name not in obsolete_sources}
    if any(pins.get(name) != digest for name, digest in SOURCE_SHA256.items() if name in pins):
        raise ValueError("export template boundary source identity differs")
    # Some old requests did not enumerate every parent source. Verify the fixed
    # boundary directly as well, without trusting omission from their manifest.
    for relative, digest in {**pins, **SOURCE_SHA256}.items():
        source = (checkout / relative).resolve()
        if not source.is_relative_to(checkout) or sha256_file(source) != digest:
            raise ValueError(f"export template source identity changed: {relative}")
    for key in ("backend", "python", *(["racket"] if "racket" in request else [])):
        executable = Path(request[key])
        if (
            not executable.is_absolute()
            or not os.access(executable, os.X_OK)
            or sha256_file(executable) != request[key + "_sha256"]
        ):
            raise ValueError(f"export template {key} identity changed")
    if provenance := request.get("backend_preparation", request.get("backend_provenance")):
        receipt = Path(provenance["receipt"])
        if sha256_file(receipt) != provenance["sha256"] or verified_backend_receipt(receipt) != Path(
            request["backend"]
        ):
            raise ValueError("export template backend provenance changed")
    if runtime := request.get("racket_runtime"):
        receipt = Path(runtime["path"])
        if not receipt.is_absolute() or sha256_file(receipt) != runtime["sha256"]:
            raise ValueError("export template Racket runtime seal changed")
        seal = json.loads(receipt.read_text())
        if seal.get("schema") != "misaal-racket-runtime-v1" or seal.get("status") != "source-api-compatible":
            raise ValueError("export template Racket runtime has not passed source API gates")
    if (containment := request.get("racket_group_containment")) and (
        containment != CONTRACT or pins.get(SOURCE) != GROUP_SOURCE_SHA256 or "racket" not in request
    ):
        raise ValueError("export template Racket containment is unpinned")
    for key, contract, required in (
        ("parameter_abi", PARAMETER_ABI_CONTRACT, PARAMETER_ABI_SOURCE_SHA256),
        ("literal_width_guard", LITERAL_WIDTH_CONTRACT, LITERAL_WIDTH_SOURCE_SHA256),
    ):
        if key in request and (
            request[key] != contract or any(pins.get(name) != digest for name, digest in required.items())
        ):
            raise ValueError(f"export template {key} is unpinned")
    # Rebuild graph/runtime identities instead of inheriting old selector build
    # directories, publication receipts, or obsolete generator/library products.
    identities = [str(checkout / name) for name in pins]
    identities.extend(
        str(checkout / name)
        for name in ("lib", "targets", "misaal", "Hydride/codegen-generator", "Hydride/code-synthesizer")
        if (checkout / name).is_dir()
    )
    identities.extend(request[key] for key in ("backend", "python", "racket") if key in request)
    python_library = Path(request["python"]).parent.parent / "lib"
    if python_library.is_dir():
        identities.append(str(python_library))
    if runtime:
        identities.extend([runtime["path"], *(row["path"] for row in seal["code_trees"].values())])
    if provenance:
        identities.append(provenance["receipt"])
    request["source_hashes"] = pins
    request["identity_paths"] = list(dict.fromkeys(identities))
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
    patched = patched_sources(source)
    frontend = source / "frontends/halide"
    inputs = {str(p.relative_to(frontend)): sha256_file(p) for p in sorted(frontend.rglob("*")) if p.is_file()}
    tools = [Path("/usr/bin/clang"), Path("/usr/bin/clang++"), LLVM12 / "bin/llvm-config"]
    if any(not os.access(tool, os.X_OK) for tool in tools):
        raise ValueError("missing retained native frontend build tool")
    output.mkdir(parents=True)
    preparation = Preparation(output)
    checkout = output / "sources/MISAAL"
    shutil.copytree(source, checkout, ignore=shutil.ignore_patterns(".git", "__pycache__"))
    for relative, content in patched.items():
        destination = checkout / relative
        if relative == HEADER_PATH:
            with destination.open("x") as stream:
                stream.write(content)
        else:
            preparation.patch(destination, [(destination.read_text(), content)], "export-" + destination.stem)
    after = {relative: sha256_file(checkout / relative) for relative in patched}
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
        or identity.get("source_before") != SOURCE_SHA256
        or identity.get("implementation_sha256") != sha256_file(Path(__file__))
        or record.get("identity_sha256") != sha256_file(directory / "identity.json")
        or identity.get("guard_sources") != {name: sha256_file(ROOT / name) for name in GUARD_SOURCES}
    ):
        raise ValueError("unrecognized export frontend build receipt")
    expected_after = {
        name: digest
        for name, digest in EXPORT_SOURCE_SHA256.items()
        if name == HEADER_PATH or digest != SOURCE_SHA256.get(name)
    }
    if record.get("source_after") != expected_after or identity.get("source_after") != expected_after:
        raise ValueError("export frontend patch identity changed")
    for relative, digest in EXPORT_SOURCE_SHA256.items():
        if sha256_file(checkout / relative) != digest:
            raise ValueError(f"export source identity changed: {relative}")
    frontend = checkout / "frontends/halide"
    expected_inputs = dict(identity["frontend_inputs"])
    expected_inputs.update(
        {str(Path(name).relative_to("frontends/halide")): digest for name, digest in expected_after.items()}
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
    for number, name in ((1, "export-halide-configure"), (2, "export-halide-build")):
        prefix = f"steps/{number:03}-{name}"
        if not {prefix + ".request.json", prefix + ".result.json"}.issubset(record["evidence"]):
            raise ValueError("export build evidence is incomplete")
        result = json.loads((directory / (prefix + ".result.json")).read_text())
        request = json.loads((directory / (prefix + ".request.json")).read_text())
        if (
            result.get("status") != "success"
            or result.get("returncode") != 0
            or request.get("require_guard") is not True
            or request.get("memory_limit_bytes") != 5 * 1024**3
            or request.get("disk_reserve_bytes") != 10 * 1024**3
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
            or step_request.get("memory_limit_bytes") != 5 * 1024**3
            or step_request.get("disk_reserve_bytes") != 10 * 1024**3
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
