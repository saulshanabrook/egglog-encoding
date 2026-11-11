"""Prepare the pinned native MISAAL x86 canary, without running its generator.

Run from the repository root with ``python -m scripts.reproduction_prepare_misaal``.
Every subprocess has the shared guard; one cross-process lock covers preparation.
Sources, patches and numbered logs belong to a fresh immutable attempt directory.
"""

from __future__ import annotations

import argparse
import difflib
import hashlib
import json
import os
import platform
import re
import tarfile
import traceback
import uuid
from dataclasses import asdict
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

from benchmarking.pilot import run_bounded_command
from scripts.reproduction_misaal_legalizer import simd_mode_replacements
from scripts.reproduction_process import DISK_RESERVE_BYTES, exclusive_job

ROOT = Path(__file__).resolve().parents[1]
MISAAL_REVISION = "44ff893445d664cd87f52b08a138260ed2015ba8"
HYDRIDE_REVISION = "beb825327fc946d65032e96f7cde9acf3d24c13e"
EGGLOG_REVISION = "6b6938bc0088163f61240482cd34a1579715b804"
EGGLOG_SHA256 = "6bbb9c3fa064b300590ce059ec25eb9cbe10b5572e1e2ed2d80ea1fa332eb0c7"
EGGLOG_ARCHIVE_SHA256 = "2ad90a57a4b940dc02476121b1d09d19ddb0025957ef4562dbf08cff9227959c"
EGGLOG_LOCK_SHA256 = "50da3a4e74386cfed4667df1e76748407b3b76f5e36282700dfa39373cedac45"
BOOST_SHA256 = "71feeed900fbccca04a3b4f2f84a7c217186f28a940ed8b7ed4725986baf99fa"
LLVM12 = Path("/opt/homebrew/opt/llvm@12")
MEMORY_BYTES = 5 * 1024**3


def sha256_file(path: Path) -> str:
    """Use raw hex required by the capture protocol, without loading large files."""
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def write_json(path: Path, value: Any) -> None:
    """Never overwrite a retained receipt, including an incomplete earlier run."""
    with path.open("x") as output:
        json.dump(value, output, indent=2, default=str)
        output.write("\n")


class Preparation:
    """Own sequential guarded steps and immutable command/result evidence."""

    def __init__(self, directory: Path, *, continuation: bool = False):
        self.directory = directory.resolve()
        self.logs = self.directory / "steps"
        self.logs.mkdir(exist_ok=continuation)
        self.count = max((int(p.name.split("-")[0]) for p in self.logs.glob("*.request.json")), default=0)

    def step(self, name: str, command: list[str], *, cwd: Path | None = None, timeout: int = 600) -> str:
        self.count += 1
        prefix = self.logs / f"{self.count:03}-{name}"
        workdir = (cwd or self.directory).resolve()
        request = {
            "command": command,
            "cwd": str(workdir),
            "timeout_sec": timeout,
            "memory_limit_bytes": MEMORY_BYTES,
            "allow_warning_pressure": True,
            "require_guard": True,
            "disk_reserve_bytes": DISK_RESERVE_BYTES,
        }
        write_json(prefix.with_suffix(".request.json"), request)
        print(f"START {self.count:03} {name}", flush=True)
        try:
            result = run_bounded_command(
                command,
                workdir,
                prefix,
                timeout_sec=timeout,
                memory_limit_bytes=MEMORY_BYTES,
                allow_warning_pressure=True,
                require_guard=True,
                disk_reserve_bytes=DISK_RESERVE_BYTES,
            )
        except (OSError, ValueError) as error:
            write_json(prefix.with_suffix(".result.json"), {"status": "launch-refused", "reason": str(error)})
            raise
        write_json(prefix.with_suffix(".result.json"), asdict(result))
        print(f"END {self.count:03} {name}: {result.status} ({result.wall_sec:.1f}s)", flush=True)
        if result.status != "success":
            raise RuntimeError(f"{name}: {result.status}; see {prefix}.result.json")
        return result.stdout_path.read_text()

    def patch(self, source: Path, replacements: list[tuple[str, str]], name: str) -> None:
        """Change only acquired source, with exact contexts and a reversible diff."""
        if not source.resolve().is_relative_to(self.directory / "sources"):
            raise ValueError("refusing to patch a source outside this preparation")
        before = source.read_text()
        after = before
        for old, new in replacements:
            if after.count(old) != 1:
                raise ValueError(f"patch {name} expected exactly one context in {source}")
            after = after.replace(old, new)
        patch = self.directory / "patches" / f"{name}.patch"
        patch.parent.mkdir(exist_ok=True)
        relative = source.relative_to(self.directory / "sources")
        with patch.open("x") as output:
            output.writelines(
                difflib.unified_diff(before.splitlines(True), after.splitlines(True), f"a/{relative}", f"b/{relative}")
            )
        write_json(
            patch.with_suffix(".before.json"),
            {"path": str(source), "sha256": sha256_file(source)},
        )
        source.write_text(after)
        write_json(patch.with_suffix(".after.json"), {"path": str(source), "sha256": sha256_file(source)})


def patch_wrapper_inliner(preparation: Preparation) -> None:
    """Map call arguments only; CallInst operands also include the callee/bundles."""
    source = preparation.directory / "sources/MISAAL/frontends/halide/src/CodeGen_LLVM.cpp"
    before = """    if (!CF) return;

    // Map Arguments in the VMAP
    for (unsigned i = 0; i < CI->getNumOperands(); i++) {
        llvm::Value *ActualParam = CI->getArgOperand(i);

        llvm::Value *FormalParam = llvm::dyn_cast<llvm::Argument>((CF->arg_begin() + i));

        VMap[FormalParam] = ActualParam;
    }
"""
    after = before.replace(
        "    // Map Arguments in the VMAP\n",
        "    internal_assert(!CF->isVarArg() && CI->arg_size() == CF->arg_size())\n"
        '        << "Hydride wrapper call must match the fixed formal argument count";\n\n'
        "    // Map Arguments in the VMAP\n",
    ).replace("i < CI->getNumOperands()", "i < CI->arg_size()")
    preparation.patch(source, [(before, after)], "halide-wrapper-inliner-arguments")


def patch_pattern_cache(preparation: Preparation) -> None:
    """Keep cache bytes/generation unchanged while allowing an attempt-owned directory."""
    for module, stem in {"Halide": "halide", "x86": "x86", "ARM": "ARM", "HVX": "hvx"}.items():
        source = preparation.directory / f"sources/MISAAL/lib/patterns/{module}.py"
        before = source.read_text()
        matches = re.findall(r"^(?:pickle_file_name|abstract_pickle_file_name) = .*\n", before, re.M)
        if (
            len(matches) != 2
            or f"/lib/patterns/{stem}.pickle" not in matches[0]
            or (f"/lib/patterns/{stem}_abstract.pickle" not in matches[1])
        ):
            raise ValueError(f"unexpected original cache declarations: {source}")
        preparation.patch(
            source,
            [
                (
                    matches[0],
                    'pattern_cache_dir = os.getenv("MISAAL_PATTERN_CACHE_DIR", '
                    'os.path.join(MISAAL_ROOT, "lib", "patterns"))\n'
                    f'pickle_file_name = os.path.join(pattern_cache_dir, "{stem}.pickle")\n',
                ),
                (
                    matches[1],
                    f'abstract_pickle_file_name = os.path.join(pattern_cache_dir, "{stem}_abstract.pickle")\n',
                ),
            ],
            f"pattern-cache-directory-{module}",
        )


def build_backend(preparation: Preparation) -> Path:
    """Build the original backend from pinned source, without a retained binary prerequisite."""
    directory = preparation.directory
    archive = directory / "egglog.tar.gz"
    preparation.step(
        "backend-download",
        [
            "curl",
            "--fail",
            "--location",
            "--max-filesize",
            str(8 * 1024**2),
            f"https://codeload.github.com/egraphs-good/egglog/tar.gz/{EGGLOG_REVISION}",
            "-o",
            str(archive),
        ],
    )
    if sha256_file(archive) != EGGLOG_ARCHIVE_SHA256:
        raise ValueError("original backend archive differs from the verified source")
    with tarfile.open(archive) as tree:
        members = tree.getmembers()
        if sum(member.size for member in members) > 64 * 1024**2:
            raise ValueError("original backend source archive exceeds its size bound")
        for member in members:
            parts = Path(member.name).parts
            if (
                not parts
                or parts[0] != f"egglog-{EGGLOG_REVISION}"
                or ".." in parts
                or not (member.isfile() or member.isdir())
            ):
                raise ValueError("unexpected original backend archive member")
        tree.extractall(directory, filter="data")
    source = directory / f"egglog-{EGGLOG_REVISION}"
    if sha256_file(source / "Cargo.lock") != EGGLOG_LOCK_SHA256:
        raise ValueError("original backend dependency lock differs from the verified build")
    rust = preparation.step("backend-rust", ["rustc", "+1.91.0", "--version", "--verbose"], timeout=30)
    if not rust.startswith("rustc 1.91.0 ") or "host: aarch64-apple-darwin" not in rust:
        raise ValueError("backend requires the recorded native Rust 1.91.0 toolchain")
    preparation.step(
        "backend-build",
        [
            "env",
            "CARGO_INCREMENTAL=0",
            "CARGO_PROFILE_DEV_DEBUG=0",
            "RUSTC_WRAPPER=",
            "cargo",
            "+1.91.0",
            "build",
            "--locked",
            "--jobs",
            "1",
            "--bin",
            "egglog",
        ],
        cwd=source,
        timeout=600,
    )
    backend = source / "target/debug/egglog"
    if not backend.is_file() or not backend.stat().st_size or not os.access(backend, os.X_OK):
        raise ValueError("original backend build did not produce an executable")
    if sha256_file(source / "Cargo.lock") != EGGLOG_LOCK_SHA256:
        raise ValueError("backend build changed the dependency lock")
    write_json(
        directory / "backend.json",
        {
            "source_revision": EGGLOG_REVISION,
            "archive_sha256": EGGLOG_ARCHIVE_SHA256,
            "lock_sha256": EGGLOG_LOCK_SHA256,
            "backend": str(backend),
            "sha256": sha256_file(backend),
            "rust": rust,
        },
    )
    return backend


def prepare(directory: Path, backend: Path | None = None) -> Path:
    """Acquire the exact online compiler dependencies and prepare one x86 request."""
    if (platform.system(), platform.machine()) != ("Darwin", "arm64"):
        raise ValueError("this recipe is explicitly for native Apple Silicon")
    if backend is not None and sha256_file(backend) != EGGLOG_SHA256:
        raise ValueError("retained original Egglog binary differs from the inspected build")
    preparation = Preparation(directory)
    with (directory / "preparer.py").open("xb") as snapshot:
        snapshot.write(Path(__file__).read_bytes())
    if backend is None:
        backend = build_backend(preparation)
    write_json(
        directory / "identity.json",
        {
            "misaal_revision": MISAAL_REVISION,
            "hydride_revision": HYDRIDE_REVISION,
            "egglog_revision": EGGLOG_REVISION,
            "backend": str(backend),
            "backend_sha256": sha256_file(backend),
            "llvm_root": str(LLVM12.resolve()),
            "script_sha256": sha256_file(Path(__file__)),
            "guard_sources": {
                path: sha256_file(ROOT / path)
                for path in [
                    "benchmarking/pilot.py",
                    "benchmarking/memory_guard.py",
                    "scripts/reproduction_process.py",
                    "scripts/reproduction_misaal_legalizer.py",
                ]
            },
        },
    )
    preparation.step("llvm-version", [str(LLVM12 / "bin/llvm-config"), "--version"], timeout=30)
    preparation.step("native-tools", ["file", str(backend), str(LLVM12 / "bin/opt"), "/usr/bin/clang++"], timeout=30)
    sources = directory / "sources"
    sources.mkdir()
    misaal = sources / "MISAAL"
    preparation.step(
        "misaal-clone",
        [
            "git",
            "clone",
            "--depth",
            "1",
            "--filter=blob:none",
            "--no-checkout",
            "https://github.com/RafaeNoor/MISAAL.git",
            str(misaal),
        ],
    )
    preparation.step("misaal-fetch", ["git", "fetch", "--depth", "1", "origin", MISAAL_REVISION], cwd=misaal)
    preparation.step("misaal-checkout", ["git", "checkout", "--detach", MISAAL_REVISION], cwd=misaal)
    if preparation.step("misaal-head", ["git", "rev-parse", "HEAD"], cwd=misaal, timeout=30).strip() != MISAAL_REVISION:
        raise ValueError("MISAAL revision mismatch")
    hydride = misaal / "Hydride"
    preparation.step(
        "hydride-clone",
        [
            "git",
            "clone",
            "--depth",
            "1",
            "--filter=blob:none",
            "--no-checkout",
            "https://github.com/akothen/Hydride.git",
            str(hydride),
        ],
    )
    preparation.step("hydride-fetch", ["git", "fetch", "--depth", "1", "origin", HYDRIDE_REVISION], cwd=hydride)
    preparation.step(
        "hydride-sparse",
        ["git", "sparse-checkout", "set", "codegen-generator", "code-synthesizer/dsl-ir"],
        cwd=hydride,
    )
    preparation.step("hydride-checkout", ["git", "checkout", "--detach", HYDRIDE_REVISION], cwd=hydride)
    if (
        preparation.step("hydride-head", ["git", "rev-parse", "HEAD"], cwd=hydride, timeout=30).strip()
        != HYDRIDE_REVISION
    ):
        raise ValueError("Hydride revision mismatch")
    preparation.step("source-gitlinks", ["git", "ls-tree", "HEAD", "Hydride", "egglog"], cwd=misaal, timeout=30)
    frontend = misaal / "frontends/halide"
    preparation.patch(
        frontend / "src/CMakeLists.txt",
        [("    HydrideCodeGen.cpp\n", "    HydrideCodeGen.cpp\n    misaal.cpp\n")],
        "halide-include-misaal",
    )
    preparation.patch(
        frontend / "dependencies/llvm/CMakeLists.txt",
        [("if (${OPTION} OR Halide_SHARED_LLVM)", "if (${OPTION})")],
        "halide-selected-llvm-targets",
    )
    patch_wrapper_inliner(preparation)
    build = directory / "halide-build"
    cmake = ["uv", "tool", "run", "--from", "cmake==3.31.10", "cmake"]
    preparation.step(
        "halide-configure",
        [
            *cmake,
            "-S",
            str(frontend),
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
    )
    preparation.step(
        "halide-build", [*cmake, "--build", str(build), "--target", "Halide", "--parallel", "1"], timeout=1800
    )
    boost_archive = directory / "boost_1_81_0.tar.bz2"
    preparation.step(
        "boost-download",
        [
            "curl",
            "--fail",
            "--location",
            "https://archives.boost.io/release/1.81.0/source/boost_1_81_0.tar.bz2",
            "-o",
            str(boost_archive),
        ],
    )
    if sha256_file(boost_archive) != BOOST_SHA256:
        raise ValueError("Boost archive does not match the official release hash")
    preparation.step("boost-extract", ["tar", "-xjf", str(boost_archive), "-C", str(directory), "boost_1_81_0/boost"])
    legalizer_source = hydride / "codegen-generator/tools/low-level-codegen"
    preparation.patch(
        legalizer_source / "CMakeLists.txt",
        [
            (
                "add_library(x86LegalizerAllArgs SHARED ${x86_legalizer})",
                "add_library(x86LegalizerAllArgs SHARED ${x86_legalizer})\nif(APPLE)\n"
                '  set_target_properties(x86LegalizerAllArgs PROPERTIES SUFFIX ".so")\nendif()',
            )
        ],
        "legalizer-native-output-suffix",
    )
    legalizers = directory / "legalizers-build"
    preparation.step(
        "legalizer-configure",
        [
            *cmake,
            "-S",
            str(legalizer_source),
            "-B",
            str(legalizers),
            f"-DLLVM_DIR={LLVM12}/lib/cmake/llvm",
            "-DCMAKE_CXX_COMPILER=/usr/bin/clang++",
            f"-DCMAKE_CXX_FLAGS=-I{directory}/boost_1_81_0",
            "-DCMAKE_CXX_FLAGS_RELEASE=-O0 -DNDEBUG",
        ],
    )
    patch_wide_literals(preparation)
    selector = legalizer_source / "InstSelectors/x86/x86LegalizerAllArgs.cpp"
    preparation.patch(selector, simd_mode_replacements(selector.read_text(), "x86"), "legalizer-simd-mode")
    # Legalizer::legalize(Function&) accumulates whether any instruction changed.
    # Every matched branch returns true; an unmatched instruction changes nothing.
    no_match = "\n    \n}\n    \n\n};\n\n\nbool X86LegalizationPass::runOnFunction(Function &F) {\n"
    preparation.patch(
        selector,
        [(no_match, no_match.replace("\n}\n", "\n  return false;\n}\n", 1))],
        "legalizer-no-match-return",
    )
    preparation.step(
        "legalizer-build", [*cmake, "--build", str(legalizers), "--target", "x86LegalizerAllArgs", "--parallel", "1"]
    )
    return finish_native(preparation, backend)


def finish_native(preparation: Preparation, backend: Path) -> Path:
    """Validate real legalizer/Python dependencies and compile the original generator."""
    directory = preparation.directory
    misaal = directory / "sources/MISAAL"
    hydride = misaal / "Hydride"
    frontend = misaal / "frontends/halide"
    build = directory / "halide-build"
    legalizers = directory / "legalizers-build"
    legalizer = legalizers / "libx86LegalizerAllArgs.so"
    help_output = preparation.step(
        "legalizer-load", [str(LLVM12 / "bin/opt"), "-load", str(legalizer), "-enable-new-pm=0", "-help"], timeout=30
    )
    if "x86-hydride-legalize" not in help_output:
        raise ValueError("LLVM12 did not register the x86 legalizer pass")
    python = directory / "python/bin/python"
    preparation.step("python-environment", ["uv", "venv", "--python", "3.13.11", str(python.parent.parent)])
    preparation.step(
        "python-dependencies",
        [
            "uv",
            "pip",
            "install",
            "--python",
            str(python),
            "numpy==2.5.1",
            "psutil==7.2.2",
            "pyparsing==3.3.3",
            "z3-solver==5.1.0.0",
            "sympy==1.14.0",
            "mpmath==1.3.0",
            "ply==3.11",
            "toml==0.10.2",
        ],
    )
    preparation.step("python-freeze", ["uv", "pip", "freeze", "--python", str(python)], timeout=30)
    keys = [
        "PYTHONPATH",
        "MISAAL_SRC",
        "MISAAL_ROOT_DIR",
        "HYDRIDE_DIR",
        "HYDRIDE_ROOT",
        "DYLD_LIBRARY_PATH",
        "LD_LIBRARY_PATH",
    ]
    environment = json.loads(
        preparation.step(
            "source-environment",
            [
                "/usr/bin/env",
                "-u",
                "PYTHONPATH",
                "-u",
                "DYLD_LIBRARY_PATH",
                "-u",
                "LD_LIBRARY_PATH",
                "/bin/bash",
                "-ec",
                'source ./setup.sh\nexec "$1" -c "$2"',
                "prepare",
                str(python),
                f"import os,json; print(json.dumps({{k:os.environ.get(k,'') for k in {keys!r}}}))",
            ],
            cwd=misaal,
            timeout=30,
        )
    )
    environment.update(
        PATH=f"{python.parent}:{LLVM12}/bin:/usr/bin:/bin:/usr/sbin:/sbin:/opt/homebrew/bin",
        LLVM_ROOT=str(LLVM12),
        LLVM_DIS_ROOT=str(LLVM12),
        LLVM_CONFIG=str(LLVM12 / "bin/llvm-config"),
        LEGALIZERS_DIR=str(legalizers),
        HALIDE_SRC=str(frontend),
        HALIDE_DIR=str(build),
        HALIDE_DISTRIB=str(build),
        HL_EXPR_DEPTH="2",
        HYDRIDE_BENCHMARK="blur3x3_x86_depth2_misaal",
        HL_ENABLE_MISAAL="1",
        HL_ENABLE_HYDRIDE="1",
        HL_SYNTH_BW="16",
        HYDRIDE_INITIAL_HASH="empty_hash",
        MISAAL_DISABLE_FRONTEND_PATTERNS="1",
    )
    # Explicitly remove inherited source controls, then supply only this recipe.
    clear = [arg for key in os.environ if key.startswith(("HL_", "MISAAL_", "HYDRIDE_")) for arg in ("-u", key)]
    native_env = ["/usr/bin/env", *clear, *[f"{key}={value}" for key, value in environment.items()]]
    probe = (
        "import json,pathlib,llvmlite; from RosetteLifter import RosetteLifter; "
        "from RoseLowLevelCodeGen import HandleLowLevelCodeGen; "
        f"assert pathlib.Path(llvmlite.__file__).resolve().is_relative_to(pathlib.Path({str(hydride)!r})); "
        "print(json.dumps({'llvmlite':llvmlite.__file__,'rose_imports':'success'}))"
    )
    preparation.step("rose-imports", [*native_env, str(python), "-c", probe], timeout=60)
    generator = directory / "blur3x3_generator"
    generator_source = misaal / "benchmarks/x86/halide/blur3x3/src/blur3x3_generator.cpp"
    preparation.step(
        "generator-build",
        [
            "/usr/bin/clang++",
            "--std=c++17",
            "-fno-rtti",
            "-O3",
            "-g",
            "-DLOG2VLEN=7",
            "-I",
            str(build / "include"),
            "-I",
            str(frontend / "tools"),
            str(generator_source),
            str(frontend / "tools/GenGen.cpp"),
            str(misaal / "benchmarks/x86/halide/hannk/common_halide.cpp"),
            "-o",
            str(generator),
            "-L",
            str(build / "src"),
            "-lHalide",
            f"-Wl,-rpath,{build}/src",
        ],
    )
    if list((misaal / "lib/patterns").glob("*.pickle")):
        raise ValueError("preparation unexpectedly generated or acquired a pattern cache")
    patch_pattern_cache(preparation)
    source_paths = [
        "lib/compiler/EggLogCompiler.py",
        "lib/compiler/HydrideCompiler.py",
        "lib/patterns/x86.py",
        "lib/patterns/PatternUtils.py",
        "lib/patterns/Halide.py",
        "lib/patterns/ARM.py",
        "lib/patterns/HVX.py",
        "frontends/halide/src/CodeGen_LLVM.cpp",
        "frontends/halide/src/Rosette.cpp",
        "frontends/halide/src/misaal.cpp",
        "frontends/halide/src/misaal.h",
        "benchmarks/x86/halide/blur3x3/src/blur3x3_generator.cpp",
        "Hydride/codegen-generator/tools/low-level-codegen/RoseLowLevelCodeGen.py",
        "Hydride/codegen-generator/tools/low-level-codegen/InstSelectors/x86/x86LegalizerAllArgs.cpp",
        "Hydride/codegen-generator/tools/low-level-codegen/wrappers/x86_wrappers.c.ll",
    ]
    request = {
        "case_id": "misaal-x86-blur3x3",
        "source": "benchmarks/x86/halide/blur3x3",
        "configuration": {"target": "x86"},
        "revision": MISAAL_REVISION,
        "checkout": str(misaal),
        "source_hashes": {path: sha256_file(misaal / path) for path in source_paths},
        "environment": environment,
        "environment_unset": sorted(
            key for key in os.environ if key.startswith(("HL_", "MISAAL_", "HYDRIDE_")) and key not in environment
        ),
        "generator_command": [
            str(generator),
            "-t",
            "0",
            "-o",
            "{output}",
            "-g",
            "blur3x3",
            "-e",
            "static_library,stmt,h,llvm_assembly,assembly",
            "-f",
            "blur3x3",
            "target=host-x86-64-no_bounds_query-no_asserts",
        ],
        "expected_generator_outputs": [f"blur3x3.{suffix}" for suffix in ["a", "stmt", "h", "ll", "s"]],
        "preparation": str(directory),
        "hydride_revision": HYDRIDE_REVISION,
        "egglog_revision": EGGLOG_REVISION,
        "library": str((build / "src/libHalide.dylib").resolve()),
        "legalizer": str(legalizer),
        "library_sha256": sha256_file(build / "src/libHalide.dylib"),
        "legalizer_sha256": sha256_file(legalizer),
        "patches": {str(p.relative_to(directory)): sha256_file(p) for p in (directory / "patches").glob("*.patch")},
        "pattern_cache_contract": {
            "environment": "MISAAL_PATTERN_CACHE_DIR",
            "required": "adapter supplies a fresh empty attempt-owned directory before child imports",
            "generation": "unchanged",
            "default": "source lib/patterns when variable is absent",
        },
    }
    for key, executable in {
        "python": python,
        "backend": backend,
        "llvm_as": LLVM12 / "bin/llvm-as",
        "generator": generator,
    }.items():
        request[key] = str(executable)
        request[f"{key}_sha256"] = sha256_file(executable)
    path = directory / "capture-request.json"
    write_json(path, request)
    return path


def patch_wide_literals(preparation: Preparation) -> None:
    """Preserve the 12 pinned arbitrary-width constants using their existing type."""
    source = (
        preparation.directory
        / "sources/MISAAL/Hydride/codegen-generator/tools/low-level-codegen/InstSelectors/x86/x86LegalizerAllArgs.cpp"
    )
    before = source.read_text()
    count = 0

    def replace(match: re.Match[str]) -> str:
        nonlocal count
        value = int(match[2])
        if value <= 2**64 - 1:
            return match[0]
        if value > 2**512 - 1:
            raise ValueError("generated constant exceeds the declared int512_t type")
        count += 1
        return f'isAMatch(CI, {match[1]}, int512_t("{match[2]}"))'

    after = re.sub(r"isAMatch\(CI, (\d+), (\d+)\)", replace, before)
    if count != 12:
        raise ValueError(f"expected the 12 observed oversized literals, found {count}")
    preparation.patch(source, [(before, after)], "legalizer-exact-wide-constants")


def repair_wide_literals(directory: Path, backend: Path) -> Path:
    """One explicit repair for the observed C++ integer-literal compilation failure."""
    identity = json.loads((directory / "identity.json").read_text())
    if (identity["misaal_revision"], identity["hydride_revision"], sha256_file(backend)) != (
        MISAAL_REVISION,
        HYDRIDE_REVISION,
        EGGLOG_SHA256,
    ):
        raise ValueError("repair source/backend identity differs from the prepared attempt")
    failed = sorted((directory / "steps").glob("*-legalizer-build.result.json"))[-1]
    result = json.loads(failed.read_text())
    if (
        result["status"] != "failure"
        or "integer literal is too large to be represented in any integer type"
        not in Path(result["stderr_path"]).read_text()
    ):
        raise ValueError("this repair only applies to the retained wide-integer compile error")
    for receipt in (directory / "patches").glob("*.after.json"):
        record = json.loads(receipt.read_text())
        if sha256_file(Path(record["path"])) != record["sha256"]:
            raise ValueError(f"previously patched source changed: {receipt}")
    with (directory / "repair-preparer.py").open("xb") as snapshot:
        snapshot.write(Path(__file__).read_bytes())
    preparation = Preparation(directory, continuation=True)
    patch_wide_literals(preparation)
    preparation.step(
        "legalizer-build-repaired",
        [
            "uv",
            "tool",
            "run",
            "--from",
            "cmake==3.31.10",
            "cmake",
            "--build",
            str(directory / "legalizers-build"),
            "--target",
            "x86LegalizerAllArgs",
            "--parallel",
            "1",
        ],
    )
    return finish_native(preparation, backend)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--storage", type=Path, default=ROOT / "benchmarks/local/reproduction/prerequisites/misaal-44ff"
    )
    parser.add_argument("--lock", type=Path, default=ROOT / "benchmarks/local/reproduction/stages/.heavy-job.lock")
    parser.add_argument(
        "--repair-wide-literals", type=Path, help="Continue exactly one retained failed legalizer build"
    )
    parser.add_argument(
        "--backend",
        type=Path,
        help="Reuse the recorded original backend; otherwise acquire and build its pinned source",
    )
    args = parser.parse_args()
    with exclusive_job(args.lock.resolve()):
        if args.repair_wide_literals:
            if args.backend is None:
                raise ValueError("continuing a historical repair requires its recorded --backend")
            directory = args.repair_wide_literals.resolve()
            if not directory.is_relative_to(args.storage.resolve()):
                raise ValueError("repair attempt must belong to the preparation storage")
            receipt_name = "repair-summary"
            if (directory / f"{receipt_name}.json").exists():
                raise ValueError("the one bounded repair has already been attempted")
        else:
            directory = args.storage.resolve() / f"attempt-{datetime.now(UTC):%Y%m%dT%H%M%SZ}-{uuid.uuid4().hex[:8]}"
            directory.mkdir(parents=True)
            receipt_name = "summary"
        print(f"HEAVY_START {directory}", flush=True)
        summary: dict[str, Any] = {"attempt": str(directory), "started_at": datetime.now(UTC).isoformat()}
        try:
            request = (
                repair_wide_literals(directory, args.backend.resolve())
                if args.repair_wide_literals
                else prepare(directory, args.backend.resolve() if args.backend else None)
            )
            summary.update(
                status="canary-ready", capture_request=str(request), capture_request_sha256=sha256_file(request)
            )
        except BaseException as error:
            summary.update(status="failed", reason=str(error))
            with (directory / f"{receipt_name}-failure.txt").open("x") as output:
                output.write(traceback.format_exc())
            raise
        finally:
            summary["finished_at"] = datetime.now(UTC).isoformat()
            write_json(directory / f"{receipt_name}.json", summary)
            print(f"HEAVY_FINISH {directory}: {summary['status']}", flush=True)


if __name__ == "__main__":
    main()
