#!/usr/bin/env python3
"""Materialize paper artifact programs as current, self-contained Egglog files."""

from __future__ import annotations

import argparse
import hashlib
import re
import subprocess
import textwrap
from collections.abc import Callable, Sequence
from pathlib import Path

MISAAL_COMMIT = "c098f0f289d03f0c58db1ef85d9b4ff7eef9dec4"
CHURCHROAD_COMMIT = "9f82ca23b273a5a500cc6a1ca60b30d3c33c5721"
DIALEGG_COMMIT = "4d0d522e98c15becdc5e7d711348cb0891ff0d44"

MISAAL_SOURCE_SHA256 = "158d265a52e1b82143f573748a0f600d3d4646c71c98df53bc4da33aa98d4864"
CHURCHROAD_PRELUDE_SHA256 = "2003bf604b44a3c760e4e0dbe645a2acd50367e81223498564240be6906341f6"
CHURCHROAD_WIDE_MUL_SHA256 = "793eaa9b8af1b7432e60af4739819373d2f7bc84b670816f9f23b7d5ec942de5"
CHURCHROAD_MAIN_SHA256 = "ee0df34796744c548fb4d8058fd2fde2bb5165e00097a3626314d2d62484b541"
CHURCHROAD_PLUGIN_SHA256 = "da3f0fabeb0b8337a57833a45e94a1631eee1711e516a918a33adbb4560023af"
CHURCHROAD_GENERATED_SHA256 = "d4264a2c04382e1a78c0ceb4323b363b11a320bf3b66e3ac451a8114707e479b"
CHURCHROAD_BENCHMARK_CYCLES = 17
YOSYS_COMMIT = "f8d4d7128cf72456cc03b0738a8651ac5dbe52e1"
DIALEGG_BASE_SHA256 = "69768076a70f83075cafd00aa053b227e257ecf88e5afaf368af44801fae2e5f"
DIALEGG_NMM_TEMPLATE_SHA256 = "548e5fc8f0bd4cbf294760769f783b48979021a58b93dd14cb104d14b612fc91"
DIALEGG_NMM_MLIR_SHA256 = {
    20: "57ba62628b10426cadfc3608dc64bea99cc768b55a9a65581bbd9da3d131722a",
    40: "d7cafa8c51645fb364e3696dd14407f81a6d57f62e29ee0d0c48229d588aeac3",
    80: "afa416c4f78a236f014480f0387de00b00c35058b396522bf99300af6f806a07",
}

MISAAL_EXPECTED = (
    "(typed_vec-add "
    "(hvx_swizzle_43 "
    "(hexagon_V6_vmpybv_128B "
    "(SYMBV 1) (SYMBV 2) 1024 1024 0 512 8 0 512 8 16 1 1 1 16 1024 1 1 8 2 0) "
    "2048 32 0 32 16 64 2 0) "
    "(SYMBV 0) 16 2048)"
)


def sha256_text(text: str) -> str:
    """Return the SHA-256 of UTF-8 source text."""
    return hashlib.sha256(text.encode()).hexdigest()


def read_verified(path: Path, expected_sha256: str) -> str:
    """Read an upstream input and reject a different artifact revision."""
    source = path.read_text(encoding="utf-8")
    actual_sha256 = sha256_text(source)
    if actual_sha256 != expected_sha256:
        raise ValueError(f"unexpected source at {path}: expected {expected_sha256}, got {actual_sha256}")
    return source


def replace_once(source: str, old: str, new: str, description: str) -> str:
    """Replace one expected artifact fragment, failing closed on source drift."""
    occurrences = source.count(old)
    if occurrences != 1:
        raise ValueError(f"expected exactly one {description}, found {occurrences}")
    return source.replace(old, new, 1)


def prefix_atoms(source: str, names: set[str]) -> str:
    """Prefix selected Egglog atoms with `$`, without touching strings or comments."""
    output: list[str] = []
    index = 0
    while index < len(source):
        character = source[index]
        if character == ";":
            newline = source.find("\n", index)
            if newline == -1:
                output.append(source[index:])
                break
            output.append(source[index : newline + 1])
            index = newline + 1
            continue
        if character == '"':
            end = index + 1
            while end < len(source):
                if source[end] == "\\":
                    end += 2
                    continue
                end += 1
                if source[end - 1] == '"':
                    break
            output.append(source[index:end])
            index = end
            continue
        if character.isspace() or character in "()":
            output.append(character)
            index += 1
            continue

        end = index
        while end < len(source) and not source[end].isspace() and source[end] not in '();"':
            end += 1
        atom = source[index:end]
        output.append(f"${atom}" if atom in names else atom)
        index = end
    return "".join(output)


def constructors(source: str, function_names: set[str] | None = None) -> str:
    """Convert paper-era constructor-like `(function ...)` declarations."""
    output: list[str] = []
    for line in source.splitlines():
        if line.startswith("(function ") and ":merge " not in line and ":no-merge" not in line:
            function_name = line.removeprefix("(function ").split(maxsplit=1)[0]
            if function_names is None or function_name in function_names:
                line = line.replace("(function ", "(constructor ", 1)
        output.append(line)
    return "\n".join(output)


def header(lines: Sequence[str]) -> str:
    """Format a provenance header as Egglog comments."""
    return "\n".join(f";; {line}" if line else ";;" for line in lines) + "\n\n"


def materialize_misaal(checkout: Path) -> str:
    """Materialize MISAAL's generated HVX dot-product workload."""
    relative_source = Path("test/compiler/egg_compiler/test_hvx_dot_prod.egg")
    source = read_verified(checkout / relative_source, MISAAL_SOURCE_SHA256)
    marker = "(let reg_1 (SYMBV 1))"
    before_globals, separator, after_globals = source.partition(marker)
    if not separator:
        raise ValueError("MISAAL global marker not found")
    modern_globals = prefix_atoms(separator + after_globals, {"reg_0", "reg_1", "reg_2", "srcexpr"})
    source = before_globals + modern_globals
    source = replace_once(
        source,
        "(extract $srcexpr)",
        f"(check (= $srcexpr {MISAAL_EXPECTED}))",
        "MISAAL extraction",
    )
    provenance = header(
        (
            "MISAAL: An E-Graph Based System for Synthesis of Machine-Independent Code",
            "PLDI 2025 artifact workload: HVX dot product",
            "SPDX-License-Identifier: Apache-2.0",
            f"Source: https://github.com/RafaeNoor/MISAAL/tree/{MISAAL_COMMIT}",
            f"Original: {relative_source.as_posix()}",
            f"Original SHA-256: {MISAAL_SOURCE_SHA256}",
            "Adaptations: use current `$` global syntax and replace extraction-only success with an equality check.",
            "Reproduce: uv run python scripts/paper_benchmarks/materialize.py misaal --checkout MISAAL --output OUT",
        )
    )
    return provenance + source.rstrip() + "\n"


def churchroad_mapping_program(main_source: str) -> str:
    """Extract the mapping rules embedded in the paper-era Churchroad driver."""
    start_marker = 'r#"\n        (ruleset mapping)'
    start = main_source.find(start_marker)
    end = main_source.find('\n    "#,', start)
    if start < 0 or end < 0:
        raise ValueError("Churchroad mapping program not found in src/main.rs")
    return textwrap.dedent(main_source[start + 3 : end]).strip()


def generate_churchroad_wide_mul(checkout: Path, yosys: Path, plugin: Path) -> str:
    """Run the pinned Yosys/Churchroad frontend for the paper's wide multiply."""
    version = subprocess.run((str(yosys), "-V"), check=True, capture_output=True, text=True).stdout
    if YOSYS_COMMIT[:9] not in version:
        raise ValueError(f"expected Yosys {YOSYS_COMMIT[:9]}, got {version.strip()}")
    verilog = (checkout / "tests/integration_tests/wide_mul.v").resolve()
    escaped_verilog = str(verilog).replace("\\", "\\\\").replace('"', '\\"')
    program = f'read_verilog -sv "{escaped_verilog}"; hierarchy -simcheck -top mul; prep; write_churchroad -letbindings'
    completed = subprocess.run(
        (str(yosys), "-m", str(plugin), "-q", "-p", program),
        check=True,
        capture_output=True,
        text=True,
    )
    return completed.stdout


def materialize_churchroad_wide_mul(
    checkout: Path,
    generated_path: Path | None,
    yosys: Path | None,
    plugin: Path | None,
) -> str:
    """Materialize the actual 16-by-32-bit multiply workload from the paper."""
    prelude_path = Path("egglog_src/churchroad.egg")
    verilog_path = Path("tests/integration_tests/wide_mul.v")
    main_path = Path("src/main.rs")
    plugin_path = Path("yosys-plugin/churchroad.cc")
    prelude = constructors(read_verified(checkout / prelude_path, CHURCHROAD_PRELUDE_SHA256))
    read_verified(checkout / verilog_path, CHURCHROAD_WIDE_MUL_SHA256)
    main_source = read_verified(checkout / main_path, CHURCHROAD_MAIN_SHA256)
    read_verified(checkout / plugin_path, CHURCHROAD_PLUGIN_SHA256)
    if generated_path is None:
        if yosys is None or plugin is None:
            raise ValueError("Churchroad generation requires --generated or both --yosys and --plugin")
        generated = generate_churchroad_wide_mul(checkout, yosys.resolve(), plugin.resolve())
    else:
        if yosys is not None or plugin is not None:
            raise ValueError("--generated cannot be combined with --yosys or --plugin")
        generated = generated_path.read_text(encoding="utf-8")
    if sha256_text(generated) != CHURCHROAD_GENERATED_SHA256:
        raise ValueError("unexpected write_churchroad output for wide_mul.v")
    generated = replace_once(
        generated,
        '(let a (Var "a" 16))\n(union v0 a)',
        '(union v0 (Var "a" 16))',
        "Churchroad input a alias",
    )
    generated = replace_once(
        generated,
        '(let b (Var "b" 32))\n(union v1 b)',
        '(union v1 (Var "b" 32))',
        "Churchroad input b alias",
    )
    generated = replace_once(generated, "(let out v2)\n", "", "Churchroad output alias")
    globals_ = set(re.findall(r"^\(let ([^\s()]+)", generated, re.MULTILINE))
    generated = prefix_atoms(generated, globals_)
    mapping = churchroad_mapping_program(main_source)
    low_b = "(Op1 (Extract 15 0) $v1)"
    high_b = "(Op1 (Extract 31 16) $v1)"
    low_mul = f"(Op2 (Mul) (Op1 (ZeroExtend 32) $v0) (Op1 (ZeroExtend 32) {low_b}))"
    high_mul = f"(Op2 (Mul) (Op1 (ZeroExtend 32) $v0) (Op1 (ZeroExtend 32) {high_b}))"
    shifted_high = f"(Op2 (Shl) {high_mul} (Op0 (BV 16 32)))"
    checks = "\n".join(
        (
            f"; The paper driver saturates this sequence. This {CHURCHROAD_BENCHMARK_CYCLES}-cycle prefix",
            "; measured about 0.9 seconds in normal release mode on the calibration machine;",
            f"; {CHURCHROAD_BENCHMARK_CYCLES + 1} cycles measured about 1.6 seconds.",
            f"(run-schedule (repeat {CHURCHROAD_BENCHMARK_CYCLES} (seq (run typing) (run transform) (run mapping))))",
            f"(check (= $v2 (Op2 (Add) {low_mul} {shifted_high})))",
            f"(check (= {low_mul} (PrimitiveInterfaceDSP $v0 {low_b})))",
            f"(check (= {high_mul} (PrimitiveInterfaceDSP $v0 {high_b})))",
            f"(check (= $v2 (PrimitiveInterfaceDSP3 $v0 {low_b} {shifted_high})))",
        )
    )
    provenance = header(
        (
            "Churchroad: Automated Technology Mapping for Hardware Generation",
            "WOSET 2024 paper workload: 16-by-32-bit wide multiply mapped toward Xilinx DSPs",
            "SPDX-License-Identifier: MIT",
            f"Source: https://github.com/gussmith23/churchroad/tree/{CHURCHROAD_COMMIT}",
            f"Original prelude: {prelude_path.as_posix()} ({CHURCHROAD_PRELUDE_SHA256})",
            f"Original Verilog: {verilog_path.as_posix()} ({CHURCHROAD_WIDE_MUL_SHA256})",
            f"Original driver: {main_path.as_posix()} ({CHURCHROAD_MAIN_SHA256})",
            f"Original Yosys plugin: {plugin_path.as_posix()} ({CHURCHROAD_PLUGIN_SHA256})",
            f"Generated commands SHA-256: {CHURCHROAD_GENERATED_SHA256}",
            f"Yosys source: https://github.com/YosysHQ/yosys/tree/{YOSYS_COMMIT}",
            "Scope: the paper's Egglog rewrite/mapping phase; external Lakeroad synthesis is not replayed.",
            "The paper schedule does not invoke module enumeration, so its Rust-only debruijnify primitive",
            "and module_enumeration_rewrites.egg are intentionally not part of this standalone workload.",
            "Adaptations: inline the prelude, use current constructors/globals, bound the paper's saturating",
            f"typing/transform/mapping sequence to {CHURCHROAD_BENCHMARK_CYCLES} cycles, and add checks for",
            "the wide-multiply expansion and the two-input and three-input DSP mapping proposals.",
            f"Calibration: {CHURCHROAD_BENCHMARK_CYCLES} cycles measured about 0.9 seconds in normal release",
            f"mode on the calibration machine; {CHURCHROAD_BENCHMARK_CYCLES + 1} cycles measured about 1.6",
            "seconds. Timings are machine-dependent.",
            "Reproduce: uv run python scripts/paper_benchmarks/materialize.py churchroad-wide-multiply "
            "--checkout churchroad --yosys YOSYS --plugin churchroad.so --output OUT",
        )
    )
    return (
        provenance
        + prelude.rstrip()
        + "\n\n;;; Commands generated from the paper's wide_mul.v\n"
        + generated.strip()
        + "\n\n;;; Mapping rules and schedule from the paper-era Churchroad driver\n"
        + mapping
        + "\n\n;;; Replay oracles\n"
        + checks
        + "\n"
    )


def modernize_dialegg_base(source: str) -> str:
    """Modernize DialEgg's shared prelude while retaining its lookup functions."""
    source = replace_once(source, "(function type-of (Op) Type)", "(function type-of (Op) Type :merge old)", "type-of")
    source = replace_once(source, "(function dims (Type) IntVec)", "(function dims (Type) IntVec :merge old)", "dims")
    return constructors(source)


def materialize_dialegg_nmm(checkout: Path, generated_path: Path | None, size: int) -> str:
    """Materialize one of DialEgg's generated matrix-chain scaling workloads."""
    base_path = Path("src/base.egg")
    template_path = Path("bench/nmm/nmm.egg")
    mlir_path = Path(f"bench/nmm/{size}mm.mlir")
    base = modernize_dialegg_base(read_verified(checkout / base_path, DIALEGG_BASE_SHA256))
    read_verified(checkout / template_path, DIALEGG_NMM_TEMPLATE_SHA256)
    read_verified(checkout / mlir_path, DIALEGG_NMM_MLIR_SHA256[size])
    generated = generated_path or checkout / "bench/nmm/nmm.ops.egg"
    generated_source = generated.read_text(encoding="utf-8")
    if f"; _{size}mm_func.func" not in generated_source:
        raise ValueError(f"{generated} is not the generated _{size}mm workload")
    generated_lines = [line for line in generated_source.splitlines() if line != '(include "src/base.egg")']
    generated_source = "\n".join(generated_lines)
    generated_source = replace_once(
        generated_source,
        "(function nrows (Type) i64)",
        "(function nrows (Type) i64 :merge old)",
        "nrows",
    )
    generated_source = replace_once(
        generated_source,
        "(function ncols (Type) i64)",
        "(function ncols (Type) i64 :merge old)",
        "ncols",
    )
    generated_source = replace_once(generated_source, "(unstable-cost ", "(set-cost ", "dynamic cost command")
    generated_source = constructors(generated_source)
    generated_source = replace_once(
        generated_source,
        "(constructor linalg_matmul (Op Op Op Type) Op)",
        "(with-dynamic-cost\n  (constructor linalg_matmul (Op Op Op Type) Op))",
        "dynamic-cost linalg_matmul declaration",
    )
    generated_source = prefix_atoms(generated_source, {f"op{index}" for index in range(3 * size + 2)})
    generated_source = replace_once(
        generated_source,
        ";; EXTRACTS HERE ;;",
        ";; CORRECTNESS CHECK ;;",
        "DialEgg extraction marker",
    )
    expected = (
        "(linalg_matmul $op0 "
        "(linalg_matmul $op1 $op2 "
        "(tensor_empty (RankedTensor (vec-of 77 39) (I32))) "
        "(RankedTensor (vec-of 77 39) (I32))) "
        f"$op{size + 3} (RankedTensor (vec-of 73 39) (I32)))"
    )
    generated_source = replace_once(
        generated_source,
        f"(extract $op{3 * size})",
        f"(check (= $op{size + 4} {expected}))",
        "DialEgg extraction",
    )
    provenance = header(
        (
            "DialEgg: Equality Saturation for Dialect-Agnostic Compiler Optimization",
            f"CGO 2025 artifact scaling workload: generated nmm.ops.egg for _{size}mm",
            "SPDX-License-Identifier: Apache-2.0",
            f"Source: https://github.com/AzizZayed/dialegg-cgo-artifact/tree/{DIALEGG_COMMIT}",
            f"Original prelude: {base_path.as_posix()} ({DIALEGG_BASE_SHA256})",
            f"Original template: {template_path.as_posix()} ({DIALEGG_NMM_TEMPLATE_SHA256})",
            f"Original MLIR: {mlir_path.as_posix()} ({DIALEGG_NMM_MLIR_SHA256[size]})",
            f"Generated by EqualitySaturationPass for the artifact's NMM-{size} scaling case.",
            "Adaptations: inline base.egg, use current constructors, globals, and dynamic cost command, "
            "and replace extraction with an associativity check.",
            "Reproduce: uv run python scripts/paper_benchmarks/materialize.py dialegg-nmm "
            f"--size {size} --checkout dialegg --output OUT",
        )
    )
    return provenance + base.rstrip() + "\n\n" + generated_source.strip() + "\n"


def write_or_check(output: Path, content: str, check: bool) -> None:
    """Write generated output, or verify that it matches a checked-in file."""
    content = "\n".join(line.rstrip() for line in content.splitlines()) + "\n"
    if check:
        existing = output.read_text(encoding="utf-8")
        if existing != content:
            raise ValueError(f"generated output does not match {output}")
        return
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(content, encoding="utf-8")


def add_common_arguments(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--checkout", type=Path, required=True, help="Pinned upstream checkout")
    parser.add_argument("--output", type=Path, required=True, help="Materialized .egg path")
    parser.add_argument("--check", action="store_true", help="Verify output instead of writing it")


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="project", required=True)
    add_common_arguments(subparsers.add_parser("misaal"))
    churchroad_parser = subparsers.add_parser("churchroad-wide-multiply")
    add_common_arguments(churchroad_parser)
    churchroad_parser.add_argument("--generated", type=Path, help="Previously generated write_churchroad output")
    churchroad_parser.add_argument("--yosys", type=Path, help="Pinned Yosys executable")
    churchroad_parser.add_argument("--plugin", type=Path, help="Built churchroad.so Yosys plugin")
    dialegg_parser = subparsers.add_parser("dialegg-nmm")
    add_common_arguments(dialegg_parser)
    dialegg_parser.add_argument("--size", type=int, choices=tuple(DIALEGG_NMM_MLIR_SHA256), required=True)
    dialegg_parser.add_argument(
        "--generated",
        type=Path,
        help="Generated nmm.ops.egg (defaults inside checkout)",
    )
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    materializers: dict[str, Callable[[Path], str]] = {
        "misaal": materialize_misaal,
    }
    if args.project == "dialegg-nmm":
        content = materialize_dialegg_nmm(args.checkout, args.generated, args.size)
    elif args.project == "churchroad-wide-multiply":
        content = materialize_churchroad_wide_mul(args.checkout, args.generated, args.yosys, args.plugin)
    else:
        content = materializers[args.project](args.checkout)
    write_or_check(args.output, content, args.check)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
