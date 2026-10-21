#!/usr/bin/env python3
"""Record a SpEQ artifact workload as replayable textual Egglog."""

from __future__ import annotations

import argparse
import hashlib
import importlib
import importlib.metadata
import re
import shlex
import subprocess
import sys
import tempfile
from collections.abc import Sequence
from pathlib import Path
from types import ModuleType
from typing import Any, cast

SPEQ_RECORD = "10963236"
SPEQ_ARCHIVE_MD5 = "813c94e4c12a3466909849f38b6ac1fe"
LLEQ_COMMIT = "00bd6254b3832d94558b7c38a394ea03d01a2763"
EGGLOG_PYTHON_VERSION = "13.2.0"
PARSE_IR_SHA256 = "37c30827e8ce8e2fc82be02c077e420f611a57e9358f12d228785f94a541dae0"
RUN_BENCHMARK_SHA256 = "d18ed3f2d132124b9023ee76da286fed3e8bddbb5838ebc9c9b16bfdffef0d82"
REV_TESTS_SHA256 = "6dc7b594b2c33917c1332615a476258c2166901c2bb5900ab8f7c455bc05ba33"
REV_PASS_SHA256 = "3d08d63232636db679365c5b6772e8193d1ca8bdbd7cd8b48b501755c3b753c5"
REV_PASS_HEADER_SHA256 = "b2901e1859ad2a06b443628669e2bb8c7ab4606f8e215fe05cbf7a456e3f54a5"
REFERENCE_ANALYSIS_SHA256 = {
    "gemm_ref": "82b1b9e129b7cc75a0456e267ab9dcd6e747fc4feeb37488e3ddf7bb58f54ab2",
    "gemv": "c985c5893ca005aac8822aa62a7f384c78337a319375e1b7ce92cc6ee440c3c9",
    "gemv_sink_perm": "8e14500f29a488629b9555f23e78cedaacb715607ee715c2f9456f1b06d0e551",
    "histogram": "b9ccb3de90635e13f03ce36e1bdd6b7993dbf243117884e1ccedb79f1534b909",
}
REFERENCE_FIR_SHA256 = {
    "gemm_ref": "a2b2ba3274b103a06666d0de2ec1fb518f26375c48b8aeed7c185e73141351f8",
    "gemv": "5de9cbfc235c056489d7275f95ad6647bf815c5b19d101aba12780bb41506de4",
    "gemv_sink_perm": "7a3949cd2947b0a88527f7765b82f63f4c0248d36092eec2d02c394930901f6e",
    "histogram": "fee918c713f15c02e209ba145c0f13ace12f9194db986d51480fcfef78b9c59d",
}
PRESERVED_REFERENCE_SUITE = (
    "taco_spmv_csc",
    "csparse_spmv_csc_nostruct",
    "npb_is_hist",
    "parboil_hist",
)
EXPECTED_KERNEL = {
    "polybench_gemm": "gemm",
    "taco_spmv_csc": "gemv",
    "csparse_spmv_csc_nostruct": "gemv",
    "SparseCompRow_matmult": "gemv",
    "spmv_npb": "gemv",
    "sparsebench_spmv_csr": "gemv",
    "npb_is_hist": "histogram",
    "parboil_hist": "histogram",
}


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--artifact", type=Path, required=True, help="Extracted lleq-artifact directory")
    parser.add_argument(
        "--rev-tests",
        type=Path,
        required=True,
        help="llvm/unittests/Transforms/REV/REVTest.cpp from the pinned lleq checkout",
    )
    parser.add_argument("--lleq", type=Path, required=True, help="Pinned lleq checkout")
    parser.add_argument(
        "--llvm-config",
        type=Path,
        required=True,
        help="llvm-config for a compatible LLVM installation (the paper's LLVM 17 is verified)",
    )
    parser.add_argument(
        "--rev-plugin",
        type=Path,
        help="Prebuilt REV pass plugin; otherwise build it in a temporary directory",
    )
    selection = parser.add_mutually_exclusive_group(required=True)
    selection.add_argument(
        "--benchmark",
        action="append",
        help="REVTEST workload name; repeat to record multiple workloads",
    )
    selection.add_argument(
        "--preserved-reference-suite",
        action="store_true",
        help="Record the four preserved workloads that match the artifact's reference rules",
    )
    parser.add_argument("--output", type=Path, required=True, help="Path for recorded textual Egglog")
    parser.add_argument("--check", action="store_true", help="Verify output instead of writing it")
    return parser.parse_args(argv)


def sha256_text(source: str) -> str:
    """Return the SHA-256 of UTF-8 source text."""
    return hashlib.sha256(source.encode()).hexdigest()


def read_verified(path: Path, expected_sha256: str) -> str:
    """Read a source file and reject an unexpected artifact revision."""
    source = path.read_text(encoding="utf-8")
    actual_sha256 = sha256_text(source)
    if actual_sha256 != expected_sha256:
        raise ValueError(f"unexpected source at {path}: expected {expected_sha256}, got {actual_sha256}")
    return source


def replace_exact(source: str, old: str, new: str, expected: int = 1) -> str:
    """Apply one fail-closed compatibility edit."""
    actual = source.count(old)
    if actual != expected:
        raise ValueError(f"expected {expected} occurrences of {old!r}, found {actual}")
    return source.replace(old, new)


def adapt_parse_ir(source: str) -> str:
    """Port the paper artifact to the native recorder in egglog-python 13.2."""
    source = replace_exact(
        source,
        "\negraph = EGraph()\n",
        "\negraph = EGraph(save_egglog_string=True)\n",
    )
    source = replace_exact(source, "@egraph.class_\n", "")
    source = replace_exact(source, "@egraph.method", "@method")
    source = replace_exact(source, "@egraph.function", "@function", expected=18)
    source = replace_exact(source, 'egraph.ruleset("expand")', 'ruleset(name="expand")')
    source = replace_exact(source, 'egraph.ruleset("transform")', 'ruleset(name="transform")')
    return replace_exact(source, 'egraph.constant("const", Val)', 'constant("const", Val)')


def extract_rev_test(path: Path, benchmark: str) -> str:
    """Extract the preserved custom-LLVM output for one REVTEST workload."""
    source = read_verified(path, REV_TESTS_SHA256)
    markers = (f"REVTEST(\n    {benchmark},", f"REVTEST(\n    DISABLED_{benchmark},")
    offsets = [source.find(marker) for marker in markers]
    starts = [offset for offset in offsets if offset >= 0]
    if len(starts) != 1:
        raise ValueError(f"expected exactly one REVTEST for {benchmark} in {path}")
    raw_start = source.find('R"(', starts[0])
    raw_end = source.find(')")', raw_start)
    if raw_start < 0 or raw_end < 0:
        raise ValueError(f"could not extract raw REV output for {benchmark} from {path}")
    return source[raw_start + 3 : raw_end]


def import_parse_ir(parse_ir: Path) -> ModuleType:
    """Import an adapted artifact module from an isolated temporary directory."""
    sys.path.insert(0, str(parse_ir.parent))
    module = importlib.import_module("parseIR")
    try:
        _ = module.egraph.as_egglog_string
    except ValueError as error:
        raise RuntimeError("adapted SpEQ parseIR.py did not enable native EGraph recording") from error
    return module


def command_output(command: Sequence[str]) -> str:
    """Run one reproduction command and return stdout, surfacing diagnostics on failure."""
    completed = subprocess.run(command, check=True, capture_output=True, text=True)
    return completed.stdout.strip()


def build_rev_plugin(lleq: Path, llvm_config: Path, output: Path) -> tuple[Path, Path, str]:
    """Build the pinned LLEQ REV analysis as a loadable LLVM plugin."""
    rev_pass = lleq / "llvm/lib/Analysis/REVPass.cpp"
    rev_header = lleq / "llvm/include/llvm/Analysis/REVPass.h"
    read_verified(rev_pass, REV_PASS_SHA256)
    read_verified(rev_header, REV_PASS_HEADER_SHA256)
    llvm_bindir = Path(command_output((str(llvm_config), "--bindir")))
    clangxx = llvm_bindir / "clang++"
    opt = llvm_bindir / "opt"
    flags = shlex.split(
        command_output(
            (
                str(llvm_config),
                "--cxxflags",
                "--ldflags",
                "--libs",
                "core",
                "analysis",
                "passes",
                "scalaropts",
                "transformutils",
                "ipo",
                "support",
                "--system-libs",
            )
        )
    )
    wrapper = Path(__file__).with_name("speq_rev_plugin.cpp")
    subprocess.run(
        (
            str(clangxx),
            "-fPIC",
            "-shared",
            str(rev_pass),
            str(wrapper),
            f"-I{lleq / 'llvm/include'}",
            *flags,
            "-o",
            str(output),
        ),
        check=True,
    )
    return opt, output, command_output((str(llvm_config), "--version"))


def reference_fir(opt: Path, plugin: Path, analysis: Path, name: str) -> str:
    """Run the paper's REV analysis and verify one reference-kernel FIR snapshot."""
    read_verified(analysis, REFERENCE_ANALYSIS_SHA256[name])
    completed = subprocess.run(
        (
            str(opt),
            f"-load-pass-plugin={plugin}",
            "-S",
            "-passes=print<revpass>",
            str(analysis),
            "-disable-output",
        ),
        check=True,
        capture_output=True,
        text=True,
    )
    match = re.fullmatch(r"REV Start\n(.*)REV End\n", completed.stderr, re.DOTALL)
    if match is None:
        raise ValueError(f"REV pass did not emit exactly one FIR program for {analysis}")
    fir = match.group(1)
    actual_sha256 = sha256_text(fir)
    expected_sha256 = REFERENCE_FIR_SHA256[name]
    if actual_sha256 != expected_sha256:
        raise ValueError(f"unexpected FIR for {name}: expected {expected_sha256}, got {actual_sha256}")
    return fir


def add_reference_rule(
    parse_ir: Any,
    egraph: Any,
    fir: str,
    name: str,
    params: Sequence[Any],
    function: Any | None = None,
) -> Any:
    """Register one reference implementation exactly as SpEQ's FIR.add does."""
    _, _, ast = parse_ir.foldFromStr(fir)
    abstractor = parse_ir.ToEggAbstract(params)
    pattern = abstractor.run(ast)
    if function is None:
        arguments = [
            "name: Val",
            *(f"{str(value).replace('%', '').replace('.', '_')}: Val" for value in abstractor.get_params()),
        ]
        namespace = {"Val": parse_ir.Val}
        exec(f"def {name}({', '.join(arguments)}) -> Val: ...", namespace)
        function = parse_ir.function(cost=0)(namespace[name])
    template = function(abstractor.root, *abstractor.get_params())
    egraph.register(parse_ir.rewrite(pattern, ruleset=parse_ir.transform).to(template))
    return function


def add_reference_rules(parse_ir: Any, egraph: Any, fir: dict[str, str]) -> None:
    """Register the GEMM, GEMV, and histogram rules from run_benchmark.py."""
    add_reference_rule(
        parse_ir,
        egraph,
        fir["gemm_ref"],
        "gemm",
        ("%ni", "%nj", "%nk", "%alpha", "%beta", "%C", "%A", "%B"),
    )
    gemv = add_reference_rule(
        parse_ir,
        egraph,
        fir["gemv"],
        "gemv",
        ("%m", "%n", "%alpha", "%a", "%x", "%beta", "%y"),
    )
    add_reference_rule(
        parse_ir,
        egraph,
        fir["gemv_sink_perm"],
        "gemv",
        ("%m", "%n", "%alpha", "%a", "%x", parse_ir.Val.constant_real(0.0), "%y"),
        gemv,
    )
    add_reference_rule(
        parse_ir,
        egraph,
        fir["histogram"],
        "histogram",
        ("%N", "%buckets", "%key", "%add"),
    )


def write_or_check(output: Path, content: str, check: bool) -> None:
    """Write the recording, or verify that it matches a checked-in file."""
    if check:
        if output.read_text(encoding="utf-8") != content:
            raise ValueError(f"native recording does not match {output}")
        return
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(content, encoding="utf-8")


def substitute_atoms(source: str, replacements: dict[str, str]) -> str:
    """Substitute complete Egglog atoms without touching string contents."""
    output: list[str] = []
    index = 0
    while index < len(source):
        character = source[index]
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
        while end < len(source) and not source[end].isspace() and source[end] not in '()"':
            end += 1
        atom = source[index:end]
        output.append(replacements.get(atom, atom))
        index = end
    return "".join(output)


def sort_constructor_blocks(lines: Sequence[str]) -> list[str]:
    """Stabilize independent constructor declarations emitted on first use."""
    output: list[str] = []
    constructors: list[str] = []
    for line in lines:
        if line.startswith("(constructor "):
            constructors.append(line)
            continue
        output.extend(sorted(constructors))
        constructors.clear()
        output.append(line)
    output.extend(sorted(constructors))
    return output


def benchmark_slug(benchmark: str) -> str:
    """Return a stable Egglog identifier fragment for a REVTEST name."""
    return re.sub(r"[^a-z0-9]+", "-", benchmark.lower()).strip("-")


def normalize_recording(source: str, benchmarks: Sequence[str]) -> str:
    """Normalize native recorder DAG factoring while preserving command order."""
    replacements: dict[str, str] = {}
    context_atoms: dict[str, str] = {}
    output: list[str] = []
    autogenerated_lets = 0
    context_index = 0
    for line in source.splitlines():
        if line == "(push 1)":
            replacements.clear()
            if context_index >= len(benchmarks):
                raise ValueError("native recorder emitted too many contexts")
            benchmark = benchmarks[context_index]
            slug = benchmark_slug(benchmark)
            context_atoms = {
                "parseIR.transform": f"parseIR.transform-{slug}",
                "parseIR.expand": f"parseIR.expand-{slug}",
            }
            output.append(f";; Preserved artifact workload: {benchmark}")
            context_index += 1
            output.append(line)
            continue
        if line == "(pop 1)":
            replacements.clear()
            context_atoms.clear()
            output.append(line)
            continue
        atom_replacements = context_atoms | replacements
        match = re.fullmatch(r"\(let (\$__expr_[0-9]+) (.*)\)", line)
        if match is None:
            output.append(substitute_atoms(line, atom_replacements))
            continue
        autogenerated_lets += 1
        name, expression = match.groups()
        expression = substitute_atoms(expression, atom_replacements)
        replacements[name] = expression
    normalized = "\n".join(sort_constructor_blocks(output)) + "\n"
    if context_index != len(benchmarks) or autogenerated_lets < len(benchmarks) or "$__expr_" in normalized:
        raise ValueError("unexpected native recorder let factoring")
    for benchmark in benchmarks:
        root = f"$speq-root-{benchmark_slug(benchmark)}"
        normalized = replace_exact(normalized, f"(extract {root} 0)\n", "")
    return normalized


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    artifact = args.artifact.resolve()
    version = importlib.metadata.version("egglog")
    if version != EGGLOG_PYTHON_VERSION:
        raise RuntimeError(f"recording requires egglog=={EGGLOG_PYTHON_VERSION}, found {version}")

    parse_ir_source = read_verified(artifact / "parseIR.py", PARSE_IR_SHA256)
    read_verified(artifact / "run_benchmark.py", RUN_BENCHMARK_SHA256)
    benchmarks = PRESERVED_REFERENCE_SUITE if args.preserved_reference_suite else tuple(args.benchmark)
    if len(set(benchmarks)) != len(benchmarks):
        raise ValueError("each SpEQ workload may only be recorded once")
    unsupported = set(benchmarks) - EXPECTED_KERNEL.keys()
    if unsupported:
        raise ValueError(f"no reference-kernel oracle is defined for {sorted(unsupported)}")
    with tempfile.TemporaryDirectory(prefix="speq-egglog-record-") as temporary_directory:
        temporary_path = Path(temporary_directory)
        lleq = args.lleq.resolve()
        if args.rev_plugin is None:
            opt, rev_plugin, llvm_version = build_rev_plugin(
                lleq,
                args.llvm_config.resolve(),
                temporary_path / "speq-rev-plugin.dylib",
            )
        else:
            read_verified(lleq / "llvm/lib/Analysis/REVPass.cpp", REV_PASS_SHA256)
            read_verified(lleq / "llvm/include/llvm/Analysis/REVPass.h", REV_PASS_HEADER_SHA256)
            llvm_bindir = Path(command_output((str(args.llvm_config.resolve()), "--bindir")))
            opt = llvm_bindir / "opt"
            rev_plugin = args.rev_plugin.resolve()
            llvm_version = command_output((str(args.llvm_config.resolve()), "--version"))
        reference_programs = {
            name: reference_fir(opt, rev_plugin, artifact / f"analysis/{name}.ll", name)
            for name in REFERENCE_ANALYSIS_SHA256
        }
        adapted_parse_ir = Path(temporary_directory) / "parseIR.py"
        adapted_parse_ir.write_text(adapt_parse_ir(parse_ir_source), encoding="utf-8")
        parse_ir = cast(Any, import_parse_ir(adapted_parse_ir))
        egraph = parse_ir.egraph
        add_reference_rules(parse_ir, egraph, reference_programs)
        extractions: list[str] = []
        for benchmark in benchmarks:
            fir = extract_rev_test(args.rev_tests.resolve(), benchmark)
            _, _, ast = parse_ir.foldFromStr(fir)
            ast_egg = ast.toEgg()
            with egraph:
                root = egraph.let(f"speq-root-{benchmark_slug(benchmark)}", ast_egg)
                egraph.run(5, ruleset=parse_ir.transform)
                egraph.run(1, ruleset=parse_ir.expand)
                egraph.run(3, ruleset=parse_ir.transform)
                extracted = egraph.extract(root)
                extraction = str(extracted)
                expected_kernel = EXPECTED_KERNEL[benchmark]
                if f"{expected_kernel}(" not in extraction:
                    raise ValueError(f"{benchmark} did not extract to {expected_kernel}: {extraction}")
                extractions.append(extraction)
                egraph.check(parse_ir.eq(root).to(extracted))
        egglog_source = normalize_recording(egraph.as_egglog_string, benchmarks)
    if not egglog_source.strip():
        raise RuntimeError("SpEQ's native recorder returned an empty program")

    provenance = "\n".join(
        (
            ";; SpEQ: Translation of Sparse Codes using Equivalences",
            f";; PLDI 2024 artifact benchmark(s): {', '.join(benchmarks)}",
            ";; Creator: Avery Laird",
            ";; SPDX-License-Identifier: CC-BY-4.0",
            ";; License: https://creativecommons.org/licenses/by/4.0/",
            f";; Artifact: https://zenodo.org/records/{SPEQ_RECORD}",
            f";; Archive MD5: {SPEQ_ARCHIVE_MD5}",
            f";; LLVM source: https://github.com/avery-laird/lleq/tree/{LLEQ_COMMIT}",
            f";; Artifact parseIR.py SHA-256: {PARSE_IR_SHA256}",
            f";; Artifact run_benchmark.py SHA-256: {RUN_BENCHMARK_SHA256}",
            f";; LLVM REVTest.cpp SHA-256: {REV_TESTS_SHA256}",
            f";; LLVM REVPass.cpp SHA-256: {REV_PASS_SHA256}",
            f";; Reference analysis SHA-256: {REFERENCE_ANALYSIS_SHA256}",
            f";; Reference FIR SHA-256: {REFERENCE_FIR_SHA256}",
            f";; Reference FIR generated with LLVM {llvm_version}.",
            f";; Recorded with egglog-python {EGGLOG_PYTHON_VERSION}.",
            ";; Recorded through egglog-python's native save_egglog_string/as_egglog_string playback path.",
            ";; Adaptations: enable native recording and port bound decorators, constants, and rulesets",
            ";; to their current unbound egglog-python APIs; register run_benchmark.py's reference",
            ";; implementations; retain each artifact workload's 5/1/3 schedule.",
            ";; Normalize temporary lets, give scoped rulesets stable per-workload names, and omit",
            ";; extraction from replay in favor of each workload's check.",
            ";; Native extractions:",
            *(
                f";; {benchmark}: {extraction.replace(chr(10), chr(10) + ';; ')}"
                for benchmark, extraction in zip(benchmarks, extractions, strict=True)
            ),
            "",
        )
    )
    write_or_check(args.output, provenance + egglog_source.rstrip() + "\n", args.check)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
