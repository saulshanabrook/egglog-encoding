#!/usr/bin/env python3
"""Record a SpEQ artifact workload as replayable textual Egglog."""

from __future__ import annotations

import argparse
import contextlib
import hashlib
import importlib
import importlib.metadata
import json
import os
import re
import shlex
import subprocess
import sys
import tempfile
from collections.abc import Sequence
from pathlib import Path
from types import ModuleType
from typing import Any, cast

# Direct recorder execution must resolve the tracked source-repair modules.
if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

SPEQ_RECORD = "10963236"
SPEQ_ARCHIVE_MD5 = "813c94e4c12a3466909849f38b6ac1fe"
LLEQ_COMMIT = "00bd6254b3832d94558b7c38a394ea03d01a2763"
EGGLOG_PYTHON_VERSION = "13.2.0"
PARSE_IR_SHA256 = "37c30827e8ce8e2fc82be02c077e420f611a57e9358f12d228785f94a541dae0"
RUN_BENCHMARK_SHA256 = "d18ed3f2d132124b9023ee76da286fed3e8bddbb5838ebc9c9b16bfdffef0d82"
REV_TESTS_SHA256 = "6dc7b594b2c33917c1332615a476258c2166901c2bb5900ab8f7c455bc05ba33"
REV_PASS_SHA256 = "3d08d63232636db679365c5b6772e8193d1ca8bdbd7cd8b48b501755c3b753c5"
REV_PASS_HEADER_SHA256 = "b2901e1859ad2a06b443628669e2bb8c7ab4606f8e215fe05cbf7a456e3f54a5"
REV_MEMORY_SSA_SHA256 = "99eebae9253222fd998975546537fe47740c2979d5afdcf608a7a6efc353289e"
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
APPLICATION_C_SHA256 = {
    "SparseCompRow_matmult": "cf55ecf031b7791df6eb1466f94fab8751b6d2ad38eaf3a305c9c2c28be4dfd0",
    "spmv_npb": "0dd5a063e9cc57b479af225e9aba7b52dd0e9c119a6bfd3bb8d4cb56da1a54ca",
    "sparsebench_spmv_csr": "56a6b7be1fe5045bdab3c5a231b9fc61fa2e27d0eaa633047899fce0042dc707",
}
# Original members of the completely indexed, checksum-verified Zenodo archive.
# Kept separate from the historical REVTest/single-region recorder selection.
COMPLETE_APPLICATION_C_SHA256 = {
    **APPLICATION_C_SHA256,
    "polybench_gemm": "e0fc07f40f59e83fc57f1d4e1e99f1718ffce106dcdc44c3e30ed88848228aea",
    "taco_spmv_csc": "ee8e52b5e316321b517b5017dabf28324f302a6c4105fd7c71e23d68b970499f",
    "csparse_spmv_csc_nostruct": "fa00745f846cbfb663293aff18a82b6b1f63e403b170722eeee155e0033f0aa1",
    "npb_is_hist": "ac6731acf5c8417ae03c9b4f65be13747d7f91f8c83696b2f660c85d85848481",
    "parboil_hist": "7d1e8d746ca40c4579377867e79674caad15b81592ce8037e96c474c44e41172",
}
APPLICATION_HEADER_SHA256 = {
    "polybench.h": "e3eccb3e06867a483631c3c4ca851164002ea4d886ba3aa5061670fedfdc443d",
    "gemm.h": "5f00ecaa574abcde34da0e1f86ef53b6609060df9b2a3600650cf4a336986d66",
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
        help="SpEQ workload name; repeat to record multiple workloads",
    )
    selection.add_argument(
        "--preserved-reference-suite",
        action="store_true",
        help="Record the four preserved workloads that match the artifact's reference rules",
    )
    parser.add_argument("--output", type=Path, required=True, help="Path for recorded textual Egglog")
    parser.add_argument(
        "--source-evidence",
        type=Path,
        help="Fresh directory retaining original-C frontend commands, logs and every FIR chunk",
    )
    parser.add_argument("--check", action="store_true", help="Verify output instead of writing it")
    parser.add_argument("--complete", action="store_true", help="Record every original-C FIR region and parent outcome")
    parser.add_argument(
        "--frontend-flag",
        action="append",
        default=[],
        help="Opt-in original-C compiler flag in complete mode; repeat using --frontend-flag=VALUE",
    )
    parser.add_argument(
        "--repair-phi-polarity",
        action="store_true",
        help="Opt in to the recorded edge-aware REV PHI repair; requires a fresh complete-mode plugin build",
    )
    parser.add_argument(
        "--c99-frontend-repair",
        choices=("polybench-gemm-address-v1",),
        help="Scoped original-C PolyBench GEMM address repair; requires PHI and fresh paired plugins",
    )
    args = parser.parse_args(argv)
    if args.frontend_flag and not args.complete:
        parser.error("--frontend-flag requires --complete")
    if args.repair_phi_polarity and (not args.complete or args.rev_plugin is not None):
        parser.error("--repair-phi-polarity requires --complete and cannot use --rev-plugin")
    if args.c99_frontend_repair and (
        not args.complete
        or not args.repair_phi_polarity
        or args.rev_plugin is not None
        or args.benchmark != ["polybench_gemm"]
    ):
        parser.error("C99 repair requires complete polybench_gemm, PHI repair, and no --rev-plugin")
    return args


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


def build_rev_plugin(
    lleq: Path, llvm_config: Path, output: Path, *, repair_phi_polarity: bool = False
) -> tuple[Path, Path, str]:
    """Build the pinned LLEQ REV analysis as a loadable LLVM plugin."""
    rev_pass = lleq / "llvm/lib/Analysis/REVPass.cpp"
    rev_header = lleq / "llvm/include/llvm/Analysis/REVPass.h"
    read_verified(rev_pass, REV_PASS_SHA256)
    read_verified(rev_header, REV_PASS_HEADER_SHA256)
    read_verified(lleq / "llvm/include/llvm/Analysis/MemorySSA.h", REV_MEMORY_SSA_SHA256)
    if repair_phi_polarity:
        # Direct script execution needs the repository package on sys.path.
        # Local import avoids a cycle: the diagnostic shares these source pins.
        repository = str(Path(__file__).resolve().parents[2])
        if repository not in sys.path:
            sys.path.insert(0, repository)
        from scripts.speq_phi_diagnostic import materialize

        repair = output.parent / "phi-repair"
        materialize(lleq, repair)
        lleq = repair / "patched"
    return compile_rev_plugin(lleq, llvm_config, output)


def compile_rev_plugin(lleq: Path, llvm_config: Path, output: Path) -> tuple[Path, Path, str]:
    """Compile an already verified/materialized REV source with the original wrapper.

    Native callers run this entire operation below the outer process guard.
    Source pinning belongs to build_rev_plugin or the paired C99 materializer.
    """
    rev_pass = lleq / "llvm/lib/Analysis/REVPass.cpp"
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
    if "SPEQ_REV_C99_DIAGNOSTIC" in os.environ:
        raise ValueError("C99 must be disabled for every reference analysis")
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


def application_fir(
    artifact: Path,
    opt: Path,
    plugin: Path,
    name: str,
    evidence: Path,
    *,
    complete: bool = False,
    frontend_flags: Sequence[str] = (),
    c99_frontend_repair: bool = False,
) -> str | list[str]:
    """Regenerate original C; complete mode returns all ordered regions, including setup."""
    if frontend_flags and not complete:
        raise ValueError("frontend flags require complete original-C recording")
    if "SPEQ_REV_C99_DIAGNOSTIC" in os.environ:
        raise ValueError("C99 must be disabled in the inherited frontend environment")
    if c99_frontend_repair:
        from scripts.speq_c99_diagnostic import FRONTEND_FLAGS, FUNCTION

        if not complete or name != FUNCTION or tuple(frontend_flags) != FRONTEND_FLAGS:
            raise ValueError("C99 repair requires the pinned complete GEMM frontend configuration")
    source = artifact / f"benchmarks/{name}.c"
    expected = (COMPLETE_APPLICATION_C_SHA256 if complete else APPLICATION_C_SHA256)[name]
    read_verified(source, expected)
    headers = APPLICATION_HEADER_SHA256 if complete and name == "polybench_gemm" else {}
    for header, digest in headers.items():
        read_verified(source.parent / header, digest)
    evidence.mkdir(parents=True, exist_ok=False)
    commands = [
        [
            str(opt.parent / "clang"),
            "-S",
            "-emit-llvm",
            "-O0",
            "-Xclang",
            "-disable-O0-optnone",
            "-fno-discard-value-names",
            *frontend_flags,
            str(source),
            "-o",
            str(evidence / "input.ll"),
        ],
        [
            str(opt),
            f"-load-pass-plugin={plugin}",
            "-S",
            "-passes=mem2reg,loop-rotate,instcombine,simplifycfg,loop-simplify,gvn,lcssa,print<revpass>",
            "-enable-load-in-loop-pre=false",
            str(evidence / "input.ll"),
            "-o",
            str(evidence / "analysis.ll"),
        ],
    ]
    manifest: dict[str, Any] = {
        "source_c": str(source),
        "source_sha256": expected,
        "header_sha256": headers,
        "frontend_flags": list(frontend_flags),
        "boundary": "original artifact C through native LLVM and pinned REV pass; not the Docker build",
        "commands": [],
        "chunks": [],
    }
    for index, command in enumerate(commands):
        stdout_path = evidence / f"frontend-{index}.stdout.log"
        stderr_path = evidence / f"frontend-{index}.stderr.log"
        environment = None
        if c99_frontend_repair and index == 1:
            environment = {**os.environ, "SPEQ_REV_C99_DIAGNOSTIC": "1"}
        with stdout_path.open("wb") as stdout, stderr_path.open("wb") as stderr:
            result = subprocess.run(command, stdout=stdout, stderr=stderr, check=False, env=environment)
        manifest["commands"].append(
            {
                "command": command,
                "c99_enabled": environment is not None,
                "returncode": result.returncode,
                "stdout": str(stdout_path),
                "stderr": str(stderr_path),
            }
        )
        (evidence / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
        if result.returncode:
            raise ValueError(f"{name} frontend command failed with exit {result.returncode}; see {stderr_path}")
    diagnostic = stderr_path.read_text()
    firs: list[str] = re.findall(r"REV Start\n(.*?)REV End", diagnostic, re.DOTALL)
    if complete and (diagnostic.count("REV Start") != len(firs) or diagnostic.count("REV End") != len(firs)):
        raise ValueError("REV frontend emitted truncated or nested region markers; diagnostics retained")
    for index, fir in enumerate(firs):
        path = evidence / f"application-{index:03}.fir"
        path.write_text(fir)
        manifest["chunks"].append({"index": index, "path": str(path), "sha256": sha256_text(fir)})
    manifest["analysis_sha256"] = hashlib.sha256((evidence / "analysis.ll").read_bytes()).hexdigest()
    (evidence / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    if complete:
        return firs
    if len(firs) != 1:
        raise ValueError(
            f"{name}: expected one original-C FIR invocation, got {len(firs)}; all chunks retained in {evidence}"
        )
    return firs[0]


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
    return normalized


def record_complete_regions(
    parse_ir: Any, egraph: Any, firs: Sequence[str], benchmark: str, evidence: Path, manifest: dict[str, Any]
) -> list[str]:
    """Follow Analysis.run's parsing/skip, 5/1/3 extraction, and formatting decisions.

    The pinned Python backend's extraction report supplies the actual Egglog term
    and cost. Observing that report adds no query, fact, or extraction to the graph.
    """
    bindings = importlib.import_module("egglog.bindings")

    contexts = []
    native_extract = egraph._run_extract
    reports: list[Any] = []

    def observe_extract(*args: Any, **kwargs: Any) -> Any:
        report = native_extract(*args, **kwargs)
        reports.append(report)
        return report

    egraph._run_extract = observe_extract
    try:
        for index, fir in enumerate(firs):
            region = evidence / f"region-{index:03}"
            region.mkdir()
            row: dict[str, Any] = {"index": index, "fir_sha256": sha256_text(fir), "status": "parsing"}
            manifest["regions"].append(row)
            (evidence / "region-outcomes.json").write_text(json.dumps(manifest, indent=2, default=str) + "\n")
            (evidence / "native-session.egg").write_text(egraph.as_egglog_string)
            # This is exactly the original driver's skip boundary. Egglog failures
            # below it abort the parent instead of being disguised as setup skips.
            with (region / "parse.stdout.log").open("w") as out, (region / "parse.stderr.log").open("w") as err:
                try:
                    with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
                        formats, rtc, ast = parse_ir.foldFromStr(fir)
                except Exception as error:
                    row.update(status="skipped-parse", reason=f"{type(error).__name__}: {error}")
                    continue
            row["formats"] = formats
            row["runtime_checks"] = [str(check) for check in rtc]
            ast_egg = ast.toEgg()
            row["status"] = "optimizing"
            label = f"{benchmark}-region-{index:03}"
            contexts.append(label)
            with egraph:
                root = egraph.let(f"speq-root-{benchmark_slug(label)}", ast_egg)
                egraph.run(5, ruleset=parse_ir.transform)
                egraph.run(1, ruleset=parse_ir.expand)
                egraph.run(3, ruleset=parse_ir.transform)
                before = len(reports)
                extracted = egraph.extract(root)
                if len(reports) != before + 1 or not isinstance(reports[-1], bindings.ExtractBest):
                    raise ValueError("native best-extraction report contract changed")
                report = reports[-1]
                term = report.termdag.to_string(report.term)
                extraction = str(extracted)
                row.update(status="unmatched", extraction=extraction, egglog_term=term, cost=report.cost)
                # Preserve the driver's ordered GEMM, GEMV, Histogram match and
                # sparse-format rendering; require the paper application's target below.
                for kernel, sparse in (("gemm", "spmm"), ("gemv", "spmv"), ("histogram", None)):
                    match = re.search(rf"\b{kernel}\(", extraction)
                    if match is None:
                        continue
                    start = match.end() - 1
                    depth, end = 1, start + 1
                    while depth and end < len(extraction):
                        depth += (extraction[end] == "(") - (extraction[end] == ")")
                        end += 1
                    if depth:
                        raise ValueError("unbalanced native Python extraction rendering")
                    representation = formats[0] if formats is not None else []
                    rendered_kernel = kernel
                    if "CSR" in representation or "CSC" in representation:
                        if sparse is None:
                            raise ValueError("original driver has no sparse name for this extracted kernel")
                        rendered_kernel = sparse + ("_csr" if "CSR" in representation else "_csc")
                    row.update(status="matched", kernel=kernel, translation=rendered_kernel + extraction[start:end])
                    break
    except Exception as error:
        if manifest["regions"]:
            manifest["regions"][-1].update(status="failed", reason=f"{type(error).__name__}: {error}")
        raise
    finally:
        egraph._run_extract = native_extract
        manifest["contexts"] = contexts
        manifest["expected_stdout"] = "".join(
            row["egglog_term"] + "\n" for row in manifest["regions"] if "egglog_term" in row
        )
        (evidence / "region-outcomes.json").write_text(json.dumps(manifest, indent=2, default=str) + "\n")
        (evidence / "native-session.egg").write_text(egraph.as_egglog_string)
    return contexts


def record_complete(args: argparse.Namespace, artifact: Path, parse_ir_source: str, benchmarks: Sequence[str]) -> int:
    """One original-C application is one parent with inherited reference rules and pushed regions."""
    if len(benchmarks) != 1 or args.source_evidence is None or args.check:
        raise ValueError("complete mode requires one --benchmark, a fresh --source-evidence, and no --check")
    name = benchmarks[0]
    frontend_flags = getattr(args, "frontend_flag", [])
    repair_phi = bool(getattr(args, "repair_phi_polarity", False))
    c99_mode = getattr(args, "c99_frontend_repair", None)
    if "SPEQ_REV_C99_DIAGNOSTIC" in os.environ:
        raise ValueError("C99 must be disabled at recorder entry and for every reference")
    if c99_mode is not None:
        from scripts import speq_c99_diagnostic as c99

        if (
            c99_mode != c99.CONTRACT
            or name != c99.FUNCTION
            or not repair_phi
            or args.rev_plugin is not None
            or tuple(frontend_flags) != c99.FRONTEND_FLAGS
        ):
            raise ValueError("C99 repair requires the pinned complete GEMM configuration, PHI, and fresh plugins")
    if repair_phi and args.rev_plugin is not None:
        raise ValueError("PHI polarity repair cannot use a supplied prebuilt REV plugin")
    if name not in COMPLETE_APPLICATION_C_SHA256:
        raise ValueError(f"exact original C is unavailable for {name}")
    evidence = args.source_evidence.resolve()
    evidence.mkdir(parents=True, exist_ok=False)
    manifest: dict[str, Any] = {
        "benchmark": name,
        "source_complete": False,
        "regions": [],
        "contexts": [],
        "expected_stdout": "",
        "source_c_sha256": COMPLETE_APPLICATION_C_SHA256[name],
        "frontend_revision": LLEQ_COMMIT,
        "frontend_flags": list(frontend_flags),
        "phi_polarity_repair": repair_phi,
        "c99_frontend_repair": c99_mode,
        "parse_ir_sha256": PARSE_IR_SHA256,
        "driver_sha256": RUN_BENCHMARK_SHA256,
        "egglog_python": EGGLOG_PYTHON_VERSION,
        "schedule": [5, 1, 3],
        "boundary": "native LLVM/REV and original driver decisions with egglog-python API compatibility port",
        "proof_validation": "not-run",
    }
    egraph = None
    try:
        lleq = args.lleq.resolve()
        if c99_mode:
            pair = c99.build_plugins(lleq, args.llvm_config.resolve(), evidence / "c99-pair")
            opt, plugin, llvm_version = Path(pair["opt"]), Path(pair["candidate_plugin"]), pair["llvm_version"]
            manifest["c99_pair"] = pair
        elif args.rev_plugin is None:
            opt, plugin, llvm_version = build_rev_plugin(
                lleq, args.llvm_config.resolve(), evidence / "rev-plugin.so", repair_phi_polarity=repair_phi
            )
            if repair_phi:
                repair_receipt = evidence / "phi-repair/diagnostic.json"
                manifest["phi_repair_evidence"] = {
                    "path": str(repair_receipt),
                    "sha256": hashlib.sha256(repair_receipt.read_bytes()).hexdigest(),
                    "source_patch": json.loads(repair_receipt.read_text()),
                }
        else:
            read_verified(lleq / "llvm/lib/Analysis/REVPass.cpp", REV_PASS_SHA256)
            read_verified(lleq / "llvm/include/llvm/Analysis/REVPass.h", REV_PASS_HEADER_SHA256)
            opt = Path(command_output((str(args.llvm_config.resolve()), "--bindir"))) / "opt"
            plugin = args.rev_plugin.resolve()
            llvm_version = command_output((str(args.llvm_config.resolve()), "--version"))
        manifest.update(llvm_version=llvm_version, rev_plugin_sha256=hashlib.sha256(plugin.read_bytes()).hexdigest())
        if c99_mode:
            baseline = application_fir(
                artifact,
                opt,
                Path(pair["baseline_plugin"]),
                name,
                evidence / "baseline-frontend",
                complete=True,
                frontend_flags=frontend_flags,
            )
        firs = application_fir(
            artifact,
            opt,
            plugin,
            name,
            evidence / "frontend",
            complete=True,
            frontend_flags=frontend_flags,
            **({"c99_frontend_repair": True} if c99_mode else {}),
        )
        assert isinstance(firs, list)
        if c99_mode:
            assert isinstance(baseline, list)
            manifest["fresh_frontend_comparison"] = c99.compare_frontends(
                baseline, firs, evidence / "baseline-frontend", evidence / "frontend"
            )
        references = {
            key: reference_fir(opt, plugin, artifact / f"analysis/{key}.ll", key) for key in REFERENCE_ANALYSIS_SHA256
        }
        adapted = evidence / "parseIR.py"
        adapted.write_text(adapt_parse_ir(parse_ir_source))
        manifest["adapted_parse_ir_sha256"] = hashlib.sha256(adapted.read_bytes()).hexdigest()
        parse_ir = import_parse_ir(adapted)
        egraph = parse_ir.egraph
        add_reference_rules(parse_ir, egraph, references)
        contexts = record_complete_regions(parse_ir, egraph, firs, name, evidence, manifest)
        if [row["index"] for row in manifest["regions"]] != list(range(len(firs))):
            raise ValueError("an ordered native region was omitted")
        source = normalize_recording(egraph.as_egglog_string, contexts) if contexts else egraph.as_egglog_string
        write_or_check(args.output, source, False)
        manifest["standalone_sha256"] = hashlib.sha256(args.output.read_bytes()).hexdigest()
        target = EXPECTED_KERNEL[name]
        manifest["source_complete"] = any(row.get("kernel") == target for row in manifest["regions"])
        if not manifest["source_complete"]:
            raise ValueError(f"{name}: all {len(firs)} regions processed, but intended {target} translation was absent")
    except Exception as error:
        manifest["reason"] = f"{type(error).__name__}: {error}"
        raise
    finally:
        if egraph is not None:
            (evidence / "native-session.egg").write_text(egraph.as_egglog_string)
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.with_suffix(".manifest.json").write_text(json.dumps(manifest, indent=2, default=str) + "\n")
    return 0


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
    if args.complete:
        return record_complete(args, artifact, parse_ir_source, benchmarks)
    if any(name in APPLICATION_C_SHA256 for name in benchmarks) and args.source_evidence is None:
        raise ValueError("original-C SpMV recording requires --source-evidence for complete frontend accounting")
    application_hashes: dict[str, str] = {}
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
            if benchmark in APPLICATION_C_SHA256:
                fir = cast(
                    str,
                    application_fir(artifact, opt, rev_plugin, benchmark, args.source_evidence.resolve() / benchmark),
                )
                application_hashes[benchmark] = sha256_text(fir)
            else:
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
            ";; Normalize temporary lets and give scoped rulesets stable per-workload names;",
            ";; preserve each ordinary extraction, including its arguments and push/pop scope.",
            *(
                f";; Original-C application {name}: C SHA-256 {APPLICATION_C_SHA256[name]}; FIR SHA-256 {digest}."
                for name, digest in application_hashes.items()
            ),
            *(
                [
                    ";; These application FIR inputs use the artifact's C/frontend flags on native LLVM, "
                    "not REVTest snapshots or Docker."
                ]
                if application_hashes
                else []
            ),
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
