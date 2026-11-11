"""Source-pinned C99 materialization, paired compilation and exact FIR comparison.

The CLI only materializes source. Native callers must run build_plugins below
an outer process guard. The PHI materializer owns original source/header pins;
source capture and ordinary admission remain separate operations.
"""

from __future__ import annotations

import argparse
import difflib
import hashlib
import json
import os
import re
from pathlib import Path
from typing import Any

from scripts import speq_phi_diagnostic as phi
from scripts.paper_benchmarks.record_speq import PARSE_IR_SHA256

SUPPORT = Path(__file__).with_name("paper_benchmarks")
ENABLE_ENV = "SPEQ_REV_C99_DIAGNOSTIC"
CONTRACT = "polybench-gemm-address-v1"
FUNCTION = "polybench_gemm"
FRONTEND_FLAGS = ("-D_FORTIFY_SOURCE=0", "-DPOLYBENCH_USE_C99_PROTO")


def candidate_rev(original: str, function: str) -> str:
    """Bind the exact fragment into pinned PHI-repaired REV, without modifying IR."""
    if not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9.]*", function):
        raise ValueError("diagnostic requires one explicit simple LLVM function name")
    repaired = phi.patched_rev(original)
    fragment = (SUPPORT / "speq_c99_fir.inc").read_text()
    first = repaired.index("class Lambda {")
    last = repaired.index("Value *findLiveOut(", first)
    before, body, after = repaired[:first], repaired[first:last], repaired[last:]
    replacements = {
        "DenseMap<Value *, Tensor *> &TM, DenseMap<Value *, LevelBounds> &LM)": (
            "DenseMap<Value *, Tensor *> &TM, DenseMap<Value *, LevelBounds> &LM, Function &F)"
        ),
        "TensorMap(TM), LevelMap(LM) {}": "TensorMap(TM), LevelMap(LM), C99(LI, SE, MSSA.getDomTree(), F,\n"
        f'            std::getenv("{ENABLE_ENV}") && F.getName() == "{function}") {{}}',
        '    return Out;\n    //    llvm_unreachable("val doesn\'t exist in tensor map.");': (
            "    std::string C99Type = C99.memoryType(I);\n"
            "    if (!C99Type.empty()) return C99Type;\n"
            '    return Out;\n    //    llvm_unreachable("val doesn\'t exist in tensor map.");'
        ),
        "    auto *Header = L.getHeader();\n": "    auto *Header = L.getHeader();\n    C99.prelude(L, OUTS);\n",
        "        LoopBody.push_back(&*I);\n": (
            "        LoopBody.push_back(&*I);\n        if (C99.emit(*I, OUTS)) continue;\n"
        ),
        "  DenseMap<Value *, LevelBounds> &LevelMap;\n": (
            "  DenseMap<Value *, LevelBounds> &LevelMap;\n  C99AddressFIR C99;\n"
        ),
    }
    for old, new in replacements.items():
        if body.count(old) != 1:
            raise ValueError(f"C99 REV substitution boundary changed: {old!r}")
        body = body.replace(old, new, 1)
    invocation = "  Lambda Lam(LI, SE, MSSA, TensorMap, LevelMap);"
    if after.count(invocation) != 1:
        raise ValueError("C99 Lambda invocation boundary changed")
    after = after.replace(invocation, "  Lambda Lam(LI, SE, MSSA, TensorMap, LevelMap, F);", 1)
    entry = "REVInfo REVPass::run(Function &F, FunctionAnalysisManager &AM) {\n"
    if after.count(entry) != 1:
        raise ValueError("C99 REV entry boundary changed")
    after = after.replace(
        entry,
        entry + f'  if (const char *Enabled = std::getenv("{ENABLE_ENV}")) {{\n'
        '    if (StringRef(Enabled) != "1")\n'
        '      report_fatal_error("REV C99 diagnostic enable value must be 1");\n'
        f'    Function *Selected = F.getParent()->getFunction("{function}");\n'
        "    if (!Selected || Selected->isDeclaration())\n"
        '      report_fatal_error("REV C99 selected definition is missing");\n'
        "    // LLVM module verification requires unique global/function names.\n"
        "  }\n",
        1,
    )
    return '#include <cstdlib>\n#include "llvm/IR/Module.h"\n' + before + fragment + "\n" + body + after


def fixture_cases() -> dict[str, tuple[str, str | None]]:
    """Use actual LLVM mutations of one guarded kernel as discriminating controls."""
    original = (SUPPORT / "speq_c99_fixture.ll").read_text()
    cases: dict[str, tuple[str, str | None]] = {"guarded_stride": (original, None)}
    mutations = {
        "nonzero_offset": (
            "  %element = getelementptr inbounds double, ptr %row.ptr, i64 %j64",
            "  %shifted = add nuw nsw i64 %j64, 3\n"
            "  %element = getelementptr inbounds double, ptr %row.ptr, i64 %shifted",
            None,
        ),
        "different_stride": (
            "%row.offset = mul nuw nsw i64 %row64, %n64",
            "%wide.stride = add nuw nsw i64 %n64, 7\n  %row.offset = mul nuw nsw i64 %row64, %wide.stride",
            None,
        ),
        "negative_offset": (
            "ptr %row.ptr, i64 %j64",
            "ptr %row.ptr, i64 -1",
            "negative index",
        ),
        "unguarded_zext": (
            "%row.valid = icmp sge i32 %row, 0",
            "%row.valid = icmp sge i32 %row, -1",
            "nonnegativity proof",
        ),
        "truncation": (
            "%j64 = zext i32 %j to i64",
            "%small = trunc i32 %j to i8\n  %j64 = zext i8 %small to i64",
            "preserve this cast",
        ),
        "wrapping_sum": (
            "%row.offset = mul nuw nsw i64 %row64, %n64",
            "%row.offset = add i64 %row64, 9223372036854775807",
            "may wrap",
        ),
        "external_load": (
            "%n64 = zext i32 %n to i64",
            "%n64 = load i64, ptr @stride",
            "external definition",
        ),
        "mixed_memory_type": (
            "%old = load double, ptr %element, align 8",
            "%wrong = load i32, ptr %element, align 4\n  %old = load double, ptr %element, align 8",
            "incompatible load",
        ),
        "non_inbounds": (
            "%element = getelementptr inbounds double",
            "%element = getelementptr double",
            "incompatible GEP",
        ),
        "pointer_escape": (
            "%old = load double, ptr %element, align 8",
            "call void @escape(ptr %C)\n  %old = load double, ptr %element, align 8",
            "escapes",
        ),
        "non_i64_index": (
            "ptr %row.ptr, i64 %j64",
            "ptr %row.ptr, i32 %j",
            "index is not i64",
        ),
        "narrow_pointer_layout": (
            'target datalayout = "e-p:64:64-i64:64-n8:16:32:64-S128"',
            'target datalayout = "e-p:64:64:64:32-i64:64-n8:16:32:64-S128"',
            "64-bit pointer index layout",
        ),
        "opaque_external_phi": (
            "preheader:\n  br label %body",
            "preheader:\n  %stride.phi = phi i64 [ %n64, %rowguard ]\n  br label %body",
            "external definition",
        ),
        "reserved_name": (
            "%row.offset",
            "%reproduction.c99.offset.0",
            "reserved diagnostic temporary",
        ),
    }
    for name, (old, new, error) in mutations.items():
        if old not in original:
            raise ValueError(f"C99 fixture mutation boundary changed: {name}")
        source = original.replace(old, new).replace("@guarded_stride(", f"@{name}(", 1)
        if name == "external_load":
            source += "\n@stride = external global i64\n"
        if name == "pointer_escape":
            source += "\ndeclare void @escape(ptr)\n"
        if name == "opaque_external_phi":
            source = source.replace("mul nuw nsw i64 %row64, %n64", "mul nuw nsw i64 %row64, %stride.phi")
        cases[name] = (source, error)
    cases["unsupported_i16"] = (
        original.replace("i32", "i16").replace("@guarded_stride(", "@unsupported_i16("),
        "preserve this cast",
    )
    return cases


def materialize(source: Path, output: Path, function: str) -> dict:
    """Reuse PHI evidence, retain a separate disabled candidate and exact-fragment gates."""
    source, output = source.resolve(), output.resolve()
    if output.exists() or output.is_relative_to(source):
        raise ValueError("diagnostic output must be fresh and outside original source")
    original = (source / "llvm/lib/Analysis/REVPass.cpp").read_text()
    candidate = candidate_rev(original, function)
    phi_record = phi.materialize(source, output / "phi")
    template = (SUPPORT / "speq_c99_harness.cpp").read_text()
    if template.count("// INSERT_EXACT_C99_FRAGMENT") != 1:
        raise ValueError("C99 harness substitution boundary changed")
    fragment = (SUPPORT / "speq_c99_fir.inc").read_text()
    files = {
        "candidate/llvm/lib/Analysis/REVPass.cpp": candidate,
        "candidate/llvm/include/llvm/Analysis/REVPass.h": (output / "phi/original/REVPass.h").read_text(),
        "candidate/llvm/include/llvm/Analysis/MemorySSA.h": (output / "phi/original/MemorySSA.h").read_text(),
        "c99-harness.cpp": template.replace("// INSERT_EXACT_C99_FRAGMENT", fragment),
        "c99-fragment.inc": fragment,
        "c99-candidate.patch": "".join(
            difflib.unified_diff(
                phi.patched_rev(original).splitlines(True),
                candidate.splitlines(True),
                fromfile="phi/llvm/lib/Analysis/REVPass.cpp",
                tofile="candidate/llvm/lib/Analysis/REVPass.cpp",
            )
        ),
    }
    cases = fixture_cases()
    files.update({f"fixtures/{name}.ll": text for name, (text, _) in cases.items()})
    for relative, text in files.items():
        destination = output / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_text(text)
    record = {
        "status": "diagnostic-materialized-unrun",
        "native_execution": False,
        "corpus_admission": False,
        "selected_function": function,
        "candidate_default": "disabled",
        "parser_contract_sha256": PARSE_IR_SHA256,
        "enable_environment": {ENABLE_ENV: "1"},
        "original_source": str(source),
        "phi_evidence": phi_record,
        "domain": "dominating pure closure, nonnegative bounded same-double i64 inbounds address chains, typed memory",
        "unchanged": [
            "source C",
            "LLVM input module",
            "frontend passes",
            "other functions",
            "reference rules",
            "5/1/3 schedule",
        ],
        "gates": {
            name: {"expected_exit": "zero" if error is None else "nonzero", "stderr_contains": error}
            for name, (_, error) in cases.items()
        },
        "required_native_gates": [
            "verify original failure and exact-fragment positive/negative fixture results",
            "verify candidate disabled matches PHI baseline for all four reference FIR hashes",
            "verify enabling missing selected function fails, unrelated function FIR stays unchanged",
            "verify enabled retained GEMM has complete scalar closure, flat addresses and typed memory",
            "original complete parent then standalone ordinary replay (separate admission)",
        ],
        "implementation_hashes": {
            str(path.relative_to(Path(__file__).parent.parent)): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in (
                Path(__file__),
                Path(phi.__file__),
                SUPPORT / "speq_c99_fir.inc",
                SUPPORT / "speq_c99_harness.cpp",
                SUPPORT / "speq_c99_fixture.ll",
            )
        },
        "files": {name: hashlib.sha256((output / name).read_bytes()).hexdigest() for name in files},
    }
    (output / "diagnostic.json").write_text(json.dumps(record, indent=2) + "\n")
    return record


def build_plugins(source: Path, llvm_config: Path, output: Path) -> dict[str, Any]:
    """Build one fresh, pinned PHI/candidate pair; callers own the native guard.

    Both builds consume only this materialization. Its source bytes and the
    tracked plugin wrapper are checked again after compilation. No arbitrary
    prebuilt library can stand in for either half of the comparison.
    """
    from scripts.paper_benchmarks.record_speq import compile_rev_plugin

    if ENABLE_ENV in os.environ:
        raise ValueError("C99 must be disabled at plugin preparation entry")
    output = output.resolve()
    if output.exists():
        raise ValueError("paired plugin preparation requires fresh output")
    materialized = output / "source"
    materialize(source, materialized, FUNCTION)
    source_hashes = {
        str(path.relative_to(materialized)): hashlib.sha256(path.read_bytes()).hexdigest()
        for path in sorted(materialized.rglob("*"))
        if path.is_file()
    }
    wrapper = SUPPORT / "speq_rev_plugin.cpp"
    wrapper_hash = hashlib.sha256(wrapper.read_bytes()).hexdigest()
    opt, baseline, version = compile_rev_plugin(materialized / "phi/patched", llvm_config, output / "phi.so")
    candidate_opt, candidate, candidate_version = compile_rev_plugin(
        materialized / "candidate", llvm_config, output / "candidate.so"
    )
    if (opt, version) != (candidate_opt, candidate_version) or version != "17.0.6":
        raise ValueError("paired plugins require the same LLVM 17.0.6 tools")
    observed = {
        str(path.relative_to(materialized)): hashlib.sha256(path.read_bytes()).hexdigest()
        for path in sorted(materialized.rglob("*"))
        if path.is_file()
    }
    if observed != source_hashes or hashlib.sha256(wrapper.read_bytes()).hexdigest() != wrapper_hash:
        raise ValueError("paired plugin source changed during compilation")
    receipt = materialized / "diagnostic.json"
    result = {
        "contract": CONTRACT,
        "selected_function": FUNCTION,
        "opt": str(opt),
        "baseline_plugin": str(baseline),
        "candidate_plugin": str(candidate),
        "llvm_version": version,
        "materialization": {"path": str(receipt), "sha256": hashlib.sha256(receipt.read_bytes()).hexdigest()},
        "source_files": source_hashes,
        "wrapper_sha256": wrapper_hash,
        "artifacts": {str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in (baseline, candidate)},
    }
    (output / "plugins.json").write_text(json.dumps(result, indent=2) + "\n")
    return result


def compare_selected_region(baseline: str, candidate: str) -> dict[str, Any]:
    """Derive state names from the PHI-only run and allow only the C99 edits."""
    folds = re.findall(r"^.* = fold .*?$", baseline, re.MULTILINE)
    shapes = [
        r"\((%C\.\d+)\) = fold \(ptr (%C)\) %for.body8 Range\(i32 0, i32 %nj\)",
        r"\((%C\.\d+)\) = fold \(ptr (%C)\) %for.body16 Range\(i32 0, i32 %nj\)",
        r"\((%C\.\d+)\) = fold \(ptr (%C\.\d+)\) %for.body13 Range\(i32 0, i32 %nk\)",
        r"\((%C\.\d+)\) = fold \(ptr (%C)\) %for.body Range\(i32 0, i32 %ni\)",
    ]
    if len(folds) != len(shapes):
        raise ValueError("fresh PHI baseline does not retain the four GEMM folds")
    matches = [re.fullmatch(shape, fold) for shape, fold in zip(shapes, folds, strict=True)]
    if any(match is None for match in matches):
        raise ValueError("fresh PHI baseline GEMM order, bounds, or state shape differs")
    matched = [match for match in matches if match is not None]
    first, second, inner, outer = [match[1] for match in matched]
    alias = matched[2][2]
    if len({first, second, inner, outer, alias}) != 5:
        raise ValueError("fresh PHI baseline aliases distinct memory definitions")
    expected_edges = [
        f"  {inner} = if ptr %cmp71 then {second} else %C",
        f"  {alias} = if ptr %cmp71 then {first} else %C",
        f"  {outer} = if ptr %cmp125 then {inner} else {alias}",
    ]
    if re.findall(r"^.* = if ptr .*?$", baseline, re.MULTILINE) != expected_edges:
        raise ValueError("fresh PHI baseline memory-state edges differ")
    for store in (
        f"  {first} =  store double %mul, ptr %arrayidx10, align 8\n",
        f"  {second} =  store double %10, ptr %arrayidx30, align 8\n",
    ):
        if baseline.count(store) != 1:
            raise ValueError("fresh PHI baseline fold output is not its original store")
    if baseline.count("%for.body13 = λ ptr %C, i32 %k.06 .\n" + expected_edges[0] + "\n") != 1:
        raise ValueError("inner memory edge moved outside its loop")
    outer_prefix = (
        "%for.body = λ ptr %C, i32 %i.09 .\n  %cmp71 = icmp sgt i32 %nj, 0\n"
        + expected_edges[1]
        + "\n  %cmp125 = icmp sgt i32 %nk, 0\n"
        + expected_edges[2]
        + "\n"
    )
    if baseline.count(outer_prefix) != 1:
        raise ValueError("outer memory edges or guards changed")
    expected = baseline
    for old, new, count in [
        ("λ ptr %C", "λ ptr 1 double %C", 4),
        ("fold (ptr ", "fold (ptr 1 double ", 4),
        ("if ptr ", "if ptr 1 double ", 3),
    ]:
        if expected.count(old) != count:
            raise ValueError("typed-memory boundary changed: " + old)
        expected = expected.replace(old, new)
    for header, closure in [
        ("%for.body8 = λ ptr 1 double %C, i32 %j.02 .\n", "  %0 = zext i32 %nj to i64\n"),
        ("%for.body16 = λ ptr 1 double %C, i32 %j.14 .\n", "  %1 = zext i32 %nk to i64\n  %0 = zext i32 %nj to i64\n"),
    ]:
        if expected.count(header) != 1:
            raise ValueError("dominating-closure boundary changed")
        expected = expected.replace(header, header + closure)
    for index, (destination, intermediate, root, left, right) in enumerate(
        [
            ("arrayidx10", "arrayidx", "C", "2", "idxprom9"),
            ("arrayidx20", "arrayidx18", "A", "4", "idxprom19"),
            ("arrayidx25", "arrayidx23", "B", "6", "idxprom24"),
            ("arrayidx30", "arrayidx28", "C", "8", "idxprom24"),
        ]
    ):
        old = f"  %{destination} = getelementptr inbounds double, ptr %{intermediate}, i64 %{right}\n"
        offset = f"%reproduction.c99.offset.{index}"
        new = (
            f"  {offset} = add nsw i64 %{left}, %{right}\n"
            f"  %{destination} = getelementptr inbounds double, ptr %{root}, i64 {offset}\n"
        )
        if expected.count(old) != 1:
            raise ValueError("chained-GEP boundary changed: " + destination)
        expected = expected.replace(old, new)
    if candidate != expected:
        raise ValueError("candidate FIR differs from the exact edits to its fresh PHI-only baseline")
    return {
        "folds": folds,
        "memory_state_edges": expected_edges,
        "memory_alias": alias,
        "baseline_sha256": hashlib.sha256(baseline.encode()).hexdigest(),
        "candidate_sha256": hashlib.sha256(candidate.encode()).hexdigest(),
        "variable_renaming": False,
    }


def compare_frontends(
    baseline: list[str], candidate: list[str], baseline_directory: Path, candidate_directory: Path
) -> dict[str, Any]:
    """Preserve all unselected regions and compare identical LLVM input/output IR."""
    if len(baseline) != 3 or len(candidate) != 3:
        raise ValueError("fresh frontends must retain all three ordered application regions")
    if baseline[:2] != candidate[:2]:
        raise ValueError("an unselected region changed; no temporary-name normalization is allowed")
    directories = [Path(baseline_directory), Path(candidate_directory)]
    inputs = [(directory / "input.ll").read_bytes() for directory in directories]
    if inputs[0] != inputs[1]:
        raise ValueError("paired original-C clang inputs differ")
    analyses = []
    bodies = []
    for directory in directories:
        data = (directory / "analysis.ll").read_bytes()
        prefix = f"; ModuleID = '{directory / 'input.ll'}'\n".encode()
        if not data.startswith(prefix):
            raise ValueError("analysis module comment has an unexpected origin")
        analyses.append(hashlib.sha256(data).hexdigest())
        bodies.append(data[len(prefix) :])
    if bodies[0] != bodies[1]:
        raise ValueError("paired pipelines changed LLVM IR beyond their exact ModuleID path comment")
    selected = compare_selected_region(baseline[2], candidate[2])
    return {
        "status": "exact-scoped-repair",
        "ordered_regions": 3,
        "unselected_regions_byte_identical": [0, 1],
        "selected": selected,
        "clang_input_sha256": hashlib.sha256(inputs[0]).hexdigest(),
        "analysis_sha256": analyses,
        "analysis_body_sha256": hashlib.sha256(bodies[0]).hexdigest(),
        "only_ignored_llvm_bytes": "exact first ModuleID comment naming each retained input.ll; no FIR normalization",
        "no_output_substitution": True,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--function", required=True)
    args = parser.parse_args()
    print(json.dumps(materialize(args.source, args.output, args.function), indent=2))


if __name__ == "__main__":
    main()
