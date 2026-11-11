"""Materialize a disabled, source-pinned C99 REV candidate and native analysis gates.

No native tools, source capture, settings publication or admission run here. The
existing PHI materializer owns the original source/header checks and baseline.
"""

from __future__ import annotations

import argparse
import difflib
import hashlib
import json
import re
from pathlib import Path

from scripts import speq_phi_diagnostic as phi
from scripts.paper_benchmarks.record_speq import PARSE_IR_SHA256

SUPPORT = Path(__file__).with_name("paper_benchmarks")
ENABLE_ENV = "SPEQ_REV_C99_DIAGNOSTIC"


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


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--function", required=True)
    args = parser.parse_args()
    print(json.dumps(materialize(args.source, args.output, args.function), indent=2))


if __name__ == "__main__":
    main()
