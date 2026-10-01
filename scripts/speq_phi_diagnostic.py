"""Materialize an isolated, opt-in REV PHI-polarity diagnostic; never run native tools.

This does not change source C, reference rules, the original recorder, or corpus
admission. A later guarded LLVM build must validate both the original failure and
the patched behavior before the compiler repair can be used for a capture.
"""

from __future__ import annotations

import argparse
import difflib
import hashlib
import json
from pathlib import Path

from scripts.paper_benchmarks.record_speq import REV_MEMORY_SSA_SHA256 as MEMORY_SSA_SHA256
from scripts.paper_benchmarks.record_speq import REV_PASS_HEADER_SHA256, REV_PASS_SHA256

SUPPORT = Path(__file__).with_name("paper_benchmarks")
BEGIN = "  template <class PHITy>\n  BranchInst *getPhiBr("
END = "  // a loop has a header/latch/exit blocks,"
EDGE_AWARE_PHI = """  template <class PHITy>
  BranchInst *getPhiBr(PHITy *Phi, BasicBlock **Then, BasicBlock **Else) {
    *Then = nullptr;
    *Else = nullptr;
    if (Phi->getNumIncomingValues() != 2)
      return nullptr;
    auto *BB1 = Phi->getIncomingBlock(0);
    auto *BB2 = Phi->getIncomingBlock(1);
    if (BB1 == BB2)
      return nullptr;
    BasicBlock *CommonDenom = DT.findNearestCommonDominator(BB1, BB2);
    if (!CommonDenom)
      return nullptr;
    auto *Br = dyn_cast<BranchInst>(CommonDenom->getTerminator());
    if (!Br || !Br->isConditional())
      return nullptr;
    const BasicBlock *Merge;
    if (const auto *MemPhi = dyn_cast<MemoryPhi>(Phi))
      Merge = MemPhi->getBlock();
    else
      Merge = cast<PHINode>(static_cast<const Value *>(Phi))->getParent();
    for (BasicBlock *Pred : {BB1, BB2}) {
      // A bypass arrives directly from the conditional branch's block. The
      // merge itself need not dominate that predecessor or the other arm.
      bool OnTrue = Pred == CommonDenom
                        ? Br->getSuccessor(0) == Merge
                        : Br->getSuccessor(0) != Merge &&
                              DT.dominates(Br->getSuccessor(0), Pred);
      bool OnFalse = Pred == CommonDenom
                         ? Br->getSuccessor(1) == Merge
                         : Br->getSuccessor(1) != Merge &&
                               DT.dominates(Br->getSuccessor(1), Pred);
      if (OnTrue == OnFalse)
        return nullptr;
      BasicBlock **Arm = OnTrue ? Then : Else;
      if (*Arm)
        return nullptr;
      *Arm = Pred;
    }
    return *Then && *Else ? Br : nullptr;
  }
"""


def patched_rev(source: str) -> str:
    """Apply only edge-aware PHI classification and an explicit unsupported-shape failure."""
    if hashlib.sha256(source.encode()).hexdigest() != REV_PASS_SHA256:
        raise ValueError("PHI diagnostic requires the exact pinned REVPass.cpp")
    first, last = source.index(BEGIN), source.index(END)
    patched = source[:first] + EDGE_AWARE_PHI + source[last:]
    original = "    BranchInst *Br = getPhiBr(Phi, &Then, &Else);\n"
    if patched.count(original) != 1:
        raise ValueError("REV translatePhi boundary changed")
    patched = patched.replace(
        original,
        original + '    if (!Br)\n      report_fatal_error("REV: unsupported PHI control-flow polarity");\n',
        1,
    )
    include = '#include "llvm/Support/Debug.h"\n'
    if patched.count(include) != 1:
        raise ValueError("REV include boundary changed")
    return patched.replace(include, include + '#include "llvm/Support/ErrorHandling.h"\n', 1)


def materialize(source: Path, output: Path) -> dict:
    """Keep immutable originals and a minimal patch beside exact-function LLVM harnesses."""
    source, output = source.resolve(), output.resolve()
    if output.exists() or output.is_relative_to(source):
        raise ValueError("diagnostic output must be fresh and outside the original source")
    cpp = source / "llvm/lib/Analysis/REVPass.cpp"
    header = source / "llvm/include/llvm/Analysis/REVPass.h"
    memory_header = source / "llvm/include/llvm/Analysis/MemorySSA.h"
    if hashlib.sha256(memory_header.read_bytes()).hexdigest() != MEMORY_SSA_SHA256:
        raise ValueError("PHI diagnostic requires the exact pinned custom MemorySSA.h")
    original = cpp.read_text()
    repaired = patched_rev(original)
    if hashlib.sha256(header.read_bytes()).hexdigest() != REV_PASS_HEADER_SHA256:
        raise ValueError("PHI diagnostic requires the exact pinned REVPass.h")
    template = (SUPPORT / "speq_phi_harness.cpp").read_text()
    if template.count("// INSERT_EXACT_GET_PHI_BR") != 1:
        raise ValueError("diagnostic harness substitution boundary changed")
    files = {
        "original/REVPass.cpp": original,
        "original/REVPass.h": header.read_text(),
        "original/MemorySSA.h": memory_header.read_text(),
        "patched/llvm/include/llvm/Analysis/MemorySSA.h": memory_header.read_text(),
        "patched/llvm/lib/Analysis/REVPass.cpp": repaired,
        "patched/llvm/include/llvm/Analysis/REVPass.h": header.read_text(),
        "phi-cases.ll": (SUPPORT / "speq_phi_fixtures.ll").read_text(),
        "phi-polarity.patch": "".join(
            difflib.unified_diff(
                original.splitlines(True),
                repaired.splitlines(True),
                fromfile="a/llvm/lib/Analysis/REVPass.cpp",
                tofile="b/llvm/lib/Analysis/REVPass.cpp",
            )
        ),
    }
    for label, body in (("original", original), ("patched", repaired)):
        method = body[body.index(BEGIN) : body.index(END)]
        files[label + "-phi-harness.cpp"] = template.replace("// INSERT_EXACT_GET_PHI_BR", method)
    output.mkdir(parents=True)
    for relative, content in files.items():
        path = output / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content)
    record = {
        "status": "diagnostic-materialized-unrun",
        "original_source": str(source),
        "native_execution": False,
        "corpus_admission": False,
        "scope": "PHI polarity only; source C, reference rules and standard frontend pipeline unchanged",
        "expected_original_harness": "nonzero: direct-true bypass polarity mismatch",
        "expected_patched_harness": "zero: all scalar and MemoryPhi predecessor-order cases pass",
        "files": {name: hashlib.sha256((output / name).read_bytes()).hexdigest() for name in files},
    }
    (output / "diagnostic.json").write_text(json.dumps(record, indent=2) + "\n")
    return record


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(materialize(args.source, args.output), indent=2))


if __name__ == "__main__":
    main()
