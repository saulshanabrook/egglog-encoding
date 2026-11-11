// Native analysis diagnostic only. This host harness never executes input IR.
// Materialization inserts getPhiBr verbatim from the original/patched REV source.
#include "llvm/Analysis/AssumptionCache.h"
#include "llvm/Analysis/BasicAliasAnalysis.h"
#include "llvm/Analysis/MemorySSA.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Verifier.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Support/raw_ostream.h"
#include <utility>
using namespace llvm;

struct Probe {
  DominatorTree &DT;
  template <class PHITy>
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

};

int main(int argc, char **argv) {
  if (argc != 2) return 2;
  LLVMContext Context;
  SMDiagnostic Error;
  auto M = parseIRFile(argv[1], Error, Context);
  if (!M) { Error.print(argv[0], errs()); return 2; }
  if (verifyModule(*M, &errs())) return 2;
  unsigned Failures = 0, Checks = 0;
  for (Function &F : *M) {
    DominatorTree DT(F);
    Probe P{DT};
    TargetLibraryInfoImpl TLII;
    TargetLibraryInfo TLI(TLII);
    AssumptionCache AC(F);
    BasicAAResult BAA(M->getDataLayout(), F, TLI, AC, &DT);
    AAResults AA(TLI);
    AA.addAAResult(BAA);
    MemorySSA MSSA(F, &AA, &DT);
    BasicBlock *Merge = nullptr;
    for (BasicBlock &BB : F) if (BB.getName() == "merge") Merge = &BB;
    if (!Merge) return 2;
    auto *Scalar = dyn_cast<PHINode>(&*Merge->begin());
    auto *Memory = MSSA.getMemoryAccess(Merge);
    if (!Scalar || !Memory) return 2;
    auto Check = [&](auto *Phi, StringRef Kind) {
      BasicBlock *Then = nullptr, *Else = nullptr;
      BranchInst *Br = P.getPhiBr(Phi, &Then, &Else);
      bool Supported = !F.getName().starts_with("unsupported_");
      StringRef ExpectedTrue = F.getName().starts_with("direct_true") ? "entry" : "then";
      StringRef ExpectedFalse = F.getName().starts_with("direct_false") ? "entry" : "else";
      bool Okay = Supported ? Br && Then && Else &&
          Then->getName() == ExpectedTrue && Else->getName() == ExpectedFalse : !Br;
      ++Checks;
      if (!Okay) ++Failures;
      outs() << F.getName() << " " << Kind << " true="
             << (Then ? Then->getName() : "none") << " false="
             << (Else ? Else->getName() : "none") << " " << (Okay ? "PASS" : "FAIL") << "\n";
    };
    Check(Scalar, "scalar");
    Check(static_cast<const MemoryPhi *>(Memory), "memory-original-order");
    if (Memory->getNumIncomingValues() == 2) {
      auto *V0 = Memory->getIncomingValue(0), *V1 = Memory->getIncomingValue(1);
      auto *B0 = Memory->getIncomingBlock(0), *B1 = Memory->getIncomingBlock(1);
      Memory->setIncomingValue(0, V1); Memory->setIncomingBlock(0, B1);
      Memory->setIncomingValue(1, V0); Memory->setIncomingBlock(1, B0);
      MSSA.verifyMemorySSA();
      Check(static_cast<const MemoryPhi *>(Memory), "memory-reversed-order");
    }
  }
  outs() << "checks=" << Checks << " failures=" << Failures << "\n";
  return Failures ? 1 : 0;
}
