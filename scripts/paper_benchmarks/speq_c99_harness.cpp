// Analysis-only host harness: verifies LLVM IR, never executes input functions.
#include "llvm/ADT/APInt.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Analysis/AssumptionCache.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Verifier.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Support/raw_ostream.h"
using namespace llvm;

// INSERT_EXACT_C99_FRAGMENT

int main(int argc, char **argv) {
  if (argc != 3) return 2;
  LLVMContext Context;
  SMDiagnostic Error;
  auto M = parseIRFile(argv[1], Error, Context);
  if (!M) { Error.print(argv[0], errs()); return 2; }
  if (verifyModule(*M, &errs())) return 2;
  Function *F = M->getFunction(argv[2]);
  if (!F || F->isDeclaration()) return 2;
  std::string Before;
  raw_string_ostream Saved(Before);
  M->print(Saved, nullptr);
  DominatorTree DT(*F);
  LoopInfo LI(DT);
  AssumptionCache AC(*F);
  TargetLibraryInfoImpl TLII;
  TargetLibraryInfo TLI(TLII);
  ScalarEvolution SE(*F, TLI, AC, DT, LI);
  C99AddressFIR Probe(LI, SE, DT, *F, true);
  outs() << "memory-type: " << Probe.memoryType(F->getArg(0)) << "\n";
  for (Loop *L : LI.getLoopsInPreorder()) {
    outs() << "loop: " << L->getName() << "\n";
    Probe.prelude(*L, outs());
    for (BasicBlock *BB : L->blocks()) {
      if (LI.getLoopFor(BB) != L) continue;
      for (Instruction &I : *BB) {
        if (isa<PHINode>(&I) || I.isTerminator()) continue;
        if (!Probe.emit(I, outs())) outs() << I << "\n";
      }
    }
  }
  std::string After;
  raw_string_ostream Current(After);
  M->print(Current, nullptr);
  if (Before != After) return 3;
  outs() << "LLVM module unchanged\n";
  return 0;
}
