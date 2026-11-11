// Diagnostic only. Compile against the freshly prepared generated selector and
// its PRIVATE common/Legalizer.cpp. This never executes a target instruction:
// LLVM constant-folds the portable output and compares every resulting lane.
#include "HexLegalizer.cpp"
#include "llvm/Analysis/ConstantFolding.h"
#include "llvm/IR/IRBuilder.h"
#include <cstdint>
#include <iostream>
#include <string>
#include <vector>

using namespace llvm;

static Constant *vectorValue(LLVMContext &C, unsigned Bits,
                             const std::vector<uint64_t> &Values) {
  std::vector<Constant *> Elements;
  for (auto V : Values)
    Elements.push_back(ConstantInt::get(IntegerType::get(C, Bits), V));
  return ConstantVector::get(Elements);
}

static Function *functionWithCall(Module &M, const std::string &Name,
                                  Type *Result, std::vector<Value *> Args) {
  std::vector<Type *> Types;
  for (auto *Arg : Args) Types.push_back(Arg->getType());
  auto *Source = Function::Create(FunctionType::get(Result, Types, false),
                                  Function::ExternalLinkage, Name, M);
  auto *F = Function::Create(FunctionType::get(Result, false),
                             Function::ExternalLinkage, "hydride.diagnostic", M);
  IRBuilder<> B(BasicBlock::Create(M.getContext(), "entry", F));
  B.CreateRet(B.CreateCall(Source, Args));
  return F;
}

static void lowerAndCheck(Module &M, Function *F,
                          const std::vector<uint64_t> &Expected) {
  HexLegalizationPass Pass;
  Pass.runOnFunction(*F); // Includes the actual pre-ADCE verifier.
  if (verifyFunction(*F, &errs())) report_fatal_error("harness: invalid result");
  for (auto &BB : *F) {
    for (auto It = BB.begin(); It != BB.end();) {
      Instruction *I = &*It++;
      if (isa<ReturnInst>(I)) continue;
      if (auto *Folded = ConstantFoldInstruction(I, M.getDataLayout())) {
        I->replaceAllUsesWith(Folded);
        I->eraseFromParent();
      }
    }
  }
  auto *Ret = cast<ReturnInst>(F->back().getTerminator());
  auto *Result = dyn_cast<Constant>(Ret->getReturnValue());
  if (!Result) report_fatal_error("harness: portable lowering did not fold");
  // IRBuilder can leave a bitcast ConstantExpr directly in the return operand.
  Result = ConstantFoldConstant(Result, M.getDataLayout());
  auto *Ty = dyn_cast<FixedVectorType>(Result->getType());
  if (!Ty || Ty->getNumElements() != Expected.size())
    report_fatal_error("harness: result shape mismatch");
  for (unsigned I = 0; I < Expected.size(); ++I) {
    auto *Lane = dyn_cast_or_null<ConstantInt>(Result->getAggregateElement(I));
    if (!Lane || Lane->getZExtValue() != Expected[I])
      report_fatal_error("harness: result lane mismatch");
  }
}

static void checkShift(uint32_t Shift, const std::string &Suffix = "") {
  LLVMContext C;
  Module M("shift", C);
  M.setDataLayout("e-p:64:64");
  std::vector<uint64_t> Words, Expected;
  for (unsigned I = 0; I < 32; ++I) {
    uint32_t Word = 0x80000001u + I * 1234567u;
    Words.push_back(Word);
    Expected.push_back(Shift >= 32 ? 0 : Word >> Shift);
  }
  std::vector<Value *> Args = {vectorValue(C, 32, {31}), vectorValue(C, 32, Words),
                               vectorValue(C, 32, {Shift})};
  for (unsigned V : {1024, 1024, 0, 1024, 32, 0})
    Args.push_back(ConstantInt::get(Type::getInt32Ty(C), V));
  auto *F = functionWithCall(M, "llvm.hydride.hexagon_V6_vlsrw_128B_dsl" + Suffix,
                             FixedVectorType::get(Type::getInt32Ty(C), 32), Args);
  lowerAndCheck(M, F, Expected);
}

static void checkHalf(bool High) {
  LLVMContext C;
  Module M("half", C);
  M.setDataLayout("e-p:64:64");
  std::vector<uint64_t> Words, Expected;
  for (unsigned I = 0; I < 64; ++I) Words.push_back(0x9A430000u + I * 123u);
  for (unsigned Byte = 0; Byte < 128; ++Byte)
    Expected.push_back((Words[(High ? 32 : 0) + Byte / 4] >> (8 * (Byte % 4))) & 255);
  std::vector<Value *> Args = {vectorValue(C, 32, Words)};
  std::vector<unsigned> Constants = {1024, 1024, 0, 1024, 8};
  if (High) Constants.push_back(1024);
  Constants.push_back(0);
  for (auto V : Constants) Args.push_back(ConstantInt::get(Type::getInt32Ty(C), V));
  auto *F = functionWithCall(M, High ? "llvm.hydride.hexagon_V6_lo_128B_dsl"
                                    : "llvm.hydride.hexagon_V6_vassign_128B_dsl",
                             FixedVectorType::get(Type::getInt8Ty(C), 128), Args);
  lowerAndCheck(M, F, Expected);
}

static void checkSwizzle(unsigned Width, unsigned Element, unsigned Stride,
                          bool Bad = false) {
  LLVMContext C;
  Module M("swizzle", C);
  M.setDataLayout("e-p:64:64");
  std::vector<uint64_t> Values, Expected;
  for (unsigned I = 0; I < Width / Element; ++I) Values.push_back(I);
  // Original formal interleaves the two input halves at element granularity.
  for (unsigned I = 0; I < Values.size() / 2; ++I) {
    Expected.push_back(Values[I]);
    Expected.push_back(Values[I + Values.size() / 2]);
  }
  std::vector<Value *> Args = {vectorValue(C, Element, Values)};
  for (unsigned V : {Width, Element * 2, Bad ? 1u : 0u, Element * 2, Element, Stride, 2u, 0u})
    Args.push_back(ConstantInt::get(Type::getInt32Ty(C), V));
  auto *F = functionWithCall(M, "llvm.hydride.hvx_swizzle_1_dsl",
                             FixedVectorType::get(IntegerType::get(C, Element), Width / Element), Args);
  lowerAndCheck(M, F, Expected);
}

static void checkPermutation(const std::string &Mode) {
  LLVMContext C;
  Module M("permutation", C);
  M.setDataLayout("e-p:64:64");
  Type *I32 = Type::getInt32Ty(C);
  auto *F = functionWithCall(M, "original", I32,
                             {ConstantInt::get(I32, 1), ConstantInt::get(I32, 2)});
  auto *Call = cast<CallInst>(&F->front().front());
  auto *Target = Function::Create(
      FunctionType::get(I32, {Mode == "width" ? Type::getInt64Ty(C) : I32, I32}, false),
      Function::ExternalLinkage, "target", M);
  std::vector<int> Map = {0, 1};
  if (Mode == "missing") Map = {0, -1};
  if (Mode == "duplicate") Map = {0, 0};
  if (Mode == "negative") Map = {0, -2};
  if (Mode == "large") Map = {0, 2};
  if (Mode == "short") Map = {0};
  HexLegalizer Legalizer;
  auto Args = Legalizer.getArgsAfterPermutation(Call, Target, Map, Call);
  if (Mode != "valid") report_fatal_error("harness: malformed permutation accepted");
  if (Args.size() != 2 || Args[0] != Call->getArgOperand(0) || Args[1] != Call->getArgOperand(1))
    report_fatal_error("harness: valid permutation changed operands");
}

int main(int Argc, char **Argv) {
  const std::string Mode = Argc > 1 ? Argv[1] : "all";
  if (Mode == "invalid-ir") {
    LLVMContext C;
    Module M("invalid", C);
    auto *F = Function::Create(FunctionType::get(Type::getInt32Ty(C), false),
                               Function::ExternalLinkage, "hydride.invalid", M);
    ReturnInst::Create(C, ConstantInt::get(Type::getInt16Ty(C), 7), BasicBlock::Create(C, "entry", F));
    HexLegalizationPass Pass;
    Pass.runOnFunction(*F);
    errs() << "ADCE_WOULD_START\n";
    return 1; // Reaching this point is always a test failure.
  }
  if (Mode == "bad-swizzle") { checkSwizzle(1024, 16, 32, true); return 1; }
  if (Mode != "all") { checkPermutation(Mode); return 0; }
  for (uint32_t Shift : {0u, 1u, 17u, 30u, 31u, 32u, 33u, 63u, 64u, 0x80000000u, 0xffffffffu})
    checkShift(Shift);
  checkShift(17, ".1");
  checkHalf(false);
  checkHalf(true);
  checkSwizzle(2048, 32, 32);
  checkSwizzle(2048, 16, 64);
  checkSwizzle(1024, 16, 32);
  checkSwizzle(1024, 8, 64);
  checkPermutation("valid");
  std::cout << "19 portable-lowering/permutation checks passed; no target execution\n";
}
