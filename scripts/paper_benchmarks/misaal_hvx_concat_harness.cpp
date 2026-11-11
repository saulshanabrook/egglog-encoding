// Host LLVM analysis only: no generated kernel or target-device code executes.
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/Analysis/ConstantFolding.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/raw_ostream.h"
#include <cstdlib>
#include <string>
#include <vector>

using namespace llvm;

class Legalizer {
public:
  DenseMap<Value *, Value *> InstToInstMap;
  SmallPtrSet<Instruction *, 16> ToBeRemoved;
  Value *getBitvectorOfRequiredType(Value *, Type *, Instruction *);
  bool lower(CallInst *CI) {
// INSERT_EXACT_CONCAT_FRAGMENT
    return false;
  }
};

// INSERT_EXACT_COMMON_ACCESSOR

static void require(bool condition, const char *message) {
  if (!condition) {
    errs() << "HARNESS_ASSERT: " << message << "\n";
    std::exit(2);
  }
}

// Evaluate the emitted LLVM DAG with LLVM's constant folder, not an alternative
// implementation of concat. The independent oracle below checks every lane.
static Constant *evaluate(Value *value, DenseMap<Value *, Constant *> &values,
                          const DataLayout &layout) {
  if (auto *constant = dyn_cast<Constant>(value))
    return constant;
  if (auto *known = values.lookup(value))
    return known;
  auto *instruction = dyn_cast<Instruction>(value);
  require(instruction != nullptr, "unbound emitted operand");
  SmallVector<Constant *, 4> operands;
  for (Value *operand : instruction->operands())
    operands.push_back(evaluate(operand, values, layout));
  Constant *result = ConstantFoldInstOperands(instruction, operands, layout);
  require(result != nullptr, "LLVM could not evaluate an emitted instruction");
  values[value] = result;
  return result;
}

static uint64_t exercise(Module &module, unsigned width, StringRef mode) {
  LLVMContext &context = module.getContext();
  unsigned repeat = 32 / width;
  Type *integer = IntegerType::get(context, width);
  Type *input = FixedVectorType::get(integer, 1);
  Type *output = FixedVectorType::get(integer, repeat);
  if (mode == "scalar-input") input = integer;
  if (mode == "input-lanes") input = FixedVectorType::get(integer, 2);
  if (mode == "input-element") input = FixedVectorType::get(Type::getFloatTy(context), 1);
  if (mode == "input-integer-width") input = FixedVectorType::get(IntegerType::get(context, width + 1), 1);
  if (mode == "input-scalable") input = VectorType::get(integer, ElementCount::getScalable(1));
  if (mode == "scalar-output") output = Type::getInt32Ty(context);
  if (mode == "output-lanes") output = FixedVectorType::get(integer, 1);
  if (mode == "output-element") output = FixedVectorType::get(IntegerType::get(context, width / 2), repeat);
  if (mode == "output-scalable") output = VectorType::get(integer, ElementCount::getScalable(repeat));
  auto *function = Function::Create(
      FunctionType::get(output, {input, input, Type::getInt32Ty(context)}, false),
      GlobalValue::ExternalLinkage, "fixture", module);
  auto *block = BasicBlock::Create(context, "entry", function);
  IRBuilder<> builder(block);
  Value *original = function->getArg(0);
  Value *replacement = function->getArg(1);
  Value *inputWidth = builder.getInt32(width);
  Value *outputWidth = builder.getInt32(32);
  if (mode == "input-width-value") inputWidth = builder.getInt32(width + 1);
  if (mode == "output-width-value") outputWidth = builder.getInt32(64);
  if (mode == "input-width-type") inputWidth = builder.getInt64(width);
  if (mode == "output-width-type") outputWidth = builder.getInt64(32);
  if (mode == "input-width-variable") inputWidth = function->getArg(2);
  if (mode == "output-width-variable") outputWidth = function->getArg(2);
  std::vector<Value *> arguments{original, inputWidth, outputWidth};
  if (mode == "arity-two") arguments.pop_back();
  if (mode == "arity-four") arguments.push_back(builder.getInt32(0));
  std::vector<Type *> types;
  for (Value *argument : arguments) types.push_back(argument->getType());
  std::string name = "llvm.hydride.hexagon_V6_interleave_" +
                     std::to_string(repeat) + "_128B_dsl";
  if (mode == "unrelated") name = "unrelated_call";
  auto callee = module.getOrInsertFunction(name, FunctionType::get(output, types, false));
  auto *call = builder.CreateCall(callee, arguments);
  auto *ret = builder.CreateRet(call);
  require(!verifyModule(module, &errs()), "invalid original fixture IR");
  Legalizer legalizer;
  if (mode == "mapped-vector") legalizer.InstToInstMap[original] = replacement;
  if (mode == "mapped-scalar") {
    IRBuilder<> before(call);
    legalizer.InstToInstMap[original] = before.CreateBitCast(replacement, integer);
  }
  if (mode == "mapped-width") legalizer.InstToInstMap[original] = builder.getInt32(0);
  bool changed = legalizer.lower(call);
  if (mode == "unrelated") {
    require(!changed && legalizer.ToBeRemoved.empty() && legalizer.InstToInstMap.empty(),
            "unrelated call was changed");
    return 1;
  }
  require(changed, "concat was not handled");
  Value *result = legalizer.InstToInstMap.lookup(call);
  require(result && result->getType() == output, "replacement lost exact fixed-vector type");
  require(legalizer.ToBeRemoved.size() == 1 && legalizer.ToBeRemoved.count(call),
          "original call was not marked for removal");
  call->replaceAllUsesWith(result);
  call->eraseFromParent();
  require(!verifyModule(module, &errs()), "invalid lowered fixture IR");
  bool mapped = mode == "mapped-vector" || mode == "mapped-scalar";
  require(mode == "direct" || mapped, "malformed fixture unexpectedly accepted");
  uint64_t count = uint64_t(1) << width;
  for (uint64_t value = 0; value < count; ++value) {
    // Original and replacement always differ, detecting an ignored child map.
    uint64_t previous = value ^ (count - 1);
    DenseMap<Value *, Constant *> values;
    values[original] = ConstantVector::get({ConstantInt::get(integer, mapped ? previous : value)});
    values[replacement] = ConstantVector::get({ConstantInt::get(integer, value)});
    values[function->getArg(2)] = builder.getInt32(0);
    Constant *actual = evaluate(ret->getReturnValue(), values, module.getDataLayout());
    require(actual->getType() == output, "constant result lost fixed-vector shape");
    for (unsigned lane = 0; lane < repeat; ++lane) {
      auto *element = dyn_cast_or_null<ConstantInt>(actual->getAggregateElement(lane));
      require(element && element->getZExtValue() == value, "concat lane differs from source repetition");
    }
  }
  return count;
}

int main(int argc, char **argv) {
  // Avoid crash/core-dump ambiguity: an actual fragment fatal is a distinct
  // process result, with its exact reason checked by the guarded runner.
  install_fatal_error_handler([](void *, const std::string &reason, bool) {
    errs() << "CONCAT_REJECT: " << reason << "\n";
    errs().flush();
    std::_Exit(86);
  });
  if (argc != 3) return 2;
  unsigned width = std::strtoul(argv[2], nullptr, 10);
  if (width != 8 && width != 16) return 2;
  LLVMContext context;
  Module module("concat-diagnostic", context);
  // Repeating identical lanes has the same value on either endianness; retain
  // the explicit analysis layout so LLVM bitcast evaluation is reproducible.
  module.setDataLayout("e-p:64:64-i64:64-n8:16:32:64");
  uint64_t checks = exercise(module, width, argv[1]);
  outs() << "{\"mode\":\"" << argv[1] << "\",\"width\":" << width
         << ",\"checks\":" << checks << ",\"verified_ir\":true}\n";
  return 0;
}
