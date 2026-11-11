#include "llvm/Analysis/REVPass.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"

using namespace llvm;

extern "C" LLVM_ATTRIBUTE_WEAK PassPluginLibraryInfo llvmGetPassPluginInfo() {
  return {
      LLVM_PLUGIN_API_VERSION,
      "revpass",
      LLVM_VERSION_STRING,
      [](PassBuilder &pass_builder) {
        pass_builder.registerAnalysisRegistrationCallback(
            [](FunctionAnalysisManager &function_analyses) {
              function_analyses.registerPass([] { return REVPass(); });
            });
        pass_builder.registerPipelineParsingCallback(
            [](StringRef name, FunctionPassManager &function_passes,
               ArrayRef<PassBuilder::PipelineElement>) {
              if (name != "print<revpass>") {
                return false;
              }
              function_passes.addPass(REVPrinterPass(errs()));
              return true;
            });
      }};
}
