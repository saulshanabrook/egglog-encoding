"""Source-bound HVX lowering repairs; active Egglog semantics stay unchanged."""

from __future__ import annotations

import ast
import hashlib
import json
import re
from typing import Any

CONCAT_WIDTHS = {"hexagon_V6_interleave_2_128B": 16, "hexagon_V6_interleave_4_128B": 8}

# Digests cover complete original group metadata and formal bodies, retained in
# tests/fixtures/misaal-hvx/source-lowerings.json. The preparer also pins files.
SOURCE_LOWERINGS = {
    "hexagon_V6_vlsrw_128B": "bcc35c6b58ccd3e53e17adbf4cb5839787d29634830905aa886dc0453007b042",
    "hexagon_V6_vassign_128B": "79bf6029fe973772b3662496bac8f4ea2049c63af63325b9bc56b92d11448678",
    "hexagon_V6_lo_128B": "b2a1941e76f191ca07bc928460d6860987dd1d9f603c6ab073bc21731a131200",
    "hvx_swizzle_1": "26bc7e99d3d7690c981accd98d20059dd7004be3f1ce9d5133a4876740fd699e",
}
SWIZZLE_SHAPES = (
    (2048, 64, 0, 64, 32, 32, 2, 0),
    (2048, 32, 0, 32, 16, 64, 2, 0),
    (1024, 32, 0, 32, 16, 32, 2, 0),
    (1024, 16, 0, 16, 8, 64, 2, 0),
)


def validate_source_lowerings(semantics: dict[str, Any], swizzles: dict[str, Any]) -> None:
    """Bind hand-lowered operations to the complete pinned frontend definitions."""
    for name, expected in SOURCE_LOWERINGS.items():
        group = (swizzles if name == "hvx_swizzle_1" else semantics).get(name)
        digest = hashlib.sha256(json.dumps(group, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
        if digest != expected:
            raise ValueError(f"HVX source lowering definition changed: {name}")


def swizzle_mask(shape: tuple[int, ...]) -> list[int]:
    """Evaluate the pinned formal's source-bit offsets, rejecting other shapes."""
    if shape not in SWIZZLE_SHAPES:
        raise ValueError("unsupported HVX swizzle source shape")
    width, outer, start, end, element, stride, divisor, padding = shape
    offsets = [
        lane // divisor + inner * stride for lane in range(0, width, outer) for inner in range(start, end, element)
    ]
    if padding or any(lane % divisor for lane in range(0, width, outer)):
        raise ValueError("HVX swizzle requires integral offsets and no padding")
    if len(offsets) * element != width or any(offset % element or offset + element > width for offset in offsets):
        raise ValueError("HVX swizzle offsets must be aligned and in bounds")
    return [offset // element for offset in offsets]


def validate_concat_semantics(semantics: dict[str, Any]) -> None:
    """Reject changes to arity, bitvector shape or the source concat definition."""
    for name, width in CONCAT_WIDTHS.items():
        group = semantics.get(name, {})
        targets = group.get("target_instructions", {})
        if set(targets) != {name}:
            raise ValueError(f"expected exactly the original concat target: {name}")
        expected = {
            "args": [f"SYMBOLIC_BV_{width}", str(width), "32"],
            "in_vectsize": width,
            "out_vectsize": 32,
            "lanesize": width,
            "in_precision": width,
            "out_precision": width,
            "in_vectsize_index": 1,
            "out_vectsize_index": 2,
            "in_lanesize_index": 1,
            "out_lanesize_index": 1,
            "in_precision_index": 1,
            "out_precision_index": 1,
        }
        if any(targets[name].get(key) != value for key, value in expected.items()):
            raise ValueError(f"concat argument/shape metadata changed: {name}")
        fragments = [ast.literal_eval(fragment) for fragment in group.get("semantics", [])]
        if not all(isinstance(fragment, str) for fragment in fragments):
            raise ValueError(f"concat semantics must contain literal source strings: {name}")
        definition = " ".join(fragments)
        wanted = f"(define ({name} %arg0 %num1 %num2) (concat {' '.join(['%arg0'] * (32 // width))}))"
        if re.findall(r"[^\s()]+|[()]", definition) != re.findall(r"[^\s()]+|[()]", wanted):
            raise ValueError(f"concat semantics changed: {name}")


def concat_lowering_cpp() -> str:
    """Emit exact fixed-vector shape checks and the source's repeated concat.

    The scalar integer representation is only an internal bitcast. Using the
    common mapping accessor preserves a child already replaced by legalization.
    """
    cases = []
    for name, width in CONCAT_WIDTHS.items():
        repeat = 32 // width
        cases.append(
            f"""      if (CI->getCalledFunction() &&
          CI->getCalledFunction()->getName() == "llvm.hydride.{name}_dsl") {{
        if (CI->arg_size() != 3)
          report_fatal_error("MISAAL concat requires three arguments");
        auto *InputType = dyn_cast<FixedVectorType>(CI->getArgOperand(0)->getType());
        auto *OutputType = dyn_cast<FixedVectorType>(CI->getType());
        auto *InputWidth = dyn_cast<ConstantInt>(CI->getArgOperand(1));
        auto *OutputWidth = dyn_cast<ConstantInt>(CI->getArgOperand(2));
        if (!InputType || InputType->getNumElements() != 1 ||
            !InputType->getElementType()->isIntegerTy({width}) ||
            !OutputType || OutputType->getNumElements() != {repeat} ||
            !OutputType->getElementType()->isIntegerTy({width}) ||
            !InputWidth || !InputWidth->getType()->isIntegerTy(32) ||
            !InputWidth->equalsInt({width}) ||
            !OutputWidth || !OutputWidth->getType()->isIntegerTy(32) ||
            !OutputWidth->equalsInt(32))
          report_fatal_error("MISAAL concat source shape or width annotation changed");
        auto *Input = getBitvectorOfRequiredType(
            CI->getArgOperand(0), IntegerType::get(CI->getContext(), {width}), CI);
        if (!Input)
          report_fatal_error("MISAAL concat input mapping has an incompatible width");
        IRBuilder<> Builder(CI);
        Value *Unit = Builder.CreateZExt(Input, Builder.getInt32Ty());
        Value *Result = Unit;
        for (unsigned Shift = {width}; Shift < 32; Shift += {width})
          Result = Builder.CreateOr(Result, Builder.CreateShl(Unit, Shift));
        InstToInstMap[CI] = Builder.CreateBitCast(Result, CI->getType());
        ToBeRemoved.insert(CI);
        return true;
      }}"""
        )
    return "\n".join(cases)


def source_lowering_cpp() -> str:
    """Portable LLVM operations for the four exact active source definitions.

    The masked LLVM shift avoids poison, followed by zero selection for the
    full-width Rosette shift. No target intrinsic semantics are substituted.
    """
    cpp = r"""      auto *Callee = CI->getCalledFunction();
      if (!Callee)
        return false;
      if (!CI->getModule()->getDataLayout().isLittleEndian())
        report_fatal_error("MISAAL HVX source requires little-endian bitvector packing");
      StringRef SourceName = Callee->getName();
      auto IsSource = [&](StringRef Expected) {
        if (SourceName == Expected)
          return true;
        unsigned Overload;
        return SourceName.startswith(Expected) && SourceName.size() > Expected.size() + 1 &&
               SourceName[Expected.size()] == '.' &&
               !SourceName.drop_front(Expected.size() + 1).getAsInteger(10, Overload);
      };
      auto HasWidth = [](Value *V, unsigned Bits) {
        auto *Ty = dyn_cast<FixedVectorType>(V->getType());
        return Ty && Ty->getElementType()->isIntegerTy() &&
               uint64_t(Ty->getNumElements()) * Ty->getElementType()->getIntegerBitWidth() == Bits;
      };
      auto Annotations = [&](unsigned Start, ArrayRef<int64_t> Values) {
        if (CI->arg_size() != Start + Values.size())
          return false;
        for (unsigned N = 0; N < Values.size(); ++N) {
          auto *C = dyn_cast<ConstantInt>(CI->getArgOperand(Start + N));
          if (!C || !C->getType()->isIntegerTy(32) || C->getSExtValue() != Values[N])
            return false;
        }
        return true;
      };
      if (IsSource("llvm.hydride.hexagon_V6_vlsrw_128B_dsl")) {
        if (!Annotations(3, {1024, 1024, 0, 1024, 32, 0}) ||
            CI->getArgOperand(0)->getType() != FixedVectorType::get(Type::getInt32Ty(CI->getContext()), 1) ||
            !HasWidth(CI->getArgOperand(1), 1024) ||
            CI->getArgOperand(2)->getType() != FixedVectorType::get(Type::getInt32Ty(CI->getContext()), 1) ||
            CI->getType() != FixedVectorType::get(Type::getInt32Ty(CI->getContext()), 32))
          report_fatal_error("MISAAL vlsrw source shape changed");
        auto *Mask = dyn_cast<Constant>(CI->getArgOperand(0));
        auto *MaskElement = Mask ? dyn_cast_or_null<ConstantInt>(Mask->getAggregateElement(0U)) : nullptr;
        if (!MaskElement || !MaskElement->equalsInt(31))
          report_fatal_error("MISAAL vlsrw source mask changed");
        IRBuilder<> Builder(CI);
        auto *VectorTy = FixedVectorType::get(Builder.getInt32Ty(), 32);
        auto *Vector = getBitvectorOfRequiredType(CI->getArgOperand(1), VectorTy, CI);
        auto *Shift = getBitvectorOfRequiredType(CI->getArgOperand(2), Builder.getInt32Ty(), CI);
        if (!Vector || !Shift)
          report_fatal_error("MISAAL vlsrw mapped operand width changed");
        auto *SafeShift = Builder.CreateAnd(Shift, Builder.getInt32(31));
        auto *Shifted = Builder.CreateLShr(Vector, Builder.CreateVectorSplat(32, SafeShift));
        auto *Result = Builder.CreateSelect(Builder.CreateICmpULT(Shift, Builder.getInt32(32)),
                                            Shifted, Constant::getNullValue(VectorTy));
        InstToInstMap[CI] = Result;
        ToBeRemoved.insert(CI);
        return true;
      }
"""
    for name, offset, constants in (
        ("hexagon_V6_vassign_128B", 0, (1024, 1024, 0, 1024, 8, 0)),
        ("hexagon_V6_lo_128B", 32, (1024, 1024, 0, 1024, 8, 1024, 0)),
    ):
        mask = ", ".join(str(n) for n in range(offset, offset + 32))
        cpp += f"""      if (IsSource("llvm.hydride.{name}_dsl")) {{
        if (!Annotations(1, {{{", ".join(map(str, constants))}}}) ||
            !HasWidth(CI->getArgOperand(0), 2048) ||
            CI->getType() != FixedVectorType::get(Type::getInt8Ty(CI->getContext()), 128))
          report_fatal_error("MISAAL half-extract source shape changed");
        IRBuilder<> Builder(CI);
        auto *Input = getBitvectorOfRequiredType(
            CI->getArgOperand(0), FixedVectorType::get(Builder.getInt32Ty(), 64), CI);
        if (!Input)
          report_fatal_error("MISAAL half-extract mapped input width changed");
        auto *Result = Builder.CreateShuffleVector(Input, Input, ArrayRef<int>{{{mask}}});
        InstToInstMap[CI] = Builder.CreateBitCast(Result, CI->getType());
        ToBeRemoved.insert(CI);
        return true;
      }}
"""
    cpp += '      if (IsSource("llvm.hydride.hvx_swizzle_1_dsl")) {\n'
    for shape in SWIZZLE_SHAPES:
        width, _, _, _, element, _, _, _ = shape
        mask = ", ".join(map(str, swizzle_mask(shape)))
        cpp += f"""        if (Annotations(1, {{{", ".join(map(str, shape))}}}) &&
            HasWidth(CI->getArgOperand(0), {width}) &&
            CI->getType() == FixedVectorType::get(IntegerType::get(CI->getContext(), {element}), {width // element})) {{
          IRBuilder<> Builder(CI);
          auto *Input = getBitvectorOfRequiredType(CI->getArgOperand(0), CI->getType(), CI);
          if (!Input)
            report_fatal_error("MISAAL swizzle mapped input width changed");
          InstToInstMap[CI] = Builder.CreateShuffleVector(Input, Input, ArrayRef<int>{{{mask}}});
          ToBeRemoved.insert(CI);
          return true;
        }}
"""
    return cpp + '        report_fatal_error("unsupported MISAAL swizzle source shape");\n      }'


def hvx_common_replacements(source: str) -> list[tuple[str, str]]:
    """Fail before LLVM mutation if a private HVX intrinsic map is incomplete."""
    start = source.index("    // Some sanity checks\n", source.index("Legalizer::getArgsAfterPermutation("))
    end = source.index("    // Generate some new args\n", start)
    before = source[start:end]
    replacement = r"""    // Validate the complete map before inserting any bitcasts or call.
    if (Permutation.size() != BitvectorList.size())
        report_fatal_error("MISAAL HVX permutation/source arity mismatch");
    std::vector<bool> Assigned(RequiredTypes.size(), false);
    for (int Index : Permutation) {
        if (Index == -1) continue;
        if (Index < 0 || unsigned(Index) >= RequiredTypes.size() || Assigned[Index])
            report_fatal_error("MISAAL HVX invalid or duplicate permutation index");
        Assigned[Index] = true;
    }
    for (bool Present : Assigned)
        if (!Present)
            report_fatal_error("MISAAL HVX missing intrinsic operand");
"""
    conversions = """                                                         RequiredTypes[PermIdx], InsertBefore);
            if (Bitvector == nullptr)
                return std::vector<Value *>();
            NewArgs[PermIdx] = Bitvector;"""
    replacements = [
        ('#include "llvm/IR/IRBuilder.h"', '#include "llvm/IR/IRBuilder.h"\n#include "llvm/Support/ErrorHandling.h"'),
        (before, replacement),
        ("            if (PermIdx >= RequiredTypes.size()) continue;  // Immediate Number\n", ""),
        (
            conversions,
            """                                                         RequiredTypes[PermIdx], InsertBefore);
            if (Bitvector == nullptr || Bitvector->getType() != RequiredTypes[PermIdx])
                report_fatal_error("MISAAL HVX incompatible intrinsic operand type");
            NewArgs[PermIdx] = Bitvector;""",
        ),
    ]
    if any(source.count(old) != 1 for old, _ in replacements):
        raise ValueError("HVX common legalizer differs from exact repair contexts")
    return replacements


def hvx_generator_replacements(source: str) -> list[tuple[str, str]]:
    """Patch only exact pinned generator contexts; ordinary patterns stay intact."""
    header = r'      "#include \"Legalizer.h\"",'
    replacement = (
        header
        + '\n      "#include \\"llvm/IR/IRBuilder.h\\"",'
        + '\n      "#include \\"llvm/Support/ErrorHandling.h\\"",'
        + '\n      "#include \\"llvm/IR/Verifier.h\\"",'
        + '\n      "using namespace boost::multiprecision::literals;",'
    )
    old_body = "      {}\n    }}\n    '''.format(self.generateInstSelectorForAllInsts())"
    cpp = (concat_lowering_cpp() + "\n" + source_lowering_cpp()).replace("{", "{{").replace("}", "}}")
    replacements = [
        (header, replacement),
        ("            ArgVal = int(ArgVal, 16)\n", "            ArgVal = int(ArgVal, 0)\n"),
        ("            ArgVal = int(ArgVal)\n", '            ArgVal = hex(ArgVal) + "_cppi"\n'),
        (
            old_body,
            cpp + "\n      {}\n      return false;\n    }}\n    '''.format(self.generateInstSelectorForAllInsts())",
        ),
        (
            "      Legalizer *L = new HexLegalizer();\n      return L->legalize(F);",
            "      HexLegalizer Selector;\n      Legalizer *L = &Selector;\n      L->bitsimd = false;\n"
            "      bool Changed = L->legalize(F);\n"
            "      if (verifyFunction(F, &errs()))\n"
            '        report_fatal_error("MISAAL HVX legalization produced invalid LLVM IR");\n'
            "      return Changed;",
        ),
    ]
    if any(source.count(old) != 1 for old, _ in replacements):
        raise ValueError("HVX selector generator differs from exact repair contexts")
    return replacements
