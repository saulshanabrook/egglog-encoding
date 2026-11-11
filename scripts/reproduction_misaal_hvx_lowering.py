"""Checked source repair for MISAAL's two HVX concat pseudo instructions.

These are not LLVM Hexagon intrinsics. The pinned frontend defines them as
repeated bitvector concatenation; every other instruction keeps Rose's mapping.
"""

from __future__ import annotations

import ast
import re
from typing import Any

from scripts.reproduction_misaal_legalizer import simd_mode_replacements

CONCAT_WIDTHS = {"hexagon_V6_interleave_2_128B": 16, "hexagon_V6_interleave_4_128B": 8}


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


def hvx_generator_replacements(source: str) -> list[tuple[str, str]]:
    """Patch only exact pinned generator contexts; ordinary patterns stay intact."""
    header = r'      "#include \"Legalizer.h\"",'
    replacement = (
        header
        + '\n      "#include \\"llvm/IR/IRBuilder.h\\"",'
        + '\n      "#include \\"llvm/Support/ErrorHandling.h\\"",'
        + '\n      "using namespace boost::multiprecision::literals;",'
    )
    old_body = "      {}\n    }}\n    '''.format(self.generateInstSelectorForAllInsts())"
    cpp = concat_lowering_cpp().replace("{", "{{").replace("}", "}}")
    replacements = [
        (header, replacement),
        ("            ArgVal = int(ArgVal, 16)\n", "            ArgVal = int(ArgVal, 0)\n"),
        ("            ArgVal = int(ArgVal)\n", '            ArgVal = hex(ArgVal) + "_cppi"\n'),
        (
            old_body,
            cpp + "\n      {}\n      return false;\n    }}\n    '''.format(self.generateInstSelectorForAllInsts())",
        ),
        *simd_mode_replacements(source, "hvx"),
    ]
    if any(source.count(old) != 1 for old, _ in replacements):
        raise ValueError("HVX selector generator differs from exact repair contexts")
    return replacements
