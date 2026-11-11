"""Detect the actual valid-LLVM loss of SIMD results without native jobs."""

import pytest

from scripts.reproduction_misaal_legalizer import audit_simd_lowering, simd_mode_replacements


@pytest.mark.parametrize(
    ("target", "pass_name", "selector"),
    [
        ("x86", "X86LegalizationPass", "X86Legalizer"),
        ("arm", "ARMLegalizationPass", "ARMLegalizer"),
        ("hvx", "HexLegalizationPass", "HexLegalizer"),
    ],
)
def test_only_selected_simd_instance_changes(target: str, pass_name: str, selector: str) -> None:
    bitsimd = "bool bitsimd = true;\nLegalizer *L = new BitSIMDLegalizer();\nreturn L->legalize(F);\n"
    source = (
        bitsimd + f"bool {pass_name}::runOnFunction(Function &F) {{\n"
        f"  Legalizer *L = new {selector}();\n  return L->legalize(F);\n}}\n"
    )
    replacements = simd_mode_replacements(source, target)
    assert len(replacements) == 1
    old, new = replacements[0]
    patched = source.replace(old, new)
    assert patched.startswith(bitsimd)
    assert f"new {selector}();\n  L->bitsimd = false;\n  return L->legalize(F);" in patched
    assert simd_mode_replacements(patched, target) == []
    with pytest.raises(ValueError, match="exactly one"):
        simd_mode_replacements(source + source, target)


def test_unrecognized_mode_or_target_is_not_silently_rewritten() -> None:
    source = (
        "bool X86LegalizationPass::runOnFunction(Function &F) {\n"
        "  Legalizer *L = new X86Legalizer();\n  L->bitsimd = something_else;\n  return L->legalize(F);\n}"
    )
    with pytest.raises(ValueError, match="unambiguous"):
        simd_mode_replacements(source, "x86")
    with pytest.raises(ValueError, match="only x86"):
        simd_mode_replacements(source, "bitsimd")


@pytest.mark.parametrize("undefined", ["undef", "poison"])
def test_real_canary_shape_is_rejected_even_with_target_wrapper_calls(undefined: str) -> None:
    llvm = f"""define <32 x i16> @hydride.node.blur.0(<64 x i8> %arg) {{
entry:
  %0 = bitcast <64 x i8> %arg to <8 x i64>
  %1 = call <8 x i64> @_mm512_add_epi16_wrapper(<8 x i64> %0, <8 x i64> %0)
  ret <32 x i16> {undefined}
}}
"""
    result = audit_simd_lowering(llvm, {"hydride.node.blur.0"})
    assert result["status"] == "failure"
    assert result["undefined_return_functions"] == ["hydride.node.blur.0"]
    assert not result["unlowered_hydride_call_functions"]


def test_selected_result_is_returned_and_unrelated_wrapper_undef_is_not_confused() -> None:
    llvm = """define <8 x i64> @hydride.node.0(<8 x i64> %arg) {
entry:
  %result = call <8 x i64> @real_wrapper(<8 x i64> %arg)
  ret <8 x i64> %result
}
define i32 @unused_wrapper() {
  ret i32 undef
}
"""
    assert audit_simd_lowering(llvm, {"hydride.node.0"})["status"] == "success"
    assert audit_simd_lowering(llvm, {"hydride.node.0", "missing"})["missing_functions"] == ["missing"]
    with pytest.raises(ValueError, match="actual requested"):
        audit_simd_lowering(llvm, set())


def test_remaining_target_agnostic_call_is_rejected_with_quoted_name() -> None:
    llvm = """define i32 @"hydride.node.0"(i32 %arg) {
  %result = call i32 @"llvm.hydride.unknown_dsl"(i32 %arg)
  ret i32 %result
}
"""
    result = audit_simd_lowering(llvm, {"hydride.node.0"})
    assert result["status"] == "failure"
    assert result["unlowered_hydride_call_functions"] == ["hydride.node.0"]
