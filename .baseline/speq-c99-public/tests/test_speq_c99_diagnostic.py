"""Data-only candidate gates. LLVM compilation/execution belongs to the root gate."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path

import pytest

from scripts import speq_c99_diagnostic as diagnostic
from scripts import speq_phi_diagnostic as phi


@pytest.fixture
def source(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> Path:
    cpp = tmp_path / "source/llvm/lib/Analysis/REVPass.cpp"
    header = tmp_path / "source/llvm/include/llvm/Analysis/REVPass.h"
    cpp.parent.mkdir(parents=True)
    header.parent.mkdir(parents=True)
    # Only materializer boundary syntax is modeled; this is never a native fixture.
    cpp.write_text(
        '#include "llvm/Support/Debug.h"\n'
        "class Lambda {\n"
        "  Lambda(DenseMap<Value *, Tensor *> &TM, DenseMap<Value *, LevelBounds> &LM)\n"
        "      : TensorMap(TM), LevelMap(LM) {}\n"
        "  std::string arrayType(Value *I) {\n"
        "    if (existing_tensor) return original_type;\n"
        "    return Out;\n"
        '    //    llvm_unreachable("val doesn\'t exist in tensor map.");\n  }\n'
        + phi.BEGIN
        + "PHITy *Phi, BasicBlock **Then, BasicBlock **Else) { return nullptr; }\n"
        + phi.END
        + "\n"
        "    BranchInst *Br = getPhiBr(Phi, &Then, &Else);\n"
        "    auto *Header = L.getHeader();\n"
        "        LoopBody.push_back(&*I);\n"
        "  DenseMap<Value *, LevelBounds> &LevelMap;\n"
        "};\n"
        "Value *findLiveOut(Loop *L) { return nullptr; }\n"
        "REVInfo REVPass::run(Function &F, FunctionAnalysisManager &AM) {\n"
        "  Lambda Lam(LI, SE, MSSA, TensorMap, LevelMap);\n"
        "  return unchanged_output;\n}\n"
    )
    header.write_text("exact synthetic REV header")
    memory = header.with_name("MemorySSA.h")
    memory.write_text("exact synthetic MemorySSA header")
    for name, path in (("REV_PASS_SHA256", cpp), ("REV_PASS_HEADER_SHA256", header), ("MEMORY_SSA_SHA256", memory)):
        monkeypatch.setattr(phi, name, hashlib.sha256(path.read_bytes()).hexdigest())
    return tmp_path / "source"


def test_candidate_binds_exact_fragment_and_preserves_originals(source: Path, tmp_path: Path) -> None:
    original = (source / "llvm/lib/Analysis/REVPass.cpp").read_bytes()
    out = tmp_path / "candidate"
    receipt = diagnostic.materialize(source, out, "selected_kernel")
    assert (source / "llvm/lib/Analysis/REVPass.cpp").read_bytes() == original
    assert (out / "phi/original/REVPass.cpp").read_bytes() == original
    fragment = (diagnostic.SUPPORT / "speq_c99_fir.inc").read_text()
    candidate = (out / "candidate/llvm/lib/Analysis/REVPass.cpp").read_text()
    harness = (out / "c99-harness.cpp").read_text()
    assert candidate.count(fragment) == harness.count(fragment) == 1
    assert phi.EDGE_AWARE_PHI in candidate
    assert receipt["native_execution"] is receipt["corpus_admission"] is False
    assert receipt["candidate_default"] == "disabled"
    assert receipt["selected_function"] == "selected_kernel"
    assert receipt["enable_environment"] == {diagnostic.ENABLE_ENV: "1"}
    assert 'F.getName() == "selected_kernel"' in candidate
    assert "!Selected || Selected->isDeclaration()" in candidate
    assert 'StringRef(Enabled) != "1"' in candidate
    for relative, digest in receipt["files"].items():
        assert hashlib.sha256((out / relative).read_bytes()).hexdigest() == digest
    assert json.loads((out / "diagnostic.json").read_text()) == receipt


@pytest.mark.parametrize("function", ["", "a b", 'x";abort();', "@name", "a\nb", "λ"])
def test_function_selection_cannot_be_implicit_or_cpp_injection(source: Path, tmp_path: Path, function: str) -> None:
    with pytest.raises(ValueError, match="explicit simple LLVM function"):
        diagnostic.materialize(source, tmp_path / "out", function)
    assert not (tmp_path / "out").exists()


@pytest.mark.parametrize("changed", ["source", "header", "memory", "existing-output", "source-output"])
def test_source_pins_and_fresh_evidence_remain_mandatory(source: Path, tmp_path: Path, changed: str) -> None:
    out = tmp_path / "out"
    paths = {
        "source": "llvm/lib/Analysis/REVPass.cpp",
        "header": "llvm/include/llvm/Analysis/REVPass.h",
        "memory": "llvm/include/llvm/Analysis/MemorySSA.h",
    }
    if changed in paths:
        with (source / paths[changed]).open("a") as file:
            file.write("changed")
    elif changed == "existing-output":
        out.mkdir()
    else:
        out = source / "new-evidence"
    with pytest.raises(ValueError):
        diagnostic.materialize(source, out, "selected_kernel")
    assert not (out / "diagnostic.json").exists()


def test_disabled_and_unrelated_functions_have_no_serialization_changes(source: Path) -> None:
    candidate = diagnostic.candidate_rev((source / "llvm/lib/Analysis/REVPass.cpp").read_text(), "kernel")
    fragment = (diagnostic.SUPPORT / "speq_c99_fir.inc").read_text()
    # The native gate must verify actual FIR bytes. These are source-scope guards,
    # not a claim that C++ has compiled or that native outputs already match.
    assert 'std::getenv("SPEQ_REV_C99_DIAGNOSTIC") && F.getName() == "kernel"' in candidate
    assert fragment.index("if (!Selected) return;") < fragment.index("for (Argument &A")
    assert 'if (!Active) return "";' in fragment
    assert "if (!Active) return false;" in fragment
    assert "if (!Active) return;" in fragment
    assert "return original_type;" in candidate
    assert "return unchanged_output;" in candidate
    assert "setOperand(" not in fragment
    assert "Create(" not in fragment


def test_real_fixture_controls_are_distinct_and_bind_expected_failures() -> None:
    cases = diagnostic.fixture_cases()
    assert len(cases) == 16
    assert [name for name, (_, error) in cases.items() if error is None] == [
        "guarded_stride",
        "nonzero_offset",
        "different_stride",
    ]
    assert len({hashlib.sha256(text.encode()).hexdigest() for text, _ in cases.values()}) == len(cases)
    for name, (text, error) in cases.items():
        assert text.count(f"define void @{name}(") == 1
        assert "br i1 %positive, label %rowguard, label %exit" in text
        integer = "i16" if name == "unsupported_i16" else "i32"
        assert f"%next = add nuw nsw {integer} %j, 1" in text
        assert f"%more = icmp slt {integer} %next, %n" in text
        if error:
            assert isinstance(error, str)
    assert "%stride.phi = phi i64 [ %n64, %rowguard ]" in cases["opaque_external_phi"][0]
    assert "load i64, ptr @stride" in cases["external_load"][0]
    assert "load i32, ptr %element" in cases["mixed_memory_type"][0]


def test_fixture_address_oracle_preserves_zero_negative_dimensions_and_distinct_strides() -> None:
    # Independent arithmetic for the real fixture, including paths on which no
    # address is evaluated. This does not substitute for LLVM analysis gates.
    for n in (-5, 0, 1, 3, 11):
        for row in (-2, 0, 1, 7):
            for extra_stride, offset in ((0, 0), (0, 3), (7, 0)):
                addresses = []
                if n > 0 and row >= 0:
                    for j in range(n):
                        original_byte_address = (row * (n + extra_stride)) * 8 + (j + offset) * 8
                        combined_byte_address = (row * (n + extra_stride) + j + offset) * 8
                        assert combined_byte_address == original_byte_address
                        addresses.append(combined_byte_address)
                assert len(addresses) == (n if n > 0 and row >= 0 else 0)
    assert (2**31 - 1) * (2**31 - 1 + 7) + (2**31 - 1) < 2**63


def test_fragment_does_not_assume_cast_or_wrapping_index_equivalence() -> None:
    fragment = (diagnostic.SUPPORT / "speq_c99_fir.inc").read_text()
    assert "SE.isKnownPredicateAt(ICmpInst::ICMP_SGE" in fragment
    assert "DT.dominates(I, &Use)" in fragment
    assert "if (isa<ZExtInst>(Cast) && !nonnegative" in fragment
    assert "Bound.ugt(Limit)" in fragment
    assert "APInt::getSignedMaxValue(64).zext(128)" in fragment
    assert "Part->getPointerAddressSpace() != 0" in fragment
    assert "G->getSourceElementType()->isDoubleTy()" in fragment
    assert "OS << *I" in fragment  # Keep original external cast bytes, do not substitute the source variable.
    assert "return false; // Preserve the actual cast" in fragment
