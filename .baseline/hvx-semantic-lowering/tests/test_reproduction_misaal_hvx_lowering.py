"""Source/model checks only: these do not compile or execute LLVM instructions."""

import ast
import copy
import hashlib
import json
from pathlib import Path
from typing import Any

import pytest

from scripts.reproduction_misaal_hvx_lowering import (
    CONCAT_WIDTHS,
    concat_lowering_cpp,
    hvx_generator_replacements,
    validate_concat_semantics,
)

FIXTURES = Path(__file__).parent / "fixtures/misaal-hvx"


def generator_class(source: str) -> Any:
    """Evaluate only the pure source-emitting class, excluding upstream imports/main."""
    node = next(node for node in ast.parse(source).body if isinstance(node, ast.ClassDef))
    namespace: dict[str, Any] = {"GenHeadersForAutoGenFiles": lambda _: "// fixture source emission\n"}
    exec(compile(ast.Module(body=[node], type_ignores=[]), "selector-class", "exec"), namespace)
    return namespace["RoseInstSelectorGenerator"]


def patched_generator() -> str:
    """Apply the exact reviewed contexts to the retained pinned generator fixture."""
    source = (FIXTURES / "RoseHexLegalizerGen.py.txt").read_text()
    for old, new in hvx_generator_replacements(source):
        assert source.count(old) == 1
        source = source.replace(old, new)
    return source


def test_pinned_semantics_and_exhaustive_concat_bitpatterns() -> None:
    semantics = json.loads((FIXTURES / "concat-semantics.json").read_text())
    validate_concat_semantics(semantics)
    provenance = json.loads((FIXTURES / "provenance.json").read_text())
    assert (
        hashlib.sha256((FIXTURES / "RoseHexLegalizerGen.py.txt").read_bytes()).hexdigest()
        == provenance["generator_sha256"]
    )
    # Independent source concat model vs the emitted zext/shl/or construction;
    # exhaustive over both declared input domains, including their sign bits.
    for name, width in CONCAT_WIDTHS.items():
        count = semantics[name]["semantics"][1].count("%arg0")
        for value in range(1 << width):
            expected = int(f"{value:0{width}b}" * count, 2)
            actual = value
            for shift in range(width, 32, width):
                actual |= value << shift
            assert actual == expected
            assert actual < 1 << 32


@pytest.mark.parametrize("change", ["body", "arity", "width", "precision", "extra-target"])
def test_concat_source_drift_rejected(change: str) -> None:
    semantics = json.loads((FIXTURES / "concat-semantics.json").read_text())
    name = "hexagon_V6_interleave_2_128B"
    group = semantics[name]
    target = group["target_instructions"][name]
    if change == "body":
        group["semantics"][1] = '"(concat %arg0 (bv 0 16))"'
    elif change == "arity":
        target["args"].append("16")
    elif change == "width":
        target["out_vectsize"] = 64
    elif change == "precision":
        target["in_precision"] = 8
    else:
        group["target_instructions"]["unexpected"] = copy.deepcopy(target)
    with pytest.raises(ValueError, match="concat"):
        validate_concat_semantics(semantics)


def test_original_patterns_preserved_and_wide_constants_exact(capsys: pytest.CaptureFixture[str]) -> None:
    original = generator_class((FIXTURES / "RoseHexLegalizerGen.py.txt").read_text())({})
    prepared = generator_class(patched_generator())({})
    for info in (
        {"args": ["SYMBOLIC_BV_1024"], "arg_permute_map": [0]},
        {"args": ["SYMBOLIC_BV_1024", "16"], "arg_permute_map": [0, -1]},
    ):
        patterns = {"hexagon_V6_vasrh_128B": info}
        assert prepared.generateAPattern("ordinary", patterns) == original.generateAPattern("ordinary", patterns)
    value = (1 << 511) - 1
    info = {"args": [f"(bv #x{value:x} 512)"], "arg_permute_map": [-1]}
    emitted = prepared.generateAPattern("wide", {"hexagon_V6_fixture": info})
    assert f"isAMatch(CI, 0, 0x{value:x}_cppi)" in emitted
    assert str(value) not in emitted
    for bits, value in (("0", 0), ("00", 0), ("1", 1), ("11", 3)):
        info = {"args": [f"(bv #b{bits} {len(bits)})"], "arg_permute_map": [-1]}
        emitted = prepared.generateAPattern("binary", {"hexagon_V6_fixture": info})
        assert f"isAMatch(CI, 0, {hex(value)}_cppi)" in emitted
    capsys.readouterr()


def test_generated_cpp_checks_exact_shapes_and_preserves_pass_mode() -> None:
    cls = generator_class(patched_generator())({})
    emitted = cls.generateLegalizerPassDefinition()
    assert concat_lowering_cpp() in emitted
    assert emitted.count("CI->arg_size() != 3") == 2
    assert emitted.count("dyn_cast<FixedVectorType>") == 4
    assert emitted.count("getBitvectorOfRequiredType(") == 2
    assert emitted.count("ToBeRemoved.insert(CI);") == 2
    assert "InputType->getElementType()->isIntegerTy(16)" in emitted
    assert "InputType->getElementType()->isIntegerTy(8)" in emitted
    assert "OutputType->getNumElements() != 2" in emitted
    assert "OutputType->getNumElements() != 4" in emitted
    assert emitted.count("InputWidth->getType()->isIntegerTy(32)") == 2
    assert emitted.count("OutputWidth->equalsInt(32)") == 2
    assert "Shift < 32" in emitted
    assert "CreateSExt" not in emitted and "UndefValue" not in emitted
    assert "return false;\n    }" in emitted
    assert "L->bitsimd = false;\n      return L->legalize(F);" in emitted
    assert "using namespace boost::multiprecision::literals;" in cls.genHeader()


def test_generator_drift_fails_before_any_source_change() -> None:
    source = (FIXTURES / "RoseHexLegalizerGen.py.txt").read_text()
    with pytest.raises(ValueError, match="repair contexts"):
        hvx_generator_replacements(source.replace("ArgVal = int(ArgVal)", "ArgVal = str(ArgVal)"))
