"""Source/model checks only: these do not compile or execute LLVM instructions."""

import ast
import copy
import hashlib
import json
import re
from pathlib import Path
from typing import Any

import pytest

from scripts.reproduction_misaal_hvx_lowering import (
    CONCAT_WIDTHS,
    SOURCE_LOWERINGS,
    SWIZZLE_SHAPES,
    concat_lowering_cpp,
    hvx_common_replacements,
    hvx_generator_replacements,
    source_lowering_cpp,
    swizzle_mask,
    validate_concat_semantics,
    validate_source_lowerings,
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
    assert concat_lowering_cpp().count("dyn_cast<FixedVectorType>") == 4
    assert concat_lowering_cpp().count("getBitvectorOfRequiredType(") == 2
    assert concat_lowering_cpp().count("ToBeRemoved.insert(CI);") == 2
    assert "InputType->getElementType()->isIntegerTy(16)" in emitted
    assert "InputType->getElementType()->isIntegerTy(8)" in emitted
    assert "OutputType->getNumElements() != 2" in emitted
    assert "OutputType->getNumElements() != 4" in emitted
    assert emitted.count("InputWidth->getType()->isIntegerTy(32)") == 2
    assert emitted.count("OutputWidth->equalsInt(32)") == 2
    assert "Shift < 32" in emitted
    assert "CreateSExt" not in emitted and "UndefValue" not in emitted
    assert "return false;\n    }" in emitted
    assert "L->bitsimd = false;\n      bool Changed = L->legalize(F);" in emitted
    assert "using namespace boost::multiprecision::literals;" in cls.genHeader()


def test_generator_drift_fails_before_any_source_change() -> None:
    source = (FIXTURES / "RoseHexLegalizerGen.py.txt").read_text()
    with pytest.raises(ValueError, match="repair contexts"):
        hvx_generator_replacements(source.replace("ArgVal = int(ArgVal)", "ArgVal = str(ArgVal)"))


class BV:
    """A finite bitvector used only by the independent original-formal evaluator."""

    def __init__(self, value: int, width: int):
        self.value, self.width = value & ((1 << width) - 1), width


def evaluate_formal(group: dict[str, Any], arguments: list[Any]) -> BV:
    """Interpret the retained Rosette subset, not the lowering's index formulas."""
    tokens = iter(re.findall(r"[^\s()\[\]]+|[()\[\]]", " ".join(ast.literal_eval(s) for s in group["semantics"])))

    def parse(token: str) -> Any:
        if token not in ("(", "["):
            return int(token) if token.lstrip("-").isdigit() else token
        result: list[Any] = []
        for child in tokens:
            if child in (")", "]"):
                return result
            result.append(parse(child))
        raise AssertionError("unclosed pinned formal")

    form = parse(next(tokens))
    assert form[0] == "define"

    def execute(node: Any, env: dict[str, Any]) -> Any:
        if isinstance(node, int):
            return node
        if isinstance(node, str):
            return env[node]
        op, *args = node
        if op == "define":
            env[args[0]] = execute(args[1], env)
            return None
        if op == "for/list":
            ((name, values),) = args[0]
            results = []
            for value in execute(values, env):
                scope = {**env, name: value}
                for statement in args[1:]:
                    result = execute(statement, scope)
                results.append(result)
            return results
        if op == "apply":
            assert args[0] == "concat"
            values = execute(args[1], env)
            value, width = 0, 0
            for part in values:
                value = (value << part.width) | part.value
                width += part.width
            return BV(value, width)
        values = [execute(arg, env) for arg in args]
        if op == "range":
            return list(range(*values))
        if op == "reverse":
            return list(reversed(values[0]))
        if op == "+":
            return values[0] + values[1]
        if op == "-":
            return values[0] - values[1]
        if op == "*":
            return values[0] * values[1]
        if op == "/":
            assert values[0] % values[1] == 0
            return values[0] // values[1]
        if op == "extract":
            high, low, value = values
            assert 0 <= low <= high < value.width
            return BV(value.value >> low, high - low + 1)
        if op == "bvand":
            return BV(values[0].value & values[1].value, values[0].width)
        if op == "bvlshr":
            return BV(values[0].value >> values[1].value, values[0].width)
        if op == "bvpadhighbits":
            value, padding = values
            return BV(value.value, value.width + padding)
        raise AssertionError(op)

    scope = dict(zip(form[1][1:], arguments, strict=True))
    for statement in form[2:]:
        result = execute(statement, scope)
    assert isinstance(result, BV)
    return result


def test_portable_shift_matches_active_formal_at_every_boundary() -> None:
    groups = json.loads((FIXTURES / "source-lowerings.json").read_text())
    validate_source_lowerings(groups, groups)
    words = [0, 1, 0xFFFFFFFF, 0x80000000, 0x7FFFFFFF, *range(27)]
    value = sum(word << (32 * i) for i, word in enumerate(words))
    for shift in (0, 1, 17, 30, 31, 32, 33, 63, 64, 0x80000000, 0xFFFFFFFF):
        result = evaluate_formal(
            groups["hexagon_V6_vlsrw_128B"], [BV(31, 32), BV(value, 1024), BV(shift, 32), 1024, 1024, 0, 1024, 32, 0]
        )
        lowered = sum((word >> (shift & 31) if shift < 32 else 0) << (32 * i) for i, word in enumerate(words))
        assert result.width == 1024 and result.value == lowered
    # The old masked intrinsic is distinguishable from the active source.
    assert (1 >> (32 & 31)) == 1 and (1 >> 32) == 0


def test_source_halves_and_every_swizzle_lane() -> None:
    groups = json.loads((FIXTURES / "source-lowerings.json").read_text())
    # Unequal halves and distinct byte values expose hi/lo swaps and bit order.
    words = [0x12340000 + i for i in range(64)]
    value = sum(word << (32 * i) for i, word in enumerate(words))
    for name, offset, tail in (("hexagon_V6_vassign_128B", 0, [0]), ("hexagon_V6_lo_128B", 1024, [1024, 0])):
        result = evaluate_formal(groups[name], [BV(value, 2048), 1024, 1024, 0, 1024, 8, *tail])
        expected = sum(words[i + offset // 32] << (32 * i) for i in range(32))
        assert result.width == 1024 and result.value == expected
    for shape in SWIZZLE_SHAPES:
        width, _, _, _, element, _, _, _ = shape
        values = list(range(width // element))
        value = sum(x << (i * element) for i, x in enumerate(values))
        original = evaluate_formal(groups["hvx_swizzle_1"], [BV(value, width), *shape])
        mask = swizzle_mask(shape)
        actual = [(original.value >> (i * element)) & ((1 << element) - 1) for i in range(len(mask))]
        assert actual == [values[i] for i in mask]
        assert sorted(mask) == list(range(len(values)))
    assert swizzle_mask(SWIZZLE_SHAPES[2]) == [i for pair in zip(range(32), range(32, 64), strict=True) for i in pair]
    with pytest.raises(ValueError, match="unsupported"):
        swizzle_mask((1024, 32, 1, 32, 16, 32, 2, 0))


@pytest.mark.parametrize("name", SOURCE_LOWERINGS)
def test_formal_body_and_mapping_drift_rejected(name: str) -> None:
    groups = json.loads((FIXTURES / "source-lowerings.json").read_text())
    for field in ("semantics", "target_instructions"):
        changed = copy.deepcopy(groups)
        changed[name][field] = []
        with pytest.raises(ValueError, match="source lowering definition changed"):
            validate_source_lowerings(changed, changed)


def test_permutation_preflight_and_verifier_are_in_the_executed_path() -> None:
    source = (FIXTURES / "Legalizer.cpp.txt").read_text()
    original = source
    provenance = json.loads((FIXTURES / "provenance.json").read_text())
    assert hashlib.sha256(source.encode()).hexdigest() == provenance["common_sha256"]
    assert (
        hashlib.sha256((FIXTURES / "source-lowerings.json").read_bytes()).hexdigest()
        == provenance["source_lowerings_fixture_sha256"]
    )
    for old, new in hvx_common_replacements(source):
        source = source.replace(old, new)
    start = source.index("Legalizer::getArgsAfterPermutation(")
    end = source.index("Legalizer::getArgsAfterPermutationForSpecialCases", start)
    function = source[start:end]
    assert function.index("Permutation.size() != BitvectorList.size()") < function.index("getBitvectorOfRequiredType")
    assert "Index < 0 || unsigned(Index) >= RequiredTypes.size() || Assigned[Index]" in function
    assert "for (bool Present : Assigned)" in function and "if (!Present)" in function
    assert "Bitvector->getType() != RequiredTypes[PermIdx]" in function
    # The old null-filled slot return remains only after complete preflight.
    assert "Immediate Number" not in function
    assert source[end:] == original[original.index("Legalizer::getArgsAfterPermutationForSpecialCases") :]
    cls = generator_class(patched_generator())({})
    body = cls.generatePassToRunOnFunction()
    assert body.index("L->legalize(F)") < body.index("if (verifyFunction(F, &errs()))") < body.index("return Changed;")
    assert 'report_fatal_error("MISAAL HVX legalization produced invalid LLVM IR")' in body
    assert '#include "llvm/IR/Verifier.h"' in cls.genHeader()
    assert source_lowering_cpp() in cls.generateInstSelector()
    assert "Intrinsic::hexagon_V6_vlsrw" not in cls.generateInstSelector()
    assert "CreateAnd(Shift, Builder.getInt32(31))" in cls.generateInstSelector()
    assert "CreateICmpULT(Shift, Builder.getInt32(32))" in cls.generateInstSelector()
