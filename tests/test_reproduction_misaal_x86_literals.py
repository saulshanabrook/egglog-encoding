"""Source literal semantics and real generated selector cases; no native tools."""

import ast
import hashlib
import json
import re
from pathlib import Path
from typing import Any

import pytest

from scripts import reproduction_misaal_x86_literals as repair
from scripts.reproduction_prepare_misaal import Preparation

FIXTURES = Path(__file__).parent / "fixtures/misaal-x86-literals"


@pytest.mark.parametrize(
    ("source", "expected"),
    [
        ("(bv #b1 1)", 1),
        ("(bv #b0 1)", 0),
        ("(bv #b11 2)", 3),
        ("(bv #b10 2)", 2),
        ("(bv #b01 2)", 1),
        ("(bv #x00000020 32)", 32),
        ("(bv #xFF 8)", 255),
        ("(bv 177 8)", 177),
        ("(bv -1 32)", 2**32 - 1),
        ("(bv #x-1 8)", 255),
        ("(bv #b-10 8)", 254),
        ("(bv 257 8)", 1),
        ("(bv -257 8)", 255),
        ("(bv -1 512)", 2**512 - 1),
        ("-1", -1),
        ("177", 177),
    ],
)
def test_width_radix_and_signed_bits(source: str, expected: int) -> None:
    assert repair.parse_selector_literal(source) == expected


@pytest.mark.parametrize(
    "source",
    [
        "(bv #b2 1)",
        "(bv #xg 8)",
        "(bv #o1 1)",
        "(bv #b 1)",
        "(bv 1 0)",
        "(bv 1 -1)",
        "(bv 1 513)",
        "(bv 1 1.0)",
        "(bv 1.5 8)",
        "(bv 1 8) extra",
        "(bv 1 8 0)",
        "(bv 1)",
        "#b1",
        "1x",
        "",
        str(2**512),
    ],
)
def test_unsupported_literals_fail_closed(source: str) -> None:
    with pytest.raises(ValueError):
        repair.parse_selector_literal(source)


def generated_method(source: str, instructions: dict[str, Any]) -> str:
    # Compile the actual generator class, omitting only external import/main
    # execution. These fixture cases are present in the checked-in selector.
    class Validity:
        def checkValidityOnTarget(self, name: str, target: str) -> bool:
            assert target == "x86"
            return name in instructions

    namespace: dict[str, Any] = {"RoseISAValidityChecker": Validity}
    tree = ast.parse(source)
    selected: list[ast.stmt] = [node for node in tree.body if isinstance(node, (ast.ClassDef, ast.FunctionDef))]
    exec(compile(ast.Module(body=selected, type_ignores=[]), "original-generator", "exec"), namespace)
    result = namespace["RoseInstSelectorGenerator"]({}).generateAPattern("unused", instructions)
    assert isinstance(result, str)
    return result


def test_actual_generator_and_checked_in_cases_agree_on_srav_and_two_bit_literals() -> None:
    provenance = json.loads((FIXTURES / "provenance.json").read_text())
    for name, expected in provenance["fixtures"].items():
        assert hashlib.sha256((FIXTURES / name).read_bytes()).hexdigest() == expected
    source = (FIXTURES / "original-cases.cpp.txt").read_text()
    semantics = json.loads((FIXTURES / "semantics.json").read_text())
    generator = (FIXTURES / "RoseX86LegalizerGen.py.txt").read_text()
    assert hashlib.sha256(generator.encode()).hexdigest() == repair.SOURCE_SHA256[repair.GENERATOR]
    fixed, changes = repair.repair_generated_cases(source, semantics)
    assert len(changes) == 17  # Nine SRAV guards and eight two-bit guards in two extract cases.
    assert {c["literal"] for c in changes} == {"(bv #b1 1)", "(bv #b11 2)", "(bv #b10 2)", "(bv #b01 2)", "(bv #b00 2)"}
    actual = [c for c in changes if c["instruction"] == "_mm512_srav_epi32"]
    assert actual == [
        {"instruction": "_mm512_srav_epi32", "argument": 4, "literal": "(bv #b1 1)", "before": 177, "after": 1}
    ]
    # Only the offending digits change, preserving all original branch bodies.
    assert re.sub(r"isAMatch\(CI, \d+, -?\d+\)", "GUARD", source) == re.sub(
        r"isAMatch\(CI, \d+, -?\d+\)", "GUARD", fixed
    )
    for group in semantics.values():
        instructions = group["target_instructions"]
        original = generated_method(generator, instructions)
        regenerated = generated_method(repair.repair_generator(generator), instructions)
        expected = original
        for old, new in [
            ("0xb1_cppi", "0x1_cppi"),
            ("0xb11_cppi", "0x3_cppi"),
            ("0xb10_cppi", "0x2_cppi"),
            ("0xb01_cppi", "0x1_cppi"),
            ("0xb00_cppi", "0x0_cppi"),
        ]:
            expected = expected.replace(old, new)
        assert regenerated == expected
    # The full 14-guard native 512/32 branch now matches its captured arguments.
    branch = fixed[fixed.index("if(isAMatch(CI", fixed.index('"_mm512_srav_epi16_wrapper"')) :]
    branch = branch[: branch.index('"_mm512_srav_epi32_wrapper"')]
    guards = re.findall(r"isAMatch\(CI, (\d+), (-?\d+)\)", branch)
    guards = guards[-14:]
    values = {
        1: 0,
        3: 4294967295,
        4: 1,
        5: 32,
        6: 512,
        7: 512,
        8: 0,
        9: 512,
        10: 32,
        11: 0,
        12: 32,
        13: 32,
        14: 1,
        15: 0,
    }
    assert len(guards) == len(values)
    assert all(values[int(index)] == int(value) for index, value in guards)
    assert values[4] != 177


def test_real_generator_rejects_malformed_bv_and_retains_negative_bits() -> None:
    generator = repair.repair_generator((FIXTURES / "RoseX86LegalizerGen.py.txt").read_text())
    info: dict[str, Any] = {"_mm_srav_epi32": {"args": ["(bv -1 32)", "-1"], "arg_permute_map": [-1, -1]}}
    emitted = generated_method(generator, info)
    assert "isAMatch(CI, 0, 0xffffffff_cppi)" in emitted
    assert "isAMatch(CI, 1, -1)" in emitted
    for malformed in ["(bv #b2 1)", "1garbage", "0x1"]:
        info["_mm_srav_epi32"]["args"][0] = malformed
        with pytest.raises(ValueError, match="unsupported selector literal"):
            generated_method(generator, info)


@pytest.mark.parametrize("drift", ["guard", "order", "duplicate", "syntax"])
def test_source_or_generated_case_drift_refused(drift: str) -> None:
    source = (FIXTURES / "original-cases.cpp.txt").read_text()
    table = json.loads((FIXTURES / "semantics.json").read_text())
    if drift == "guard":
        source = source.replace("isAMatch(CI, 4, 177)", "isAMatch(CI, 4, 1)", 1)
    elif drift == "order":
        source = source.replace('"llvm.hydride._mm512_srav_epi16_dsl"', '"llvm.hydride._mm_srav_epi16_dsl"', 1)
    elif drift == "duplicate":
        table["duplicate"] = table["_mm512_srav_epi16"]
    else:
        source = source.replace("isAMatch(CI, 4, 177)", "customMatch(CI, 4, 177)", 1)
    with pytest.raises(ValueError):
        repair.repair_generated_cases(source, table)


def test_materializer_hash_gates_before_mutation(tmp_path: Path) -> None:
    hydride = tmp_path / "sources/MISAAL/Hydride"
    for relative in repair.SOURCE_SHA256:
        path = hydride / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("wrong source")
    with pytest.raises(ValueError, match="source changed"):
        repair.patch_selector_literals(Preparation(tmp_path))
    assert not (tmp_path / "patches").exists()
    assert all((hydride / name).read_text() == "wrong source" for name in repair.SOURCE_SHA256)


def test_materializer_keeps_derivations_and_only_patches_fresh_sources(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    table = json.loads((FIXTURES / "semantics.json").read_text())
    files = {
        repair.SELECTOR: (FIXTURES / "original-cases.cpp.txt").read_text(),
        repair.GENERATOR: (FIXTURES / "RoseX86LegalizerGen.py.txt").read_text(),
        repair.SEMANTICS: "semantcs = " + repr(table) + "\n",
    }
    hashes = {key: hashlib.sha256(value.encode()).hexdigest() for key, value in files.items()}
    monkeypatch.setattr(repair, "SOURCE_SHA256", hashes)
    monkeypatch.setattr(repair, "EXPECTED_REPAIR_COUNTS", (17, 11))
    for name, text in files.items():
        path = tmp_path / "sources/MISAAL/Hydride" / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
    repair.patch_selector_literals(Preparation(tmp_path))
    receipt = json.loads((tmp_path / "patches/legalizer-literal-derivation.json").read_text())
    assert receipt["source_sha256"] == hashes
    assert len(receipt["changes"]) == 17
    assert (tmp_path / "sources/MISAAL/Hydride" / repair.SEMANTICS).read_text() == files[repair.SEMANTICS]
    for name, digest in receipt["after_sha256"].items():
        assert hashlib.sha256((tmp_path / "sources/MISAAL/Hydride" / name).read_bytes()).hexdigest() == digest
    with pytest.raises(ValueError, match="source changed"):
        repair.patch_selector_literals(Preparation(tmp_path, continuation=True))
