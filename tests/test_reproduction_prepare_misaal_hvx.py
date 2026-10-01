"""HVX preparation/requests with controlled compiler outputs, never native jobs."""

import json
from pathlib import Path
from typing import Any

import pytest

from scripts import reproduction_prepare_misaal_cases as cases
from scripts import reproduction_prepare_misaal_hvx as preparation
from scripts.reproduction_misaal_hvx_lowering import CONCAT_WIDTHS, SOURCE_LOWERINGS
from tests.test_reproduction_misaal_hvx_lowering import FIXTURES, generator_class
from tests.test_reproduction_prepare_misaal_arm import arm_environment as arm_environment
from tests.test_reproduction_prepare_misaal_cases import environment as environment


@pytest.fixture
def hvx_environment(arm_environment: dict[str, Any], monkeypatch: pytest.MonkeyPatch) -> dict[str, Any]:
    state = arm_environment
    root, checkout, codegen = state["compiler"].parent, state["checkout"], state["codegen"]
    monkeypatch.setattr(preparation, "ROOT", root)
    semantics = json.loads((FIXTURES / "concat-semantics.json").read_text())
    groups = json.loads((FIXTURES / "source-lowerings.json").read_text())
    semantics.update({k: v for k, v in groups.items() if k != "hvx_swizzle_1"})
    for name in ("hexagon_V6_vasrh_128B", "hexagon_V6_vasrw_128B"):
        semantics[name] = {"target_instructions": {name: {"args": ["SYMBOLIC_BV_1024"], "arg_permute_map": [0]}}}
    source = codegen / "tools/low-level-codegen/InstSelectors/hexagon/RoseHexLegalizerGen.py"
    files = {
        checkout / "lib/sema/hexsemantics_new.py": f"semantics = {semantics!r}\n",
        checkout / "lib/sema/hex_swizzles.py": f"hvx_swizzles = {groups!r}\n",
        codegen / "tools/low-level-codegen/InstSelectors/common/Legalizer.cpp": (
            FIXTURES / "Legalizer.cpp.txt"
        ).read_text(),
        source: (FIXTURES / "RoseHexLegalizerGen.py.txt").read_text(),
        codegen / "tools/rosette-lifter/RosetteLifter.py": "# Source bitvector to fixed-vector mapping",
        codegen / "codegen/llvm/RoseLLVMCodeGen.py": "# Original opaque LLVM calls",
        codegen / "tools/low-level-codegen/RoseLowLevelCodeGen.py": "# Original link / disassemble / legalize pipeline",
        root / "llvm/include/llvm/IR/IntrinsicsHexagon.h": "hexagon_V6_vasrh_128B, hexagon_V6_vasrw_128B,",
        checkout / "benchmarks/hexagon/halide/Makefile": "original HVX Makefile",
        checkout / "benchmarks/hexagon/halide/hannk/common_halide.cpp": "// original HVX support",
        checkout / "frontends/halide/src/misaal.cpp": "// Original HVX plugin and wrapper paths",
        checkout / "frontends/halide/src/Rosette.cpp": "// Original expression-depth handling",
    }
    for path, text in files.items():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
    monkeypatch.setattr(
        preparation,
        "HVX_SOURCE_SHA256",
        {relative: preparation.sha256_file(checkout / relative) for relative in preparation.HVX_SOURCE_SHA256},
    )
    monkeypatch.setattr(
        cases, "HVX_MAKEFILE_SHA256", preparation.sha256_file(checkout / "benchmarks/hexagon/halide/Makefile")
    )
    catalog = root / "benchmarks/catalog.json"
    entries = json.loads(catalog.read_text())
    for name in ("blur3x3", "fully_connected"):
        source = checkout / f"benchmarks/hexagon/halide/{name}/src/{name}_generator.cpp"
        source.parent.mkdir(parents=True)
        source.write_text(f"HALIDE_REGISTER_GENERATOR(OriginalHVX, {name})\n")
        entries["cases"].append(
            {
                "id": f"misaal-hexagon-{name}",
                "family": "misaal",
                "source": f"benchmarks/hexagon/halide/{name}",
                "configuration": {"target": "hexagon"},
            }
        )
    catalog.write_text(json.dumps(entries))
    state["seed"]["preparation"] = str(root)
    state["seed"]["environment"].update(HYDRIDE_TARGET="x86", MISAAL_EQ_SAT_ITERS="7")
    state["template"].write_text(json.dumps(state["seed"]))
    upstream_step = preparation.Preparation.step

    def step(self: preparation.Preparation, name: str, command: list[str], **kwargs: Any) -> str:
        result = upstream_step(self, name, command, **kwargs)
        if name == "generate-hvx-selector":
            original = self.directory / "sources/hvx/RoseHexLegalizerGen.py"
            generator = generator_class(original.read_text())(
                {k: v for k, v in semantics.items() if k not in set(CONCAT_WIDTHS) | SOURCE_LOWERINGS.keys()}
            )
            cpp = generator.genHeader() + generator.generateLegalizerPassDeclaration()
            cpp += generator.generateLegalizerPassDefinition() + generator.generateCodeForRegisteringPass()
            if state["missing_generated"]:
                cpp = cpp.replace("Intrinsic::hexagon_V6_vasrh_128B", "Intrinsic::hexagon_V6_missing")
            (kwargs["cwd"] / "HexLegalizer.cpp").write_text(cpp)
        elif name == "build-hvx-legalizer" and not state["missing_library"]:
            build = Path(command[command.index("--build") + 1])
            build.mkdir()
            (build / "libHVXLegalizer.so").write_bytes(b"compiled HVX legalizer fixture")
        return result

    monkeypatch.setattr(preparation.Preparation, "step", step)
    monkeypatch.setattr(preparation, "exclusive_job", lambda *_: pytest.fail("in-process API must not lock"))
    return state


def test_source_selector_receipt_and_all_hvx_requests(hvx_environment: dict[str, Any]) -> None:
    state = hvx_environment
    result = preparation.prepare_misaal_hvx(
        state["output"],
        state["template"],
        compiler=state["compiler"],
        cmake=state["cmake"],
        boost_include=state["boost"],
    )
    assert result["status"] == "success", result["reason"]
    receipt = Path(result["selector_preparation"])
    selector = json.loads(receipt.read_text())
    assert selector["status"] == "success" and selector["target"] == "hvx"
    assert selector["lowering_contract"]["ordinary_intrinsics"] == ["hexagon_V6_vasrh_128B", "hexagon_V6_vasrw_128B"]
    assert selector["lowering_contract"]["native_lowering_validation"] == "pending actual canary"
    assert selector["lowering_contract"]["source_lowering_contract"] == "active-formals-portable-v1"
    assert selector["lowering_contract"]["verification"] == "inside-selector-before-ADCE"
    original_common = state["codegen"] / "tools/low-level-codegen/InstSelectors/common/Legalizer.cpp"
    assert original_common.read_bytes() == (FIXTURES / "Legalizer.cpp.txt").read_bytes()
    private_common = state["output"] / "sources/common/Legalizer.cpp"
    assert "missing intrinsic operand" in private_common.read_text()
    assert selector["prepared_sources"][str(private_common)] == preparation.sha256_file(private_common)
    cmake = (state["output"] / "cmake/CMakeLists.txt").read_text()
    assert str(private_common) in cmake and str(original_common) not in cmake
    assert not result["generator_execution"] and not result["device_execution"]
    assert "from sema.hexsemantics_new import semantics" in (state["output"] / "generate_hvx.py").read_text()
    assert (
        "L->bitsimd = false;"
        not in (state["codegen"] / "tools/low-level-codegen/InstSelectors/hexagon/RoseHexLegalizerGen.py").read_text()
    )
    assert len(result["cases"]) == 2
    for case_id, row in result["cases"].items():
        request = preparation.verified_request(Path(row["request"]))
        contract = request["hvx_link_contract"]
        assert contract["selector_preparation_sha256"] == preparation.sha256_file(receipt)
        assert contract["mode"] == "intrinsics-only"
        assert not Path(contract["omitted_wrapper"]).exists()
        assert request["environment"]["HYDRIDE_TARGET"] == "hvx"
        assert request["environment"]["HL_FORCE_HEXAGON_OPT"] == "1"
        assert request["environment"]["MISAAL_EQ_SAT_ITERS"] == "3"
        assert "MISAAL_DISABLE_FRONTEND_PATTERNS" not in request["environment"]
        assert "HYDRIDE_DISTRIBUTE_LOOK_AHEAD" not in request["environment"]
        assert request["generator_command"][-1] == "target=" + cases.HVX_TARGET
        assert request["generator_command"][-2].endswith("_hvx128")
        assert all(name.split(".")[0].endswith("_hvx128") for name in request["expected_generator_outputs"])
        if case_id.endswith("fully_connected"):
            assert request["environment"]["HL_EXPR_DEPTH"] == "2"
            assert request["environment"]["HL_SYNTH_BW"] == "16"
            assert request["environment"]["HYDRIDE_INITIAL_HASH"] == "empty_hash"
            assert "output.type=uint8" in request["generator_command"]
            assert request["configuration_variances"][0]["make_variable"] == "EXPR_DEPTH"
        else:
            assert "HL_EXPR_DEPTH" not in request["environment"]
            assert "HL_SYNTH_BW" not in request["environment"]
            assert "HYDRIDE_INITIAL_HASH" not in request["environment"]
        assert request["pattern_cache_contract"] == state["seed"]["pattern_cache_contract"]
    assert all("_generator" not in Path(command[0]).name for _, command, _ in state["commands"])


@pytest.mark.parametrize("missing", ["missing_generated", "missing_library"])
def test_failed_selector_does_not_seal_receipt_or_emit_requests(hvx_environment: dict[str, Any], missing: str) -> None:
    state = hvx_environment
    state[missing] = True
    result = preparation.prepare_misaal_hvx(
        state["output"],
        state["template"],
        compiler=state["compiler"],
        cmake=state["cmake"],
        boost_include=state["boost"],
    )
    assert result["status"] == "blocked"
    assert not (state["output"] / "selector-preparation.json").exists()
    assert all(row["request"] is None for row in result["cases"].values())


def test_selector_resource_stop_retains_failure_and_stops(hvx_environment: dict[str, Any]) -> None:
    state = hvx_environment
    state["stop"] = True
    result = preparation.prepare_misaal_hvx(
        state["output"],
        state["template"],
        compiler=state["compiler"],
        cmake=state["cmake"],
        boost_include=state["boost"],
    )
    assert result["status"] == "memory-limit"
    assert len(state["commands"]) == 1
    assert all(row["request"] is None for row in result["cases"].values())


def test_llvm_missing_intrinsic_blocks_before_generation(hvx_environment: dict[str, Any]) -> None:
    state = hvx_environment
    (state["compiler"].parent / "llvm/include/llvm/IR/IntrinsicsHexagon.h").write_text("hexagon_V6_vasrh_128B,")
    result = preparation.prepare_misaal_hvx(
        state["output"],
        state["template"],
        compiler=state["compiler"],
        cmake=state["cmake"],
        boost_include=state["boost"],
    )
    assert result["status"] == "blocked" and "absent from LLVM12" in result["reason"]
    assert not state["commands"]


def test_prepared_request_detects_selector_tampering(hvx_environment: dict[str, Any]) -> None:
    state = hvx_environment
    result = preparation.prepare_misaal_hvx(
        state["output"],
        state["template"],
        compiler=state["compiler"],
        cmake=state["cmake"],
        boost_include=state["boost"],
    )
    assert result["status"] == "success", result["reason"]
    receipt = Path(result["selector_preparation"])
    receipt.write_text(receipt.read_text() + " ")
    for row in result["cases"].values():
        with pytest.raises(ValueError, match="identity changed"):
            preparation.verified_request(Path(row["request"]))


def test_matcher_width_limit_is_checked_before_generation(
    hvx_environment: dict[str, Any], monkeypatch: pytest.MonkeyPatch
) -> None:
    state = hvx_environment
    semantics = json.loads((FIXTURES / "concat-semantics.json").read_text())
    groups = json.loads((FIXTURES / "source-lowerings.json").read_text())
    semantics.update({k: v for k, v in groups.items() if k != "hvx_swizzle_1"})
    name = "hexagon_V6_vasrh_128B"
    semantics[name] = {"target_instructions": {name: {"args": [f"(bv #x{1 << 512:x} 1024)"], "arg_permute_map": [-1]}}}
    (state["checkout"] / "lib/sema/hexsemantics_new.py").write_text(f"semantics = {semantics!r}\n")
    monkeypatch.setitem(
        preparation.HVX_SOURCE_SHA256,
        "lib/sema/hexsemantics_new.py",
        preparation.sha256_file(state["checkout"] / "lib/sema/hexsemantics_new.py"),
    )
    result = preparation.prepare_misaal_hvx(
        state["output"],
        state["template"],
        compiler=state["compiler"],
        cmake=state["cmake"],
        boost_include=state["boost"],
    )
    assert result["status"] == "blocked" and "int512_t" in result["reason"]
    assert not state["commands"]


@pytest.mark.parametrize("changed", ["ordinary-permutation", "generator-non-anchor"])
def test_unlisted_hvx_source_changes_fail_before_generation(hvx_environment: dict[str, Any], changed: str) -> None:
    state = hvx_environment
    if changed == "ordinary-permutation":
        relative = "lib/sema/hexsemantics_new.py"
        before, after = "'arg_permute_map': [0]", "'arg_permute_map': [1]"
    else:
        relative = "Hydride/codegen-generator/tools/low-level-codegen/InstSelectors/hexagon/RoseHexLegalizerGen.py"
        before, after = "InstNames = list()", "InstNames = ['unexpected']"
    assert relative not in state["seed"]["source_hashes"]
    source = state["checkout"] / relative
    original = source.read_text()
    assert before in original
    source.write_text(original.replace(before, after, 1))
    result = preparation.prepare_misaal_hvx(
        state["output"],
        state["template"],
        compiler=state["compiler"],
        cmake=state["cmake"],
        boost_include=state["boost"],
    )
    assert result["status"] == "blocked" and f"pinned HVX source changed: {relative}" in result["reason"]
    assert not state["commands"]
    assert not (state["output"] / "selector-preparation.json").exists()
    assert all(row["request"] is None for row in result["cases"].values())


def test_existing_wrapper_cannot_use_intrinsic_omission_contract(hvx_environment: dict[str, Any]) -> None:
    state = hvx_environment
    wrapper = state["codegen"] / "tools/low-level-codegen/wrappers/hvx_wrappers.ll"
    wrapper.parent.mkdir(parents=True, exist_ok=True)
    wrapper.write_text("; A real wrapper would require a separately reviewed recipe\n")
    result = preparation.prepare_misaal_hvx(
        state["output"],
        state["template"],
        compiler=state["compiler"],
        cmake=state["cmake"],
        boost_include=state["boost"],
    )
    assert result["status"] == "blocked" and "wrapper to be absent" in result["reason"]
    assert not state["commands"]
