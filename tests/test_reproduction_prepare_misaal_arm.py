"""ARM source preparation contracts; every native process is a controlled fixture."""

import json
import shutil
from pathlib import Path
from typing import Any

import pytest

from scripts import reproduction_prepare_misaal_arm as preparation
from scripts import reproduction_prepare_misaal_cases as cases
from tests.test_reproduction_prepare_misaal_cases import environment as environment


@pytest.fixture
def arm_environment(environment: dict[str, Any], monkeypatch: pytest.MonkeyPatch) -> dict[str, Any]:
    root = environment["compiler"].parent
    monkeypatch.setattr(preparation, "ROOT", root)
    checkout = environment["checkout"]
    codegen = checkout / "Hydride/codegen-generator"
    environment["codegen"] = codegen
    selector_source = (
        "cpp = '''bool ARMLegalizationPass::runOnFunction(Function &F) {\n"
        "  Legalizer *L = new ARMLegalizer();\n  return L->legalize(F);\n}\n'''\n"
    )
    files = {
        checkout / "lib/sema/ARMSema.py": (
            "arm_semantics = {'add': {'target_instructions': {'vadd': {}}}, "
            "'shift': {'target_instructions': {'vshift': {}}}}"
        ),
        codegen
        / "targets/arm/AllSema.py": "AllSema = {'vadd': ARMSema(imm_width=None), 'vshift': ARMSema(imm_width=(1,2))}",
        codegen / "targets/arm/intr.json": "[]",
        codegen / "targets/arm/ARMSemanticGen.py": "# Original raw metadata reader",
        codegen / "tools/low-level-codegen/InstSelectors/arm/RoseARMLegalizerGen.py": selector_source,
        codegen / "tools/low-level-codegen/InstSelectors/common/Legalizer.cpp": "// Original base implementation",
        codegen / "tools/low-level-codegen/InstSelectors/common/Legalizer.h": "// Original base declaration",
        codegen / "tools/low-level-codegen/InstSelectors/common/libpimeval.h": "// Original PIM declaration",
        checkout / "Hydride/code-synthesizer/dsl-ir/ARMSemantics.py": "semantcs = {'wrong_old_dictionary': {}}",
        checkout / "benchmarks/arm/halide/Makefile": "original ARM Makefile",
        checkout / "benchmarks/arm/halide/hannk/common_halide.cpp": "// original ARM support",
    }
    wrappers = "\n".join(
        f"define i32 @{name}() {{\n ret i32 1\n}}" for name in ("vadd_wrapper", "vshift_wrapper_1", "vshift_wrapper_2")
    )
    for relative in ("InstSelectors/arm/arm_wrappers.c.ll", "wrappers/arm_wrappers.c.ll"):
        files[codegen / "tools/low-level-codegen" / relative] = wrappers
    for path, text in files.items():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
    monkeypatch.setattr(
        preparation,
        "ARM_INPUT_PINS",
        {relative: preparation.sha256_file(checkout / relative) for relative in preparation.ARM_INPUT_PINS},
    )
    monkeypatch.setattr(
        cases, "ARM_MAKEFILE_SHA256", preparation.sha256_file(checkout / "benchmarks/arm/halide/Makefile")
    )
    catalog = root / "benchmarks/catalog.json"
    entries = json.loads(catalog.read_text())
    for name in ("blur3x3", "fully_connected"):
        source = checkout / f"benchmarks/arm/halide/{name}/src/{name}_generator.cpp"
        source.parent.mkdir(parents=True)
        source.write_text(f"HALIDE_REGISTER_GENERATOR(OriginalARM, {name})\n")
        entries["cases"].append(
            {
                "id": f"misaal-arm-{name}",
                "family": "misaal",
                "source": f"benchmarks/arm/halide/{name}",
                "configuration": {"target": "arm"},
            }
        )
    catalog.write_text(json.dumps(entries))
    seed = environment["seed"]
    seed["preparation"] = str(root)
    seed["hydride_revision"] = preparation.HYDRIDE_REVISION
    seed["environment"].update(PYTHONPATH=str(checkout / "lib"), HYDRIDE_ROOT=str(checkout / "Hydride"))
    llvm = root / "llvm"
    for relative in ("bin/llvm-as", "lib/cmake/llvm/LLVMConfig.cmake", "include/llvm/IR/Function.h"):
        path = llvm / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(b"LLVM12 prepared input")
        path.chmod(0o755)
    seed.update(llvm_as=str(llvm / "bin/llvm-as"), llvm_as_sha256=preparation.sha256_file(llvm / "bin/llvm-as"))
    environment["template"].write_text(json.dumps(seed))
    boost = root / "boost"
    for name, text in {
        "version.hpp": "#define BOOST_VERSION 108100\n",
        "multiprecision/cpp_int.hpp": "// Boost",
    }.items():
        path = boost / "boost" / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
    cmake = root / "cmake"
    cmake.write_bytes(b"CMake fixture, never executed")
    cmake.chmod(0o755)
    environment.update(boost=boost, cmake=cmake, missing_generated=False, missing_library=False, stop=False)
    compiler_step = preparation.Preparation.step

    def step(self: preparation.Preparation, name: str, command: list[str], **kwargs: Any) -> str:
        if name.startswith(("compile-", "link-")):
            return compiler_step(self, name, command, **kwargs)
        environment["commands"].append((name, command, kwargs))
        self.count += 1
        prefix = self.logs / f"{self.count:03}-{name}"
        status = "memory-limit" if environment["stop"] else "success"
        preparation.write_json(prefix.with_suffix(".request.json"), {"command": command, **kwargs})
        preparation.write_json(prefix.with_suffix(".result.json"), {"status": status})
        if status != "success":
            raise RuntimeError(status)
        if name == "generate-arm-selectors":
            generated = kwargs["cwd"]
            (generated / "ARMLegalizer.cpp").write_text(
                selector_source.split("'''", 2)[1].replace(
                    "  return L->legalize(F);", "  L->bitsimd = false;\n  return L->legalize(F);"
                )
            )
            (generated / "ARMLegalizer.h").write_text("class ARMLegalizer;\n")
            for group in ("add", "shift"):
                if group == "shift" and environment["missing_generated"]:
                    continue
                (generated / f"{group.capitalize()}Selector.cpp").write_text(
                    f"bool ARMLegalizer::legalize_{group}(CallInst *CI, Instruction *I) {{return false;}}\n"
                )
        elif name == "build-arm-legalizer" and not environment["missing_library"]:
            build = Path(command[command.index("--build") + 1])
            build.mkdir()
            (build / "libARMLegalizer.so").write_bytes(b"compiled native ARM legalizer fixture")
        return ""

    monkeypatch.setattr(preparation.Preparation, "step", step)
    monkeypatch.setattr(preparation, "exclusive_job", lambda *_: pytest.fail("in-process preparation must not lock"))
    return environment


def test_actual_frontend_semantics_and_every_original_request(arm_environment: dict[str, Any]) -> None:
    state = arm_environment
    result = preparation.prepare_misaal_arm(
        state["output"],
        state["template"],
        compiler=state["compiler"],
        cmake=state["cmake"],
        boost_include=state["boost"],
    )
    assert result["status"] == "success", result["reason"]
    assert result["inputs"]["required_wrappers"] == 3
    assert len(result["generated_sources"]) == 4
    assert not result["generator_execution"] and not result["device_execution"]
    assert "from sema.ARMSema import arm_semantics" in (state["output"] / "generate_arm.py").read_text()
    assert "L->bitsimd = false;" in (state["output"] / "sources/arm/RoseARMLegalizerGen.py").read_text()
    original = state["codegen"] / "tools/low-level-codegen/InstSelectors/arm/RoseARMLegalizerGen.py"
    assert "L->bitsimd = false;" not in original.read_text()
    build_command = next(command for name, command, _ in state["commands"] if name == "build-arm-legalizer")
    assert build_command[-2:] == ["--parallel", "1"]
    assert set(result["cases"]) == {"misaal-arm-blur3x3", "misaal-arm-fully_connected"}
    for case_id, row in result["cases"].items():
        request = preparation.verified_request(Path(row["request"]))
        assert request["configuration"] == {"target": "arm"}
        assert request["generator_command"][-1] == "target=" + cases.ARM_TARGET
        assert request["environment"]["HYDRIDE_TARGET"] == "arm"
        assert request["environment"]["HYDRIDE_DISTRIBUTE_LOOK_AHEAD"] == "1"
        assert "HL_EXPR_DEPTH" not in request["environment"]
        assert request["legalizer_sha256"] == result["legalizer_sha256"]
        assert request["environment"]["LEGALIZERS_DIR"] == str(Path(result["legalizer"]).parent)
        assert "lib/sema/ARMSema.py" in request["source_hashes"]
        assert ("output.type=uint8" in request["generator_command"]) == case_id.endswith("fully_connected")
        assert request["pattern_cache_contract"] == state["seed"]["pattern_cache_contract"]
    assert all("_generator" not in Path(command[0]).name for _, command, _ in state["commands"])


def test_default_boost_uses_seed_preparation_after_legalizer_relocation(arm_environment: dict[str, Any]) -> None:
    state = arm_environment
    original_preparation = state["compiler"].parent / "original-preparation"
    shutil.copytree(state["boost"], original_preparation / "boost_1_81_0")
    relocated = state["compiler"].parent / "continuation/native/libx86LegalizerAllArgs.so"
    relocated.parent.mkdir(parents=True)
    relocated.write_bytes(Path(state["seed"]["legalizer"]).read_bytes())
    state["seed"].update(preparation=str(original_preparation), legalizer=str(relocated))
    state["template"].write_text(json.dumps(state["seed"]))
    result = preparation.prepare_misaal_arm(
        state["output"],
        state["template"],
        compiler=state["compiler"],
        cmake=state["cmake"],
    )
    assert result["status"] == "success", result["reason"]
    assert str(original_preparation / "boost_1_81_0/boost/version.hpp") in result["inputs"]["input_hashes"]
    assert not (relocated.parent.parent / "boost_1_81_0").exists()


@pytest.mark.parametrize(
    "relative", ["lib/sema/ARMSema.py", *[p for p in preparation.ARM_INPUT_PINS if p.endswith("Gen.py")]]
)
def test_changed_original_arm_inputs_block_before_any_step(arm_environment: dict[str, Any], relative: str) -> None:
    state = arm_environment
    source = state["checkout"] / relative
    source.write_text(source.read_text() + "\n# Unrecorded local edit outside exact patch contexts\n")
    result = preparation.prepare_misaal_arm(
        state["output"],
        state["template"],
        compiler=state["compiler"],
        cmake=state["cmake"],
        boost_include=state["boost"],
    )
    assert result["status"] == "blocked" and "original pinned ARM input changed" in result["reason"]
    assert not state["commands"]


@pytest.mark.parametrize("missing", ["missing_generated", "missing_library"])
def test_absent_produced_prerequisite_blocks_every_case(arm_environment: dict[str, Any], missing: str) -> None:
    state = arm_environment
    state[missing] = True
    result = preparation.prepare_misaal_arm(
        state["output"],
        state["template"],
        compiler=state["compiler"],
        cmake=state["cmake"],
        boost_include=state["boost"],
    )
    assert result["status"] == "blocked"
    assert all(row["status"] == "not-reached" and row["request"] is None for row in result["cases"].values())
    assert not (state["output"] / "generators").exists()
    assert "settings" not in result


def test_resource_stop_has_receipt_and_no_followup_build(arm_environment: dict[str, Any]) -> None:
    state = arm_environment
    state["stop"] = True
    result = preparation.prepare_misaal_arm(
        state["output"],
        state["template"],
        compiler=state["compiler"],
        cmake=state["cmake"],
        boost_include=state["boost"],
    )
    assert result["status"] == "memory-limit"
    assert len(result["steps"]) == 1 and len(state["commands"]) == 1
    assert all(row["reason"] == "memory-limit" for row in result["cases"].values())


def test_missing_metadata_or_wrapper_cannot_be_replaced_by_stub(arm_environment: dict[str, Any]) -> None:
    state = arm_environment
    raw = state["codegen"] / "targets/arm/AllSema.py"
    before = raw.read_text()
    raw.write_text("AllSema = {}")
    with pytest.raises(ValueError, match="original pinned ARM input changed"):
        preparation.inspect_arm_inputs(state["checkout"])
    raw.write_text(before)
    wrapper = state["codegen"] / "tools/low-level-codegen/InstSelectors/arm/arm_wrappers.c.ll"
    wrapper.write_text("; valid but empty LLVM")
    with pytest.raises(ValueError, match="original pinned ARM input changed"):
        preparation.inspect_arm_inputs(state["checkout"])
    assert not state["commands"]
