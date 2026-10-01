"""Retained-checkpoint protocol tests; all native process calls are mocked."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any, Literal

import pytest

from benchmarking.pilot import PilotProcessResult
from scripts import reproduction_continue_misaal_simd as continuation
from scripts import reproduction_prepare_misaal as preparer
from scripts.reproduction_prepare_misaal import sha256_file


@pytest.fixture
def checkpoint(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> tuple:
    monkeypatch.setattr(continuation, "ROOT", tmp_path)
    durable = tmp_path / "benchmarks/local/reproduction"
    previous = durable / "environment"
    generators, output, stage_dir = durable / "generators", durable / "continued", durable / "stage"
    checkout = previous / "sources/MISAAL"
    selector = checkout / continuation.SELECTOR
    low = selector.parents[2]
    build = previous / "legalizers-build"
    library = build / "libx86LegalizerAllArgs.so"
    llvm = tmp_path / "llvm"
    engine = tmp_path / "ordinary"

    def file(path: Path, content: Any = "unchanged prerequisite") -> Path:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content if isinstance(content, str) else json.dumps(content))
        return path

    old = (
        "bool X86LegalizationPass::runOnFunction(Function &F) {\n"
        "    Legalizer *L = new X86Legalizer();\n    return L->legalize(F);\n}\n"
    )
    file(selector, old)
    file(checkout / continuation.PATTERN_UTILS, "original pattern source")
    file(library, "old broken selector")
    file(low / "CMakeLists.txt", "retained output-suffix repair")
    file(engine)
    file(tmp_path / "scripts/reproduction_misaal_legalizer.py", "canonical audit identity")
    for name, path in (
        ("legalizer-exact-wide-constants", selector),
        ("legalizer-native-output-suffix", low / "CMakeLists.txt"),
    ):
        file(previous / f"patches/{name}.after.json", {"path": str(path), "sha256": sha256_file(path)})
        file(previous / f"patches/{name}.patch", "retained source patch")
    file(
        build / "CMakeCache.txt",
        f"CMAKE_HOME_DIRECTORY:INTERNAL={low}\nLLVM_DIR:UNINITIALIZED={llvm}/lib/cmake/llvm\nCMAKE_CXX_COMPILER:STRING=/usr/bin/clang++\n",
    )
    build_command = [
        "uv",
        "tool",
        "run",
        "--from",
        "cmake==3.31.10",
        "cmake",
        "--build",
        str(build),
        "--target",
        "x86LegalizerAllArgs",
        "--parallel",
        "1",
    ]
    file(previous / "steps/019-legalizer-build-repaired.request.json", {"command": build_command})
    file(previous / "steps/019-legalizer-build-repaired.result.json", {"status": "success"})
    opt = file(llvm / "bin/opt")
    common = {
        "checkout": str(checkout),
        "preparation": str(previous),
        "revision": continuation.MISAAL_REVISION,
        "configuration": {"target": "x86"},
        "environment": {"LEGALIZERS_DIR": str(build), "UNCHANGED": "yes"},
        "source_hashes": {},
        "compile_dependencies": {},
        "patches": {},
        "identity_paths": [str(library)],
    }
    for key, path in {
        "backend": previous / "backend",
        "llvm_as": llvm / "bin/llvm-as",
        "python": previous / "python/bin/python",
        "library": previous / "halide/libHalide.dylib",
        "legalizer": library,
    }.items():
        if not path.exists():
            file(path)
        common[key], common[key + "_sha256"] = str(path), sha256_file(path)
    cases = {}
    for case in ["blur3x3", *[f"case{index}" for index in range(31)]]:
        case_id = "misaal-x86-" + case
        binary = file(generators / case / "generator")
        request = {
            **common,
            "case_id": case_id,
            "source": "original/" + case,
            "generator": str(binary),
            "generator_sha256": sha256_file(binary),
            "generator_command": [str(binary), "-o", "{output}"],
            "expected_generator_outputs": [case + ".ll"],
        }
        path = file(generators / "requests" / (case_id + ".json"), request)
        step = file(generators / case / "build.result.json", {"status": "success"})
        cases[case_id] = {
            "id": case_id,
            "status": "prepared",
            "source": request["source"],
            "configuration": request["configuration"],
            "request": str(path),
            "request_sha256": sha256_file(path),
            "generator_sha256": request["generator_sha256"],
            "build_steps": [str(step)],
        }
    settings = file(generators / "settings.json", {"old": "immutable"})
    file(generators / "identity.json", {"original": "identity"})
    saved = {
        "status": "success",
        "revision": continuation.MISAAL_REVISION,
        "cases": cases,
        "selected_cases": list(cases.values()),
        "settings_sha256": sha256_file(settings),
    }
    file(generators / "preparation.json", saved)
    child = stage_dir / "capture/children/child-0000/capture.json"
    legal_dir = child.parent / "legalize-0000"
    linked = file(legal_dir / "source.linked.ll", "actual retained linked input")
    lowered = file(legal_dir / "source.legalize.ll", "define i32 @requested() {\n ret i32 undef\n}\n")
    original_path = "/tmp/original.legalize.ll"
    tool = {
        "executable": str(opt),
        "executable_sha256": sha256_file(opt),
        "command": [
            "opt",
            "-load",
            str(library),
            "-enable-new-pm=0",
            "-x86-hydride-legalize",
            "-adce",
            "-globaldce",
            "/tmp/original.linked.ll",
            "-S",
            "-o",
            original_path,
        ],
    }
    tools = file(legal_dir / "tools.json", [tool])
    # Match the archived validation basename to its durable copy.
    linked.rename(legal_dir / "original.linked.ll")
    lowered.rename(legal_dir / "original.legalize.ll")
    file(child, {"legalizations": [{"required_functions": ["requested"], "validation": {"path": original_path}}]})
    captured = file(stage_dir / "capture-result.json", {"children": [{"path": str(child)}]})
    stage = file(
        stage_dir / "stage.json",
        {
            "case": "misaal-x86-blur3x3",
            "capture": str(captured),
            "artifacts": {
                str(path): "sha256:" + sha256_file(path)
                for path in (
                    child,
                    captured,
                    tools,
                    legal_dir / "original.linked.ll",
                    legal_dir / "original.legalize.ll",
                )
            },
        },
    )
    state: dict[str, Any] = {"saved": saved, "old": old, "selector": selector, "library": library}
    launches = []

    def run(command: list[str], cwd: Path, prefix: Path, **options: Any) -> PilotProcessResult:
        name = prefix.name.split("-", 1)[1]
        launches.append({"name": name, "command": command, "options": options})
        out, err = prefix.with_suffix(".stdout.log"), prefix.with_suffix(".stderr.log")
        out.write_text("")
        err.write_text("")
        if state.get("refuse") == name:
            raise ValueError("memory guard refused to launch")
        if name == "hydride-revision":
            out.write_text(continuation.HYDRIDE_REVISION)
        elif name == "hydride-local-changes":
            out.write_text(
                "\n".join(str(path.relative_to(checkout / "Hydride")) for path in (selector, low / "CMakeLists.txt"))
                + state.get("extra_change", "")
            )
        elif name == "pattern-source":
            out.write_text("original pattern source")
        elif name == "x86-simd-rebuild":
            assert (output / "before/selector.cpp").read_text() == old
            assert (output / "before/libx86LegalizerAllArgs.so").read_text() == "old broken selector"
            assert "L->bitsimd = false;" in selector.read_text()
            assert (output / "simd-mode.patch").is_file()
            assert command[-4:] == ["--target", "x86LegalizerAllArgs", "--parallel", "1"]
            library.write_text("new selector")
        elif name == "retained-llvm-lowering":
            assert str(output / "native/libx86LegalizerAllArgs.so") in command
            assert (output / "before/original.linked.ll").read_text() == "actual retained linked input"
            value = "undef" if state.get("bad_lowering") else "0"
            Path(command[-1]).write_text(f"define i32 @requested() {{\n ret i32 {value}\n}}\n")
        status: Literal["memory-limit", "success"] = "memory-limit" if state.get("stop") == name else "success"
        return PilotProcessResult(status, 0 if status == "success" else -9, 0.01, 100, out, err, None)

    monkeypatch.setattr(preparer, "run_bounded_command", run)
    return generators, stage, output, engine, state, launches


def test_complete_continuation_preserves_originals_and_derives_all_requests(checkpoint: tuple) -> None:
    generators, stage, output, engine, state, launches = checkpoint
    originals = {path: path.read_bytes() for path in generators.rglob("*") if path.is_file()}
    record = continuation.continue_misaal_simd(generators, stage, output, engine)
    assert record["status"] == "success", record
    assert record["request_count"] == 32 and record["corpus_admission"] is False
    assert all(path.read_bytes() == content for path, content in originals.items())
    assert json.loads((output / "lowering-audit.json").read_text())["status"] == "success"
    assert [step["name"] for step in launches] == [
        "hydride-revision",
        "hydride-local-changes",
        "pattern-source",
        "x86-simd-rebuild",
        "retained-llvm-lowering",
        "retained-llvm-verify",
    ]
    for step in launches:
        assert step["options"]["memory_limit_bytes"] == 5 * 1024**3
        assert step["options"]["require_guard"] is True
        assert step["options"]["disk_reserve_bytes"] == 2 * 1024**3
    for path in (output / "requests").glob("*.json"):
        before = json.loads((generators / "requests" / path.name).read_text())
        after = json.loads(path.read_text())
        assert after["legalizer"] == str(output / "native/libx86LegalizerAllArgs.so")
        assert after["environment"] == {**before["environment"], "LEGALIZERS_DIR": str(output / "native")}
        assert after["source_hashes"][continuation.SELECTOR] == sha256_file(state["selector"])
        assert continuation.PATTERN_UTILS in after["source_hashes"]
        for key in (
            "generator_command",
            "expected_generator_outputs",
            "library",
            "library_sha256",
            "generator_sha256",
            "configuration",
        ):
            assert after[key] == before[key]
    with pytest.raises(ValueError, match="fresh separate"):
        continuation.continue_misaal_simd(generators, stage, output, engine)


@pytest.mark.parametrize("change", ["missing-request", "request", "failed-parent-build", "selector", "linked-input"])
def test_changed_or_partial_checkpoint_cannot_be_rebuilt(checkpoint: tuple, change: str) -> None:
    generators, stage, output, engine, state, launches = checkpoint
    if change == "missing-request":
        next((generators / "requests").glob("*.json")).unlink()
    elif change == "request":
        next((generators / "requests").glob("*.json")).write_text("{}")
    elif change == "failed-parent-build":
        path = next(generators.glob("*/build.result.json"))
        path.write_text('{"status":"failure"}')
    elif change == "selector":
        state["selector"].write_text(state["old"].replace("return L", "L->bitsimd = false;\n    return L"))
    else:
        next(stage.parent.rglob("original.linked.ll")).write_text("different LLVM")
    record = continuation.continue_misaal_simd(generators, stage, output, engine)
    assert record["status"] != "success"
    assert not (output / "settings.json").exists()
    assert not any(step["name"] == "x86-simd-rebuild" for step in launches)


@pytest.mark.parametrize("failure", ["guard", "memory", "audit", "unexpected-source"])
def test_stopped_rebuild_or_bad_diagnostic_never_publishes_requests(checkpoint: tuple, failure: str) -> None:
    generators, stage, output, engine, state, launches = checkpoint
    if failure == "guard":
        state["refuse"] = "x86-simd-rebuild"
    elif failure == "memory":
        state["stop"] = "x86-simd-rebuild"
    elif failure == "audit":
        state["bad_lowering"] = True
    else:
        state["extra_change"] = "\ncodegen-generator/tools/low-level-codegen/InstSelectors/common/Legalizer.h"
    record = continuation.continue_misaal_simd(generators, stage, output, engine)
    assert record["status"] != "success"
    assert not (output / "requests").exists() and not (output / "settings.json").exists()
    assert not any(step["name"] == "retained-llvm-verify" for step in launches)
    if failure == "guard":
        assert record["status"] == "resource-stopped"
    elif failure == "memory":
        assert record["status"] == "memory-limit"
    elif failure == "audit":
        assert json.loads((output / "lowering-audit.json").read_text())["status"] == "failure"
