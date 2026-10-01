"""Request expansion verifies produced files without running a native compiler."""

import json
import shlex
from pathlib import Path
from typing import Any

import pytest

from scripts import reproduction_prepare_misaal_cases as preparation


@pytest.fixture
def environment(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> dict[str, Any]:
    monkeypatch.setattr(preparation, "ROOT", tmp_path)
    monkeypatch.setattr(preparation.platform, "system", lambda: "Darwin")
    monkeypatch.setattr(preparation.platform, "machine", lambda: "arm64")
    checkout = tmp_path / "source"
    build = tmp_path / "halide-build"
    names = ["blur3x3", "batched_matmul_256_32bit", "tensor_shr"]
    sources = [f"benchmarks/x86/halide/{name}/src/{name}_generator.cpp" for name in names]
    for relative in (
        "benchmarks/x86/halide/Makefile",
        "benchmarks/x86/halide/hannk/common_halide.cpp",
        "frontends/halide/tools/GenGen.cpp",
        "lib/compiler/EggLogCompiler.py",
        "lib/compiler/HydrideCompiler.py",
        *sources,
    ):
        path = checkout / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("original source\n")
    for name, relative in zip(names, sources, strict=True):
        (checkout / relative).write_text(f"HALIDE_REGISTER_GENERATOR(OriginalGenerator, {name})\n")
    header = build / "include/Halide.h"
    header.parent.mkdir(parents=True)
    header.write_text("original header\n")
    local_header = checkout / "benchmarks/x86/halide/hannk/common_halide.h"
    local_header.write_text("local transitive header\n")
    makefile = checkout / "benchmarks/x86/halide/Makefile"
    monkeypatch.setattr(preparation, "MAKEFILE_SHA256", preparation.sha256_file(makefile))
    compiler = tmp_path / "clang++"
    compiler.write_bytes(b"compiler fixture, never executed")
    compiler.chmod(0o755)
    seed: dict[str, Any] = {
        "revision": preparation.MISAAL_REVISION,
        "checkout": str(checkout),
        "case_id": "misaal-x86-blur3x3",
        "source": "benchmarks/x86/halide/blur3x3",
        "configuration": {"target": "x86"},
        "source_hashes": {
            relative: preparation.sha256_file(checkout / relative)
            for relative in ["lib/compiler/EggLogCompiler.py", "lib/compiler/HydrideCompiler.py", sources[0]]
        },
        "environment": {**preparation.DEFAULTS, "HALIDE_DISTRIB": str(build), "PATH": "/prepared/bin"},
        "environment_unset": ["HL_TARGET"],
        "pattern_cache_contract": {
            "environment": "MISAAL_PATTERN_CACHE_DIR",
            "required": "fresh empty attempt-owned directory",
        },
        "expected_generator_outputs": ["blur3x3.ll"],
    }
    for key in ("backend", "llvm_as", "python", "generator", "library", "legalizer"):
        file = tmp_path / key
        file.write_bytes(key.encode())
        file.chmod(0o755)
        seed[key], seed[f"{key}_sha256"] = str(file), preparation.sha256_file(file)
    seed["generator_command"] = [seed["generator"], "-o", "{output}", f"target={preparation.TARGET}"]
    template = tmp_path / "template.json"
    template.write_text(json.dumps(seed))
    catalog = tmp_path / "benchmarks/catalog.json"
    catalog.parent.mkdir()
    catalog.write_text(
        json.dumps(
            {
                "cases": [
                    {
                        "id": f"misaal-x86-{name}",
                        "family": "misaal",
                        "source": f"benchmarks/x86/halide/{name}",
                        "configuration": {"target": "x86"},
                    }
                    for name in names
                ]
            }
        )
    )
    population = tmp_path / "benchmarks/reproduction/population.json"
    population.parent.mkdir()
    population.write_text(
        json.dumps(
            {
                "misaal": {
                    "paper_rows": [
                        {"paper": "blur3x3", "source_generator": "blur3x3"},
                        *[{"paper": f"matmul[b={batch}]", "source_generator": names[1]} for batch in (1, 2, 4)],
                    ]
                },
                "dialegg": {"runtime_programs": [], "runtime_passes": {}, "timer_nmm": [], "artifact_extra_nmm": []},
                "churchroad": {"later_evaluation": {"sources": []}},
            }
        )
    )
    state: dict[str, Any] = {
        "commands": [],
        "failure": None,
        "missing_binary": None,
        "failure_status": "failure",
        "output": tmp_path / "benchmarks/local/reproduction/case-attempt",
        "template": template,
        "compiler": compiler,
        "checkout": checkout,
        "header": header,
        "names": names,
        "seed": seed,
    }

    def step(self: preparation.Preparation, name: str, command: list[str], **kwargs: Any) -> str:
        state["commands"].append((name, command, kwargs))
        self.count += 1
        prefix = self.logs / f"{self.count:03}-{name}"
        status = state["failure_status"] if name == state["failure"] else "success"
        preparation.write_json(prefix.with_suffix(".request.json"), {"command": command, **kwargs})
        preparation.write_json(
            prefix.with_suffix(".result.json"), {"status": status, "returncode": 0 if status == "success" else 1}
        )
        if status != "success":
            raise RuntimeError(f"{name}: {status}; see {prefix}.result.json")
        destination = Path(command[command.index("-o") + 1])
        if "-c" in command:
            source = Path(command[command.index("-c") + 1])
            destination.write_bytes(b"original source object")
            depfile = Path(command[command.index("-MF") + 1])
            depfile.write_text(f"{destination}: {source} \\\n {header} {local_header}\n")
        elif name != state["missing_binary"]:
            destination.write_bytes(b"original generator executable")
            destination.chmod(0o755)
        return ""

    monkeypatch.setattr(preparation.Preparation, "step", step)

    def no_lock(*_: object) -> None:
        pytest.fail("callable API must not acquire the caller's heavy slot")

    monkeypatch.setattr(preparation, "exclusive_job", no_lock)
    return state


def test_original_generators_aliases_and_verified_inputs(environment: dict[str, Any]) -> None:
    result = preparation.prepare_misaal_cases(
        environment["output"], environment["template"], compiler=environment["compiler"]
    )
    assert result["status"] == "success"
    assert not result["generator_execution"] and not result["device_execution"]
    assert list(result["cases"]) == [f"misaal-x86-{name}" for name in environment["names"]]
    assert len(environment["commands"]) == 2 + 2 * len(environment["names"])
    assert all(command[0] == str(environment["compiler"]) for _, command, _ in environment["commands"])
    for name, row in zip(environment["names"], result["cases"].values(), strict=True):
        request = preparation.verified_request(Path(row["request"]))
        assert row["status"] == "prepared" and len(row["build_steps"]) == 2
        assert request["source"] == f"benchmarks/x86/halide/{name}"
        assert request["configuration"] == {"target": "x86"}
        assert request["environment_unset"] == ["HL_TARGET"]
        assert request["pattern_cache_contract"] == environment["seed"]["pattern_cache_contract"]
        assert "MISAAL_PATTERN_CACHE_DIR" not in request["environment"]
        assert request["generator_command"][-1] == f"target={preparation.TARGET}"
        assert request["generator_command"][6] == name
        assert request["source_hashes"][f"benchmarks/x86/halide/{name}/src/{name}_generator.cpp"]
        assert "benchmarks/x86/halide/hannk/common_halide.h" in request["source_hashes"]
        assert str(environment["header"]) in request["identity_paths"]
        assert not any("batch=" in argument for argument in request["generator_command"])
    assert result["cases"]["misaal-x86-batched_matmul_256_32bit"]["paper_aliases"] == [
        "matmul[b=1]",
        "matmul[b=2]",
        "matmul[b=4]",
    ]
    assert result["cases"]["misaal-x86-tensor_shr"]["scope"] == "artifact-extra"
    with pytest.raises(ValueError, match="fresh immutable"):
        preparation.prepare_misaal_cases(
            environment["output"], environment["template"], compiler=environment["compiler"]
        )


def test_absent_output_never_publishes_request(environment: dict[str, Any]) -> None:
    environment["missing_binary"] = "link-blur3x3"
    result = preparation.prepare_misaal_cases(
        environment["output"], environment["template"], compiler=environment["compiler"]
    )
    row = result["cases"]["misaal-x86-blur3x3"]
    assert result["status"] == "blocked" and row["status"] == "blocked"
    assert "omitted" in row["reason"] and row["request"] is None
    assert not (environment["output"] / "requests/misaal-x86-blur3x3.json").exists()
    assert Path(result["settings"]).is_file()  # Other prepared cases remain usable, with failures explicit.


def test_compiler_failure_is_retained_without_contaminating_next_case(environment: dict[str, Any]) -> None:
    environment["failure"] = "compile-blur3x3_generator"
    source = (
        environment["checkout"]
        / "benchmarks/x86/halide/batched_matmul_256_32bit/src/batched_matmul_256_32bit_generator.cpp"
    )
    source.write_text("wrong registration")
    result = preparation.prepare_misaal_cases(
        environment["output"], environment["template"], compiler=environment["compiler"]
    )
    first, second, third = result["cases"].values()
    assert first["status"] == "failure" and len(first["build_steps"]) == 1
    assert json.loads(Path(first["build_steps"][0]).read_text())["returncode"] == 1
    assert second["status"] == "blocked" and not second["build_steps"]
    assert third["status"] == "prepared"


def test_resource_stop_accounts_for_every_selected_case(environment: dict[str, Any]) -> None:
    environment.update(failure="compile-blur3x3_generator", failure_status="memory-limit")
    result = preparation.prepare_misaal_cases(
        environment["output"], environment["template"], compiler=environment["compiler"]
    )
    assert result["status"] == "memory-limit"
    assert [row["status"] for row in result["cases"].values()] == ["memory-limit", "not-reached", "not-reached"]
    assert len(environment["commands"]) == 3
    for case_id in result["cases"]:
        assert (environment["output"] / f"case-{case_id}.json").is_file()
    assert "settings" not in result


@pytest.mark.parametrize("selection", [[], ["misaal-arm-blur3x3"], ["misaal-x86-blur3x3"] * 2])
def test_rejects_empty_non_x86_or_duplicate_selection(environment: dict[str, Any], selection: list[str]) -> None:
    with pytest.raises(ValueError, match="selected|selectors"):
        preparation.prepare_misaal_cases(
            environment["output"], environment["template"], compiler=environment["compiler"], case_ids=selection
        )
    assert not environment["commands"] and not environment["output"].exists()


def test_changed_library_refuses_preparation(environment: dict[str, Any]) -> None:
    Path(environment["seed"]["library"]).write_bytes(b"changed library")
    with pytest.raises(ValueError, match="MISAAL library identity changed"):
        preparation.prepare_misaal_cases(
            environment["output"], environment["template"], compiler=environment["compiler"]
        )
    assert not environment["commands"]


def test_dependency_closure_handles_escaped_spaces_and_requires_original_source(tmp_path: Path) -> None:
    source = tmp_path / "source file.cpp"
    source.write_bytes(b"source")
    dependency = tmp_path / "generator.d"
    # Clang's dependency format escapes spaces rather than shell-quoting the name.
    dependency.write_text("object.o: " + str(source).replace(" ", "\\ ") + "\n")
    assert preparation.compile_dependencies(dependency, tmp_path, {source}) == {
        str(source): preparation.sha256_file(source)
    }
    dependency.write_text("object.o: " + shlex.quote(str(source)) + "\n")
    with pytest.raises(ValueError, match="omitted"):
        preparation.compile_dependencies(dependency, tmp_path, {tmp_path / "missing.cpp"})


def test_shared_support_failure_blocks_every_case(environment: dict[str, Any]) -> None:
    environment["failure"] = "compile-GenGen"
    result = preparation.prepare_misaal_cases(
        environment["output"], environment["template"], compiler=environment["compiler"]
    )
    assert result["status"] == "failure" and len(result["support_steps"]) == 1
    assert "shared original generator support failed" in result["reason"]
    assert len(result["cases"]) == 3
    assert all(row["status"] == "not-reached" and row["request"] is None for row in result["cases"].values())
    assert len(environment["commands"]) == 1


def test_explicit_selection_compiles_only_selected_generator(environment: dict[str, Any]) -> None:
    result = preparation.prepare_misaal_cases(
        environment["output"],
        environment["template"],
        compiler=environment["compiler"],
        case_ids=["misaal-x86-tensor_shr"],
    )
    assert list(result["cases"]) == ["misaal-x86-tensor_shr"]
    assert len(environment["commands"]) == 4
    assert result["status"] == "success"
