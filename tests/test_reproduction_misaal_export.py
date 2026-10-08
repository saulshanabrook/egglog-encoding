"""Pure source/receipt controls; these tests never execute a compiler or generator."""

import json
from pathlib import Path
from typing import Any

import pytest

from scripts import reproduction_misaal_export as export


@pytest.fixture
def source(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> Path:
    root = tmp_path / "original"
    for relative in export.SOURCE_SHA256:
        path = root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(f"unchanged original {relative}\n")
    monkeypatch.setattr(
        export, "SOURCE_SHA256", {name: export.sha256_file(root / name) for name in export.SOURCE_SHA256}
    )

    def apply_patch(self: export.Preparation, checkout: Path, patch: Path) -> None:
        # Receipt tests isolate builds and patch execution; concrete patches have
        # separate application and semantic tests.
        for relative in {line[6:] for line in patch.read_text().splitlines() if line.startswith("+++ b/")}:
            target = checkout / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text((target.read_text() if target.exists() else "") + patch.name + "\n")

    monkeypatch.setattr(export.Preparation, "apply_patch", apply_patch)
    original = {path: path.read_bytes() for path in root.rglob("*") if path.is_file()}
    for patch in export.PATCHES:
        apply_patch(None, root, patch)  # type: ignore[arg-type]
    monkeypatch.setattr(
        export,
        "EXPORT_SOURCE_SHA256",
        {str(path.relative_to(root)): export.sha256_file(path) for path in root.rglob("*") if path.is_file()},
    )
    for path in list(root.rglob("*")):
        if path.is_file():
            if path in original:
                path.write_bytes(original[path])
            else:
                path.unlink()
    return root


@pytest.fixture
def preparation(source: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> dict[str, Any]:
    monkeypatch.setattr(export, "ROOT", tmp_path)
    monkeypatch.setattr(export.platform, "system", lambda: "Darwin")
    monkeypatch.setattr(export.platform, "machine", lambda: "arm64")
    for name in export.GUARD_SOURCES:
        path = tmp_path / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(name)
    llvm = tmp_path / "llvm12"
    (llvm / "bin").mkdir(parents=True)
    (llvm / "bin/llvm-config").write_text("mock tool, never executed")
    (llvm / "bin/llvm-config").chmod(0o755)
    monkeypatch.setattr(export, "LLVM12", llvm)
    for relative in (
        "frontends/halide/tools/GenGen.cpp",
        "benchmarks/arm/halide/hannk/common_halide.cpp",
        "benchmarks/arm/halide/blur5x5/src/blur5x5_generator.cpp",
    ):
        path = source / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("original generator source\n")
    template = tmp_path / "template.json"
    seed: dict[str, Any] = {
        "revision": export.MISAAL_REVISION,
        "checkout": str(source),
        "configuration": {"target": "arm"},
        "source": "benchmarks/arm/halide/blur5x5",
        "case_id": "misaal-arm-blur5x5",
        "source_hashes": dict(export.SOURCE_SHA256),
        "backend": "/retained/backend",
        "backend_sha256": "a" * 64,
        "python": "/retained/python",
        "python_sha256": "b" * 64,
        "library": "/retained/halide-build/src/libHalide.dylib",
        "library_sha256": "c" * 64,
        "generator_command": ["/retained/generator", "-o", "{output}", "-g", "blur5x5", "target=arm-64-osx"],
        "environment": {
            "HALIDE_DISTRIB": "/retained/halide-build",
            "HALIDE_SRC": str(source / "frontends/halide"),
            "PYTHONPATH": str(source / "lib"),
            "LEGALIZERS_DIR": "/absent/legalizer-directory",
        },
        "legalizer": "/absent/libARMLegalizer.so",
        "legalizer_sha256": "d" * 64,
        "llvm_as": "/absent/llvm-as",
        "llvm_as_sha256": "e" * 64,
        "hvx_link_contract": {"unused": True},
        "terminal_empty_child": "arm-empty-terminal-v1",
    }
    for key in ("backend", "python"):
        executable = tmp_path / key
        executable.write_text("retained executable, never run")
        executable.chmod(0o755)
        seed[key], seed[key + "_sha256"] = str(executable), export.sha256_file(executable)
    template.write_text(json.dumps(seed))
    state: dict[str, Any] = {
        "calls": [],
        "failure": None,
        "missing": False,
        "source": source,
        "template": template,
        "frontend": tmp_path / "benchmarks/local/reproduction/export-frontend",
        "generator": tmp_path / "benchmarks/local/reproduction/export-generator",
    }

    def step(self: export.Preparation, name: str, command: list[str], **kwargs: Any) -> str:
        state["calls"].append((name, command, kwargs))
        self.count += 1
        prefix = self.logs / f"{self.count:03}-{name}"
        export.write_json(
            prefix.with_suffix(".request.json"),
            {
                "command": command,
                "require_guard": True,
                "memory_limit_bytes": 10 * 1024**3,
                **kwargs,
            },
        )
        status = "timeout" if name == state["failure"] else "success"
        export.write_json(
            prefix.with_suffix(".result.json"), {"status": status, "returncode": 0 if status == "success" else 1}
        )
        if status != "success":
            raise RuntimeError(status)
        if name == "export-halide-build" and not state["missing"]:
            for relative in ("src/libHalide.dylib", "include/Halide.h"):
                file = self.directory / "halide-build" / relative
                file.parent.mkdir(parents=True, exist_ok=True)
                file.write_text(relative)
        if "-c" in command:
            Path(command[command.index("-o") + 1]).write_text("compiled object")
            source_path = command[command.index("-c") + 1]
            header = command[command.index("-I") + 1] + "/Halide.h"
            Path(command[command.index("-MF") + 1]).write_text(f"object: {source_path} {header}\n")
        if name == "link-export-generator":
            binary = Path(command[-1])
            binary.write_text("linked export generator")
            binary.chmod(0o755)
        return ""

    monkeypatch.setattr(export.Preparation, "step", step)
    return state


def test_frontend_and_generator_receipts_bind_original_source_new_library(preparation: dict[str, Any]) -> None:
    state = preparation
    before = {p: p.read_bytes() for p in state["source"].rglob("*") if p.is_file()}
    result = export.prepare_export_frontend(state["frontend"], state["template"])
    assert result["status"] == "success"
    receipt = state["frontend"] / "frontend.json"
    assert export.verified_frontend(receipt) == result
    assert [name for name, _, _ in state["calls"]] == ["export-halide-configure", "export-halide-build"]
    assert state["calls"][-1][1][-4:] == ["--target", "Halide", "--parallel", "2"]
    result = export.prepare_export_generator(state["generator"], state["template"], receipt)
    assert result["status"] == "success"
    request = json.loads((state["generator"] / "capture-request.json").read_text())
    export.verify_export_request(request)
    assert request["expected_generator_outputs"] == []
    assert request["egglog_export"] == export.EXPORT_POLICY
    assert not {"legalizer", "llvm_as", "hvx_link_contract", "terminal_empty_child"}.intersection(request)
    assert request["environment"]["LEGALIZERS_DIR"] == "/absent/legalizer-directory"
    assert request["library"] in result["link_command"]
    assert len(state["calls"]) == 6
    assert {p: p.read_bytes() for p in before} == before
    assert not any("selector" in name or "backend" in name for name, _, _ in state["calls"])


@pytest.mark.parametrize("failure", ["export-halide-configure", "export-halide-build"])
def test_failed_frontend_retained_and_not_reused(preparation: dict[str, Any], failure: str) -> None:
    state = preparation
    state["failure"] = failure
    result = export.prepare_export_frontend(state["frontend"], state["template"])
    assert result["status"] == "failed"
    with pytest.raises(ValueError, match="unrecognized"):
        export.verified_frontend(state["frontend"] / "frontend.json")
    assert state["calls"][-1][0] == failure


def test_success_without_library_fails(preparation: dict[str, Any]) -> None:
    preparation["missing"] = True
    result = export.prepare_export_frontend(preparation["frontend"], preparation["template"])
    assert result["status"] == "failed"
    assert "omitted" in result["reason"]


@pytest.mark.parametrize("change", ["source", "library", "generator", "link", "guard", "request", "receipt"])
def test_admission_rejects_tampering(preparation: dict[str, Any], change: str) -> None:
    state = preparation
    export.prepare_export_frontend(state["frontend"], state["template"])
    frontend = state["frontend"] / "frontend.json"
    export.prepare_export_generator(state["generator"], state["template"], frontend)
    request = json.loads((state["generator"] / "capture-request.json").read_text())
    if change in ("library", "generator"):
        Path(request[change]).write_text("changed binary")
    elif change == "source":
        (Path(request["checkout"]) / "frontends/halide/src/Module.cpp").write_text("changed source")
    elif change in ("guard", "link"):
        step = sorted((state["generator"] / "steps").glob("*.request.json"))[-1]
        data = json.loads(step.read_text())
        if change == "guard":
            data["require_guard"] = False
        else:
            data["command"].remove(request["library"])
        step.write_text(json.dumps(data))
    elif change == "request":
        request["generator_command"].append("changed-source-option")
    else:
        request["export_preparation"]["frontend_sha256"] = "0" * 64
    with pytest.raises(ValueError):
        export.verify_export_request(request)


def test_fresh_attempt_and_ambient_mode_fail_before_build(
    preparation: dict[str, Any], monkeypatch: pytest.MonkeyPatch
) -> None:
    state = preparation
    monkeypatch.setenv("MISAAL_EXPORT_MODE", export.EXPORT_POLICY)
    with pytest.raises(ValueError, match="ambient"):
        export.prepare_export_frontend(state["frontend"], state["template"])
    assert not state["frontend"].exists()
    assert not state["calls"]
    monkeypatch.delenv("MISAAL_EXPORT_MODE")
    state["frontend"].mkdir(parents=True)
    with pytest.raises(ValueError, match="fresh"):
        export.prepare_export_frontend(state["frontend"], state["template"])
    assert not state["calls"]


def test_generator_compile_failure_does_not_link_or_publish(preparation: dict[str, Any]) -> None:
    state = preparation
    export.prepare_export_frontend(state["frontend"], state["template"])
    state["failure"] = "compile-common_halide"
    result = export.prepare_export_generator(state["generator"], state["template"], state["frontend"] / "frontend.json")
    assert result["status"] == "failed"
    assert state["calls"][-1][0] == "compile-common_halide"
    assert not (state["generator"] / "capture-request.json").exists()


def test_multitarget_rejected_before_generator_build(preparation: dict[str, Any]) -> None:
    state = preparation
    export.prepare_export_frontend(state["frontend"], state["template"])
    seed = json.loads(state["template"].read_text())
    seed["generator_command"][-1] = "target=arm-64-osx,host"
    state["template"].write_text(json.dumps(seed))
    with pytest.raises(ValueError, match="single-target"):
        export.prepare_export_generator(state["generator"], state["template"], state["frontend"] / "frontend.json")
    assert len(state["calls"]) == 2
    assert not state["generator"].exists()


@pytest.mark.parametrize("command", ["frontend", "generator"])
def test_public_cli_forwards_under_shared_lock(tmp_path: Path, monkeypatch: pytest.MonkeyPatch, command: str) -> None:
    import sys
    from collections.abc import Iterator
    from contextlib import contextmanager

    observed: list[Any] = []
    monkeypatch.setattr(export, "ROOT", tmp_path)

    @contextmanager
    def locked(path: Path) -> Iterator[None]:
        observed.append(("lock", path))
        yield
        observed.append("unlock")

    def prepared(*args: Any, **kwargs: Any) -> dict[str, str]:
        observed.append((args, kwargs))
        return {"status": "success"}

    monkeypatch.setattr(export, "exclusive_job", locked)
    monkeypatch.setattr(export, "prepare_export_frontend", prepared)
    monkeypatch.setattr(export, "prepare_export_generator", prepared)
    arguments = ["export", command, "--output", "output", "--template", "template", "--timeout", "123"]
    if command == "generator":
        arguments += ["--frontend", "frontend.json"]
    monkeypatch.setattr(sys, "argv", arguments)
    assert export.main() == 0
    assert observed[0] == ("lock", tmp_path / "benchmarks/local/reproduction/stages/.heavy-job.lock")
    expected: tuple[Path, ...] = (Path("output"), Path("template"))
    if command == "generator":
        expected += (Path("frontend.json"),)
    assert observed[1] == (expected, {"timeout_sec": 123})
    assert observed[2] == "unlock"


def test_fresh_template_needs_no_old_native_products(preparation: dict[str, Any]) -> None:
    state = preparation
    seed = json.loads(state["template"].read_text())
    for key in (
        "library",
        "library_sha256",
        "legalizer",
        "legalizer_sha256",
        "llvm_as",
        "llvm_as_sha256",
        "hvx_link_contract",
        "terminal_empty_child",
    ):
        seed.pop(key)
    seed["environment"].pop("LEGALIZERS_DIR")
    state["template"].write_text(json.dumps(seed))
    assert export.verified_export_template(state["template"]) == seed
    assert not state["calls"]


def test_template_checks_every_declared_source(preparation: dict[str, Any]) -> None:
    state = preparation
    seed = json.loads(state["template"].read_text())
    source = state["source"] / next(iter(seed["source_hashes"]))
    source.write_text("changed pinned source")
    with pytest.raises(ValueError, match="prepared source changed"):
        export.verified_export_template(state["template"])
    assert not state["calls"]


@pytest.mark.parametrize("key", ["backend", "python"])
def test_template_still_requires_actual_optimizer_and_python(preparation: dict[str, Any], key: str) -> None:
    state = preparation
    seed = json.loads(state["template"].read_text())
    Path(seed[key]).write_text("changed executable")
    with pytest.raises(ValueError, match=key):
        export.verified_export_template(state["template"])
    assert not state["calls"]
