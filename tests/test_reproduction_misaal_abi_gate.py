"""Durable source-script generation and mocked guarded execution; never native jobs."""

from __future__ import annotations

import hashlib
import json
from collections.abc import Iterator
from contextlib import contextmanager
from pathlib import Path
from typing import Any, cast

import pytest

from benchmarking.pilot import PilotProcessResult
from scripts import reproduction_misaal_abi_gate as gate
from tests.test_reproduction_misaal_patterns import (
    _CURRENT_PARAMETER_SOURCE,
    _PARAMETER_RACKET_SOURCE,
    _RACKET_COND_SOURCE,
)


@pytest.fixture
def prepared(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> dict[str, Any]:
    """Reuse verbatim source excerpts already verified against retained source hashes."""
    checkout = tmp_path / "checkout"
    source = checkout / "lib/patterns/PatternUtils.py"
    source.parent.mkdir(parents=True)
    source.write_text(_CURRENT_PARAMETER_SOURCE + '\nraise RuntimeError("module population imports must not run")\n')
    racket_source = checkout / "misaal/synthesis/param_abstract.rkt"
    racket_source.parent.mkdir(parents=True)
    racket_source.write_text(_PARAMETER_RACKET_SOURCE)
    oracle = (gate.FIXTURES / "c098-ordinary-depth2.rkt").read_text()
    header = oracle.split("(define param-test-cases", 1)[0][:-1]
    helper = checkout / gate.SOURCE
    helper.parent.mkdir(parents=True)
    helper.write_text(f"HYDRIDE_HEADER = {header!r}\n" + _RACKET_COND_SOURCE + '\nraise RuntimeError("no imports")\n')
    source_pins = {
        str(path.relative_to(checkout)): hashlib.sha256(path.read_bytes()).hexdigest()
        for path in (source, racket_source)
    }
    monkeypatch.setattr(gate.adaptation, "PARAMETER_ABI_SOURCE_SHA256", source_pins)
    monkeypatch.setattr(gate, "SOURCE_SHA256", hashlib.sha256(helper.read_bytes()).hexdigest())
    root = tmp_path / "repo"
    monkeypatch.setattr(gate, "ROOT", root)
    runtime_root = root / "benchmarks/local/reproduction/runtime"
    runtime_root.mkdir(parents=True)
    installation = tmp_path / "Racket"
    executables = {
        "racket": installation / "bin/racket",
        "raco": installation / "bin/raco",
        "z3": runtime_root / "bin/z3",
    }
    binary_hashes = {}
    for name, path in executables.items():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(name)
        path.chmod(0o700)
        binary_hashes[name] = hashlib.sha256(path.read_bytes()).hexdigest()
    monkeypatch.setattr(gate.runtime_contract, "RACKET_INSTALLATION", installation)
    monkeypatch.setattr(gate.runtime_contract, "EXECUTABLE_SHA256", binary_hashes)
    packages = {}
    modules = {}
    for name, tree in gate.runtime_contract.PACKAGE_TREES.items():
        directory = runtime_root / "addon" / name
        directory.mkdir(parents=True)
        (directory / "main.rkt").write_text(f"; {name}")
        files = {"main.rkt": hashlib.sha256((directory / "main.rkt").read_bytes()).hexdigest()}
        if name == "misaal":
            path = directory / "synthesis/param_abstract.rkt"
            path.parent.mkdir()
            path.write_bytes(racket_source.read_bytes())
            files["synthesis/param_abstract.rkt"] = source_pins["misaal/synthesis/param_abstract.rkt"]
        packages[name] = {"path": str(directory), "tree": tree, "files": files}
        if name in {"rosette", "hydride", "misaal"}:
            modules[name] = str(directory / "main.rkt")
    environment = {
        "PLTUSERHOME": str(runtime_root / "user"),
        "PLTADDONDIR": str(runtime_root / "addon"),
        "TMPDIR": str(runtime_root / "tmp"),
        "HYDRIDE_ROOT": str(checkout / "Hydride"),
        "MISAAL_Z3_PATH": str(executables["z3"]),
        "PATH": f"{runtime_root / 'bin'}:{installation / 'bin'}:/usr/bin:/bin:/usr/sbin:/sbin",
    }
    runtime = {
        "status": "source-api-blocked",
        "promoted": False,
        "workflow_ready": False,
        "implementation_sha256": hashlib.sha256(
            Path(gate.__file__).with_name("reproduction_prepare_misaal_racket.py").read_bytes()
        ).hexdigest(),
        "gates": {
            "imports": {"status": "success", "module_paths": modules},
            "tiny_solver": {"status": "success"},
            "source_four_args": {"status": "success"},
            "captured_five_args": {
                "status": "expected-api-failure",
                "modified": False,
                "sha256": gate.FIXTURE_SHA256["ki4k2nlc.rkt"],
            },
        },
        "pgid_observation": {"status": "observed-same-group", "cleanup": {"status": "drained"}},
        "racket": {
            "path": str(executables["racket"]),
            "sha256": binary_hashes["racket"],
            "raco_sha256": binary_hashes["raco"],
        },
        "solver": {"path": str(executables["z3"]), "sha256": binary_hashes["z3"]},
        "environment": environment,
        "installed_packages": packages,
    }
    runtime_path = runtime_root / "runtime.json"
    runtime_path.write_text(json.dumps(runtime))
    state: dict[str, Any] = {
        "checkout": checkout,
        "runtime_path": runtime_path,
        "runtime": runtime,
        "output": runtime_root.parent / "abi-gate",
        "calls": [],
        "locks": [],
        "failure": None,
    }

    @contextmanager
    def lock(path: Path) -> Iterator[None]:
        state["locks"].append(("acquire", path))
        try:
            yield
        finally:
            state["locks"].append(("release", path))

    def run(command: list[str], cwd: Path, prefix: Path, **kwargs: Any) -> PilotProcessResult:
        state["calls"].append({"command": command, "cwd": cwd, "options": kwargs})
        assert kwargs == {
            "timeout_sec": 60,
            "memory_limit_bytes": 5 * 1024**3,
            "require_guard": True,
            "allow_warning_pressure": True,
            "disk_reserve_bytes": 2 * 1024**3,
        }
        assert command == [
            "/usr/bin/env",
            "-i",
            *[f"{k}={v}" for k, v in environment.items()],
            str(executables["racket"]),
            command[-1],
        ]
        assert Path(command[-1]).is_file()
        stdout, stderr = prefix.with_suffix(".stdout.log"), prefix.with_suffix(".stderr.log")
        stdout.write_text("mock process output")
        negative = cwd.name.endswith("-unadapted")
        stderr.write_text("synthesize-param-expression: arity mismatch; expected: 4; given: 5" if negative else "")
        code: int | None = 1 if negative else 0
        status = "failure" if negative else "success"
        if state["failure"] and state["failure"][0] == cwd.name:
            action = state["failure"][1]
            if action == "wrong-error":
                stderr.write_text("missing collection misaal")
            elif action == "interrupted":
                raise KeyboardInterrupt
            elif action == "empty-result":
                pass
            else:
                status, code = "memory-limit", None
        if not negative:
            name = "6lt2r1zf.temp" if cwd.name == "captured" else f"{cwd.name}.temp"
            empty = state["failure"] == (cwd.name, "empty-result")
            (cwd / name).write_text("" if empty else "(MUL (SCALAR 2) (reg (bv #x00 8)))")
        return PilotProcessResult(cast(Any, status), code, 0.01, 1024, stdout, stderr, None)

    monkeypatch.setattr(gate, "exclusive_job", lock)
    monkeypatch.setattr(gate, "run_bounded_command", run)
    return state


def test_captured_fixture_is_exact_source_diagnostic() -> None:
    original = gate.FIXTURES / "ki4k2nlc.rkt"
    assert hashlib.sha256(original.read_bytes()).hexdigest() == gate.runtime_contract.CAPTURED_SHA256
    assert original.read_bytes().count(b"(TESTS ") == 28
    assert original.read_bytes().count(gate.runtime_contract.CAPTURED_BEFORE.encode()) == 1
    provenance = json.loads((gate.FIXTURES / "provenance.json").read_text())
    assert provenance["files"] == gate.FIXTURE_SHA256
    assert provenance["admitted"] is False and "not benchmark" in provenance["scope"]


def test_offline_generation_uses_source_and_exact_paper_bytes(prepared: dict[str, Any]) -> None:
    source_files = [path for path in prepared["checkout"].rglob("*") if path.is_file()]
    before = {path: path.read_bytes() for path in source_files}
    manifest = gate.prepare_programs(prepared["checkout"], prepared["output"])
    assert prepared["calls"] == []
    assert set(manifest["programs"]) == set(gate.runtime_contract.ABI_RUNS)
    for name in ("ordinary-depth2", "general-depth1"):
        assert (
            Path(manifest["programs"][name]["path"]).read_bytes() == (gate.FIXTURES / f"c098-{name}.rkt").read_bytes()
        )
        unchanged = Path(manifest["programs"][name + "-unadapted"]["path"]).read_text()
        assert ("(list 1) #t)" if name.startswith("general") else "(list 1) #f)") in unchanged
    assert all(path.read_bytes() == contents for path, contents in before.items())
    assert manifest["adaptation_receipt"]["parameter_abi"]["status"] == "complete"
    with pytest.raises(ValueError, match="fresh"):
        gate.prepare_programs(prepared["checkout"], prepared["output"])


@pytest.mark.parametrize("lock_owned", [False, True])
def test_sequential_guarded_receipts_match_sealer_contract(prepared: dict[str, Any], lock_owned: bool) -> None:
    result = gate.run_gates(prepared["runtime_path"], prepared["checkout"], prepared["output"], lock_owned=lock_owned)
    assert result["status"] == "success" and result["admitted"] is False
    assert [call["cwd"].name for call in prepared["calls"]] == [
        "ordinary-depth2",
        "ordinary-depth2-unadapted",
        "general-depth1",
        "general-depth1-unadapted",
        "captured",
    ]
    assert [action for action, _ in prepared["locks"]] == ([] if lock_owned else ["acquire", "release"])
    abi = json.loads(Path(result["abi_gate"]["path"]).read_text())
    captured = json.loads(Path(result["captured_gate"]["path"]).read_text())
    assert abi["status"] == captured["status"] == "success"
    expected_runtime = {
        "path": str(prepared["runtime_path"]),
        "sha256": hashlib.sha256(prepared["runtime_path"].read_bytes()).hexdigest(),
    }
    assert abi["runtime"] == captured["runtime"] == expected_runtime
    for row in abi["runs"]:
        assert row["passed"] is True
        gate.runtime_contract._process_evidence(
            row["process"], gate.runtime_contract.ABI_RUNS[row["name"]], abi["artifacts"], {}
        )
        if "result" in row:
            assert abi["artifacts"][row["result"]["path"]] == row["result"]["sha256"]
    gate.runtime_contract._process_evidence(captured["process"], 0, captured["artifacts"], {})
    original = Path(captured["original"]["path"]).read_bytes()
    assert Path(captured["adapted"]["path"]).read_bytes() == original.replace(
        gate.runtime_contract.CAPTURED_BEFORE.encode(),
        gate.runtime_contract.CAPTURED_AFTER.encode(),
        1,
    )
    assert captured["replacement"] == {
        "before": gate.runtime_contract.CAPTURED_BEFORE,
        "after": gate.runtime_contract.CAPTURED_AFTER,
        "count": 1,
    }
    assert captured["artifacts"][captured["output"]["path"]] == captured["output"]["sha256"]
    for reference in (result["abi_gate"], result["captured_gate"], abi["manifest"]):
        assert hashlib.sha256(Path(reference["path"]).read_bytes()).hexdigest() == reference["sha256"]


@pytest.mark.parametrize("change", ["package", "binary", "environment", "incomplete", "source", "imports"])
def test_prelaunch_changes_fail_closed(prepared: dict[str, Any], change: str) -> None:
    runtime = prepared["runtime"]
    if change == "package":
        path = Path(runtime["installed_packages"]["rosette"]["path"]) / "main.rkt"
        path.write_text("changed")
    elif change == "binary":
        Path(runtime["solver"]["path"]).write_text("changed")
    elif change == "environment":
        runtime["environment"]["PLTCOLLECTS"] = "/untrusted"
    elif change == "incomplete":
        runtime["pgid_observation"]["cleanup"]["status"] = "running"
    elif change == "imports":
        runtime["gates"]["imports"]["module_paths"]["misaal"] = "/unexpected/main.rkt"
    else:
        (prepared["checkout"] / "lib/patterns/PatternUtils.py").write_text("changed")
    prepared["runtime_path"].write_text(json.dumps(runtime))
    with pytest.raises(ValueError):
        gate.run_gates(prepared["runtime_path"], prepared["checkout"], prepared["output"])
    assert prepared["calls"] == []
    result = json.loads((prepared["output"] / "result.json").read_text())
    assert result["status"] == "failure"


@pytest.mark.parametrize(
    "name,action,count",
    [
        ("ordinary-depth2-unadapted", "wrong-error", 2),
        ("ordinary-depth2-unadapted", "memory", 2),
        ("general-depth1", "empty-result", 3),
        ("captured", "memory", 5),
        ("ordinary-depth2", "interrupted", 1),
    ],
)
def test_failure_stops_sequence_and_retains_receipts(
    prepared: dict[str, Any], name: str, action: str, count: int
) -> None:
    prepared["failure"] = (name, action)
    with pytest.raises(KeyboardInterrupt if action == "interrupted" else ValueError):
        gate.run_gates(prepared["runtime_path"], prepared["checkout"], prepared["output"])
    assert len(prepared["calls"]) == count
    result = json.loads((prepared["output"] / "result.json").read_text())
    assert result["status"] == "failure"
    target = "captured_gate" if name == "captured" else "abi_gate"
    assert result["active_gate"] == name
    if action == "memory":
        assert result["process"]["status"] == "memory-limit"
    elif action == "interrupted":
        assert "process" not in result
    partial = json.loads(Path(result[target]["path"]).read_text())
    assert partial["status"] == "failure" and partial["artifacts"]
    assert prepared["locks"][-1][0] == "release"


def test_existing_output_is_never_reused(prepared: dict[str, Any]) -> None:
    prepared["output"].mkdir()
    marker = prepared["output"] / "prior.json"
    marker.write_text("preserve")
    with pytest.raises(ValueError, match="fresh"):
        gate.run_gates(prepared["runtime_path"], prepared["checkout"], prepared["output"])
    assert marker.read_text() == "preserve" and prepared["calls"] == prepared["locks"] == []


def test_oracle_mismatch_never_reaches_native_work(prepared: dict[str, Any], monkeypatch: pytest.MonkeyPatch) -> None:
    emit = gate._emit
    monkeypatch.setattr(gate, "_emit", lambda *args: emit(*args) + b"\n")
    with pytest.raises(ValueError, match="c098 oracle"):
        gate.run_gates(prepared["runtime_path"], prepared["checkout"], prepared["output"])
    assert prepared["calls"] == []
    assert json.loads((prepared["output"] / "result.json").read_text())["status"] == "failure"


def test_changed_runtime_during_gates_is_not_success(prepared: dict[str, Any], monkeypatch: pytest.MonkeyPatch) -> None:
    run = gate.run_bounded_command

    def changed(command: list[str], cwd: Path, prefix: Path, **kwargs: Any) -> PilotProcessResult:
        result = run(command, cwd, prefix, **kwargs)
        if cwd.name == "captured":
            with prepared["runtime_path"].open("a") as stream:
                stream.write("\n")
        return result

    monkeypatch.setattr(gate, "run_bounded_command", changed)
    with pytest.raises(ValueError, match="input changed"):
        gate.run_gates(prepared["runtime_path"], prepared["checkout"], prepared["output"])
    assert len(prepared["calls"]) == 5
    result = json.loads((prepared["output"] / "result.json").read_text())
    assert result["status"] == "failure"
