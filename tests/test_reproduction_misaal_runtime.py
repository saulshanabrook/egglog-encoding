"""Data-only runtime identity tests; no Racket, solver, installation, or download."""

from __future__ import annotations

import hashlib
import json
import shutil
import subprocess
from pathlib import Path
from typing import Any

import pytest

from scripts import reproduction_misaal_runtime as runtime


@pytest.fixture
def evidence(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> dict[str, Any]:
    def forbidden(*args: Any, **kwargs: Any) -> None:
        raise AssertionError("The seal and verifier must never launch a native process")

    monkeypatch.setattr(subprocess, "run", forbidden)
    monkeypatch.setattr(subprocess, "Popen", forbidden)

    def retain(path: Path, value: str | dict[str, Any]) -> dict[str, str]:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(value, indent=2) if isinstance(value, dict) else value)
        return {"path": str(path), "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}

    root = tmp_path / "preparation"
    installation = tmp_path / "Racket v9.2"
    binaries = {}
    for name in ("racket", "raco", "z3"):
        path = (root if name == "z3" else installation) / "bin" / name
        binaries[name] = retain(path, f"synthetic {name} bytes")
        path.chmod(0o755)
    monkeypatch.setattr(runtime, "RACKET_INSTALLATION", installation)
    monkeypatch.setattr(runtime, "EXECUTABLE_SHA256", {name: row["sha256"] for name, row in binaries.items()})
    helper = retain(tmp_path / "implementation/abi.py", "synthetic ABI implementation")
    preparer = retain(
        tmp_path / "implementation/preparer.py",
        (
            'HEADER = "header\\n"\nSOLVE = "solver\\n"\nPARAMETER_SMOKE = "four arguments\\n"\n'
            'raise RuntimeError("historical source must never execute")\n'
            'def prepare():\n    imports.write_text(HEADER + "imports\\n")\n'
        ),
    )
    monkeypatch.setattr(runtime, "ABI_HELPER", Path(helper["path"]))
    monkeypatch.setattr(runtime, "PREPARER", Path(preparer["path"]))
    checkout = tmp_path / "MISAAL"
    source_pins = {}
    source_hashes = {}
    for relative in (*runtime.PARAMETER_ABI_SOURCE_SHA256, runtime.SOURCE):
        ref = retain(checkout / relative, f"synthetic source {relative}")
        source_pins[ref["path"]] = ref["sha256"]
        source_hashes[relative] = ref["sha256"]
    monkeypatch.setattr(
        runtime, "PARAMETER_ABI_SOURCE_SHA256", {key: source_hashes[key] for key in runtime.PARAMETER_ABI_SOURCE_SHA256}
    )
    monkeypatch.setattr(runtime, "SOURCE_SHA256", source_hashes[runtime.SOURCE])
    original = retain(
        tmp_path / "capture/original.rkt", f"#lang rosette\n; genuine retained test data\n{runtime.CAPTURED_BEFORE}\n"
    )
    monkeypatch.setattr(runtime, "CAPTURED_SHA256", original["sha256"])
    for name in ("addon", "user", "tmp"):
        (root / name).mkdir()
    packages: dict[str, Any] = {}
    for name, tree in runtime.PACKAGE_TREES.items():
        directory = root / "addon/pkgs" / name
        source = retain(directory / "main.rkt", f"synthetic {name} source")
        retain(directory / "compiled/main_rkt.zo", f"synthetic {name} bytecode")
        packages[name] = {"path": str(directory), "tree": tree, "files": {"main.rkt": source["sha256"]}}
    retain(root / "addon/links.rktd", "synthetic package registry")
    retain(installation / "collects/compiled/runtime.zo", "synthetic installed bytecode")
    environment = {
        "PLTUSERHOME": str(root / "user"),
        "PLTADDONDIR": str(root / "addon"),
        "TMPDIR": str(root / "tmp"),
        "HYDRIDE_ROOT": str(checkout / "Hydride"),
        "MISAAL_Z3_PATH": binaries["z3"]["path"],
        "PATH": f"{root / 'bin'}:{installation / 'bin'}:/usr/bin:/bin:/usr/sbin:/sbin",
    }
    prefix = [
        "/usr/bin/env",
        "-i",
        *[f"{key}={value}" for key, value in environment.items()],
        binaries["racket"]["path"],
    ]
    scan = retain(root / "source-scan.json", {"status": "no-escape-patterns-found", "findings": [], "files_scanned": 5})
    pgids = {
        "status": "observed-same-group",
        "expected_pgid": 42,
        "processes": [
            {"pid": 45, "pgid": 42, "executable": binaries["racket"]["path"]},
            {"pid": 46, "pgid": 42, "executable": binaries["z3"]["path"]},
        ],
        "cleanup": {"status": "drained", "release": "sent", "racket_returncode": 0, "snapshots": [{"remaining": []}]},
    }
    pgids_ref = retain(root / "pgids.json", pgids)
    four = retain(root / "smokes/parameter-four-args.rkt", "header\nfour arguments\n")
    retain(root / "smokes/captured-five-args.rkt", Path(original["path"]).read_text())
    retain(root / "smokes/imports.rkt", "header\nimports\n")
    retain(root / "smokes/solver.rkt", "header\nsolver\n")
    python = retain(tmp_path / "python", "synthetic Python executable")
    bootstrap = (
        f"import runpy,sys; sys.path.insert(0,{str(runtime.PREPARER.parent.parent)!r}); "
        f"runpy.run_path({str(runtime.PREPARER)!r}, run_name='__main__')"
    )
    child = [python["path"], "-c", bootstrap]
    isolated = prefix[:-1]
    racket, raco, z3 = (binaries[name]["path"] for name in ("racket", "raco", "z3"))
    commands = [
        ("acquire-pinned-packages", [*child, "_acquire", str(root / "sources")]),
        ("racket-version", [*isolated, racket, "--version"]),
        ("z3-version", [*isolated, z3, "--version"]),
        ("installation-packages", [*isolated, raco, "pkg", "show", "--all", "--long", "--dir"]),
        *[
            (
                f"install-{name}",
                [
                    *isolated,
                    raco,
                    "pkg",
                    "install",
                    "--scope",
                    "user",
                    "--batch",
                    "--deps",
                    "fail",
                    "--copy",
                    "--no-setup",
                    "--name",
                    name,
                    str(root / "sources" / name),
                ],
            )
            for name in runtime.PACKAGE_TREES
        ],
        ("isolated-packages", [*isolated, raco, "pkg", "show", "--all", "--long", "--dir"]),
        ("compile-imports", [*isolated, raco, "make", str(root / "smokes/imports.rkt")]),
        ("imports", [*isolated, racket, str(root / "smokes/imports.rkt")]),
        (
            "tiny-solver-pgid",
            [*isolated, *child, "_observe", racket, str(root / "smokes/solver.rkt"), z3, str(root / "pgids.json")],
        ),
        ("parameter-four-args", [*isolated, racket, str(root / "smokes/parameter-four-args.rkt")]),
        ("captured-five-args", [*isolated, racket, str(root / "smokes/captured-five-args.rkt")]),
    ]
    steps = []
    arity = "synthesize-param-expression: arity mismatch; expected: 4 given: 5"
    for name, command in commands:
        negative = name == "captured-five-args"
        stdout = retain(root / "steps" / name / "stdout", "synthetic log")
        stderr = retain(root / "steps" / name / "stderr", arity if negative else "")
        steps.append(
            {
                "name": name,
                "command": command,
                "cwd": str(root),
                "status": "failure" if negative else "success",
                "returncode": int(negative),
                "stdout_path": stdout["path"],
                "stderr_path": stderr["path"],
            }
        )
    record = {
        "status": "source-api-blocked",
        "promoted": False,
        "workflow_ready": False,
        "gates": {
            "imports": {
                "status": "success",
                "module_paths": {
                    name: str(Path(packages[name]["path"]) / "main.rkt") for name in ("hydride", "misaal", "rosette")
                },
            },
            "tiny_solver": {"status": "success", "pgids_sha256": pgids_ref["sha256"]},
            "source_four_args": {"status": "success", "sha256": four["sha256"]},
            "captured_five_args": {"status": "expected-api-failure", "sha256": original["sha256"], "modified": False},
        },
        "racket": {**binaries["racket"], "raco_sha256": binaries["raco"]["sha256"]},
        "solver": binaries["z3"],
        "environment": environment,
        "installed_packages": packages,
        "implementation_sha256": preparer["sha256"],
        "source_scan": scan,
        "pgid_observation": pgids,
        "steps": steps,
    }
    runtime_ref = retain(root / "runtime.json", record)
    programs, runs, artifacts = {}, [], {}
    arity = "synthesize-param-expression: arity mismatch; expected: 4 given: 5"
    for name, code in runtime.ABI_RUNS.items():
        program = retain(tmp_path / "original-programs" / f"{name}.rkt", f"synthetic source-emitted {name}")
        actual = retain(tmp_path / "live-programs" / f"{name}.rkt", Path(program["path"]).read_text())
        programs[name] = {**program, "expected_exit": code}
        stdout = retain(tmp_path / "abi-runs" / name / "stdout", "output")
        stderr = retain(tmp_path / "abi-runs" / name / "stderr", arity if code else "")
        artifacts.update({row["path"]: row["sha256"] for row in (stdout, stderr)})
        row = {
            "name": name,
            "command": [*prefix, actual["path"]],
            "program_sha256": program["sha256"],
            "passed": True,
            "process": {
                "status": "failure" if code else "success",
                "returncode": code,
                "stdout_path": stdout["path"],
                "stderr_path": stderr["path"],
            },
        }
        if not code:
            result = retain(tmp_path / "abi-runs" / name / "result.temp", "(reg 0)")
            row["result"] = {**result, "text": "(reg 0)"}
            artifacts[result["path"]] = result["sha256"]
        runs.append(row)
    source_request = {
        "checkout": str(checkout),
        "revision": runtime.REVISION,
        "parameter_abi": runtime.PARAMETER_ABI_CONTRACT,
        "source_hashes": runtime.PARAMETER_ABI_SOURCE_SHA256,
    }
    manifest = retain(
        tmp_path / "abi/manifest.json",
        {
            "request": source_request,
            "programs": programs,
            "source_pins": source_pins,
            "adaptation_receipt": {
                "parameter_abi": {
                    "contract": runtime.PARAMETER_ABI_CONTRACT,
                    "status": "complete",
                    "paper_revision": runtime.PAPER_REVISION,
                    "sources": runtime.PARAMETER_ABI_SOURCE_SHA256,
                    "implementation_sha256": helper["sha256"],
                    "adapted_methods": {"emit_synthesize_query": "pinned", "generate_param_expr_general": "pinned"},
                }
            },
        },
    )
    abi = retain(
        tmp_path / "abi/result.json",
        {
            "status": "success",
            "runtime": runtime_ref,
            "manifest": manifest,
            "implementation": helper,
            "runs": runs,
            "artifacts": artifacts,
        },
    )
    adapted = retain(
        tmp_path / "captured/adapted.rkt",
        Path(original["path"]).read_text().replace(runtime.CAPTURED_BEFORE, runtime.CAPTURED_AFTER, 1),
    )
    stdout = retain(tmp_path / "captured/stdout", "output")
    stderr = retain(tmp_path / "captured/stderr", "")
    result = retain(tmp_path / "captured/output.temp", "(reg 9)")
    captured = retain(
        tmp_path / "captured/result.json",
        {
            "status": "success",
            "runtime": runtime_ref,
            "contract": runtime.PARAMETER_ABI_CONTRACT,
            "original": original,
            "adapted": adapted,
            "replacement": {"before": runtime.CAPTURED_BEFORE, "after": runtime.CAPTURED_AFTER, "count": 1},
            "command": [*prefix, adapted["path"]],
            "process": {
                "status": "success",
                "returncode": 0,
                "stdout_path": stdout["path"],
                "stderr_path": stderr["path"],
            },
            "output": {**result, "text": "(reg 9)"},
            "artifacts": {row["path"]: row["sha256"] for row in (adapted, stdout, stderr, result)},
        },
    )
    request = {
        **source_request,
        "source_hashes": source_hashes,
        "racket": binaries["racket"]["path"],
        "racket_sha256": binaries["racket"]["sha256"],
        "racket_group_containment": runtime.GROUP_CONTRACT,
        "environment": {**environment, "PATH": f"{root / 'bin'}:{installation / 'bin'}:/existing/native/bin:/usr/bin"},
        "environment_unset": list(runtime.REQUIRED_UNSET),
    }
    return {
        "root": root,
        "installation": installation,
        "runtime": Path(runtime_ref["path"]),
        "abi": Path(abi["path"]),
        "captured": Path(captured["path"]),
        "seal": tmp_path / "seal.json",
        "request": request,
        "retain": retain,
    }


@pytest.fixture
def sealed(evidence: dict[str, Any]) -> dict[str, Any]:
    seal = runtime.seal_runtime(
        evidence["runtime"], evidence["abi"], evidence["seal"], captured_gate_path=evidence["captured"]
    )
    evidence["request"]["racket_runtime"] = {
        "path": str(evidence["seal"]),
        "sha256": hashlib.sha256(evidence["seal"].read_bytes()).hexdigest(),
    }
    evidence["description"] = seal
    return evidence


def test_seal_preserves_historical_inputs_and_allows_only_explicit_new_request(evidence: dict[str, Any]) -> None:
    before = {name: evidence[name].read_bytes() for name in ("runtime", "abi", "captured")}
    request_before = json.dumps(evidence["request"], sort_keys=True)
    seal = runtime.seal_runtime(
        evidence["runtime"], evidence["abi"], evidence["seal"], captured_gate_path=evidence["captured"]
    )
    assert {name: evidence[name].read_bytes() for name in before} == before
    assert json.dumps(evidence["request"], sort_keys=True) == request_before
    assert seal["status"] == "source-api-compatible"
    assert set(seal["code_trees"]) == {"addon", "user", "racket_installation"}
    assert json.loads(before["runtime"])["status"] == "source-api-blocked"
    with pytest.raises(ValueError, match="Incomplete runtime request"):
        runtime.verify_runtime(evidence["request"])
    evidence["request"]["racket_runtime"] = {
        "path": str(evidence["seal"]),
        "sha256": hashlib.sha256(evidence["seal"].read_bytes()).hexdigest(),
    }
    assert runtime.verify_runtime(evidence["request"]) == seal
    with pytest.raises(ValueError, match="fresh"):
        runtime.seal_runtime(
            evidence["runtime"], evidence["abi"], evidence["seal"], captured_gate_path=evidence["captured"]
        )


@pytest.mark.parametrize(
    "change", ["changed-zo", "added-zo", "removed-zo", "registry-link", "installed-zo", "user-cache"]
)
def test_compiled_code_membership_and_registry_changes_invalidate_seal(sealed: dict[str, Any], change: str) -> None:
    root = sealed["root"]
    source = root / "addon/pkgs/misaal/main.rkt"
    before = source.read_bytes()
    compiled = root / "addon/pkgs/misaal/compiled/main_rkt.zo"
    if change == "changed-zo":
        compiled.write_text("changed compiled code with unchanged source")
    elif change == "added-zo":
        compiled.with_name("new.zo").write_text("new consumed code")
    elif change == "removed-zo":
        compiled.unlink()
    elif change == "registry-link":
        registry = root / "addon/links.rktd"
        registry.unlink()
        registry.symlink_to(source)
    elif change == "installed-zo":
        (sealed["installation"] / "collects/compiled/runtime.zo").write_text("changed installation bytecode")
    else:
        (root / "user/new.zo").write_text("new user bytecode")
    with pytest.raises(ValueError, match="changed after sealing"):
        runtime.verify_runtime(sealed["request"])
    assert source.read_bytes() == before


@pytest.mark.parametrize(
    "which",
    ["runtime", "abi", "captured", "scan", "pgids", "live-script", "negative-log", "positive-result", "helper", "seal"],
)
def test_retained_evidence_changes_are_rejected(sealed: dict[str, Any], which: str) -> None:
    abi = json.loads(sealed["abi"].read_text())
    positive = next(row for row in abi["runs"] if row["name"] == "ordinary-depth2")
    negative = next(row for row in abi["runs"] if row["name"] == "ordinary-depth2-unadapted")
    paths = {
        **{name: sealed[name] for name in ("runtime", "abi", "captured", "seal")},
        "scan": sealed["root"] / "source-scan.json",
        "pgids": sealed["root"] / "pgids.json",
        "live-script": Path(positive["command"][-1]),
        "negative-log": Path(negative["process"]["stderr_path"]),
        "positive-result": Path(positive["result"]["path"]),
        "helper": runtime.ABI_HELPER,
    }
    with paths[which].open("a") as stream:
        stream.write("changed")
    with pytest.raises(ValueError, match="identity changed"):
        runtime.verify_runtime(sealed["request"])


@pytest.mark.parametrize(
    "change",
    [
        "missing-run",
        "duplicate-run",
        "failed-positive",
        "bad-negative-code",
        "not-passed",
        "missing-output",
        "missing-log",
        "wrong-env",
    ],
)
def test_incomplete_abi_gate_cannot_be_sealed(evidence: dict[str, Any], change: str) -> None:
    gate = json.loads(evidence["abi"].read_text())
    positive = next(row for row in gate["runs"] if row["name"] == "ordinary-depth2")
    negative = next(row for row in gate["runs"] if row["name"] == "ordinary-depth2-unadapted")
    if change == "missing-run":
        gate["runs"].pop()
    elif change == "duplicate-run":
        gate["runs"][-1] = gate["runs"][0]
    elif change == "failed-positive":
        positive["process"]["status"] = "failure"
    elif change == "bad-negative-code":
        negative["process"]["returncode"] = -9
    elif change == "not-passed":
        positive["passed"] = False
    elif change == "missing-output":
        del positive["result"]
    elif change == "missing-log":
        del gate["artifacts"][positive["process"]["stdout_path"]]
    else:
        positive["command"].insert(2, "PLTCOLLECTS=/ambient")
    evidence["retain"](evidence["abi"], gate)
    with pytest.raises(ValueError):
        runtime.seal_runtime(
            evidence["runtime"], evidence["abi"], evidence["seal"], captured_gate_path=evidence["captured"]
        )
    assert not evidence["seal"].exists()


@pytest.mark.parametrize(
    "change", ["failed", "wrong-runtime", "extra-edit", "wrong-replacement", "wrong-process", "empty-result"]
)
def test_captured_gate_preserves_original_data_and_exact_call(evidence: dict[str, Any], change: str) -> None:
    gate = json.loads(evidence["captured"].read_text())
    if change == "failed":
        gate["status"] = "failure"
    elif change == "wrong-runtime":
        gate["runtime"]["sha256"] = "0" * 64
    elif change == "extra-edit":
        gate["adapted"] = evidence["retain"](Path(gate["adapted"]["path"]), "changed test data")
    elif change == "wrong-replacement":
        gate["replacement"]["count"] = 2
    elif change == "wrong-process":
        gate["process"]["returncode"] = 1
    else:
        gate["output"]["text"] = ""
    evidence["retain"](evidence["captured"], gate)
    with pytest.raises(ValueError):
        runtime.seal_runtime(
            evidence["runtime"], evidence["abi"], evidence["seal"], captured_gate_path=evidence["captured"]
        )


@pytest.mark.parametrize(
    "change",
    [
        "missing-unset",
        "reintroduced-root",
        "reintroduced-zo",
        "wrong-addon",
        "wrong-user",
        "path-prepend",
        "wrong-abi",
        "wrong-lease",
        "wrong-source",
        "wrong-checkout",
        "wrong-racket",
        "wrong-schema",
    ],
)
def test_request_cannot_bypass_runtime_or_mixed_revision_contract(sealed: dict[str, Any], change: str) -> None:
    request = sealed["request"]
    if change == "missing-unset":
        request["environment_unset"].remove("PLTCOMPILEDROOTS")
    elif change == "reintroduced-root":
        request["environment"]["PLTCOMPILEDROOTS"] = "/ambient"
    elif change == "reintroduced-zo":
        request["environment"]["PLT_ZO_PATH"] = "other-compiled"
    elif change in ("wrong-addon", "wrong-user"):
        request["environment"]["PLTADDONDIR" if change == "wrong-addon" else "PLTUSERHOME"] = "/ambient"
    elif change == "path-prepend":
        request["environment"]["PATH"] = "/ambient/bin:" + request["environment"]["PATH"]
    elif change == "wrong-abi":
        request["parameter_abi"] = "ignore-fifth-argument"
    elif change == "wrong-lease":
        request["racket_group_containment"] = "arbitrary-process-groups"
    elif change == "wrong-source":
        request["source_hashes"][runtime.SOURCE] = "0" * 64
    elif change == "wrong-checkout":
        request["checkout"] = "/different/source"
    elif change == "wrong-racket":
        request["racket"] = "/opt/homebrew/bin/racket"
    else:
        seal = json.loads(sealed["seal"].read_text())
        seal["schema"] = "unreviewed"
        request["racket_runtime"] = sealed["retain"](sealed["seal"], seal)
    with pytest.raises(ValueError):
        runtime.verify_runtime(request)


def test_seal_cannot_modify_its_own_hashed_tree(evidence: dict[str, Any]) -> None:
    output = evidence["root"] / "addon/seal.json"
    with pytest.raises(ValueError, match="outside its immutable code trees"):
        runtime.seal_runtime(evidence["runtime"], evidence["abi"], output, captured_gate_path=evidence["captured"])
    assert not output.exists()


@pytest.mark.parametrize(
    "change",
    [
        "missing-gate",
        "unclear-scan",
        "undrained",
        "detached",
        "missing-solver",
        "package-tree",
        "package-escape",
        "runtime-environment",
    ],
)
def test_incomplete_prerequisite_evidence_never_seals(evidence: dict[str, Any], change: str) -> None:
    record = json.loads(evidence["runtime"].read_text())
    if change == "missing-gate":
        del record["gates"]["source_four_args"]
    elif change == "unclear-scan":
        scan = json.loads(Path(record["source_scan"]["path"]).read_text())
        scan["status"] = "review-required"
        record["source_scan"] = evidence["retain"](Path(record["source_scan"]["path"]), scan)
    elif change in ("undrained", "detached", "missing-solver"):
        pgids = record["pgid_observation"]
        if change == "undrained":
            pgids["cleanup"]["status"] = "unverified"
        elif change == "detached":
            pgids["processes"][-1]["pgid"] += 1
        else:
            pgids["processes"].pop()
        ref = evidence["retain"](evidence["root"] / "pgids.json", pgids)
        record["gates"]["tiny_solver"]["pgids_sha256"] = ref["sha256"]
    elif change == "package-tree":
        record["installed_packages"]["rosette"]["tree"] = "0" * 40
    elif change == "package-escape":
        record["installed_packages"]["rosette"]["path"] = "/ambient/package"
    else:
        record["environment"]["PLTCOMPILEDROOTS"] = "/ambient/compiled"
    evidence["retain"](evidence["runtime"], record)
    with pytest.raises(ValueError):
        runtime.seal_runtime(
            evidence["runtime"], evidence["abi"], evidence["seal"], captured_gate_path=evidence["captured"]
        )
    assert not evidence["seal"].exists()


def test_unexpected_executable_shadow_is_rejected(sealed: dict[str, Any]) -> None:
    # Solver bin precedes Racket bin; a newly added racket must not shadow it.
    shadow = sealed["root"] / "bin/racket"
    shutil.copyfile(sealed["request"]["racket"], shadow)
    shadow.chmod(0o755)
    with pytest.raises(ValueError, match="bypasses"):
        runtime.verify_runtime(sealed["request"])


@pytest.mark.parametrize(
    "change",
    [
        "missing-step",
        "duplicate-step",
        "failed-import",
        "bad-solver-code",
        "wrong-script",
        "wrong-native-env",
        "changed-imports",
        "changed-solver",
    ],
)
def test_prerequisite_process_records_and_literal_smokes_are_required(evidence: dict[str, Any], change: str) -> None:
    record = json.loads(evidence["runtime"].read_text())
    imports = next(step for step in record["steps"] if step["name"] == "imports")
    if change == "missing-step":
        record["steps"].remove(imports)
    elif change == "duplicate-step":
        record["steps"].append(imports)
    elif change == "failed-import":
        imports["status"] = "failure"
    elif change == "bad-solver-code":
        next(step for step in record["steps"] if step["name"] == "tiny-solver-pgid")["returncode"] = -9
    elif change == "wrong-script":
        imports["command"][-1] = "/different/smoke.rkt"
    elif change == "wrong-native-env":
        imports["command"].insert(2, "PLTCOMPILEDROOTS=/ambient")
    else:
        name = "imports.rkt" if change == "changed-imports" else "solver.rkt"
        (evidence["root"] / "smokes" / name).write_text("changed diagnostic with success metadata")
    evidence["retain"](evidence["runtime"], record)
    with pytest.raises(ValueError):
        runtime.seal_runtime(
            evidence["runtime"], evidence["abi"], evidence["seal"], captured_gate_path=evidence["captured"]
        )
    assert not evidence["seal"].exists()


def test_archived_preparer_preserves_historical_identity_after_lock_only_change(evidence: dict[str, Any]) -> None:
    archive = evidence["root"].parent / "historical-preparer.py"
    archived = runtime.PREPARER.read_bytes()
    archive.write_bytes(archived)
    runtime.PREPARER.write_text("new lock ownership implementation; historical diagnostics unchanged")
    before = evidence["runtime"].read_bytes()
    seal = runtime.seal_runtime(
        evidence["runtime"],
        evidence["abi"],
        evidence["seal"],
        captured_gate_path=evidence["captured"],
        preparer_path=archive,
    )
    assert seal["preparer"]["path"] == str(archive)
    assert archive.read_bytes() == archived and evidence["runtime"].read_bytes() == before
    request = evidence["request"]
    request["racket_runtime"] = {
        "path": str(evidence["seal"]),
        "sha256": hashlib.sha256(evidence["seal"].read_bytes()).hexdigest(),
    }
    assert runtime.verify_runtime(request) == seal
    with pytest.raises(ValueError, match="identity changed"):
        runtime.seal_runtime(
            evidence["runtime"],
            evidence["abi"],
            evidence["seal"].with_name("default.json"),
            captured_gate_path=evidence["captured"],
        )
