"""Rebuild and run source-backed MISAAL ABI diagnostics, never source workloads."""

from __future__ import annotations

import argparse
import ast
import hashlib
import json
import os
from contextlib import nullcontext
from dataclasses import asdict
from pathlib import Path
from types import CodeType, FunctionType, ModuleType, SimpleNamespace
from typing import Any

from benchmarking.pilot import run_bounded_command
from scripts import reproduction_misaal_patterns as adaptation
from scripts import reproduction_misaal_runtime as runtime_contract
from scripts.reproduction_misaal_groups import SOURCE, SOURCE_SHA256
from scripts.reproduction_process import DISK_RESERVE_BYTES, exclusive_job

ROOT = Path(__file__).resolve().parents[1]
FIXTURES = ROOT / "benchmarks/reproduction/fixtures/misaal-parameter"
CAPTURED_FIXTURE = FIXTURES / "ki4k2nlc.rkt"
CAPTURED_SHA256 = "32d0edbfbd86bdde0ba6b47af8eebd260f1421af79dcbb223923015f389a8521"
FIXTURE_SHA256 = {
    "ki4k2nlc.rkt": CAPTURED_SHA256,
    "c098-ordinary-depth2.rkt": "c6149ee7123608f10facf84e0eccd1f652436f2f5066bd99a661bf4f70309650",
    "c098-general-depth1.rkt": "a1b97d6a5bd1c149bcc0116c14eefb1ec5f121a1c93b8a373951060e37ffd51a",
}


def _pin(path: Path, expected: str | None = None) -> dict[str, str]:
    """Require a retained absolute regular file with its exact declared bytes."""
    if not path.is_absolute() or path.is_symlink() or not path.is_file():
        raise ValueError(f"ABI gate input must be an absolute regular file: {path}")
    digest = hashlib.sha256(path.read_bytes()).hexdigest()
    if expected is not None and digest != expected:
        raise ValueError(f"ABI gate input changed: {path}")
    return {"path": str(path), "sha256": digest}


def _abstractor(source_path: Path, helper_source: str) -> ModuleType:
    """Instantiate original full-module code objects without running any imports."""
    source = source_path.read_text()
    syntax = ast.parse(source)
    cls = next(n for n in syntax.body if isinstance(n, ast.ClassDef) and n.name == "PatternAbstractor")
    compiled = compile(source, str(source_path), "exec", dont_inherit=True)
    class_code = next(n for n in compiled.co_consts if isinstance(n, CodeType) and n.co_name == "PatternAbstractor")
    codes = {n.co_name: n for n in class_code.co_consts if isinstance(n, CodeType)}
    module = ModuleType("patterns.PatternUtils")
    module.__file__ = str(source_path)
    methods: dict[str, Any] = {"__module__": module.__name__}
    for method in cls.body:
        if isinstance(method, ast.FunctionDef):
            defaults = tuple(ast.literal_eval(n) for n in method.args.defaults) or None
            methods[method.name] = FunctionType(codes[method.name], vars(module), method.name, defaults)
    module.__dict__["PatternAbstractor"] = type("PatternAbstractor", (), methods)
    helper_code = compile(helper_source, str(source_path.parents[2] / SOURCE), "exec", dont_inherit=True)
    cond = next(n for n in helper_code.co_consts if isinstance(n, CodeType) and n.co_name == "emit_racket_cond")
    module.__dict__["emit_racket_cond"] = FunctionType(cond, vars(module), "emit_racket_cond")
    return module


def _emit(module: ModuleType, name: str, header: str) -> bytes:
    """Use both actual generation paths; intercept only their native launch."""
    captures: list[bytes] = []

    def capture(statements: list[str]) -> SimpleNamespace:
        captures.append((header + "\n" + "\n".join(statements) + "\n").encode())
        return SimpleNamespace(returncode=1)  # Do not open an absent native result file.

    module.__dict__.update(
        tempfile=SimpleNamespace(_get_candidate_names=lambda: iter([name])), execute_racket_file=capture
    )
    instance = module.PatternAbstractor.__new__(module.PatternAbstractor)
    instance.examples_limit = None
    if name == "general-depth1":
        result = instance.generate_param_expr_general(
            {0: [2, 4, 6], 1: [1, 2, 3], 2: [5, 7, 11]}, 0, depth=1, exclude_regs=[1]
        )
    else:
        result = instance.generate_param_expr(
            {0: [1, 2, 3]}, {0: [2, 4, 6], 1: [5, 7, 11]}, 0, depth=2, only_src_params=False, exclude_regs=[1]
        )
    if result != (False, None) or len(captures) != 1:
        raise ValueError("ABI generator bypassed the actual emitted-script boundary")
    return captures[0]


def prepare_programs(checkout: Path, output: Path) -> dict[str, Any]:
    """Offline-only generation of the four programs and immutable source manifest."""
    checkout, output = checkout.resolve(), output.resolve()
    if output.exists():
        raise ValueError("ABI program output must be fresh")
    pins = {}
    for relative, expected in {**adaptation.PARAMETER_ABI_SOURCE_SHA256, SOURCE: SOURCE_SHA256}.items():
        reference = _pin(checkout / relative, expected)
        pins[reference["path"]] = reference["sha256"]
    for name, expected in FIXTURE_SHA256.items():
        reference = _pin(FIXTURES / name, expected)
        pins[reference["path"]] = reference["sha256"]
    for path in (FIXTURES / "provenance.json", Path(__file__).resolve(), Path(adaptation.__file__).resolve()):
        reference = _pin(path)
        pins[reference["path"]] = reference["sha256"]
    provenance = json.loads((FIXTURES / "provenance.json").read_text())
    if provenance["files"] != FIXTURE_SHA256 or provenance["admitted"] is not False:
        raise ValueError("ABI fixture provenance does not describe the pinned diagnostic bytes")
    source_path = checkout / "lib/patterns/PatternUtils.py"
    helper_source = (checkout / SOURCE).read_text()
    header = next(
        ast.literal_eval(node.value)
        for node in ast.parse(helper_source).body
        if isinstance(node, ast.Assign)
        and any(isinstance(target, ast.Name) and target.id == "HYDRIDE_HEADER" for target in node.targets)
    )
    module = _abstractor(source_path, helper_source)
    originals = dict(vars(module.PatternAbstractor))
    names = ("ordinary-depth2", "general-depth1")
    original = {name: _emit(module, name, header) for name in names}
    request = {
        "checkout": str(checkout),
        "revision": runtime_contract.REVISION,
        "parameter_abi": adaptation.PARAMETER_ABI_CONTRACT,
        "source_hashes": dict(adaptation.PARAMETER_ABI_SOURCE_SHA256),
    }
    receipt: dict[str, Any] = {}
    programs: dict[str, dict[str, Any]] = {}
    with adaptation.restore_parameter_abi(module, request, receipt, lambda: None):
        for name in names:
            adapted = _emit(module, name, header)
            if adapted != (FIXTURES / f"c098-{name}.rkt").read_bytes() or adapted == original[name]:
                raise ValueError(f"Actual emitted program differs from its c098 oracle: {name}")
            programs[name] = {"bytes": adapted, "expected_exit": 0, "result_file": f"{name}.temp"}
            programs[f"{name}-unadapted"] = {"bytes": original[name], "expected_exit": 1}
        if any(
            vars(module.PatternAbstractor)[name] is not value
            for name, value in originals.items()
            if name not in {"emit_synthesize_query", "generate_param_expr_general"}
        ):
            raise ValueError("ABI restoration changed an unrelated source method")
    if vars(module.PatternAbstractor) != originals:
        raise ValueError("ABI restoration left source methods changed")
    for filename, digest in pins.items():
        _pin(Path(filename), digest)
    output.mkdir(parents=True)
    for name, program in programs.items():
        path = output / f"{name}.rkt"
        path.write_bytes(program.pop("bytes"))
        program.update(_pin(path))
    manifest = {
        "status": "prepared-offline-only",
        "admitted": False,
        "proof_admitted": False,
        "source_pins": pins,
        "adaptation_receipt": receipt,
        "programs": programs,
        "request": request,
        "scope": "source-emitted ABI diagnostics compared with c098 oracle bytes; not workload admission",
    }
    (output / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    return manifest


def _runtime(runtime_path: Path, checkout: Path, preparer_path: Path | None = None) -> dict[str, Any]:
    """Reject incomplete or changed prerequisite bytes before any native gate."""
    _pin(runtime_path)
    runtime: dict[str, Any] = json.loads(runtime_path.read_text())
    root = runtime_path.parent
    if (
        runtime["status"] != "source-api-blocked"
        or runtime["promoted"] is not False
        or runtime["workflow_ready"] is not False
        or any(runtime["gates"][name]["status"] != "success" for name in ("imports", "tiny_solver", "source_four_args"))
        or runtime["gates"]["captured_five_args"]
        != {
            "status": "expected-api-failure",
            "sha256": FIXTURE_SHA256["ki4k2nlc.rkt"],
            "modified": False,
        }
        or runtime["pgid_observation"]["status"] != "observed-same-group"
        or runtime["pgid_observation"]["cleanup"]["status"] != "drained"
    ):
        raise ValueError("ABI gates require completed isolated runtime prerequisites")
    _pin(
        preparer_path or Path(__file__).with_name("reproduction_prepare_misaal_racket.py"),
        runtime["implementation_sha256"],
    )
    executables = {
        "racket": runtime_contract.RACKET_INSTALLATION / "bin/racket",
        "raco": runtime_contract.RACKET_INSTALLATION / "bin/raco",
        "z3": root / "bin/z3",
    }
    if (
        runtime["racket"]["path"] != str(executables["racket"])
        or runtime["solver"]["path"] != str(executables["z3"])
        or runtime["racket"]["sha256"] != runtime_contract.EXECUTABLE_SHA256["racket"]
        or runtime["racket"]["raco_sha256"] != runtime_contract.EXECUTABLE_SHA256["raco"]
        or runtime["solver"]["sha256"] != runtime_contract.EXECUTABLE_SHA256["z3"]
    ):
        raise ValueError("ABI runtime executable identity changed")
    for name, path in executables.items():
        _pin(path, runtime_contract.EXECUTABLE_SHA256[name])
        if not os.access(path, os.X_OK):
            raise ValueError("ABI runtime executable is not executable")
    expected_environment = {
        "PLTUSERHOME": str(root / "user"),
        "PLTADDONDIR": str(root / "addon"),
        "TMPDIR": str(root / "tmp"),
        "HYDRIDE_ROOT": str(checkout / "Hydride"),
        "MISAAL_Z3_PATH": str(executables["z3"]),
        "PATH": f"{root / 'bin'}:{runtime_contract.RACKET_INSTALLATION / 'bin'}:/usr/bin:/bin:/usr/sbin:/sbin",
    }
    if runtime["environment"] != expected_environment:
        raise ValueError("ABI runtime environment differs from the completed isolated preparation")
    packages = runtime["installed_packages"]
    if set(packages) != set(runtime_contract.PACKAGE_TREES):
        raise ValueError("ABI runtime package closure changed")
    for name, package in packages.items():
        directory = Path(package["path"])
        if (
            not directory.resolve().is_relative_to(root / "addon")
            or package["tree"] != runtime_contract.PACKAGE_TREES[name]
            or not package["files"]
        ):
            raise ValueError("ABI runtime package path or tree changed")
        for relative, expected in package["files"].items():
            path = directory / relative
            if not path.resolve().is_relative_to(directory.resolve()):
                raise ValueError("ABI runtime package source escapes its directory")
            _pin(path, expected)
    _pin(
        Path(packages["misaal"]["path"]) / "synthesis/param_abstract.rkt",
        adaptation.PARAMETER_ABI_SOURCE_SHA256["misaal/synthesis/param_abstract.rkt"],
    )
    modules = runtime["gates"]["imports"]["module_paths"]
    if set(modules) != {"rosette", "hydride", "misaal"} or any(
        not Path(path).resolve().is_relative_to(Path(packages[name]["path"]).resolve())
        for name, path in modules.items()
    ):
        raise ValueError("ABI runtime imports escaped the pinned packages")
    return runtime


def run_gates(
    runtime_path: Path,
    checkout: Path,
    output: Path,
    *,
    lock_owned: bool = False,
    preparer_path: Path | None = None,
) -> dict[str, Any]:
    """Run five fresh sequential diagnostics; the coordinator may already own the lock."""
    runtime_path, checkout, output = runtime_path.resolve(), checkout.resolve(), output.resolve()
    durable = ROOT / "benchmarks/local/reproduction"
    if output.exists() or not output.is_relative_to(durable):
        raise ValueError("ABI gate output must be fresh and beneath benchmarks/local/reproduction")
    lock = nullcontext() if lock_owned else exclusive_job(durable / "stages/.heavy-job.lock")
    with lock:
        output.mkdir(parents=True)
        summary: dict[str, Any] = {"status": "running", "admitted": False, "proof_admitted": False}
        try:
            runtime = _runtime(runtime_path, checkout, preparer_path)
            summary["preparer_evidence"] = _pin(
                preparer_path or Path(__file__).with_name("reproduction_prepare_misaal_racket.py"),
                runtime["implementation_sha256"],
            )
            runtime_ref = _pin(runtime_path)
            manifest = prepare_programs(checkout, output / "programs")
            manifest_ref = _pin(output / "programs/manifest.json")
            implementation = _pin(Path(adaptation.__file__).resolve())
            prefix = [
                "/usr/bin/env",
                "-i",
                *[f"{k}={v}" for k, v in runtime["environment"].items()],
                runtime["racket"]["path"],
            ]
            abi: dict[str, Any] = {
                "status": "running",
                "admitted": False,
                "runtime": runtime_ref,
                "manifest": manifest_ref,
                "implementation": implementation,
                "runs": [],
            }
            abi_dir = output / "abi"
            abi_dir.mkdir()
            try:
                for name, program in manifest["programs"].items():
                    attempt = abi_dir / name
                    attempt.mkdir()
                    source = Path(program["path"])
                    _pin(source, program["sha256"])
                    command = [*prefix, str(source)]
                    row: dict[str, Any] = {
                        "name": name,
                        "command": command,
                        "program_sha256": program["sha256"],
                        "passed": False,
                    }
                    abi["runs"].append(row)
                    summary["active_gate"] = name
                    summary.pop("process", None)
                    process = run_bounded_command(
                        command,
                        attempt,
                        attempt / "process",
                        timeout_sec=60,
                        memory_limit_bytes=5 * 1024**3,
                        require_guard=True,
                        allow_warning_pressure=True,
                        disk_reserve_bytes=DISK_RESERVE_BYTES,
                    )
                    row["process"] = asdict(process)
                    summary["process"] = row["process"]
                    expected = program["expected_exit"]
                    if process.status != ("success" if expected == 0 else "failure") or process.returncode != expected:
                        raise ValueError(f"ABI gate did not complete with the expected outcome: {name}")
                    if expected == 0:
                        path = attempt / program["result_file"]
                        row["result"] = {**_pin(path), "text": path.read_text()}
                        if not row["result"]["text"]:
                            raise ValueError("ABI gate produced an empty solver result")
                    elif not all(
                        text in process.stderr_path.read_text()
                        for text in (
                            "synthesize-param-expression",
                            "arity mismatch",
                            "expected: 4",
                            "given: 5",
                        )
                    ):
                        raise ValueError("ABI control failed for a different reason")
                    row["passed"] = True
                abi["status"] = "success"
            except BaseException as error:
                abi.update(status="failure", reason=f"{type(error).__name__}: {error}")
                raise
            finally:
                abi["artifacts"] = {str(path): _pin(path)["sha256"] for path in abi_dir.rglob("*") if path.is_file()}
                (abi_dir / "result.json").write_text(json.dumps(abi, indent=2, default=str) + "\n")
                summary["abi_gate"] = _pin(abi_dir / "result.json")
            captured_dir = output / "captured"
            captured_dir.mkdir()
            original = CAPTURED_FIXTURE
            captured_bytes = original.read_bytes()
            before, after = runtime_contract.CAPTURED_BEFORE, runtime_contract.CAPTURED_AFTER
            if _pin(original)["sha256"] != FIXTURE_SHA256["ki4k2nlc.rkt"] or captured_bytes.count(before.encode()) != 1:
                raise ValueError("Captured diagnostic source identity changed")
            adapted = captured_dir / "adapted.rkt"
            adapted.write_bytes(captured_bytes.replace(before.encode(), after.encode(), 1))
            captured: dict[str, Any] = {
                "status": "running",
                "admitted": False,
                "runtime": runtime_ref,
                "original": _pin(original),
                "adapted": _pin(adapted),
                "replacement": {"before": before, "after": after, "count": 1},
                "contract": adaptation.PARAMETER_ABI_CONTRACT,
                "command": [*prefix, str(adapted)],
            }
            try:
                summary["active_gate"] = "captured"
                summary.pop("process", None)
                process = run_bounded_command(
                    captured["command"],
                    captured_dir,
                    captured_dir / "process",
                    timeout_sec=60,
                    memory_limit_bytes=5 * 1024**3,
                    require_guard=True,
                    allow_warning_pressure=True,
                    disk_reserve_bytes=DISK_RESERVE_BYTES,
                )
                captured["process"] = asdict(process)
                summary["process"] = captured["process"]
                if process.status != "success" or process.returncode != 0:
                    raise ValueError("Captured diagnostic gate did not complete successfully")
                value = captured_dir / "6lt2r1zf.temp"
                captured["output"] = {**_pin(value), "text": value.read_text()}
                if not captured["output"]["text"]:
                    raise ValueError("Captured diagnostic gate produced an empty solver result")
                captured["status"] = "success"
            except BaseException as error:
                captured.update(status="failure", reason=f"{type(error).__name__}: {error}")
                raise
            finally:
                captured["artifacts"] = {
                    str(path): _pin(path)["sha256"] for path in captured_dir.iterdir() if path.is_file()
                }
                (captured_dir / "result.json").write_text(json.dumps(captured, indent=2, default=str) + "\n")
                summary["captured_gate"] = _pin(captured_dir / "result.json")
            _pin(runtime_path, runtime_ref["sha256"])
            _runtime(runtime_path, checkout, preparer_path)
            for path, digest in manifest["source_pins"].items():
                _pin(Path(path), digest)
            summary["status"] = "success"
        except BaseException as error:
            summary.update(status="failure", reason=f"{type(error).__name__}: {error}")
            raise
        finally:
            (output / "result.json").write_text(json.dumps(summary, indent=2, default=str) + "\n")
        return summary


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--runtime", required=True, type=Path)
    parser.add_argument("--checkout", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument(
        "--preparer-source", type=Path, help="Exact historical preparer source; evidence only, never executed"
    )
    args = parser.parse_args()
    result = run_gates(args.runtime, args.checkout, args.output, preparer_path=args.preparer_source)
    print(json.dumps(result, indent=2, default=str))


if __name__ == "__main__":
    main()
