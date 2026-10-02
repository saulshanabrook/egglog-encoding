"""Rebuild and run source-backed MISAAL ABI diagnostics, never source workloads."""

from __future__ import annotations

import ast
import hashlib
import json
from pathlib import Path
from types import CodeType, FunctionType, ModuleType, SimpleNamespace
from typing import Any

from scripts import reproduction_misaal_patterns as adaptation
from scripts import reproduction_misaal_runtime as runtime_contract
from scripts.reproduction_misaal_groups import SOURCE, SOURCE_SHA256

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
