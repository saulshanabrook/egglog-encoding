"""Rebuild and run source-backed MISAAL ABI diagnostics, never source workloads."""

from __future__ import annotations

import ast
import hashlib
import json
from pathlib import Path
from types import ModuleType, SimpleNamespace
from typing import Any

from scripts.reproduction_misaal_export import EXPORT_SOURCE_SHA256
from scripts.reproduction_misaal_groups import SOURCE

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
    """Compile the repaired source class and its helper without population imports."""
    source = source_path.read_text()
    syntax = ast.parse(source)
    cls = next(n for n in syntax.body if isinstance(n, ast.ClassDef) and n.name == "PatternAbstractor")
    module = ModuleType("patterns.PatternUtils")
    module.__file__ = str(source_path)
    helper = next(
        n for n in ast.parse(helper_source).body if isinstance(n, ast.FunctionDef) and n.name == "emit_racket_cond"
    )
    exec(compile(ast.Module(body=[cls, helper], type_ignores=[]), str(source_path), "exec"), vars(module))
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
    """Check the repaired emitter against its two source-backed positive oracles."""
    checkout, output = checkout.resolve(), output.resolve()
    if output.exists():
        raise ValueError("ABI program output must be fresh")
    pins = {}
    for relative in ("lib/patterns/PatternUtils.py", SOURCE):
        reference = _pin(checkout / relative, EXPORT_SOURCE_SHA256[relative])
        pins[reference["path"]] = reference["sha256"]
    helper_source = (checkout / SOURCE).read_text()
    header = next(
        ast.literal_eval(node.value)
        for node in ast.parse(helper_source).body
        if isinstance(node, ast.Assign)
        and any(isinstance(target, ast.Name) and target.id == "HYDRIDE_HEADER" for target in node.targets)
    )
    module = _abstractor(checkout / "lib/patterns/PatternUtils.py", helper_source)
    output.mkdir(parents=True)
    programs = {}
    for name in ("ordinary-depth2", "general-depth1"):
        content = _emit(module, name, header)
        fixture = FIXTURES / f"c098-{name}.rkt"
        _pin(fixture, FIXTURE_SHA256[fixture.name])
        if content != fixture.read_bytes():
            raise ValueError(f"Repaired emitter differs from its paper ABI oracle: {name}")
        path = output / f"{name}.rkt"
        path.write_bytes(content)
        programs[name] = {**_pin(path), "expected_exit": 0, "result_file": f"{name}.temp"}
    manifest = {"admitted": False, "source_pins": pins, "programs": programs}
    (output / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    return manifest
