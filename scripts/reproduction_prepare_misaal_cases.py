"""Compile original MISAAL generators and emit complete-capture requests.

Reuse a verified prepared 44ff environment. This runs serial host compiler jobs
only; native optimization remains with the coordinator. The API uses its caller's
job slot, while the CLI acquires the shared lock. Pattern caches remain fresh.
"""

from __future__ import annotations

import shlex
from pathlib import Path

from scripts.source_tools import Preparation, sha256_file

TARGET = "host-x86-64-no_bounds_query-no_asserts"
ARM_TARGET = "arm-64-osx-arm_dot_prod-no_asserts-no_bounds_query"
HVX_TARGET = "hexagon-32-noos-no_bounds_query-no_asserts-hvx_128-hvx_v66"
DEFAULTS = {
    "HL_EXPR_DEPTH": "2",
    "HL_SYNTH_BW": "16",
    "HL_ENABLE_MISAAL": "1",
    "HL_ENABLE_HYDRIDE": "1",
    "HYDRIDE_INITIAL_HASH": "empty_hash",
    "MISAAL_DISABLE_FRONTEND_PATTERNS": "1",
}


def compile_dependencies(path: Path, checkout: Path, required: set[Path]) -> dict[str, str]:
    """Bind the compiler-observed dependency closure, including local included headers."""
    target, separator, content = path.read_text().replace("\\\n", " ").partition(":")
    if not target or not separator:
        raise ValueError("compiler did not emit a valid dependency file")
    paths = {(checkout / name).resolve() for name in shlex.split(content)}
    if not {file.resolve() for file in required}.issubset(paths):
        raise ValueError("compiler dependency file omitted an original generator input")
    return {str(file): sha256_file(file) for file in sorted(paths)}


def compile_object(
    preparation: Preparation,
    source: Path,
    directory: Path,
    flags: list[str],
    checkout: Path,
    header: Path,
    timeout_sec: int,
) -> tuple[Path, dict[str, str]]:
    """Compile one translation unit so its dependency file cannot be overwritten."""
    destination = directory / f"{source.stem}.o"
    dependencies = directory / f"{source.stem}.d"
    preparation.step(
        f"compile-{source.stem}",
        [*flags, "-c", str(source), "-MMD", "-MF", str(dependencies), "-o", str(destination)],
        cwd=checkout,
        timeout=timeout_sec,
    )
    if not destination.is_file() or not destination.stat().st_size:
        raise ValueError("successful compile omitted a native object")
    return destination, compile_dependencies(dependencies, checkout, {source, header})
