"""Recognize the fixed Math11 input used by the native runner."""

from __future__ import annotations

import hashlib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MATH_WORKLOAD_PATH = Path("egglog-experimental/tests/math-microbenchmark-rational.egg")
# Pin the unchanged language/rules/seeds, rather than accepting whatever happens
# to occupy the legacy filename when a native binary ignores its contents.
LEGACY_SHA256 = "29e120079c588d0bf079891b393ae041ec4e1a45d369114cde3754e5c6b7878f"


def recognize_math_workload(path: Path) -> None:
    """Accept only the complete unchanged Math11 input used by the native runner."""

    try:
        digest = hashlib.sha256(path.read_bytes()).hexdigest()
    except OSError as error:
        raise ValueError(f"cannot read canonical Math workload: {path}") from error
    if digest != LEGACY_SHA256:
        raise ValueError(f"native egg supports only the fixed Math11 workload ({MATH_WORKLOAD_PATH}): {path}")
