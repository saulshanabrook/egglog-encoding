"""Portable corpus identities and names shared by explicit source commands."""

from __future__ import annotations

import hashlib
import json
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Literal, NotRequired, TypedDict

MANIFEST_RELATIVE_PATH = Path("benchmarks/corpus/manifest.json")
VALIDATION_POLICY = "proof-testing-v1"
SAFETY_POLICY = "native-memory-limit-v1"


class CorpusOutcome(TypedDict):
    file_sha256: str
    fact_directory_sha256: str
    binary_sha256: str
    timeout_sec: int
    disequality_encoding: Literal["nee", "ee"]
    kind: Literal["validation", "safety"]
    policy: str
    status: Literal["success", "failure", "deferred"]
    reason: str | None
    evidence: NotRequired[str]


@dataclass(frozen=True)
class CorpusManifest:
    path: Path
    sources: dict[str, dict[str, Any]]
    cases: tuple[dict[str, Any], ...]
    workloads: tuple[dict[str, Any], ...]
    outcomes: tuple[CorpusOutcome, ...]


def sha256_file(path: Path) -> str:
    """Identify corpus bytes without depending on the measurement runner."""
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return "sha256:" + digest.hexdigest()


def load_manifest(root: Path) -> CorpusManifest:
    """Read the public corpus and optional local diagnostics without running work."""
    path = root / MANIFEST_RELATIVE_PATH
    raw = json.loads(path.read_text())
    outcomes = path.parent / ".local/outcomes.json"
    return CorpusManifest(
        path,
        raw["sources"],
        tuple(raw["cases"]),
        tuple(raw["workloads"]),
        tuple(json.loads(outcomes.read_text())) if outcomes.is_file() else (),
    )


def workload_name(case: dict[str, Any], order: int, digest: str, existing: set[str]) -> str:
    """Choose a readable initial name while retaining existing identity aliases."""
    family = case["family"]
    if family == "math-growth":
        name = "math/math-iteration-11.egg"
    else:
        stem = case["id"].removeprefix(family + "-")
        stem = re.sub(r"[^A-Za-z0-9._-]+", "-", stem).strip("-.").lower()
        stem = re.sub(r"-{2,}", "-", stem)
        name = f"{family}/{stem}-call-{order + 1:02}.egg"
    if name not in existing:
        return name
    stem = name.removesuffix(".egg")
    for size in range(8, 65, 8):
        candidate = stem + "-" + digest.removeprefix("sha256:")[:size] + ".egg"
        if candidate not in existing:
            return candidate
    raise ValueError("cannot assign a unique prepared workload name")
