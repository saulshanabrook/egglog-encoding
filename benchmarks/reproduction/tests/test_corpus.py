"""The published population preserves exact inputs and portable source provenance."""

from __future__ import annotations

import ast
import hashlib
import json
import re
from collections import Counter
from pathlib import Path

from benchmarks.reproduction.corpus import load_manifest, sha256_file, workload_name

ROOT = Path(__file__).resolve().parents[3]


def test_complete_population_has_readable_paths_and_unchanged_bytes() -> None:
    manifest = load_manifest(ROOT)
    cases = {case["id"]: case for case in manifest.cases}
    files = set()
    identities = set()
    families: Counter[str] = Counter()
    for workload in manifest.workloads:
        name = workload["file"]
        path = manifest.path.parent / name
        assert path.resolve().is_relative_to(manifest.path.parent.resolve())
        assert not re.fullmatch(r"[a-f0-9]{64}", path.stem)
        assert sha256_file(path) == workload["sha256"]
        identity = (workload["sha256"], workload.get("facts_sha256", ""))
        assert identity not in identities
        identities.add(identity)
        files.add(path)
        families[cases[workload["aliases"][0]["case"]]["family"]] += 1
        for alias in workload["aliases"]:
            assert name in cases[alias["case"]]["workloads"]
            assert alias["order"] >= 0
    assert len(identities) == 487
    assert files == set(manifest.path.parent.rglob("*.egg"))
    assert families == {
        "math-growth": 1,
        "luminal": 7,
        "eggcc": 217,
        "hardboiled": 42,
        "misaal": 173,
        "churchroad": 21,
        "dialegg": 26,
    }


def test_renaming_preserves_the_entire_canonical_manifest_by_identity() -> None:
    manifest = load_manifest(ROOT)
    raw = json.loads(manifest.path.read_text())
    names = {row["file"]: row["sha256"] + "/" + row.get("facts_sha256", "") for row in raw["workloads"]}
    for row in raw["workloads"]:
        row["file"] = names[row["file"]]
    for case in raw["cases"]:
        case["workloads"] = [names[name] for name in case["workloads"]]
    encoded = json.dumps(raw, sort_keys=True, separators=(",", ":")).encode()
    # Original recovery manifest, with only physical paths replaced by identities.
    assert hashlib.sha256(encoded).hexdigest() == "f0b181e60f42f391f4903363290bd8a5fff93b75e18563b06b8c88537a2bbf80"


def test_readable_name_collisions_extend_the_digest_without_replacing_an_input() -> None:
    case = {"id": "eggcc-example--statewalk", "family": "eggcc"}
    digest = "sha256:" + "a" * 64
    first = workload_name(case, 0, digest, set())
    second = workload_name(case, 0, digest, {first})
    third = workload_name(case, 0, digest, {first, second})
    assert first == "eggcc/example-statewalk-call-01.egg"
    assert second.endswith("-aaaaaaaa.egg")
    assert third.endswith("-aaaaaaaaaaaaaaaa.egg")


def test_regeneration_does_not_import_measurement_or_old_script_packages() -> None:
    for path in (ROOT / "benchmarks/reproduction").glob("*.py"):
        for node in ast.walk(ast.parse(path.read_text())):
            if isinstance(node, ast.Import):
                imports = [alias.name for alias in node.names]
            elif isinstance(node, ast.ImportFrom) and node.level == 0:
                imports = [node.module or ""]
            else:
                continue
            assert not any(name.split(".")[0] in {"benchmarking", "scripts", "process_guard"} for name in imports), path
