#!/usr/bin/env python3
"""Freeze the corrected QR7 compiler delta and bind it to the evaluated binary."""

from __future__ import annotations

import difflib
import hashlib
import io
import json
from pathlib import Path
import tarfile


ROOT = Path(__file__).resolve().parent
HOST = Path("/private/tmp/eggcc-qr7-candidate")
ENGINE = Path("/private/tmp/encoding-qr7-candidate")
BASE_HOST = ROOT.parent / "parts32-integration/eggcc-parts32-candidate.tar"
BASE_ENGINE = ROOT.parent / "parts32-integration/encoding-parts32-candidate.tar"
ARCHIVE = ROOT / "corrected-source-r1.tar"
PATCH = ROOT / "eggcc-candidate-r1.patch"
IDENTITIES = ROOT / "source-identities-r1.json"

HOST_FILES = [
    "Cargo.toml",
    "Cargo.lock",
    "dag_in_context/Cargo.toml",
    "dag_in_context/Cargo.lock",
    "dag_in_context/src/lib.rs",
    "dag_in_context/src/optimizations/mem_simple.egg",
    "dag_in_context/src/scoped_qr7.rs",
]

ENGINE_FILES = [
    "Cargo.toml",
    "Cargo.lock",
    "egglog-experimental/Cargo.toml",
    "egglog-experimental/src/lib.rs",
    "egglog-experimental/src/injectivity.rs",
    "egglog-experimental/src/disequality.rs",
]

HARNESS_FILES = [
    "admit.py",
    "write-candidate.py",
    "run.py",
    "matrix.py",
    "inspect.py",
    "scoped_qr7.rs",
    "integration-plan.md",
    "source-admission.json",
    "binary-identities-r1.json",
    "fixtures/source.bril",
    "fixtures/omit-quotient-v2.bril",
    "fixtures/omit-remainder-v2.bril",
    "fixtures/different-divisor.bril",
    "final-r1/positive-results.json",
    "final-r1/negative-results.json",
    "final-r1/loop-negative-results.json",
    "final-r1/context-negative-results.json",
    "final-r1/inspection.json",
]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def row(path: Path, *, relative: str | None = None) -> dict[str, object]:
    return {
        "path": str(path),
        **({"relative": relative} if relative is not None else {}),
        "size": path.stat().st_size,
        "sha256": sha256(path),
    }


def add_bytes(archive: tarfile.TarFile, name: str, data: bytes) -> None:
    info = tarfile.TarInfo(name)
    info.size = len(data)
    info.mtime = 0
    info.uid = 0
    info.gid = 0
    info.uname = "root"
    info.gname = "root"
    info.mode = 0o644
    archive.addfile(info, io.BytesIO(data))


def main() -> None:
    for path in (ARCHIVE, PATCH, IDENTITIES):
        if path.exists():
            raise RuntimeError(f"refusing to overwrite {path}")

    template = ROOT / "scoped_qr7.rs"
    installed = HOST / "dag_in_context/src/scoped_qr7.rs"
    assert installed.read_bytes() == template.read_bytes()

    frozen = ROOT / "bin-r1/eggcc"
    built = ENGINE / "target/release/eggcc"
    assert sha256(frozen) == sha256(built)

    patch_lines: list[str] = []
    with tarfile.open(BASE_HOST) as base:
        for relative in HOST_FILES:
            current = (HOST / relative).read_text()
            try:
                original_file = base.extractfile(relative)
            except KeyError:
                original = ""
            else:
                assert original_file is not None
                original = original_file.read().decode()
            patch_lines.extend(
                difflib.unified_diff(
                    original.splitlines(True),
                    current.splitlines(True),
                    fromfile="a/" + relative,
                    tofile="b/" + relative,
                )
            )
    PATCH.write_text("".join(patch_lines))

    archive_entries: list[dict[str, object]] = []
    sources: list[tuple[str, Path]] = []
    sources.extend(("eggcc/" + relative, HOST / relative) for relative in HOST_FILES)
    sources.extend(("encoding/" + relative, ENGINE / relative) for relative in ENGINE_FILES)
    sources.extend(("evidence/" + relative, ROOT / relative) for relative in HARNESS_FILES)
    for name, path in sorted(sources):
        if not path.is_file():
            raise RuntimeError(f"missing source input {path}")
        archive_entries.append(
            {"member": name, "size": path.stat().st_size, "sha256": sha256(path)}
        )
    manifest_bytes = (json.dumps(archive_entries, indent=2, sort_keys=True) + "\n").encode()
    with tarfile.open(ARCHIVE, "x") as archive:
        for name, path in sorted(sources):
            add_bytes(archive, name, path.read_bytes())
        add_bytes(archive, "MANIFEST.json", manifest_bytes)

    result = {
        "schema_version": 1,
        "status": "corrected-source-frozen-and-release-target-revalidated",
        "base_archives": [row(BASE_HOST), row(BASE_ENGINE)],
        "compiler_delta_patch": row(PATCH),
        "compiler_source_archive": row(ARCHIVE),
        "archive_entries": archive_entries,
        "host_files": [row(HOST / relative, relative=relative) for relative in HOST_FILES],
        "engine_files": [row(ENGINE / relative, relative=relative) for relative in ENGINE_FILES],
        "harness_files": [row(ROOT / relative, relative=relative) for relative in HARNESS_FILES],
        "frozen_compiler_binary": row(frozen),
        "revalidated_release_target": row(built),
        "binary_identity_equal": sha256(frozen) == sha256(built),
        "release_recheck_receipt": row(
            ROOT
            / "source-revalidation-r1/commands/corrected-source-release-recheck/receipt.json"
        ),
        "timing_samples_taken": False,
    }
    IDENTITIES.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"archive_sha256": sha256(ARCHIVE), "patch_sha256": sha256(PATCH), "binary_sha256": sha256(frozen)}, indent=2))


if __name__ == "__main__":
    main()
