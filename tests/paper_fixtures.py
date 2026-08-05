"""Create tiny local artifact archives and provenance objects for paper harness tests."""

from __future__ import annotations

import io
import tarfile
from collections.abc import Sequence
from pathlib import Path

from paper_benchmarking.artifact import REQUIRED_ARCHIVE_MEMBERS, ArtifactCache
from paper_benchmarking.hashing import sha256_file

ROOT = Path(__file__).resolve().parents[1]


def write_artifact_archive(
    path: Path,
    *,
    extra_members: Sequence[tuple[str, bytes]] = (),
) -> str:
    """Write a tiny archive containing every required allowlist marker."""

    members = [(name, f"fixture:{name}\n".encode()) for name in sorted(REQUIRED_ARCHIVE_MEMBERS)]
    members.extend(extra_members)
    with tarfile.open(path, mode="w:gz") as archive:
        for name, contents in members:
            info = tarfile.TarInfo(name)
            info.size = len(contents)
            info.mode = 0o755 if name.endswith((".sh", "run.py")) else 0o644
            info.mtime = 1_678_233_600
            archive.addfile(info, io.BytesIO(contents))
    return sha256_file(path)


def fake_artifact_cache(root: Path) -> ArtifactCache:
    """Return a lightweight already-verified artifact record for runner tests."""

    root.mkdir(parents=True, exist_ok=True)
    artifact_root = root / "artifact"
    artifact_root.mkdir(exist_ok=True)
    archive_path = root / "archive.tar.gz"
    manifest_path = root / "manifest.json"
    archive_path.write_bytes(b"archive")
    manifest_path.write_text("{}\n", encoding="utf-8")
    return ArtifactCache(
        root=root,
        artifact_root=artifact_root,
        archive_path=archive_path,
        manifest_path=manifest_path,
        archive_sha256="a" * 64,
        tree_sha256="b" * 64,
        manifest_sha256="c" * 64,
        file_count=1,
    )
