"""Create tiny local artifact archives and provenance objects for paper harness tests."""

from __future__ import annotations

import io
import tarfile
from collections.abc import Sequence
from pathlib import Path

from paper_benchmarking.artifact import REQUIRED_ARCHIVE_MEMBERS, ArtifactCache, setup_artifact
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
    """Create a tiny, fully verified artifact cache for runner tests."""

    root.parent.mkdir(parents=True, exist_ok=True)
    archive = root.with_suffix(".tar.gz")
    digest = write_artifact_archive(archive)
    return setup_artifact(root, archive_path=archive, expected_sha256=digest)
