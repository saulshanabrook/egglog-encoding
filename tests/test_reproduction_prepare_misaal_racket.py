"""No-network/no-native tests of source identity, isolation, and candidate gates."""

from __future__ import annotations

import hashlib
import io
import json
import stat
import zipfile
from pathlib import Path
from typing import Any

import pytest

from scripts import reproduction_prepare_misaal_racket as prep


@pytest.fixture
def tree() -> tuple[dict[str, Any], str, bytes]:
    data = b"#lang info\n"
    blob = hashlib.sha1(f"blob {len(data)}\0".encode() + data).hexdigest()
    body = b"100644 info.rkt\0" + bytes.fromhex(blob)
    digest = hashlib.sha1(f"tree {len(body)}\0".encode() + body).hexdigest()
    return (
        {
            "truncated": False,
            "tree": [{"path": "info.rkt", "mode": "100644", "type": "blob", "size": len(data), "sha": blob}],
        },
        digest,
        data,
    )


def test_git_tree_pin_and_complete_blob_identity(tree: tuple[dict[str, Any], str, bytes]) -> None:
    metadata, digest, _ = tree
    assert prep.verify_tree(metadata, digest) == metadata["tree"]
    with pytest.raises(ValueError, match="pinned Git identity"):
        prep.verify_tree(metadata, "0" * 40)


@pytest.mark.parametrize(
    ("change", "message"),
    [
        ({"path": "../outside"}, "unsafe"),
        ({"path": "dir/info.rkt"}, "omits a parent"),
        ({"mode": "120000"}, "symlink"),
        ({"size": prep.MAX_FILE_BYTES + 1}, "byte bound"),
        ({"sha": "not-a-hash"}, "invalid Git"),
    ],
)
def test_tree_rejects_untrusted_paths_and_members(
    tree: tuple[dict[str, Any], str, bytes], change: dict[str, Any], message: str
) -> None:
    metadata, digest, _ = tree
    metadata["tree"][0].update(change)
    with pytest.raises(ValueError, match=message):
        prep.verify_tree(metadata, digest)


def test_acquisition_rejects_changed_blob_before_install(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, tree: tuple[dict[str, Any], str, bytes]
) -> None:
    metadata, digest, _ = tree
    monkeypatch.setattr(prep, "PACKAGES", {"package": (digest, "https://source/tree", "https://source/raw/")})
    monkeypatch.setattr(
        prep, "fetch_bytes", lambda url, limit: json.dumps(metadata).encode() if url.endswith("tree") else b"bad"
    )
    with pytest.raises(ValueError, match="blob differs"):
        prep.acquire_packages(tmp_path / "sources")
    assert not (tmp_path / "sources/package/info.rkt").exists()
    assert not (tmp_path / "sources/package.json").exists()


@pytest.mark.parametrize("redirect", [False, True])
def test_download_bounds_and_redirect_origin(monkeypatch: pytest.MonkeyPatch, redirect: bool) -> None:
    class Response(io.BytesIO):
        url = "https://other/file" if redirect else "https://source/file"

    monkeypatch.setattr(prep.urllib.request, "urlopen", lambda *a, **kw: Response(b"12345"))
    with pytest.raises(ValueError, match="origin" if redirect else "byte bound"):
        prep.fetch_bytes("https://source/file", 4)


@pytest.mark.parametrize("kind", ["traversal", "symlink", "extra"])
def test_z3_archive_refuses_unexpected_members(tmp_path: Path, monkeypatch: pytest.MonkeyPatch, kind: str) -> None:
    archive = tmp_path / "solver.zip"
    member = zipfile.ZipInfo("../z3" if kind == "traversal" else "z3")
    member.external_attr = ((stat.S_IFLNK if kind == "symlink" else stat.S_IFREG) | 0o755) << 16
    with zipfile.ZipFile(archive, "w") as bundle:
        bundle.writestr(member, b"binary")
        if kind == "extra":
            bundle.writestr("other", b"extra")
    monkeypatch.setattr(prep, "Z3_ARCHIVE_BYTES", archive.stat().st_size)
    monkeypatch.setattr(prep, "Z3_ARCHIVE_SHA256", prep.sha256_file(archive))
    monkeypatch.setattr(prep, "Z3_BYTES", 6)
    with pytest.raises(ValueError, match="member"):
        prep.unpack_z3(archive, tmp_path / "bin/z3")
    assert not (tmp_path / "bin/z3").exists()


def test_unpinned_archive_is_rejected_before_unzip(tmp_path: Path) -> None:
    archive = tmp_path / "not-the-archive"
    archive.write_bytes(b"not zip bytes")
    with pytest.raises(ValueError, match="pinned bytes"):
        prep.unpack_z3(archive, tmp_path / "z3")
