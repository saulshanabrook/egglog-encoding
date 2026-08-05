"""Test paper artifact hashing, allowlisting, traversal rejection, and cache verification."""

from __future__ import annotations

from pathlib import Path

import pytest

from paper_benchmarking.artifact import UnsafeArchiveError, setup_artifact, verify_artifact_cache

from .paper_fixtures import write_artifact_archive


def test_setup_rejects_full_archive_hash_mismatch(tmp_path: Path) -> None:
    archive = tmp_path / "artifact.tar.gz"
    write_artifact_archive(archive)
    cache = tmp_path / ".paper-artifact"

    with pytest.raises(ValueError, match="SHA-256 mismatch"):
        setup_artifact(cache, archive_path=archive, expected_sha256="0" * 64)

    assert not cache.exists()


def test_setup_rejects_traversal_before_installing_cache(tmp_path: Path) -> None:
    archive = tmp_path / "artifact.tar.gz"
    digest = write_artifact_archive(
        archive,
        extra_members=(("artifact/eqlog/../../escaped.txt", b"unsafe"),),
    )
    cache = tmp_path / ".paper-artifact"

    with pytest.raises(UnsafeArchiveError, match="unsafe archive path"):
        setup_artifact(cache, archive_path=archive, expected_sha256=digest)

    assert not cache.exists()
    assert not (tmp_path / "escaped.txt").exists()


def test_setup_extracts_only_allowlisted_members_and_is_deterministic(tmp_path: Path) -> None:
    archive = tmp_path / "artifact.tar.gz"
    digest = write_artifact_archive(
        archive,
        extra_members=(("artifact/not-allowlisted.txt", b"skip me"),),
    )
    first = setup_artifact(tmp_path / "cache-one", archive_path=archive, expected_sha256=digest)
    second = setup_artifact(tmp_path / "cache-two", archive_path=archive, expected_sha256=digest)

    assert not (first.artifact_root / "not-allowlisted.txt").exists()
    assert first.manifest_path.read_bytes() == second.manifest_path.read_bytes()
    verified = verify_artifact_cache(first.root, expected_sha256=digest)
    assert verified.archive_sha256 == digest
    assert verified.tree_sha256 == first.tree_sha256


def test_setup_downloads_a_file_url_before_verification(tmp_path: Path) -> None:
    archive = tmp_path / "artifact.tar.gz"
    digest = write_artifact_archive(archive)

    cache = setup_artifact(tmp_path / "cache", url=archive.as_uri(), expected_sha256=digest)

    assert cache.archive_sha256 == digest
    assert cache.archive_path.read_bytes() == archive.read_bytes()


def test_cache_verification_rejects_modified_extracted_file(tmp_path: Path) -> None:
    archive = tmp_path / "artifact.tar.gz"
    digest = write_artifact_archive(archive)
    cache = setup_artifact(tmp_path / "cache", archive_path=archive, expected_sha256=digest)
    (cache.artifact_root / "README.md").write_text("modified\n", encoding="utf-8")

    with pytest.raises(ValueError, match="extracted metadata changed|extracted file hash changed"):
        verify_artifact_cache(cache.root, expected_sha256=digest)
