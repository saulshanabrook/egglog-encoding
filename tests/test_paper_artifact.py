"""Test paper artifact hashing, allowlisting, traversal rejection, and cache verification."""

from __future__ import annotations

import json
from pathlib import Path

import pytest

from paper_benchmarking.artifact import UnsafeArchiveError, setup_artifact, verify_artifact_cache
from paper_benchmarking.hashing import sha256_file

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


def test_setup_refuses_to_replace_an_existing_directory(tmp_path: Path) -> None:
    archive = tmp_path / "artifact.tar.gz"
    digest = write_artifact_archive(archive)
    destination = tmp_path / "important"
    destination.mkdir()
    sentinel = destination / "keep.txt"
    sentinel.write_text("keep\n", encoding="utf-8")

    with pytest.raises(FileExistsError, match="already exists"):
        setup_artifact(destination, archive_path=archive, expected_sha256=digest)

    assert sentinel.read_text(encoding="utf-8") == "keep\n"


def test_cache_verification_derives_inventory_from_archive(tmp_path: Path) -> None:
    archive = tmp_path / "artifact.tar.gz"
    digest = write_artifact_archive(archive)
    cache = setup_artifact(tmp_path / "cache", archive_path=archive, expected_sha256=digest)
    payload = cache.artifact_root / "eqlog" / "Cargo.toml"
    payload.write_text("forged\n", encoding="utf-8")
    manifest = json.loads(cache.manifest_path.read_text(encoding="utf-8"))
    record = next(record for record in manifest["files"] if record["path"] == "artifact/eqlog/Cargo.toml")
    record["size_bytes"] = payload.stat().st_size
    record["sha256"] = sha256_file(payload)
    cache.manifest_path.write_text(json.dumps(manifest), encoding="utf-8")

    with pytest.raises(ValueError, match="manifest does not match its archive"):
        verify_artifact_cache(cache.root, expected_sha256=digest)


def test_cache_verification_rejects_unmanifested_payload(tmp_path: Path) -> None:
    archive = tmp_path / "artifact.tar.gz"
    digest = write_artifact_archive(archive)
    cache = setup_artifact(tmp_path / "cache", archive_path=archive, expected_sha256=digest)
    (cache.artifact_root / "eqlog" / ".cargo").mkdir()
    (cache.artifact_root / "eqlog" / ".cargo" / "config.toml").write_text(
        "[build]\nrustflags = []\n",
        encoding="utf-8",
    )

    with pytest.raises(ValueError, match="tree does not match its archive"):
        verify_artifact_cache(cache.root, expected_sha256=digest)
