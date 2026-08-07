"""Verify, safely extract, cache, and inventory the historical paper artifact."""

from __future__ import annotations

import hashlib
import os
import re
import shutil
import stat
import tarfile
import tempfile
from collections.abc import Sequence
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Final, TypedDict
from urllib.request import Request, urlopen

from .hashing import copy_and_sha256, sha256_file, sha256_stream
from .jsonio import load_json_object, serialize_json_line, write_json_document

EXPECTED_ARCHIVE_SHA256: Final = "2f061f4f59fd3404638db0d9ad9d130e008d4c41fdeb58ade30684d8e424607a"
SETUP_SCHEMA_VERSION: Final = 1
ARCHIVE_FILENAME: Final = "egglog-pldi-artifact.tar.gz"
SETUP_MANIFEST_FILENAME: Final = "manifest.json"
DOWNLOAD_TIMEOUT_SEC: Final = 60
MAX_ARCHIVE_BYTES: Final = 2 * 1024 * 1024 * 1024

ALLOWED_TOP_LEVEL_FILES: Final = frozenset(
    {
        "artifact/.dockerignore",
        "artifact/.gitignore",
        "artifact/.gitmodules",
        "artifact/Dockerfile",
        "artifact/Makefile",
        "artifact/README.md",
        "artifact/docker.sh",
    }
)
ALLOWED_TREE_PREFIXES: Final = (
    "artifact/eqlog",
    "artifact/eqlog-herbie-tweaks",
    "artifact/herbie-eqlog",
    "artifact/micro-benchmarks",
    "artifact/pointer-analysis-benchmark",
)
REQUIRED_ARCHIVE_MEMBERS: Final = frozenset(
    {
        "artifact/README.md",
        "artifact/Makefile",
        "artifact/eqlog/Cargo.toml",
        "artifact/eqlog-herbie-tweaks/Cargo.toml",
        "artifact/herbie-eqlog/evaleqlog.sh",
        "artifact/micro-benchmarks/Cargo.toml",
        "artifact/pointer-analysis-benchmark/run.py",
    }
)

_SHA256 = re.compile(r"[0-9a-f]{64}\Z")


class ExtractedFileRecord(TypedDict):
    """One immutable source file extracted from the verified archive."""

    mode: int
    mtime: int
    path: str
    sha256: str
    size_bytes: int


@dataclass(frozen=True)
class ArtifactCache:
    """Verified cache paths and hashes consumed by paper runs."""

    root: Path
    artifact_root: Path
    archive_path: Path
    manifest_path: Path
    archive_sha256: str
    tree_sha256: str
    manifest_sha256: str
    file_count: int

    def to_record(self) -> dict[str, object]:
        """Return the run-manifest provenance record for this cache."""

        return {
            "archive_path": str(self.archive_path),
            "archive_sha256": self.archive_sha256,
            "artifact_root": str(self.artifact_root),
            "file_count": self.file_count,
            "manifest_path": str(self.manifest_path),
            "manifest_sha256": self.manifest_sha256,
            "setup_schema_version": SETUP_SCHEMA_VERSION,
            "tree_sha256": self.tree_sha256,
        }


class UnsafeArchiveError(ValueError):
    """Raised when an archive member cannot be handled without trust."""


def setup_artifact(
    cache_root: Path,
    *,
    archive_path: Path | None = None,
    url: str | None = None,
    expected_sha256: str = EXPECTED_ARCHIVE_SHA256,
) -> ArtifactCache:
    """Verify one local or remote archive and atomically install its allowlist."""

    if (archive_path is None) == (url is None):
        raise ValueError("select exactly one paper artifact source: archive_path or url")
    _validate_expected_sha256(expected_sha256)
    destination = cache_root.expanduser().absolute()
    if os.path.lexists(destination):
        raise FileExistsError(f"paper artifact cache already exists; remove it explicitly before setup: {destination}")
    destination.parent.mkdir(parents=True, exist_ok=True)
    stage = Path(tempfile.mkdtemp(prefix=f".{destination.name}.staging-", dir=destination.parent))
    try:
        staged_archive = stage / ARCHIVE_FILENAME
        if archive_path is not None:
            source_path = archive_path.expanduser().resolve(strict=True)
            if not source_path.is_file():
                raise ValueError(f"paper artifact archive is not a regular file: {source_path}")
            with source_path.open("rb") as source, staged_archive.open("xb") as output:
                actual_sha256, _size = copy_and_sha256(
                    source,
                    output,
                    max_bytes=MAX_ARCHIVE_BYTES,
                )
        else:
            assert url is not None
            request = Request(url, headers={"User-Agent": "egglog-paper-harness/1"})
            with (
                urlopen(request, timeout=DOWNLOAD_TIMEOUT_SEC) as source,  # noqa: S310
                staged_archive.open("xb") as output,
            ):
                actual_sha256, _size = copy_and_sha256(
                    source,
                    output,
                    max_bytes=MAX_ARCHIVE_BYTES,
                )
        if actual_sha256 != expected_sha256:
            raise ValueError(f"paper artifact SHA-256 mismatch: expected {expected_sha256}, got {actual_sha256}")

        files = safe_extract_archive(staged_archive, stage)
        tree_sha256 = _tree_sha256(files)
        manifest = _setup_manifest(actual_sha256, files)
        write_json_document(stage / SETUP_MANIFEST_FILENAME, manifest)
        _install_cache(stage, destination)
    except BaseException:
        _remove_path(stage)
        raise

    manifest_path = destination / SETUP_MANIFEST_FILENAME
    return ArtifactCache(
        root=destination,
        artifact_root=destination / "artifact",
        archive_path=destination / ARCHIVE_FILENAME,
        manifest_path=manifest_path,
        archive_sha256=expected_sha256,
        tree_sha256=tree_sha256,
        manifest_sha256=sha256_file(manifest_path),
        file_count=len(files),
    )


def _setup_manifest(
    archive_sha256: str,
    files: Sequence[ExtractedFileRecord],
) -> dict[str, object]:
    """Build the canonical manifest entirely from the authenticated archive."""

    return {
        "allowlist": {
            "top_level_files": sorted(ALLOWED_TOP_LEVEL_FILES),
            "tree_prefixes": list(ALLOWED_TREE_PREFIXES),
        },
        "archive": {
            "cached_path": ARCHIVE_FILENAME,
            "sha256": archive_sha256,
        },
        "files": list(files),
        "schema_version": SETUP_SCHEMA_VERSION,
        "tree_sha256": _tree_sha256(files),
    }


def safe_extract_archive(archive_path: Path, destination: Path) -> tuple[ExtractedFileRecord, ...]:
    """Extract regular allowlisted members after validating the complete archive."""

    records = _inventory_archive(archive_path)
    expected = {record["path"]: record for record in records}
    with tarfile.open(archive_path, mode="r:gz") as archive:
        for member in archive:
            member_path = _validated_member_path(member.name)
            normalized = member_path.as_posix()
            record = expected.get(normalized)
            if record is None:
                continue
            target = destination.joinpath(*member_path.parts)
            _require_within(target, destination)
            target.parent.mkdir(parents=True, exist_ok=True)
            source = archive.extractfile(member)
            if source is None:
                raise UnsafeArchiveError(f"could not read regular archive member: {member.name!r}")
            with source, target.open("xb") as output:
                digest, size = copy_and_sha256(source, output)
            if digest != record["sha256"] or size != record["size_bytes"]:
                raise UnsafeArchiveError(f"archive member changed while extracting: {member.name!r}")
            target.chmod(record["mode"])
            os.utime(target, (record["mtime"], record["mtime"]), follow_symlinks=False)
    return records


def _inventory_archive(archive_path: Path) -> tuple[ExtractedFileRecord, ...]:
    """Derive the canonical extracted-file inventory from the archive itself."""

    seen_casefolded: set[str] = set()
    present: set[str] = set()
    records: list[ExtractedFileRecord] = []
    with tarfile.open(archive_path, mode="r:gz") as archive:
        for member in archive:
            member_path = _validated_member_path(member.name)
            normalized = member_path.as_posix()
            collision_key = normalized.casefold()
            if collision_key in seen_casefolded:
                raise UnsafeArchiveError(f"duplicate or case-colliding archive path: {member.name!r}")
            seen_casefolded.add(collision_key)
            if not (member.isdir() or member.isreg()):
                raise UnsafeArchiveError(f"unsupported archive member type: {member.name!r}")
            if normalized in REQUIRED_ARCHIVE_MEMBERS and not member.isreg():
                raise UnsafeArchiveError(f"required archive member is not a regular file: {member.name!r}")
            if not (_is_allowed(member_path) and member.isreg()):
                continue
            present.add(normalized)
            source = archive.extractfile(member)
            if source is None:
                raise UnsafeArchiveError(f"could not read regular archive member: {member.name!r}")
            with source:
                digest, size = sha256_stream(source)
            if size != member.size:
                raise UnsafeArchiveError(f"archive member size changed while reading: {member.name!r}")
            records.append(
                {
                    "mode": member.mode & 0o777,
                    "mtime": int(member.mtime),
                    "path": normalized,
                    "sha256": digest,
                    "size_bytes": size,
                }
            )

    missing = sorted(REQUIRED_ARCHIVE_MEMBERS - present)
    if missing:
        raise ValueError(f"paper artifact archive is missing required members: {', '.join(missing)}")

    return tuple(sorted(records, key=lambda record: record["path"]))


def verify_artifact_cache(
    cache_root: Path,
    *,
    expected_sha256: str = EXPECTED_ARCHIVE_SHA256,
) -> ArtifactCache:
    """Fail closed unless the cache matches its archive and extracted inventory."""

    _validate_expected_sha256(expected_sha256)
    raw_root = cache_root.expanduser().absolute()
    if raw_root.is_symlink():
        raise ValueError(f"paper artifact cache must not be a symlink: {raw_root}")
    root = raw_root.resolve(strict=True)
    if not root.is_dir():
        raise ValueError(f"paper artifact cache is not a regular directory: {root}")
    archive_path = root / ARCHIVE_FILENAME
    manifest_path = root / SETUP_MANIFEST_FILENAME
    if archive_path.is_symlink() or not archive_path.is_file():
        raise ValueError(f"paper artifact cache is missing {archive_path}")
    if manifest_path.is_symlink() or not manifest_path.is_file():
        raise ValueError(f"paper artifact cache is missing {manifest_path}")

    actual_archive_sha256 = sha256_file(archive_path)
    if actual_archive_sha256 != expected_sha256:
        raise ValueError(
            f"cached paper artifact SHA-256 mismatch: expected {expected_sha256}, got {actual_archive_sha256}"
        )

    files = _inventory_archive(archive_path)
    tree_sha256 = _tree_sha256(files)
    manifest = load_json_object(manifest_path)
    if manifest != _setup_manifest(actual_archive_sha256, files):
        raise ValueError(f"paper artifact setup manifest does not match its archive: {manifest_path}")
    artifact_root = root / "artifact"
    if artifact_root.is_symlink() or not artifact_root.is_dir():
        raise ValueError(f"paper artifact cache is missing extracted payload: {artifact_root}")
    _verify_cache_census(root, files)
    for record in files:
        path = root.joinpath(*PurePosixPath(record["path"]).parts)
        _verify_extracted_file(path, record)

    return ArtifactCache(
        root=root,
        artifact_root=artifact_root,
        archive_path=archive_path,
        manifest_path=manifest_path,
        archive_sha256=actual_archive_sha256,
        tree_sha256=tree_sha256,
        manifest_sha256=sha256_file(manifest_path),
        file_count=len(files),
    )


def render_setup_summary(cache: ArtifactCache) -> str:
    """Render the machine-independent setup result as Markdown."""

    return (
        "# Paper Artifact Setup\n\n"
        f"- Cache: `{cache.root}`\n"
        f"- Archive SHA-256: `{cache.archive_sha256}`\n"
        f"- Extracted tree SHA-256: `{cache.tree_sha256}`\n"
        f"- Extracted files: {cache.file_count}\n"
    )


def _validated_member_path(raw_name: str) -> PurePosixPath:
    name = raw_name[:-1] if raw_name.endswith("/") else raw_name
    if not name or name.startswith("/") or "\\" in name:
        raise UnsafeArchiveError(f"unsafe archive path: {raw_name!r}")
    raw_parts = name.split("/")
    if any(part in {"", ".", ".."} for part in raw_parts):
        raise UnsafeArchiveError(f"unsafe archive path: {raw_name!r}")
    path = PurePosixPath(*raw_parts)
    if path.is_absolute() or any(part == ".." for part in path.parts):
        raise UnsafeArchiveError(f"unsafe archive path: {raw_name!r}")
    return path


def _is_allowed(path: PurePosixPath) -> bool:
    normalized = path.as_posix()
    if normalized == "artifact" or normalized in ALLOWED_TOP_LEVEL_FILES:
        return True
    return any(normalized == prefix or normalized.startswith(prefix + "/") for prefix in ALLOWED_TREE_PREFIXES)


def _require_within(path: Path, root: Path) -> None:
    try:
        path.resolve(strict=False).relative_to(root.resolve(strict=False))
    except ValueError as error:
        raise UnsafeArchiveError(f"archive extraction escaped destination: {path}") from error


def _tree_sha256(files: Sequence[ExtractedFileRecord]) -> str:
    return hashlib.sha256(serialize_json_line(list(files))).hexdigest()


def _verify_extracted_file(path: Path, record: ExtractedFileRecord) -> None:
    try:
        metadata = path.lstat()
    except FileNotFoundError as error:
        raise ValueError(f"paper artifact cache is missing extracted file: {path}") from error
    if not stat.S_ISREG(metadata.st_mode):
        raise ValueError(f"paper artifact extracted path is not a regular file: {path}")
    if (
        metadata.st_size != record["size_bytes"]
        or metadata.st_mode & 0o777 != record["mode"]
        or int(metadata.st_mtime) != record["mtime"]
    ):
        raise ValueError(f"paper artifact extracted metadata changed: {path}")
    actual_sha256 = sha256_file(path)
    if actual_sha256 != record["sha256"]:
        raise ValueError(f"paper artifact extracted file hash changed: {path}")


def _verify_cache_census(root: Path, files: Sequence[ExtractedFileRecord]) -> None:
    expected_files = {ARCHIVE_FILENAME, SETUP_MANIFEST_FILENAME}
    expected_files.update(record["path"] for record in files)
    expected_directories: set[str] = set()
    for relative in expected_files:
        parent = PurePosixPath(relative).parent
        while parent != PurePosixPath("."):
            expected_directories.add(parent.as_posix())
            parent = parent.parent

    actual_files: set[str] = set()
    actual_directories: set[str] = set()
    for path in root.rglob("*"):
        relative = path.relative_to(root).as_posix()
        metadata = path.lstat()
        if stat.S_ISREG(metadata.st_mode):
            actual_files.add(relative)
        elif stat.S_ISDIR(metadata.st_mode):
            actual_directories.add(relative)
        else:
            raise ValueError(f"paper artifact cache contains a symlink or special path: {path}")
    if actual_files != expected_files or actual_directories != expected_directories:
        extras = sorted((actual_files - expected_files) | (actual_directories - expected_directories))
        missing = sorted((expected_files - actual_files) | (expected_directories - actual_directories))
        detail = []
        if extras:
            detail.append("unexpected: " + ", ".join(extras))
        if missing:
            detail.append("missing: " + ", ".join(missing))
        raise ValueError("paper artifact cache tree does not match its archive (" + "; ".join(detail) + ")")


def _install_cache(stage: Path, destination: Path) -> None:
    """Publish a staged cache without replacing any existing path."""

    if os.path.lexists(destination):
        raise FileExistsError(f"paper artifact cache appeared during setup: {destination}")
    stage.rename(destination)


def _remove_path(path: Path) -> None:
    if not os.path.lexists(path):
        return
    if path.is_symlink() or not path.is_dir():
        path.unlink()
    else:
        shutil.rmtree(path)


def _validate_expected_sha256(value: str) -> None:
    if _SHA256.fullmatch(value) is None:
        raise ValueError(f"invalid expected SHA-256: {value!r}")
