"""Verify, safely extract, cache, and inventory the historical paper artifact."""

from __future__ import annotations

import hashlib
import os
import re
import shutil
import stat
import tarfile
import tempfile
import uuid
from collections.abc import Sequence
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Any, Final, TypedDict, cast
from urllib.request import Request, urlopen

from .hashing import copy_and_sha256, sha256_file
from .jsonio import load_json_object, serialize_json_line, write_json_document

EXPECTED_ARCHIVE_SHA256: Final = "2f061f4f59fd3404638db0d9ad9d130e008d4c41fdeb58ade30684d8e424607a"
SETUP_SCHEMA_VERSION: Final = 1
ARCHIVE_FILENAME: Final = "egglog-pldi-artifact.tar.gz"
SETUP_MANIFEST_FILENAME: Final = "manifest.json"

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
    raw_destination = cache_root.expanduser().absolute()
    if raw_destination.is_symlink():
        raise ValueError(f"paper artifact cache must not be a symlink: {raw_destination}")
    destination = raw_destination.resolve(strict=False)
    destination.parent.mkdir(parents=True, exist_ok=True)
    stage = Path(tempfile.mkdtemp(prefix=f".{destination.name}.staging-", dir=destination.parent))
    try:
        staged_archive = stage / ARCHIVE_FILENAME
        if archive_path is not None:
            source_path = archive_path.expanduser().resolve(strict=True)
            if not source_path.is_file():
                raise ValueError(f"paper artifact archive is not a regular file: {source_path}")
            with source_path.open("rb") as source, staged_archive.open("xb") as output:
                actual_sha256, _size = copy_and_sha256(source, output)
            source_record = {"kind": "archive", "location": str(source_path)}
        else:
            assert url is not None
            request = Request(url, headers={"User-Agent": "egglog-paper-harness/1"})
            with urlopen(request) as source, staged_archive.open("xb") as output:  # noqa: S310
                actual_sha256, _size = copy_and_sha256(source, output)
            source_record = {"kind": "url", "location": url}
        if actual_sha256 != expected_sha256:
            raise ValueError(f"paper artifact SHA-256 mismatch: expected {expected_sha256}, got {actual_sha256}")

        files = safe_extract_archive(staged_archive, stage)
        tree_sha256 = _tree_sha256(files)
        manifest: dict[str, object] = {
            "allowlist": {
                "top_level_files": sorted(ALLOWED_TOP_LEVEL_FILES),
                "tree_prefixes": list(ALLOWED_TREE_PREFIXES),
            },
            "archive": {
                "cached_path": ARCHIVE_FILENAME,
                "sha256": actual_sha256,
                "source": source_record,
            },
            "files": files,
            "schema_version": SETUP_SCHEMA_VERSION,
            "tree_sha256": tree_sha256,
        }
        write_json_document(stage / SETUP_MANIFEST_FILENAME, manifest)
        _replace_cache(stage, destination)
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


def safe_extract_archive(archive_path: Path, destination: Path) -> tuple[ExtractedFileRecord, ...]:
    """Extract regular allowlisted members after validating the complete archive."""

    allowed_names: set[str] = set()
    seen_casefolded: set[str] = set()
    present: set[str] = set()
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
            if _is_allowed(member_path):
                allowed_names.add(normalized)
                present.add(normalized)

    missing = sorted(REQUIRED_ARCHIVE_MEMBERS - present)
    if missing:
        raise ValueError(f"paper artifact archive is missing required members: {', '.join(missing)}")

    records: list[ExtractedFileRecord] = []
    directories: list[tuple[Path, int, int]] = []
    with tarfile.open(archive_path, mode="r:gz") as archive:
        for member in archive:
            member_path = _validated_member_path(member.name)
            normalized = member_path.as_posix()
            if normalized not in allowed_names:
                continue
            target = destination.joinpath(*member_path.parts)
            _require_within(target, destination)
            if member.isdir():
                target.mkdir(parents=True, exist_ok=True)
                directories.append((target, member.mode & 0o777, int(member.mtime)))
                continue
            target.parent.mkdir(parents=True, exist_ok=True)
            source = archive.extractfile(member)
            if source is None:
                raise UnsafeArchiveError(f"could not read regular archive member: {member.name!r}")
            with source, target.open("xb") as output:
                digest, size = copy_and_sha256(source, output)
            if size != member.size:
                raise UnsafeArchiveError(f"archive member size changed while extracting: {member.name!r}")
            target.chmod(member.mode & 0o777)
            os.utime(target, (member.mtime, member.mtime), follow_symlinks=False)
            records.append(
                {
                    "mode": member.mode & 0o777,
                    "mtime": int(member.mtime),
                    "path": normalized,
                    "sha256": digest,
                    "size_bytes": size,
                }
            )
    for directory, mode, mtime in sorted(directories, key=lambda item: len(item[0].parts), reverse=True):
        directory.chmod(mode)
        os.utime(directory, (mtime, mtime), follow_symlinks=False)
    return tuple(sorted(records, key=lambda record: record["path"]))


def verify_artifact_cache(
    cache_root: Path,
    *,
    expected_sha256: str = EXPECTED_ARCHIVE_SHA256,
    verify_payload: bool = True,
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

    manifest = load_json_object(manifest_path)
    if manifest.get("schema_version") != SETUP_SCHEMA_VERSION:
        raise ValueError(f"unsupported paper artifact setup manifest in {manifest_path}")
    archive_record = manifest.get("archive")
    if not isinstance(archive_record, dict) or archive_record.get("sha256") != expected_sha256:
        raise ValueError(f"paper artifact setup manifest has the wrong archive hash: {manifest_path}")
    actual_archive_sha256 = sha256_file(archive_path)
    if actual_archive_sha256 != expected_sha256:
        raise ValueError(
            f"cached paper artifact SHA-256 mismatch: expected {expected_sha256}, got {actual_archive_sha256}"
        )

    raw_files = manifest.get("files")
    if not isinstance(raw_files, list):
        raise ValueError(f"paper artifact setup manifest has no file inventory: {manifest_path}")
    files = tuple(_parse_file_record(raw_record) for raw_record in raw_files)
    inventory_paths = [record["path"] for record in files]
    if len({path.casefold() for path in inventory_paths}) != len(inventory_paths):
        raise ValueError(f"paper artifact setup manifest has duplicate file paths: {manifest_path}")
    missing = sorted(REQUIRED_ARCHIVE_MEMBERS - set(inventory_paths))
    if missing:
        raise ValueError(f"paper artifact setup manifest is missing required files: {', '.join(missing)}")
    tree_sha256 = _tree_sha256(files)
    if manifest.get("tree_sha256") != tree_sha256:
        raise ValueError(f"paper artifact setup manifest has an invalid tree hash: {manifest_path}")
    artifact_root = root / "artifact"
    if artifact_root.is_symlink() or not artifact_root.is_dir():
        raise ValueError(f"paper artifact cache is missing extracted payload: {artifact_root}")
    if verify_payload:
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


def _parse_file_record(value: object) -> ExtractedFileRecord:
    if not isinstance(value, dict):
        raise ValueError("paper artifact file inventory contains a non-object entry")
    record = cast(dict[str, Any], value)
    path_value = record.get("path")
    sha256 = record.get("sha256")
    size = record.get("size_bytes")
    mode = record.get("mode")
    mtime = record.get("mtime")
    if not isinstance(path_value, str) or not isinstance(sha256, str) or _SHA256.fullmatch(sha256) is None:
        raise ValueError("paper artifact file inventory contains invalid path or hash data")
    path = _validated_member_path(path_value)
    if not _is_allowed(path):
        raise ValueError(f"paper artifact file inventory contains a disallowed path: {path_value}")
    integers = (size, mode, mtime)
    if (
        any(not isinstance(value, int) or isinstance(value, bool) for value in integers)
        or cast(int, size) < 0
        or not 0 <= cast(int, mode) <= 0o777
    ):
        raise ValueError(f"paper artifact file inventory contains invalid metadata: {path_value}")
    return {
        "mode": cast(int, mode),
        "mtime": cast(int, mtime),
        "path": path_value,
        "sha256": sha256,
        "size_bytes": cast(int, size),
    }


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


def _replace_cache(stage: Path, destination: Path) -> None:
    backup = destination.with_name(f".{destination.name}.backup-{uuid.uuid4().hex}")
    had_destination = os.path.lexists(destination)
    if had_destination:
        os.replace(destination, backup)
    try:
        os.replace(stage, destination)
    except BaseException:
        if had_destination:
            os.replace(backup, destination)
        raise
    if had_destination:
        _remove_path(backup)


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
