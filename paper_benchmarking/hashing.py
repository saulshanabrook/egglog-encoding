"""Hash archives, files, symlinks, and directory trees deterministically."""

from __future__ import annotations

import hashlib
import stat
from dataclasses import dataclass
from pathlib import Path
from typing import IO, Protocol

_COPY_CHUNK_SIZE = 1024 * 1024


@dataclass(frozen=True)
class PathDigest:
    """One provenance digest for a file, symlink, or directory tree."""

    path: str
    kind: str
    sha256: str
    size_bytes: int | None

    def to_record(self) -> dict[str, object]:
        """Return the stable JSON representation."""

        return {
            "kind": self.kind,
            "path": self.path,
            "sha256": self.sha256,
            "size_bytes": self.size_bytes,
        }


def copy_and_sha256(
    source: IO[bytes],
    destination: IO[bytes],
    *,
    max_bytes: int | None = None,
) -> tuple[str, int]:
    """Copy a complete stream while computing its SHA-256 and byte count."""

    digest = hashlib.sha256()
    size = 0
    while chunk := source.read(_COPY_CHUNK_SIZE):
        destination.write(chunk)
        digest.update(chunk)
        size += len(chunk)
        if max_bytes is not None and size > max_bytes:
            raise ValueError(f"input exceeds maximum size of {max_bytes} bytes")
    return digest.hexdigest(), size


def sha256_file(path: Path) -> str:
    """Hash the complete contents of one regular file."""

    with path.open("rb") as handle:
        digest, _size = sha256_stream(handle)
    return digest


def sha256_stream(source: IO[bytes]) -> tuple[str, int]:
    """Hash one complete byte stream without materializing it."""

    digest = hashlib.sha256()
    size = 0
    while chunk := source.read(_COPY_CHUNK_SIZE):
        digest.update(chunk)
        size += len(chunk)
    return digest.hexdigest(), size


def hash_path(path: Path) -> PathDigest:
    """Hash one regular path, rejecting symlinks and special files."""

    absolute_path = path.expanduser().absolute()
    metadata = path.lstat()
    if stat.S_ISLNK(metadata.st_mode):
        raise ValueError(f"paper benchmark input must not be a symlink: {path}")
    if stat.S_ISREG(metadata.st_mode):
        return PathDigest(str(absolute_path), "file", sha256_file(path), metadata.st_size)
    if stat.S_ISDIR(metadata.st_mode):
        return PathDigest(str(absolute_path), "directory", _sha256_directory(path), None)
    raise ValueError(f"cannot provenance-hash special path: {path}")


def _sha256_directory(root: Path) -> str:
    digest = hashlib.sha256(b"paper-directory-v1\0")
    children = sorted(root.rglob("*"), key=lambda child: child.relative_to(root).as_posix())
    for child in children:
        relative = child.relative_to(root).as_posix().encode()
        metadata = child.lstat()
        if stat.S_ISLNK(metadata.st_mode):
            raise ValueError(f"paper benchmark input tree must not contain symlinks: {child}")
        elif stat.S_ISDIR(metadata.st_mode):
            _update_tree_digest(digest, b"D", relative, b"")
        elif stat.S_ISREG(metadata.st_mode):
            payload = f"{metadata.st_mode & 0o777:o}:{metadata.st_size}:{sha256_file(child)}".encode()
            _update_tree_digest(digest, b"F", relative, payload)
        else:
            raise ValueError(f"cannot provenance-hash special path: {child}")
    return digest.hexdigest()


class _Hash(Protocol):
    def update(self, data: bytes) -> object: ...


def _update_tree_digest(digest: _Hash, kind: bytes, relative: bytes, payload: bytes) -> None:
    digest.update(kind)
    digest.update(b"\0")
    digest.update(relative)
    digest.update(b"\0")
    digest.update(payload)
    digest.update(b"\0")
