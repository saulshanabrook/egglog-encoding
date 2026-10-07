"""Guarded source preparation with pinned inputs and local command evidence."""

from __future__ import annotations

import hashlib
import json
from dataclasses import asdict
from pathlib import Path
from typing import Any

from process_guard import GROUP_LIMIT_BYTES
from scripts.reproduction_process import DISK_RESERVE_BYTES, run_bounded_command

MEMORY_BYTES = GROUP_LIMIT_BYTES


def sha256_file(path: Path) -> str:
    """Use raw hex required by the capture protocol, without loading large files."""
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def write_json(path: Path, value: Any) -> None:
    """Never overwrite a retained receipt, including an incomplete earlier run."""
    with path.open("x") as output:
        json.dump(value, output, indent=2, default=str)
        output.write("\n")


class Preparation:
    """Own sequential guarded steps and immutable command/result evidence."""

    def __init__(self, directory: Path, *, continuation: bool = False):
        self.directory = directory.resolve()
        self.logs = self.directory / "steps"
        self.logs.mkdir(exist_ok=continuation)
        self.count = max((int(p.name.split("-")[0]) for p in self.logs.glob("*.request.json")), default=0)

    def step(self, name: str, command: list[str], *, cwd: Path | None = None, timeout: int = 600) -> str:
        self.count += 1
        prefix = self.logs / f"{self.count:03}-{name}"
        workdir = (cwd or self.directory).resolve()
        request = {
            "command": command,
            "cwd": str(workdir),
            "timeout_sec": timeout,
            "memory_limit_bytes": MEMORY_BYTES,
            "require_guard": True,
            "disk_reserve_bytes": DISK_RESERVE_BYTES,
        }
        write_json(prefix.with_suffix(".request.json"), request)
        print(f"START {self.count:03} {name}", flush=True)
        try:
            result = run_bounded_command(
                command,
                workdir,
                prefix,
                timeout_sec=timeout,
                memory_limit_bytes=MEMORY_BYTES,
                require_guard=True,
                disk_reserve_bytes=DISK_RESERVE_BYTES,
            )
        except (OSError, ValueError) as error:
            write_json(prefix.with_suffix(".result.json"), {"status": "launch-refused", "reason": str(error)})
            raise
        write_json(prefix.with_suffix(".result.json"), asdict(result))
        print(f"END {self.count:03} {name}: {result.status} ({result.wall_sec:.1f}s)", flush=True)
        if result.status != "success":
            detail = f": {result.message}" if result.message else ""
            raise RuntimeError(f"{name}: {result.status}{detail}; see {prefix}.result.json")
        return result.stdout_path.read_text()

    def apply_patch(self, checkout: Path, patch: Path) -> None:
        """Apply a versioned diff to acquired source and retain its exact bytes."""
        checkout = checkout.resolve()
        if not checkout.is_relative_to(self.directory / "sources"):
            raise ValueError("refusing to patch a source outside this preparation")
        retained = self.directory / "patches" / patch.name
        retained.parent.mkdir(exist_ok=True)
        with retained.open("xb") as output:
            output.write(patch.read_bytes())
        write_json(
            retained.with_suffix(".json"),
            {"checkout": str(checkout), "patch_sha256": sha256_file(retained)},
        )
        self.step(patch.stem + "-check", ["git", "apply", "--check", str(retained)], cwd=checkout, timeout=30)
        self.step(patch.stem + "-apply", ["git", "apply", str(retained)], cwd=checkout, timeout=30)


def acquire_source(preparation: Preparation, name: str, url: str, revision: str) -> Path:
    """Acquire a fresh source directory and reject any checkout other than its pin."""
    source = preparation.directory / "sources" / name
    preparation.step(f"{name}-init", ["git", "init", str(source)])
    preparation.step(f"{name}-remote", ["git", "remote", "add", "origin", url], cwd=source)
    preparation.step(f"{name}-fetch", ["git", "fetch", "--depth", "1", "origin", revision], cwd=source)
    preparation.step(f"{name}-checkout", ["git", "checkout", "--detach", revision], cwd=source)
    if preparation.step(f"{name}-head", ["git", "rev-parse", "HEAD"], cwd=source, timeout=30).strip() != revision:
        raise ValueError(f"{name} revision differs from requested pin")
    return source
