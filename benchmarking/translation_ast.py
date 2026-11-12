"""Identity-cached, compile-only whole-program representation measurements."""

from __future__ import annotations

import json
import os
import shutil
import signal
import subprocess
import tempfile
from collections.abc import Sequence
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from .config import DEFAULT_MEMORY_LIMIT_BYTES, DEFAULT_TIMEOUT_SEC
from .models import FileSpec
from .native_memory import NATIVE_ALLOCATION_EXIT, NATIVE_SETUP_EXIT, native_memory_command
from .processes import terminate_process_group
from .targets import git_dirty, git_sha, sha256_file
from .workloads import require_workload_unchanged, validate_workloads

ROOT = Path(__file__).resolve().parents[1]
CACHE_VERSION = 1
PIPELINE = {
    "count": "sexp-list-atom-literal-v1",
    "source_normalization": "self-contained-source-v1",
    "input_boundary": "self-contained-no-include-no-input-v1",
    "proof_profile": "proof-testing-rewrite-without-execution-v1",
}
PROFILES = ("c", "cp", "d", "dcp", "s", "scp")
SAFETY_STATUSES = {"memory-limited", "safety-failure", "timed-out"}


@dataclass(frozen=True)
class TranslationRequest:
    """One independently compiled source/configuration and its display identity."""

    file: FileSpec
    profile: str
    family: str
    project: str = ""
    no_aliasing: bool | None = None


def translation_ast_records(
    requests: Sequence[TranslationRequest],
    cache: Path,
    *,
    collect: bool = False,
    compiler: Path | None = None,
    timeout_sec: int = DEFAULT_TIMEOUT_SEC,
    memory_limit_bytes: int | None = DEFAULT_MEMORY_LIMIT_BYTES,
) -> tuple[dict[str, Any], ...]:
    """Reuse one compiler cohort, appending each fresh outcome before continuing.

    A recorded resource failure is terminal for this collection, including on a
    resumed invocation. Changing a guard never silently retries that identity.
    """
    keys = [(request.file.sha256, request.profile, request.no_aliasing) for request in requests]
    if len(set(keys)) != len(keys):
        raise ValueError("translation AST requests contain duplicate input/profile identities")
    if any(request.profile not in PROFILES for request in requests):
        raise ValueError("unknown translation AST profile")
    records = [json.loads(line) for line in cache.read_text().splitlines()] if cache.exists() else []
    records = [record for record in records if record["version"] == CACHE_VERSION and record["pipeline"] == PIPELINE]
    revision = None
    dirty = None
    compiler_sha: str | None
    if collect:
        # Checking each distinct source once also verifies the frozen dependency boundary.
        unique = {request.file.sha256: request.file for request in requests}
        validate_workloads(tuple(unique.values()))
        if compiler is None:
            built = subprocess.run(
                [
                    "cargo",
                    "build",
                    "--locked",
                    "--release",
                    "-p",
                    "egglog-experimental",
                    "--features",
                    "bin",
                    "--example",
                    "translation_ast",
                    "--message-format=json",
                ],
                cwd=ROOT,
                encoding="utf-8",
                stdout=subprocess.PIPE,
                check=True,
            )
            compiler = next(
                Path(message["executable"])
                for line in built.stdout.splitlines()
                if (message := json.loads(line)).get("reason") == "compiler-artifact"
                and message["target"]["name"] == "translation_ast"
                and message.get("executable")
            )
        compiler_sha = sha256_file(compiler)
        frozen = cache.parent / "executables" / compiler_sha.removeprefix("sha256:") / "translation_ast"
        frozen.parent.mkdir(parents=True, exist_ok=True)
        if not frozen.exists():
            with tempfile.TemporaryDirectory(dir=frozen.parent) as scratch:
                staged = Path(scratch) / frozen.name
                shutil.copyfile(compiler, staged)
                if sha256_file(staged) != compiler_sha:
                    raise ValueError("translation AST compiler changed before freezing")
                staged.chmod(0o555)
                os.replace(staged, frozen)
        if sha256_file(frozen) != compiler_sha:
            raise ValueError("frozen translation AST compiler identity changed")
        compiler = frozen.resolve()
        revision, dirty = git_sha(ROOT), git_dirty(ROOT)
    else:
        compiler_sha = (
            sha256_file(compiler)
            if compiler is not None
            else (records[-1]["compiler_binary_sha256"] if records else None)
        )
    indexed = {
        (record["file_sha256"], record["profile"], record["no_aliasing"]): record
        for record in records
        if record["compiler_binary_sha256"] == compiler_sha
    }
    selected = []
    halted = False
    for request, key in zip(requests, keys, strict=True):
        if key not in indexed:
            if not collect or halted:
                continue
            assert compiler is not None
            require_workload_unchanged(request.file)
            args = [str(compiler), "--profile", request.profile]
            if request.no_aliasing is False:
                args.append("--complete-slotted")
            args.append(str(request.file.absolute_path))
            command, env = native_memory_command(args, os.environ, memory_limit_bytes)
            with subprocess.Popen(
                command,
                cwd=ROOT,
                env=env,
                encoding="utf-8",
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                start_new_session=True,
            ) as process:
                try:
                    stdout, stderr = process.communicate(timeout=timeout_sec)
                    returncode = process.returncode
                except subprocess.TimeoutExpired:
                    terminate_process_group(process)
                    stdout, stderr = process.communicate()
                    returncode = None
                finally:
                    terminate_process_group(process)
            require_workload_unchanged(request.file)
            row: dict[str, Any] = {
                "source_ast_nodes": None,
                "normalized_source_ast_nodes": None,
                "output_ast_nodes": None,
                "error_stage": "process",
                "error": None,
                "include_files": [],
            }
            if returncode == 0:
                measured = json.loads(stdout)
                if (
                    measured["version"] != 1
                    or measured["file"] != str(request.file.absolute_path)
                    or measured["profile"] != request.profile
                    or measured["no_aliasing"] != request.no_aliasing
                    or measured["source_normalization"] != PIPELINE["source_normalization"]
                    or measured["count_convention"] != PIPELINE["count"]
                    or measured["include_files"]
                ):
                    raise ValueError(
                        f"translation AST compiler returned a different identity: {request.file.display_path}"
                    )
                row.update(measured)
                status = measured["status"]
            else:
                status = (
                    "timed-out"
                    if returncode is None
                    else "memory-limited"
                    if returncode == NATIVE_ALLOCATION_EXIT
                    else "safety-failure"
                    if returncode in (NATIVE_SETUP_EXIT, -signal.SIGKILL)
                    else "failure"
                )
                row["error"] = (
                    f"compiler timed out after {timeout_sec} seconds"
                    if returncode is None
                    else stderr.strip() or stdout.strip() or f"compiler exited with status {returncode}"
                )
            indexed[key] = {
                "version": CACHE_VERSION,
                "pipeline": PIPELINE,
                "compiler_binary": str(compiler),
                "compiler_binary_sha256": compiler_sha,
                "source_checkout": str(ROOT),
                "source_revision": revision,
                "source_dirty": dirty,
                "file": request.file.display_path,
                "file_sha256": request.file.sha256,
                "profile": request.profile,
                "no_aliasing": request.no_aliasing,
                "family": request.family,
                "project": request.project,
                "dependency_boundary": {"policy": PIPELINE["input_boundary"], "include_files": [], "input_files": []},
                "timeout_sec": timeout_sec,
                "memory_limit_bytes": memory_limit_bytes,
                "status": status,
                "exit_code": returncode,
                "row": row,
            }
            cache.parent.mkdir(parents=True, exist_ok=True)
            with cache.open("a") as handle:
                handle.write(json.dumps(indexed[key], ensure_ascii=False, allow_nan=False) + "\n")
        selected.append(indexed[key])
        if collect and indexed[key]["status"] in SAFETY_STATUSES:
            halted = True
    if collect and compiler is not None and sha256_file(compiler) != compiler_sha:
        raise ValueError("frozen translation AST compiler changed during collection")
    return tuple(selected)
