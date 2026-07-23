"""Parse, materialize, build, describe, and construct commands for targets.

This module owns backend/treatment workload command construction. Subprocess
measurement and report persistence belong in their dedicated modules.
"""

from __future__ import annotations

import hashlib
import os
import re
import subprocess
import sys
from collections.abc import Sequence
from dataclasses import replace
from pathlib import Path
from typing import Literal

from rich.console import Console
from rich.text import Text

from .models import Backend, FileSpec, ResolvedTarget, TargetRequest, TargetRow, Treatment, backend_spec

BuildProfile = Literal["release", "profiling"]


def treatment_flags(treatment: Treatment) -> list[str]:
    return {
        "off": [],
        "term": ["--term-encoding"],
        "proofs": ["--proofs"],
        "causal-receipts": ["--causal-receipts"],
        "causal-proofs": ["--causal-slice", "--proofs"],
    }[treatment]


def backend_flags(backend: Backend) -> list[str]:
    return list(backend_spec(backend).flags)


def parse_target(raw: str) -> TargetRequest:
    if "=" in raw:
        label, source = raw.split("=", 1)
        if not label:
            raise ValueError(f"target label cannot be empty: {raw}")
        parse_pr_number(source)
        return TargetRequest(raw=raw, source=source, label=label)
    if parse_pr_number(raw) is not None:
        return TargetRequest(raw=raw, source=raw, label=raw)
    return TargetRequest(raw=raw, source=raw, label=None)


def parse_pr_number(source: str) -> int | None:
    if not source.startswith("#"):
        return None
    match = re.fullmatch(r"#([1-9][0-9]*)", source)
    if match is None:
        raise ValueError(f"invalid PR target {source!r}: use #<positive-number>")
    return int(match.group(1))


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return f"sha256:{digest.hexdigest()}"


def sha256_directory(path: Path) -> str:
    digest = hashlib.sha256()
    files = sorted(candidate for candidate in path.rglob("*") if candidate.is_file())
    for file in files:
        relative = file.relative_to(path).as_posix().encode()
        digest.update(relative)
        digest.update(b"\0")
        with file.open("rb") as handle:
            for chunk in iter(lambda: handle.read(1024 * 1024), b""):
                digest.update(chunk)
        digest.update(b"\0")
    return f"sha256:{digest.hexdigest()}"


def run_text(args: Sequence[str], cwd: Path) -> str:
    completed = subprocess.run(
        list(args),
        cwd=cwd,
        check=True,
        text=True,
        capture_output=True,
    )
    return completed.stdout.strip()


def git_root_for_path(path: Path) -> Path:
    return Path(run_text(["git", "rev-parse", "--show-toplevel"], path)).resolve()


def git_sha(cwd: Path, ref: str = "HEAD") -> str:
    return run_text(["git", "rev-parse", ref], cwd)


def git_dirty(cwd: Path) -> bool:
    return bool(run_text(["git", "status", "--porcelain"], cwd))


def sanitize_label(value: str) -> str:
    sanitized = re.sub(r"[^A-Za-z0-9_.-]+", "-", value).strip(".-")
    return sanitized or "target"


def find_clean_worktree_for_sha(repo: Path, sha: str) -> Path | None:
    output = run_text(["git", "worktree", "list", "--porcelain"], repo)
    current_path: Path | None = None
    current_head: str | None = None
    for line in [*output.splitlines(), ""]:
        if line.startswith("worktree "):
            current_path = Path(line.removeprefix("worktree ")).resolve()
            current_head = None
        elif line.startswith("HEAD "):
            current_head = line.removeprefix("HEAD ")
        elif not line:
            if (
                current_path is not None
                and current_head == sha
                and current_path.is_dir()
                and not git_dirty(current_path)
            ):
                return current_path
            current_path = None
            current_head = None
    return None


def materialize_git_ref(repo: Path, ref: str, label_hint: str | None) -> tuple[Path, str]:
    sha = git_sha(repo, ref)
    existing = find_clean_worktree_for_sha(repo, sha)
    if existing is not None:
        return (existing, sha)

    base_name = sanitize_label(label_hint or ref.replace("/", "-").replace("@", "") or sha[:12])
    worktree_root = repo / ".bench-worktrees"
    path = worktree_root / base_name
    if path.exists():
        path_stem = f"{base_name}-{sha[:12]}"
        path = worktree_root / path_stem
        disambiguator = 2
        while path.exists():
            path = worktree_root / f"{path_stem}-{disambiguator}"
            disambiguator += 1
    path.parent.mkdir(parents=True, exist_ok=True)
    subprocess.run(
        ["git", "worktree", "add", "--detach", str(path), sha],
        cwd=repo,
        check=True,
        stdout=sys.stderr,
        stderr=sys.stderr,
    )
    return (path, sha)


def fetch_pr_ref(repo: Path, number: int) -> str:
    ref = f"refs/remotes/origin/pr/{number}"
    subprocess.run(
        ["git", "fetch", "origin", f"+refs/pull/{number}/head:{ref}"],
        cwd=repo,
        check=True,
        stdout=sys.stderr,
        stderr=sys.stderr,
    )
    return ref


def materialize_pr_target(repo: Path, source: str, label_hint: str | None) -> tuple[Path, str]:
    number = parse_pr_number(source)
    if number is None:
        raise ValueError(f"not a PR target: {source}")
    ref = fetch_pr_ref(repo, number)
    return materialize_git_ref(repo, ref, label_hint or source)


def resolve_path_target(source: str, invocation_cwd: Path) -> tuple[Path, str]:
    raw_path = Path(source).expanduser()
    if not raw_path.is_absolute():
        raw_path = invocation_cwd / raw_path
    root = git_root_for_path(raw_path.resolve())
    return (root, "HEAD")


def target_row_for_request(
    request: TargetRequest,
    checkout_path: Path,
    git_ref_value: str,
) -> TargetRow:
    return TargetRow(
        source=request.raw,
        path=str(checkout_path.resolve()),
        git_ref=git_ref_value,
        git_sha=git_sha(checkout_path),
        is_dirty=git_dirty(checkout_path),
        label=request.label,
    )


def materialize_target_request(request: TargetRequest, invocation_cwd: Path, repo_root: Path) -> TargetRow:
    if request.is_label_lookup:
        raise ValueError("cache-only target labels cannot be materialized without a cached report row")
    if request.source.startswith("@"):
        ref = request.source[1:]
        if not ref:
            raise ValueError(f"git target is missing a ref: {request.raw}")
        checkout_path, git_ref_value = materialize_git_ref(repo_root, ref, request.label or ref)
    elif parse_pr_number(request.source) is not None:
        checkout_path, git_ref_value = materialize_pr_target(repo_root, request.source, request.label)
    else:
        checkout_path, git_ref_value = resolve_path_target(request.source, invocation_cwd)
    return target_row_for_request(request, checkout_path, git_ref_value)


def build_target(
    row: TargetRow,
    console: Console,
    build_profile: BuildProfile = "release",
    cargo_features: Sequence[str] = (),
) -> tuple[Path, str]:
    checkout_path = Path(row.path)
    console.print(Text.assemble(("Building", "bold"), " ", _display_target(row)))
    if build_profile == "release":
        build_args = ["cargo", "build", "--release", "-p", "egglog-experimental"]
    else:
        build_args = ["cargo", "build", "--profile", "profiling", "-p", "egglog-experimental"]
    if cargo_features:
        build_args.extend(("--features", ",".join(cargo_features)))
    subprocess.run(
        build_args,
        cwd=checkout_path,
        check=True,
        stdout=sys.stderr,
        stderr=sys.stderr,
    )
    binary_name = "egglog-experimental.exe" if os.name == "nt" else "egglog-experimental"
    binary_path = checkout_path / "target" / build_profile / binary_name
    if not binary_path.is_file():
        raise FileNotFoundError(f"{build_profile} binary was not produced: {binary_path}")
    binary_sha256 = sha256_file(binary_path)
    return (binary_path, binary_sha256)


def build_resolved_target(
    request: TargetRequest,
    row: TargetRow,
    console: Console,
    build_profile: BuildProfile,
    cargo_features: Sequence[str],
) -> ResolvedTarget:
    binary_path, binary_sha256 = build_target(row, console, build_profile, cargo_features)
    row = replace(row, is_dirty=git_dirty(Path(row.path)))
    return ResolvedTarget(request=request, row=row, binary_sha256=binary_sha256, binary_path=binary_path)


def resolve_profile_target(
    request: TargetRequest,
    backend: Backend,
    invocation_cwd: Path,
    repo_root: Path,
    console: Console,
) -> ResolvedTarget:
    if request.is_label_lookup:
        raise ValueError("profile mode does not support cache-only label= targets; use label=SOURCE")
    row = materialize_target_request(request, invocation_cwd, repo_root)
    return build_resolved_target(request, row, console, "profiling", backend_spec(backend).cargo_features)


def _display_target(row: TargetRow) -> str:
    """Return the operational label for one target build."""

    if row.label:
        return row.label
    if row.git_ref != "HEAD":
        return row.git_ref
    return f"{Path(row.path).name}@{row.git_sha[:12]}"


def workload_command(
    binary_path: Path,
    file_spec: FileSpec,
    backend: Backend,
    treatment: Treatment,
) -> list[str]:
    return [
        str(binary_path),
        "--mode",
        "no-messages",
        "-j",
        "1",
        *(["--fact-directory", str(file_spec.fact_directory)] if file_spec.fact_directory is not None else []),
        *backend_flags(backend),
        *treatment_flags(treatment),
        str(file_spec.absolute_path),
    ]
