"""Parse, materialize, build, describe, and construct commands for targets.

This module owns treatment-specific workload command construction. Subprocess
measurement and report persistence belong in their dedicated modules.
"""

from __future__ import annotations

import hashlib
import os
import re
import signal
import subprocess
import sys
import time
from collections.abc import Sequence
from dataclasses import replace
from pathlib import Path
from typing import Literal

from rich.console import Console
from rich.text import Text

from process_guard import MemoryGuard, ResourceStopped, terminate_process_group

from .engines import TREATMENT_SPECS, Engine, Treatment, validate_engine_workload
from .models import EngineBinary, FileSpec, ResolvedTarget, TargetRequest, TargetRow
from .processes import COLLECTION_DEADLINE, BudgetExpired

BuildProfile = Literal["release", "profiling"]


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


def run_text(args: Sequence[str], cwd: Path, *, capture_output: bool = True) -> str:
    """Run target setup, bounding its whole process group when nightly is active."""

    deadline = COLLECTION_DEADLINE.get()
    if deadline is None:
        completed = subprocess.run(
            list(args),
            cwd=cwd,
            check=True,
            text=True,
            stdout=subprocess.PIPE if capture_output else sys.stderr,
            stderr=subprocess.PIPE if capture_output else sys.stderr,
        )
        return completed.stdout.strip() if capture_output else ""
    remaining = deadline - time.monotonic()
    if remaining <= 0:
        raise BudgetExpired("nightly collection budget exhausted before target setup")
    process = subprocess.Popen(
        list(args),
        cwd=cwd,
        text=True,
        stdout=subprocess.PIPE if capture_output else sys.stderr,
        stderr=subprocess.PIPE if capture_output else sys.stderr,
        start_new_session=True,
    )
    try:
        stdout, stderr = process.communicate(timeout=max(0, deadline - time.monotonic()))
    except subprocess.TimeoutExpired as error:
        raise BudgetExpired("nightly collection budget exhausted during target setup") from error
    finally:
        terminate_process_group(process)
    if process.returncode:
        raise subprocess.CalledProcessError(process.returncode, list(args), output=stdout, stderr=stderr)
    return stdout.strip() if stdout is not None else ""


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
    run_text(
        ["git", "worktree", "add", "--detach", str(path), sha],
        cwd=repo,
        capture_output=False,
    )
    return (path, sha)


def fetch_pr_ref(repo: Path, number: int) -> str:
    ref = f"refs/remotes/origin/pr/{number}"
    run_text(
        ["git", "fetch", "origin", f"+refs/pull/{number}/head:{ref}"],
        cwd=repo,
        capture_output=False,
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
    engine: Engine = "egglog",
) -> tuple[Path, str]:
    checkout_path = Path(row.path)
    engine_label = "" if engine == "egglog" else f" · {engine}"
    console.print(Text.assemble(("Building", "bold"), " ", _display_target(row), engine_label))
    package = {"egglog": "egglog-experimental", "egg": "egg-math-benchmark"}.get(engine)
    target_dir = checkout_path / os.environ.get("CARGO_TARGET_DIR", "target")
    build_args = ["cargo", "build"]
    if build_profile == "release":
        build_args.append("--release")
    else:
        build_args.extend(("--profile", build_profile))
    if package is None:
        native = checkout_path / "benchmarks/disequality/native"
        target_dir = checkout_path / "benchmarks/local/parameter-native/target"
        build_args.extend(
            (
                "--locked",
                "--manifest-path",
                str(native / "Cargo.toml"),
                "--target-dir",
                str(target_dir),
                "--bin",
                engine,
            )
        )
    else:
        build_args.extend(("-p", package))
    deadline = COLLECTION_DEADLINE.get()
    if deadline is not None and time.monotonic() >= deadline:
        raise BudgetExpired("nightly collection budget exhausted before build")
    if os.environ.get("EGGLOG_BENCH_MEMORY_GUARD") == "1" or deadline is not None:
        guard = MemoryGuard.from_environment()
        if guard is not None:
            build_args.extend(("--jobs", "1"))
        process = subprocess.Popen(
            build_args, cwd=checkout_path, stdout=sys.stderr, stderr=sys.stderr, start_new_session=True
        )
        timed_out = False
        try:
            if guard is not None:
                guard.start(process.pid)
            return_code = process.wait(timeout=None if deadline is None else max(0, deadline - time.monotonic()))
        except subprocess.TimeoutExpired:
            timed_out = True
        finally:
            try:
                if guard is not None:
                    guard.close()
            finally:
                terminate_process_group(process)
        if guard is not None and guard.reason is not None:
            raise ResourceStopped(f"resource guard stopped build: {guard.reason}")
        if timed_out:
            raise BudgetExpired("nightly collection budget exhausted during build")
        if guard is not None and return_code == -signal.SIGKILL:
            raise ResourceStopped("resource guard halted collection after build SIGKILL (cause unknown)")
        if return_code != 0:
            raise subprocess.CalledProcessError(return_code, build_args)
    else:
        subprocess.run(build_args, cwd=checkout_path, check=True, stdout=sys.stderr, stderr=sys.stderr)
    binary_stem = package or engine
    binary_name = f"{binary_stem}.exe" if os.name == "nt" else binary_stem
    binary_path = target_dir / build_profile / binary_name
    if not binary_path.is_file():
        raise FileNotFoundError(f"{build_profile} binary was not produced: {binary_path}")
    binary_sha256 = sha256_file(binary_path)
    return (binary_path, binary_sha256)


def build_resolved_target(
    request: TargetRequest,
    row: TargetRow,
    console: Console,
    build_profile: BuildProfile,
    engines: Sequence[Engine] = ("egglog",),
) -> ResolvedTarget:
    required_engines = tuple(dict.fromkeys(engines))
    if not required_engines:
        raise ValueError("target build requires at least one engine")
    binaries = tuple(
        EngineBinary(engine, binary_sha256, binary_path)
        for engine in required_engines
        for binary_path, binary_sha256 in (build_target(row, console, build_profile, engine),)
    )
    primary = binaries[0]
    row = replace(row, is_dirty=git_dirty(Path(row.path)))
    return ResolvedTarget(
        request=request,
        row=row,
        binary_sha256=primary.sha256,
        binary_path=primary.path,
        engine_binaries=binaries,
        primary_engine=primary.engine,
    )


def resolve_profile_target(
    request: TargetRequest,
    treatment: Treatment,
    invocation_cwd: Path,
    repo_root: Path,
    console: Console,
) -> ResolvedTarget:
    if request.is_label_lookup:
        raise ValueError("profile mode does not support cache-only label= targets; use label=SOURCE")
    row = materialize_target_request(request, invocation_cwd, repo_root)
    return build_resolved_target(
        request,
        row,
        console,
        "profiling",
        (TREATMENT_SPECS[treatment].engine,),
    )


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
    treatment: Treatment,
    disequality_encoding: str = "nee",
) -> list[str]:
    specification = TREATMENT_SPECS[treatment]
    file_spec = file_spec.for_engine(specification.engine)
    if specification.engine != "egglog":
        if disequality_encoding != "nee":
            raise ValueError("disequality encoding selection is only supported by egglog treatments")
        validate_engine_workload(file_spec, treatment)
        if specification.engine != "egg":
            return [str(binary_path), str(file_spec.absolute_path), "100000", "10000"]
        return [str(binary_path), *specification.flags]
    return [
        str(binary_path),
        "--mode",
        "no-messages",
        "-j",
        "1",
        *(["--disequality-encoding", disequality_encoding] if disequality_encoding != "nee" else []),
        *(["--fact-directory", str(file_spec.fact_directory)] if file_spec.fact_directory is not None else []),
        *specification.flags,
        str(file_spec.absolute_path),
    ]
