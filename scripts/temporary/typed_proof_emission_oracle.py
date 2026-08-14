#!/usr/bin/env python3
"""Temporary exact-output oracle for the typed proof-emission migration.

This script deliberately invokes the real egglog-experimental frontends. It does
not duplicate proof generation or source transformation in Python. The default
sample is discovered from Git-tracked deterministic proof-testing snapshots; it
is intentionally not an exhaustive proof-support classification.
Standalone replay is intentionally not claimed: proof-testing desugar artifacts
need the original source proof-checking program installed through the Rust API.

Exit codes:
    0: exact parity
    1: baseline/candidate parity difference
    2: invocation, binary, hash, or fixture configuration error
    3: baseline/oracle execution error or baseline nondeterminism
    4: a bounded subprocess timed out
    5: optional current-worktree ``make proof-tests`` failed
"""

from __future__ import annotations

import argparse
import contextlib
import hashlib
import itertools
import json
import math
import os
import re
import shutil
import signal
import subprocess
import sys
import tempfile
from collections import deque
from collections.abc import Sequence
from dataclasses import dataclass
from enum import IntEnum
from pathlib import Path
from typing import cast

BASELINE_BINARY = Path("/tmp/egglog-typed-emission-base-target/release/egglog-experimental")
BASELINE_SHA256 = "2b5974385231069c8bac1f9067e946f24c48fd33cb81be4c3cccde0fe238d200"
BASELINE_SOURCE_SHA = "ffb8ae435bd6421077b1c15826f32a6aeecf5b1b"
BASELINE_VERSION = "egglog 2.0.0_2026-08-14_ffb8ae4"
DEFAULT_ARTIFACT_PARENT = Path("/tmp/egglog-typed-proof-emission-oracle")
ARTIFACT_MARKER = ".typed-proof-emission-oracle"
ARTIFACT_LOCK = ".typed-proof-emission-oracle.lock"
SNAPSHOT_PREFIX = "files__proofs__"
SNAPSHOT_SUFFIX = "_proof_testing.snap"
SHA256_RE = re.compile(r"[0-9a-f]{64}")
INCLUDE_RE = re.compile(r'\(\s*include\s+"((?:\\.|[^"\\])*)"\s*\)')
INPUT_RE = re.compile(r'\(\s*input\s+[^\s()]+\s+"((?:\\.|[^"\\])*)"\s*\)')
INCLUDE_HEAD_RE = re.compile(r"\(\s*include(?:\s|\))")
INPUT_HEAD_RE = re.compile(r"\(\s*input(?:\s|\))")
OUTPUT_HEAD_RE = re.compile(r"\(\s*output(?:\s|\))")


class ExitCode(IntEnum):
    EXACT_PARITY = 0
    PARITY_DIFFERENCE = 1
    CONFIGURATION_ERROR = 2
    ORACLE_ERROR = 3
    TIMEOUT = 4
    PROOF_CORPUS_FAILURE = 5


@dataclass(frozen=True)
class BinaryIdentity:
    label: str
    path: Path
    sha256: str
    version: str
    source_sha: str | None


@dataclass(frozen=True)
class ProcessResult:
    command: tuple[str, ...]
    cwd: Path
    returncode: int
    timed_out: bool
    stdout_path: Path
    stderr_path: Path


@dataclass(frozen=True)
class StreamDifference:
    byte_offset: int
    line: int
    byte_column: int
    expected_line: str | None
    actual_line: str | None
    previous_equal_lines: tuple[str, ...]
    expected_following_lines: tuple[str, ...]
    actual_following_lines: tuple[str, ...]


@dataclass(frozen=True)
class Stage:
    name: str
    treatment: str
    mode: str
    flag: str


DESUGAR_STAGE = Stage(
    name="desugar",
    treatment="proofs",
    mode="desugar",
    flag="--proofs",
)
PROOF_TESTING_DESUGAR_STAGE = Stage(
    name="proof-testing-desugar",
    treatment="proof-testing",
    mode="desugar",
    flag="--proof-testing",
)
EXECUTION_STAGE = Stage(
    name="execution",
    treatment="proof-testing",
    mode="normal",
    flag="--proof-testing",
)


class OracleConfigurationError(Exception):
    """The oracle cannot make a trustworthy comparison with this invocation."""


def sha256_file(path: Path) -> str:
    """Hash a file without loading a possibly large executable or output into memory."""
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        while chunk := handle.read(1024 * 1024):
            digest.update(chunk)
    return digest.hexdigest()


def sha256_directory(path: Path) -> str:
    """Hash a fact directory's stable relative structure and file contents."""
    digest = hashlib.sha256()
    for entry in sorted(path.rglob("*"), key=lambda item: item.relative_to(path).as_posix()):
        relative = entry.relative_to(path).as_posix().encode()
        if entry.is_symlink():
            digest.update(b"L\0" + relative + b"\0" + os.readlink(entry).encode() + b"\0")
        elif entry.is_dir():
            digest.update(b"D\0" + relative + b"\0")
        elif entry.is_file():
            digest.update(b"F\0" + relative + b"\0")
            with entry.open("rb") as handle:
                while chunk := handle.read(1024 * 1024):
                    digest.update(chunk)
            digest.update(b"\0")
        else:
            raise OracleConfigurationError(f"unsupported fact-directory entry: {entry}")
    return digest.hexdigest()


def fixture_input_identity(repo_root: Path, fixture: Path) -> dict[str, object]:
    """Pin one fixture and the same-stem fact directory used by the file harness."""
    fact_directory = fixture.with_suffix("")
    identity: dict[str, object] = {
        "path": fixture.relative_to(repo_root).as_posix(),
        "sha256": sha256_file(fixture),
    }
    if fact_directory.is_dir():
        identity["fact_directory"] = {
            "path": fact_directory.relative_to(repo_root).as_posix(),
            "sha256": sha256_directory(fact_directory),
        }
    return identity


def test_tree_identities(repo_root: Path) -> list[dict[str, object]]:
    """Pin the complete test trees that own includes and non-same-stem inputs."""
    return [
        {
            "path": f"{crate}/tests",
            "sha256": sha256_directory(repo_root / crate / "tests"),
        }
        for crate in ("egglog", "egglog-experimental")
    ]


def fixture_manifest_sha256(
    fixtures: Sequence[dict[str, object]],
    test_trees: Sequence[dict[str, object]],
    *,
    stages: Sequence[Stage],
    run_proof_tests: bool,
) -> str:
    """Identify the exact selected inputs and parity stages for deterministic artifact paths."""
    payload = {
        "schema": "temporary-typed-proof-emission-oracle-v1",
        "fixtures": list(fixtures),
        "test_trees": list(test_trees),
        "stages": [
            {"name": stage.name, "treatment": stage.treatment, "mode": stage.mode, "flag": stage.flag}
            for stage in stages
        ],
        "run_proof_tests": run_proof_tests,
    }
    return hashlib.sha256(json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def stable_environment() -> dict[str, str]:
    """Return a deterministic subprocess environment without output sidecars."""
    environment = os.environ.copy()
    environment.update({"LANG": "C", "LC_ALL": "C", "RUST_LOG": "warn", "TZ": "UTC"})
    environment.pop("EGGLOG_GENERATED_FRONTEND_SIDECAR", None)
    return environment


def terminate_process_group(process: subprocess.Popen[bytes]) -> None:
    """Stop a timed-out command and any children it may have started."""
    with contextlib.suppress(ProcessLookupError):
        os.killpg(process.pid, signal.SIGKILL)
    process.wait()


def run_process(
    command: Sequence[str],
    *,
    cwd: Path,
    stdout_path: Path,
    stderr_path: Path,
    timeout_seconds: float,
    environment: dict[str, str],
) -> ProcessResult:
    """Run one bounded command and preserve its exact output streams in artifacts."""
    stdout_path.parent.mkdir(parents=True, exist_ok=True)
    with stdout_path.open("wb") as stdout, stderr_path.open("wb") as stderr:
        try:
            process = subprocess.Popen(
                list(command),
                cwd=cwd,
                env=environment,
                stdin=subprocess.DEVNULL,
                stdout=stdout,
                stderr=stderr,
                start_new_session=True,
            )
        except OSError as error:
            stderr.write(f"failed to start command: {error}\n".encode())
            return ProcessResult(tuple(command), cwd, 127, False, stdout_path, stderr_path)

        timed_out = False
        try:
            process.wait(timeout=timeout_seconds)
        except subprocess.TimeoutExpired:
            timed_out = True
            terminate_process_group(process)
        except BaseException:
            if process.poll() is None:
                terminate_process_group(process)
            raise

    return ProcessResult(
        command=tuple(command),
        cwd=cwd,
        returncode=process.returncode,
        timed_out=timed_out,
        stdout_path=stdout_path,
        stderr_path=stderr_path,
    )


def capture_version(binary: Path) -> str:
    """Require a healthy CLI metadata response in addition to the byte hash."""
    try:
        completed = subprocess.run(
            [str(binary), "--version"],
            check=False,
            capture_output=True,
            timeout=10,
            env=stable_environment(),
        )
    except (OSError, subprocess.TimeoutExpired) as error:
        raise OracleConfigurationError(f"cannot query {binary} --version: {error}") from error
    if completed.returncode != 0 or completed.stderr:
        raise OracleConfigurationError(
            f"{binary} --version failed: returncode={completed.returncode}, stderr={completed.stderr!r}"
        )
    try:
        return completed.stdout.decode("utf-8").strip()
    except UnicodeDecodeError as error:
        raise OracleConfigurationError(f"{binary} --version did not emit UTF-8") from error


def validate_binary(
    path: Path,
    *,
    label: str,
    expected_sha256: str,
    source_sha: str | None,
    expected_version: str | None = None,
) -> BinaryIdentity:
    """Resolve and validate one executable against its caller-supplied identity."""
    try:
        resolved = path.expanduser().resolve(strict=True)
    except OSError as error:
        raise OracleConfigurationError(f"{label} binary does not resolve: {path}: {error}") from error
    if not resolved.is_file() or not os.access(resolved, os.X_OK):
        raise OracleConfigurationError(f"{label} binary is not an executable regular file: {resolved}")

    actual_sha256 = sha256_file(resolved)
    if actual_sha256 != expected_sha256:
        raise OracleConfigurationError(
            f"{label} SHA-256 mismatch: expected {expected_sha256}, observed {actual_sha256} at {resolved}"
        )
    version = capture_version(resolved)
    if expected_version is not None and version != expected_version:
        raise OracleConfigurationError(f"{label} version mismatch: expected {expected_version!r}, observed {version!r}")
    return BinaryIdentity(label, resolved, actual_sha256, version, source_sha)


def normalize_fixture_stem(path: Path) -> str:
    """Mirror the file harness's stable fixture-name normalization."""
    return path.stem.replace(".", "_").replace("-", "_").replace(" ", "_")


def git_tracked_files(repo_root: Path, directory: Path) -> set[Path]:
    """Freeze discovery to files that are part of repository history."""
    relative = directory.relative_to(repo_root)
    output = subprocess.run(
        ["git", "ls-files", "-z", "--", relative.as_posix()],
        cwd=repo_root,
        check=True,
        stdout=subprocess.PIPE,
    ).stdout
    return {(repo_root / item.decode()).resolve() for item in output.split(b"\0") if item}


def discover_crate_snapshot_corpus(repo_root: Path, crate: str) -> list[Path]:
    """Resolve one crate's deterministic proof snapshots back to its fixtures."""
    tests_root = repo_root / crate / "tests"
    tracked_tests = git_tracked_files(repo_root, tests_root)
    fixture_by_name: dict[str, Path] = {}
    for fixture in sorted(tests_root.rglob("*.egg")):
        if fixture.resolve() not in tracked_tests:
            continue
        if "header" in fixture.relative_to(tests_root).parts:
            continue
        name = normalize_fixture_stem(fixture)
        previous = fixture_by_name.get(name)
        if previous is not None:
            raise OracleConfigurationError(
                f"ambiguous normalized fixture name {name!r}: {previous.relative_to(repo_root)} and "
                f"{fixture.relative_to(repo_root)}"
            )
        fixture_by_name[name] = fixture

    snapshot_dir = tests_root / "snapshots"
    snapshots = sorted(
        snapshot
        for snapshot in snapshot_dir.glob(f"{SNAPSHOT_PREFIX}*{SNAPSHOT_SUFFIX}")
        if snapshot.resolve() in tracked_tests
    )
    if not snapshots:
        raise OracleConfigurationError(f"no deterministic proof snapshots found under {snapshot_dir}")

    fixtures: list[Path] = []
    for snapshot in snapshots:
        name = snapshot.name.removeprefix(SNAPSHOT_PREFIX).removesuffix(SNAPSHOT_SUFFIX)
        matched_fixture = fixture_by_name.get(name)
        if matched_fixture is None:
            raise OracleConfigurationError(
                f"proof snapshot {snapshot.relative_to(repo_root)} has no matching .egg fixture"
            )
        fixtures.append(matched_fixture)
    return sorted(fixtures, key=lambda path: path.relative_to(repo_root).as_posix())


def discover_snapshot_corpus(repo_root: Path, crates: Sequence[str]) -> list[Path]:
    """Combine deterministic proof-output corpora without hard-coding fixture names."""
    fixtures = list(itertools.chain.from_iterable(discover_crate_snapshot_corpus(repo_root, crate) for crate in crates))
    return sorted(fixtures, key=lambda path: path.relative_to(repo_root).as_posix())


def discover_explicit_proof_corpus(repo_root: Path) -> list[Path]:
    """Discover both crates' compact fixtures that explicitly require proof mode."""
    proof_roots = [repo_root / crate / "tests" / "proofs" for crate in ("egglog", "egglog-experimental")]
    tracked_tests: set[Path] = set()
    for crate in ("egglog", "egglog-experimental"):
        tracked_tests.update(git_tracked_files(repo_root, repo_root / crate / "tests"))
    fixtures = sorted(
        (
            fixture
            for fixture in itertools.chain.from_iterable(proof_root.rglob("*.egg") for proof_root in proof_roots)
            if fixture.resolve() in tracked_tests
        ),
        key=lambda path: path.relative_to(repo_root).as_posix(),
    )
    if not fixtures:
        raise OracleConfigurationError(f"no explicit proof fixtures found under {proof_roots}")
    return fixtures


def resolve_explicit_fixtures(repo_root: Path, values: Sequence[str]) -> list[Path]:
    """Validate user-selected fixtures while retaining deterministic repository paths."""
    tests_roots = tuple((repo_root / crate / "tests").resolve() for crate in ("egglog", "egglog-experimental"))
    fixtures: list[Path] = []
    for value in values:
        candidate = Path(value)
        if not candidate.is_absolute():
            candidate = repo_root / candidate
        try:
            fixture = candidate.resolve(strict=True)
        except OSError as error:
            raise OracleConfigurationError(f"fixture does not resolve: {value}: {error}") from error
        in_tests = any(fixture.is_relative_to(tests_root) for tests_root in tests_roots)
        if fixture.suffix != ".egg" or not fixture.is_file() or not in_tests:
            raise OracleConfigurationError(f"fixture must be an .egg file under one of {tests_roots}: {fixture}")
        fixtures.append(fixture)
    unique = sorted(set(fixtures), key=lambda path: path.relative_to(repo_root).as_posix())
    if not unique:
        raise OracleConfigurationError("at least one explicit fixture is required")
    return unique


def artifact_slug(repo_root: Path, fixture: Path, index: int) -> str:
    """Create a collision-resistant stable artifact directory name."""
    relative = fixture.relative_to(repo_root).with_suffix("").as_posix()
    slug = re.sub(r"[^A-Za-z0-9._-]+", "__", relative)
    return f"{index:04d}-{slug}"


def display_bytes(line: bytes | None, *, limit: int = 500) -> str | None:
    """Render one exact-output context line safely and with a bounded report size."""
    if line is None:
        return None
    text = line.decode("utf-8", errors="backslashreplace")
    if len(text) > limit:
        return f"{text[:limit]}... <{len(text) - limit} characters omitted>"
    return text


def first_stream_difference(expected: Path, actual: Path) -> StreamDifference | None:
    """Locate the first differing byte and retain a small line-oriented witness."""
    previous: deque[bytes] = deque(maxlen=2)
    byte_offset = 0
    with expected.open("rb") as expected_file, actual.open("rb") as actual_file:
        pairs = itertools.zip_longest(expected_file, actual_file)
        for line_number, (expected_line, actual_line) in enumerate(pairs, start=1):
            if expected_line == actual_line:
                if expected_line is not None:
                    previous.append(expected_line)
                    byte_offset += len(expected_line)
                continue

            expected_bytes = expected_line or b""
            actual_bytes = actual_line or b""
            local_offset = 0
            for expected_byte, actual_byte in zip(expected_bytes, actual_bytes, strict=False):
                if expected_byte != actual_byte:
                    break
                local_offset += 1

            expected_following = tuple(display_bytes(expected_file.readline()) for _ in range(2))
            actual_following = tuple(display_bytes(actual_file.readline()) for _ in range(2))
            return StreamDifference(
                byte_offset=byte_offset + local_offset,
                line=line_number,
                byte_column=local_offset + 1,
                expected_line=display_bytes(expected_line),
                actual_line=display_bytes(actual_line),
                previous_equal_lines=tuple(display_bytes(line) or "" for line in previous),
                expected_following_lines=tuple(line for line in expected_following if line),
                actual_following_lines=tuple(line for line in actual_following if line),
            )
    return None


def stream_summary(path: Path) -> dict[str, object]:
    """Record enough provenance to verify a preserved exact stream."""
    return {"path": str(path), "bytes": path.stat().st_size, "sha256": sha256_file(path)}


def process_summary(result: ProcessResult) -> dict[str, object]:
    """Serialize one bounded invocation and its exact stream identities."""
    return {
        "command": list(result.command),
        "cwd": str(result.cwd),
        "returncode": result.returncode,
        "timed_out": result.timed_out,
        "stdout": stream_summary(result.stdout_path),
        "stderr": stream_summary(result.stderr_path),
    }


def difference_summary(
    *,
    kind: str,
    stage: Stage,
    fixture: Path,
    expected: ProcessResult,
    actual: ProcessResult,
    stream: str | None = None,
    difference: StreamDifference | None = None,
) -> dict[str, object]:
    """Build a precise, machine-readable first-difference witness."""
    summary: dict[str, object] = {
        "kind": kind,
        "stage": stage.name,
        "treatment": stage.treatment,
        "mode": stage.mode,
        "fixture": str(fixture),
        "expected_label": "baseline",
        "actual_label": "candidate",
        "expected_returncode": expected.returncode,
        "actual_returncode": actual.returncode,
        "expected_timed_out": expected.timed_out,
        "actual_timed_out": actual.timed_out,
    }
    if stream is not None:
        summary["stream"] = stream
    if difference is not None:
        summary["first_byte_offset_zero_based"] = difference.byte_offset
        summary["first_line_one_based"] = difference.line
        summary["first_byte_column_one_based"] = difference.byte_column
        summary["expected_line"] = difference.expected_line
        summary["actual_line"] = difference.actual_line
        summary["previous_equal_lines"] = list(difference.previous_equal_lines)
        summary["expected_following_lines"] = list(difference.expected_following_lines)
        summary["actual_following_lines"] = list(difference.actual_following_lines)
    return summary


def command_for_stage(
    binary: BinaryIdentity, stage: Stage, fixture_argument: Path, fact_directory: Path | None
) -> list[str]:
    """Own the exact CLI treatment/mode contract being compared."""
    command = [
        str(binary.path),
        "--threads",
        "1",
        stage.flag,
        "--mode",
        stage.mode,
    ]
    if fact_directory is not None:
        command.extend(["--fact-directory", str(fact_directory)])
    command.append(str(fixture_argument))
    return command


def compare_stage(
    *,
    stage: Stage,
    fixture: Path,
    baseline: BinaryIdentity,
    candidate: BinaryIdentity,
    baseline_cwd: Path,
    baseline_repeat_cwd: Path,
    candidate_cwd: Path,
    baseline_fixture_argument: Path,
    baseline_repeat_fixture_argument: Path,
    candidate_fixture_argument: Path,
    baseline_fact_directory: Path | None,
    baseline_repeat_fact_directory: Path | None,
    candidate_fact_directory: Path | None,
    artifact_dir: Path,
    timeout_seconds: float,
    environment: dict[str, str],
) -> tuple[dict[str, object], ExitCode | None, dict[str, object] | None]:
    """Require a deterministic baseline and compare the candidate byte-for-byte."""
    variants = (
        (
            "baseline",
            baseline,
            baseline_cwd,
            baseline_fixture_argument,
            baseline_fact_directory,
        ),
        (
            "baseline-repeat",
            baseline,
            baseline_repeat_cwd,
            baseline_repeat_fixture_argument,
            baseline_repeat_fact_directory,
        ),
        (
            "candidate",
            candidate,
            candidate_cwd,
            candidate_fixture_argument,
            candidate_fact_directory,
        ),
    )
    results: dict[str, ProcessResult] = {}
    for variant, binary, cwd, fixture_argument, fact_directory in variants:
        command = command_for_stage(binary, stage, fixture_argument, fact_directory)
        results[variant] = run_process(
            command,
            cwd=cwd,
            stdout_path=artifact_dir / f"{variant}.stdout",
            stderr_path=artifact_dir / f"{variant}.stderr",
            timeout_seconds=timeout_seconds,
            environment=environment,
        )

    baseline_result = results["baseline"]
    baseline_repeat = results["baseline-repeat"]
    candidate_result = results["candidate"]
    summary: dict[str, object] = {
        "stage": stage.name,
        "treatment": stage.treatment,
        "mode": stage.mode,
        "baseline": process_summary(baseline_result),
        "baseline_repeat": process_summary(baseline_repeat),
        "candidate": process_summary(candidate_result),
    }

    if baseline_result.timed_out or baseline_repeat.timed_out:
        failure = difference_summary(
            kind="baseline-timeout",
            stage=stage,
            fixture=fixture,
            expected=baseline_result,
            actual=baseline_repeat,
        )
        failure["actual_label"] = "baseline-repeat"
        return summary, ExitCode.TIMEOUT, failure
    if baseline_result.returncode != 0 or baseline_repeat.returncode != 0:
        failure = difference_summary(
            kind="baseline-execution-error",
            stage=stage,
            fixture=fixture,
            expected=baseline_result,
            actual=baseline_repeat,
        )
        failure["actual_label"] = "baseline-repeat"
        return summary, ExitCode.ORACLE_ERROR, failure

    for stream in ("stdout", "stderr"):
        expected_path = getattr(baseline_result, f"{stream}_path")
        repeated_path = getattr(baseline_repeat, f"{stream}_path")
        difference = first_stream_difference(expected_path, repeated_path)
        if difference is not None:
            failure = difference_summary(
                kind="baseline-nondeterminism",
                stage=stage,
                fixture=fixture,
                expected=baseline_result,
                actual=baseline_repeat,
                stream=stream,
                difference=difference,
            )
            failure["actual_label"] = "baseline-repeat"
            return summary, ExitCode.ORACLE_ERROR, failure

    if candidate_result.timed_out:
        failure = difference_summary(
            kind="candidate-timeout",
            stage=stage,
            fixture=fixture,
            expected=baseline_result,
            actual=candidate_result,
        )
        return summary, ExitCode.TIMEOUT, failure
    if candidate_result.returncode != baseline_result.returncode:
        return_code_failure: dict[str, object] | None = None
        for stream in ("stderr", "stdout"):
            expected_path = getattr(baseline_result, f"{stream}_path")
            actual_path = getattr(candidate_result, f"{stream}_path")
            difference = first_stream_difference(expected_path, actual_path)
            if difference is not None:
                return_code_failure = difference_summary(
                    kind="return-code",
                    stage=stage,
                    fixture=fixture,
                    expected=baseline_result,
                    actual=candidate_result,
                    stream=stream,
                    difference=difference,
                )
                break
        if return_code_failure is None:
            return_code_failure = difference_summary(
                kind="return-code",
                stage=stage,
                fixture=fixture,
                expected=baseline_result,
                actual=candidate_result,
            )
        return summary, ExitCode.PARITY_DIFFERENCE, return_code_failure

    for stream in ("stdout", "stderr"):
        expected_path = getattr(baseline_result, f"{stream}_path")
        actual_path = getattr(candidate_result, f"{stream}_path")
        difference = first_stream_difference(expected_path, actual_path)
        if difference is not None:
            failure = difference_summary(
                kind="exact-output",
                stage=stage,
                fixture=fixture,
                expected=baseline_result,
                actual=candidate_result,
                stream=stream,
                difference=difference,
            )
            return summary, ExitCode.PARITY_DIFFERENCE, failure

    return summary, None, None


def remove_controlled_directory(path: Path, artifact_root: Path) -> None:
    """Clear only a named oracle-owned subtree under the validated artifact root."""
    resolved_root = artifact_root.resolve()
    resolved_path = path.resolve()
    if resolved_path == resolved_root or not resolved_path.is_relative_to(resolved_root):
        raise OracleConfigurationError(f"refusing to clear non-child artifact path: {resolved_path}")
    if path.is_symlink():
        path.unlink()
        return
    if resolved_path.exists():
        shutil.rmtree(resolved_path)


def decode_egg_path(raw: str, fixture: Path) -> str:
    """Decode the quoted path subset used by repository include/input/output commands."""
    try:
        decoded = json.loads(f'"{raw}"')
    except json.JSONDecodeError as error:
        raise OracleConfigurationError(f"cannot decode dependency path in {fixture}: {raw!r}") from error
    if not isinstance(decoded, str):
        raise OracleConfigurationError(f"dependency path is not a string in {fixture}: {raw!r}")
    return decoded


def strip_egglog_line_comments(program: str) -> str:
    """Remove semicolon comments while preserving semicolons and escapes inside strings."""
    stripped: list[str] = []
    in_string = False
    escaped = False
    in_comment = False
    for character in program:
        if in_comment:
            if character == "\n":
                stripped.append(character)
                in_comment = False
            continue
        if in_string:
            stripped.append(character)
            if escaped:
                escaped = False
            elif character == "\\":
                escaped = True
            elif character == '"':
                in_string = False
            continue
        if character == '"':
            stripped.append(character)
            in_string = True
        elif character == ";":
            in_comment = True
        else:
            stripped.append(character)
    return "".join(stripped)


def resolve_test_dependency(
    *,
    repo_root: Path,
    fixture: Path,
    raw_path: str,
    fact_directory: Path | None,
    use_fact_directory: bool,
    must_exist: bool,
) -> Path:
    """Resolve a fixture dependency and reject paths that escape its crate test tree."""
    crate = fixture_crate(repo_root, fixture)
    crate_root = repo_root / crate
    tests_root = (crate_root / "tests").resolve()
    decoded = decode_egg_path(raw_path, fixture)
    dependency = Path(decoded)
    if not dependency.is_absolute():
        base = fact_directory if use_fact_directory and fact_directory is not None else crate_root
        dependency = base / dependency
    resolved = dependency.resolve()
    if not resolved.is_relative_to(tests_root):
        raise OracleConfigurationError(
            f"execution dependency escapes {tests_root}: {raw_path!r} in {fixture.relative_to(repo_root)}"
        )
    if must_exist and not resolved.exists():
        raise OracleConfigurationError(
            f"execution dependency does not exist: {raw_path!r} in {fixture.relative_to(repo_root)}"
        )
    return resolved


def fixture_execution_dependencies(repo_root: Path, fixture: Path) -> list[Path]:
    """Discover selected fixture files, recursive includes, and external input blobs."""
    fact_directory = fixture.with_suffix("")
    active_fact_directory = fact_directory if fact_directory.is_dir() else None
    dependencies: set[Path] = {fixture}
    if active_fact_directory is not None:
        dependencies.update(path for path in active_fact_directory.rglob("*") if path.is_file())

    pending = [fixture]
    scanned: set[Path] = set()
    while pending:
        source = pending.pop()
        if source in scanned:
            continue
        scanned.add(source)
        program = strip_egglog_line_comments(source.read_text(encoding="utf-8"))
        includes = INCLUDE_RE.findall(program)
        inputs = INPUT_RE.findall(program)
        if len(INCLUDE_HEAD_RE.findall(program)) != len(includes):
            raise OracleConfigurationError(
                f"cannot safely resolve every include command in {source.relative_to(repo_root)}; "
                "remove comments between the command head and path or omit this fixture"
            )
        if len(INPUT_HEAD_RE.findall(program)) != len(inputs):
            raise OracleConfigurationError(
                f"cannot safely resolve every input command in {source.relative_to(repo_root)}; "
                "remove comments between command fields or omit this fixture"
            )
        if OUTPUT_HEAD_RE.search(program) is not None:
            raise OracleConfigurationError(
                f"execution/output isolation is not implemented for output commands in "
                f"{source.relative_to(repo_root)}; omit this fixture from the temporary oracle"
            )
        for raw_path in includes:
            included = resolve_test_dependency(
                repo_root=repo_root,
                fixture=fixture,
                raw_path=raw_path,
                fact_directory=active_fact_directory,
                use_fact_directory=False,
                must_exist=True,
            )
            if not included.is_file():
                raise OracleConfigurationError(f"include dependency is not a file: {included}")
            dependencies.add(included)
            pending.append(included)
        for raw_path in inputs:
            input_path = resolve_test_dependency(
                repo_root=repo_root,
                fixture=fixture,
                raw_path=raw_path,
                fact_directory=active_fact_directory,
                use_fact_directory=True,
                must_exist=True,
            )
            if not input_path.is_file():
                raise OracleConfigurationError(f"input dependency is not a file: {input_path}")
            dependencies.add(input_path)
    return sorted(dependencies, key=lambda path: path.relative_to(repo_root).as_posix())


def prepare_execution_sandboxes(
    artifact_root: Path,
    fixtures: Sequence[Path],
    repo_root: Path,
    dependencies: dict[Path, list[Path]],
) -> dict[tuple[Path, str], Path]:
    """Copy each fixture into three isolated trees without modifying included fixtures."""
    sandbox_root = artifact_root / "execution-sandboxes"
    remove_controlled_directory(sandbox_root, artifact_root)
    sandboxes: dict[tuple[Path, str], Path] = {}
    for index, fixture in enumerate(fixtures, start=1):
        fixture_root = sandbox_root / artifact_slug(repo_root, fixture, index)
        for variant in ("baseline", "baseline-repeat", "candidate"):
            variant_root = fixture_root / variant
            crate = fixture_crate(repo_root, fixture)
            crate_root = repo_root / crate
            for source in dependencies[fixture]:
                destination = variant_root / crate / source.relative_to(crate_root)
                destination.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(source, destination)
            relative_to_crate = fixture.relative_to(repo_root / crate)
            sandbox_fixture = variant_root / crate / relative_to_crate
            with sandbox_fixture.open("ab") as handle:
                handle.write(b"\n(print-size)\n")
            sandboxes[(fixture, variant)] = variant_root
    return sandboxes


def fixture_crate(repo_root: Path, fixture: Path) -> str:
    """Identify which crate owns a selected repository fixture."""
    for crate in ("egglog", "egglog-experimental"):
        if fixture.is_relative_to(repo_root / crate / "tests"):
            return crate
    raise OracleConfigurationError(f"fixture is outside the supported crate test trees: {fixture}")


def fixture_arguments(
    *,
    repo_root: Path,
    fixture: Path,
    stage: Stage,
    sandboxes: dict[tuple[Path, str], Path] | None,
) -> tuple[tuple[Path, Path, Path], tuple[Path | None, Path | None, Path | None], tuple[Path, Path, Path]]:
    """Map one source fixture into isolated stage-specific paths and working directories."""
    crate = fixture_crate(repo_root, fixture)
    relative_to_crate = fixture.relative_to(repo_root / crate)
    if stage.mode == "desugar":
        cwd = repo_root / crate
        fact_directory = relative_to_crate.with_suffix("")
        fact = fact_directory if (cwd / fact_directory).is_dir() else None
        return (relative_to_crate,) * 3, (fact,) * 3, (cwd,) * 3

    if sandboxes is None:
        raise OracleConfigurationError("execution parity requested without isolated sandboxes")
    arguments: list[Path] = []
    facts: list[Path | None] = []
    working_directories: list[Path] = []
    for variant in ("baseline", "baseline-repeat", "candidate"):
        cwd = sandboxes[(fixture, variant)] / crate
        fact_directory = relative_to_crate.with_suffix("")
        arguments.append(relative_to_crate)
        facts.append(fact_directory if (cwd / fact_directory).is_dir() else None)
        working_directories.append(cwd)
    return tuple(arguments), tuple(facts), tuple(working_directories)  # type: ignore[return-value]


def atomic_write_json(path: Path, value: object) -> None:
    """Atomically replace a report only after complete JSON serialization."""
    temporary = path.with_name(f".{path.name}.tmp")
    temporary.unlink(missing_ok=True)
    temporary.write_text(f"{json.dumps(value, indent=2, sort_keys=True)}\n", encoding="utf-8")
    temporary.replace(path)


def git_metadata(repo_root: Path) -> dict[str, object]:
    """Record the source checkout used for discovery and optional proof tests."""
    head = subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=repo_root,
        check=True,
        stdout=subprocess.PIPE,
        text=True,
    ).stdout.strip()
    status = subprocess.run(
        ["git", "status", "--porcelain"],
        cwd=repo_root,
        check=True,
        stdout=subprocess.PIPE,
        text=True,
    ).stdout
    tracked_status = subprocess.run(
        ["git", "status", "--porcelain", "--untracked-files=no"],
        cwd=repo_root,
        check=True,
        stdout=subprocess.PIPE,
        text=True,
    ).stdout
    short_head = subprocess.run(
        ["git", "rev-parse", "--short", "HEAD"],
        cwd=repo_root,
        check=True,
        stdout=subprocess.PIPE,
        text=True,
    ).stdout.strip()
    untracked_output = subprocess.run(
        ["git", "ls-files", "--others", "--exclude-standard", "-z"],
        cwd=repo_root,
        check=True,
        stdout=subprocess.PIPE,
    ).stdout
    untracked_files = sorted(item.decode() for item in untracked_output.split(b"\0") if item)
    return {
        "head": head,
        "short_head": short_head,
        "dirty": bool(status),
        "tracked_dirty": bool(tracked_status),
        "untracked_files": untracked_files,
    }


def validate_untracked_nonbuild_files(
    repo_root: Path,
    observed: Sequence[str],
    allowed_values: Sequence[str],
) -> list[dict[str, object]]:
    """Require every untracked file to be explicitly allowed and reject likely build inputs."""
    allowed: set[str] = set()
    for value in allowed_values:
        candidate = Path(value)
        if candidate.is_absolute():
            try:
                relative = candidate.resolve(strict=True).relative_to(repo_root)
            except (OSError, ValueError) as error:
                raise OracleConfigurationError(
                    f"allowed untracked file must resolve inside the repository: {value}"
                ) from error
        else:
            relative = candidate
        if relative.is_absolute() or ".." in relative.parts:
            raise OracleConfigurationError(f"allowed untracked file must be a repository-relative child: {value}")
        allowed.add(relative.as_posix())

    observed_set = set(observed)
    missing = sorted(allowed - observed_set)
    unapproved = sorted(observed_set - allowed)
    if missing:
        raise OracleConfigurationError(f"--allow-untracked-nonbuild-file names files that are not untracked: {missing}")
    if unapproved:
        raise OracleConfigurationError(
            "candidate certification found untracked files; commit them or explicitly allow "
            f"document-only files with --allow-untracked-nonbuild-file: {unapproved}"
        )

    identities: list[dict[str, object]] = []
    for relative_text in sorted(allowed):
        relative = Path(relative_text)
        path = (repo_root / relative).resolve(strict=True)
        if not path.is_relative_to(repo_root):
            raise OracleConfigurationError(f"allowed untracked file resolves outside the repository: {relative_text}")
        if not path.is_file():
            raise OracleConfigurationError(f"allowed untracked path is not a regular file: {relative_text}")
        if (
            path.suffix in {".rs", ".toml", ".lock"}
            or path.name == "build.rs"
            or "src" in relative.parts
            or ".cargo" in relative.parts
        ):
            raise OracleConfigurationError(
                f"refusing to certify likely build input as an allowed untracked file: {relative_text}"
            )
        identities.append(
            {
                "path": relative.as_posix(),
                "sha256": sha256_file(path),
            }
        )
    return identities


def run_proof_corpus_command(
    *,
    repo_root: Path,
    artifact_root: Path,
    timeout_seconds: float,
    environment: dict[str, str],
) -> tuple[dict[str, object], ExitCode | None]:
    """Run the locked equivalent of the repository proof gate with an external target."""
    command = ["cargo", "test", "--locked", "--workspace", "--test", "files", "proofs/"]
    proof_environment = environment.copy()
    proof_environment.update(
        {
            "CARGO_TARGET_DIR": str(artifact_root / "proof-tests-target"),
            "INSTA_UPDATE": "no",
        }
    )
    result = run_process(
        command,
        cwd=repo_root,
        stdout_path=artifact_root / "proof-tests.stdout",
        stderr_path=artifact_root / "proof-tests.stderr",
        timeout_seconds=timeout_seconds,
        environment=proof_environment,
    )
    summary = process_summary(result)
    summary["label"] = "current-worktree proof corpus"
    summary["treatment"] = "proof-testing"
    summary["mode"] = "locked equivalent of make proof-tests"
    summary["candidate_binary_note"] = (
        "This repository-owned command validates the current source worktree; it does not consume --candidate."
    )
    if result.timed_out:
        return summary, ExitCode.TIMEOUT
    if result.returncode != 0:
        return summary, ExitCode.PROOF_CORPUS_FAILURE
    return summary, None


def validate_artifact_root(path: Path, repo_root: Path) -> Path:
    """Ensure every generated artifact stays outside the source repository."""
    resolved = path.expanduser().resolve()
    if resolved == repo_root or resolved.is_relative_to(repo_root):
        raise OracleConfigurationError(f"artifact root must be outside the repository: {resolved}")
    artifact_parent = DEFAULT_ARTIFACT_PARENT.resolve()
    if resolved in {Path("/").resolve(), Path("/tmp").resolve(), artifact_parent}:
        raise OracleConfigurationError(f"artifact root is too broad for safe replacement: {resolved}")
    marker = resolved / ARTIFACT_MARKER
    if marker.is_symlink():
        raise OracleConfigurationError(f"artifact ownership marker must not be a symlink: {marker}")
    if resolved.exists() and any(resolved.iterdir()) and not marker.is_file():
        raise OracleConfigurationError(
            f"refusing to reuse a nonempty artifact directory not owned by this oracle: {resolved}"
        )
    resolved.mkdir(parents=True, exist_ok=True)
    marker.write_text("temporary typed proof-emission oracle artifacts\n", encoding="utf-8")
    return resolved


def acquire_artifact_lock(artifact_root: Path) -> Path:
    """Fail closed when another process is using the same deterministic artifact root."""
    lock_path = artifact_root / ARTIFACT_LOCK
    try:
        descriptor = os.open(lock_path, os.O_CREAT | os.O_EXCL | os.O_WRONLY, 0o600)
    except FileExistsError as error:
        owner = lock_path.read_text(encoding="utf-8", errors="replace").strip()
        raise OracleConfigurationError(
            f"artifact root is already locked by {owner or 'an unknown process'}: {lock_path}"
        ) from error
    with os.fdopen(descriptor, "w", encoding="utf-8") as handle:
        handle.write(f"pid={os.getpid()}\n")
    return lock_path


def self_test() -> None:
    """Exercise exact-byte difference reporting and deterministic corpus discovery."""
    repo_root = Path(__file__).resolve().parents[2]
    fixtures = discover_explicit_proof_corpus(repo_root)
    assert all(path.is_file() for path in fixtures)
    snapshot_fixtures = discover_snapshot_corpus(repo_root, ("egglog", "egglog-experimental"))
    assert all(fixture_execution_dependencies(repo_root, fixture) for fixture in snapshot_fixtures)
    commented = strip_egglog_line_comments(
        '(include; adjacent comment\n "tests/header.egg")\n'
        '(output; adjacent comment\n "/tmp/must-be-rejected" x)\n'
        '(input table "semi;colon.csv")\n'
    )
    assert INCLUDE_RE.findall(commented) == ["tests/header.egg"]
    assert len(INCLUDE_HEAD_RE.findall(commented)) == 1
    assert OUTPUT_HEAD_RE.search(commented) is not None
    assert INPUT_RE.findall(commented) == ["semi;colon.csv"]
    with tempfile.TemporaryDirectory(prefix="egglog-typed-emission-oracle-self-test-") as temporary:
        test_root = Path(temporary)
        expected = test_root / "expected"
        actual = test_root / "actual"
        expected.write_bytes(b"same\nexpected value\ntail\n")
        actual.write_bytes(b"same\nactual value\ntail\n")
        difference = first_stream_difference(expected, actual)
        assert difference is not None
        assert difference.byte_offset == 5
        assert difference.line == 2
        assert difference.byte_column == 1
        actual.write_bytes(expected.read_bytes())
        assert first_stream_difference(expected, actual) is None


def build_parser() -> argparse.ArgumentParser:
    """Define a CLI that never guesses the candidate release path or hash."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--candidate", type=Path, help="candidate egglog-experimental executable (required for a run)")
    parser.add_argument("--candidate-sha256", help="required full expected SHA-256 for --candidate")
    parser.add_argument(
        "--corpus",
        choices=(
            "proof-snapshots",
            "core-proof-snapshots",
            "experimental-proof-snapshots",
            "explicit-proofs",
        ),
        default="proof-snapshots",
        help=(
            "repository-discovered deterministic fixture sample; proof-snapshots combines both crates but is not "
            "the exhaustive proof-compatible corpus"
        ),
    )
    parser.add_argument(
        "--fixture",
        action="append",
        default=[],
        metavar="PATH",
        help="compare selected egglog or egglog-experimental test fixture(s), overriding --corpus",
    )
    parser.add_argument("--max-fixtures", type=int, help="deterministically truncate the selected corpus")
    parser.add_argument("--timeout-seconds", type=float, default=30.0, help="per-binary, per-fixture timeout")
    parser.add_argument(
        "--include-proof-testing-desugar",
        action="store_true",
        help="also compare exact --proof-testing --mode desugar output, including generated prove-query lowering",
    )
    parser.add_argument(
        "--execution-parity",
        action="store_true",
        help=(
            "also compare strict original-source --proof-testing --mode normal output plus the harness's "
            "(print-size) table-size projection in isolated /tmp fixture copies"
        ),
    )
    parser.add_argument(
        "--run-proof-tests",
        action="store_true",
        help=(
            "after binary parity, run the locked current-worktree equivalent of `make proof-tests` with "
            "CARGO_TARGET_DIR under artifacts; this separate source gate does not consume --candidate"
        ),
    )
    parser.add_argument(
        "--proof-tests-timeout-seconds",
        type=float,
        default=900.0,
        help="timeout for optional make proof-tests",
    )
    parser.add_argument("--artifact-root", type=Path, help="override the deterministic /tmp artifact directory")
    parser.add_argument(
        "--allow-identical-binaries",
        action="store_true",
        help="allow a baseline-vs-itself smoke run; rejected by default for migration comparisons",
    )
    parser.add_argument(
        "--allow-untracked-nonbuild-file",
        action="append",
        default=[],
        metavar="PATH",
        help=(
            "explicitly permit and hash one untracked document-only file during real candidate certification; "
            "likely Cargo inputs remain forbidden"
        ),
    )
    parser.add_argument(
        "--list-fixtures", action="store_true", help="list selected fixtures without validating binaries"
    )
    parser.add_argument("--self-test", action="store_true", help="run fast internal tests without invoking egglog")
    return parser


def select_fixtures(args: argparse.Namespace, repo_root: Path) -> list[Path]:
    """Select, validate, sort, and optionally bound the exact migration corpus."""
    if args.fixture:
        fixtures = resolve_explicit_fixtures(repo_root, args.fixture)
    elif args.corpus == "proof-snapshots":
        fixtures = discover_snapshot_corpus(repo_root, ("egglog", "egglog-experimental"))
    elif args.corpus == "core-proof-snapshots":
        fixtures = discover_snapshot_corpus(repo_root, ("egglog",))
    elif args.corpus == "experimental-proof-snapshots":
        fixtures = discover_snapshot_corpus(repo_root, ("egglog-experimental",))
    else:
        fixtures = discover_explicit_proof_corpus(repo_root)
    if args.max_fixtures is not None:
        if args.max_fixtures <= 0:
            raise OracleConfigurationError("--max-fixtures must be positive")
        fixtures = fixtures[: args.max_fixtures]
    if not fixtures:
        raise OracleConfigurationError("fixture selection is empty")
    return fixtures


def print_first_difference(difference: dict[str, object], report_path: Path) -> None:
    """Put the actionable witness on stderr while retaining full streams on disk."""
    print(
        f"FAIL [{difference['stage']}/{difference['treatment']}] {difference['fixture']}: {difference['kind']}",
        file=sys.stderr,
    )
    if "stream" in difference:
        print(
            f"  stream={difference['stream']} byte={difference['first_byte_offset_zero_based']} "
            f"line={difference['first_line_one_based']} column={difference['first_byte_column_one_based']}",
            file=sys.stderr,
        )
        print(f"  {difference['expected_label']}: {difference['expected_line']!r}", file=sys.stderr)
        print(f"  {difference['actual_label']}: {difference['actual_line']!r}", file=sys.stderr)
    else:
        print(
            f"  {difference['expected_label']} rc={difference['expected_returncode']} "
            f"timeout={difference['expected_timed_out']}; {difference['actual_label']} "
            f"rc={difference['actual_returncode']} timeout={difference['actual_timed_out']}",
            file=sys.stderr,
        )
    print(f"  full exact streams and JSON: {report_path.parent}", file=sys.stderr)


def bounded_error(error: BaseException, *, limit: int = 2000) -> str:
    """Keep aggregate filesystem failures actionable without flooding stderr or JSON."""
    message = str(error)
    if len(message) <= limit:
        return message
    return f"{message[:limit]}... <{len(message) - limit} characters omitted>"


def main(argv: Sequence[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    repo_root = Path(__file__).resolve().parents[2]
    lock_path: Path | None = None
    report_path: Path | None = None
    report: dict[str, object] | None = None

    try:
        if args.self_test:
            self_test()
            print(
                "PASS [self-test] exact-byte reporting, proof fixture discovery, and dependency isolation",
                file=sys.stderr,
            )
            return ExitCode.EXACT_PARITY

        fixtures = select_fixtures(args, repo_root)
        if args.list_fixtures:
            for fixture in fixtures:
                print(fixture.relative_to(repo_root).as_posix())
            return ExitCode.EXACT_PARITY

        fixture_dependencies = {fixture: fixture_execution_dependencies(repo_root, fixture) for fixture in fixtures}

        if args.candidate is None or args.candidate_sha256 is None:
            raise OracleConfigurationError("--candidate and --candidate-sha256 are required for a comparison")
        candidate_sha256 = args.candidate_sha256.lower()
        if SHA256_RE.fullmatch(candidate_sha256) is None:
            raise OracleConfigurationError("--candidate-sha256 must contain exactly 64 hexadecimal digits")
        if (
            not math.isfinite(args.timeout_seconds)
            or not math.isfinite(args.proof_tests_timeout_seconds)
            or args.timeout_seconds <= 0
            or args.proof_tests_timeout_seconds <= 0
        ):
            raise OracleConfigurationError("timeouts must be finite and positive")

        stages = [DESUGAR_STAGE]
        if args.include_proof_testing_desugar:
            stages.append(PROOF_TESTING_DESUGAR_STAGE)
        if args.execution_parity:
            stages.append(EXECUTION_STAGE)
        fixture_inputs = [fixture_input_identity(repo_root, fixture) for fixture in fixtures]
        test_trees = test_tree_identities(repo_root)
        fixture_manifest = fixture_manifest_sha256(
            fixture_inputs,
            test_trees,
            stages=stages,
            run_proof_tests=args.run_proof_tests,
        )
        source_metadata = git_metadata(repo_root)

        baseline = validate_binary(
            BASELINE_BINARY,
            label="baseline",
            expected_sha256=BASELINE_SHA256,
            source_sha=BASELINE_SOURCE_SHA,
            expected_version=BASELINE_VERSION,
        )
        candidate = validate_binary(
            args.candidate,
            label="candidate",
            expected_sha256=candidate_sha256,
            source_sha=None,
        )
        identical_binaries = baseline.sha256 == candidate.sha256
        allowed_untracked_files: list[dict[str, object]] = []
        if identical_binaries:
            if not args.allow_identical_binaries:
                raise OracleConfigurationError(
                    "candidate is byte-identical to the baseline; use --allow-identical-binaries "
                    "only for an oracle smoke run"
                )
        else:
            if source_metadata["tracked_dirty"]:
                raise OracleConfigurationError(
                    "candidate certification requires a tracked-clean source worktree; "
                    "commit the typed-emission checkpoint before building the candidate"
                )
            allowed_untracked_files = validate_untracked_nonbuild_files(
                repo_root,
                cast(Sequence[str], source_metadata["untracked_files"]),
                args.allow_untracked_nonbuild_file,
            )
            expected_version_suffix = f"_{source_metadata['short_head']}"
            if not candidate.version.endswith(expected_version_suffix):
                raise OracleConfigurationError(
                    f"candidate version {candidate.version!r} is not bound to current source "
                    f"{source_metadata['head']}; expected suffix {expected_version_suffix!r}"
                )

        corpus_label = "explicit-fixtures" if args.fixture else args.corpus
        default_root = (
            DEFAULT_ARTIFACT_PARENT / f"{baseline.sha256}-vs-{candidate.sha256}" / corpus_label / fixture_manifest
        )
        artifact_root = validate_artifact_root(args.artifact_root or default_root, repo_root)
        lock_path = acquire_artifact_lock(artifact_root)
        first_difference_path = artifact_root / "first-difference.json"
        first_difference_path.unlink(missing_ok=True)
        environment = stable_environment()
        report = {
            "schema": "temporary-typed-proof-emission-oracle-v1",
            "status": "running",
            "repo_root": str(repo_root),
            "source_worktree": source_metadata,
            "allowed_untracked_nonbuild_files": allowed_untracked_files,
            "baseline": {
                "label": baseline.label,
                "path": str(baseline.path),
                "sha256": baseline.sha256,
                "source_sha": baseline.source_sha,
                "version": baseline.version,
            },
            "candidate": {
                "label": candidate.label,
                "path": str(candidate.path),
                "sha256": candidate.sha256,
                "source_sha": baseline.source_sha if identical_binaries else source_metadata["head"],
                "version": candidate.version,
            },
            "primary_contract": {"treatment": DESUGAR_STAGE.treatment, "mode": DESUGAR_STAGE.mode, "threads": 1},
            "fixture_discovery": corpus_label,
            "coverage_note": (
                "Snapshot-backed corpora are deterministic samples, not the exhaustive set accepted by the Rust "
                "proof-support predicates. Use explicit --fixture for additional campaign canaries."
            ),
            "fixture_manifest_sha256": fixture_manifest,
            "fixtures": fixture_inputs,
            "resolved_dependencies": {
                fixture.relative_to(repo_root).as_posix(): [
                    dependency.relative_to(repo_root).as_posix() for dependency in fixture_dependencies[fixture]
                ]
                for fixture in fixtures
            },
            "test_trees": test_trees,
            "input_isolation": (
                "desugar reads the repository under pre/post complete test-tree hashes; optional execution copies "
                "only selected fixtures, recursive includes, fact directories, and input blobs"
            ),
            "timeout_seconds": args.timeout_seconds,
            "execution_parity": args.execution_parity,
            "include_proof_testing_desugar": args.include_proof_testing_desugar,
            "execution_state_projection": (
                "(print-size) appended in isolated copies; this covers table sizes, not every stored row"
                if args.execution_parity
                else None
            ),
            "run_proof_tests": args.run_proof_tests,
            "results": [],
        }
        report_path = artifact_root / "report.json"
        atomic_write_json(report_path, report)

        sandboxes: dict[tuple[Path, str], Path] | None = None
        if args.execution_parity:
            sandboxes = prepare_execution_sandboxes(
                artifact_root,
                fixtures,
                repo_root,
                fixture_dependencies,
            )

        fixture_reports: list[dict[str, object]] = []
        report["results"] = fixture_reports
        comparison_exit: ExitCode | None = None
        first_difference: dict[str, object] | None = None
        total_stages = len(fixtures) * len(stages)
        progress = 0
        for index, fixture in enumerate(fixtures, start=1):
            fixture_report: dict[str, object] = {
                "fixture": fixture.relative_to(repo_root).as_posix(),
                "stages": [],
            }
            fixture_reports.append(fixture_report)
            stage_reports: list[dict[str, object]] = []
            fixture_report["stages"] = stage_reports
            for stage in stages:
                progress += 1
                print(
                    f"[{progress}/{total_stages}] treatment={stage.treatment} mode={stage.mode} "
                    f"fixture={fixture.relative_to(repo_root)}",
                    file=sys.stderr,
                )
                fixture_artifact_root = artifact_root / artifact_slug(repo_root, fixture, index)
                arguments, facts, working_directories = fixture_arguments(
                    repo_root=repo_root,
                    fixture=fixture,
                    stage=stage,
                    sandboxes=sandboxes,
                )
                stage_artifact_dir = fixture_artifact_root / stage.name
                remove_controlled_directory(stage_artifact_dir, artifact_root)
                stage_report, comparison_exit, first_difference = compare_stage(
                    stage=stage,
                    fixture=fixture.relative_to(repo_root),
                    baseline=baseline,
                    candidate=candidate,
                    baseline_cwd=working_directories[0],
                    baseline_repeat_cwd=working_directories[1],
                    candidate_cwd=working_directories[2],
                    baseline_fixture_argument=arguments[0],
                    baseline_repeat_fixture_argument=arguments[1],
                    candidate_fixture_argument=arguments[2],
                    baseline_fact_directory=facts[0],
                    baseline_repeat_fact_directory=facts[1],
                    candidate_fact_directory=facts[2],
                    artifact_dir=stage_artifact_dir,
                    timeout_seconds=args.timeout_seconds,
                    environment=environment,
                )
                stage_reports.append(stage_report)
                atomic_write_json(report_path, report)
                if comparison_exit is not None:
                    break
            if comparison_exit is not None:
                break

        if first_difference is not None:
            report["status"] = "failed"
            report["first_difference"] = first_difference
            atomic_write_json(first_difference_path, first_difference)
            atomic_write_json(report_path, report)
            print_first_difference(first_difference, report_path)

        if comparison_exit is None and args.run_proof_tests:
            print(
                "running treatment=proof-testing mode='locked make proof-tests equivalent' against current worktree",
                file=sys.stderr,
            )
            proof_summary, comparison_exit = run_proof_corpus_command(
                repo_root=repo_root,
                artifact_root=artifact_root,
                timeout_seconds=args.proof_tests_timeout_seconds,
                environment=environment,
            )
            report["proof_corpus"] = proof_summary
            if comparison_exit is not None:
                report["status"] = "failed"
                print(
                    f"FAIL treatment=proof-testing mode='locked make proof-tests equivalent' "
                    f"returncode={proof_summary['returncode']} timed_out={proof_summary['timed_out']}; "
                    f"stdout={proof_summary['stdout']} stderr={proof_summary['stderr']}",
                    file=sys.stderr,
                )
            atomic_write_json(report_path, report)

        post_baseline_sha = sha256_file(baseline.path)
        post_candidate_sha = sha256_file(candidate.path)
        post_fixture_inputs = [fixture_input_identity(repo_root, fixture) for fixture in fixtures]
        post_test_trees = test_tree_identities(repo_root)
        post_source_metadata = git_metadata(repo_root)
        report["post_run_binary_hashes"] = {
            "baseline": post_baseline_sha,
            "candidate": post_candidate_sha,
        }
        report["post_run_fixtures"] = post_fixture_inputs
        report["post_run_test_trees"] = post_test_trees
        report["post_run_source_worktree"] = post_source_metadata
        if post_baseline_sha != baseline.sha256 or post_candidate_sha != candidate.sha256:
            report["status"] = "binary-drift"
            atomic_write_json(report_path, report)
            raise OracleConfigurationError("a compared binary changed during the run; results are invalid")
        if post_fixture_inputs != fixture_inputs:
            report["status"] = "fixture-drift"
            atomic_write_json(report_path, report)
            raise OracleConfigurationError("a fixture or fact directory changed during the run; results are invalid")
        if post_test_trees != test_trees:
            report["status"] = "test-input-drift"
            atomic_write_json(report_path, report)
            raise OracleConfigurationError("a repository test input changed during the run; results are invalid")
        if not identical_binaries:
            post_allowed_untracked_files = validate_untracked_nonbuild_files(
                repo_root,
                cast(Sequence[str], post_source_metadata["untracked_files"]),
                args.allow_untracked_nonbuild_file,
            )
            if (
                post_source_metadata["head"] != source_metadata["head"]
                or post_source_metadata["tracked_dirty"]
                or post_allowed_untracked_files != allowed_untracked_files
            ):
                report["status"] = "candidate-source-drift"
                atomic_write_json(report_path, report)
                raise OracleConfigurationError(
                    "the candidate source checkout changed during the run; results are invalid"
                )

        if comparison_exit is not None:
            atomic_write_json(report_path, report)
            return comparison_exit

        report["status"] = "exact-parity"
        atomic_write_json(report_path, report)
        print(
            f"PASS treatment=proofs mode=desugar fixtures={len(fixtures)} exact byte parity; report={report_path}",
            file=sys.stderr,
        )
        if args.execution_parity:
            print(
                f"PASS treatment=proof-testing mode=normal fixtures={len(fixtures)} exact byte parity",
                file=sys.stderr,
            )
        if args.include_proof_testing_desugar:
            print(
                f"PASS treatment=proof-testing mode=desugar fixtures={len(fixtures)} exact byte parity",
                file=sys.stderr,
            )
        return ExitCode.EXACT_PARITY
    except OracleConfigurationError as error:
        error_message = bounded_error(error)
        if report is not None and report_path is not None:
            report["status"] = "configuration-error"
            report["error"] = error_message
            with contextlib.suppress(OSError):
                atomic_write_json(report_path, report)
        print(f"oracle configuration error: {error_message}", file=sys.stderr)
        return ExitCode.CONFIGURATION_ERROR
    except (OSError, subprocess.SubprocessError, ValueError) as error:
        error_message = bounded_error(error)
        if report is not None and report_path is not None:
            report["status"] = "oracle-error"
            report["error"] = error_message
            with contextlib.suppress(OSError):
                atomic_write_json(report_path, report)
        print(f"oracle execution error: {error_message}", file=sys.stderr)
        return ExitCode.ORACLE_ERROR
    finally:
        if lock_path is not None:
            with contextlib.suppress(OSError):
                lock_path.unlink(missing_ok=True)


if __name__ == "__main__":
    raise SystemExit(main())
