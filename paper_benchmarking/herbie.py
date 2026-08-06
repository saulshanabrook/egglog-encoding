"""Stage and validate the bounded end-to-end Herbie artifact lane."""

from __future__ import annotations

import argparse
import math
import os
import re
import shutil
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path

from .hashing import sha256_file
from .models import CommandSpec, Preset, ProcessLane
from .rust_artifact import make_manifest_standalone, remove_tree, replace_directory

HERBIE_LOCK_SHA256 = "15f0a8eb20cdf988a7cb74e18d1d3663cb2cf823df85c0fc507ba42e368c65f6"
HERBIE_CORPUS_SHA256 = "8f99986949188e80a404a7b9f5743df06d4bb059d1fae3f010ebe2f61d223201"
HERBIE_NAME = "2cos (problem 3.3.5)"
HERBIE_TOOLCHAIN = "1.91.0"

_REMOTE_PACKAGES = (
    ("generic-flonum", "e2226376ed7b9bb543ec21606327d52e4077818a", True),
    ("fpbench", "7e2b76b1c3b55f923753e23ddfc979f847c50dbb", False),
    ("rival", "4d2334a05338be8df9c6924e30534d693f83267d", False),
)


@dataclass(frozen=True)
class _String:
    value: str


type SExpr = str | _String | list[SExpr]


def herbie_lanes(repo_root: Path, artifact_root: Path, preset: Preset) -> tuple[ProcessLane, ...]:
    """Return the one bounded artifact Herbie lane."""

    if preset != "quick":
        raise ValueError("the bounded Herbie evaluation currently supports only the quick preset")

    module = Path(__file__).resolve()
    lockfile = module.parent / "assets" / "herbie" / "Cargo.lock"
    build_root = repo_root / ".paper-build" / "herbie"
    staged_root = build_root / "work"
    staged_source = staged_root / "herbie-eqlog"
    cargo_target = build_root / "cargo-target"
    racket_home = build_root / "racket-home"
    native_library = _native_library(cargo_target)
    python_env = {"PYTHONPATH": str(repo_root)}
    racket_env = {"PLTUSERHOME": str(racket_home)}

    build: list[CommandSpec] = [
        CommandSpec(
            label="stage",
            argv=(
                str(Path(sys.executable).resolve()),
                "-m",
                "paper_benchmarking.herbie",
                "stage",
                "--artifact-root",
                str(artifact_root),
                "--destination",
                str(staged_root),
                "--lockfile",
                str(lockfile),
                "--cargo-target",
                str(cargo_target),
                "--racket-home",
                str(racket_home),
            ),
            cwd=repo_root,
            timeout_sec=60,
            env=python_env,
        ),
        CommandSpec(
            label="cargo",
            argv=("cargo", "build", "--release", "--locked", "--manifest-path", "egg-herbie/Cargo.toml"),
            cwd=staged_source,
            timeout_sec=300,
            env={
                "CARGO_INCREMENTAL": "0",
                "CARGO_TARGET_DIR": str(cargo_target),
                "RUSTC_WRAPPER": "",
                "RUSTUP_TOOLCHAIN": HERBIE_TOOLCHAIN,
            },
        ),
    ]
    for package, checksum, auto in _REMOTE_PACKAGES:
        dependency_args = ("--auto",) if auto else ("--deps", "fail")
        build.append(
            CommandSpec(
                label=f"racket-{package}",
                argv=(
                    "raco",
                    "pkg",
                    "install",
                    *dependency_args,
                    "--batch",
                    "--no-docs",
                    "--skip-installed",
                    "--checksum",
                    checksum,
                    package,
                ),
                cwd=staged_source,
                timeout_sec=300,
                env=racket_env,
            )
        )
    build.extend(
        (
            CommandSpec(
                label="racket-egg-herbie",
                argv=(
                    "raco",
                    "pkg",
                    "install",
                    "--deps",
                    "fail",
                    "--batch",
                    "--no-docs",
                    "--skip-installed",
                    "--link",
                    "./egg-herbie",
                ),
                cwd=staged_source,
                timeout_sec=120,
                env=racket_env,
            ),
            CommandSpec(
                label="racket-herbie",
                argv=(
                    "raco",
                    "pkg",
                    "install",
                    "--deps",
                    "fail",
                    "--batch",
                    "--no-docs",
                    "--skip-installed",
                    "--link",
                    "--name",
                    "herbie",
                    "src",
                ),
                cwd=staged_source,
                timeout_sec=120,
                env=racket_env,
            ),
        )
    )

    return (
        ProcessLane(
            evaluation="herbie",
            name="artifact-eqlog-2cos",
            build=tuple(build),
            prepare=(
                CommandSpec(
                    label="packages",
                    argv=(
                        str(Path(sys.executable).resolve()),
                        "-m",
                        "paper_benchmarking.herbie",
                        "verify-packages",
                        "--source-root",
                        str(staged_source),
                    ),
                    cwd=staged_source,
                    timeout_sec=30,
                    env={**python_env, **racket_env},
                ),
                CommandSpec(
                    label="linkage",
                    argv=("racket", "src/herbie.rkt", "improve", "--help"),
                    cwd=staged_source,
                    timeout_sec=30,
                    env=racket_env,
                ),
            ),
            observations=(
                CommandSpec(
                    label="run-1",
                    argv=(
                        str(Path(sys.executable).resolve()),
                        "-m",
                        "paper_benchmarking.herbie",
                        "run",
                        "--source-root",
                        str(staged_source),
                    ),
                    cwd=staged_source,
                    timeout_sec=60,
                    env={**python_env, **racket_env},
                    runtime_executables=("racket",),
                    runtime_artifacts=(racket_home, native_library),
                ),
            ),
            input_paths=(
                artifact_root / "herbie-eqlog",
                artifact_root / "eqlog-herbie-tweaks",
                lockfile,
                module,
            ),
            versions={
                "cargo-lock-sha256": HERBIE_LOCK_SHA256,
                "egg-herbie-cargo": "0.3.0",
                "egg-herbie-racket": "1.6",
                "fpbench": _REMOTE_PACKAGES[1][1],
                "generic-flonum": _REMOTE_PACKAGES[0][1],
                "herbie": "1.6",
                "rival": _REMOTE_PACKAGES[2][1],
                "rust-toolchain": HERBIE_TOOLCHAIN,
                "workload": "2cos-one-iteration-64-points-seed-0",
            },
        ),
    )


def stage_artifact(
    artifact_root: Path,
    destination: Path,
    lockfile: Path,
    cargo_target: Path,
    racket_home: Path,
) -> None:
    """Copy immutable artifact sources to a mutable, isolated build tree."""

    source_root = artifact_root.resolve(strict=True)
    source_herbie = source_root / "herbie-eqlog"
    source_eqlog = source_root / "eqlog-herbie-tweaks"
    lock = lockfile.resolve(strict=True)
    if sha256_file(lock) != HERBIE_LOCK_SHA256:
        raise ValueError("Herbie compatibility Cargo.lock has the wrong SHA-256")
    _validate_corpus(source_herbie / "2cos.fpcore")

    target = destination.expanduser().absolute()
    target.parent.mkdir(parents=True, exist_ok=True)
    cargo = cargo_target.expanduser().absolute()
    cargo.mkdir(parents=True, exist_ok=True)
    racket = racket_home.expanduser().absolute()
    remove_tree(racket)
    racket.mkdir(parents=True)
    stage = Path(tempfile.mkdtemp(prefix=f".{target.name}.staging-", dir=target.parent))
    try:
        shutil.copytree(source_herbie, stage / "herbie-eqlog")
        shutil.copytree(source_eqlog, stage / "eqlog-herbie-tweaks")
        staged_lock = stage / "herbie-eqlog" / "egg-herbie" / "Cargo.lock"
        shutil.copyfile(lock, staged_lock)
        make_manifest_standalone(staged_lock.parent / "Cargo.toml")
        target_link = staged_lock.parent / "target"
        if os.path.lexists(target_link):
            remove_tree(target_link)
        target_link.symlink_to(cargo, target_is_directory=True)
        replace_directory(stage, target)
    except BaseException:
        remove_tree(stage)
        raise


def run_bounded_herbie(source_root: Path) -> int:
    """Run one Herbie problem, forward its logs, and reject semantic failures."""

    root = source_root.resolve(strict=True)
    corpus = root / "2cos.fpcore"
    _validate_corpus(corpus)
    argv = (
        "racket",
        "src/herbie.rkt",
        "improve",
        "--threads",
        "no",
        "--seed",
        "0",
        "--timeout",
        "30",
        "--num-iters",
        "1",
        "--num-points",
        "64",
        "--no-pareto",
        "--enable",
        "generate:eqlog",
        "2cos.fpcore",
        "-",
    )
    completed = subprocess.run(argv, cwd=root, capture_output=True, text=True, check=False)
    sys.stdout.write(completed.stdout)
    sys.stderr.write(completed.stderr)
    sys.stdout.flush()
    sys.stderr.flush()
    if completed.returncode != 0:
        return completed.returncode if completed.returncode > 0 else 1
    try:
        validate_herbie_output(corpus, completed.stdout, completed.stderr)
    except ValueError as error:
        print(f"Herbie semantic validation failed: {error}", file=sys.stderr)
        return 1
    return 0


def verify_racket_packages(source_root: Path) -> int:
    """Reject stale package revisions or links in the isolated Racket scope."""

    root = source_root.resolve(strict=True)
    argv = (
        "raco",
        "pkg",
        "show",
        "--all",
        "--long",
        "--full-checksum",
        "--dir",
        *(package for package, _checksum, _auto in _REMOTE_PACKAGES),
        "egg-herbie",
        "herbie",
    )
    completed = subprocess.run(argv, cwd=root, capture_output=True, text=True, check=False)
    sys.stdout.write(completed.stdout)
    sys.stderr.write(completed.stderr)
    if completed.returncode != 0:
        return completed.returncode if completed.returncode > 0 else 1
    try:
        for package, checksum, _auto in _REMOTE_PACKAGES:
            if re.search(rf"(?m)^\s*{re.escape(package)}\s+{checksum}\s", completed.stdout) is None:
                raise ValueError(f"Racket package {package} is not installed at {checksum}")
        _validate_package_link(completed.stdout, "egg-herbie", root / "egg-herbie")
        _validate_package_link(completed.stdout, "herbie", root / "src")
    except ValueError as error:
        print(f"Racket package validation failed: {error}", file=sys.stderr)
        return 1
    return 0


def validate_herbie_output(corpus: Path, stdout: str, stderr: str) -> None:
    """Require the bounded run's source, status, scores, and progress evidence."""

    source = _parse_one(corpus.read_text(encoding="utf-8"))
    expected_source: SExpr = [
        "FPCore",
        ["x", "eps"],
        ":name",
        _String(HERBIE_NAME),
        ["-", ["cos", ["+", "x", "eps"]], ["cos", "x"]],
    ]
    if source != expected_source:
        raise ValueError("2cos.fpcore does not contain the expected source expression")
    if ";; seed: 0" not in stdout.splitlines():
        raise ValueError("stdout is missing the seed marker")
    result = _parse_one(stdout)
    if not isinstance(result, list) or len(result) < 4 or result[0] != "FPCore" or result[1] != ["x", "eps"]:
        raise ValueError("stdout does not contain the expected one-result FPCore form")
    properties, expression = _fpcore_properties(result)
    if properties.get(":name") != _String(HERBIE_NAME):
        raise ValueError("result name changed")
    if properties.get(":precision") != "binary64":
        raise ValueError("result precision changed")
    if properties.get(":herbie-status") != "imp-start":
        raise ValueError(f"unexpected Herbie status: {properties.get(':herbie-status')!r}")
    _validate_error_improvement(properties, ":herbie-error-input", ":herbie-error-output")
    if not isinstance(expression, list) or not expression:
        raise ValueError("result expression is missing")
    if "Starting Herbie on 1 problems (seed: 0)" not in stderr or "1/1" not in stderr:
        raise ValueError("stderr does not show completion of the one-problem corpus")


def _validate_corpus(path: Path) -> None:
    if sha256_file(path.resolve(strict=True)) != HERBIE_CORPUS_SHA256:
        raise ValueError("Herbie 2cos corpus has the wrong SHA-256")


def _validate_package_link(output: str, package: str, expected: Path) -> None:
    match = re.search(rf'(?m)^\s*{re.escape(package)}\s+#f\s+\(link "([^"]+)"\)', output)
    if match is None or Path(match.group(1)).resolve(strict=False) != expected.resolve(strict=True):
        raise ValueError(f"Racket package {package} is not linked to the staged artifact")


def _native_library(cargo_target: Path) -> Path:
    if sys.platform == "darwin":
        return cargo_target / "release" / "libegg_math.dylib"
    if sys.platform == "win32":
        return cargo_target / "release" / "egg_math.dll"
    return cargo_target / "release" / "libegg_math.so"


def _fpcore_properties(form: list[SExpr]) -> tuple[dict[str, SExpr], SExpr]:
    properties: dict[str, SExpr] = {}
    index = 2
    while index < len(form):
        key = form[index]
        if not isinstance(key, str) or not key.startswith(":"):
            break
        if index + 1 >= len(form):
            raise ValueError("FPCore property is missing its value")
        properties[key] = form[index + 1]
        index += 2
    if index + 1 != len(form):
        raise ValueError("FPCore result must contain exactly one expression")
    return properties, form[index]


def _validate_error_improvement(properties: dict[str, SExpr], input_key: str, output_key: str) -> None:
    input_errors = _error_table(properties.get(input_key), input_key)
    output_errors = _error_table(properties.get(output_key), output_key)
    if input_errors.keys() != output_errors.keys() or set(input_errors) != {64, 8000}:
        raise ValueError("Herbie error tables do not cover the expected 64 and 8000 point samples")
    if any(output_errors[size] >= input_errors[size] for size in input_errors):
        raise ValueError("Herbie did not improve every recorded error score")


def _error_table(value: SExpr | None, label: str) -> dict[int, float]:
    if not isinstance(value, list):
        raise ValueError(f"{label} is not an error table")
    result: dict[int, float] = {}
    for row in value:
        if not isinstance(row, list) or len(row) != 2 or not isinstance(row[0], str) or not isinstance(row[1], str):
            raise ValueError(f"{label} contains an invalid row")
        try:
            count = int(row[0])
            error = float(row[1])
        except ValueError as parse_error:
            raise ValueError(f"{label} contains a nonnumeric row") from parse_error
        if not math.isfinite(error) or error < 0 or count in result:
            raise ValueError(f"{label} contains an invalid score")
        result[count] = error
    return result


def _parse_one(source: str) -> SExpr:
    tokens = _tokenize(source)
    if not tokens:
        raise ValueError("S-expression input is empty")
    value, index = _parse(tokens, 0)
    if index != len(tokens):
        raise ValueError("S-expression input contains more than one form")
    return value


def _tokenize(source: str) -> list[str | _String]:
    tokens: list[str | _String] = []
    index = 0
    while index < len(source):
        char = source[index]
        if char.isspace():
            index += 1
        elif char == ";":
            newline = source.find("\n", index)
            index = len(source) if newline < 0 else newline + 1
        elif char in "()":
            tokens.append(char)
            index += 1
        elif char == '"':
            value, index = _read_string(source, index + 1)
            tokens.append(_String(value))
        else:
            end = index
            while end < len(source) and not source[end].isspace() and source[end] not in "();":
                end += 1
            tokens.append(source[index:end])
            index = end
    return tokens


def _read_string(source: str, index: int) -> tuple[str, int]:
    value: list[str] = []
    escapes = {"n": "\n", "r": "\r", "t": "\t"}
    while index < len(source):
        char = source[index]
        if char == '"':
            return "".join(value), index + 1
        if char == "\\":
            index += 1
            if index >= len(source):
                break
            char = escapes.get(source[index], source[index])
        value.append(char)
        index += 1
    raise ValueError("unterminated S-expression string")


def _parse(tokens: list[str | _String], index: int) -> tuple[SExpr, int]:
    if index >= len(tokens):
        raise ValueError("unexpected end of S-expression")
    token = tokens[index]
    if token == "(":
        values: list[SExpr] = []
        index += 1
        while index < len(tokens) and tokens[index] != ")":
            value, index = _parse(tokens, index)
            values.append(value)
        if index >= len(tokens):
            raise ValueError("unterminated S-expression list")
        return values, index + 1
    if token == ")":
        raise ValueError("unexpected closing parenthesis")
    return token, index + 1


def _parse_args(argv: list[str] | None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    stage = commands.add_parser("stage")
    stage.add_argument("--artifact-root", type=Path, required=True)
    stage.add_argument("--destination", type=Path, required=True)
    stage.add_argument("--lockfile", type=Path, required=True)
    stage.add_argument("--cargo-target", type=Path, required=True)
    stage.add_argument("--racket-home", type=Path, required=True)
    run = commands.add_parser("run")
    run.add_argument("--source-root", type=Path, required=True)
    verify = commands.add_parser("verify-packages")
    verify.add_argument("--source-root", type=Path, required=True)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    """Dispatch the adapter's isolated staging and observation helpers."""

    args = _parse_args(argv)
    try:
        if args.command == "stage":
            stage_artifact(
                args.artifact_root,
                args.destination,
                args.lockfile,
                args.cargo_target,
                args.racket_home,
            )
            return 0
        if args.command == "verify-packages":
            return verify_racket_packages(args.source_root)
        return run_bounded_herbie(args.source_root)
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
