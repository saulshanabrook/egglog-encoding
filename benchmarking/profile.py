"""Define, parse, and execute CPU profile requests and cache Samply artifacts.

Profile-specific request policy lives here. Artifact decoding and presentation
belong in :mod:`benchmarking.samply_analysis`.
"""

from __future__ import annotations

import argparse
import math
import os
import shutil
import subprocess
import sys
import uuid
from collections.abc import Sequence
from contextlib import suppress
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Literal, cast

from rich.text import Text

from . import samply_analysis
from .models import (
    BACKEND_SPECS,
    Backend,
    FileSpec,
    TargetRequest,
    Treatment,
    validate_backend_treatment,
)
from .output import RunnerOutput
from .processes import run_command, terminate_process_group
from .targets import git_root_for_path, parse_target, resolve_profile_target, workload_command
from .workloads import require_workload_unchanged, resolve_files

DEFAULT_PROFILES_DIR = ".profiles"
DEFAULT_PROFILE_SECONDS = 10
DEFAULT_PROFILE_TOP = 15
DEFAULT_TIMEOUT_SEC = 120
MAX_PROFILE_ITERATIONS = 10_000
PROFILE_CACHE_VERSION = "v3"
PROFILE_SAMPLY_RATE_HZ = 1000
OutputFormat = Literal["rich", "markdown"]


@dataclass(frozen=True)
class ProfileMode:
    """Explicit or duration-calibrated profile iteration policy."""

    iterations: int | None
    profile_seconds: int | None

    @property
    def cache_label(self) -> str:
        if self.iterations is not None:
            return f"i{self.iterations}"
        assert self.profile_seconds is not None
        return f"auto{self.profile_seconds}s"


@dataclass(frozen=True)
class ProfileRequest:
    """Validated profile CLI request resolved before target materialization."""

    file: FileSpec
    target_request: TargetRequest
    backend: Backend
    treatment: Treatment
    timeout_sec: int
    profiles_dir: Path
    mode: ProfileMode
    open_after: bool
    force_run: bool
    top: int = DEFAULT_PROFILE_TOP
    show_summary: bool = True
    output_format: OutputFormat = "rich"


def parse_profile_args(argv: Sequence[str]) -> argparse.Namespace:
    """Parse profile arguments without importing the benchmark data stack."""
    parser = argparse.ArgumentParser(
        prog=f"{Path(sys.argv[0]).name} profile",
        description="Record or reuse a cached Samply CPU profile for one egglog workload.",
    )
    parser.add_argument("file", help="egglog file to profile")
    parser.add_argument(
        "--fact-directory",
        default=None,
        help="fact directory used by the profiled workload",
    )
    parser.add_argument(
        "--target",
        default=".",
        help="target source: ., /path, @git-ref, #pr, or label=source; cache-only label= is not supported",
    )
    parser.add_argument(
        "--backend",
        choices=tuple(BACKEND_SPECS),
        default="main",
        help="backend to profile (default: main)",
    )
    parser.add_argument(
        "--treatment",
        choices=("off", "term", "proofs"),
        default="proofs",
        help="treatment to profile (default: proofs)",
    )
    iteration_group = parser.add_mutually_exclusive_group()
    iteration_group.add_argument(
        "--iterations", type=positive_int, default=None, help="explicit Samply iteration count"
    )
    iteration_group.add_argument(
        "--profile-seconds",
        type=positive_int,
        default=None,
        help=f"target duration for automatic iteration selection (default: {DEFAULT_PROFILE_SECONDS})",
    )
    parser.add_argument(
        "--profiles-dir",
        default=DEFAULT_PROFILES_DIR,
        help=f"profile cache directory (default: {DEFAULT_PROFILES_DIR})",
    )
    parser.add_argument(
        "--top",
        type=positive_int,
        default=DEFAULT_PROFILE_TOP,
        help=f"application functions to show in the macOS CPU summary (default: {DEFAULT_PROFILE_TOP})",
    )
    parser.add_argument("--no-summary", action="store_true", help="print only the profile artifact path")
    parser.add_argument(
        "--format",
        choices=("rich", "markdown"),
        default="rich",
        help="summary format: rich to stderr, or markdown to stdout (default: rich)",
    )
    parser.add_argument(
        "--open", action="store_true", help="open the profile with samply load after recording or cache hit"
    )
    parser.add_argument(
        "--force-run",
        action="store_true",
        help="record again and atomically replace the cached profile",
    )
    parser.add_argument(
        "--timeout-sec",
        type=positive_int,
        default=DEFAULT_TIMEOUT_SEC,
        help=f"per-workload timeout in seconds for calibration and profiling watchdog (default: {DEFAULT_TIMEOUT_SEC})",
    )
    args = parser.parse_args(argv)
    args.command = "profile"
    return args


def positive_int(value: str) -> int:
    """Parse a positive integer for one profile CLI option."""

    parsed = int(value)
    if parsed <= 0:
        raise argparse.ArgumentTypeError("must be positive")
    return parsed


def profile_hash_component(value: str) -> str:
    return value.removeprefix("sha256:")


def profile_cache_path(
    profiles_dir: Path,
    binary_sha256: str,
    file_sha256: str,
    backend: Backend,
    treatment: Treatment,
    mode: ProfileMode,
    fact_directory_sha256: str = "",
) -> Path:
    return (
        profiles_dir
        / PROFILE_CACHE_VERSION
        / profile_hash_component(binary_sha256)
        / profile_hash_component(file_sha256)
        / (profile_hash_component(fact_directory_sha256) if fact_directory_sha256 else "no-facts")
        / f"{backend}-{treatment}-{mode.cache_label}.json.gz"
    )


def profile_cache_hit(path: Path) -> bool:
    return path.is_file() and path.stat().st_size > 0


def profile_display_path(path: Path, invocation_cwd: Path) -> Path:
    resolved = path.resolve()
    try:
        return resolved.relative_to(invocation_cwd.resolve())
    except ValueError:
        return resolved


def calculate_profile_iterations(
    elapsed_seconds: float,
    profile_seconds: int,
    max_iterations: int = MAX_PROFILE_ITERATIONS,
) -> tuple[int, bool]:
    if elapsed_seconds <= 0:
        return (max_iterations, True)
    uncapped = max(1, math.ceil(profile_seconds * 1.10 / elapsed_seconds))
    if uncapped > max_iterations:
        return (max_iterations, True)
    return (uncapped, False)


def profile_name(
    file_spec: FileSpec,
    backend: Backend,
    treatment: Treatment,
    mode: ProfileMode,
    iterations: int,
    binary_sha256: str,
) -> str:
    stem = Path(file_spec.display_path).stem
    file_hash = profile_hash_component(file_spec.sha256)[:8]
    binary_hash = profile_hash_component(binary_sha256)[:8]
    mode_label = mode.cache_label if mode.iterations is not None else f"auto>={mode.profile_seconds}s"
    return f"{stem} {backend}/{treatment} {mode_label} x{iterations} [bin:{binary_hash} file:{file_hash}]"


def profile_temp_path(artifact: Path) -> Path:
    base_name = artifact.name.removesuffix(".json.gz")
    return artifact.with_name(f".{base_name}.tmp-{uuid.uuid4().hex}.json.gz")


def samply_executable() -> str:
    executable = shutil.which("samply")
    if executable is None:
        raise FileNotFoundError("Install Samply with: cargo install --locked samply")
    return executable


def samply_record_command(
    samply: str,
    artifact: Path,
    name: str,
    iterations: int,
    workload: Sequence[str],
) -> list[str]:
    return [
        samply,
        "record",
        "--save-only",
        "--rate",
        str(PROFILE_SAMPLY_RATE_HZ),
        "--reuse-threads",
        "--iteration-count",
        str(iterations),
        "--profile-name",
        name,
        "--output",
        str(artifact),
        "--",
        *workload,
    ]


def profile_record_timeout(timeout_sec: int, iterations: int) -> int:
    return max(timeout_sec + 60, timeout_sec * iterations + 60)


def run_samply_record(
    *,
    artifact: Path,
    file_spec: FileSpec,
    name: str,
    iterations: int,
    workload: Sequence[str],
    checkout_path: Path,
    timeout_sec: int,
) -> dict[str, Any]:
    temp_artifact = profile_temp_path(artifact)
    temp_artifact.parent.mkdir(parents=True, exist_ok=True)
    with suppress(FileNotFoundError):
        temp_artifact.unlink()
    command = samply_record_command(samply_executable(), temp_artifact, name, iterations, workload)
    env = os.environ.copy()
    env["RUST_LOG"] = "error"
    try:
        process = subprocess.Popen(
            command,
            cwd=checkout_path,
            env=env,
            stdout=sys.stderr,
            stderr=sys.stderr,
            start_new_session=True,
        )
        try:
            return_code = process.wait(timeout=profile_record_timeout(timeout_sec, iterations))
        except BaseException:
            terminate_process_group(process)
            raise
        if return_code != 0:
            terminate_process_group(process)
            raise subprocess.CalledProcessError(return_code, command)
        if not profile_cache_hit(temp_artifact):
            raise ValueError(f"Samply did not produce a nonempty profile artifact: {temp_artifact}")
        require_workload_unchanged(file_spec)
        profile = samply_analysis.read_artifact(temp_artifact)
        artifact.parent.mkdir(parents=True, exist_ok=True)
        os.replace(temp_artifact, artifact)
        return profile
    except BaseException:
        with suppress(FileNotFoundError):
            temp_artifact.unlink()
        raise


def open_samply_profile(artifact: Path, checkout_path: Path) -> None:
    try:
        subprocess.run(
            [samply_executable(), "load", str(artifact)],
            cwd=checkout_path,
            check=True,
            stdout=sys.stderr,
            stderr=sys.stderr,
        )
    except KeyboardInterrupt:
        return


def resolve_profile_request(args: argparse.Namespace, invocation_cwd: Path) -> ProfileRequest:
    files = resolve_files([str(args.file)], invocation_cwd, args.fact_directory)
    backend = cast(Backend, str(args.backend))
    treatment = cast(Treatment, str(args.treatment))
    validate_backend_treatment(backend, treatment)
    if args.iterations is not None:
        mode = ProfileMode(iterations=args.iterations, profile_seconds=None)
    else:
        profile_seconds = args.profile_seconds if args.profile_seconds is not None else DEFAULT_PROFILE_SECONDS
        mode = ProfileMode(iterations=None, profile_seconds=profile_seconds)
    profiles_dir = Path(str(args.profiles_dir)).expanduser()
    if not profiles_dir.is_absolute():
        profiles_dir = invocation_cwd / profiles_dir
    request = ProfileRequest(
        file=files[0],
        target_request=parse_target(str(args.target)),
        backend=backend,
        treatment=treatment,
        timeout_sec=int(args.timeout_sec),
        profiles_dir=profiles_dir,
        mode=mode,
        open_after=bool(args.open),
        force_run=bool(args.force_run),
        top=int(args.top),
        show_summary=not bool(args.no_summary),
        output_format=cast(OutputFormat, str(args.format)),
    )
    return request


def run_profile(args: argparse.Namespace, output: RunnerOutput, invocation_cwd: Path, repo_root: Path) -> None:
    request = resolve_profile_request(args, invocation_cwd)
    target = resolve_profile_target(request.target_request, request.backend, invocation_cwd, repo_root, output)
    if target.binary_path is None:
        raise ValueError(f"target {target.display_label} needs a profiling binary")
    checkout_path = Path(target.row.path)
    workload = workload_command(target.binary_path, request.file, request.backend, request.treatment)
    artifact = profile_cache_path(
        request.profiles_dir,
        target.binary_sha256,
        request.file.sha256,
        request.backend,
        request.treatment,
        request.mode,
        request.file.fact_directory_sha256,
    )
    profile: dict[str, Any] | None = None
    cache_status: Literal["hit", "recorded"] = "recorded"
    if profile_cache_hit(artifact) and not request.force_run:
        try:
            profile = samply_analysis.read_artifact(artifact)
        except ValueError as error:
            output.console.print(
                Text.assemble(("warning:", "yellow"), " ignoring invalid profile cache entry: ", str(error))
            )
        else:
            cache_status = "hit"
            output.console.print(Text.assemble(("Profile cache hit", "bold"), " ", str(artifact)))

    if profile is None:
        iterations = request.mode.iterations
        if iterations is None:
            assert request.mode.profile_seconds is not None
            output.console.print(
                Text.assemble(
                    ("Calibrating", "bold"),
                    " ",
                    request.file.display_path,
                    f" {request.backend}/{request.treatment} for {request.mode.profile_seconds}s",
                )
            )
            calibration = run_command(workload, checkout_path, request.timeout_sec)
            if calibration.status != "success" or calibration.timing.wall_sec is None:
                detail = calibration.error.message if calibration.error is not None else calibration.status
                raise ValueError(f"profile calibration failed: {detail}")
            iterations, capped = calculate_profile_iterations(
                calibration.timing.wall_sec,
                request.mode.profile_seconds,
            )
            output.console.print(
                f"  calibration: {calibration.timing.wall_sec:.3f}s; recording {iterations} Samply iteration(s)"
            )
            if capped:
                output.console.print(
                    "[yellow]warning:[/yellow] maximum profile iterations reached; "
                    "the profile may be shorter than the requested duration"
                )

        assert iterations is not None
        name = profile_name(
            request.file,
            request.backend,
            request.treatment,
            request.mode,
            iterations,
            target.binary_sha256,
        )
        output.console.print(Text.assemble(("Recording profile", "bold"), " ", str(artifact)))
        profile = run_samply_record(
            artifact=artifact,
            file_spec=request.file,
            name=name,
            iterations=iterations,
            workload=workload,
            checkout_path=checkout_path,
            timeout_sec=request.timeout_sec,
        )
        output.console.print(Text.assemble(("Profile written", "bold"), " ", str(artifact)))

    if request.show_summary:
        display_artifact = profile_display_path(artifact, invocation_cwd)
        summary: samply_analysis.ProfileCpuSummary | None = None
        if sys.platform == "darwin":
            try:
                summary = samply_analysis.summarize(profile, target.binary_path)
            except ValueError as error:
                output.console.print(
                    Text.assemble(("warning:", "yellow"), " CPU profile summary unavailable: ", str(error))
                )
            if summary is not None:
                for warning in summary.warnings:
                    output.console.print(Text.assemble(("warning:", "yellow"), " ", warning))
        else:
            output.console.print(
                "[yellow]warning:[/yellow] CPU profile summaries are currently available on macOS only; "
                "the Samply artifact was created normally."
            )
        report = samply_analysis.ProfileReport(
            artifact=display_artifact,
            cache_status=cache_status,
            workload=request.file.display_path,
            backend=request.backend,
            treatment=request.treatment,
            top=request.top,
            cpu_summary=summary,
        )
        if request.output_format == "markdown":
            rendered = samply_analysis.render_markdown(report)
            sys.stdout.write(rendered + "\n")
            sys.stdout.flush()
        else:
            samply_analysis.render_rich(output.console, report)
    else:
        sys.stdout.write(str(artifact.resolve()) + "\n")
        sys.stdout.flush()
    if request.open_after:
        open_samply_profile(artifact, checkout_path)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_profile_args(tuple(sys.argv[1:] if argv is None else argv))
    output = RunnerOutput()
    try:
        script_root = Path(__file__).resolve().parents[1]
        run_profile(args, output, Path.cwd(), git_root_for_path(script_root))
    except (FileNotFoundError, ValueError, subprocess.CalledProcessError, subprocess.TimeoutExpired) as error:
        output.print_error(error)
        return 2
    return 0
