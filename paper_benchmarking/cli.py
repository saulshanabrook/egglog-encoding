"""Parse and dispatch setup and run commands for the paper artifact harness."""

from __future__ import annotations

import argparse
import secrets
import subprocess
import sys
import tarfile
from collections.abc import Callable, Mapping, Sequence
from datetime import UTC, datetime
from pathlib import Path
from typing import TextIO, cast

from .adapters import production_registry
from .artifact import EXPECTED_ARCHIVE_SHA256, render_setup_summary, setup_artifact, verify_artifact_cache
from .lanes import LaneRegistry
from .models import (
    EVALUATION_SELECTIONS,
    PRESETS,
    EvaluationSelection,
    Preset,
    expand_evaluations,
)
from .processes import ProcessExecutor
from .runner import run_lanes


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    """Parse the stable public setup/run command surface."""

    parser = argparse.ArgumentParser(description="Set up and run the standalone paper artifact harness.")
    subparsers = parser.add_subparsers(dest="command", required=True)

    setup_parser = subparsers.add_parser("setup", help="verify and safely cache the historical artifact")
    source = setup_parser.add_mutually_exclusive_group()
    source.add_argument("--archive", help="existing artifact .tar.gz path")
    source.add_argument("--url", help="artifact archive URL to download")
    setup_parser.add_argument(
        "--cache-dir",
        default=None,
        help="artifact cache directory (default: .paper-artifact)",
    )

    run_parser = subparsers.add_parser("run", help="run one paper evaluation selection")
    run_parser.add_argument("preset", choices=PRESETS)
    run_parser.add_argument("evaluation", choices=EVALUATION_SELECTIONS)
    run_parser.add_argument(
        "--artifact-dir",
        default=None,
        help="verified artifact cache directory (default: .paper-artifact)",
    )
    run_parser.add_argument(
        "--results-dir",
        default=None,
        help="exclusive run directory root (default: .paper-results)",
    )
    run_parser.add_argument("--run-id", default=None, help="explicit result directory id")
    return parser.parse_args(argv)


def main(
    argv: Sequence[str] | None = None,
    *,
    lane_registry: LaneRegistry | None = None,
    executor: ProcessExecutor | None = None,
    stdout: TextIO | None = None,
    stderr: TextIO | None = None,
    now: Callable[[], datetime] | None = None,
    environment: Mapping[str, str] | None = None,
    repo_root: Path | None = None,
    expected_archive_sha256: str = EXPECTED_ARCHIVE_SHA256,
) -> int:
    """Dispatch one paper command with injectable lanes, execution, and clock."""

    raw_argv = tuple(sys.argv[1:] if argv is None else argv)
    invocation_argv = tuple(sys.argv if argv is None else ("paper_bench.py", *raw_argv))
    args = parse_args(raw_argv)
    output = stdout or sys.stdout
    diagnostics = stderr or sys.stderr
    clock = now or (lambda: datetime.now(UTC))
    invocation_cwd = Path.cwd().resolve()
    root = (repo_root or Path(__file__).resolve().parents[1]).resolve()
    base_environment = dict(environment) if environment is not None else None

    try:
        if args.command == "setup":
            cache_root = (
                root / ".paper-artifact"
                if args.cache_dir is None
                else _resolve_path(str(args.cache_dir), invocation_cwd)
            )
            if args.archive is None and args.url is None:
                print(f"Verifying cached paper artifact at {cache_root}", file=diagnostics)
                cache = verify_artifact_cache(cache_root, expected_sha256=expected_archive_sha256)
            else:
                print(f"Preparing paper artifact cache at {cache_root}", file=diagnostics)
                archive_path = _resolve_path(str(args.archive), invocation_cwd) if args.archive is not None else None
                cache = setup_artifact(
                    cache_root,
                    archive_path=archive_path,
                    url=args.url,
                    expected_sha256=expected_archive_sha256,
                )
            output.write(render_setup_summary(cache))
            return 0

        preset = cast(Preset, str(args.preset))
        selection = cast(EvaluationSelection, str(args.evaluation))
        evaluations = expand_evaluations(selection)
        artifact_root = (
            root / ".paper-artifact"
            if args.artifact_dir is None
            else _resolve_path(str(args.artifact_dir), invocation_cwd)
        )
        results_root = (
            root / ".paper-results"
            if args.results_dir is None
            else _resolve_path(str(args.results_dir), invocation_cwd)
        )
        print(f"Verifying paper artifact cache at {artifact_root}", file=diagnostics)
        artifact = verify_artifact_cache(artifact_root, expected_sha256=expected_archive_sha256)
        registry = lane_registry or production_registry(root)
        lanes = registry.lanes_for(preset, evaluations, artifact.artifact_root)
        created_at = clock()
        run_id = str(args.run_id) if args.run_id is not None else _new_run_id(created_at)
        result = run_lanes(
            lanes,
            run_id=run_id,
            preset=preset,
            evaluations=evaluations,
            artifact=artifact,
            results_root=results_root,
            invocation_argv=invocation_argv,
            invocation_cwd=invocation_cwd,
            repo_root=root,
            executor=executor,
            environment=base_environment,
            created_at=created_at,
            report=lambda message: print(message, file=diagnostics),
        )
        output.write(result.summary)
        if result.infrastructure_error:
            return 2
        return 0 if result.success else 1
    except (OSError, ValueError, subprocess.SubprocessError, tarfile.TarError) as error:
        print(f"error: {error}", file=diagnostics)
        return 2


def _resolve_path(raw_path: str, cwd: Path) -> Path:
    path = Path(raw_path).expanduser()
    if not path.is_absolute():
        path = cwd / path
    return path.resolve(strict=False)


def _new_run_id(created_at: datetime) -> str:
    timestamp = created_at.astimezone(UTC).strftime("%Y%m%dT%H%M%SZ")
    return f"{timestamp}-{secrets.token_hex(4)}"
