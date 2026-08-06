"""Test paper CLI parsing, adapter dispatch, and stdout/stderr isolation."""

from __future__ import annotations

import sys
from collections.abc import Sequence
from datetime import UTC, datetime
from pathlib import Path

import pytest

from paper_benchmarking.artifact import setup_artifact
from paper_benchmarking.cli import main, parse_args
from paper_benchmarking.lanes import LaneRegistry
from paper_benchmarking.models import CommandSpec, Preset, ProcessLane

from .paper_fixtures import ROOT, write_artifact_archive


def test_parser_accepts_public_setup_and_run_selections() -> None:
    setup = parse_args(("setup", "--archive", "/tmp/artifact.tar.gz"))
    run = parse_args(("run", "artifact-full", "all", "--run-id", "paper-run"))

    assert setup.command == "setup"
    assert setup.archive == "/tmp/artifact.tar.gz"
    assert run.command == "run"
    assert run.preset == "artifact-full"
    assert run.evaluation == "all"
    assert run.run_id == "paper-run"


def test_setup_dispatch_writes_markdown_to_stdout_and_status_to_stderr(
    tmp_path: Path,
    capsys: pytest.CaptureFixture[str],
) -> None:
    archive = tmp_path / "artifact.tar.gz"
    digest = write_artifact_archive(archive)
    cache = tmp_path / "cache"

    status = main(
        ("setup", "--archive", str(archive), "--cache-dir", str(cache)),
        expected_archive_sha256=digest,
    )
    captured = capsys.readouterr()

    assert status == 0
    assert captured.out.startswith("# Paper Artifact Setup\n")
    assert "Preparing paper artifact cache" in captured.err


def test_run_dispatches_injected_local_lane_and_isolates_child_logs(
    tmp_path: Path,
    capsys: pytest.CaptureFixture[str],
) -> None:
    archive = tmp_path / "artifact.tar.gz"
    digest = write_artifact_archive(archive)
    cache = setup_artifact(tmp_path / "cache", archive_path=archive, expected_sha256=digest)

    def math_lanes(preset: Preset, artifact_root: Path) -> Sequence[ProcessLane]:
        assert preset == "quick"
        assert artifact_root == cache.artifact_root
        return (
            ProcessLane(
                evaluation="math",
                name="fake-cli",
                observations=(
                    CommandSpec(
                        label="local",
                        argv=(
                            sys.executable,
                            "-c",
                            "import sys; print('child-only-stdout'); print('child-only-stderr', file=sys.stderr)",
                        ),
                        cwd=ROOT,
                        timeout_sec=2,
                    ),
                ),
            ),
        )

    result_root = tmp_path / "results"
    status = main(
        (
            "run",
            "quick",
            "math",
            "--artifact-dir",
            str(cache.root),
            "--results-dir",
            str(result_root),
            "--run-id",
            "cli-run",
        ),
        lane_registry=LaneRegistry({"math": math_lanes}),
        now=lambda: datetime(2026, 8, 5, 12, 0, tzinfo=UTC),
        repo_root=ROOT,
        expected_archive_sha256=digest,
    )
    captured = capsys.readouterr()

    assert status == 0
    assert captured.out.startswith("# Paper Artifact Run `cli-run`\n")
    assert "child-only-stdout" not in captured.out
    assert "child-only-stderr" not in captured.err
    assert "Running math/fake-cli observation 1/1" in captured.err
    result_dir = result_root / "cli-run"
    assert captured.out == (result_dir / "summary.md").read_text(encoding="utf-8")
    assert "child-only-stdout" in next((result_dir / "logs").glob("*.stdout.log")).read_text(encoding="utf-8")
    assert "child-only-stderr" in next((result_dir / "logs").glob("*.stderr.log")).read_text(encoding="utf-8")


def test_run_rejects_unimplemented_broad_herbie_preset_before_creating_results(
    tmp_path: Path,
    capsys: pytest.CaptureFixture[str],
) -> None:
    archive = tmp_path / "artifact.tar.gz"
    digest = write_artifact_archive(archive)
    cache = setup_artifact(tmp_path / "cache", archive_path=archive, expected_sha256=digest)
    results = tmp_path / "results"

    status = main(
        (
            "run",
            "representative",
            "herbie",
            "--artifact-dir",
            str(cache.root),
            "--results-dir",
            str(results),
        ),
        expected_archive_sha256=digest,
    )
    captured = capsys.readouterr()

    assert status == 2
    assert captured.out == ""
    assert "supports only the quick preset" in captured.err
    assert not results.exists()
