"""Prove paper cache isolation and preservation of the existing benchmark artifacts."""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path

from paper_benchmarking.hashing import sha256_file
from paper_benchmarking.models import CommandSpec, ProcessLane
from paper_benchmarking.runner import run_lanes

from .paper_fixtures import ROOT, fake_artifact_cache


def test_paper_cache_and_result_roots_are_git_ignored() -> None:
    completed = subprocess.run(
        ("git", "check-ignore", ".paper-artifact/probe", ".paper-build/probe", ".paper-results/probe"),
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
    )

    assert completed.stdout.splitlines() == [
        ".paper-artifact/probe",
        ".paper-build/probe",
        ".paper-results/probe",
    ]


def test_local_lane_does_not_touch_bench_or_default_reports(tmp_path: Path) -> None:
    bench = ROOT / "bench.py"
    reports = ROOT / ".reports.jsonl"
    bench_before = sha256_file(bench)
    reports_before = sha256_file(reports) if reports.exists() else None
    lane = ProcessLane(
        evaluation="math",
        name="scope",
        observations=(
            CommandSpec(
                label="noop",
                argv=(sys.executable, "-c", "pass"),
                cwd=ROOT,
                timeout_sec=2,
            ),
        ),
    )

    result = run_lanes(
        (lane,),
        run_id="scope-run",
        preset="quick",
        evaluations=("math",),
        artifact=fake_artifact_cache(tmp_path / "artifact-cache"),
        results_root=tmp_path / "results",
        invocation_argv=("paper_bench.py", "run", "quick", "math"),
        invocation_cwd=tmp_path,
        repo_root=ROOT,
        machine={"machine": "test", "system": "TestOS"},
        repository={"git_sha": "1" * 40, "is_dirty": False, "root": str(ROOT), "status": []},
    )

    assert result.success
    assert sha256_file(bench) == bench_before
    assert (sha256_file(reports) if reports.exists() else None) == reports_before
