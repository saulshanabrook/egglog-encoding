"""Provide shared typed records, targets, subprocesses, and profile fixtures."""

from __future__ import annotations

import gzip
import json
import subprocess
from pathlib import Path
from typing import Any

import pytest

from benchmarking import models, samply_analysis, targets
from benchmarking import profile as profile_runner
from benchmarking.reports.database import ReportDatabase
from benchmarking.reports.records import (
    ReportRecord,
    RulesetTimingRecord,
    TimingSummaryRecord,
)

ROOT = Path(__file__).resolve().parents[1]


def make_record(
    _index: int,
    *,
    started_at: str,
    status: models.Status = "success",
    wall_sec: float | None = 1.0,
    max_rss_bytes: int | None = None,
    binary_sha256: str = "sha256:bin",
    file_sha256: str = "sha256:file",
    fact_directory_sha256: str = "",
    backend: models.Backend = "main",
    treatment: models.Treatment = "off",
    timeout_sec: int = 120,
    target_label: str | None = None,
    timing_summary: TimingSummaryRecord | None = None,
) -> ReportRecord:
    if status == "success" and timing_summary is None:
        timing_summary = make_timing_summary()
    return {
        "started_at": started_at,
        "status": status,
        "target_label": target_label,
        "target_source": ".",
        "target_path": str(ROOT),
        "target_git_ref": "HEAD",
        "target_git_sha": "abc123",
        "target_is_dirty": False,
        "binary_sha256": binary_sha256,
        "file_path": "file.egg",
        "file_sha256": file_sha256,
        "fact_directory_path": None,
        "fact_directory_sha256": fact_directory_sha256,
        "backend": backend,
        "treatment": treatment,
        "timeout_sec": timeout_sec,
        "wall_sec": None if status == "timed-out" else wall_sec,
        "max_rss_bytes": None if status == "timed-out" else max_rss_bytes,
        "error_exit_code": None,
        "error_signal": None,
        "error_message": "timed out" if status == "timed-out" else None,
        "timing_summary": timing_summary if status == "success" else None,
    }


def make_ruleset_timing(
    name: str = "rules",
    *,
    search_ns: int = 400_000_000,
    apply_ns: int = 200_000_000,
    unattributed_ns: int = 0,
    merge_ns: int = 200_000_000,
    rebuild_ns: int = 100_000_000,
) -> RulesetTimingRecord:
    """Construct one valid ruleset timing fixture."""

    return {
        "name": name,
        "search_ns": search_ns,
        "apply_ns": apply_ns,
        "unattributed_ns": unattributed_ns,
        "merge_ns": merge_ns,
        "rebuild_ns": rebuild_ns,
    }


def make_timing_summary(*rulesets: RulesetTimingRecord) -> TimingSummaryRecord:
    """Construct a valid v2 timing-summary fixture."""

    return {
        "schema_version": 2,
        "rulesets": list(rulesets or (make_ruleset_timing(),)),
    }


def write_report(path: Path, *records: ReportRecord) -> None:
    """Write deterministic records through the persistent cache boundary."""

    with ReportDatabase(path) as database:
        for record in records:
            database.append(record)


def make_target(
    *,
    target_label: str | None = None,
    binary_sha256: str = "sha256:bin",
    binary_path: Path | None = None,
) -> models.ResolvedTarget:
    return models.ResolvedTarget(
        request=models.TargetRequest(raw=".", source=".", label=target_label),
        row=models.TargetRow(
            source=".",
            path=str(ROOT),
            git_ref="HEAD",
            git_sha="abc123",
            is_dirty=False,
            label=target_label,
        ),
        binary_sha256=binary_sha256,
        binary_path=binary_path,
    )


def make_endpoint(
    *,
    target_label: str | None = None,
    binary_sha256: str = "sha256:bin",
    backend: models.Backend = "main",
    treatment: models.Treatment = "off",
) -> models.BenchmarkEndpoint:
    """Construct one resolved endpoint used by pair-report tests."""

    return models.BenchmarkEndpoint(
        make_target(target_label=target_label, binary_sha256=binary_sha256),
        backend,
        treatment,
    )


def make_profile_data() -> dict[str, Any]:
    return {
        "meta": {"sampleUnits": {"threadCPUDelta": "us"}},
        "libs": [],
        "threads": [],
    }


def make_cpu_profile_data(binary_path: Path) -> dict[str, Any]:
    thread = {
        "stringArray": ["0x10", "system_call", "application", "system"],
        "samples": {
            "length": 4,
            "stack": [0, 0, 1, None],
            "threadCPUDelta": [9_000_000, 100_000, 200_000, 300_000],
        },
        "stackTable": {"length": 2, "frame": [0, 1], "prefix": [None, None]},
        "frameTable": {"length": 2, "address": [0x10, 0x20], "func": [0, 1]},
        "funcTable": {"length": 2, "name": [0, 1], "resource": [0, 1]},
        "resourceTable": {"length": 2, "name": [2, 3], "lib": [0, 1]},
    }
    parked_thread = {
        **thread,
        "samples": {
            "length": 2,
            "stack": [0, 0],
            "threadCPUDelta": [5_000_000, 0],
        },
    }
    return {
        "meta": {"sampleUnits": {"threadCPUDelta": "us"}},
        "libs": [
            {"name": binary_path.name, "path": str(binary_path), "arch": "arm64"},
            {"name": "libsystem_kernel.dylib", "path": "/usr/lib/system/libsystem_kernel.dylib", "arch": "arm64"},
        ],
        "threads": [thread, parked_thread],
    }


def write_profile(path: Path, profile: dict[str, Any] | None = None, *, compressed: bool = True) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    data = make_profile_data() if profile is None else profile
    if compressed:
        with gzip.open(path, "wt", encoding="utf-8") as handle:
            json.dump(data, handle)
    else:
        path.write_text(json.dumps(data), encoding="utf-8")


def make_cpu_summary() -> samply_analysis.ProfileCpuSummary:
    return samply_analysis.ProfileCpuSummary(
        observed_cpu_seconds=1.0,
        application_cpu_seconds=0.8,
        other_library_cpu_seconds=0.15,
        unattributed_cpu_seconds=0.05,
        symbolized_application_cpu_seconds=0.6,
        functions=(
            samply_analysis.ProfileFunctionCpu("first<T>", 0.4),
            samply_analysis.ProfileFunctionCpu("second", 0.2),
        ),
        warnings=(),
    )


def make_dirty_git_repo(path: Path) -> tuple[str, Path]:
    tracked = path / "tracked.txt"
    (path / ".gitignore").write_text("/.bench-worktrees/\n", encoding="utf-8")
    tracked.write_text("committed\n", encoding="utf-8")
    subprocess.run(["git", "init", "--quiet"], cwd=path, check=True)
    subprocess.run(["git", "add", ".gitignore", tracked.name], cwd=path, check=True)
    subprocess.run(
        [
            "git",
            "-c",
            "user.name=Benchmark Test",
            "-c",
            "user.email=benchmark@example.com",
            "commit",
            "--quiet",
            "-m",
            "initial",
        ],
        cwd=path,
        check=True,
    )
    sha = targets.git_sha(path)
    tracked.write_text("dirty\n", encoding="utf-8")
    return (sha, tracked)


def make_profile_case(
    tmp_path: Path,
    *,
    mode: profile_runner.ProfileMode | None = None,
    open_after: bool = False,
    force_run: bool = False,
    top: int = 15,
    show_summary: bool = True,
    output_format: profile_runner.OutputFormat = "rich",
) -> tuple[profile_runner.ProfileRequest, models.ResolvedTarget, Path]:
    file_spec = models.FileSpec("file.egg", ROOT / "file.egg", "sha256:" + "b" * 64)
    request = profile_runner.ProfileRequest(
        file=file_spec,
        target_request=models.TargetRequest(raw=".", source=".", label=None),
        backend="main",
        treatment="proofs",
        timeout_sec=120,
        profiles_dir=tmp_path,
        mode=profile_runner.ProfileMode(None, 10) if mode is None else mode,
        open_after=open_after,
        force_run=force_run,
        top=top,
        show_summary=show_summary,
        output_format=output_format,
    )
    target = make_target(binary_sha256="sha256:" + "a" * 64, binary_path=ROOT / "egglog-experimental")
    artifact = profile_runner.profile_cache_path(
        tmp_path,
        target.binary_sha256,
        file_spec.sha256,
        request.backend,
        request.treatment,
        request.mode,
    )
    return (request, target, artifact)


def mock_profile_resolution(
    monkeypatch: pytest.MonkeyPatch,
    request: profile_runner.ProfileRequest,
    target: models.ResolvedTarget,
) -> None:
    monkeypatch.setattr(profile_runner, "resolve_profile_request", lambda *args: request)
    monkeypatch.setattr(profile_runner, "resolve_profile_target", lambda *args: target)
