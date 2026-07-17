"""Construct Samply artifacts, summaries, and resolved profile requests for tests."""

from __future__ import annotations

import gzip
import json
from pathlib import Path
from typing import Any

import pytest

from benchmarking import models, samply_analysis
from benchmarking import profile as profile_runner

from .report_fixtures import ROOT, make_target


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
