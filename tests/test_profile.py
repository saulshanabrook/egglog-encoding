"""Test profile CLI handling, Samply recording, caching, lifecycle, and opening."""

from __future__ import annotations

import argparse
import subprocess
import sys
from collections.abc import Callable
from pathlib import Path
from typing import Any, cast

import pytest
from rich.console import Console

from benchmarking import benchmark, collection, models, processes, samply_analysis, targets
from benchmarking import profile as profile_runner
from benchmarking.reports.store import ReportStore

from .profile_fixtures import (
    make_cpu_summary,
    make_profile_case,
    make_profile_data,
    mock_profile_resolution,
    write_profile,
)
from .report_fixtures import ROOT, make_target


def stable_file_spec(tmp_path: Path) -> models.FileSpec:
    """Create one immutable workload identity for profile lifecycle tests."""

    path = tmp_path / "workload.egg"
    path.write_text("(check (= 1 1))\n", encoding="utf-8")
    return models.FileSpec(path.name, path, targets.sha256_file(path))


def stub_samply_record_process(
    monkeypatch: pytest.MonkeyPatch,
    action: Callable[..., None],
    return_code: int = 0,
) -> None:
    """Run a Samply-record test action through the isolated Popen lifecycle."""

    class FakeProcess:
        pid = 1

        def __init__(self, command: list[str], kwargs: dict[str, Any]) -> None:
            self.command = command
            self.kwargs = kwargs
            self.returncode: int | None = None

        def wait(self, timeout: int | None = None) -> int:
            if self.returncode is None:
                action(self.command, **self.kwargs)
                self.returncode = return_code
            return self.returncode

    def fake_popen(command: list[str], **kwargs: Any) -> FakeProcess:
        assert kwargs["start_new_session"] is True
        return FakeProcess(command, kwargs)

    monkeypatch.setattr(profile_runner, "samply_executable", lambda: "samply")
    monkeypatch.setattr(profile_runner.subprocess, "Popen", fake_popen)
    monkeypatch.setattr(profile_runner, "terminate_process_group", lambda process: process.wait())


def record_profile(
    artifact: Path,
    file_spec: models.FileSpec,
    *,
    iterations: int = 1,
) -> dict[str, Any]:
    """Record with the arguments shared by every Samply lifecycle test."""

    return profile_runner.run_samply_record(
        artifact=artifact,
        file_spec=file_spec,
        name="profile",
        iterations=iterations,
        workload=["workload"],
        checkout_path=ROOT,
        timeout_sec=120,
    )


def test_parse_args_dispatches_profile_without_changing_benchmark_defaults() -> None:
    benchmark_args = benchmark.parse_benchmark_args(["--rounds", "1", "file.egg"])
    profile_args = profile_runner.parse_profile_args(["file.egg"])

    assert benchmark_args.command == "benchmark"
    assert benchmark_args.files == ["file.egg"]
    assert benchmark_args.rounds == 1
    assert benchmark_args.format == "rich"
    assert benchmark_args.treatment == "proofs"
    assert profile_args.command == "profile"
    assert profile_args.file == "file.egg"
    assert profile_args.backend == "main"
    assert profile_args.treatment == "proofs"
    assert profile_args.top == 15
    assert not profile_args.no_summary
    assert profile_args.format == "rich"


def test_profile_main_reports_filesystem_errors(monkeypatch: pytest.MonkeyPatch, capsys: Any) -> None:
    def fail(*_args: object) -> None:
        raise PermissionError("[bold]read-only[/bold] artifact")

    monkeypatch.setattr(profile_runner, "run_profile", fail)

    assert profile_runner.main(["file.egg"]) == 2
    assert "error: [bold]read-only[/bold] artifact" in capsys.readouterr().err


def test_benchmark_and_profile_cli_accept_windows_fact_paths() -> None:
    file = r"C:\bench\file.egg"
    facts = r"D:\facts"
    benchmark_args = benchmark.parse_benchmark_args([file, "--fact-directory", facts])
    profile_args = profile_runner.parse_profile_args([file, "--fact-directory", facts])

    assert benchmark_args.files == [file]
    assert benchmark_args.fact_directory == facts
    assert profile_args.file == file
    assert profile_args.fact_directory == facts


def test_parse_profile_args_accepts_presentation_options() -> None:
    args = profile_runner.parse_profile_args(
        ["file.egg", "--top", "7", "--no-summary", "--format", "markdown", "--open"]
    )

    assert args.top == 7
    assert args.no_summary
    assert args.format == "markdown"
    assert args.open


def test_parse_profile_args_rejects_iterations_with_profile_seconds() -> None:
    with pytest.raises(SystemExit):
        profile_runner.parse_profile_args(["file.egg", "--iterations", "1", "--profile-seconds", "1"])


def test_resolve_profile_request_reuses_backend_treatment_validation(tmp_path: Path) -> None:
    file_path = tmp_path / "file.egg"
    file_path.write_text("(check (= 1 1))\n", encoding="utf-8")
    args = profile_runner.parse_profile_args([str(file_path), "--backend", "dd", "--treatment", "off"])

    with pytest.raises(ValueError, match="backend dd does not support treatment off"):
        profile_runner.resolve_profile_request(args, ROOT)


def test_profile_accepts_explicit_main_proof_extraction(tmp_path: Path) -> None:
    file_path = tmp_path / "file.egg"
    file_path.write_text("(check (= 1 1))\n", encoding="utf-8")
    args = profile_runner.parse_profile_args([str(file_path), "--treatment", "proof-extraction"])

    request = profile_runner.resolve_profile_request(args, ROOT)

    assert request.backend == "main"
    assert request.treatment == "proof-extraction"


def test_target_resolvers_share_materialization_and_select_build_profile(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    request = targets.parse_target(".")
    row = models.TargetRow(".", str(ROOT), "HEAD", "abc123", False)
    target = make_target(binary_path=ROOT / "egglog-experimental")
    materialized: list[models.TargetRequest] = []
    build_profiles: list[targets.BuildProfile] = []
    build_features: list[tuple[str, ...]] = []

    def fake_materialize(
        target_request: models.TargetRequest,
        invocation_cwd: Path,
        repo_root: Path,
    ) -> models.TargetRow:
        materialized.append(target_request)
        return row

    def fake_build(
        target_request: models.TargetRequest,
        target_row: models.TargetRow,
        console: Console,
        build_profile: targets.BuildProfile,
        cargo_features: tuple[str, ...],
    ) -> models.ResolvedTarget:
        assert target_request == request
        assert target_row == row
        build_profiles.append(build_profile)
        build_features.append(cargo_features)
        return target

    monkeypatch.setattr(collection, "materialize_target_request", fake_materialize)
    monkeypatch.setattr(collection, "build_resolved_target", fake_build)
    monkeypatch.setattr(targets, "materialize_target_request", fake_materialize)
    monkeypatch.setattr(targets, "build_resolved_target", fake_build)
    file_spec = models.FileSpec("file.egg", ROOT / "file.egg", "sha256:file")
    endpoint_request = models.EndpointRequest(request, "main", "off")

    benchmark_target = collection.resolve_targets(
        ((request, (endpoint_request,)),),
        cast(ReportStore, object()),
        (file_spec,),
        1,
        120,
        False,
        ROOT,
        ROOT,
        Console(stderr=True),
    )[request]
    profile_target = targets.resolve_profile_target(request, "dd", ROOT, ROOT, Console(stderr=True))

    assert benchmark_target == target
    assert profile_target == target
    assert materialized == [request, request]
    assert build_profiles == ["release", "profiling"]
    assert build_features == [(), ("dd-backend",)]


def test_build_target_uses_profiling_profile(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    commands: list[list[str]] = []
    binary = tmp_path / "target" / "profiling" / "egglog-experimental"
    binary.parent.mkdir(parents=True)
    binary.write_text("binary", encoding="utf-8")
    row = models.TargetRow(
        source=".",
        path=str(tmp_path),
        git_ref="HEAD",
        git_sha="abc123",
        is_dirty=False,
    )

    def fake_run(command: list[str], **kwargs: Any) -> None:
        commands.append(command)

    monkeypatch.setattr(targets.subprocess, "run", fake_run)
    monkeypatch.setattr(targets, "sha256_file", lambda path: "sha256:bin")

    binary_path, binary_sha256 = targets.build_target(row, Console(stderr=True), "profiling")

    assert commands == [["cargo", "build", "--profile", "profiling", "-p", "egglog-experimental"]]
    assert binary_path == binary
    assert binary_sha256 == "sha256:bin"


def test_profile_cache_path_uses_full_binary_and_file_hashes() -> None:
    binary_hash = "sha256:" + "a" * 64
    file_hash = "sha256:" + "b" * 64

    explicit = profile_runner.profile_cache_path(
        Path(".profiles"), binary_hash, file_hash, "main", "proofs", profile_runner.ProfileMode(5, None)
    )
    automatic = profile_runner.profile_cache_path(
        Path(".profiles"),
        binary_hash,
        file_hash,
        "main",
        "proofs",
        profile_runner.ProfileMode(None, 10),
    )

    base = Path(".profiles") / "v3" / ("a" * 64) / ("b" * 64) / "no-facts"
    assert explicit == base / "main-proofs-i5.json.gz"
    assert automatic == base / "main-proofs-auto10s.json.gz"

    data_hash = "sha256:" + "c" * 64
    with_facts = profile_runner.profile_cache_path(
        Path(".profiles"),
        binary_hash,
        file_hash,
        "main",
        "proofs",
        profile_runner.ProfileMode(5, None),
        data_hash,
    )
    assert with_facts == base.parent / ("c" * 64) / "main-proofs-i5.json.gz"


def test_profile_display_path_is_relative_inside_invocation_directory(tmp_path: Path) -> None:
    artifact = tmp_path / ".profiles" / "v1" / "profile.json.gz"

    assert profile_runner.profile_display_path(artifact, tmp_path) == Path(".profiles/v1/profile.json.gz")


def test_calculate_profile_iterations_uses_margin_and_cap() -> None:
    assert profile_runner.calculate_profile_iterations(2.0, 10) == (6, False)
    assert profile_runner.calculate_profile_iterations(20.0, 10) == (1, False)
    assert profile_runner.calculate_profile_iterations(0.00001, 10, max_iterations=7) == (7, True)
    assert profile_runner.calculate_profile_iterations(0.0, 10, max_iterations=7) == (7, True)


def test_samply_record_uses_fixed_flags_and_replaces_artifact(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    artifact = tmp_path / "profile.json.gz"
    artifact.write_bytes(b"old")
    profile = make_profile_data()
    commands: list[list[str]] = []

    def fake_run(command: list[str], **kwargs: Any) -> None:
        commands.append(command)
        assert kwargs["env"]["RUST_LOG"] == "error"
        output = Path(command[command.index("--output") + 1])
        write_profile(output, profile)

    stub_samply_record_process(monkeypatch, fake_run)

    recorded_profile = record_profile(artifact, stable_file_spec(tmp_path), iterations=3)

    assert recorded_profile == profile
    assert artifact.read_bytes()[:2] == b"\x1f\x8b"
    command = commands[0]
    temporary_output = Path(command[command.index("--output") + 1])
    assert temporary_output.name.endswith(".json.gz")
    assert command[:7] == ["samply", "record", "--save-only", "--rate", "1000", "--reuse-threads", "--iteration-count"]
    assert command[command.index("--iteration-count") + 1] == "3"
    assert command[-2:] == ["--", "workload"]


def test_samply_mutated_workload_is_not_promoted(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    artifact = tmp_path / "profile.json.gz"
    artifact.write_bytes(b"old")
    file_spec = stable_file_spec(tmp_path)
    temporary_paths: list[Path] = []

    def fake_run(command: list[str], **kwargs: Any) -> None:
        output = Path(command[command.index("--output") + 1])
        temporary_paths.append(output)
        write_profile(output)
        file_spec.absolute_path.write_text("(check (= 2 2))\n", encoding="utf-8")

    stub_samply_record_process(monkeypatch, fake_run)

    with pytest.raises(ValueError, match=r"workload changed during execution: workload\.egg"):
        record_profile(artifact, file_spec)

    assert artifact.read_bytes() == b"old"
    assert temporary_paths and not temporary_paths[0].exists()


def test_samply_failure_leaves_no_new_artifact(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    artifact = tmp_path / "profile.json.gz"
    temp_artifact = tmp_path / ".profile.tmp-test.json.gz"

    def fake_run(command: list[str], **kwargs: Any) -> None:
        temp_artifact.write_bytes(b"partial")

    monkeypatch.setattr(profile_runner, "profile_temp_path", lambda path: temp_artifact)
    stub_samply_record_process(monkeypatch, fake_run, return_code=1)

    with pytest.raises(subprocess.CalledProcessError):
        record_profile(artifact, stable_file_spec(tmp_path))

    assert not artifact.exists()
    assert not temp_artifact.exists()


def test_samply_timeout_cleans_up_before_propagating(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    artifact = tmp_path / "profile.json.gz"
    artifact.write_bytes(b"old")
    terminated: list[object] = []

    class TimedOutProcess:
        pid = 1
        returncode: int | None = None

        def wait(self, timeout: float | None = None) -> int:
            raise subprocess.TimeoutExpired("samply", timeout if timeout is not None else 0.0)

    process = TimedOutProcess()

    def fake_popen(command: list[str], **kwargs: Any) -> TimedOutProcess:
        assert kwargs["start_new_session"] is True
        return process

    monkeypatch.setattr(profile_runner, "samply_executable", lambda: "samply")
    monkeypatch.setattr(profile_runner.subprocess, "Popen", fake_popen)
    monkeypatch.setattr(profile_runner, "terminate_process_group", terminated.append)

    with pytest.raises(subprocess.TimeoutExpired):
        record_profile(artifact, stable_file_spec(tmp_path))

    assert terminated == [process]
    assert artifact.read_bytes() == b"old"


def test_samply_plain_json_output_is_not_promoted(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    artifact = tmp_path / "profile.json.gz"
    artifact.write_bytes(b"old")
    temporary_paths: list[Path] = []

    def fake_run(command: list[str], **kwargs: Any) -> None:
        output = Path(command[command.index("--output") + 1])
        temporary_paths.append(output)
        write_profile(output, compressed=False)

    stub_samply_record_process(monkeypatch, fake_run)

    with pytest.raises(ValueError, match="gzip"):
        record_profile(artifact, stable_file_spec(tmp_path))

    assert artifact.read_bytes() == b"old"
    assert temporary_paths and not temporary_paths[0].exists()


def test_missing_samply_reports_install_command(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(profile_runner.shutil, "which", lambda name: None)

    with pytest.raises(FileNotFoundError, match="cargo install --locked samply"):
        profile_runner.samply_executable()


def test_open_samply_profile_redirects_viewer_output_and_handles_interrupt(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    artifact = tmp_path / "profile.json.gz"
    calls: list[dict[str, Any]] = []

    def fake_run(command: list[str], **kwargs: Any) -> None:
        calls.append(kwargs)
        raise KeyboardInterrupt

    monkeypatch.setattr(profile_runner, "samply_executable", lambda: "samply")
    monkeypatch.setattr(profile_runner.subprocess, "run", fake_run)

    profile_runner.open_samply_profile(artifact, ROOT)

    assert len(calls) == 1
    call = calls[0]
    assert call["cwd"] == ROOT
    assert call["check"]
    assert call["stdout"] is sys.stderr
    assert call["stderr"] is sys.stderr
    assert "env" not in call


@pytest.mark.parametrize("platform", ["linux", "win32"])
def test_profile_cache_hit_on_non_macos_skips_cpu_summary_and_workload(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
    capsys: Any,
    platform: str,
) -> None:
    request, target, artifact = make_profile_case(tmp_path)
    write_profile(artifact)
    monkeypatch.setattr(profile_runner.sys, "platform", platform)
    mock_profile_resolution(monkeypatch, request, target)
    monkeypatch.setattr(
        profile_runner, "run_command", lambda *args, **kwargs: pytest.fail("calibration should not run")
    )
    monkeypatch.setattr(profile_runner, "run_samply_record", lambda **kwargs: pytest.fail("samply should not run"))
    monkeypatch.setattr(
        samply_analysis,
        "summarize",
        lambda *args, **kwargs: pytest.fail("macOS summary should not run"),
    )

    profile_runner.run_profile(argparse.Namespace(), Console(stderr=True), ROOT, ROOT)

    captured = capsys.readouterr()
    assert captured.out == ""
    assert "Profile Ready" in captured.err
    assert "Artifact" in captured.err
    assert ".json.gz" in captured.err
    assert "CPU Profile Summary" not in captured.err
    assert "samply load" in captured.err
    assert "profiler.firefox.com" not in captured.err
    assert "currently available on macOS only" in captured.err


def test_profile_cache_hit_on_non_macos_prints_markdown_handoff(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
    capsys: Any,
) -> None:
    request, target, artifact = make_profile_case(tmp_path, output_format="markdown")
    write_profile(artifact)
    monkeypatch.setattr(profile_runner.sys, "platform", "linux")
    mock_profile_resolution(monkeypatch, request, target)
    monkeypatch.setattr(samply_analysis, "summarize", lambda *args: pytest.fail("summary should not run"))

    profile_runner.run_profile(argparse.Namespace(), Console(stderr=True), ROOT, ROOT)

    captured = capsys.readouterr()
    assert captured.out.startswith("## Profile Ready\n")
    assert "| Field | Value |" in captured.out
    assert "```shell\nsamply load " in captured.out
    assert "CPU Breakdown" not in captured.out
    assert "currently available on macOS only" in captured.err


def test_profile_cache_hit_on_macos_prints_cpu_summary(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
    capsys: Any,
) -> None:
    request, target, artifact = make_profile_case(tmp_path, top=1)
    write_profile(artifact)
    summary = make_cpu_summary()
    monkeypatch.setattr(profile_runner.sys, "platform", "darwin")
    mock_profile_resolution(monkeypatch, request, target)
    monkeypatch.setattr(samply_analysis, "summarize", lambda profile, binary: summary)

    profile_runner.run_profile(argparse.Namespace(), Console(stderr=True), ROOT, ROOT)

    captured = capsys.readouterr()
    assert captured.out == ""
    assert "CPU Profile Summary" in captured.err
    assert "CPU breakdown" in captured.err
    assert "Observed thread" in captured.err
    assert "Application symbols" in captured.err
    assert "Top functions by self CPU" in captured.err
    assert "first" in captured.err
    assert "second" not in captured.err
    assert "samply load" in captured.err


def test_profile_cache_hit_prints_github_markdown_summary(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
    capsys: Any,
) -> None:
    request, target, artifact = make_profile_case(tmp_path, top=1, output_format="markdown")
    write_profile(artifact)
    monkeypatch.setattr(profile_runner.sys, "platform", "darwin")
    mock_profile_resolution(monkeypatch, request, target)
    monkeypatch.setattr(samply_analysis, "summarize", lambda profile, binary: make_cpu_summary())

    profile_runner.run_profile(argparse.Namespace(), Console(stderr=True), ROOT, ROOT)

    captured = capsys.readouterr()
    assert captured.out.startswith("## CPU Profile Summary\n")
    assert "| Field | Value |" in captured.out
    assert "### CPU Breakdown" in captured.out
    assert "| Metric | CPU | Share |" in captured.out
    assert "### Top Functions by Self CPU" in captured.out
    assert "first" in captured.out
    assert "second" not in captured.out
    assert "```shell\nsamply load " in captured.out
    assert "\x1b[" not in captured.out
    assert not any(character in captured.out for character in "┏┓┗┛━┃")
    assert captured.out.endswith("\n") and not captured.out.endswith("\n\n")
    assert "Profile cache hit" in captured.err


def test_profile_no_summary_prints_only_absolute_artifact_path(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
    capsys: Any,
) -> None:
    request, target, artifact = make_profile_case(
        tmp_path,
        mode=profile_runner.ProfileMode(1, None),
        show_summary=False,
    )
    write_profile(artifact)
    monkeypatch.setattr(profile_runner.sys, "platform", "linux")
    mock_profile_resolution(monkeypatch, request, target)

    profile_runner.run_profile(argparse.Namespace(), Console(stderr=True), ROOT, ROOT)

    captured = capsys.readouterr()
    assert captured.out == f"{artifact.resolve()}\n"
    assert "currently available on macOS only" not in captured.err


def test_profile_cache_hit_can_open_profile(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    request, target, artifact = make_profile_case(
        tmp_path,
        mode=profile_runner.ProfileMode(1, None),
        open_after=True,
        show_summary=False,
    )
    write_profile(artifact)
    opened: list[Path] = []
    mock_profile_resolution(monkeypatch, request, target)
    monkeypatch.setattr(profile_runner, "open_samply_profile", lambda artifact, checkout_path: opened.append(artifact))

    profile_runner.run_profile(argparse.Namespace(), Console(stderr=True), ROOT, ROOT)

    assert opened == [artifact]


def test_profile_explicit_iterations_skip_calibration_and_bypass_cache(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    request, target, artifact = make_profile_case(
        tmp_path,
        mode=profile_runner.ProfileMode(3, None),
        force_run=True,
        show_summary=False,
    )
    artifact.parent.mkdir(parents=True)
    artifact.write_bytes(b"old")
    recorded: list[tuple[Path, int]] = []

    def fake_record(**kwargs: Any) -> dict[str, Any]:
        recorded.append((kwargs["artifact"], kwargs["iterations"]))
        return make_profile_data()

    mock_profile_resolution(monkeypatch, request, target)
    monkeypatch.setattr(
        profile_runner, "run_command", lambda *args, **kwargs: pytest.fail("calibration should not run")
    )
    monkeypatch.setattr(profile_runner, "run_samply_record", fake_record)

    profile_runner.run_profile(argparse.Namespace(), Console(stderr=True), ROOT, ROOT)

    assert recorded == [(artifact, 3)]


def test_profile_auto_calibrates_once_and_uses_derived_iterations(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    request, target, _ = make_profile_case(tmp_path, force_run=True, show_summary=False)
    recorded: list[int] = []

    def fake_record(**kwargs: Any) -> dict[str, Any]:
        recorded.append(kwargs["iterations"])
        return make_profile_data()

    mock_profile_resolution(monkeypatch, request, target)
    monkeypatch.setattr(
        profile_runner,
        "run_command",
        lambda command, checkout_path, timeout_sec: processes.TimingResult(
            "success", processes.TimingRow(wall_sec=2.0), None
        ),
    )
    monkeypatch.setattr(profile_runner, "run_samply_record", fake_record)
    profile_runner.run_profile(argparse.Namespace(), Console(stderr=True), ROOT, ROOT)

    assert recorded == [6]


def test_profile_auto_calibration_failure_stops_before_samply(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    request, target, _ = make_profile_case(tmp_path, force_run=True, show_summary=False)
    mock_profile_resolution(monkeypatch, request, target)
    monkeypatch.setattr(
        profile_runner,
        "run_command",
        lambda command, checkout_path, timeout_sec: processes.TimingResult(
            "timed-out", processes.TimingRow(), processes.ErrorRow("timed out")
        ),
    )
    monkeypatch.setattr(profile_runner, "run_samply_record", lambda **kwargs: pytest.fail("samply should not run"))

    with pytest.raises(ValueError, match="profile calibration failed"):
        profile_runner.run_profile(argparse.Namespace(), Console(stderr=True), ROOT, ROOT)


def test_profile_auto_iteration_cap_prints_warning(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, capsys: Any
) -> None:
    request, target, _ = make_profile_case(tmp_path, force_run=True, show_summary=False)
    mock_profile_resolution(monkeypatch, request, target)
    monkeypatch.setattr(
        profile_runner,
        "run_command",
        lambda command, checkout_path, timeout_sec: processes.TimingResult(
            "success", processes.TimingRow(wall_sec=0.001), None
        ),
    )
    monkeypatch.setattr(
        profile_runner, "calculate_profile_iterations", lambda elapsed_seconds, profile_seconds: (7, True)
    )
    monkeypatch.setattr(profile_runner, "run_samply_record", lambda **kwargs: make_profile_data())

    profile_runner.run_profile(argparse.Namespace(), Console(stderr=True), ROOT, ROOT)

    assert "maximum profile iterations reached" in capsys.readouterr().err


def test_profile_rejects_cache_only_label_targets() -> None:
    with pytest.raises(ValueError, match="cache-only label="):
        targets.resolve_profile_target(targets.parse_target("cached="), "main", ROOT, ROOT, Console(stderr=True))
