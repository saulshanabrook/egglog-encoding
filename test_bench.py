from __future__ import annotations

import argparse
import gzip
import io
import json
import resource
import signal
import subprocess
import sys
from pathlib import Path
from typing import Any

import pandera.errors as pa_errors
import pytest
from rich.console import Console

import bench
import samply_analysis

ROOT = Path(__file__).resolve().parent


def make_record(
    index: int,
    *,
    started_at: str,
    status: bench.Status = "success",
    wall_sec: float | None = 1.0,
    max_rss_bytes: int | None = None,
    binary_sha256: str = "sha256:bin",
    file_sha256: str = "sha256:file",
    backend: bench.Backend = "main",
    treatment: bench.Treatment = "off",
    timeout_sec: int = 120,
    target_label: str | None = None,
) -> dict[str, Any]:
    return {
        "row_index": index,
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
        "backend": backend,
        "treatment": treatment,
        "timeout_sec": timeout_sec,
        "wall_sec": None if status == "timed-out" else wall_sec,
        "user_sec": None,
        "system_sec": None,
        "cpu_wall_ratio": None,
        "max_rss_bytes": None if status == "timed-out" else max_rss_bytes,
        "error_exit_code": None,
        "error_signal": None,
        "error_message": "timed out" if status == "timed-out" else None,
    }


def make_rows(*records: dict[str, Any]) -> bench.DataFrame[bench.ReportFrame]:
    return bench.report_frame_from_records(records)


def make_spec(file_spec: bench.FileSpec) -> bench.BenchmarkSpec:
    return bench.BenchmarkSpec(files=(file_spec,), treatments=("off",), rounds=2, timeout_sec=120)


def make_full_spec(file_spec: bench.FileSpec) -> bench.BenchmarkSpec:
    return bench.BenchmarkSpec(files=(file_spec,), treatments=("off", "term", "proofs"), rounds=2, timeout_sec=120)


def make_target(
    *,
    target_label: str | None = None,
    binary_sha256: str = "sha256:bin",
    binary_path: Path | None = None,
) -> bench.ResolvedTarget:
    return bench.ResolvedTarget(
        request=bench.TargetRequest(raw=".", source=".", label=target_label),
        row=bench.TargetRow(
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
    sha = bench.git_sha(path)
    tracked.write_text("dirty\n", encoding="utf-8")
    return (sha, tracked)


def make_profile_case(
    tmp_path: Path,
    *,
    mode: bench.ProfileMode | None = None,
    open_after: bool = False,
    force_run: bool = False,
    top: int = 15,
    show_summary: bool = True,
    output_format: bench.OutputFormat = "rich",
) -> tuple[bench.ProfileRequest, bench.ResolvedTarget, Path]:
    file_spec = bench.FileSpec("file.egg", ROOT / "file.egg", "sha256:" + "b" * 64)
    request = bench.ProfileRequest(
        file=file_spec,
        target_request=bench.TargetRequest(raw=".", source=".", label=None),
        backend="main",
        treatment="proofs",
        timeout_sec=120,
        profiles_dir=tmp_path,
        mode=bench.ProfileMode(None, 10) if mode is None else mode,
        open_after=open_after,
        force_run=force_run,
        top=top,
        show_summary=show_summary,
        output_format=output_format,
    )
    target = make_target(binary_sha256="sha256:" + "a" * 64, binary_path=ROOT / "egglog-experimental")
    artifact = bench.profile_cache_path(
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
    request: bench.ProfileRequest,
    target: bench.ResolvedTarget,
) -> None:
    monkeypatch.setattr(bench, "resolve_profile_request", lambda *args: request)
    monkeypatch.setattr(bench, "resolve_profile_target", lambda *args: target)


def test_selected_rows_uses_latest_timestamp_then_jsonl_order() -> None:
    rows = make_rows(
        make_record(0, started_at="2026-07-04T12:00:00Z", wall_sec=1.0),
        make_record(1, started_at="2026-07-04T12:00:01Z", wall_sec=2.0),
        make_record(2, started_at="2026-07-04T12:00:01Z", wall_sec=3.0),
    )

    selected = bench.selected_rows(rows, bench.EstimateKey("sha256:bin", "sha256:file", "off", 120), 2)

    assert selected["row_index"].tolist() == [1, 2]


def test_timeout_counts_for_cache_but_invalidates_stats() -> None:
    rows = make_rows(
        make_record(0, started_at="2026-07-04T12:00:00Z", status="timed-out", wall_sec=None),
        make_record(1, started_at="2026-07-04T12:00:01Z", wall_sec=1.0),
    )

    selected = bench.selected_rows(rows, bench.EstimateKey("sha256:bin", "sha256:file", "off", 120), 2)
    summary = bench.summarize_cell(selected, 2)

    assert len(selected) == 2
    assert summary.issue == "timeout row selected"
    assert not summary.ok


def test_ratio_from_samples_reports_fieller_interval() -> None:
    summary = bench.ratio_from_samples(
        [1.00, 1.05, 0.95, 1.02, 0.98],
        [1.45, 1.52, 1.48, 1.50, 1.55],
    )

    assert summary.point == pytest.approx(1.5, rel=0.05)
    assert summary.ci_low is not None
    assert summary.ci_high is not None
    assert summary.point is not None
    assert summary.ci_low < summary.point < summary.ci_high


def test_suite_ratio_sums_fixed_files() -> None:
    baseline_a = bench.summarize_cell(
        make_rows(
            make_record(0, started_at="2026-07-04T12:00:00Z", wall_sec=1.0),
            make_record(1, started_at="2026-07-04T12:00:01Z", wall_sec=1.2),
        ),
        2,
    )
    candidate_a = bench.summarize_cell(
        make_rows(
            make_record(2, started_at="2026-07-04T12:00:00Z", wall_sec=2.0),
            make_record(3, started_at="2026-07-04T12:00:01Z", wall_sec=2.2),
        ),
        2,
    )
    baseline_b = bench.summarize_cell(
        make_rows(
            make_record(4, started_at="2026-07-04T12:00:00Z", wall_sec=3.0),
            make_record(5, started_at="2026-07-04T12:00:01Z", wall_sec=3.2),
        ),
        2,
    )
    candidate_b = bench.summarize_cell(
        make_rows(
            make_record(6, started_at="2026-07-04T12:00:00Z", wall_sec=4.0),
            make_record(7, started_at="2026-07-04T12:00:01Z", wall_sec=4.2),
        ),
        2,
    )

    summary = bench.suite_ratio([(baseline_a, candidate_a), (baseline_b, candidate_b)])

    assert summary.point == pytest.approx((2.1 + 4.1) / (1.1 + 3.1))


def test_target_suite_treatment_ratio_compares_same_treatment_between_targets() -> None:
    base = make_target(target_label="base", binary_sha256="sha256:base")
    candidate = make_target(target_label="candidate", binary_sha256="sha256:candidate")
    file_a = bench.FileSpec("a.egg", ROOT / "a.egg", "sha256:a")
    file_b = bench.FileSpec("b.egg", ROOT / "b.egg", "sha256:b")
    spec = bench.BenchmarkSpec(files=(file_a, file_b), treatments=("off",), rounds=2, timeout_sec=120)
    rows = make_rows(
        make_record(
            0, started_at="2026-07-04T12:00:00Z", binary_sha256="sha256:base", file_sha256="sha256:a", wall_sec=1.0
        ),
        make_record(
            1, started_at="2026-07-04T12:00:01Z", binary_sha256="sha256:base", file_sha256="sha256:a", wall_sec=1.2
        ),
        make_record(
            2, started_at="2026-07-04T12:00:00Z", binary_sha256="sha256:candidate", file_sha256="sha256:a", wall_sec=0.8
        ),
        make_record(
            3, started_at="2026-07-04T12:00:01Z", binary_sha256="sha256:candidate", file_sha256="sha256:a", wall_sec=0.9
        ),
        make_record(
            4, started_at="2026-07-04T12:00:00Z", binary_sha256="sha256:base", file_sha256="sha256:b", wall_sec=3.0
        ),
        make_record(
            5, started_at="2026-07-04T12:00:01Z", binary_sha256="sha256:base", file_sha256="sha256:b", wall_sec=3.2
        ),
        make_record(
            6, started_at="2026-07-04T12:00:00Z", binary_sha256="sha256:candidate", file_sha256="sha256:b", wall_sec=2.4
        ),
        make_record(
            7, started_at="2026-07-04T12:00:01Z", binary_sha256="sha256:candidate", file_sha256="sha256:b", wall_sec=2.5
        ),
    )
    base_cells = bench.target_cell_summaries(rows, base, spec)
    candidate_cells = bench.target_cell_summaries(rows, candidate, spec)

    ratio = bench.target_suite_treatment_ratio(base_cells, candidate_cells, spec, "off")

    assert ratio.point == pytest.approx((0.85 + 2.45) / (1.1 + 3.1))
    assert ratio.ci_low is not None
    assert ratio.ci_high is not None


def test_summary_formatters_show_ranges_when_defined_and_points_otherwise() -> None:
    empty_rows = bench.empty_report_frame()

    assert (
        bench.format_seconds_summary(
            bench.CellSummary(empty_rows, (), {}, mean=1.0, ci_low=0.75, ci_high=1.25, issue=None)
        )
        == "[0.7500s, 1.2500s]"
    )
    assert (
        bench.format_ratio_summary(bench.RatioSummary(point=2.0, ci_low=1.6, ci_high=2.6, issue=None))
        == "[1.600x, 2.600x]"
    )
    assert bench.format_ratio_summary(bench.RatioSummary(point=2.0, ci_low=None, ci_high=None, issue=None)) == "2.000x"
    assert bench.format_bytes(512) == "512 B"
    assert bench.format_bytes(2 * 1024 * 1024) == "2.0 MiB"
    assert (
        bench.format_bytes_summary(
            bench.CellSummary(empty_rows, (), {}, mean=2 * 1024 * 1024, ci_low=None, ci_high=None, issue=None)
        )
        == "2.0 MiB"
    )
    assert (
        bench.format_wall_time_change(bench.RatioSummary(point=0.8, ci_low=0.7, ci_high=0.9, issue=None))
        == "[-30.0%, -10.0%]"
    )
    assert (
        bench.format_wall_time_change(bench.RatioSummary(point=1.25, ci_low=None, ci_high=None, issue=None)) == "25.0%"
    )
    assert (
        bench.format_wall_time_change(bench.RatioSummary(point=None, ci_low=None, ci_high=None, issue="invalid")) == "-"
    )
    assert bench.lower_is_better_result(bench.RatioSummary(point=0.8, ci_low=0.7, ci_high=0.9, issue=None)) == "less"
    assert bench.lower_is_better_result(bench.RatioSummary(point=1.2, ci_low=1.1, ci_high=1.3, issue=None)) == "more"


def test_parse_target_variants() -> None:
    assert bench.parse_target(".") == bench.TargetRequest(raw=".", source=".", label=None)
    assert bench.parse_target("main=@main") == bench.TargetRequest(raw="main=@main", source="@main", label="main")
    assert bench.parse_target("prev-run=") == bench.TargetRequest(raw="prev-run=", source="", label="prev-run")
    assert bench.parse_target("#33") == bench.TargetRequest(raw="#33", source="#33", label="#33")
    assert bench.parse_target("candidate=#33") == bench.TargetRequest(
        raw="candidate=#33", source="#33", label="candidate"
    )


@pytest.mark.parametrize("raw", ["#", "#0", "#abc", "candidate=#0"])
def test_parse_target_rejects_invalid_pr_targets(raw: str) -> None:
    with pytest.raises(ValueError, match="invalid PR target"):
        bench.parse_target(raw)


def test_parse_treatments_rejects_duplicates() -> None:
    with pytest.raises(ValueError, match="duplicate treatment: off"):
        bench.parse_treatments("off,term,off")


def test_parse_backends_accepts_single_and_comma_separated_values() -> None:
    assert bench.parse_backends("main") == ("main",)
    assert bench.parse_backends("main,dd") == ("main", "dd")
    assert bench.parse_backends(" dd , main ") == ("dd", "main")


def test_parse_backends_rejects_duplicates_unknowns_and_empty_values() -> None:
    with pytest.raises(ValueError, match="duplicate backend: main"):
        bench.parse_backends("main,dd,main")
    with pytest.raises(ValueError, match="unknown backend: bogus"):
        bench.parse_backends("bogus")
    with pytest.raises(ValueError, match="at least one backend"):
        bench.parse_backends(",,")


def test_backend_registry_drives_parsing_capabilities_flags_and_display(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setitem(
        bench.BACKEND_SPECS,
        "future",
        bench.BackendSpec("Future", ("proofs",), ("--backend", "future"), ("future-backend",)),
    )

    assert bench.parse_backends("future") == ("future",)
    assert bench.supported_treatments("future") == ("proofs",)
    assert bench.backend_flags("future") == ["--backend", "future"]
    assert bench.backend_cargo_features(("main", "future")) == ("future-backend",)
    assert bench.display_backend("future") == "Future"
    assert bench.backend_treatment_cells(("future",), ("off", "proofs")) == (bench.BenchmarkCell("future", "proofs"),)


def test_parse_args_dispatches_profile_without_changing_benchmark_defaults() -> None:
    benchmark_args = bench.parse_args(["--rounds", "1", "file.egg"])
    profile_args = bench.parse_args(["profile", "file.egg"])

    assert benchmark_args.command == "benchmark"
    assert benchmark_args.files == ["file.egg"]
    assert benchmark_args.rounds == 1
    assert benchmark_args.format == "rich"
    assert profile_args.command == "profile"
    assert profile_args.file == "file.egg"
    assert profile_args.backend == "main"
    assert profile_args.treatment == "proofs"
    assert profile_args.top == 15
    assert not profile_args.no_summary
    assert profile_args.format == "rich"


def test_parse_profile_args_accepts_presentation_options() -> None:
    args = bench.parse_args(["profile", "file.egg", "--top", "7", "--no-summary", "--format", "markdown", "--open"])

    assert args.top == 7
    assert args.no_summary
    assert args.format == "markdown"
    assert args.open


def test_parse_args_rejects_markdown_report_dash() -> None:
    with pytest.raises(SystemExit):
        bench.parse_args(["--format", "markdown", "--report", "-", "file.egg"])


def test_parse_profile_args_rejects_iterations_with_profile_seconds() -> None:
    with pytest.raises(SystemExit):
        bench.parse_args(["profile", "file.egg", "--iterations", "1", "--profile-seconds", "1"])


def test_benchmark_cells_filter_off_for_non_main_backends() -> None:
    file_spec = bench.FileSpec("file.egg", ROOT / "file.egg", "sha256:file")
    spec = bench.BenchmarkSpec(
        files=(file_spec,),
        treatments=("off", "term", "proofs"),
        rounds=1,
        timeout_sec=120,
        backends=("main", "dd"),
    )

    assert bench.benchmark_cells(spec) == (
        bench.BenchmarkCell("main", "off"),
        bench.BenchmarkCell("main", "term"),
        bench.BenchmarkCell("main", "proofs"),
        bench.BenchmarkCell("dd", "term"),
        bench.BenchmarkCell("dd", "proofs"),
    )


def test_validate_spec_rejects_backend_with_no_supported_treatments() -> None:
    file_spec = bench.FileSpec("file.egg", ROOT / "file.egg", "sha256:file")
    spec = bench.BenchmarkSpec(
        files=(file_spec,),
        treatments=("off",),
        rounds=1,
        timeout_sec=120,
        backends=("dd",),
    )

    with pytest.raises(ValueError, match="backend dd has no supported treatments"):
        bench.validate_spec(spec)


def test_resolve_profile_request_reuses_backend_treatment_validation(tmp_path: Path) -> None:
    file_path = tmp_path / "file.egg"
    file_path.write_text("(check (= 1 1))\n", encoding="utf-8")
    args = bench.parse_args(["profile", str(file_path), "--backend", "dd", "--treatment", "off"])

    with pytest.raises(ValueError, match="backend dd has no supported treatments"):
        bench.resolve_profile_request(args, ROOT)


def test_validate_spec_rejects_executable_prove_benchmark_file(tmp_path: Path) -> None:
    prove_file = tmp_path / "prove.egg"
    prove_file.write_text(
        "; comments may mention (prove ...)\n(datatype Expr)\n(prove (Fact))\n",
        encoding="utf-8",
    )
    spec = bench.BenchmarkSpec(
        files=bench.resolve_files([str(prove_file)], tmp_path),
        treatments=("off", "term", "proofs"),
        rounds=1,
        timeout_sec=120,
    )

    with pytest.raises(ValueError, match="explicit prove command"):
        bench.validate_spec(spec)


def test_validate_spec_allows_prove_mentions_in_comments(tmp_path: Path) -> None:
    check_file = tmp_path / "check.egg"
    check_file.write_text(
        "; comments may mention (prove ...)\n(datatype Expr)\n(check (Fact))\n",
        encoding="utf-8",
    )
    spec = bench.BenchmarkSpec(
        files=bench.resolve_files([str(check_file)], tmp_path),
        treatments=("off", "term", "proofs"),
        rounds=1,
        timeout_sec=120,
    )

    bench.validate_spec(spec)


def test_default_files_use_dd_safe_math_microbenchmark() -> None:
    display_paths = tuple(file.display_path for file in bench.resolve_files([], ROOT))

    assert "egglog/tests/math-microbenchmark-mini.egg" in display_paths
    assert "egglog/tests/math-microbenchmark.egg" not in display_paths


def test_estimate_model_is_exact_only_and_updates_from_successful_processes() -> None:
    rows = make_rows(
        make_record(0, started_at="2026-07-04T12:00:00Z", wall_sec=2.0),
        make_record(1, started_at="2026-07-04T12:00:01Z", wall_sec=50.0, binary_sha256="sha256:other"),
        make_record(2, started_at="2026-07-04T12:00:02Z", status="timed-out", wall_sec=None),
    )
    model = bench.EstimateModel.from_rows(rows)
    exact_key = bench.EstimateKey("sha256:bin", "sha256:file", "off", 120)
    other_timeout_key = bench.EstimateKey("sha256:bin", "sha256:file", "off", 60)

    assert model.process_mean(exact_key) == pytest.approx(2.0)
    assert model.estimate_processes(exact_key, 3) == bench.DurationEstimate(seconds=6.0, unknown_processes=0)
    assert model.estimate_processes(other_timeout_key, 3) == bench.DurationEstimate(seconds=None, unknown_processes=3)

    model.record_process(exact_key, bench.TimingResult("success", bench.TimingRow(wall_sec=4.0), None))

    assert model.process_mean(exact_key) == pytest.approx(3.0)


def test_materialize_pr_target_fetches_origin_pull_ref(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    calls: list[list[str]] = []

    def fake_run(
        args: list[str],
        *,
        cwd: Path,
        check: bool,
        stdout: Any | None = None,
        stderr: Any | None = None,
    ) -> None:
        calls.append(args)
        assert cwd == tmp_path
        assert check
        assert stdout is sys.stderr
        assert stderr is sys.stderr

    def fake_git_sha(cwd: Path, ref: str = "HEAD") -> str:
        assert cwd in {tmp_path, tmp_path / ".bench-worktrees" / "33"}
        if ref == "refs/remotes/origin/pr/33":
            return "abc123"
        if ref == "HEAD":
            return "abc123"
        raise AssertionError(f"unexpected ref: {ref}")

    monkeypatch.setattr(bench.subprocess, "run", fake_run)
    monkeypatch.setattr(bench, "git_sha", fake_git_sha)
    monkeypatch.setattr(bench, "find_clean_worktree_for_sha", lambda repo, sha: None)

    checkout_path, sha = bench.materialize_pr_target(tmp_path, "#33", "#33")

    assert checkout_path == tmp_path / ".bench-worktrees" / "33"
    assert sha == "abc123"
    assert calls == [
        ["git", "fetch", "origin", "+refs/pull/33/head:refs/remotes/origin/pr/33"],
        ["git", "worktree", "add", "--detach", str(tmp_path / ".bench-worktrees" / "33"), "abc123"],
    ]


@pytest.mark.parametrize("source", ["@HEAD", "#33"])
def test_explicit_git_sources_isolate_dirty_matching_worktree(
    source: str,
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    sha, _ = make_dirty_git_repo(tmp_path)

    if source == "#33":

        def fake_fetch_pr_ref(repo: Path, number: int) -> str:
            assert repo == tmp_path
            assert number == 33
            return "HEAD"

        monkeypatch.setattr(bench, "fetch_pr_ref", fake_fetch_pr_ref)

    row = bench.materialize_target_request(bench.parse_target(source), tmp_path, tmp_path)
    checkout = Path(row.path)

    assert checkout != tmp_path.resolve()
    assert row.git_sha == sha
    assert not row.is_dirty
    assert (checkout / "tracked.txt").read_text(encoding="utf-8") == "committed\n"


@pytest.mark.parametrize("use_absolute_path", [False, True])
def test_path_targets_retain_dirty_checkout(use_absolute_path: bool, tmp_path: Path) -> None:
    sha, tracked = make_dirty_git_repo(tmp_path)
    source = str(tmp_path) if use_absolute_path else "."

    row = bench.materialize_target_request(bench.parse_target(source), tmp_path, tmp_path)

    assert Path(row.path) == tmp_path.resolve()
    assert row.git_ref == "HEAD"
    assert row.git_sha == sha
    assert row.is_dirty
    assert tracked.read_text(encoding="utf-8") == "dirty\n"


def test_target_resolvers_share_materialization_and_select_build_profile(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    request = bench.parse_target(".")
    row = bench.TargetRow(".", str(ROOT), "HEAD", "abc123", False)
    target = make_target(binary_path=ROOT / "egglog-experimental")
    materialized: list[bench.TargetRequest] = []
    build_profiles: list[bench.BuildProfile] = []
    build_features: list[tuple[str, ...]] = []

    def fake_materialize(
        target_request: bench.TargetRequest,
        invocation_cwd: Path,
        repo_root: Path,
    ) -> bench.TargetRow:
        materialized.append(target_request)
        return row

    def fake_build(
        target_request: bench.TargetRequest,
        target_row: bench.TargetRow,
        output: bench.RunnerOutput,
        build_profile: bench.BuildProfile,
        cargo_features: tuple[str, ...],
    ) -> bench.ResolvedTarget:
        assert target_request == request
        assert target_row == row
        build_profiles.append(build_profile)
        build_features.append(cargo_features)
        return target

    monkeypatch.setattr(bench, "materialize_target_request", fake_materialize)
    monkeypatch.setattr(bench, "build_resolved_target", fake_build)
    file_spec = bench.FileSpec("file.egg", ROOT / "file.egg", "sha256:file")

    benchmark_target = bench.resolve_target(
        request,
        bench.empty_report_frame(),
        make_spec(file_spec),
        False,
        ROOT,
        ROOT,
        bench.RunnerOutput(),
    )
    profile_target = bench.resolve_profile_target(request, "dd", ROOT, ROOT, bench.RunnerOutput())

    assert benchmark_target == target
    assert profile_target == target
    assert materialized == [request, request]
    assert build_profiles == ["release", "profiling"]
    assert build_features == [(), ("dd-backend",)]


def test_collection_plan_counts_cache_and_missing_rows() -> None:
    rows = make_rows(make_record(0, started_at="2026-07-04T12:00:00Z", wall_sec=1.0))
    target = make_target()
    file_spec = bench.FileSpec("file.egg", ROOT / "file.egg", "sha256:file")
    spec = make_spec(file_spec)

    plan = bench.build_collection_plan(rows, target, spec, False)
    force_plan = bench.build_collection_plan(rows, target, spec, True)

    assert plan.cells[0].selected_cached_rows["row_index"].tolist() == [0]
    assert plan.cells[0].missing_observations == 1
    assert plan.total_planned_processes == 2
    assert force_plan.cells[0].missing_observations == 2
    assert force_plan.total_planned_processes == 3


def test_collection_plan_does_not_reuse_main_rows_for_dd() -> None:
    rows = make_rows(make_record(0, started_at="2026-07-04T12:00:00Z", backend="main", treatment="term", wall_sec=1.0))
    target = make_target()
    file_spec = bench.FileSpec("file.egg", ROOT / "file.egg", "sha256:file")
    spec = bench.BenchmarkSpec(
        files=(file_spec,),
        treatments=("term",),
        rounds=1,
        timeout_sec=120,
        backends=("main", "dd"),
    )

    plan = bench.build_collection_plan(rows, target, spec, False)

    main_cell, dd_cell = plan.cells
    assert main_cell.backend == "main"
    assert main_cell.missing_observations == 0
    assert dd_cell.backend == "dd"
    assert dd_cell.missing_observations == 1


def test_parse_args_rejects_removed_output_mode() -> None:
    with pytest.raises(SystemExit):
        bench.parse_args(["--output", "jsonl"])


def test_parse_args_rejects_removed_warmup_mode() -> None:
    with pytest.raises(SystemExit):
        bench.parse_args(["--warmup", "0"])


def test_collection_plan_writes_human_output_to_stderr(monkeypatch: pytest.MonkeyPatch) -> None:
    rows = make_rows(make_record(0, started_at="2026-07-04T12:00:00Z", wall_sec=1.0))
    target = make_target()
    file_spec = bench.FileSpec("file.egg", ROOT / "file.egg", "sha256:file")
    plan = bench.build_collection_plan(rows, target, make_spec(file_spec), False)
    stream = io.StringIO()
    monkeypatch.setattr(sys, "stderr", stream)
    output = bench.RunnerOutput()

    bench.emit_collection_plan(output, plan, bench.EstimateModel.from_rows(rows))

    output_text = stream.getvalue()
    assert "cache and estimate plan" in output_text
    assert "file.egg" in output_text
    assert "1/2" in output_text
    assert "Estimated fresh collection time" in output_text


def test_render_report_omits_empty_issue_column() -> None:
    rows = make_rows(make_record(0, started_at="2026-07-04T12:00:00Z", wall_sec=1.0))
    target = make_target()
    file_spec = bench.FileSpec("file.egg", ROOT / "file.egg", "sha256:file")
    stream = io.StringIO()
    console = Console(file=stream, width=200, color_system=None)

    bench.render_report(
        console,
        bench.ReportDestination(path=None, stream=io.StringIO()),
        rows,
        [target],
        bench.BenchmarkSpec(files=(file_spec,), treatments=("off",), rounds=1, timeout_sec=120),
    )

    assert "Issue" not in stream.getvalue()


def test_render_report_puts_single_target_summary_after_diagnostics() -> None:
    rows = make_rows(
        make_record(0, started_at="2026-07-04T12:00:00Z", treatment="off", wall_sec=1.0),
        make_record(1, started_at="2026-07-04T12:00:01Z", treatment="off", wall_sec=1.1),
        make_record(2, started_at="2026-07-04T12:00:00Z", treatment="proofs", wall_sec=2.0),
        make_record(3, started_at="2026-07-04T12:00:01Z", treatment="proofs", wall_sec=2.1),
    )
    target = make_target()
    file_spec = bench.FileSpec("file.egg", ROOT / "file.egg", "sha256:file")
    stream = io.StringIO()
    console = Console(file=stream, width=200, color_system=None)

    bench.render_report(
        console,
        bench.ReportDestination(path=None, stream=io.StringIO()),
        rows,
        [target],
        bench.BenchmarkSpec(files=(file_spec,), treatments=("off", "proofs"), rounds=2, timeout_sec=120),
    )

    output = stream.getvalue()
    assert "Outcome" not in output
    assert output.index("overhead ratios") < output.index("per-file wall time")
    assert output.index("per-file wall time") < output.index("Benchmark summary")
    assert "wall proofs/off" in output
    assert "peak RSS proofs/off" in output


def test_render_report_compares_multiple_targets_before_bottom_summary() -> None:
    rows = make_rows(
        make_record(0, started_at="2026-07-04T12:00:00Z", binary_sha256="sha256:base", treatment="off", wall_sec=1.0),
        make_record(1, started_at="2026-07-04T12:00:01Z", binary_sha256="sha256:base", treatment="off", wall_sec=1.1),
        make_record(2, started_at="2026-07-04T12:00:00Z", binary_sha256="sha256:base", treatment="term", wall_sec=1.5),
        make_record(3, started_at="2026-07-04T12:00:01Z", binary_sha256="sha256:base", treatment="term", wall_sec=1.6),
        make_record(
            4, started_at="2026-07-04T12:00:00Z", binary_sha256="sha256:base", treatment="proofs", wall_sec=2.0
        ),
        make_record(
            5, started_at="2026-07-04T12:00:01Z", binary_sha256="sha256:base", treatment="proofs", wall_sec=2.1
        ),
        make_record(
            6, started_at="2026-07-04T12:00:00Z", binary_sha256="sha256:candidate", treatment="off", wall_sec=0.8
        ),
        make_record(
            7, started_at="2026-07-04T12:00:01Z", binary_sha256="sha256:candidate", treatment="off", wall_sec=0.9
        ),
        make_record(
            8, started_at="2026-07-04T12:00:00Z", binary_sha256="sha256:candidate", treatment="term", wall_sec=1.2
        ),
        make_record(
            9, started_at="2026-07-04T12:00:01Z", binary_sha256="sha256:candidate", treatment="term", wall_sec=1.3
        ),
        make_record(
            10, started_at="2026-07-04T12:00:00Z", binary_sha256="sha256:candidate", treatment="proofs", wall_sec=1.7
        ),
        make_record(
            11, started_at="2026-07-04T12:00:01Z", binary_sha256="sha256:candidate", treatment="proofs", wall_sec=1.8
        ),
    )
    baseline = make_target(target_label="base", binary_sha256="sha256:base")
    candidate = make_target(target_label="candidate", binary_sha256="sha256:candidate")
    file_spec = bench.FileSpec("file.egg", ROOT / "file.egg", "sha256:file")
    stream = io.StringIO()
    console = Console(file=stream, width=220, color_system=None)

    bench.render_report(
        console,
        bench.ReportDestination(path=None, stream=io.StringIO()),
        rows,
        [baseline, candidate],
        make_full_spec(file_spec),
    )

    output = stream.getvalue()
    assert "target / base" in output
    assert "Per-file wall-time change vs base" in output
    assert "Wall-time summary vs base" in output
    assert "Peak RSS summary vs base" in output
    assert "Suite ratio" not in output
    assert "Target comparison" not in output
    assert output.index("Per-file wall-time change vs base") < output.index("base: per-file wall time")
    assert output.index("base: per-file wall time") < output.index("Benchmark summary")


def test_render_report_compares_backends_for_single_target() -> None:
    rows = make_rows(
        make_record(0, started_at="2026-07-04T12:00:00Z", backend="main", treatment="term", wall_sec=1.0),
        make_record(1, started_at="2026-07-04T12:00:01Z", backend="main", treatment="term", wall_sec=1.1),
        make_record(2, started_at="2026-07-04T12:00:00Z", backend="dd", treatment="term", wall_sec=2.0),
        make_record(3, started_at="2026-07-04T12:00:01Z", backend="dd", treatment="term", wall_sec=2.1),
    )
    target = make_target()
    file_spec = bench.FileSpec("file.egg", ROOT / "file.egg", "sha256:file")
    stream = io.StringIO()
    console = Console(file=stream, width=240, color_system=None)

    bench.render_report(
        console,
        bench.ReportDestination(path=None, stream=io.StringIO()),
        rows,
        [target],
        bench.BenchmarkSpec(
            files=(file_spec,),
            treatments=("term",),
            rounds=2,
            timeout_sec=120,
            backends=("main", "dd"),
        ),
    )

    output = stream.getvalue()
    assert "Per-file backend wall-time change vs main" in output
    assert "DD vs main wall time" in output
    assert "DD/main" in output
    assert "Best file" in output
    assert "Best ratio" in output
    assert "Faster files" in output
    assert "main/term" in output
    assert "dd/term" in output
    assert "dd/off" not in output
    assert "1.952x" in output
    assert output.index("DD vs main wall time") < output.index("proof overhead summary")


def test_render_report_backend_summary_highlights_best_file() -> None:
    records: list[dict[str, Any]] = []

    def add_cell(
        *,
        file_sha256: str,
        backend: bench.Backend,
        wall_sec: float,
        max_rss_bytes: int,
    ) -> None:
        for _ in range(2):
            records.append(
                make_record(
                    len(records),
                    started_at=f"2026-07-04T12:00:{len(records):02d}Z",
                    file_sha256=file_sha256,
                    backend=backend,
                    treatment="term",
                    wall_sec=wall_sec,
                    max_rss_bytes=max_rss_bytes,
                )
            )

    mib = 1024 * 1024
    add_cell(file_sha256="sha256:slow", backend="main", wall_sec=1.0, max_rss_bytes=100 * mib)
    add_cell(file_sha256="sha256:slow", backend="dd", wall_sec=2.0, max_rss_bytes=200 * mib)
    add_cell(file_sha256="sha256:fast", backend="main", wall_sec=1.0, max_rss_bytes=100 * mib)
    add_cell(file_sha256="sha256:fast", backend="dd", wall_sec=0.5, max_rss_bytes=80 * mib)
    rows = make_rows(*records)
    target = make_target()
    slow_file = bench.FileSpec("slow.egg", ROOT / "slow.egg", "sha256:slow")
    fast_file = bench.FileSpec("fast.egg", ROOT / "fast.egg", "sha256:fast")
    stream = io.StringIO()
    console = Console(file=stream, width=260, color_system=None)

    bench.render_report(
        console,
        bench.ReportDestination(path=None, stream=io.StringIO()),
        rows,
        [target],
        bench.BenchmarkSpec(
            files=(slow_file, fast_file),
            treatments=("term",),
            rounds=2,
            timeout_sec=120,
            backends=("main", "dd"),
        ),
    )

    output = stream.getvalue()
    assert "DD vs main wall time" in output
    assert "DD vs main peak RSS" in output
    assert "Faster files" in output
    assert "Lower-RSS files" in output
    assert "fast.egg" in output
    assert "1/2" in output
    assert "1.250x" in output
    assert "0.500x" in output
    assert "0.800x" in output


def test_render_report_compares_proofs_only_targets_with_percent_change() -> None:
    rows = make_rows(
        make_record(
            0, started_at="2026-07-04T12:00:00Z", binary_sha256="sha256:base", treatment="proofs", wall_sec=2.0
        ),
        make_record(
            1, started_at="2026-07-04T12:00:00Z", binary_sha256="sha256:candidate", treatment="proofs", wall_sec=1.0
        ),
    )
    baseline = make_target(target_label="base", binary_sha256="sha256:base")
    candidate = make_target(target_label="candidate", binary_sha256="sha256:candidate")
    file_spec = bench.FileSpec("file.egg", ROOT / "file.egg", "sha256:file")
    stream = io.StringIO()
    console = Console(file=stream, width=220, color_system=None)

    bench.render_report(
        console,
        bench.ReportDestination(path=None, stream=io.StringIO()),
        rows,
        [baseline, candidate],
        bench.BenchmarkSpec(files=(file_spec,), treatments=("proofs",), rounds=1, timeout_sec=120),
    )

    output = stream.getvalue()
    assert "Wall-time summary vs base" in output
    assert "proofs" in output
    assert "0.500x" in output
    assert "-50.0%" in output
    assert "Wall-time change" in output
    assert "<2x proof gate" not in output
    assert "Outcome" not in output


def test_render_report_compares_peak_rss_separately() -> None:
    rows = make_rows(
        make_record(
            0,
            started_at="2026-07-04T12:00:00Z",
            binary_sha256="sha256:base",
            treatment="proofs",
            wall_sec=2.0,
            max_rss_bytes=100 * 1024 * 1024,
        ),
        make_record(
            1,
            started_at="2026-07-04T12:00:01Z",
            binary_sha256="sha256:base",
            treatment="proofs",
            wall_sec=2.0,
            max_rss_bytes=100 * 1024 * 1024,
        ),
        make_record(
            2,
            started_at="2026-07-04T12:00:00Z",
            binary_sha256="sha256:candidate",
            treatment="proofs",
            wall_sec=1.0,
            max_rss_bytes=80 * 1024 * 1024,
        ),
        make_record(
            3,
            started_at="2026-07-04T12:00:01Z",
            binary_sha256="sha256:candidate",
            treatment="proofs",
            wall_sec=1.0,
            max_rss_bytes=80 * 1024 * 1024,
        ),
    )
    baseline = make_target(target_label="base", binary_sha256="sha256:base")
    candidate = make_target(target_label="candidate", binary_sha256="sha256:candidate")
    file_spec = bench.FileSpec("file.egg", ROOT / "file.egg", "sha256:file")
    stream = io.StringIO()
    console = Console(file=stream, width=240, color_system=None)

    bench.render_report(
        console,
        bench.ReportDestination(path=None, stream=io.StringIO()),
        rows,
        [baseline, candidate],
        bench.BenchmarkSpec(files=(file_spec,), treatments=("proofs",), rounds=2, timeout_sec=120),
    )

    output = stream.getvalue()
    assert "Per-file peak RSS change vs base" in output
    assert "Peak RSS summary vs base" in output
    assert "0.800x" in output
    assert "[-20.0%, -20.0%]" in output
    assert "less" in output
    assert output.index("Per-file wall-time change vs base") < output.index("Per-file peak RSS change vs base")
    assert output.index("Per-file peak RSS change vs base") < output.index("Benchmark summary")


def test_render_report_single_target_proofs_only_omits_proof_gate() -> None:
    rows = make_rows(make_record(0, started_at="2026-07-04T12:00:00Z", treatment="proofs", wall_sec=1.0))
    target = make_target()
    file_spec = bench.FileSpec("file.egg", ROOT / "file.egg", "sha256:file")
    stream = io.StringIO()
    console = Console(file=stream, width=200, color_system=None)

    bench.render_report(
        console,
        bench.ReportDestination(path=None, stream=io.StringIO()),
        rows,
        [target],
        bench.BenchmarkSpec(files=(file_spec,), treatments=("proofs",), rounds=1, timeout_sec=120),
    )

    output = stream.getvalue()
    assert "file.egg" in output
    assert "<2x proof gate" not in output
    assert "Benchmark summary" in output
    assert "no proof baseline" in output


def test_render_report_marks_invalid_multi_target_wall_time_cells() -> None:
    rows = make_rows(
        make_record(0, started_at="2026-07-04T12:00:00Z", binary_sha256="sha256:base", wall_sec=1.0),
        make_record(1, started_at="2026-07-04T12:00:01Z", binary_sha256="sha256:base", wall_sec=1.1),
        make_record(
            2, started_at="2026-07-04T12:00:00Z", binary_sha256="sha256:candidate", status="timed-out", wall_sec=None
        ),
        make_record(3, started_at="2026-07-04T12:00:01Z", binary_sha256="sha256:candidate", wall_sec=1.2),
    )
    baseline = make_target(target_label="base", binary_sha256="sha256:base")
    candidate = make_target(target_label="candidate", binary_sha256="sha256:candidate")
    file_spec = bench.FileSpec("file.egg", ROOT / "file.egg", "sha256:file")
    stream = io.StringIO()
    console = Console(file=stream, width=220, color_system=None)

    bench.render_report(
        console,
        bench.ReportDestination(path=None, stream=io.StringIO()),
        rows,
        [baseline, candidate],
        make_spec(file_spec),
    )

    output = stream.getvalue()
    assert "invalid: timeout row selected" in output
    assert "off" in output


def test_markdown_escape_cell_handles_pipes_backslashes_and_multiline() -> None:
    assert bench.markdown_escape_cell("a|b\\c\r\nnext\nlast") == "a\\|b\\\\c<br>next<br>last"


def test_render_markdown_table_uses_github_pipe_table() -> None:
    table = bench.ReportTableData(
        title="Example",
        headers=("A|B", "Count"),
        rows=(("x\\y", "one\ntwo"),),
        caption="caption | text",
        alignments=("left", "right"),
    )

    output = bench.render_markdown_table(table)

    assert output == ("### Example\n\n| A\\|B | Count |\n| --- | ---: |\n| x\\\\y | one<br>two |\n\n*caption \\| text*")


def test_benchmark_command_block_uses_fixed_entrypoint_and_shell_quoting() -> None:
    assert bench.benchmark_command_block(("--report", "/tmp/report path.jsonl", "pipe|file.egg")) == (
        "```shell\n$ ./bench.py --report '/tmp/report path.jsonl' 'pipe|file.egg'\n```"
    )


def test_render_markdown_report_deterministic_golden() -> None:
    rows = make_rows(make_record(0, started_at="2026-07-04T12:00:00Z", wall_sec=1.0))
    target = make_target()
    file_spec = bench.FileSpec("dir/file.egg", ROOT / "file.egg", "sha256:file")

    output = bench.render_markdown_report(
        bench.ReportDestination(path=Path("reports.jsonl")),
        rows,
        [target],
        bench.BenchmarkSpec(files=(file_spec,), treatments=("off",), rounds=1, timeout_sec=120),
        ("--rounds", "1", "--format", "markdown", "dir/file.egg"),
    )

    assert output == (
        "```shell\n"
        "$ ./bench.py --rounds 1 --format markdown dir/file.egg\n"
        "```\n"
        "\n"
        "# Benchmark Report\n"
        "\n"
        "- Report: `reports.jsonl`\n"
        "- Selected rows per cell: `1`\n"
        "\n"
        "## Targets\n"
        "\n"
        "| Role | Label | Git | Dirty | Binary | Path |\n"
        "| --- | --- | --- | --- | --- | --- |\n"
        f"| target | abc123 | abc123 | no | bin | {ROOT} |\n"
        "\n"
        "## Target Diagnostics\n"
        "\n"
        "### abc123: per-file wall time\n"
        "\n"
        "| File | off |\n"
        "| --- | ---: |\n"
        "| dir/file.egg | 1.0000s |\n"
        "\n"
        "*Within-target wall-time estimates. These are not target-vs-baseline ratios.*\n"
        "\n"
        "## Benchmark Summary\n"
        "\n"
        "### abc123: proof overhead summary\n"
        "\n"
        "| Metric | Ratio | Change | Worst file | Worst ratio | Result |\n"
        "| --- | ---: | ---: | --- | ---: | --- |\n"
        "| no proof baseline | - | - | - | - | select off and proofs |\n"
        "\n"
        "*Within-backend proof overhead. This is not backend-vs-main performance.*"
    )


def test_markdown_report_has_no_rich_markup_ansi_or_box_drawing() -> None:
    rows = make_rows(make_record(0, started_at="2026-07-04T12:00:00Z", wall_sec=1.0))
    target = make_target()
    file_spec = bench.FileSpec("file.egg", ROOT / "file.egg", "sha256:file")

    output = bench.render_markdown_report(
        bench.ReportDestination(path=Path("reports.jsonl")),
        rows,
        [target],
        bench.BenchmarkSpec(files=(file_spec,), treatments=("off",), rounds=1, timeout_sec=120),
    )

    assert "\x1b[" not in output
    assert "[bold]" not in output
    assert not any(character in output for character in "━─┏┓└┘│┃┡┩╇")


def test_backend_summary_table_data_feeds_rich_and_markdown_renderers() -> None:
    records: list[dict[str, Any]] = []
    for file_sha256, main_time, dd_time in (("sha256:slow", 1.0, 2.0), ("sha256:fast", 1.0, 0.5)):
        records.append(
            make_record(
                len(records),
                started_at=f"2026-07-04T12:00:{len(records):02d}Z",
                file_sha256=file_sha256,
                backend="main",
                treatment="term",
                wall_sec=main_time,
            )
        )
        records.append(
            make_record(
                len(records),
                started_at=f"2026-07-04T12:00:{len(records):02d}Z",
                file_sha256=file_sha256,
                backend="dd",
                treatment="term",
                wall_sec=dd_time,
            )
        )
    rows = make_rows(*records)
    target = make_target()
    slow_file = bench.FileSpec("slow.egg", ROOT / "slow.egg", "sha256:slow")
    fast_file = bench.FileSpec("fast.egg", ROOT / "fast.egg", "sha256:fast")
    spec = bench.BenchmarkSpec(
        files=(slow_file, fast_file),
        treatments=("term",),
        rounds=1,
        timeout_sec=120,
        backends=("main", "dd"),
    )
    cell_maps = {target: bench.target_cell_summaries(rows, target, spec)}
    rss_cell_maps = {target: bench.target_rss_cell_summaries(rows, target, spec)}
    table_data = bench.backend_summary_tables(cell_maps, rss_cell_maps, [target], spec)[0]
    rich_stream = io.StringIO()
    rich_console = Console(file=rich_stream, width=260, color_system=None)

    rich_console.print(bench.render_rich_table(table_data))
    markdown = bench.render_markdown_table(table_data)

    assert table_data.headers[-3:] == ("Best file", "Best ratio", "Best result")
    assert table_data.rows == (
        (
            "dd",
            "term",
            "2.0000s",
            "2.5000s",
            "1.250x",
            "25.0%",
            "1.000x",
            "0/2",
            "fast.egg",
            "0.500x",
            "point only",
        ),
    )
    for value in table_data.rows[0]:
        assert value in markdown
        assert value in rich_stream.getvalue()


def test_main_markdown_report_goes_to_stdout_and_status_to_stderr(
    monkeypatch: pytest.MonkeyPatch,
    capsys: Any,
    tmp_path: Path,
) -> None:
    benchmark_file = tmp_path / "file.egg"
    benchmark_file.write_text("(check (= 1 1))\n", encoding="utf-8")
    file_spec = bench.FileSpec("file.egg", benchmark_file, "sha256:file")
    rows = make_rows(make_record(0, started_at="2026-07-04T12:00:00Z", wall_sec=1.0))
    target = make_target()

    monkeypatch.setattr(bench, "git_root_for_path", lambda path: ROOT)
    monkeypatch.setattr(bench, "resolve_files", lambda raw_files, invocation_cwd: (file_spec,))
    monkeypatch.setattr(bench, "load_report", lambda destination: rows)
    monkeypatch.setattr(bench, "resolve_target", lambda *args: target)
    monkeypatch.setattr(bench, "build_collection_plan", lambda *args: object())
    monkeypatch.setattr(
        bench,
        "emit_collection_plan",
        lambda output, plan, estimate_model: output.console.print("status line"),
    )
    monkeypatch.setattr(
        bench,
        "collect_rows",
        lambda current_rows, *args: bench.CollectionResult(current_rows, bench.empty_report_frame()),
    )
    argv = [
        "--format",
        "markdown",
        "--report",
        str(tmp_path / "reports.jsonl"),
        "--rounds",
        "1",
        "--treatments",
        "off",
        "file.egg",
    ]

    result = bench.main(argv)

    captured = capsys.readouterr()
    assert result == 0
    assert captured.out.startswith(bench.benchmark_command_block(argv) + "\n\n# Benchmark Report\n")
    assert captured.out.endswith("\n")
    assert not captured.out.endswith("\n\n")
    assert "\x1b[" not in captured.out
    assert "[bold]" not in captured.out
    assert "status line" in captured.err
    assert "# Benchmark Report" not in captured.err


def test_main_rich_report_remains_on_stderr_by_default(
    monkeypatch: pytest.MonkeyPatch,
    capsys: Any,
    tmp_path: Path,
) -> None:
    benchmark_file = tmp_path / "file.egg"
    benchmark_file.write_text("(check (= 1 1))\n", encoding="utf-8")
    file_spec = bench.FileSpec("file.egg", benchmark_file, "sha256:file")
    rows = make_rows(make_record(0, started_at="2026-07-04T12:00:00Z", wall_sec=1.0))
    target = make_target()

    monkeypatch.setattr(bench, "git_root_for_path", lambda path: ROOT)
    monkeypatch.setattr(bench, "resolve_files", lambda raw_files, invocation_cwd: (file_spec,))
    monkeypatch.setattr(bench, "load_report", lambda destination: rows)
    monkeypatch.setattr(bench, "resolve_target", lambda *args: target)
    monkeypatch.setattr(bench, "build_collection_plan", lambda *args: object())
    monkeypatch.setattr(
        bench,
        "emit_collection_plan",
        lambda output, plan, estimate_model: output.console.print("status line"),
    )
    monkeypatch.setattr(
        bench,
        "collect_rows",
        lambda current_rows, *args: bench.CollectionResult(current_rows, bench.empty_report_frame()),
    )

    result = bench.main(
        [
            "--report",
            str(tmp_path / "reports.jsonl"),
            "--rounds",
            "1",
            "--treatments",
            "off",
            "file.egg",
        ]
    )

    captured = capsys.readouterr()
    assert result == 0
    assert captured.out == ""
    assert "status line" in captured.err
    assert "Benchmark report" in captured.err


def test_report_dash_writes_rows_to_stream_and_does_not_load_cache() -> None:
    stream = io.StringIO()
    destination = bench.ReportDestination(path=None, stream=stream)
    rows = make_rows(make_record(0, started_at="2026-07-04T12:00:00Z", wall_sec=1.0))

    assert bench.load_report(destination).empty

    bench.append_rows(destination, rows)

    records = [json.loads(line) for line in stream.getvalue().splitlines()]
    assert len(records) == 1
    assert records[0]["status"] == "success"
    assert records[0]["wall_sec"] == 1.0
    assert records[0]["target_source"] == "."
    assert records[0]["file_path"] == "file.egg"
    assert records[0]["backend"] == "main"
    assert "row_index" not in records[0]
    assert "warmup_rounds" not in records[0]
    assert "target" not in records[0]
    assert "timing" not in records[0]


def test_flat_jsonl_roundtrips_through_report_frame(tmp_path: Path) -> None:
    report = tmp_path / "reports.jsonl"
    destination = bench.ReportDestination(path=report)
    rows = make_rows(make_record(0, started_at="2026-07-04T12:00:00Z", wall_sec=1.0, target_label="mine"))

    bench.append_rows(destination, rows)
    loaded = bench.load_report(destination)

    raw_record = json.loads(report.read_text(encoding="utf-8"))
    assert raw_record["target_label"] == "mine"
    assert raw_record["wall_sec"] == 1.0
    assert raw_record["backend"] == "main"
    assert "row_index" not in raw_record
    assert "warmup_rounds" not in raw_record
    assert "target" not in raw_record

    assert loaded["row_index"].tolist() == [0]
    assert loaded["target_label"].tolist() == ["mine"]
    assert loaded["backend"].tolist() == ["main"]
    assert loaded["wall_sec"].tolist() == [1.0]


def test_old_flat_jsonl_without_backend_loads_as_main(tmp_path: Path) -> None:
    report = tmp_path / "reports.jsonl"
    record = make_record(0, started_at="2026-07-04T12:00:00Z", wall_sec=1.0)
    record.pop("row_index")
    record.pop("backend")
    report.write_text(json.dumps(record) + "\n", encoding="utf-8")

    loaded = bench.load_report(bench.ReportDestination(path=report))

    assert loaded["backend"].tolist() == ["main"]


def test_report_frame_rejects_success_without_wall_time() -> None:
    record = make_record(0, started_at="2026-07-04T12:00:00Z", wall_sec=None)

    with pytest.raises(pa_errors.SchemaErrors):
        bench.report_frame_from_records([record])


def test_report_frame_rejects_timeout_with_timing() -> None:
    record = make_record(0, started_at="2026-07-04T12:00:00Z", status="timed-out", wall_sec=None)
    record["wall_sec"] = 1.0

    with pytest.raises(pa_errors.SchemaErrors):
        bench.report_frame_from_records([record])


def test_report_frame_rejects_extra_columns() -> None:
    record = make_record(0, started_at="2026-07-04T12:00:00Z", wall_sec=1.0)
    record["extra"] = "nope"

    with pytest.raises(ValueError, match="unexpected report column"):
        bench.report_frame_from_records([record])


def test_ru_maxrss_to_bytes_normalizes_platform_units() -> None:
    assert bench.ru_maxrss_to_bytes(123, platform="darwin") == 123
    assert bench.ru_maxrss_to_bytes(123, platform="linux") == 123 * 1024
    assert bench.ru_maxrss_to_bytes(0, platform="linux") is None


def test_run_command_records_signal_separately_from_exit_code() -> None:
    result = bench.run_command(
        [sys.executable, "-c", "import os, signal; os.kill(os.getpid(), signal.SIGTERM)"],
        ROOT,
        120,
    )

    assert result.status == "failure"
    assert result.error is not None
    assert result.error.exit_code is None
    assert result.error.signal == signal.SIGTERM


def test_run_process_passes_backend_flag_only_for_dd(monkeypatch: pytest.MonkeyPatch) -> None:
    commands: list[list[str]] = []
    file_spec = bench.FileSpec("file.egg", ROOT / "file.egg", "sha256:file")

    def fake_run_command(command: list[str], checkout_path: Path, timeout_sec: int) -> bench.TimingResult:
        commands.append(command)
        assert checkout_path == ROOT
        assert timeout_sec == 120
        return bench.TimingResult("success", bench.TimingRow(wall_sec=1.0), None)

    monkeypatch.setattr(bench, "run_command", fake_run_command)

    bench.run_process(ROOT / "egglog-experimental", ROOT, file_spec, "main", "off", 120)
    bench.run_process(ROOT / "egglog-experimental", ROOT, file_spec, "dd", "proofs", 120)

    assert "--backend" not in commands[0]
    assert commands[1][commands[1].index("--backend") : commands[1].index("--backend") + 2] == [
        "--backend",
        "dd",
    ]
    assert "--proofs" in commands[1]


def test_workload_command_matches_benchmark_behavior() -> None:
    file_spec = bench.FileSpec("file.egg", ROOT / "file.egg", "sha256:file")

    assert bench.workload_command(ROOT / "egglog-experimental", file_spec, "main", "off") == [
        str(ROOT / "egglog-experimental"),
        "--mode",
        "no-messages",
        "-j",
        "1",
        str(file_spec.absolute_path),
    ]
    assert bench.workload_command(ROOT / "egglog-experimental", file_spec, "dd", "proofs") == [
        str(ROOT / "egglog-experimental"),
        "--mode",
        "no-messages",
        "-j",
        "1",
        "--backend",
        "dd",
        "--proofs",
        str(file_spec.absolute_path),
    ]


def test_build_target_uses_profiling_profile(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    commands: list[list[str]] = []
    binary = tmp_path / "target" / "profiling" / "egglog-experimental"
    binary.parent.mkdir(parents=True)
    binary.write_text("binary", encoding="utf-8")
    row = bench.TargetRow(
        source=".",
        path=str(tmp_path),
        git_ref="HEAD",
        git_sha="abc123",
        is_dirty=False,
    )

    def fake_run(command: list[str], **kwargs: Any) -> None:
        commands.append(command)

    monkeypatch.setattr(bench.subprocess, "run", fake_run)
    monkeypatch.setattr(bench, "sha256_file", lambda path: "sha256:bin")

    binary_path, binary_sha256 = bench.build_target(row, bench.RunnerOutput(), "profiling")

    assert commands == [["cargo", "build", "--profile", "profiling", "-p", "egglog-experimental"]]
    assert binary_path == binary
    assert binary_sha256 == "sha256:bin"


def test_build_target_enables_requested_backend_features(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    commands: list[list[str]] = []
    binary = tmp_path / "target" / "release" / "egglog-experimental"
    binary.parent.mkdir(parents=True)
    binary.write_text("binary", encoding="utf-8")
    row = bench.TargetRow(".", str(tmp_path), "HEAD", "abc123", False)
    monkeypatch.setattr(bench.subprocess, "run", lambda command, **kwargs: commands.append(command))
    monkeypatch.setattr(bench, "sha256_file", lambda path: "sha256:bin")

    bench.build_target(row, bench.RunnerOutput(), cargo_features=bench.backend_cargo_features(("main", "dd")))

    assert commands == [["cargo", "build", "--release", "-p", "egglog-experimental", "--features", "dd-backend"]]


def test_profile_cache_path_uses_full_binary_and_file_hashes() -> None:
    binary_hash = "sha256:" + "a" * 64
    file_hash = "sha256:" + "b" * 64

    explicit = bench.profile_cache_path(
        Path(".profiles"), binary_hash, file_hash, "main", "proofs", bench.ProfileMode(5, None)
    )
    automatic = bench.profile_cache_path(
        Path(".profiles"),
        binary_hash,
        file_hash,
        "main",
        "proofs",
        bench.ProfileMode(None, 10),
    )

    assert explicit == Path(".profiles") / "v1" / ("a" * 64) / ("b" * 64) / "main-proofs-i5.json.gz"
    assert automatic == Path(".profiles") / "v1" / ("a" * 64) / ("b" * 64) / "main-proofs-auto10s.json.gz"


def test_profile_display_path_is_relative_inside_invocation_directory(tmp_path: Path) -> None:
    artifact = tmp_path / ".profiles" / "v1" / "profile.json.gz"

    assert bench.profile_display_path(artifact, tmp_path) == Path(".profiles/v1/profile.json.gz")


def test_calculate_profile_iterations_uses_margin_and_cap() -> None:
    assert bench.calculate_profile_iterations(2.0, 10) == (6, False)
    assert bench.calculate_profile_iterations(20.0, 10) == (1, False)
    assert bench.calculate_profile_iterations(0.00001, 10, max_iterations=7) == (7, True)
    assert bench.calculate_profile_iterations(0.0, 10, max_iterations=7) == (7, True)


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
        output = Path(command[command.index("--output") + 1])
        write_profile(output, profile)

    monkeypatch.setattr(bench, "samply_executable", lambda: "samply")
    monkeypatch.setattr(bench.subprocess, "run", fake_run)

    recorded_profile = bench.run_samply_record(
        artifact=artifact,
        name="profile",
        iterations=3,
        workload=["workload"],
        checkout_path=ROOT,
        timeout_sec=120,
    )

    assert recorded_profile == profile
    assert artifact.read_bytes()[:2] == b"\x1f\x8b"
    command = commands[0]
    temporary_output = Path(command[command.index("--output") + 1])
    assert temporary_output.name.endswith(".json.gz")
    assert command[:7] == ["samply", "record", "--save-only", "--rate", "1000", "--reuse-threads", "--iteration-count"]
    assert command[command.index("--iteration-count") + 1] == "3"
    assert command[-2:] == ["--", "workload"]


def test_samply_failure_leaves_no_new_artifact(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    artifact = tmp_path / "profile.json.gz"
    temp_artifact = tmp_path / ".profile.tmp-test.json.gz"

    def fake_run(command: list[str], **kwargs: Any) -> None:
        temp_artifact.write_bytes(b"partial")
        raise bench.subprocess.CalledProcessError(1, command)

    monkeypatch.setattr(bench, "samply_executable", lambda: "samply")
    monkeypatch.setattr(bench, "profile_temp_path", lambda path: temp_artifact)
    monkeypatch.setattr(bench.subprocess, "run", fake_run)

    with pytest.raises(bench.subprocess.CalledProcessError):
        bench.run_samply_record(
            artifact=artifact,
            name="profile",
            iterations=1,
            workload=["workload"],
            checkout_path=ROOT,
            timeout_sec=120,
        )

    assert not artifact.exists()
    assert not temp_artifact.exists()


def test_read_profile_artifact_rejects_plain_json(tmp_path: Path) -> None:
    artifact = tmp_path / "profile.json.gz"
    write_profile(artifact, compressed=False)

    with pytest.raises(ValueError, match="not gzip-compressed"):
        samply_analysis.read_artifact(artifact)


def test_read_profile_artifact_rejects_malformed_json(tmp_path: Path) -> None:
    artifact = tmp_path / "profile.json.gz"
    with gzip.open(artifact, "wt", encoding="utf-8") as handle:
        handle.write("not-json")

    with pytest.raises(ValueError, match="could not parse profile artifact"):
        samply_analysis.read_artifact(artifact)


def test_read_profile_artifact_normalizes_os_errors(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    artifact = tmp_path / "profile.json.gz"
    artifact.write_bytes(b"\x1f\x8b")
    original_open = Path.open

    def denied_open(path: Path, *args: Any, **kwargs: Any) -> Any:
        if path == artifact:
            raise PermissionError("denied")
        return original_open(path, *args, **kwargs)

    monkeypatch.setattr(Path, "open", denied_open)

    with pytest.raises(ValueError, match="could not read profile artifact"):
        samply_analysis.read_artifact(artifact)


def test_profile_leaf_samples_have_named_fields(tmp_path: Path) -> None:
    binary = tmp_path / "egglog-experimental"
    profile = make_cpu_profile_data(binary)

    samples = tuple(samply_analysis._thread_leaf_samples(profile["threads"][0], 1e-6))

    assert samples[0].cpu_seconds == pytest.approx(0.1)
    assert samples[0].library_index == 0
    assert samples[0].function_name == "0x10"
    assert samples[0].relative_address == 0x10


def test_samply_plain_json_output_is_not_promoted(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    artifact = tmp_path / "profile.json.gz"
    artifact.write_bytes(b"old")
    temporary_paths: list[Path] = []

    def fake_run(command: list[str], **kwargs: Any) -> None:
        output = Path(command[command.index("--output") + 1])
        temporary_paths.append(output)
        write_profile(output, compressed=False)

    monkeypatch.setattr(bench, "samply_executable", lambda: "samply")
    monkeypatch.setattr(bench.subprocess, "run", fake_run)

    with pytest.raises(ValueError, match="gzip"):
        bench.run_samply_record(
            artifact=artifact,
            name="profile",
            iterations=1,
            workload=["workload"],
            checkout_path=ROOT,
            timeout_sec=120,
        )

    assert artifact.read_bytes() == b"old"
    assert temporary_paths and not temporary_paths[0].exists()


def test_missing_samply_reports_install_command(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(bench.shutil, "which", lambda name: None)

    with pytest.raises(FileNotFoundError, match="cargo install --locked samply"):
        bench.samply_executable()


def test_macos_profile_summary_uses_cpu_deltas_and_atos_offsets(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    binary = tmp_path / "egglog-experimental"
    binary.write_bytes(b"binary")
    profile = make_cpu_profile_data(binary)
    commands: list[list[str]] = []

    def fake_run(command: list[str], **kwargs: Any) -> subprocess.CompletedProcess[str]:
        commands.append(command)
        return subprocess.CompletedProcess(
            command,
            0,
            stdout="crate..Thing$LT$T$GT$::run::h1234 (in egglog-experimental) + 4\n",
            stderr="",
        )

    monkeypatch.setattr(samply_analysis.shutil, "which", lambda name: "/usr/bin/atos" if name == "atos" else None)
    monkeypatch.setattr(samply_analysis.subprocess, "run", fake_run)

    summary = samply_analysis.summarize(profile, binary)

    assert summary.observed_cpu_seconds == pytest.approx(0.6)
    assert summary.application_cpu_seconds == pytest.approx(0.1)
    assert summary.other_library_cpu_seconds == pytest.approx(0.2)
    assert summary.unattributed_cpu_seconds == pytest.approx(0.3)
    assert summary.symbolized_application_cpu_seconds == pytest.approx(0.1)
    assert len(summary.functions) == 1
    assert summary.functions[0].name == "crate::Thing<T>::run::h1234"
    assert summary.functions[0].cpu_seconds == pytest.approx(0.1)
    assert len(commands) == 1
    assert "-offset" in commands[0]
    assert "0x10" in commands[0]
    assert "0x100000010" not in commands[0]


def test_macos_profile_summary_is_partial_without_atos(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    binary = tmp_path / "egglog-experimental"
    binary.write_bytes(b"binary")
    monkeypatch.setattr(samply_analysis.shutil, "which", lambda name: None)
    monkeypatch.setattr(
        samply_analysis.subprocess,
        "run",
        lambda *args, **kwargs: pytest.fail("symbolizer should not run without atos"),
    )

    summary = samply_analysis.summarize(make_cpu_profile_data(binary), binary)

    assert summary.observed_cpu_seconds == pytest.approx(0.6)
    assert summary.application_cpu_seconds == pytest.approx(0.1)
    assert summary.symbolized_application_cpu_seconds == 0
    assert summary.functions == ()
    assert any("atos is unavailable" in warning for warning in summary.warnings)


def test_macos_rust_v0_symbols_use_llvm_cxxfilt(monkeypatch: pytest.MonkeyPatch) -> None:
    commands: list[tuple[list[str], str | None]] = []

    def fake_run(command: list[str], **kwargs: Any) -> subprocess.CompletedProcess[str]:
        commands.append((command, kwargs.get("input")))
        return subprocess.CompletedProcess(command, 0, stdout="__rustc::__rdl_alloc\n", stderr="")

    monkeypatch.setattr(
        samply_analysis.shutil,
        "which",
        lambda name: "/usr/bin/xcrun" if name == "xcrun" else None,
    )
    monkeypatch.setattr(samply_analysis.subprocess, "run", fake_run)

    symbols, warnings = samply_analysis.demangle_rust_v0_symbols({0x10: "_RNvExample"})

    assert symbols == {0x10: "__rustc::__rdl_alloc"}
    assert warnings == ()
    assert commands == [(["/usr/bin/xcrun", "llvm-cxxfilt"], "_RNvExample\n")]


def test_profile_load_command_quotes_paths_for_posix_and_windows(tmp_path: Path) -> None:
    artifact = tmp_path / "profiles with spaces" / "profile.json.gz"

    assert samply_analysis.load_command(artifact, os_name="posix") == f"samply load '{artifact.resolve()}'"
    assert samply_analysis.load_command(artifact, os_name="nt") == f'samply load "{artifact.resolve()}"'
    assert samply_analysis.load_command(Path(".profiles/profile.json.gz"), os_name="posix") == (
        "samply load .profiles/profile.json.gz"
    )


def test_profile_rich_and_markdown_render_same_summary(tmp_path: Path) -> None:
    artifact = tmp_path / "profiles with spaces" / "profile.json.gz"
    summary = make_cpu_summary()
    report = samply_analysis.ProfileReport(
        artifact=artifact,
        cache_status="hit",
        workload="dir\\name|file\nnext.egg",
        backend="main",
        treatment="proofs",
        top=1,
        cpu_summary=summary,
    )
    rich_output = io.StringIO()
    console = Console(file=rich_output, force_terminal=False, width=120)

    samply_analysis.render_rich(console, report)
    markdown = samply_analysis.render_markdown(report)

    for value in ("CPU Profile Summary", "Observed thread", "Application symbols", "first", "samply load"):
        assert value in rich_output.getvalue()
        assert value in markdown
    assert "second" not in rich_output.getvalue()
    assert "second" not in markdown
    assert "first&lt;T&gt;" in markdown
    assert "dir\\\\name\\|file<br>next.egg" in markdown
    assert "| Metric | CPU | Share |" in markdown


def test_open_samply_profile_redirects_viewer_output_and_handles_interrupt(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    artifact = tmp_path / "profile.json.gz"
    calls: list[dict[str, Any]] = []

    def fake_run(command: list[str], **kwargs: Any) -> None:
        calls.append(kwargs)
        raise KeyboardInterrupt

    monkeypatch.setattr(bench, "samply_executable", lambda: "samply")
    monkeypatch.setattr(bench.subprocess, "run", fake_run)

    bench.open_samply_profile(artifact, ROOT)

    assert calls == [{"cwd": ROOT, "check": True, "stdout": sys.stderr, "stderr": sys.stderr}]


@pytest.mark.parametrize("platform", ["linux", "win32"])
def test_profile_cache_hit_on_non_macos_skips_cpu_summary_and_workload(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
    capsys: Any,
    platform: str,
) -> None:
    request, target, artifact = make_profile_case(tmp_path)
    write_profile(artifact)
    monkeypatch.setattr(bench.sys, "platform", platform)
    mock_profile_resolution(monkeypatch, request, target)
    monkeypatch.setattr(bench, "run_command", lambda *args, **kwargs: pytest.fail("calibration should not run"))
    monkeypatch.setattr(bench, "run_samply_record", lambda **kwargs: pytest.fail("samply should not run"))
    monkeypatch.setattr(
        samply_analysis,
        "summarize",
        lambda *args, **kwargs: pytest.fail("macOS summary should not run"),
    )

    bench.run_profile(argparse.Namespace(), bench.RunnerOutput(), ROOT, ROOT)

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
    monkeypatch.setattr(bench.sys, "platform", "linux")
    mock_profile_resolution(monkeypatch, request, target)
    monkeypatch.setattr(samply_analysis, "summarize", lambda *args: pytest.fail("summary should not run"))

    bench.run_profile(argparse.Namespace(), bench.RunnerOutput(), ROOT, ROOT)

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
    monkeypatch.setattr(bench.sys, "platform", "darwin")
    mock_profile_resolution(monkeypatch, request, target)
    monkeypatch.setattr(samply_analysis, "summarize", lambda profile, binary: summary)

    bench.run_profile(argparse.Namespace(), bench.RunnerOutput(), ROOT, ROOT)

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
    monkeypatch.setattr(bench.sys, "platform", "darwin")
    mock_profile_resolution(monkeypatch, request, target)
    monkeypatch.setattr(samply_analysis, "summarize", lambda profile, binary: make_cpu_summary())

    bench.run_profile(argparse.Namespace(), bench.RunnerOutput(), ROOT, ROOT)

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
        mode=bench.ProfileMode(1, None),
        show_summary=False,
    )
    write_profile(artifact)
    monkeypatch.setattr(bench.sys, "platform", "linux")
    mock_profile_resolution(monkeypatch, request, target)

    bench.run_profile(argparse.Namespace(), bench.RunnerOutput(), ROOT, ROOT)

    captured = capsys.readouterr()
    assert captured.out == f"{artifact.resolve()}\n"
    assert "currently available on macOS only" not in captured.err


def test_profile_cache_hit_can_open_profile(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    request, target, artifact = make_profile_case(
        tmp_path,
        mode=bench.ProfileMode(1, None),
        open_after=True,
        show_summary=False,
    )
    write_profile(artifact)
    opened: list[Path] = []
    mock_profile_resolution(monkeypatch, request, target)
    monkeypatch.setattr(bench, "open_samply_profile", lambda artifact, checkout_path: opened.append(artifact))

    bench.run_profile(argparse.Namespace(), bench.RunnerOutput(), ROOT, ROOT)

    assert opened == [artifact]


def test_profile_explicit_iterations_skip_calibration_and_bypass_cache(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    request, target, artifact = make_profile_case(
        tmp_path,
        mode=bench.ProfileMode(3, None),
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
    monkeypatch.setattr(bench, "run_command", lambda *args, **kwargs: pytest.fail("calibration should not run"))
    monkeypatch.setattr(bench, "run_samply_record", fake_record)

    bench.run_profile(argparse.Namespace(), bench.RunnerOutput(), ROOT, ROOT)

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
        bench,
        "run_command",
        lambda command, checkout_path, timeout_sec: bench.TimingResult("success", bench.TimingRow(wall_sec=2.0), None),
    )
    monkeypatch.setattr(bench, "run_samply_record", fake_record)
    monkeypatch.setattr(bench, "load_report", lambda destination: pytest.fail("profile mode should not load reports"))
    monkeypatch.setattr(
        bench, "append_rows", lambda destination, rows: pytest.fail("profile mode should not append rows")
    )

    bench.run_profile(argparse.Namespace(), bench.RunnerOutput(), ROOT, ROOT)

    assert recorded == [6]


def test_profile_auto_calibration_failure_stops_before_samply(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    request, target, _ = make_profile_case(tmp_path, force_run=True, show_summary=False)
    mock_profile_resolution(monkeypatch, request, target)
    monkeypatch.setattr(
        bench,
        "run_command",
        lambda command, checkout_path, timeout_sec: bench.TimingResult(
            "timed-out", bench.TimingRow(), bench.ErrorRow("timed out")
        ),
    )
    monkeypatch.setattr(bench, "run_samply_record", lambda **kwargs: pytest.fail("samply should not run"))

    with pytest.raises(ValueError, match="profile calibration failed"):
        bench.run_profile(argparse.Namespace(), bench.RunnerOutput(), ROOT, ROOT)


def test_profile_auto_iteration_cap_prints_warning(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, capsys: Any
) -> None:
    request, target, _ = make_profile_case(tmp_path, force_run=True, show_summary=False)
    mock_profile_resolution(monkeypatch, request, target)
    monkeypatch.setattr(
        bench,
        "run_command",
        lambda command, checkout_path, timeout_sec: bench.TimingResult(
            "success", bench.TimingRow(wall_sec=0.001), None
        ),
    )
    monkeypatch.setattr(bench, "calculate_profile_iterations", lambda elapsed_seconds, profile_seconds: (7, True))
    monkeypatch.setattr(bench, "run_samply_record", lambda **kwargs: make_profile_data())

    bench.run_profile(argparse.Namespace(), bench.RunnerOutput(), ROOT, ROOT)

    assert "maximum profile iterations reached" in capsys.readouterr().err


def test_profile_rejects_cache_only_label_targets() -> None:
    with pytest.raises(ValueError, match="cache-only label="):
        bench.resolve_profile_target(bench.parse_target("cached="), "main", ROOT, ROOT, bench.RunnerOutput())


def test_run_command_records_peak_rss() -> None:
    result = bench.run_command([sys.executable, "-c", "print('ok')"], ROOT, 120)

    assert result.status == "success"
    assert result.timing.max_rss_bytes is not None
    assert result.timing.max_rss_bytes > 0


def test_timing_from_usage_records_peak_rss() -> None:
    usage = resource.struct_rusage((1.0, 2.0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0))

    timing = bench.timing_from_usage(usage, 1.0)

    assert timing.user_sec == 1.0
    assert timing.system_sec == 2.0
    assert timing.max_rss_bytes == bench.ru_maxrss_to_bytes(3)


def test_render_report_shows_peak_rss_when_available() -> None:
    rows = make_rows(make_record(0, started_at="2026-07-04T12:00:00Z", wall_sec=1.0, max_rss_bytes=2 * 1024 * 1024))
    target = make_target()
    file_spec = bench.FileSpec("file.egg", ROOT / "file.egg", "sha256:file")
    stream = io.StringIO()
    console = Console(file=stream, width=300, color_system=None)

    bench.render_report(
        console,
        bench.ReportDestination(path=None, stream=io.StringIO()),
        rows,
        [target],
        bench.BenchmarkSpec(files=(file_spec,), treatments=("off",), rounds=1, timeout_sec=120),
    )

    output = stream.getvalue()
    assert "resident set size" in output
    assert "2.0 MiB" in output


def test_render_report_hides_peak_rss_for_old_rows_without_memory() -> None:
    rows = make_rows(make_record(0, started_at="2026-07-04T12:00:00Z", wall_sec=1.0, max_rss_bytes=None))
    target = make_target()
    file_spec = bench.FileSpec("file.egg", ROOT / "file.egg", "sha256:file")
    stream = io.StringIO()
    console = Console(file=stream, width=200, color_system=None)

    bench.render_report(
        console,
        bench.ReportDestination(path=None, stream=io.StringIO()),
        rows,
        [target],
        bench.BenchmarkSpec(files=(file_spec,), treatments=("off",), rounds=1, timeout_sec=120),
    )

    output = stream.getvalue()
    assert "file.egg" in output
    assert "per-file peak RSS" not in output


def test_runner_output_routes_status_to_stderr(monkeypatch: pytest.MonkeyPatch) -> None:
    stream = io.StringIO()
    monkeypatch.setattr(sys, "stderr", stream)
    output = bench.RunnerOutput()

    output.build_start(
        bench.TargetRow(
            source=".",
            path=str(ROOT),
            git_ref="HEAD",
            git_sha="abc123",
            is_dirty=False,
            label=None,
        )
    )

    assert "Building" in stream.getvalue()
