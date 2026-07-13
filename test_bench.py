from __future__ import annotations

import io
import json
import resource
import signal
import sys
from pathlib import Path
from typing import Any

import pandera.errors as pa_errors
import pytest
from rich.console import Console

import bench
import cli
import models
import report_frame
import tables

ROOT = Path(__file__).resolve().parent


def make_record(
    index: int,
    *,
    started_at: str,
    status: models.Status = "success",
    wall_sec: float | None = 1.0,
    max_rss_bytes: int | None = None,
    binary_sha256: str = "sha256:bin",
    file_sha256: str = "sha256:file",
    treatment: models.Treatment = "off",
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


def make_rows(*records: dict[str, Any]) -> bench.DataFrame[report_frame.ReportFrame]:
    return bench.report_frame_from_records(records)


def make_spec(file_spec: models.FileSpec) -> models.BenchmarkSpec:
    return models.BenchmarkSpec(files=(file_spec,), treatments=("off",), rounds=2, timeout_sec=120)


def make_full_spec(file_spec: models.FileSpec) -> models.BenchmarkSpec:
    return models.BenchmarkSpec(files=(file_spec,), treatments=("off", "term", "proofs"), rounds=2, timeout_sec=120)


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


def test_selected_rows_uses_latest_timestamp_then_jsonl_order() -> None:
    rows = make_rows(
        make_record(0, started_at="2026-07-04T12:00:00Z", wall_sec=1.0),
        make_record(1, started_at="2026-07-04T12:00:01Z", wall_sec=2.0),
        make_record(2, started_at="2026-07-04T12:00:01Z", wall_sec=3.0),
    )

    selected = tables.selected_rows(rows, models.EstimateKey("sha256:bin", "sha256:file", "off", 120), 2)

    assert selected["row_index"].tolist() == [1, 2]


def test_timeout_counts_for_cache_but_invalidates_stats() -> None:
    rows = make_rows(
        make_record(0, started_at="2026-07-04T12:00:00Z", status="timed-out", wall_sec=None),
        make_record(1, started_at="2026-07-04T12:00:01Z", wall_sec=1.0),
    )

    selected = tables.selected_rows(rows, models.EstimateKey("sha256:bin", "sha256:file", "off", 120), 2)
    summary = tables.summarize_cell(selected, 2)

    assert len(selected) == 2
    assert summary.issue == "timeout row selected"
    assert not summary.ok


def test_ratio_from_samples_reports_fieller_interval() -> None:
    summary = tables.ratio_from_samples(
        [1.00, 1.05, 0.95, 1.02, 0.98],
        [1.45, 1.52, 1.48, 1.50, 1.55],
    )

    assert summary.point == pytest.approx(1.5, rel=0.05)
    assert summary.ci_low is not None
    assert summary.ci_high is not None
    assert summary.point is not None
    assert summary.ci_low < summary.point < summary.ci_high


def test_suite_ratio_sums_fixed_files() -> None:
    baseline_a = tables.summarize_cell(
        make_rows(
            make_record(0, started_at="2026-07-04T12:00:00Z", wall_sec=1.0),
            make_record(1, started_at="2026-07-04T12:00:01Z", wall_sec=1.2),
        ),
        2,
    )
    candidate_a = tables.summarize_cell(
        make_rows(
            make_record(2, started_at="2026-07-04T12:00:00Z", wall_sec=2.0),
            make_record(3, started_at="2026-07-04T12:00:01Z", wall_sec=2.2),
        ),
        2,
    )
    baseline_b = tables.summarize_cell(
        make_rows(
            make_record(4, started_at="2026-07-04T12:00:00Z", wall_sec=3.0),
            make_record(5, started_at="2026-07-04T12:00:01Z", wall_sec=3.2),
        ),
        2,
    )
    candidate_b = tables.summarize_cell(
        make_rows(
            make_record(6, started_at="2026-07-04T12:00:00Z", wall_sec=4.0),
            make_record(7, started_at="2026-07-04T12:00:01Z", wall_sec=4.2),
        ),
        2,
    )

    summary = tables.suite_ratio([(baseline_a, candidate_a), (baseline_b, candidate_b)])

    assert summary.point == pytest.approx((2.1 + 4.1) / (1.1 + 3.1))


def test_target_suite_treatment_ratio_compares_same_treatment_between_targets() -> None:
    base = make_target(target_label="base", binary_sha256="sha256:base")
    candidate = make_target(target_label="candidate", binary_sha256="sha256:candidate")
    file_a = models.FileSpec("a.egg", ROOT / "a.egg", "sha256:a")
    file_b = models.FileSpec("b.egg", ROOT / "b.egg", "sha256:b")
    spec = models.BenchmarkSpec(files=(file_a, file_b), treatments=("off",), rounds=2, timeout_sec=120)
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
    base_cells = tables.target_cell_summaries(rows, base, spec)
    candidate_cells = tables.target_cell_summaries(rows, candidate, spec)

    ratio = tables.target_suite_treatment_ratio(base_cells, candidate_cells, spec, "off")

    assert ratio.point == pytest.approx((0.85 + 2.45) / (1.1 + 3.1))
    assert ratio.ci_low is not None
    assert ratio.ci_high is not None


def test_summary_formatters_show_ranges_when_defined_and_points_otherwise() -> None:
    empty_rows = bench.empty_report_frame()

    assert (
        tables.format_seconds_summary(
            models.CellSummary(empty_rows, (), {}, mean=1.0, ci_low=0.75, ci_high=1.25, issue=None)
        )
        == "[0.7500s, 1.2500s]"
    )
    assert (
        tables.format_ratio_summary(models.RatioSummary(point=2.0, ci_low=1.6, ci_high=2.6, issue=None))
        == "[1.600x, 2.600x]"
    )
    assert (
        tables.format_ratio_summary(models.RatioSummary(point=2.0, ci_low=None, ci_high=None, issue=None)) == "2.000x"
    )
    assert tables.format_bytes(512) == "512 B"
    assert tables.format_bytes(2 * 1024 * 1024) == "2.0 MiB"
    assert (
        tables.format_bytes_summary(
            models.CellSummary(empty_rows, (), {}, mean=2 * 1024 * 1024, ci_low=None, ci_high=None, issue=None)
        )
        == "2.0 MiB"
    )
    assert (
        tables.format_wall_time_change(models.RatioSummary(point=0.8, ci_low=0.7, ci_high=0.9, issue=None))
        == "[-30.0%, -10.0%]"
    )
    assert (
        tables.format_wall_time_change(models.RatioSummary(point=1.25, ci_low=None, ci_high=None, issue=None))
        == "25.0%"
    )
    assert (
        tables.format_wall_time_change(models.RatioSummary(point=None, ci_low=None, ci_high=None, issue="invalid"))
        == "-"
    )
    assert tables.lower_is_better_result(models.RatioSummary(point=0.8, ci_low=0.7, ci_high=0.9, issue=None)) == "less"
    assert tables.lower_is_better_result(models.RatioSummary(point=1.2, ci_low=1.1, ci_high=1.3, issue=None)) == "more"


def test_parse_target_variants() -> None:
    assert bench.parse_target(".") == models.TargetRequest(raw=".", source=".", label=None)
    assert bench.parse_target("main=@main") == models.TargetRequest(raw="main=@main", source="@main", label="main")
    assert bench.parse_target("prev-run=") == models.TargetRequest(raw="prev-run=", source="", label="prev-run")
    assert bench.parse_target("#33") == models.TargetRequest(raw="#33", source="#33", label="#33")
    assert bench.parse_target("candidate=#33") == models.TargetRequest(
        raw="candidate=#33", source="#33", label="candidate"
    )


@pytest.mark.parametrize("raw", ["#", "#0", "#abc", "candidate=#0"])
def test_parse_target_rejects_invalid_pr_targets(raw: str) -> None:
    with pytest.raises(ValueError, match="invalid PR target"):
        bench.parse_target(raw)


def test_parse_treatments_rejects_duplicates() -> None:
    with pytest.raises(ValueError, match="duplicate treatment: off"):
        bench.parse_treatments("off,term,off")


def test_validate_spec_rejects_executable_prove_benchmark_file(tmp_path: Path) -> None:
    prove_file = tmp_path / "prove.egg"
    prove_file.write_text(
        "; comments may mention (prove ...)\n(datatype Expr)\n(prove (Fact))\n",
        encoding="utf-8",
    )
    spec = models.BenchmarkSpec(
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
    spec = models.BenchmarkSpec(
        files=bench.resolve_files([str(check_file)], tmp_path),
        treatments=("off", "term", "proofs"),
        rounds=1,
        timeout_sec=120,
    )

    bench.validate_spec(spec)


def test_estimate_model_is_exact_only_and_updates_from_successful_processes() -> None:
    rows = make_rows(
        make_record(0, started_at="2026-07-04T12:00:00Z", wall_sec=2.0),
        make_record(1, started_at="2026-07-04T12:00:01Z", wall_sec=50.0, binary_sha256="sha256:other"),
        make_record(2, started_at="2026-07-04T12:00:02Z", status="timed-out", wall_sec=None),
    )
    model = bench.EstimateModel.from_rows(rows)
    exact_key = models.EstimateKey("sha256:bin", "sha256:file", "off", 120)
    other_timeout_key = models.EstimateKey("sha256:bin", "sha256:file", "off", 60)

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
    monkeypatch.setattr(bench, "find_worktree_for_sha", lambda repo, sha: None)

    checkout_path, sha = bench.materialize_pr_target(tmp_path, "#33", "#33")

    assert checkout_path == tmp_path / ".bench-worktrees" / "33"
    assert sha == "abc123"
    assert calls == [
        ["git", "fetch", "origin", "+refs/pull/33/head:refs/remotes/origin/pr/33"],
        ["git", "worktree", "add", "--detach", str(tmp_path / ".bench-worktrees" / "33"), "abc123"],
    ]


def test_collection_plan_counts_cache_and_missing_rows() -> None:
    rows = make_rows(make_record(0, started_at="2026-07-04T12:00:00Z", wall_sec=1.0))
    target = make_target()
    file_spec = models.FileSpec("file.egg", ROOT / "file.egg", "sha256:file")
    spec = make_spec(file_spec)

    plan = bench.build_collection_plan(rows, target, spec, False)
    force_plan = bench.build_collection_plan(rows, target, spec, True)

    assert plan.cells[0].selected_cached_rows["row_index"].tolist() == [0]
    assert plan.cells[0].missing_observations == 1
    assert plan.total_planned_processes == 2
    assert force_plan.cells[0].missing_observations == 2
    assert force_plan.total_planned_processes == 3


def test_parse_args_rejects_removed_output_mode() -> None:
    with pytest.raises(SystemExit):
        bench.parse_args(["--output", "jsonl"])


def test_parse_args_rejects_removed_warmup_mode() -> None:
    with pytest.raises(SystemExit):
        bench.parse_args(["--warmup", "0"])


def test_collection_plan_writes_human_output_to_stderr(monkeypatch: pytest.MonkeyPatch) -> None:
    rows = make_rows(make_record(0, started_at="2026-07-04T12:00:00Z", wall_sec=1.0))
    target = make_target()
    file_spec = models.FileSpec("file.egg", ROOT / "file.egg", "sha256:file")
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
    file_spec = models.FileSpec("file.egg", ROOT / "file.egg", "sha256:file")
    stream = io.StringIO()
    console = Console(file=stream, width=200, color_system=None)

    cli.render_report(
        console,
        models.ReportDestination(path=None, stream=io.StringIO()),
        rows,
        [target],
        models.BenchmarkSpec(files=(file_spec,), treatments=("off",), rounds=1, timeout_sec=120),
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
    file_spec = models.FileSpec("file.egg", ROOT / "file.egg", "sha256:file")
    stream = io.StringIO()
    console = Console(file=stream, width=200, color_system=None)

    cli.render_report(
        console,
        models.ReportDestination(path=None, stream=io.StringIO()),
        rows,
        [target],
        models.BenchmarkSpec(files=(file_spec,), treatments=("off", "proofs"), rounds=2, timeout_sec=120),
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
    file_spec = models.FileSpec("file.egg", ROOT / "file.egg", "sha256:file")
    stream = io.StringIO()
    console = Console(file=stream, width=220, color_system=None)

    cli.render_report(
        console,
        models.ReportDestination(path=None, stream=io.StringIO()),
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
    file_spec = models.FileSpec("file.egg", ROOT / "file.egg", "sha256:file")
    stream = io.StringIO()
    console = Console(file=stream, width=220, color_system=None)

    cli.render_report(
        console,
        models.ReportDestination(path=None, stream=io.StringIO()),
        rows,
        [baseline, candidate],
        models.BenchmarkSpec(files=(file_spec,), treatments=("proofs",), rounds=1, timeout_sec=120),
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
    file_spec = models.FileSpec("file.egg", ROOT / "file.egg", "sha256:file")
    stream = io.StringIO()
    console = Console(file=stream, width=240, color_system=None)

    cli.render_report(
        console,
        models.ReportDestination(path=None, stream=io.StringIO()),
        rows,
        [baseline, candidate],
        models.BenchmarkSpec(files=(file_spec,), treatments=("proofs",), rounds=2, timeout_sec=120),
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
    file_spec = models.FileSpec("file.egg", ROOT / "file.egg", "sha256:file")
    stream = io.StringIO()
    console = Console(file=stream, width=200, color_system=None)

    cli.render_report(
        console,
        models.ReportDestination(path=None, stream=io.StringIO()),
        rows,
        [target],
        models.BenchmarkSpec(files=(file_spec,), treatments=("proofs",), rounds=1, timeout_sec=120),
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
    file_spec = models.FileSpec("file.egg", ROOT / "file.egg", "sha256:file")
    stream = io.StringIO()
    console = Console(file=stream, width=220, color_system=None)

    cli.render_report(
        console,
        models.ReportDestination(path=None, stream=io.StringIO()),
        rows,
        [baseline, candidate],
        make_spec(file_spec),
    )

    output = stream.getvalue()
    assert "invalid: timeout row selected" in output
    assert "off" in output


def test_report_dash_writes_rows_to_stream_and_does_not_load_cache() -> None:
    stream = io.StringIO()
    destination = models.ReportDestination(path=None, stream=stream)
    rows = make_rows(make_record(0, started_at="2026-07-04T12:00:00Z", wall_sec=1.0))

    assert bench.load_report(destination).empty

    bench.append_rows(destination, rows)

    records = [json.loads(line) for line in stream.getvalue().splitlines()]
    assert len(records) == 1
    assert records[0]["status"] == "success"
    assert records[0]["wall_sec"] == 1.0
    assert records[0]["target_source"] == "."
    assert records[0]["file_path"] == "file.egg"
    assert "row_index" not in records[0]
    assert "warmup_rounds" not in records[0]
    assert "target" not in records[0]
    assert "timing" not in records[0]


def test_flat_jsonl_roundtrips_through_report_frame(tmp_path: Path) -> None:
    report = tmp_path / "reports.jsonl"
    destination = models.ReportDestination(path=report)
    rows = make_rows(make_record(0, started_at="2026-07-04T12:00:00Z", wall_sec=1.0, target_label="mine"))

    bench.append_rows(destination, rows)
    loaded = bench.load_report(destination)

    raw_record = json.loads(report.read_text(encoding="utf-8"))
    assert raw_record["target_label"] == "mine"
    assert raw_record["wall_sec"] == 1.0
    assert "row_index" not in raw_record
    assert "warmup_rounds" not in raw_record
    assert "target" not in raw_record

    assert loaded["row_index"].tolist() == [0]
    assert loaded["target_label"].tolist() == ["mine"]
    assert loaded["wall_sec"].tolist() == [1.0]


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
    file_spec = models.FileSpec("file.egg", ROOT / "file.egg", "sha256:file")
    stream = io.StringIO()
    console = Console(file=stream, width=300, color_system=None)

    cli.render_report(
        console,
        models.ReportDestination(path=None, stream=io.StringIO()),
        rows,
        [target],
        models.BenchmarkSpec(files=(file_spec,), treatments=("off",), rounds=1, timeout_sec=120),
    )

    output = stream.getvalue()
    assert "resident set size" in output
    assert "2.0 MiB" in output


def test_render_report_hides_peak_rss_for_old_rows_without_memory() -> None:
    rows = make_rows(make_record(0, started_at="2026-07-04T12:00:00Z", wall_sec=1.0, max_rss_bytes=None))
    target = make_target()
    file_spec = models.FileSpec("file.egg", ROOT / "file.egg", "sha256:file")
    stream = io.StringIO()
    console = Console(file=stream, width=200, color_system=None)

    cli.render_report(
        console,
        models.ReportDestination(path=None, stream=io.StringIO()),
        rows,
        [target],
        models.BenchmarkSpec(files=(file_spec,), treatments=("off",), rounds=1, timeout_sec=120),
    )

    output = stream.getvalue()
    assert "file.egg" in output
    assert "per-file peak RSS" not in output


def test_runner_output_routes_status_to_stderr(monkeypatch: pytest.MonkeyPatch) -> None:
    stream = io.StringIO()
    monkeypatch.setattr(sys, "stderr", stream)
    output = bench.RunnerOutput()

    output.build_start(
        models.TargetRow(
            source=".",
            path=str(ROOT),
            git_ref="HEAD",
            git_sha="abc123",
            is_dirty=False,
            label=None,
        )
    )

    assert "Building" in stream.getvalue()
