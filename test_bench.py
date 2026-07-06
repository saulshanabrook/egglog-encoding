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

ROOT = Path(__file__).resolve().parent


def make_record(
    index: int,
    *,
    started_at: str,
    status: bench.Status = "success",
    wall_sec: float | None = 1.0,
    binary_sha256: str = "sha256:bin",
    file_sha256: str = "sha256:file",
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
        "treatment": treatment,
        "timeout_sec": timeout_sec,
        "wall_sec": None if status == "timed-out" else wall_sec,
        "user_sec": None,
        "system_sec": None,
        "cpu_wall_ratio": None,
        "max_rss_bytes": None,
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
    file_spec = bench.FileSpec("file.egg", ROOT / "file.egg", "sha256:file")
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


def test_render_report_orients_single_target_summary_before_diagnostics() -> None:
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
    assert output.index("Outcome") < output.index("per-file wall time")


def test_render_report_compares_multiple_targets_before_diagnostics() -> None:
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
    assert "Suite speed change vs base" in output
    assert "Per-file speed change vs base" in output
    assert "Proof overhead by target" in output
    assert "Target comparison" not in output
    assert output.index("Suite speed change vs base") < output.index("base: per-file wall time")


def test_render_report_marks_invalid_multi_target_speed_cells() -> None:
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


def test_timing_from_usage_leaves_rss_unset() -> None:
    before = resource.getrusage(resource.RUSAGE_CHILDREN)
    after = resource.getrusage(resource.RUSAGE_CHILDREN)

    timing = bench.timing_from_usage(before, after, 1.0)

    assert timing.max_rss_bytes is None


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
