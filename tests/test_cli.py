"""Test public CLI parsing, dispatch, validation order, and output routing."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any, cast

import duckdb
import pytest

from benchmarking import benchmark, benchmark_config, models, processes, targets
from benchmarking.reports.database import ReportDatabase
from benchmarking.reports.summary import report_file_labels

from .conftest import ROOT, make_record, make_target, write_report


def test_parse_target_variants() -> None:
    assert targets.parse_target(".") == models.TargetRequest(raw=".", source=".", label=None)
    assert targets.parse_target("main=@main") == models.TargetRequest(raw="main=@main", source="@main", label="main")
    assert targets.parse_target("prev-run=") == models.TargetRequest(raw="prev-run=", source="", label="prev-run")
    assert targets.parse_target("#33") == models.TargetRequest(raw="#33", source="#33", label="#33")
    assert targets.parse_target("candidate=#33") == models.TargetRequest(
        raw="candidate=#33", source="#33", label="candidate"
    )


@pytest.mark.parametrize("raw", ["#", "#0", "#abc", "candidate=#0"])
def test_parse_target_rejects_invalid_pr_targets(raw: str) -> None:
    with pytest.raises(ValueError, match="invalid PR target"):
        targets.parse_target(raw)


def test_parse_treatments_rejects_duplicates() -> None:
    with pytest.raises(ValueError, match="duplicate treatment: off"):
        benchmark_config.parse_treatments("off,term,off")


def test_parse_backends_accepts_single_and_comma_separated_values() -> None:
    assert benchmark_config.parse_backends("main") == ("main",)
    assert benchmark_config.parse_backends("main,dd") == ("main", "dd")
    assert benchmark_config.parse_backends(" dd , main ") == ("dd", "main")


def test_parse_backends_rejects_duplicates_unknowns_and_empty_values() -> None:
    with pytest.raises(ValueError, match="duplicate backend: main"):
        benchmark_config.parse_backends("main,dd,main")
    with pytest.raises(ValueError, match="unknown backend: bogus"):
        benchmark_config.parse_backends("bogus")
    with pytest.raises(ValueError, match="at least one backend"):
        benchmark_config.parse_backends(",,")


def test_backend_registry_drives_capabilities_flags_and_display(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setitem(
        models.BACKEND_SPECS,
        "future",
        models.BackendSpec("Future", ("proofs",), ("--backend", "future"), ("future-backend",)),
    )

    assert benchmark_config.parse_backends("future") == ("future",)
    assert models.backend_spec("future").treatments == ("proofs",)
    assert targets.backend_flags("future") == ["--backend", "future"]
    assert models.backend_cargo_features(("main", "future")) == ("future-backend",)
    assert models.backend_spec("future").display_name == "Future"
    assert models.backend_treatment_cells(("future",), ("off", "proofs")) == (models.BenchmarkCell("future", "proofs"),)


def test_benchmark_cells_filter_off_for_non_main_backends() -> None:
    file_spec = models.FileSpec("file.egg", ROOT / "file.egg", "sha256:file")
    spec = models.BenchmarkSpec(
        files=(file_spec,),
        treatments=("off", "term", "proofs"),
        rounds=1,
        timeout_sec=120,
        backends=("main", "dd"),
    )

    assert models.benchmark_cells(spec) == (
        models.BenchmarkCell("main", "off"),
        models.BenchmarkCell("main", "term"),
        models.BenchmarkCell("main", "proofs"),
        models.BenchmarkCell("dd", "term"),
        models.BenchmarkCell("dd", "proofs"),
    )


def test_validate_spec_rejects_backend_with_no_supported_treatments() -> None:
    file_spec = models.FileSpec("file.egg", ROOT / "file.egg", "sha256:file")
    spec = models.BenchmarkSpec((file_spec,), ("off",), 1, 120, ("dd",))

    with pytest.raises(ValueError, match="backend dd has no supported treatments"):
        benchmark_config.validate_spec(spec)


def test_validate_spec_rejects_duplicate_workload_cache_identities(tmp_path: Path) -> None:
    benchmark_file = tmp_path / "file.egg"
    benchmark_file.write_text("(check (= 1 1))\n", encoding="utf-8")
    first = models.FileSpec("first.egg", benchmark_file, "sha256:same", fact_directory_sha256="sha256:facts")
    second = models.FileSpec("second.egg", benchmark_file, "sha256:same", fact_directory_sha256="sha256:facts")
    spec = models.BenchmarkSpec((first, second), ("off",), 1, 120)

    with pytest.raises(ValueError, match=r"first\.egg.*second\.egg.*identical file and fact-directory hashes"):
        benchmark_config.validate_spec(spec)


def test_same_file_with_different_fact_contents_is_a_distinct_workload(tmp_path: Path) -> None:
    benchmark_file = tmp_path / "file.egg"
    benchmark_file.write_text("(check (= 1 1))\n", encoding="utf-8")
    first = models.FileSpec("first.egg", benchmark_file, "sha256:same", fact_directory_sha256="sha256:facts-a")
    second = models.FileSpec("second.egg", benchmark_file, "sha256:same", fact_directory_sha256="sha256:facts-b")

    benchmark_config.validate_spec(models.BenchmarkSpec((first, second), ("off",), 1, 120))


def test_validate_spec_rejects_executable_prove_benchmark_file(tmp_path: Path) -> None:
    prove_file = tmp_path / "prove.egg"
    prove_file.write_text(
        "; comments may mention (prove ...)\n(datatype Expr)\n(prove (Fact))\n",
        encoding="utf-8",
    )
    spec = models.BenchmarkSpec(
        files=benchmark_config.resolve_files([str(prove_file)], tmp_path),
        treatments=("off", "term", "proofs"),
        rounds=1,
        timeout_sec=120,
    )

    with pytest.raises(ValueError, match="explicit prove command"):
        benchmark_config.validate_spec(spec)


def test_validate_spec_allows_prove_mentions_in_comments(tmp_path: Path) -> None:
    check_file = tmp_path / "check.egg"
    check_file.write_text(
        "; comments may mention (prove ...)\n(datatype Expr)\n(check (Fact))\n",
        encoding="utf-8",
    )
    spec = models.BenchmarkSpec(
        files=benchmark_config.resolve_files([str(check_file)], tmp_path),
        treatments=("off", "term", "proofs"),
        rounds=1,
        timeout_sec=120,
    )

    benchmark_config.validate_spec(spec)


def test_default_workloads_are_the_six_research_cases() -> None:
    files = benchmark_config.resolve_files([], ROOT)
    assert tuple(file.display_path for file in files) == (
        "egglog/tests/math-microbenchmark.egg",
        "egglog-experimental/tests/fixtures/eggcc-2mm-pass1.egg",
        "benchmarks/pointer-analysis-small.egg",
        "egglog/tests/hardboiled_conv1d_32.egg",
        "benchmarks/luminal-llama.egg",
        "egglog/tests/web-demo/herbie.egg",
    )
    pointer = next(file for file in files if file.display_path == "benchmarks/pointer-analysis-small.egg")
    assert pointer.fact_directory == (ROOT / "benchmarks/data/pointer-analysis-small").resolve()
    assert pointer.fact_directory_sha256.startswith("sha256:")


def test_report_file_labels_disambiguate_paths_and_fact_directories() -> None:
    unique = models.FileSpec("long/path/unique.egg", ROOT / "unique.egg", "sha256:unique")
    first = models.FileSpec("alpha/shared.egg", ROOT / "first.egg", "sha256:first")
    second = models.FileSpec("beta/nested/shared.egg", ROOT / "second.egg", "sha256:second")
    same_a = models.FileSpec("query.egg", ROOT / "query.egg", "sha256:query", ROOT / "facts-a", "sha:a")
    same_b = models.FileSpec("query.egg", ROOT / "query.egg", "sha256:query", ROOT / "facts-b", "sha:b")

    assert report_file_labels((unique, first, second)) == {
        unique: "unique.egg",
        first: "alpha/shared.egg",
        second: "nested/shared.egg",
    }
    assert report_file_labels((same_a, same_b)) == {
        same_a: "query.egg:facts-a",
        same_b: "query.egg:facts-b",
    }


def test_explicit_fact_directory_is_resolved_and_hashed(tmp_path: Path) -> None:
    benchmark_file = tmp_path / "input.egg"
    benchmark_file.write_text('(input Edge "edge.tsv")\n', encoding="utf-8")
    facts = tmp_path / "facts"
    facts.mkdir()
    (facts / "edge.tsv").write_text("a\tb\n", encoding="utf-8")

    (file_spec,) = benchmark_config.resolve_files(["input.egg"], tmp_path, "facts")

    assert file_spec.fact_directory == facts.resolve()
    assert file_spec.fact_directory_sha256 == targets.sha256_directory(facts)


def test_fact_directory_requires_explicit_benchmark_file(tmp_path: Path) -> None:
    with pytest.raises(ValueError, match="requires at least one explicit benchmark file"):
        benchmark_config.resolve_files([], tmp_path, "facts")


@pytest.mark.parametrize(
    "argv",
    [
        ("--output", "jsonl"),
        ("--warmup", "0"),
        ("--collect-phase-timings", "on"),
        ("--phase-timing-rounds", "1"),
        ("--phase-timing-top", "1"),
        ("--phase-timings-report", "phase.jsonl"),
        ("--report", "-"),
    ],
)
def test_parse_args_rejects_removed_or_unsupported_modes(argv: tuple[str, ...]) -> None:
    with pytest.raises(SystemExit):
        benchmark_config.parse_benchmark_args(argv)


def test_detailed_timing_implies_compact_timing() -> None:
    args = benchmark_config.parse_benchmark_args(["--detailed-timing"])

    assert args.detailed_timing
    assert args.phase_timings


def test_duckdb_ui_is_opt_in() -> None:
    ordinary = benchmark_config.parse_benchmark_args([])
    with_ui = benchmark_config.parse_benchmark_args(["--duckdb-ui"])

    assert not ordinary.duckdb_ui
    assert with_ui.duckdb_ui


def test_duckdb_ui_reports_extension_start_failure(tmp_path: Path) -> None:
    class FailingConnection:
        def execute(self, _query: str) -> None:
            raise duckdb.Error("extension unavailable")

    database = object.__new__(ReportDatabase)
    database.path = tmp_path / "reports.jsonl"
    database._closed = False
    database._connection = cast(Any, FailingConnection())

    with pytest.raises(ValueError, match="unable to install, load, or start.*extension unavailable"):
        database.start_ui()


def test_duckdb_ui_wait_keeps_session_alive_until_input(
    monkeypatch: pytest.MonkeyPatch,
    capsys: Any,
) -> None:
    events: list[str] = []

    class FakeStdin:
        def readline(self) -> str:
            events.append("input")
            return "\n"

    monkeypatch.setattr(benchmark.sys, "stdin", FakeStdin())

    benchmark.wait_for_duckdb_ui_exit(benchmark.RunnerOutput())

    assert events == ["input"]
    assert "Press Enter or Ctrl-C" in capsys.readouterr().err


def test_duckdb_ui_wait_rejects_closed_input(monkeypatch: pytest.MonkeyPatch) -> None:
    class ClosedStdin:
        def readline(self) -> str:
            return ""

    monkeypatch.setattr(benchmark.sys, "stdin", ClosedStdin())

    with pytest.raises(ValueError, match="input closed"):
        benchmark.wait_for_duckdb_ui_exit(benchmark.RunnerOutput())


def test_main_rejects_duckdb_ui_without_interactive_stdin(
    monkeypatch: pytest.MonkeyPatch,
    capsys: Any,
) -> None:
    class NoninteractiveStdin:
        def isatty(self) -> bool:
            return False

    monkeypatch.setattr(benchmark.sys, "stdin", NoninteractiveStdin())
    monkeypatch.setattr(
        benchmark,
        "git_root_for_path",
        lambda _path: pytest.fail("noninteractive UI must fail before repository work"),
    )

    result = benchmark.main(["--duckdb-ui"])

    assert result == 2
    assert "requires an interactive terminal" in capsys.readouterr().err


def test_main_validates_old_report_shape_before_building(
    monkeypatch: pytest.MonkeyPatch,
    capsys: Any,
    tmp_path: Path,
) -> None:
    report = tmp_path / "old.jsonl"
    old = dict(make_record(0, started_at="2026-07-04T12:00:00Z"))
    old["report_schema_version"] = 1
    report.write_text(json.dumps(old) + "\n", encoding="utf-8")
    monkeypatch.setattr(benchmark, "git_root_for_path", lambda _path: ROOT)
    monkeypatch.setattr(
        benchmark,
        "resolve_target",
        lambda *_args: pytest.fail("an incompatible report must fail before target resolution/build"),
    )

    result = benchmark.main(["--report", str(report), "--rounds", "1", "--treatments", "off"])

    assert result == 2
    assert "invalid or incompatible benchmark report" in capsys.readouterr().err


def test_main_preflights_every_fresh_target_before_collecting(
    monkeypatch: pytest.MonkeyPatch,
    capsys: Any,
    tmp_path: Path,
) -> None:
    report = tmp_path / "reports.jsonl"
    benchmark_file = tmp_path / "file.egg"
    benchmark_file.write_text("(check (= 1 1))\n", encoding="utf-8")
    file_spec = models.FileSpec("file.egg", benchmark_file, "sha256:file")
    targets_by_label = {
        "first": make_target(
            target_label="first",
            binary_sha256="sha256:first",
            binary_path=tmp_path / "first-egglog",
        ),
        "second": make_target(
            target_label="second",
            binary_sha256="sha256:second",
            binary_path=tmp_path / "second-egglog",
        ),
    }
    monkeypatch.setattr(benchmark, "git_root_for_path", lambda _path: ROOT)
    monkeypatch.setattr(
        benchmark,
        "resolve_files",
        lambda _raw_files, _invocation_cwd, _fact_directory=None: (file_spec,),
    )
    monkeypatch.setattr(
        benchmark,
        "resolve_target",
        lambda request, *_args: targets_by_label[request.label or ""],
    )
    preflighted: list[str] = []

    def fail_second_preflight(plan: Any, _spec: models.BenchmarkSpec) -> processes.TimingResult:
        label = plan.target.display_label
        preflighted.append(label)
        if label == "second":
            raise ValueError("target second does not support --timing-summary")
        return processes.TimingResult("success", processes.TimingRow(wall_sec=0.1), None)

    monkeypatch.setattr(benchmark, "preflight_collection", fail_second_preflight)
    monkeypatch.setattr(
        benchmark,
        "collect_rows",
        lambda *_args: pytest.fail("collection must wait until every target passes preflight"),
    )

    result = benchmark.main(
        [
            "--report",
            str(report),
            "--rounds",
            "1",
            "--treatments",
            "off",
            "--target",
            "first=.",
            "--target",
            "second=.",
            "file.egg",
        ]
    )

    assert result == 2
    assert preflighted == ["first", "second"]
    assert report.read_text(encoding="utf-8") == ""
    assert "does not support --timing-summary" in capsys.readouterr().err


def test_main_rejects_duplicate_binary_targets_before_collection(
    monkeypatch: pytest.MonkeyPatch,
    capsys: Any,
    tmp_path: Path,
) -> None:
    report = tmp_path / "reports.jsonl"
    benchmark_file = tmp_path / "file.egg"
    benchmark_file.write_text("(check (= 1 1))\n", encoding="utf-8")
    file_spec = models.FileSpec("file.egg", benchmark_file, "sha256:file")
    targets_by_label = {
        label: make_target(target_label=label, binary_sha256="sha256:shared") for label in ("first", "second")
    }
    monkeypatch.setattr(benchmark, "git_root_for_path", lambda _path: ROOT)
    monkeypatch.setattr(
        benchmark,
        "resolve_files",
        lambda _raw_files, _invocation_cwd, _fact_directory=None: (file_spec,),
    )
    monkeypatch.setattr(
        benchmark,
        "resolve_target",
        lambda request, *_args: targets_by_label[request.label or ""],
    )
    monkeypatch.setattr(
        benchmark,
        "build_collection_plan",
        lambda *_args: pytest.fail("duplicate targets must fail before collection planning"),
    )

    result = benchmark.main(
        [
            "--report",
            str(report),
            "--rounds",
            "1",
            "--treatments",
            "off",
            "--target",
            "first=.",
            "--target",
            "second=.",
            "file.egg",
        ]
    )

    assert result == 2
    assert report.read_text(encoding="utf-8") == ""
    assert "targets 'first' and 'second' produced the same binary SHA-256" in capsys.readouterr().err


def test_main_rich_report_remains_on_stderr_by_default(
    monkeypatch: pytest.MonkeyPatch,
    capsys: Any,
    tmp_path: Path,
) -> None:
    report = tmp_path / "reports.jsonl"
    write_report(report, make_record(0, started_at="2026-07-04T12:00:00Z", wall_sec=1.0))
    benchmark_file = tmp_path / "file.egg"
    benchmark_file.write_text("(check (= 1 1))\n", encoding="utf-8")
    file_spec = models.FileSpec("file.egg", benchmark_file, "sha256:file")
    target = make_target()
    monkeypatch.setattr(benchmark, "git_root_for_path", lambda _path: ROOT)
    monkeypatch.setattr(
        benchmark,
        "resolve_files",
        lambda _raw_files, _invocation_cwd, _fact_directory=None: (file_spec,),
    )
    monkeypatch.setattr(benchmark, "resolve_target", lambda *_args: target)
    monkeypatch.setattr(
        benchmark.ReportDatabase,
        "start_ui",
        lambda *_args: pytest.fail("ordinary benchmark runs must not start the DuckDB UI"),
    )

    result = benchmark.main(
        [
            "--report",
            str(report),
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
    assert "cache and estimate plan" in captured.err
    assert "Benchmark report" in captured.err


def test_main_opens_duckdb_ui_after_installing_report_scope(
    monkeypatch: pytest.MonkeyPatch,
    capsys: Any,
    tmp_path: Path,
) -> None:
    report = tmp_path / "reports.jsonl"
    write_report(report, make_record(0, started_at="2026-07-04T12:00:00Z", wall_sec=1.0))
    benchmark_file = tmp_path / "file.egg"
    benchmark_file.write_text("(check (= 1 1))\n", encoding="utf-8")
    file_spec = models.FileSpec("file.egg", benchmark_file, "sha256:file")
    target = make_target()
    monkeypatch.setattr(benchmark, "git_root_for_path", lambda _path: ROOT)
    monkeypatch.setattr(
        benchmark,
        "resolve_files",
        lambda _raw_files, _invocation_cwd, _fact_directory=None: (file_spec,),
    )
    monkeypatch.setattr(benchmark, "resolve_target", lambda *_args: target)
    events: list[str] = []

    class InteractiveStdin:
        def isatty(self) -> bool:
            return True

    class BufferedStdout:
        text = ""

        def write(self, value: str) -> int:
            self.text += value
            events.append("write")
            return len(value)

        def flush(self) -> None:
            events.append("flush")

    stdout = BufferedStdout()
    monkeypatch.setattr(benchmark.sys, "stdin", InteractiveStdin())
    monkeypatch.setattr(benchmark.sys, "stdout", stdout)

    def start_ui(database: Any) -> str:
        scoped_targets = database._connection.execute("SELECT count(*) FROM presentation_targets").fetchone()[0]
        assert scoped_targets == 1
        events.append("start")
        return "UI started at http://localhost:4213"

    def wait_for_exit(_output: Any) -> None:
        events.append("wait")

    monkeypatch.setattr(benchmark.ReportDatabase, "start_ui", start_ui)
    monkeypatch.setattr(benchmark, "wait_for_duckdb_ui_exit", wait_for_exit)

    result = benchmark.main(
        [
            "--report",
            str(report),
            "--rounds",
            "1",
            "--treatments",
            "off",
            "--format",
            "markdown",
            "--duckdb-ui",
            "file.egg",
        ]
    )

    captured = capsys.readouterr()
    assert result == 0
    assert events == ["write", "flush", "start", "wait"]
    assert "# Benchmark Report" in stdout.text
    assert "UI started at http://localhost:4213" in captured.err
