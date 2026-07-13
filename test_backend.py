"""Backend dimension, markdown output, and profile subcommand.

Ports the behavioral coverage from the pre-refactor ``test_bench.py`` for the
features that were merged from ``main`` (backend benchmarking, ``--format
markdown``, and the ``profile`` Samply subcommand), adapted to the module layout
introduced by the eval-live refactor. Rendering is asserted against the shared
``report.ReportTable`` model rather than the removed ``ReportTableData`` API.
"""

from __future__ import annotations

import gzip
import json
import subprocess
from pathlib import Path
from typing import Any

import pytest

import analysis
import bench
import models
import report
import report_frame
import samply_analysis

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
    backend: models.Backend = "main",
    treatment: models.Treatment = "off",
    timeout_sec: int = 120,
) -> dict[str, Any]:
    return {
        "row_index": index,
        "started_at": started_at,
        "status": status,
        "target_label": None,
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


def make_rows(*records: dict[str, Any]) -> bench.DataFrame[report_frame.ReportFrame]:
    return bench.report_frame_from_records(records)


def make_target(binary_sha256: str = "sha256:bin", label: str | None = None) -> models.ResolvedTarget:
    return models.ResolvedTarget(
        request=models.TargetRequest(raw=".", source=".", label=label),
        row=models.TargetRow(source=".", path=str(ROOT), git_ref="HEAD", git_sha="abc123", is_dirty=False, label=label),
        binary_sha256=binary_sha256,
        binary_path=None,
    )


def make_spec(backends: tuple[models.Backend, ...] = ("main",)) -> models.BenchmarkSpec:
    file_spec = models.FileSpec("file.egg", ROOT / "file.egg", "sha256:file")
    return models.BenchmarkSpec(
        files=(file_spec,), treatments=("term", "proofs"), rounds=2, timeout_sec=120, backends=backends
    )


def make_profile_data() -> dict[str, Any]:
    return {"meta": {"sampleUnits": {"threadCPUDelta": "us"}}, "libs": [], "threads": []}


def write_profile(path: Path, profile: dict[str, Any] | None = None, *, compressed: bool = True) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    data = make_profile_data() if profile is None else profile
    if compressed:
        with gzip.open(path, "wt", encoding="utf-8") as handle:
            json.dump(data, handle)
    else:
        path.write_text(json.dumps(data), encoding="utf-8")


# --- backend parsing / registry / cells -------------------------------------


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


def test_backend_registry_drives_parsing_capabilities_flags_and_display(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setitem(
        models.BACKEND_SPECS,
        "future",
        models.BackendSpec("Future", ("proofs",), ("--backend", "future"), ("future-backend",)),
    )
    assert bench.parse_backends("future") == ("future",)
    assert models.supported_treatments("future") == ("proofs",)
    assert models.backend_flags("future") == ["--backend", "future"]
    assert models.backend_cargo_features(("main", "future")) == ("future-backend",)
    assert report.display_backend("future") == "Future"
    assert models.backend_treatment_cells(("future",), ("off", "proofs")) == (models.BenchmarkCell("future", "proofs"),)


def test_benchmark_cells_filter_off_for_non_main_backends() -> None:
    spec = models.BenchmarkSpec(
        files=(models.FileSpec("file.egg", ROOT / "file.egg", "sha256:file"),),
        treatments=("off", "term", "proofs"),
        rounds=1,
        timeout_sec=120,
        backends=("main", "dd"),
    )
    assert bench.benchmark_cells(spec) == (
        models.BenchmarkCell("main", "off"),
        models.BenchmarkCell("main", "term"),
        models.BenchmarkCell("main", "proofs"),
        models.BenchmarkCell("dd", "term"),
        models.BenchmarkCell("dd", "proofs"),
    )


def test_validate_spec_rejects_backend_with_no_supported_treatments() -> None:
    spec = models.BenchmarkSpec(
        files=(models.FileSpec("file.egg", ROOT / "file.egg", "sha256:file"),),
        treatments=("off",),
        rounds=1,
        timeout_sec=120,
        backends=("dd",),
    )
    with pytest.raises(ValueError, match="backend dd has no supported treatments"):
        bench.validate_spec(spec)


def test_backend_cargo_features_dedupes_union() -> None:
    assert models.backend_cargo_features(("main",)) == ()
    assert models.backend_cargo_features(("main", "dd")) == ("dd-backend",)
    assert models.backend_cargo_features(("dd", "dd")) == ("dd-backend",)


# --- argument parsing --------------------------------------------------------


def test_parse_args_dispatches_profile_without_changing_benchmark_defaults() -> None:
    benchmark_args = bench.parse_args(["--rounds", "1", "file.egg"])
    profile_args = bench.parse_args(["profile", "file.egg"])
    assert benchmark_args.command == "benchmark"
    assert benchmark_args.rounds == 1
    assert benchmark_args.format == "rich"
    assert benchmark_args.backend == "main"
    assert profile_args.command == "profile"
    assert profile_args.file == "file.egg"
    assert profile_args.backend == "main"
    assert profile_args.treatment == "proofs"


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


def test_benchmark_serve_and_backend_flags_coexist() -> None:
    args = bench.parse_args(["--serve", "--serve-port", "9001", "--backend", "main,dd", "file.egg"])
    assert args.serve
    assert args.serve_port == 9001
    assert args.backend == "main,dd"


# --- runner backend behavior -------------------------------------------------


def test_workload_command_injects_backend_flags_before_treatment_flags() -> None:
    file_spec = models.FileSpec("file.egg", ROOT / "file.egg", "sha256:file")
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


def test_run_process_passes_backend_flag_only_for_dd(monkeypatch: pytest.MonkeyPatch) -> None:
    commands: list[list[str]] = []
    file_spec = models.FileSpec("file.egg", ROOT / "file.egg", "sha256:file")

    def fake_run_command(command: list[str], checkout_path: Path, timeout_sec: int) -> bench.TimingResult:
        commands.append(command)
        return bench.TimingResult("success", bench.TimingRow(wall_sec=1.0), None)

    monkeypatch.setattr(bench, "run_command", fake_run_command)
    bench.run_process(ROOT / "egglog-experimental", ROOT, file_spec, "main", "off", 120)
    bench.run_process(ROOT / "egglog-experimental", ROOT, file_spec, "dd", "proofs", 120)
    assert "--backend" not in commands[0]
    index = commands[1].index("--backend")
    assert commands[1][index : index + 2] == ["--backend", "dd"]
    assert "--proofs" in commands[1]


def test_collection_label_and_flat_record_carry_backend() -> None:
    file_spec = models.FileSpec("file.egg", ROOT / "file.egg", "sha256:file")
    assert bench.collection_label(file_spec, "dd", "proofs", 0, 3) == "file.egg dd/proofs 1/3"
    target = make_target()
    cell = bench.CellPlan(
        target=target,
        file=file_spec,
        backend="dd",
        treatment="proofs",
        required_rows=2,
        selected_cached_rows=bench.empty_report_frame(),
        missing_observations=2,
        estimate_key=analysis.estimate_key_for(target, file_spec, "dd", "proofs", 120),
    )
    record = bench.flat_report_record(
        row_index=0,
        started_at="2026-07-04T12:00:00Z",
        target=target,
        cell=cell,
        spec=make_spec(("main", "dd")),
        result=bench.TimingResult("success", bench.TimingRow(wall_sec=1.0), None),
    )
    assert record["backend"] == "dd"
    assert record["treatment"] == "proofs"


def test_selected_rows_separates_backends() -> None:
    rows = make_rows(
        make_record(0, started_at="2026-07-04T12:00:00Z", backend="main", wall_sec=1.0),
        make_record(1, started_at="2026-07-04T12:00:01Z", backend="main", wall_sec=1.1),
        make_record(2, started_at="2026-07-04T12:00:02Z", backend="dd", wall_sec=9.0),
        make_record(3, started_at="2026-07-04T12:00:03Z", backend="dd", wall_sec=9.1),
    )
    main_key = models.EstimateKey("sha256:bin", "sha256:file", "off", 120, "main")
    dd_key = models.EstimateKey("sha256:bin", "sha256:file", "off", 120, "dd")
    assert analysis.selected_rows(rows, main_key, 2)["wall_sec"].tolist() == [1.0, 1.1]
    assert analysis.selected_rows(rows, dd_key, 2)["wall_sec"].tolist() == [9.0, 9.1]


def test_old_flat_jsonl_without_backend_loads_as_main(tmp_path: Path) -> None:
    report_path = tmp_path / "reports.jsonl"
    record = make_record(0, started_at="2026-07-04T12:00:00Z", wall_sec=1.0)
    record.pop("row_index")
    record.pop("backend")
    report_path.write_text(json.dumps(record) + "\n", encoding="utf-8")
    loaded = bench.load_report(bench.ReportDestination(path=report_path))
    assert loaded["backend"].tolist() == ["main"]


# --- profile cache / samply helpers ------------------------------------------


def test_profile_mode_cache_label() -> None:
    assert bench.ProfileMode(5, None).cache_label == "i5"
    assert bench.ProfileMode(None, 10).cache_label == "auto10s"


def test_profile_cache_path_uses_full_binary_and_file_hashes() -> None:
    binary_hash = "sha256:" + "a" * 64
    file_hash = "sha256:" + "b" * 64
    explicit = bench.profile_cache_path(
        Path(".profiles"), binary_hash, file_hash, "main", "proofs", bench.ProfileMode(5, None)
    )
    automatic = bench.profile_cache_path(
        Path(".profiles"), binary_hash, file_hash, "dd", "proofs", bench.ProfileMode(None, 10)
    )
    assert explicit == Path(".profiles") / "v1" / ("a" * 64) / ("b" * 64) / "main-proofs-i5.json.gz"
    assert automatic == Path(".profiles") / "v1" / ("a" * 64) / ("b" * 64) / "dd-proofs-auto10s.json.gz"


def test_profile_display_path_is_relative_inside_invocation_directory(tmp_path: Path) -> None:
    artifact = tmp_path / ".profiles" / "v1" / "profile.json.gz"
    assert bench.profile_display_path(artifact, tmp_path) == Path(".profiles/v1/profile.json.gz")


def test_calculate_profile_iterations_uses_margin_and_cap() -> None:
    assert bench.calculate_profile_iterations(2.0, 10) == (6, False)
    assert bench.calculate_profile_iterations(20.0, 10) == (1, False)
    assert bench.calculate_profile_iterations(0.00001, 10, max_iterations=7) == (7, True)
    assert bench.calculate_profile_iterations(0.0, 10, max_iterations=7) == (7, True)


def test_profile_record_timeout_covers_all_iterations() -> None:
    assert bench.profile_record_timeout(120, 1) == 180
    assert bench.profile_record_timeout(120, 10) == 120 * 10 + 60


def test_samply_record_command_uses_fixed_flags() -> None:
    command = bench.samply_record_command("samply", Path("/p/out.json.gz"), "name", 3, ["workload", "arg"])
    assert command[:7] == ["samply", "record", "--save-only", "--rate", "1000", "--reuse-threads", "--iteration-count"]
    assert command[command.index("--iteration-count") + 1] == "3"
    assert command[command.index("--output") + 1] == "/p/out.json.gz"
    assert command[-3:] == ["--", "workload", "arg"]


def test_run_samply_record_replaces_artifact_atomically(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    artifact = tmp_path / "profile.json.gz"
    artifact.write_bytes(b"old")
    profile = make_profile_data()
    commands: list[list[str]] = []

    def fake_run(command: list[str], **kwargs: Any) -> None:
        commands.append(command)
        write_profile(Path(command[command.index("--output") + 1]), profile)

    monkeypatch.setattr(bench, "samply_executable", lambda: "samply")
    monkeypatch.setattr(bench.subprocess, "run", fake_run)
    recorded = bench.run_samply_record(
        artifact=artifact, name="profile", iterations=3, workload=["workload"], checkout_path=ROOT, timeout_sec=120
    )
    assert recorded == profile
    assert artifact.read_bytes()[:2] == b"\x1f\x8b"


def test_run_samply_record_failure_leaves_no_new_artifact(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    artifact = tmp_path / "profile.json.gz"
    temp_artifact = tmp_path / ".profile.tmp-test.json.gz"

    def fake_run(command: list[str], **kwargs: Any) -> None:
        temp_artifact.write_bytes(b"partial")
        raise subprocess.CalledProcessError(1, command)

    monkeypatch.setattr(bench, "samply_executable", lambda: "samply")
    monkeypatch.setattr(bench, "profile_temp_path", lambda path: temp_artifact)
    monkeypatch.setattr(bench.subprocess, "run", fake_run)
    with pytest.raises(subprocess.CalledProcessError):
        bench.run_samply_record(
            artifact=artifact, name="profile", iterations=1, workload=["workload"], checkout_path=ROOT, timeout_sec=120
        )
    assert not artifact.exists()
    assert not temp_artifact.exists()


def test_missing_samply_reports_install_command(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(bench.shutil, "which", lambda name: None)
    with pytest.raises(FileNotFoundError, match="cargo install --locked samply"):
        bench.samply_executable()


def test_resolve_profile_request_reuses_backend_treatment_validation(tmp_path: Path) -> None:
    file_path = tmp_path / "file.egg"
    file_path.write_text("(check (= 1 1))\n", encoding="utf-8")
    args = bench.parse_args(["profile", str(file_path), "--backend", "dd", "--treatment", "off"])
    with pytest.raises(ValueError, match="backend dd has no supported treatments"):
        bench.resolve_profile_request(args, ROOT)


def test_resolve_profile_target_rejects_cache_only_label() -> None:
    request = models.TargetRequest(raw="old=", source="", label="old")
    with pytest.raises(ValueError, match="does not support cache-only label"):
        bench.resolve_profile_target(request, "main", ROOT, ROOT, bench.RunnerOutput())


# --- samply_analysis artifact parsing ----------------------------------------


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


def test_read_profile_artifact_round_trips_valid_profile(tmp_path: Path) -> None:
    artifact = tmp_path / "profile.json.gz"
    write_profile(artifact)
    assert samply_analysis.read_artifact(artifact) == make_profile_data()


def test_profile_load_command_quotes_paths_for_posix_and_windows(tmp_path: Path) -> None:
    artifact = tmp_path / "profiles with spaces" / "profile.json.gz"
    assert samply_analysis.load_command(artifact, os_name="posix") == f"samply load '{artifact.resolve()}'"
    assert samply_analysis.load_command(artifact, os_name="nt") == f'samply load "{artifact.resolve()}"'


# --- markdown rendering over the ReportTable model ---------------------------


def test_markdown_escape_cell_handles_pipes_backslashes_and_multiline() -> None:
    assert report.markdown_escape_cell("a|b\\c\r\nnext\nlast") == "a\\|b\\\\c<br>next<br>last"


def test_benchmark_command_block_uses_fixed_entrypoint_and_shell_quoting() -> None:
    assert report.benchmark_command_block(("--report", "/tmp/report path.jsonl", "pipe|file.egg")) == (
        "```shell\n$ ./bench.py --report '/tmp/report path.jsonl' 'pipe|file.egg'\n```"
    )


def test_render_markdown_table_is_github_pipe_table() -> None:
    table = report.ReportTable(
        web_name="Example",
        caption="caption | text",
        columns=(report.Column("Name"), report.Column("Count", numeric=True)),
        rows=({"Name": report.Cell("x|y"), "Count": report.Cell("3")},),
        cli_title=lambda _: "Example",
    )
    output = report.render_markdown_table(table)
    assert output == "### Example\n\n| Name | Count |\n| --- | ---: |\n| x\\|y | 3 |\n\n_caption \\| text_"


def _multi_backend_rows() -> tuple[Any, models.ResolvedTarget, models.BenchmarkSpec]:
    records = []
    index = 0
    for backend in ("main", "dd"):
        for treatment in ("term", "proofs"):
            for _ in range(2):
                index += 1
                records.append(
                    make_record(
                        index,
                        started_at=f"2026-07-04T12:00:{index:02d}Z",
                        backend=backend,
                        treatment=treatment,
                        wall_sec=1.0 + 0.05 * index,
                        max_rss_bytes=1000 + index,
                    )
                )
    return make_rows(*records), make_target(label="A"), make_spec(("main", "dd"))


def test_build_report_tables_adds_backend_tables_only_when_multiple_backends() -> None:
    rows, target, spec = _multi_backend_rows()
    multi_names = {table.web_name for table in report.build_report_tables(rows, [target], spec)}
    assert "Per-file backend wall-time change" in multi_names
    assert "DD vs main wall time" in multi_names

    single_spec = make_spec(("main",))
    single_names = {table.web_name for table in report.build_report_tables(rows, [target], single_spec)}
    assert not any("backend" in name.lower() or " vs " in name for name in single_names)


def test_render_markdown_report_is_backend_aware_and_ansi_free() -> None:
    rows, target, spec = _multi_backend_rows()
    document = report.render_markdown_report(
        models.ReportDestination(Path(".reports.jsonl")), rows, [target], spec, ["--backend", "main,dd"]
    )
    assert "\x1b[" not in document
    assert "# Benchmark Report" in document
    assert "## Targets" in document
    assert "### Per-file backend wall-time change" in document
    assert "### DD vs main wall time" in document
