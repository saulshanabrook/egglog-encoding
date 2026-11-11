"""Exercise the public flat figure catalog and inspectable render bindings."""

from __future__ import annotations

import io
import json
import subprocess
import sys
from pathlib import Path
from typing import Any

import pytest
from rich.console import Console

import bench
from benchmarking import figures
from benchmarking.models import FileSpec, Status
from benchmarking.reports.grouped import grouped_report_path, write_grouped_report
from benchmarking.reports.store import ReportRecord, ReportStore

from .report_fixtures import make_record, make_target, make_timing_summary, write_report


def catalog_fixture(directory: Path, **settings: Any) -> Path:
    spec = directory / "chart.vl.json"
    spec.write_text(
        json.dumps(
            {
                "data": {"url": "old-grouped.json"},
                "params": [
                    {"name": name, "value": None}
                    for name in ("selected_inputs", "target_label", "rounds", "t_critical")
                ],
            }
        )
    )
    path = directory / "catalog.json"
    path.write_text(
        json.dumps(
            {
                "rounds": 2,
                "timeout_sec": 120,
                "figures": {
                    "runtime": {"spec": "chart.vl.json", "files": ["*.egg"], "treatments": ["off"]},
                    "memory": {"spec": "chart.vl.json", "files": ["*.egg"], "treatments": ["off"]},
                },
                **settings,
            }
        )
    )
    return path


def test_public_dispatch_is_lazy(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(figures, "main", lambda argv: 7 if argv == ("--help",) else 9)
    assert bench.main(("figures", "--help")) == 7


def test_config_help_does_not_expand_files(tmp_path: Path, capsys: pytest.CaptureFixture[str]) -> None:
    path = catalog_fixture(tmp_path)
    with pytest.raises(SystemExit) as error:
        figures.parse_args(["--config", str(path), "--help"])
    assert error.value.code == 0
    text = capsys.readouterr().out
    assert "runtime:" in text and "memory:" in text
    assert "--cached" not in text


def test_paper_slotted_selection_is_the_complete_sdql_nested_suite() -> None:
    config = figures.load_config(figures.DEFAULT_CONFIG)
    (resolved,) = figures.resolve_figures(config, ["slotted-runtime"], figures.ROOT)
    assert resolved.figure.treatments == ("slotted-ref-nested", "slotted-no-aliasing")
    assert {file.absolute_path.stem for file in resolved.files} == {
        f"{kernel}_{phase}-44rules"
        for kernel in ("batax", "mmm", "mmm_sum", "mttkrp", "ttm")
        for phase in ("1st", "2nd")
    }
    assert all(file.absolute_path.parent.name == "sdql" for file in resolved.files)


def test_importing_figures_does_not_import_scipy() -> None:
    result = subprocess.run(
        [sys.executable, "-c", "import sys; import benchmarking.figures; assert 'scipy' not in sys.modules"],
        cwd=figures.ROOT,
        capture_output=True,
        text=True,
        timeout=15,
    )
    assert result.returncode == 0, result.stderr
    assert result.stdout == result.stderr == ""


@pytest.mark.parametrize("args, code", [(["--help"], 0), (["--rounds", "0"], 2)])
def test_help_and_argument_errors_have_no_phase_status(
    args: list[str], code: int, capsys: pytest.CaptureFixture[str]
) -> None:
    with pytest.raises(SystemExit) as error:
        figures.main(args)
    assert error.value.code == code
    captured = capsys.readouterr()
    assert not any(label in captured.out + captured.err for label in ("Resolving inputs", "Loading cache", "Rendering"))
    if code == 0:
        assert captured.err == ""
    else:
        assert captured.out == ""


@pytest.mark.parametrize("rounds", ["0", "-1", "no"])
def test_invalid_round_override(tmp_path: Path, rounds: str) -> None:
    with pytest.raises(SystemExit):
        figures.parse_args(["--config", str(catalog_fixture(tmp_path)), "--rounds", rounds])


@pytest.mark.parametrize("rounds", [1, 3])
def test_round_override_collects_shared_runs_and_binds_effective_samples(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, rounds: int
) -> None:
    from benchmarking import collection, processes

    path = catalog_fixture(tmp_path)
    (tmp_path / "one.egg").write_text("(check (= 1 1))")
    report = tmp_path / "report.jsonl"
    target = make_target(target_label="figures", binary_path=tmp_path / "engine")
    launched: list[Any] = []
    resolved_rounds: list[int] = []

    def resolve(requests: Any, _store: Any, rounds: int, *_args: Any) -> Any:
        resolved_rounds.append(rounds)
        return {request.endpoint.target: target for request in requests}

    def observe(*args: Any) -> Any:
        launched.append(args)
        return collection.ProcessObservation(
            processes.TimingResult("success", processes.TimingRow(wall_sec=1), None), make_timing_summary()
        )

    def render(command: list[str], **_kwargs: Any) -> None:
        Path(command[command.index("--base") - 1]).write_bytes(b"rendered")

    monkeypatch.setattr(collection, "resolve_requests", resolve)
    monkeypatch.setattr(collection, "preflight_collection", lambda *_args: None)
    monkeypatch.setattr(collection, "run_process", observe)
    monkeypatch.setattr(figures.subprocess, "run", render)
    args = ["--config", str(path), "--report", str(report), "--rounds", str(rounds)]
    assert figures.main(args) == 0
    assert len(launched) == rounds  # Both figure views share one collection request.
    assert figures.load_config(path).rounds == 2
    assert figures.load_config(figures.DEFAULT_CONFIG).rounds == 10
    for name in ("runtime", "memory"):
        receipt = json.loads((tmp_path / f"{name}.receipt.json").read_bytes())
        selected = receipt["selected_observations"][0]
        assert receipt["rounds"] == selected["requested_rows"] == selected["selected_rows"] == rounds
        assert receipt["invocation"][-2:] == ["--rounds", str(rounds)]
        bound = json.loads((tmp_path / f"{name}.bound.vl.json").read_bytes())
        params = {p["name"]: p["value"] for p in bound["params"]}
        assert params["rounds"] == rounds
        assert params["t_critical"] == (None if rounds == 1 else pytest.approx(4.302652729696142))
    assert figures.main(args) == 0
    assert len(launched) == rounds
    assert resolved_rounds == [rounds, rounds]


@pytest.mark.parametrize("settings", [{"rounds": 0}, {"rounds": True}, {"timeout_sec": -1}, {"experiments": {}}])
def test_invalid_global_settings(tmp_path: Path, settings: dict[str, Any]) -> None:
    with pytest.raises(ValueError):
        figures.load_config(catalog_fixture(tmp_path, **settings))


def test_duplicate_keys_and_treatments_are_rejected(tmp_path: Path) -> None:
    path = tmp_path / "bad.json"
    path.write_text('{"rounds":1,"rounds":2}')
    with pytest.raises(ValueError, match="duplicate"):
        figures.load_config(path)
    path = catalog_fixture(tmp_path)
    data = json.loads(path.read_text())
    data["figures"]["runtime"]["treatments"] = ["off", "off"]
    path.write_text(json.dumps(data))
    with pytest.raises(ValueError, match="duplicate treatment"):
        figures.load_config(path)


def test_names_require_config_option_and_no_new_cache_flag(tmp_path: Path) -> None:
    path = catalog_fixture(tmp_path)
    for args in ([str(path)], ["runtime", "runtime"], ["--cached"]):
        with pytest.raises(SystemExit):
            figures.parse_args(["--config", str(path), *args])


def test_globs_are_relative_sorted_and_overlaps_do_not_duplicate(tmp_path: Path) -> None:
    path = catalog_fixture(tmp_path)
    (tmp_path / "z.egg").write_text("(check (= 1 1))")
    (tmp_path / "a.egg").write_text("(check (= 2 2))")
    data = json.loads(path.read_text())
    data["figures"]["runtime"]["files"] = ["*.egg", "a.egg"]
    path.write_text(json.dumps(data))
    result = figures.resolve_figures(figures.load_config(path), ["runtime"], tmp_path.parent)
    assert [f.absolute_path.name for f in result[0].files] == ["a.egg", "z.egg"]
    assert all(f.display_path.startswith(tmp_path.name + "/") for f in result[0].files)
    (tmp_path / "copy.egg").write_bytes((tmp_path / "a.egg").read_bytes())
    with pytest.raises(ValueError, match="identical"):
        figures.resolve_figures(figures.load_config(path), ["runtime"], tmp_path)


def test_unmatched_files_and_unknown_treatments_fail_before_build(tmp_path: Path) -> None:
    path = catalog_fixture(tmp_path)
    with pytest.raises(ValueError, match="matched nothing"):
        figures.resolve_figures(figures.load_config(path), ["runtime"], tmp_path)
    data = json.loads(path.read_text())
    data["figures"]["runtime"]["treatments"] = ["not-a-treatment"]
    path.write_text(json.dumps(data))
    with pytest.raises(ValueError, match="unknown treatment"):
        figures.load_config(path)


def test_bound_copy_receipt_and_incremental_rendering(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    path = catalog_fixture(tmp_path)
    config = figures.load_config(path)
    file = FileSpec("example.egg", tmp_path / "example.egg", "sha256:file")
    resolved = [figures.ResolvedFigure(f, (file,)) for f in config.figures]
    report = tmp_path / "cache.jsonl"
    write_report(
        report, *[make_record(i, started_at=f"2026-10-01T00:00:0{i}Z", target_label="figures") for i in range(3)]
    )
    grouped = ReportStore(report).grouped_report()
    write_grouped_report(grouped, grouped_report_path(report))
    target = make_target(target_label="figures")
    calls = []
    fail_png = False

    def render(command: list[str], **_kwargs: Any) -> None:
        calls.append(command)
        generated = Path(command[command.index("--base") - 1])
        assert f"Rendering {generated.stem}" in stream.getvalue()
        generated.write_bytes(b"" if fail_png and generated.suffix == ".png" else b"rendered")
        if fail_png and generated.suffix == ".png":
            raise figures.subprocess.CalledProcessError(1, command)

    monkeypatch.setattr(figures.subprocess, "run", render)
    stream = io.StringIO()
    console = Console(file=stream, width=20)
    output_dir = tmp_path / "out[red]"
    original = (tmp_path / "chart.vl.json").read_bytes()
    outputs = figures.render_figures(resolved, config, grouped, report, target, output_dir, [], console)
    assert len(outputs) == 6 and len(calls) == 6
    assert all(str(output) in stream.getvalue().splitlines() for output in outputs)
    receipt = json.loads((output_dir / "runtime.receipt.json").read_bytes())
    other = json.loads((output_dir / "memory.receipt.json").read_bytes())
    assert receipt["selection_sha256"] == other["selection_sha256"]
    assert [row["row_index"] for row in receipt["selected_observations"][0]["rows"]] == [1, 2]
    bound = json.loads((output_dir / "runtime.bound.vl.json").read_bytes())
    params = {p["name"]: p["value"] for p in bound["params"]}
    assert params["target_label"] == "figures"
    assert params["selected_inputs"][0]["file_sha256"] == "sha256:file"
    assert params["selected_inputs"][0]["selected_row_indices"] == [1, 2]
    assert "binary_sha256" not in params["selected_inputs"][0]
    assert bound["data"]["url"] == grouped_report_path(report).as_uri()
    assert (tmp_path / "chart.vl.json").read_bytes() == original
    assert all(
        command[-2:] == ["--base", str(tmp_path)] or command[-4:-2] == ["--base", str(tmp_path)] for command in calls
    )
    figures.render_figures(resolved, config, grouped, report, target, output_dir, [], console)
    assert len(calls) == 6
    assert "runtime: unchanged" in stream.getvalue()
    assert "memory: unchanged" in stream.getvalue()

    # Corrupt output cannot become a successful cache hit. A failing retry
    # preserves the prior complete image members and provenance receipt.
    receipt_path = output_dir / "runtime.receipt.json"
    previous_receipt = receipt_path.read_bytes()
    outputs[2].write_bytes(b"corrupt")
    fail_png = True
    with pytest.raises(figures.subprocess.CalledProcessError):
        figures.render_figures(resolved, config, grouped, report, target, output_dir, [], console)
    assert receipt_path.read_bytes() == previous_receipt
    assert outputs[0].read_bytes() == b"rendered"
    fail_png = False
    figures.render_figures(resolved, config, grouped, report, target, output_dir, [], console)
    assert outputs[2].read_bytes() == b"rendered"
    assert len(calls) == 12


@pytest.mark.parametrize("verbose", [False, True])
def test_main_announces_preparation_and_fallback_before_each_operation(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, verbose: bool
) -> None:
    from benchmarking import collection
    from benchmarking.reports import store as store_module

    config = catalog_fixture(tmp_path)
    (tmp_path / "one.egg").write_text("(check (= 1 1))")
    report = tmp_path / "observations[1].jsonl"
    stream = io.StringIO()
    console = Console(file=stream, width=200, color_system=None)
    events = []
    ticks = iter((10, 11, 20, 22, 30, 33, 40, 44, 50, 55))
    monkeypatch.setattr(figures, "perf_counter", lambda: next(ticks))

    def make_console(**kwargs: Any) -> Console:
        assert kwargs["stderr"] is True
        return console

    def inputs(*args: Any) -> Any:
        assert "Resolving inputs for 2 figures" in stream.getvalue()
        events.append("inputs")
        return original_inputs(*args)

    def metadata(*args: Any) -> Any:
        assert "Loading corpus metadata" in stream.getvalue()
        events.append("metadata")
        return original_metadata(*args)

    class Store(ReportStore):
        def __init__(self, path: Path) -> None:
            assert f"Loading cache {report}" in stream.getvalue()
            events.append("cache")
            super().__init__(path)

        def grouped_report(self, *args: Any, **kwargs: Any) -> Any:
            assert f"Writing {grouped_report_path(report)}" in stream.getvalue()
            events.append("snapshot")
            return super().grouped_report(*args, **kwargs)

    def targets(requests: Any, *_args: Any) -> Any:
        assert "Resolving targets" in stream.getvalue()
        events.append("targets")
        return {request.endpoint.target: make_target(target_label="figures") for request in requests}

    def collect(*_args: Any, **kwargs: Any) -> Any:
        assert kwargs["verbose"] is verbose
        events.append("collect")
        raise OSError("collection interrupted")

    def snapshot(*args: Any) -> None:
        assert f"Writing {grouped_report_path(report)}" in stream.getvalue()
        events.append("write")
        original_snapshot(*args)

    original_inputs, original_metadata = figures.resolve_figures, figures.figure_inventory
    original_snapshot = figures.write_grouped_report
    monkeypatch.setattr(figures, "Console", make_console)
    monkeypatch.setattr(figures, "resolve_figures", inputs)
    monkeypatch.setattr(figures, "figure_inventory", metadata)
    monkeypatch.setattr(store_module, "ReportStore", Store)
    monkeypatch.setattr(collection, "resolve_requests", targets)
    monkeypatch.setattr(collection, "plan_collection", lambda *_args: ())
    monkeypatch.setattr(collection, "collect", collect)
    monkeypatch.setattr(figures, "write_grouped_report", snapshot)
    monkeypatch.setattr(figures, "render_figures", lambda *_args: ())
    args = ["--config", str(config), "--report", str(report), *(["-v"] if verbose else [])]
    assert figures.main(args) == 2
    assert events == ["inputs", "metadata", "cache", "targets", "collect", "snapshot", "write"]
    text = stream.getvalue()
    if verbose:
        assert "1 unique input" in text and "1.0s" in text
        assert "0 metadata" in text and "2.0s" in text
        assert "0 observations" in text and "3.0s" in text
        assert "1 target" in text and "4.0s" in text
        assert "5.0s" in text
    else:
        assert not any(marker in text for marker in ("  resolved", "  loaded", "  wrote"))


def test_bound_ids_and_receipts_share_adaptive_selection_without_rewriting_rows(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    path = catalog_fixture(tmp_path)
    config = figures.load_config(path)
    file = FileSpec("example.egg", tmp_path / "example.egg", "sha256:file")
    resolved = [figures.ResolvedFigure(f, (file,)) for f in config.figures]
    report = tmp_path / "cache.jsonl"
    rows = [
        make_record(0, started_at="2026-10-01T00:00:00Z", timeout_sec=120, wall_sec=120.01),
        make_record(1, started_at="2026-10-01T00:00:01Z", timeout_sec=300, wall_sec=100),
        make_record(2, started_at="2026-10-01T00:00:02Z", timeout_sec=300, wall_sec=180),
        make_record(3, started_at="2026-10-01T00:00:03Z", timeout_sec=60, status="timed-out"),
        make_record(4, started_at="2026-10-01T00:00:04Z", status="failure"),
        make_record(5, started_at="2026-10-01T00:00:05Z", status="failure"),
    ]
    for row, cap in zip(rows[-2:], (8, 16), strict=True):
        row["error_exit_code"] = 86
        row["error_memory_limit_bytes"] = cap * 1024**3
    for row in rows:
        row["target_label"] = "figures"
    write_report(report, *rows)
    original = report.read_bytes()
    grouped = ReportStore(report).grouped_report()
    write_grouped_report(grouped, grouped_report_path(report))
    assert len(grouped.data["groups"]) == 1
    assert len(grouped.data["groups"][0]["samples"]) == 6

    def render(command: list[str], **_kwargs: Any) -> None:
        Path(command[command.index("--base") - 1]).write_bytes(b"rendered")

    monkeypatch.setattr(figures.subprocess, "run", render)
    for cap, expected in ((16, [1, 5]), (32, [0, 1])):
        monkeypatch.setattr(figures, "NATIVE_LIMIT_BYTES", cap * 1024**3)
        figures.render_figures(
            resolved,
            config,
            grouped,
            report,
            make_target(target_label="figures"),
            tmp_path,
            [],
            Console(file=io.StringIO()),
        )
        selections = []
        for name in ("runtime", "memory"):
            receipt = json.loads((tmp_path / f"{name}.receipt.json").read_bytes())
            selected = receipt["selected_observations"][0]["rows"]
            bound = json.loads((tmp_path / f"{name}.bound.vl.json").read_bytes())
            params = {p["name"]: p["value"] for p in bound["params"]}
            assert params["selected_inputs"][0]["selected_row_indices"] == expected
            assert [row["row_index"] for row in selected] == expected
            assert receipt["timeout_sec"] == 120
            assert receipt["memory_limit_bytes"] == cap * 1024**3
            assert [row["timeout_sec"] for row in selected] == [rows[i]["timeout_sec"] for i in expected]
            assert "error_memory_limit_bytes" not in selected[0]
            if cap == 16:
                assert selected[1]["error_memory_limit_bytes"] == 16 * 1024**3
                assert selected[1]["error_exit_code"] == 86
            selections.append(receipt["selection_sha256"])
        assert selections[0] == selections[1]
        assert report.read_bytes() == original


def test_render_rejects_a_label_bound_to_another_executable(tmp_path: Path) -> None:
    path = catalog_fixture(tmp_path)
    config = figures.load_config(path)
    file = FileSpec("example.egg", tmp_path / "example.egg", "sha256:file")
    report = tmp_path / "cache.jsonl"
    write_report(
        report,
        make_record(0, started_at="2026-10-01T00:00:00Z", target_label="figures", binary_sha256="old"),
    )
    grouped = ReportStore(report).grouped_report()
    write_grouped_report(grouped, grouped_report_path(report))
    with pytest.raises(ValueError, match="selected executable"):
        figures.render_figures(
            [figures.ResolvedFigure(config.figures[0], (file,))],
            config,
            grouped,
            report,
            make_target(target_label="figures"),
            tmp_path,
            [],
            Console(file=io.StringIO()),
        )


@pytest.mark.parametrize("width", [80, 119, 120, 160, 200])
def test_render_names_missing_and_failed_conditions_even_when_unchanged(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, width: int
) -> None:
    config = figures.load_config(catalog_fixture(tmp_path, rounds=3))
    files = tuple(
        FileSpec(f"inputs/{name}.egg", tmp_path / f"{name}.egg", f"sha256:{name}")
        for name in ("complete", "missing", "partial", "timeout", "[red]failure", "signal", "memory", "cleanup")
    )
    rows: list[ReportRecord] = []
    statuses_by_file: list[list[Status]] = [
        ["success"] * 3,
        [],
        ["success"],
        ["timed-out"] * 3,
        ["failure"] * 2,
        ["failure"],
        ["failure"],
        ["timed-out"],
    ]
    for file, statuses in zip(files, statuses_by_file, strict=True):
        for status in statuses:
            row = make_record(
                len(rows),
                started_at=f"2026-10-01T00:00:{len(rows):02}Z",
                status=status,
                file_sha256=file.sha256,
                target_label="figures",
            )
            if file.absolute_path.stem == "timeout":
                row["error_message"] = None
                row["timeout_sec"] = 300
            elif file.absolute_path.stem == "[red]failure":
                row["error_message"] = "bad [red]\n  lookup"
                row["error_exit_code"] = 101
            elif file.absolute_path.stem == "signal":
                row["error_signal"] = 9
            elif file.absolute_path.stem == "memory":
                row["error_message"] = "native allocation failed"
                row["error_exit_code"] = 86
                row["error_memory_limit_bytes"] = 16 * 1024**3
            elif file.absolute_path.stem == "cleanup":
                row["timeout_sec"] = 60
                row["error_message"] = "process-group cleanup failed: could not reap child"
            rows.append(row)
    report = tmp_path / "cache.jsonl"
    write_report(report, *rows)
    original = report.read_bytes()
    grouped = ReportStore(report).grouped_report()
    write_grouped_report(grouped, grouped_report_path(report))
    monkeypatch.setattr(figures, "NATIVE_LIMIT_BYTES", 16 * 1024**3)
    renders = []

    def render(command: list[str], **_kwargs: Any) -> None:
        renders.append(command)
        Path(command[command.index("--base") - 1]).write_bytes(b"rendered")

    monkeypatch.setattr(figures.subprocess, "run", render)
    for unchanged in (False, True):
        stream = io.StringIO()
        figures.render_figures(
            [figures.ResolvedFigure(config.figures[0], files)],
            config,
            grouped,
            report,
            make_target(target_label="figures"),
            tmp_path,
            [],
            Console(file=stream, width=width, color_system=None),
        )
        text = " ".join(stream.getvalue().split())
        assert "runtime: 7/8 incomplete or unsuccessful conditions (timeout 120s)" in text
        assert "inputs/missing.egg · off: incomplete; 0/3 successful runs" in text
        assert "inputs/partial.egg · off: incomplete; 1/3 successful runs" in text
        assert text.count("timed out after 300 seconds; 0/3 successful runs") == 1
        assert text.count("failed: bad [red] lookup (exit 101); 0/3 successful runs") == 1
        assert "inputs/signal.egg · off: failed (signal 9); 0/3 successful runs" in text
        assert "failed: native allocation failed (memory allowance 16 GiB) (exit 86); 0/3 successful runs" in text
        assert "timed out after 60 seconds: process-group cleanup failed: could not reap child" in text
        assert "inputs/complete.egg" not in text
        assert ("runtime: unchanged" in text) is unchanged
        assert len(renders) == 3
        assert report.read_bytes() == original


@pytest.fixture
def main_environment(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> dict[str, Any]:
    from benchmarking import collection

    (tmp_path / "one.egg").write_text("(check (= 1 1))")
    config = catalog_fixture(tmp_path)
    report = tmp_path / "observations.jsonl"
    rendered: list[Any] = []
    monkeypatch.setattr(
        collection,
        "resolve_requests",
        lambda requests, *_args: {request.endpoint.target: make_target(target_label="figures") for request in requests},
    )
    monkeypatch.setattr(collection, "plan_collection", lambda *_args: ())
    monkeypatch.setattr(figures, "render_figures", lambda *args: rendered.append(args[2]))
    return {"args": ["--config", str(config), "--report", str(report)], "report": report, "rendered": rendered}


def test_main_rewrites_fresh_partial_snapshot_before_rendering(
    main_environment: dict[str, Any], monkeypatch: pytest.MonkeyPatch
) -> None:
    from benchmarking import collection
    from benchmarking.reports.store import parse_grouped_report

    report = main_environment["report"]
    write_report(report, make_record(0, started_at="2026-10-01T00:00:00Z", binary_sha256="old", target_label="figures"))
    write_grouped_report(ReportStore(report).grouped_report(), grouped_report_path(report))

    def interrupted_write(store: ReportStore, _plans: Any, requests: Any, *_args: Any, **_kwargs: Any) -> Any:
        store.append(
            make_record(
                1,
                started_at="2026-10-01T00:00:01Z",
                target_label="figures",
                status="failure",
                file_sha256=requests[0].files[0].sha256,
            )
        )
        raise OSError("initial grouped write failed after partial collection")

    monkeypatch.setattr(collection, "collect", interrupted_write)
    assert figures.main(main_environment["args"]) == 2
    assert len(main_environment["rendered"]) == 1
    fresh = parse_grouped_report(grouped_report_path(report).read_bytes(), str(report))
    assert [(g["key"]["binary_sha256"], g["labels"]) for g in fresh.data["groups"]] == [
        ("old", []),
        ("sha256:bin", ["figures"]),
    ]
    assert main_environment["rendered"][0].data == fresh.data


def test_main_skips_render_when_partial_snapshot_cannot_be_refreshed(
    main_environment: dict[str, Any], monkeypatch: pytest.MonkeyPatch
) -> None:
    from benchmarking import collection

    def fail_collection(*_args: Any, **_kwargs: Any) -> Any:
        raise OSError("collection snapshot failure")

    def fail_snapshot(*_args: Any) -> Any:
        raise OSError("snapshot remains unwritable")

    monkeypatch.setattr(collection, "collect", fail_collection)
    monkeypatch.setattr(figures, "write_grouped_report", fail_snapshot)
    assert figures.main(main_environment["args"]) == 2
    assert main_environment["rendered"] == []


def test_main_ctrl_c_preserves_collector_snapshot_without_rendering(
    main_environment: dict[str, Any], monkeypatch: pytest.MonkeyPatch
) -> None:
    from benchmarking import collection

    def interrupted(store: ReportStore, _plans: Any, requests: Any, targets: Any, *_args: Any, **_kwargs: Any) -> Any:
        store.append(
            make_record(
                0, started_at="2026-10-01T00:00:00Z", target_label="figures", file_sha256=requests[0].files[0].sha256
            )
        )
        write_grouped_report(
            store.grouped_report(collection.current_label_bindings(requests, targets)), grouped_report_path(store.path)
        )
        raise KeyboardInterrupt

    monkeypatch.setattr(collection, "collect", interrupted)
    assert figures.main(main_environment["args"]) == 130
    assert main_environment["rendered"] == []
    assert ReportStore(main_environment["report"]).row_count == 1
    assert grouped_report_path(main_environment["report"]).is_file()


def test_main_rejects_label_only_target_before_resolution(
    main_environment: dict[str, Any], monkeypatch: pytest.MonkeyPatch
) -> None:
    from benchmarking import collection

    monkeypatch.setattr(collection, "resolve_requests", lambda *_args: pytest.fail("label lookup must not resolve"))
    assert figures.main([*main_environment["args"], "--target", "figures="]) == 2
    assert main_environment["rendered"] == []
