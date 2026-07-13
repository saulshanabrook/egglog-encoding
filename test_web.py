"""Tests for the eval-live web/dump layer: report scope (ReportSelection),
serialization round-trip, browser recompute, filtering, and terminal/web
equivalence. Complements test_bench.py (runner + extracted compute)."""

from __future__ import annotations

import io
import json
from pathlib import Path
from typing import Any, cast

from rich.console import Console

import bench
import cli
import models
import report
import web
import web_registry

ROOT = Path(__file__).resolve().parent


def make_record(
    index: int,
    *,
    started_at: str,
    wall_sec: float = 1.0,
    max_rss_bytes: int | None = 1000,
    binary_sha256: str = "sha256:bin",
    file_sha256: str = "sha256:file",
    file_path: str = "file.egg",
    treatment: models.Treatment = "off",
    timeout_sec: int = 120,
    target_label: str | None = None,
    target_git_sha: str = "abc123def456",
) -> dict[str, Any]:
    return {
        "row_index": index,
        "started_at": started_at,
        "status": "success",
        "target_label": target_label,
        "target_source": ".",
        "target_path": str(ROOT),
        "target_git_ref": "HEAD",
        "target_git_sha": target_git_sha,
        "target_is_dirty": False,
        "binary_sha256": binary_sha256,
        "file_path": file_path,
        "file_sha256": file_sha256,
        "treatment": treatment,
        "timeout_sec": timeout_sec,
        "wall_sec": wall_sec,
        "user_sec": None,
        "system_sec": None,
        "cpu_wall_ratio": None,
        "max_rss_bytes": max_rss_bytes,
        "error_exit_code": None,
        "error_signal": None,
        "error_message": None,
    }


def make_rows(*records: dict[str, Any]) -> bench.DataFrame[Any]:
    return bench.report_frame_from_records(records)


def make_target(binary_sha256: str, label: str, git_sha: str = "abc123def456") -> models.ResolvedTarget:
    return models.ResolvedTarget(
        request=models.TargetRequest(raw=".", source=".", label=label),
        row=models.TargetRow(source=".", path=str(ROOT), git_ref="HEAD", git_sha=git_sha, is_dirty=False, label=label),
        binary_sha256=binary_sha256,
        binary_path=None,
    )


def make_spec(
    files: list[tuple[str, str]],
    treatments: tuple[models.Treatment, ...] = ("off",),
    rounds: int = 2,
    timeout_sec: int = 120,
) -> models.BenchmarkSpec:
    file_specs = tuple(models.FileSpec(display_path=path, absolute_path=ROOT / path, sha256=sha) for sha, path in files)
    return models.BenchmarkSpec(files=file_specs, treatments=treatments, rounds=rounds, timeout_sec=timeout_sec)


def test_report_selection_json_round_trip() -> None:
    spec = make_spec([("sha256:f1", "a.egg"), ("sha256:f2", "b.egg")], treatments=("off", "proofs"), rounds=4)
    selection = models.build_report_selection([make_target("sha256:bin", "main")], spec)

    restored = models.report_selection_from_dict(json.loads(json.dumps(models.report_selection_to_dict(selection))))

    assert restored == selection


def test_report_data_excludes_historical_timeout() -> None:
    rows = make_rows(
        make_record(0, started_at="2026-07-04T12:00:00Z", wall_sec=1.0, timeout_sec=120),
        make_record(1, started_at="2026-07-04T12:00:01Z", wall_sec=1.1, timeout_sec=120),
        # historical cache row at a different timeout — must not enter the report
        make_record(2, started_at="2026-07-04T13:00:00Z", wall_sec=99.0, timeout_sec=60),
    )
    spec = make_spec([("sha256:file", "file.egg")], rounds=2, timeout_sec=120)
    selection = models.build_report_selection([make_target("sha256:bin", "main")], spec)

    scoped = web.report_data(rows, selection)["Benchmark report"]

    assert {row["timeout_sec"] for row in scoped} == {120}
    assert all(row["wall_sec"] != 99.0 for row in scoped)


def test_report_data_keeps_only_latest_rounds() -> None:
    rows = make_rows(
        make_record(0, started_at="2026-07-04T12:00:00Z", wall_sec=1.0),
        make_record(1, started_at="2026-07-04T12:00:01Z", wall_sec=2.0),
        make_record(2, started_at="2026-07-04T12:00:02Z", wall_sec=3.0),
    )
    spec = make_spec([("sha256:file", "file.egg")], rounds=2)
    selection = models.build_report_selection([make_target("sha256:bin", "main")], spec)

    scoped = web.report_data(rows, selection)["Benchmark report"]

    assert sorted(row["wall_sec"] for row in scoped) == [2.0, 3.0]


def test_empty_filter_narrows_to_nothing() -> None:
    spec = make_spec([("sha256:file", "file.egg")], rounds=2)
    selection = models.build_report_selection([make_target("sha256:bin", "main")], spec)
    web_registry.configure(selection)
    data = {"Benchmark report": [make_record(0, started_at="2026-07-04T12:00:00Z")]}

    assert web_registry._narrow_raw_rows([], data)["Benchmark report"] == []


def test_filter_narrows_by_file_and_treatment() -> None:
    spec = make_spec([("sha256:fa", "a.egg"), ("sha256:fb", "b.egg")], treatments=("off", "proofs"))
    selection = models.build_report_selection([make_target("sha256:bin", "main")], spec)
    web_registry.configure(selection)
    data = {
        "Benchmark report": [
            make_record(
                0, started_at="2026-07-04T12:00:00Z", file_path="a.egg", file_sha256="sha256:fa", treatment="off"
            ),
            make_record(
                1, started_at="2026-07-04T12:00:01Z", file_path="b.egg", file_sha256="sha256:fb", treatment="proofs"
            ),
        ]
    }

    narrowed = web_registry._narrow_raw_rows([{"File": "a.egg", "Treatment": "off"}], data)

    assert [row["file_path"] for row in narrowed["Benchmark report"]] == ["a.egg"]


def _render_terminal(rows: Any, targets: list[models.ResolvedTarget], spec: models.BenchmarkSpec) -> str:
    stream = io.StringIO()
    console = Console(file=stream, width=200, color_system=None)
    cli.render_report(console, models.ReportDestination(path=None, stream=io.StringIO()), rows, targets, spec)
    return stream.getvalue()


def test_duplicate_labels_render_separately() -> None:
    # two distinct binaries, same display label — the terminal must keep them separate
    rows = make_rows(
        *[
            make_record(
                i,
                started_at=f"2026-07-04T12:00:{i:02d}Z",
                binary_sha256=b,
                treatment=cast("models.Treatment", t),
                wall_sec=1.0 + i,
            )
            for i, (b, t) in enumerate(
                [(b, t) for b in ("sha256:b1", "sha256:b2") for t in ("off", "proofs") for _ in range(2)]
            )
        ]
    )
    spec = make_spec([("sha256:file", "file.egg")], treatments=("off", "proofs"))
    targets = [make_target("sha256:b1", "dup", git_sha="aaa"), make_target("sha256:b2", "dup", git_sha="bbb")]

    output = _render_terminal(rows, targets, spec)

    # one "dup: overhead ratios" table per target (grouped by identity, not label)
    assert output.count("dup: overhead ratios") == 2


def test_terminal_and_web_cells_agree() -> None:
    rows = make_rows(
        *[
            make_record(
                i,
                started_at=f"2026-07-04T12:00:{i:02d}Z",
                binary_sha256=b,
                treatment=cast("models.Treatment", t),
                wall_sec=1.0 + i,
            )
            for i, (b, t) in enumerate(
                [(b, t) for b in ("sha256:base", "sha256:cand") for t in ("off", "proofs") for _ in range(2)]
            )
        ]
    )
    spec = make_spec([("sha256:file", "file.egg")], treatments=("off", "proofs"))
    targets = [make_target("sha256:base", "base"), make_target("sha256:cand", "cand")]
    selection = models.build_report_selection(targets, spec)

    terminal_catalog = {t.web_name: t for t in report.build_report_tables(rows, targets, spec)}
    web_registry.configure(selection)
    data = web.report_data(rows, selection)

    for web_name, table in terminal_catalog.items():
        web_rows = web_registry._make_fn(web_name)(data)
        assert len(web_rows) == len(table.rows)
        for web_row, table_row in zip(web_rows, table.rows, strict=True):
            for column in table.columns:
                cell = web_row.get(column.label)
                text = cell["text"] if isinstance(cell, dict) else cell
                if text is not None:  # dropped-empty columns are absent on the web side
                    assert text == table_row[column.label].text


def test_serve_binds_loopback(monkeypatch: Any) -> None:
    captured: dict[str, Any] = {}

    class FakeServer:
        def __init__(self, address: tuple[str, int], handler: Any) -> None:
            captured["address"] = address

        def serve_forever(self) -> None:
            raise KeyboardInterrupt

        def server_close(self) -> None:
            pass

    monkeypatch.setattr(web.http.server, "HTTPServer", FakeServer)
    monkeypatch.setattr(web.webbrowser, "open", lambda url: None)

    rows = make_rows(
        make_record(0, started_at="2026-07-04T12:00:00Z"),
        make_record(1, started_at="2026-07-04T12:00:01Z"),
    )
    spec = make_spec([("sha256:file", "file.egg")], rounds=2)
    selection = models.build_report_selection([make_target("sha256:bin", "main")], spec)

    web.serve_report(Console(file=io.StringIO()), rows, selection, 8000)

    assert captured["address"] == ("127.0.0.1", 8000)


def test_dump_writes_json_and_latex(tmp_path: Path) -> None:
    rows = make_rows(
        make_record(0, started_at="2026-07-04T12:00:00Z", wall_sec=1.0),
        make_record(1, started_at="2026-07-04T12:00:01Z", wall_sec=1.1),
    )
    spec = make_spec([("sha256:file", "file.egg")], rounds=2)
    selection = models.build_report_selection([make_target("sha256:bin", "main")], spec)

    web.dump_report(Console(file=io.StringIO()), rows, selection, tmp_path)

    names = {path.name for path in tmp_path.iterdir()}
    assert "per-file-wall-time.json" in names
    assert "per-file-wall-time.tex" in names


def test_graph_script_compiles() -> None:
    # The graph script is exec'd as a string in Pyodide; the baked bindings must
    # not push `from __future__ import annotations` off the first statement.
    rows = make_rows(
        make_record(0, started_at="2026-07-04T12:00:00Z"),
        make_record(1, started_at="2026-07-04T12:00:01Z"),
    )
    spec = make_spec([("sha256:file", "file.egg")], rounds=2)
    selection = models.build_report_selection([make_target("sha256:bin", "main")], spec)
    web_registry.configure(selection)
    data = web.report_data(rows, selection)
    script = web.graph_script_source(selection, web_registry.present_tables(data))

    compile(script, "<graph_script>", "exec")  # raises SyntaxError if the future import isn't first
    assert "_SELECTION = {" in script and "_PRESENT_TABLES = [" in script


def test_status_style_maps_cover_all_statuses() -> None:
    # semantics are centralized (models.RESULT_STATUSES); each renderer's style map must cover them
    for status in models.RESULT_STATUSES:
        assert status in cli.RESULT_STYLES, f"cli.RESULT_STYLES missing {status!r}"
        assert status in web_registry.STATUS_STYLE, f"web_registry.STATUS_STYLE missing {status!r}"
