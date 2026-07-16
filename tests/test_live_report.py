"""Test the cache-only live catalog adapter, scope replacement, and loopback API."""

from __future__ import annotations

import json
import threading
from http.client import HTTPConnection
from http.server import HTTPServer
from pathlib import Path
from typing import Any, cast
from urllib.error import HTTPError
from urllib.request import Request, urlopen

import pytest

from benchmarking import models
from benchmarking.reports import live
from benchmarking.reports.catalog import (
    ReportCatalog,
    ReportColumn,
    ReportMessage,
    ReportOptions,
    ReportRow,
    ReportScope,
    ReportSection,
    ReportTable,
    report_id,
    text_cell,
)
from benchmarking.reports.database import ReportDatabase
from benchmarking.reports.summary import build_report_catalog

from .conftest import make_record, make_target, write_report


def test_live_payload_preserves_catalog_order_values_styles_and_messages(tmp_path: Path) -> None:
    target = make_target()
    file = models.FileSpec("file.egg", tmp_path / "file.egg", "sha256:file")
    scope = ReportScope((target,), models.BenchmarkSpec((file,), ("off",), 1, 120))
    table = ReportTable(
        report_id("table", "results"),
        "Results",
        (
            ReportColumn("hidden", "Hidden", visible=False),
            ReportColumn("backend", "Backend"),
            ReportColumn("ratio", "Ratio", "right"),
        ),
        (
            ReportRow(
                report_id("row", "one"),
                (
                    text_cell("secret"),
                    text_cell("main"),
                    text_cell(0.8, "0.800x", tone="positive"),
                ),
            ),
        ),
        caption="Lower is faster.",
    )
    message = ReportMessage(report_id("message", "timing"), None, "Other includes uncategorized time.", "muted")
    caption = ReportMessage(
        report_id("message", "caption"),
        None,
        "Intervals are descriptive.",
        "muted",
        "caption",
    )
    catalog = ReportCatalog(
        str(tmp_path / "report.jsonl"),
        1,
        None,
        (ReportSection("summary", "Benchmark Summary", (table, caption, message)),),
    )

    payload = live.LiveReportSession(tmp_path / "report.jsonl", scope, ReportOptions(), catalog).payload()

    assert "schema_version" not in payload
    assert payload["sections"] == [
        {
            "id": "summary",
            "title": "Benchmark Summary",
            "blocks": [
                {
                    "kind": "table",
                    "id": table.id,
                    "name": "Results",
                    "caption": "Lower is faster.",
                    "columns": [
                        {"id": "backend", "name": "Backend", "alignment": "left"},
                        {"id": "ratio", "name": "Ratio", "alignment": "right"},
                    ],
                    "rows": [
                        {
                            "backend": "main",
                            "ratio": {"value": 0.8, "text": "0.800x", "style": {"color": "green"}},
                        }
                    ],
                },
                {
                    "kind": "message",
                    "id": caption.id,
                    "title": None,
                    "text": "Intervals are descriptive.",
                    "tone": "muted",
                    "layout": "caption",
                },
                {
                    "kind": "message",
                    "id": message.id,
                    "title": None,
                    "text": "Other includes uncategorized time.",
                    "tone": "muted",
                    "layout": "text",
                },
            ],
        }
    ]


def test_scope_apply_retargets_cached_rows_and_failed_replacement_is_atomic(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    report_path = tmp_path / "report.jsonl"
    write_report(
        report_path,
        make_record(
            0,
            started_at="2026-07-16T12:00:00Z",
            binary_sha256="sha256:baseline",
            wall_sec=1.0,
        ),
        make_record(
            1,
            started_at="2026-07-16T12:00:01Z",
            binary_sha256="sha256:candidate",
            wall_sec=2.0,
        ),
    )
    file = models.FileSpec("file.egg", tmp_path / "file.egg", "sha256:file")
    baseline = make_target(target_label="baseline", binary_sha256="sha256:baseline")
    candidate = make_target(target_label="candidate", binary_sha256="sha256:candidate")
    spec = models.BenchmarkSpec((file,), ("off",), 1, 120)
    scope = ReportScope((baseline, candidate), spec)
    options = ReportOptions(phase_timings=True)
    with ReportDatabase(report_path) as database:
        catalog = build_report_catalog(database, scope, options)
    session = live.LiveReportSession(report_path, scope, options, catalog)
    file_id = report_id("file", file.sha256, file.fact_directory_sha256)

    narrowed = session.apply(
        {
            "target_ids": [candidate.binary_sha256],
            "baseline_target_id": candidate.binary_sha256,
            "file_ids": [file_id],
            "backends": ["main"],
            "treatments": ["off"],
            "rounds": 1,
            "timeout_sec": 120,
            "phase_timings": False,
            "detailed_timing": False,
        }
    )
    narrowed_data = cast(dict[str, Any], narrowed)
    selectors = narrowed_data["selectors"]
    assert [choice["selected"] for choice in selectors["targets"]] == [False, True]
    blocks = [block for section in narrowed_data["sections"] for block in section["blocks"]]
    targets_table = next(table for table in blocks if table["id"] == report_id("table", "targets"))
    assert targets_table["rows"][0]["role"] == "target"
    assert targets_table["rows"][0]["label"] == "candidate"
    assert not any(section["title"] == "Engine Timing" for section in narrowed_data["sections"])

    before_failure = session.payload()

    def fail_build(*_args: object, **_kwargs: object) -> ReportCatalog:
        raise ValueError("replacement failed")

    monkeypatch.setattr(live, "build_report_catalog", fail_build)
    with pytest.raises(ValueError, match="replacement failed"):
        session.apply(
            {
                "target_ids": [baseline.binary_sha256, candidate.binary_sha256],
                "baseline_target_id": baseline.binary_sha256,
                "file_ids": [file_id],
                "backends": ["main"],
                "treatments": ["off"],
                "rounds": 1,
                "timeout_sec": 120,
                "phase_timings": True,
                "detailed_timing": False,
            }
        )
    assert session.payload() == before_failure


def test_scope_request_rejects_values_outside_the_invocation(tmp_path: Path) -> None:
    session, request = _minimal_session(tmp_path)
    request["target_ids"] = ["sha256:unknown"]
    request["baseline_target_id"] = "sha256:unknown"

    with pytest.raises(ValueError, match="unknown target id"):
        session.apply(request)


def test_scope_request_rejects_values_outside_the_sql_scope_type(tmp_path: Path) -> None:
    session, request = _minimal_session(tmp_path)
    request["rounds"] = 1 << 32

    with pytest.raises(ValueError, match="rounds must be at most 4294967295"):
        session.apply(request)


def test_live_endpoints_and_atomic_error_response() -> None:
    class StubSession:
        current: dict[str, object] = {"value": "initial"}

        def payload(self) -> dict[str, object]:
            return self.current

        def apply(self, value: object) -> dict[str, object]:
            if value == {"fail": True}:
                raise ValueError("replacement failed")
            self.current = {"value": value}
            return self.current

    assets = {
        "/": live.StaticAsset(b"index", "text/html; charset=utf-8"),
        "/app.js": live.StaticAsset(b"app", "text/javascript; charset=utf-8"),
    }
    session = StubSession()
    server = HTTPServer(("127.0.0.1", 0), live.live_handler(session, assets))  # type: ignore[arg-type]
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    base = f"http://127.0.0.1:{server.server_port}"
    try:
        with urlopen(base + "/api/report") as response:  # noqa: S310 - loopback test server
            assert json.load(response) == {"value": "initial"}
            assert response.headers["Cache-Control"] == "no-store"
            assert response.headers["X-Content-Type-Options"] == "nosniff"

        update = Request(
            base + "/api/scope",
            data=json.dumps({"rounds": 2}).encode(),
            method="PUT",
            headers={"Content-Type": "application/json"},
        )
        with urlopen(update) as response:  # noqa: S310 - loopback test server
            assert json.load(response) == {"value": {"rounds": 2}}

        failure = Request(
            base + "/api/scope",
            data=json.dumps({"fail": True}).encode(),
            method="PUT",
            headers={"Content-Type": "application/json"},
        )
        with pytest.raises(HTTPError) as error, urlopen(failure):  # noqa: S310 - loopback test server
            pass
        assert error.value.code == 400
        assert json.load(error.value) == {"error": "replacement failed"}
        assert session.payload() == {"value": {"rounds": 2}}

        connection = HTTPConnection("127.0.0.1", server.server_port, timeout=5)
        connection.putrequest("PUT", "/api/scope")
        connection.putheader("Content-Length", str((1 << 20) + 1))
        connection.endheaders()
        oversized = connection.getresponse()
        assert oversized.status == 400
        assert json.load(oversized) == {"error": "scope request body must be between 1 and 1048576 bytes"}
        connection.close()

        with urlopen(Request(base + "/app.js", method="HEAD")) as response:  # noqa: S310
            assert response.read() == b""
            assert response.headers["Content-Length"] == "3"

        with pytest.raises(HTTPError) as missing, urlopen(base + "/missing"):  # noqa: S310
            pass
        assert missing.value.code == 404
    finally:
        server.shutdown()
        thread.join(timeout=5)
        server.server_close()


def test_live_server_uses_an_os_selected_port_and_closes(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    session, _request = _minimal_session(tmp_path)
    observed: dict[str, object] = {}
    messages: list[str] = []
    opened = threading.Event()

    class StubServer:
        server_port = 4312

        def serve_forever(self) -> None:
            raise KeyboardInterrupt

        def server_close(self) -> None:
            observed["closed"] = True

    def make_server(address: tuple[str, int], _handler: object) -> StubServer:
        observed["address"] = address
        return StubServer()

    class StubConsole:
        def print(self, message: str) -> None:
            messages.append(message)

    def open_browser(url: str) -> None:
        observed["url"] = url
        opened.set()

    monkeypatch.setattr(live.http.server, "HTTPServer", make_server)
    monkeypatch.setattr(live.webbrowser, "open", open_browser)

    live.serve_live_report(session, console=StubConsole())

    assert opened.wait(timeout=1)
    assert observed["address"] == ("127.0.0.1", 0)
    assert observed["url"] == "http://127.0.0.1:4312/"
    assert observed["closed"] is True
    assert messages == [
        "Serving live benchmark report at http://127.0.0.1:4312/ (Ctrl-C to stop)",
        "Server stopped.",
    ]


def test_browser_application_uses_precomputed_tables_and_one_scope_request() -> None:
    script = live.APP_JS

    assert "initEvalLiveCatalog(reportRoot, payload.sections" in script
    assert 'fetch("/api/report"' in script
    assert script.count('fetch("/api/scope"') == 1
    assert "Pyodide" not in script
    assert "renderScope(currentPayload.selectors" in script


def _minimal_session(tmp_path: Path) -> tuple[live.LiveReportSession, dict[str, object]]:
    report_path = tmp_path / "report.jsonl"
    target = make_target()
    file = models.FileSpec("file.egg", tmp_path / "file.egg", "sha256:file")
    spec = models.BenchmarkSpec((file,), ("off",), 1, 120)
    scope = ReportScope((target,), spec)
    catalog = ReportCatalog(str(report_path), 1, None, ())
    request: dict[str, object] = {
        "target_ids": [target.binary_sha256],
        "baseline_target_id": target.binary_sha256,
        "file_ids": [report_id("file", file.sha256, file.fact_directory_sha256)],
        "backends": ["main"],
        "treatments": ["off"],
        "rounds": 1,
        "timeout_sec": 120,
        "phase_timings": False,
        "detailed_timing": False,
    }
    return live.LiveReportSession(report_path, scope, ReportOptions(), catalog), request
