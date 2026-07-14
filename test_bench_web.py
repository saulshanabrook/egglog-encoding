from __future__ import annotations

import json
import sys
import threading
from http.server import HTTPServer
from types import SimpleNamespace
from typing import Any
from urllib.error import HTTPError
from urllib.request import Request, urlopen

import pytest

import bench
import bench_web


def table(
    title: str,
    headers: tuple[str, ...] = ("File", "Result"),
    rows: tuple[tuple[str, ...], ...] = (("a.egg", "faster"),),
) -> bench.ReportTableData:
    return bench.ReportTableData(title=title, headers=headers, rows=rows)


def install_fake_eval_live(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setitem(
        sys.modules,
        "eval_live",
        SimpleNamespace(js=lambda: "/* eval-live js */", css=lambda: "/* eval-live css */"),
    )


def test_report_payload_preserves_order_and_forward_fills_elided_files() -> None:
    source = table(
        "Per-file results",
        headers=("File", "Backend", "Result"),
        rows=(("a.egg", "main", "faster"), ("", "dd", "slower"), ("b.egg", "main", "unclear")),
    )

    payload = bench_web.report_payload([source])

    assert payload == {
        "Per-file results": [
            {"File": "a.egg", "Backend": "main", "Result": "faster"},
            {"File": "a.egg", "Backend": "dd", "Result": "slower"},
            {"File": "b.egg", "Backend": "main", "Result": "unclear"},
        ]
    }
    assert source.rows[1][0] == ""
    assert list(payload["Per-file results"][0]) == ["File", "Backend", "Result"]


def test_report_payload_disambiguates_colliding_titles() -> None:
    source = (table("Same"), table("Same (2)"), table("Same"), table("Same"))

    assert list(bench_web.report_payload(source)) == ["Same", "Same (2)", "Same (3)", "Same (4)"]


def test_report_payload_keeps_hostile_text_in_json_data_not_html(monkeypatch: pytest.MonkeyPatch) -> None:
    install_fake_eval_live(monkeypatch)
    hostile = '</script><img src=x onerror="alert(1)">&\nnext'
    routes = bench_web.static_routes([table(hostile, ("File", "Value"), ((hostile, hostile),))])

    assert hostile not in routes["/"].body.decode()
    assert json.loads(routes["/report.json"].body) == {hostile: [{"File": hostile, "Value": hostile}]}
    html = routes["/"].body.decode()
    assert 'fetch("/report.json", {cache: "no-store"})' in html
    assert 'initEvalLive("eval-live-root", data, "Benchmark Report")' in html
    assert "pyodide" not in html.lower()


def test_static_endpoints_and_headers(monkeypatch: pytest.MonkeyPatch) -> None:
    install_fake_eval_live(monkeypatch)
    routes = bench_web.static_routes([table("Results")])
    server = HTTPServer(("127.0.0.1", 0), bench_web.static_handler(routes))
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    base = f"http://127.0.0.1:{server.server_port}"
    try:
        expected = {
            "/": "text/html; charset=utf-8",
            "/report.json": "application/json; charset=utf-8",
            "/eval-live.js": "text/javascript; charset=utf-8",
            "/eval-live.css": "text/css; charset=utf-8",
        }
        for path, content_type in expected.items():
            with urlopen(base + path) as response:  # noqa: S310 - loopback test server
                body = response.read()
                assert response.status == 200
                assert response.headers["Content-Type"] == content_type
                assert response.headers["Content-Length"] == str(len(body))
                assert response.headers["Cache-Control"] == "no-store"
                assert response.headers["X-Content-Type-Options"] == "nosniff"

        with urlopen(Request(base + "/report.json", method="HEAD")) as response:  # noqa: S310
            assert response.status == 200
            assert response.read() == b""
            assert int(response.headers["Content-Length"]) > 0

        with pytest.raises(HTTPError) as error:
            urlopen(base + "/missing")  # noqa: S310 - loopback test server
        assert error.value.code == 404
        assert error.value.headers["Cache-Control"] == "no-store"
        assert error.value.headers["X-Content-Type-Options"] == "nosniff"
    finally:
        server.shutdown()
        thread.join(timeout=5)
        server.server_close()


def test_serve_report_binds_loopback_opens_best_effort_and_closes(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    install_fake_eval_live(monkeypatch)
    observed: dict[str, Any] = {}

    class FakeServer:
        server_port = 8123

        def __init__(self, address: tuple[str, int], handler: Any) -> None:
            observed["address"] = address

        def serve_forever(self) -> None:
            raise KeyboardInterrupt

        def server_close(self) -> None:
            observed["closed"] = True

    def fail_to_open(url: str) -> None:
        observed["url"] = url
        raise RuntimeError("no browser")

    monkeypatch.setattr(bench_web.http.server, "HTTPServer", FakeServer)
    monkeypatch.setattr(bench_web.webbrowser, "open", fail_to_open)

    bench_web.serve_report([table("Results")], port=8123)

    assert observed == {
        "address": ("127.0.0.1", 8123),
        "url": "http://127.0.0.1:8123/",
        "closed": True,
    }


def test_serve_report_reports_bind_errors_clearly(monkeypatch: pytest.MonkeyPatch) -> None:
    install_fake_eval_live(monkeypatch)

    def fail_to_bind(address: tuple[str, int], handler: Any) -> None:
        raise OSError("address already in use")

    monkeypatch.setattr(bench_web.http.server, "HTTPServer", fail_to_bind)

    with pytest.raises(ValueError, match=r"127\.0\.0\.1:8123.*address already in use"):
        bench_web.serve_report([table("Results")], port=8123)
