"""Static eval-live presentation for already-computed benchmark tables.

This module deliberately knows nothing about benchmark rows or report
calculation.  It accepts the final table values that the terminal and Markdown
renderers consume, exposes them as eval-live raw tables, and serves four fixed
loopback-only resources.
"""

from __future__ import annotations

import http.server
import importlib
import json
import webbrowser
from collections.abc import Sequence
from contextlib import suppress
from dataclasses import dataclass
from typing import Any, Protocol, cast


class FinalReportTable(Protocol):
    """The part of ``ReportTableData`` needed by the static web adapter."""

    @property
    def title(self) -> str: ...

    @property
    def headers(self) -> Sequence[str]: ...

    @property
    def rows(self) -> Sequence[Sequence[str]]: ...


class ConsoleLike(Protocol):
    def print(self, message: str) -> Any: ...


class EvalLiveModule(Protocol):
    def css(self) -> str: ...

    def js(self) -> str: ...


TableSource = Sequence[FinalReportTable]
ReportPayload = dict[str, list[dict[str, str]]]


@dataclass(frozen=True)
class StaticAsset:
    body: bytes
    content_type: str


INDEX_HTML = b"""<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>Benchmark Report</title>
  <link rel="stylesheet" href="/eval-live.css">
</head>
<body>
  <main id="eval-live-root"></main>
  <script src="/eval-live.js"></script>
  <script>
    "use strict";
    fetch("/report.json", {cache: "no-store"})
      .then((response) => {
        if (!response.ok) throw new Error(`report request failed: ${response.status}`);
        return response.json();
      })
      .then((data) => initEvalLive("eval-live-root", data, "Benchmark Report"))
      .catch((error) => {
        document.getElementById("eval-live-root").textContent = `Unable to load report: ${error}`;
      });
  </script>
</body>
</html>
"""


def _unique_title(title: str, used: set[str]) -> str:
    if title not in used:
        used.add(title)
        return title
    suffix = 2
    while f"{title} ({suffix})" in used:
        suffix += 1
    unique = f"{title} ({suffix})"
    used.add(unique)
    return unique


def _require_string(value: object, location: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{location} must be a string, got {type(value).__name__}")
    return value


def report_payload(source: TableSource) -> ReportPayload:
    """Serialize final tables to eval-live's ``{title: [row objects]}`` shape.

    Column and table order follow the input.  Rich-style elision of repeated
    ``File`` cells is undone in this web-only copy so every independently
    filterable row retains its file identity.
    """

    payload: ReportPayload = {}
    used_titles: set[str] = set()
    for table_index, table in enumerate(source):
        title = _require_string(table.title, f"table {table_index} title")
        headers = tuple(
            _require_string(header, f"table {title!r} header {header_index}")
            for header_index, header in enumerate(table.headers)
        )
        if len(set(headers)) != len(headers):
            raise ValueError(f"table {title!r} has duplicate headers")
        file_index = headers.index("File") if "File" in headers else None
        last_file = ""
        web_rows: list[dict[str, str]] = []
        for row_index, source_row in enumerate(table.rows):
            if len(source_row) != len(headers):
                raise ValueError(
                    f"table {title!r} row {row_index} has {len(source_row)} cells; expected {len(headers)}"
                )
            row = [
                _require_string(value, f"table {title!r} row {row_index} column {headers[column_index]!r}")
                for column_index, value in enumerate(source_row)
            ]
            if file_index is not None:
                if row[file_index]:
                    last_file = row[file_index]
                elif last_file:
                    row[file_index] = last_file
            web_rows.append(dict(zip(headers, row, strict=True)))
        payload[_unique_title(title, used_titles)] = web_rows
    return payload


def static_routes(source: TableSource) -> dict[str, StaticAsset]:
    """Build the fixed resources for one report, importing eval-live lazily."""

    eval_live = cast("EvalLiveModule", importlib.import_module("eval_live"))
    payload = (json.dumps(report_payload(source), ensure_ascii=False, separators=(",", ":")) + "\n").encode()
    return {
        "/": StaticAsset(INDEX_HTML, "text/html; charset=utf-8"),
        "/report.json": StaticAsset(payload, "application/json; charset=utf-8"),
        "/eval-live.js": StaticAsset(eval_live.js().encode(), "text/javascript; charset=utf-8"),
        "/eval-live.css": StaticAsset(eval_live.css().encode(), "text/css; charset=utf-8"),
    }


def static_handler(routes: dict[str, StaticAsset]) -> type[http.server.BaseHTTPRequestHandler]:
    """Return a quiet handler that serves only the supplied exact paths."""

    class StaticReportHandler(http.server.BaseHTTPRequestHandler):
        def _respond(self, *, include_body: bool) -> None:
            asset = routes.get(self.path)
            status = 200
            if asset is None:
                status = 404
                asset = StaticAsset(b"Not found\n", "text/plain; charset=utf-8")
            self.send_response(status)
            self.send_header("Content-Type", asset.content_type)
            self.send_header("Content-Length", str(len(asset.body)))
            self.send_header("Cache-Control", "no-store")
            self.send_header("X-Content-Type-Options", "nosniff")
            self.end_headers()
            if include_body:
                self.wfile.write(asset.body)

        def do_GET(self) -> None:
            self._respond(include_body=True)

        def do_HEAD(self) -> None:
            self._respond(include_body=False)

        def log_message(self, format: str, *args: object) -> None:
            return

    return StaticReportHandler


def serve_report(source: TableSource, *, port: int = 8000, console: ConsoleLike | None = None) -> None:
    """Serve final report tables on loopback until interrupted."""

    routes = static_routes(source)
    try:
        server = http.server.HTTPServer(("127.0.0.1", port), static_handler(routes))
    except OSError as error:
        raise ValueError(f"could not bind eval-live report server to 127.0.0.1:{port}: {error}") from error

    bound_port = int(getattr(server, "server_port", port))
    url = f"http://127.0.0.1:{bound_port}/"
    try:
        if console is not None:
            console.print(f"Serving eval-live report at {url} (Ctrl-C to stop)")
        with suppress(Exception):
            webbrowser.open(url)
        try:
            server.serve_forever()
        except KeyboardInterrupt:
            if console is not None:
                console.print("Server stopped.")
    finally:
        server.server_close()
