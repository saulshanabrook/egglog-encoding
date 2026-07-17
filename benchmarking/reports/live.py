"""Serve one cached pair report as a live, cache-only browser application.

This module adapts the shared report catalog to eval-live, discovers complete
cached endpoints from one loaded report snapshot, validates browser retargeting
requests, and owns the loopback HTTP server and static UI. It never resolves
targets, builds binaries, collects observations, or polls external cache edits;
analysis and human-facing wording remain in their sibling modules.
"""

from __future__ import annotations

import http.server
import importlib
import json
import threading
import webbrowser
from collections.abc import Mapping, Sequence
from contextlib import suppress
from dataclasses import dataclass
from typing import Any, Protocol, cast

from ..models import (
    BenchmarkEndpoint,
    ComparisonSpec,
    DetailLevel,
    FileSpec,
    ResolvedTarget,
    TargetRequest,
)
from .catalog import CellTone, ReportCatalog, ReportCell, ReportMessage, ReportOptions, report_id
from .comparison import build_report_catalog, report_file_labels
from .store import CachedEndpoint, ReportStore


class ConsoleLike(Protocol):
    """The output operation used by the blocking server lifecycle."""

    def print(self, message: str) -> Any: ...


class EvalLiveModule(Protocol):
    """The two packaged static assets consumed from the pinned dependency."""

    def css(self) -> str: ...

    def js(self) -> str: ...


type JsonScalar = str | int | float | bool | None
type JsonValue = JsonScalar | list[JsonValue] | dict[str, JsonValue]

_MAX_SCOPE_REQUEST_BYTES = 1 << 20
_DETAIL_LEVELS: tuple[DetailLevel, ...] = ("summary", "files", "phases", "rulesets")


@dataclass(frozen=True)
class StaticAsset:
    """One exact HTTP resource and its response media type."""

    body: bytes
    content_type: str


@dataclass(frozen=True)
class LiveScopeRequest:
    """The mutable selectors within a session's fixed cache coordinates."""

    baseline_endpoint_id: str
    candidate_endpoint_id: str
    file_ids: tuple[str, ...]
    detail: DetailLevel


class LiveReportSession:
    """Own one immutable cache universe and an atomically replaced pair report."""

    def __init__(
        self,
        store: ReportStore,
        comparison: ComparisonSpec,
        options: ReportOptions,
        catalog: ReportCatalog,
    ) -> None:
        self._store = store
        self._files = comparison.files
        self._rounds = comparison.rounds
        self._timeout_sec = comparison.timeout_sec
        cached = store.complete_cached_endpoints(
            self._files,
            self._rounds,
            self._timeout_sec,
        )
        self._endpoints = tuple(_benchmark_endpoint(endpoint) for endpoint in cached)
        self._endpoint_by_id = {_endpoint_id(endpoint): endpoint for endpoint in self._endpoints}
        self._file_by_id = {_file_id(file): file for file in self._files}

        baseline_id = _endpoint_id(comparison.baseline)
        candidate_id = _endpoint_id(comparison.candidate)
        missing = tuple(
            role
            for role, endpoint_id in (("baseline", baseline_id), ("candidate", candidate_id))
            if endpoint_id not in self._endpoint_by_id
        )
        if missing:
            raise ValueError("initial live report endpoint(s) are not complete in the cache: " + ", ".join(missing))
        self._request = LiveScopeRequest(
            baseline_id,
            candidate_id,
            tuple(self._file_by_id),
            options.detail,
        )
        self._catalog = catalog

    def payload(self) -> dict[str, JsonValue]:
        """Return the complete current selector state and presentation catalog."""

        return self._payload(self._request, self._catalog)

    def apply(self, value: object) -> dict[str, JsonValue]:
        """Validate and compute a replacement before publishing any state."""

        request = self._parse_request(value)
        selected_file_ids = set(request.file_ids)
        files = tuple(file for file in self._files if _file_id(file) in selected_file_ids)
        comparison = ComparisonSpec(
            baseline=self._endpoint_by_id[request.baseline_endpoint_id],
            candidate=self._endpoint_by_id[request.candidate_endpoint_id],
            files=files,
            rounds=self._rounds,
            timeout_sec=self._timeout_sec,
        )
        options = ReportOptions(request.detail)

        # Compute the replacement before publishing it so a report-assembly
        # error leaves both the prior request and catalog untouched.
        catalog = build_report_catalog(self._store, comparison, options)
        payload = self._payload(request, catalog)
        self._request = request
        self._catalog = catalog
        return payload

    def _payload(self, request: LiveScopeRequest, catalog: ReportCatalog) -> dict[str, JsonValue]:
        return {
            "report_path": self._store.display_path,
            "selectors": self._selector_payload(request),
            "sections": _catalog_payload(catalog),
        }

    def _parse_request(self, value: object) -> LiveScopeRequest:
        request = _object(value, "scope request")
        baseline_id = _string(request, "baseline_endpoint_id")
        candidate_id = _string(request, "candidate_endpoint_id")
        _require_known(baseline_id, self._endpoint_by_id, "baseline endpoint")
        _require_known(candidate_id, self._endpoint_by_id, "candidate endpoint")
        if baseline_id == candidate_id:
            raise ValueError("baseline and candidate endpoints must be different")
        file_ids = _string_list(request, "file_ids")
        _require_known_subset(file_ids, self._file_by_id, "file")
        detail = _string(request, "detail")
        if detail not in _DETAIL_LEVELS:
            raise ValueError(f"unknown detail level: {detail}")
        return LiveScopeRequest(
            baseline_id,
            candidate_id,
            file_ids,
            cast(DetailLevel, detail),
        )

    def _selector_payload(self, request: LiveScopeRequest) -> dict[str, JsonValue]:
        labels = report_file_labels(self._files)
        selected_files = set(request.file_ids)
        return {
            "endpoints": [
                {
                    "id": _endpoint_id(endpoint),
                    "label": _endpoint_label(endpoint),
                    "target": endpoint.target.display_label,
                    "git_sha": endpoint.target.row.git_sha,
                    "dirty": endpoint.target.row.is_dirty,
                    "backend": endpoint.backend,
                    "treatment": endpoint.treatment,
                }
                for endpoint in self._endpoints
            ],
            "baseline_endpoint_id": request.baseline_endpoint_id,
            "candidate_endpoint_id": request.candidate_endpoint_id,
            "files": [
                {
                    "id": _file_id(file),
                    "label": labels[file],
                    "selected": _file_id(file) in selected_files,
                }
                for file in self._files
            ],
            "detail": request.detail,
            "rounds": self._rounds,
            "timeout_sec": self._timeout_sec,
        }


def _benchmark_endpoint(cached: CachedEndpoint) -> BenchmarkEndpoint:
    """Restore a report-only resolved endpoint from its cached provenance."""

    row = cached.row
    target = ResolvedTarget(
        TargetRequest(row.label or row.source, row.source, row.label),
        row,
        cached.binary_sha256,
        None,
    )
    return BenchmarkEndpoint(target, cached.backend, cached.treatment)


def _endpoint_id(endpoint: BenchmarkEndpoint) -> str:
    return report_id("endpoint", *endpoint.cache_identity)


def _endpoint_label(endpoint: BenchmarkEndpoint) -> str:
    dirty = " dirty" if endpoint.target.row.is_dirty else ""
    return (
        f"{endpoint.target.display_label} · {endpoint.target.row.git_sha[:12]}{dirty} "
        f"· {endpoint.backend}/{endpoint.treatment}"
    )


def _file_id(file: FileSpec) -> str:
    return report_id("file", file.sha256, file.fact_directory_sha256)


def live_assets() -> dict[str, StaticAsset]:
    """Load the pinned eval-live assets and return fixed browser resources."""

    eval_live = cast(EvalLiveModule, importlib.import_module("eval_live"))
    return {
        "/": StaticAsset(INDEX_HTML, "text/html; charset=utf-8"),
        "/app.js": StaticAsset(APP_JS.encode(), "text/javascript; charset=utf-8"),
        "/eval-live.js": StaticAsset(eval_live.js().encode(), "text/javascript; charset=utf-8"),
        "/eval-live.css": StaticAsset(
            (eval_live.css() + "\n" + APP_CSS).encode(),
            "text/css; charset=utf-8",
        ),
    }


def live_handler(
    session: LiveReportSession,
    assets: Mapping[str, StaticAsset] | None = None,
) -> type[http.server.BaseHTTPRequestHandler]:
    """Return a quiet exact-route handler for one single-threaded live session."""

    route_assets = live_assets() if assets is None else assets

    class LiveReportHandler(http.server.BaseHTTPRequestHandler):
        def _respond(self, status: int, asset: StaticAsset, *, include_body: bool) -> None:
            self.send_response(status)
            self.send_header("Content-Type", asset.content_type)
            self.send_header("Content-Length", str(len(asset.body)))
            self.send_header("Cache-Control", "no-store")
            self.send_header("X-Content-Type-Options", "nosniff")
            self.end_headers()
            if include_body:
                self.wfile.write(asset.body)

        def _json_response(self, status: int, value: object, *, include_body: bool = True) -> None:
            body = (json.dumps(value, ensure_ascii=False, separators=(",", ":")) + "\n").encode()
            self._respond(status, StaticAsset(body, "application/json; charset=utf-8"), include_body=include_body)

        def do_GET(self) -> None:
            if self.path == "/api/report":
                self._json_response(200, session.payload())
                return
            asset = route_assets.get(self.path)
            if asset is None:
                self._respond(404, _NOT_FOUND, include_body=True)
                return
            self._respond(200, asset, include_body=True)

        def do_HEAD(self) -> None:
            if self.path == "/api/report":
                self._json_response(200, session.payload(), include_body=False)
                return
            asset = route_assets.get(self.path)
            if asset is None:
                self._respond(404, _NOT_FOUND, include_body=False)
                return
            self._respond(200, asset, include_body=False)

        def do_PUT(self) -> None:
            if self.path != "/api/scope":
                self._respond(404, _NOT_FOUND, include_body=True)
                return
            try:
                length = int(self.headers.get("Content-Length", "0"))
                if length < 1 or length > _MAX_SCOPE_REQUEST_BYTES:
                    raise ValueError(f"scope request body must be between 1 and {_MAX_SCOPE_REQUEST_BYTES} bytes")
                value = json.loads(self.rfile.read(length))
                payload = session.apply(value)
            except (json.JSONDecodeError, TypeError, UnicodeDecodeError, ValueError) as error:
                self._json_response(400, {"error": str(error)})
                return
            self._json_response(200, payload)

        def log_message(self, format: str, *args: object) -> None:
            return

    return LiveReportHandler


def serve_live_report(
    session: LiveReportSession,
    *,
    port: int | None = None,
    console: ConsoleLike | None = None,
) -> None:
    """Serve one report on loopback until interrupted, opening a browser best-effort."""

    bind_port = 0 if port is None else port
    try:
        server = http.server.HTTPServer(("127.0.0.1", bind_port), live_handler(session))
    except OSError as error:
        raise ValueError(f"could not bind live report server to 127.0.0.1:{bind_port}: {error}") from error

    bound_port = int(getattr(server, "server_port", bind_port))
    url = f"http://127.0.0.1:{bound_port}/"
    try:
        if console is not None:
            console.print(f"Serving live benchmark report at {url} (Ctrl-C to stop)")
        threading.Thread(target=_open_browser, args=(url,), daemon=True).start()
        try:
            server.serve_forever()
        except KeyboardInterrupt:
            if console is not None:
                console.print("Server stopped.")
    finally:
        server.server_close()


def _open_browser(url: str) -> None:
    """Open the live URL best-effort without delaying request handling."""

    with suppress(Exception):
        webbrowser.open(url)


def _catalog_payload(catalog: ReportCatalog) -> list[JsonValue]:
    sections: list[JsonValue] = []
    for section in catalog.sections:
        blocks: list[JsonValue] = []
        for block in section.blocks:
            if isinstance(block, ReportMessage):
                blocks.append(
                    {
                        "kind": "message",
                        "id": block.id,
                        "title": block.title,
                        "text": block.text,
                        "tone": block.tone,
                        "layout": block.layout,
                    }
                )
                continue
            visible = tuple((index, column) for index, column in enumerate(block.columns) if column.visible)
            blocks.append(
                {
                    "kind": "table",
                    "id": block.id,
                    "name": block.title,
                    "caption": block.caption,
                    "columns": [
                        {"id": column.id, "name": column.label, "alignment": column.alignment} for _, column in visible
                    ],
                    "rows": [
                        {column.id: _cell_payload(row.cells[index]) for index, column in visible} for row in block.rows
                    ],
                }
            )
        sections.append({"id": section.id, "title": section.title, "blocks": blocks})
    return sections


def _cell_payload(cell: ReportCell) -> JsonValue:
    primitive = isinstance(cell.raw, (str, int, bool))
    if cell.tone == "default" and primitive and cell.display == _primitive_display(cell.raw):
        return cell.raw
    payload: dict[str, JsonValue] = {"value": cell.raw, "text": cell.display}
    style = _tone_style(cell.tone)
    if style:
        payload["style"] = style
    return payload


def _primitive_display(value: JsonScalar) -> str:
    if value is True:
        return "true"
    if value is False:
        return "false"
    return str(value)


def _tone_style(tone: CellTone) -> dict[str, JsonValue]:
    if tone == "positive":
        return {"color": "green"}
    if tone == "negative":
        return {"color": "red"}
    if tone == "warning":
        return {"color": "yellow"}
    if tone == "error":
        return {"color": "red", "bold": True}
    if tone == "muted":
        return {"dim": True}
    return {}


def _object(value: object, name: str) -> Mapping[str, object]:
    if not isinstance(value, dict):
        raise ValueError(f"{name} must be a JSON object")
    return cast(Mapping[str, object], value)


def _string(request: Mapping[str, object], key: str) -> str:
    value = request.get(key)
    if not isinstance(value, str):
        raise ValueError(f"{key} must be a string")
    return value


def _string_list(request: Mapping[str, object], key: str) -> tuple[str, ...]:
    value = request.get(key)
    if not isinstance(value, list) or not all(isinstance(item, str) for item in value):
        raise ValueError(f"{key} must be a JSON array of strings")
    values = cast(list[str], value)
    if not values:
        raise ValueError(f"{key} must not be empty")
    if len(set(values)) != len(values):
        raise ValueError(f"{key} must not contain duplicates")
    return tuple(values)


def _require_known(value: str, choices: Mapping[str, object], name: str) -> None:
    if value not in choices:
        raise ValueError(f"unknown {name} id: {value}")


def _require_known_subset(values: Sequence[str], choices: Mapping[str, object], name: str) -> None:
    unknown = tuple(value for value in values if value not in choices)
    if unknown:
        raise ValueError(f"unknown {name} id(s): {', '.join(unknown)}")


_NOT_FOUND = StaticAsset(b"Not found\n", "text/plain; charset=utf-8")

INDEX_HTML = b"""<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>Benchmark Report</title>
  <link rel="icon" href="data:,">
  <link rel="stylesheet" href="/eval-live.css">
</head>
<body>
  <section id="scope-root" aria-label="Report scope"></section>
  <main id="eval-live-root"></main>
  <script src="/eval-live.js"></script>
  <script src="/app.js"></script>
</body>
</html>
"""

APP_JS = """"use strict";

const scopeRoot = document.getElementById("scope-root");
const reportRoot = document.getElementById("eval-live-root");
let currentPayload = null;

function element(tag, text, className) {
  const node = document.createElement(tag);
  if (text !== undefined && text !== null) node.textContent = text;
  if (className) node.className = className;
  return node;
}

function endpointField(labelText, id, endpoints, selectedId) {
  const label = element("label", labelText + " ");
  const select = element("select");
  select.id = id;
  for (const endpoint of endpoints) {
    const option = element("option", endpoint.label);
    option.value = endpoint.id;
    option.selected = endpoint.id === selectedId;
    select.appendChild(option);
  }
  label.appendChild(select);
  return label;
}

function renderScope(selectors, reportPath, statusText = "") {
  scopeRoot.replaceChildren();
  const heading = element("h1", "Benchmark report");
  const note = element(
    "p",
    `Cache: ${reportPath}. Retargeting only selects complete cached endpoints; it never runs a benchmark.`,
    "scope-note",
  );
  const form = element("form", null, "scope-form");
  const pair = element("fieldset", null, "scope-pair");
  pair.appendChild(element("legend", "Comparison"));
  pair.append(
    endpointField(
      "Baseline",
      "scope-baseline",
      selectors.endpoints,
      selectors.baseline_endpoint_id,
    ),
    endpointField(
      "Candidate",
      "scope-candidate",
      selectors.endpoints,
      selectors.candidate_endpoint_id,
    ),
  );
  const swap = element("button", "Swap endpoints");
  swap.type = "button";
  swap.addEventListener("click", () => {
    const baseline = document.getElementById("scope-baseline");
    const candidate = document.getElementById("scope-candidate");
    [baseline.value, candidate.value] = [candidate.value, baseline.value];
  });
  pair.appendChild(swap);

  const files = element("fieldset");
  files.appendChild(element("legend", "Files"));
  for (const file of selectors.files) {
    const label = element("label", null, "scope-choice");
    const input = element("input");
    input.type = "checkbox";
    input.dataset.kind = "file";
    input.value = file.id;
    input.checked = file.selected;
    label.append(input, document.createTextNode(" " + file.label));
    files.appendChild(label);
  }

  const display = element("fieldset");
  display.appendChild(element("legend", "Display"));
  const detailLabel = element("label", "Detail ");
  const detail = element("select");
  detail.id = "scope-detail";
  for (const value of ["summary", "files", "phases", "rulesets"]) {
    const option = element("option", value[0].toUpperCase() + value.slice(1));
    option.value = value;
    option.selected = value === selectors.detail;
    detail.appendChild(option);
  }
  detailLabel.appendChild(detail);
  display.append(
    detailLabel,
    element("p", `${selectors.rounds} rounds per endpoint/file`, "scope-fixed"),
    element("p", `${selectors.timeout_sec} second timeout per run`, "scope-fixed"),
  );
  form.append(pair, files, display);

  const actions = element("div", null, "scope-actions");
  const apply = element("button", "Apply");
  apply.type = "submit";
  const status = element("span", statusText, "scope-status");
  actions.append(apply, status);
  form.appendChild(actions);
  form.addEventListener("submit", async (event) => {
    event.preventDefault();
    apply.disabled = true;
    status.textContent = "Recomputing cached report...";
    const request = {
      baseline_endpoint_id: document.getElementById("scope-baseline").value,
      candidate_endpoint_id: document.getElementById("scope-candidate").value,
      file_ids: [...scopeRoot.querySelectorAll('input[data-kind="file"]:checked')]
        .map((input) => input.value),
      detail: document.getElementById("scope-detail").value,
    };
    try {
      const response = await fetch("/api/scope", {
        method: "PUT",
        headers: {"Content-Type": "application/json"},
        body: JSON.stringify(request),
      });
      const payload = await response.json();
      if (!response.ok) throw new Error(payload.error || `scope request failed: ${response.status}`);
      renderPayload(payload);
    } catch (error) {
      const message = `Unable to apply scope: ${error}`;
      if (currentPayload) renderScope(currentPayload.selectors, currentPayload.report_path, message);
      else {
        status.textContent = message;
        apply.disabled = false;
      }
    }
  });
  scopeRoot.append(heading, note, form);
}

function renderPayload(payload) {
  currentPayload = payload;
  renderScope(payload.selectors, payload.report_path);
  initEvalLiveCatalog(reportRoot, payload.sections);
}

fetch("/api/report", {cache: "no-store"})
  .then((response) => {
    if (!response.ok) throw new Error(`report request failed: ${response.status}`);
    return response.json();
  })
  .then(renderPayload)
  .catch((error) => {
    scopeRoot.textContent = `Unable to load report: ${error}`;
  });
"""

APP_CSS = """
#scope-root {
  max-width: 1400px;
  margin: 1rem auto;
  padding: 0 1.5rem;
  font-family: system-ui, sans-serif;
}
.scope-note, .scope-fixed, .scope-status { color: #555; }
.scope-form { display: flex; flex-wrap: wrap; gap: 0.75rem; align-items: flex-start; }
.scope-form fieldset { min-width: 12rem; border: 1px solid #ccc; border-radius: 0.35rem; }
.scope-pair { flex: 2 1 42rem; }
.scope-pair > label, .scope-choice { display: block; margin: 0.35rem 0; }
.scope-pair select { max-width: min(36rem, 80vw); }
.scope-fixed { margin: 0.4rem 0; }
.scope-actions { flex-basis: 100%; display: flex; gap: 0.75rem; align-items: center; }
"""
