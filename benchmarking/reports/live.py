"""Serve the shared report catalog as a live, cache-only browser application.

This module owns the eval-live wire adapter, browser scope editor and CSS, the
immutable retargeting universe, the current browser scope, and a small loopback
HTTP server. Eval-live itself owns display-only table filters. Applying
selectors builds a complete replacement catalog from the existing JSONL cache
in a fresh :class:`ReportDatabase`; this module never resolves, builds, or runs
benchmark targets. Report calculation and wording remain in ``summary``/SQL,
with timing-specific wording in ``timing``; CLI policy remains in ``benchmark``
and ``benchmark_config``.
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
from pathlib import Path
from typing import Any, Protocol, cast

from ..models import Backend, BenchmarkSpec, FileSpec, Treatment
from .catalog import (
    CellTone,
    ReportCatalog,
    ReportCell,
    ReportMessage,
    ReportOptions,
    ReportScope,
    report_id,
)
from .database import ReportDatabase
from .summary import build_report_catalog


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
_MAX_UINTEGER = (1 << 32) - 1


@dataclass(frozen=True)
class StaticAsset:
    """One exact HTTP resource and its response media type."""

    body: bytes
    content_type: str


@dataclass(frozen=True)
class LiveScopeRequest:
    """One canonical selection within a session's fixed benchmark universe."""

    target_ids: tuple[str, ...]
    baseline_target_id: str
    file_ids: tuple[str, ...]
    backends: tuple[Backend, ...]
    treatments: tuple[Treatment, ...]
    rounds: int
    timeout_sec: int
    phase_timings: bool
    detailed_timing: bool


class LiveReportSession:
    """Own one fixed selector universe and its atomically replaced report catalog."""

    def __init__(
        self,
        report_path: Path,
        scope: ReportScope,
        options: ReportOptions,
        catalog: ReportCatalog,
    ) -> None:
        self._report_path = report_path
        self._targets = scope.targets
        self._files = scope.spec.files
        self._backends = scope.spec.backends
        self._treatments = scope.spec.treatments
        self._options_command = options.command_argv
        self._target_by_id = {target.binary_sha256: target for target in self._targets}
        self._file_by_id = {_file_id(file): file for file in self._files}
        self._request = LiveScopeRequest(
            target_ids=tuple(self._target_by_id),
            baseline_target_id=self._targets[0].binary_sha256,
            file_ids=tuple(self._file_by_id),
            backends=self._backends,
            treatments=self._treatments,
            rounds=scope.spec.rounds,
            timeout_sec=scope.spec.timeout_sec,
            phase_timings=options.phase_timings,
            detailed_timing=options.detailed_timing,
        )
        self._catalog = catalog

    def payload(self) -> dict[str, JsonValue]:
        """Return the complete current selector state and presentation catalog."""

        return self._payload(self._request, self._catalog)

    def _payload(self, request: LiveScopeRequest, catalog: ReportCatalog) -> dict[str, JsonValue]:
        return {
            "report_path": str(self._report_path),
            "selectors": self._selector_payload(request),
            "sections": _catalog_payload(catalog),
        }

    def apply(self, value: object) -> dict[str, JsonValue]:
        """Validate one browser request, recompute fully, then publish it atomically."""

        request = self._parse_request(value)
        selected_target_ids = set(request.target_ids)
        targets = (
            self._target_by_id[request.baseline_target_id],
            *(
                target
                for target in self._targets
                if target.binary_sha256 in selected_target_ids and target.binary_sha256 != request.baseline_target_id
            ),
        )
        selected_file_ids = set(request.file_ids)
        files = tuple(file for file in self._files if _file_id(file) in selected_file_ids)
        selected_backends = set(request.backends)
        backends = tuple(backend for backend in self._backends if backend in selected_backends)
        selected_treatments = set(request.treatments)
        treatments = tuple(treatment for treatment in self._treatments if treatment in selected_treatments)
        spec = BenchmarkSpec(
            files=files,
            treatments=treatments,
            rounds=request.rounds,
            timeout_sec=request.timeout_sec,
            backends=backends,
        )
        options = ReportOptions(
            command_argv=self._options_command,
            phase_timings=request.phase_timings,
            detailed_timing=request.detailed_timing,
        )

        # Build against a new transient catalog. If parsing, SQL, or report
        # assembly fails, the current request/catalog remain untouched.
        with ReportDatabase(self._report_path) as database:
            catalog = build_report_catalog(database, ReportScope(targets, spec), options)
        payload = self._payload(request, catalog)
        self._request = request
        self._catalog = catalog
        return payload

    def _parse_request(self, value: object) -> LiveScopeRequest:
        request = _object(value, "scope request")
        target_ids = _string_list(request, "target_ids")
        _require_known_subset(target_ids, self._target_by_id, "target")
        baseline_target_id = _string(request, "baseline_target_id")
        if baseline_target_id not in target_ids:
            raise ValueError("baseline_target_id must name a selected target")
        file_ids = _string_list(request, "file_ids")
        _require_known_subset(file_ids, self._file_by_id, "file")
        backends = _string_list(request, "backends")
        _require_known_subset(backends, {backend: backend for backend in self._backends}, "backend")
        treatments = _string_list(request, "treatments")
        _require_known_subset(
            treatments,
            {treatment: treatment for treatment in self._treatments},
            "treatment",
        )
        detailed_timing = _boolean(request, "detailed_timing")
        return LiveScopeRequest(
            target_ids=target_ids,
            baseline_target_id=baseline_target_id,
            file_ids=file_ids,
            backends=tuple(cast(Backend, backend) for backend in backends),
            treatments=tuple(cast(Treatment, treatment) for treatment in treatments),
            rounds=_positive_integer(request, "rounds"),
            timeout_sec=_positive_integer(request, "timeout_sec"),
            phase_timings=_boolean(request, "phase_timings") or detailed_timing,
            detailed_timing=detailed_timing,
        )

    def _selector_payload(self, request: LiveScopeRequest) -> dict[str, JsonValue]:
        selected_targets = set(request.target_ids)
        selected_files = set(request.file_ids)
        selected_backends = set(request.backends)
        selected_treatments = set(request.treatments)
        return {
            "targets": [
                {
                    "id": target.binary_sha256,
                    "label": target.display_label,
                    "selected": target.binary_sha256 in selected_targets,
                    "baseline": target.binary_sha256 == request.baseline_target_id,
                }
                for target in self._targets
            ],
            "files": [
                {
                    "id": _file_id(file),
                    "label": file.display_path,
                    "selected": _file_id(file) in selected_files,
                }
                for file in self._files
            ],
            "backends": [
                {"id": backend, "label": backend, "selected": backend in selected_backends}
                for backend in self._backends
            ],
            "treatments": [
                {"id": treatment, "label": treatment, "selected": treatment in selected_treatments}
                for treatment in self._treatments
            ],
            "rounds": request.rounds,
            "timeout_sec": request.timeout_sec,
            "phase_timings": request.phase_timings,
            "detailed_timing": request.detailed_timing,
        }


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

    # Port zero asks the OS for a free loopback port. Argparse represents an
    # omitted --serve-port as None so the choice remains local to the server.
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


def _file_id(file: FileSpec) -> str:
    return report_id("file", file.sha256, file.fact_directory_sha256)


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


def _boolean(request: Mapping[str, object], key: str) -> bool:
    value = request.get(key)
    if not isinstance(value, bool):
        raise ValueError(f"{key} must be a boolean")
    return value


def _positive_integer(request: Mapping[str, object], key: str) -> int:
    value = request.get(key)
    if isinstance(value, bool) or not isinstance(value, int) or value < 1:
        raise ValueError(f"{key} must be a positive integer")
    if value > _MAX_UINTEGER:
        raise ValueError(f"{key} must be at most {_MAX_UINTEGER}")
    return value


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

function choiceFieldset(title, kind, choices) {
  const fieldset = element("fieldset");
  fieldset.appendChild(element("legend", title));
  for (const choice of choices) {
    const label = element("label", null, "scope-choice");
    const input = element("input");
    input.type = "checkbox";
    input.dataset.kind = kind;
    input.value = choice.id;
    input.checked = choice.selected;
    label.append(input, document.createTextNode(" " + choice.label));
    fieldset.appendChild(label);
  }
  return fieldset;
}

function selected(kind) {
  return [...scopeRoot.querySelectorAll(`input[data-kind="${kind}"]:checked`)].map((input) => input.value);
}

function renderScope(selectors, reportPath, statusText = "") {
  scopeRoot.replaceChildren();
  const heading = element("h1", "Benchmark report");
  const note = element(
    "p",
    `Cache: ${reportPath}. Rounds, timeout, and selectors only reselect cached rows; `
      + "table filters only change the browser display.",
    "scope-note",
  );
  const form = element("form", null, "scope-form");
  form.append(
    choiceFieldset("Targets", "target", selectors.targets),
    choiceFieldset("Files", "file", selectors.files),
    choiceFieldset("Backends", "backend", selectors.backends),
    choiceFieldset("Treatments", "treatment", selectors.treatments),
  );

  const parameters = element("fieldset");
  parameters.appendChild(element("legend", "Analysis"));
  const baselineLabel = element("label", "Baseline target ");
  const baseline = element("select");
  baseline.id = "scope-baseline";
  for (const choice of selectors.targets) {
    const option = element("option", choice.label);
    option.value = choice.id;
    option.selected = choice.baseline;
    baseline.appendChild(option);
  }
  baselineLabel.appendChild(baseline);
  parameters.appendChild(baselineLabel);
  for (const [id, label, value] of [
    ["scope-rounds", "Rounds", selectors.rounds],
    ["scope-timeout", "Timeout (seconds)", selectors.timeout_sec],
  ]) {
    const field = element("label", label + " ");
    const input = element("input");
    input.id = id;
    input.type = "number";
    input.min = "1";
    input.value = String(value);
    field.appendChild(input);
    parameters.appendChild(field);
  }
  for (const [id, label, checked] of [
    ["scope-timing", "Engine timing", selectors.phase_timings],
    ["scope-detailed", "Detailed timing", selectors.detailed_timing],
  ]) {
    const field = element("label", null, "scope-choice");
    const input = element("input");
    input.id = id;
    input.type = "checkbox";
    input.checked = checked;
    field.append(input, document.createTextNode(" " + label));
    parameters.appendChild(field);
  }
  form.appendChild(parameters);
  const actions = element("div", null, "scope-actions");
  const apply = element("button", "Apply scope");
  apply.type = "submit";
  const status = element("span", statusText, "scope-status");
  actions.append(apply, status);
  form.appendChild(actions);
  form.addEventListener("submit", async (event) => {
    event.preventDefault();
    apply.disabled = true;
    status.textContent = "Recomputing cached report...";
    const targetIds = selected("target");
    if (!targetIds.includes(baseline.value)) targetIds.push(baseline.value);
    const request = {
      target_ids: targetIds,
      baseline_target_id: baseline.value,
      file_ids: selected("file"),
      backends: selected("backend"),
      treatments: selected("treatment"),
      rounds: Number(document.getElementById("scope-rounds").value),
      timeout_sec: Number(document.getElementById("scope-timeout").value),
      phase_timings: document.getElementById("scope-timing").checked,
      detailed_timing: document.getElementById("scope-detailed").checked,
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
.scope-note { color: #555; }
.scope-form { display: flex; flex-wrap: wrap; gap: 0.75rem; align-items: flex-start; }
.scope-form fieldset { min-width: 10rem; border: 1px solid #ccc; border-radius: 0.35rem; }
.scope-choice, .scope-form fieldset > label { display: block; margin: 0.25rem 0; }
.scope-actions { flex-basis: 100%; display: flex; gap: 0.75rem; align-items: center; }
.scope-status { color: #555; }
"""
