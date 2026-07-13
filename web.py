"""eval-live web (``--serve``) and on-disk dump (``--dump-dir``) for reports.

Serializes report rows into eval-live's data format and assembles the page /
artifacts. The tables and their live recompute live in ``web_registry.py``;
``models.py``/``tables.py`` ship to the browser as eval-live extra modules.
"""

from __future__ import annotations

import http.server
import json
import webbrowser
from contextlib import suppress
from pathlib import Path
from typing import TYPE_CHECKING, Any, cast

import pandas as pd

import report_frame

if TYPE_CHECKING:
    from pandera.typing import DataFrame

    from models import BenchmarkSpec
    from report_frame import ReportFrame

PYODIDE_CDN = "https://cdn.jsdelivr.net/pyodide/v0.27.5/full/pyodide.js"


def report_records(rows: DataFrame[ReportFrame]) -> list[dict[str, Any]]:
    """Report rows as JSON-safe dicts (the eval-live "Benchmark report" table).

    Keeps ``row_index`` (the browser recompute sorts by it) and renders
    ``started_at`` as an ISO-8601 ``Z`` string so it round-trips through JSON.
    """
    frame = rows.loc[:, report_frame.report_columns()].copy()
    frame["started_at"] = frame["started_at"].map(lambda ts: ts.isoformat().replace("+00:00", "Z"))
    safe = frame.astype(object).where(pd.notna(frame), None)
    return cast("list[dict[str, Any]]", json.loads(safe.to_json(orient="records", double_precision=15) or "[]"))


def report_data(rows: DataFrame[ReportFrame], spec: BenchmarkSpec) -> dict[str, Any]:
    """eval-live data dict: the raw report rows plus a one-row ``metadata`` table.

    The rows are the source of truth; ``web_registry`` derives files, treatments,
    and targets from them. ``metadata`` holds only render params (``rounds``).
    """
    return {
        "Benchmark report": report_records(rows),
        "metadata": [{"rounds": spec.rounds}],
    }


def graph_script_source(rows: DataFrame[ReportFrame], spec: BenchmarkSpec) -> str:
    """``web_registry.py`` source with the present table set baked in as a preamble.

    Registers exactly the tables present for this data (so no empty tables),
    derived from the shared ``build_report_tables`` catalog.
    """
    import web_registry

    present = web_registry.present_tables(report_data(rows, spec))
    preamble = f"_PRESENT_TABLES = {present!r}\n\n"
    return preamble + Path(web_registry.__file__).read_text(encoding="utf-8")


def extra_modules() -> dict[str, str]:
    """Compute modules the graph script imports, written to the Pyodide FS."""
    import models
    import tables

    return {
        "models.py": Path(models.__file__).read_text(encoding="utf-8"),
        "tables.py": Path(tables.__file__).read_text(encoding="utf-8"),
    }


def eval_live_page(data_json: str, name: str, graph_script: str, modules: dict[str, str]) -> bytes:
    """Build a self-contained eval-live HTML page that recomputes tables live."""
    import eval_live

    css = eval_live.css()
    js = eval_live.js()
    name_json = json.dumps(name)
    graph_args = f", {json.dumps(graph_script)}, {json.dumps(eval_live.pyodide_lib())}, {json.dumps(modules)}"
    page = f"""<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8">
  <meta name="viewport" content="width=device-width, initial-scale=1.0">
  <title>{name} — Eval Live</title>
  <style>
    body {{
      font-family: system-ui, -apple-system, sans-serif;
      margin: 0; padding: 2rem 3rem;
      background: #f5f6f8; color: #1a1a1a;
    }}
    {css}
  </style>
  <script src="{PYODIDE_CDN}"></script>
</head>
<body>
  <div id="eval-live-root"></div>
  <script>
    {js}
    initEvalLive("eval-live-root", {data_json}, {name_json}{graph_args});
  </script>
</body>
</html>"""
    return page.encode("utf-8")


def build_page(rows: DataFrame[ReportFrame], spec: BenchmarkSpec, name: str) -> bytes:
    data_json = json.dumps(report_data(rows, spec))
    return eval_live_page(data_json, name, graph_script_source(rows, spec), extra_modules())


def serve_report(
    console: Any,
    rows: DataFrame[ReportFrame],
    spec: BenchmarkSpec,
    port: int,
    name: str = "egglog-encoding",
) -> None:
    """Serve the report as an eval-live page on localhost:port until interrupted."""
    page_bytes = build_page(rows, spec, name)

    class Handler(http.server.BaseHTTPRequestHandler):
        def do_GET(self) -> None:
            self.send_response(200)
            self.send_header("Content-Type", "text/html; charset=utf-8")
            self.send_header("Content-Length", str(len(page_bytes)))
            self.end_headers()
            self.wfile.write(page_bytes)

        def log_message(self, format: str, *args: Any) -> None:
            pass  # keep request logs off the runner's stderr stream

    server = http.server.HTTPServer(("", port), Handler)
    url = f"http://localhost:{port}"
    console.print(f"\nServing eval-live report at [bold]{url}[/bold]  (Ctrl-C to stop)")
    with suppress(Exception):
        webbrowser.open(url)
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        console.print("\nServer stopped.")
    finally:
        server.server_close()


def dump_report(console: Any, rows: DataFrame[ReportFrame], spec: BenchmarkSpec, outdir: Path) -> None:
    """Render the registry's tables (JSON + LaTeX) into ``outdir``."""
    import eval_live

    import web_registry

    data = report_data(rows, spec)
    reg = eval_live.Registry()
    web_registry._register(reg, web_registry.present_tables(data))
    written = reg.render_to_dir(data, str(outdir))
    console.print(f"Wrote {len(written)} eval-live artifact(s) to [bold]{outdir}[/bold]:")
    for path in written:
        console.print(f"  {path}")
