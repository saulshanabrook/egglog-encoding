"""eval-live web (``--serve``) and on-disk dump (``--dump-dir``) for reports.

Serializes the active report scope (``ReportSelection``) plus only the rows that
scope selects, assembles the page, and serves it on loopback. The tables and
their live recompute live in ``web_registry.py`` (shipped to Pyodide as the graph
script); ``models.py``/``analysis.py``/``report.py`` ship as eval-live extra modules. Scope is
carried authoritatively — the browser never reconstructs it from historical rows.
"""

from __future__ import annotations

import http.server
import json
import webbrowser
from contextlib import suppress
from pathlib import Path
from typing import TYPE_CHECKING, Any, cast

import pandas as pd

import analysis
import models
import report_frame

if TYPE_CHECKING:
    from pandera.typing import DataFrame

    from models import ReportSelection
    from report_frame import ReportFrame

PYODIDE_CDN = "https://cdn.jsdelivr.net/pyodide/v0.27.5/full/pyodide.js"


def _scoped_rows(rows: DataFrame[ReportFrame], selection: ReportSelection) -> DataFrame[ReportFrame]:
    """The rows the active report selects: latest ``rounds`` per (target, file, treatment)."""
    frames = [
        analysis.selected_rows(
            rows,
            models.EstimateKey(target.binary_sha256, file.sha256, treatment, selection.timeout_sec),
            selection.rounds,
        )
        for target in selection.targets
        for file in selection.files
        for treatment in selection.treatments
    ]
    if not frames:
        return cast("DataFrame[ReportFrame]", rows.iloc[0:0])
    return cast("DataFrame[ReportFrame]", pd.concat(frames, ignore_index=True))


def report_records(rows: DataFrame[ReportFrame]) -> list[dict[str, Any]]:
    """Rows as JSON-safe dicts. Keeps ``row_index`` (browser recompute sorts by it)
    and renders ``started_at`` as an ISO-8601 ``Z`` string."""
    frame = rows.loc[:, report_frame.report_columns()].copy()
    frame["started_at"] = frame["started_at"].map(lambda ts: ts.isoformat().replace("+00:00", "Z"))
    safe = frame.astype(object).where(pd.notna(frame), None)
    return cast("list[dict[str, Any]]", json.loads(safe.to_json(orient="records", double_precision=15) or "[]"))


def report_data(rows: DataFrame[ReportFrame], selection: ReportSelection) -> dict[str, Any]:
    """eval-live data: only the scoped report rows plus a one-row ``metadata`` table."""
    return {
        "Benchmark report": report_records(_scoped_rows(rows, selection)),
        "metadata": [{"rounds": selection.rounds}],
    }


def graph_script_source(selection: ReportSelection, present: list[tuple[str, str | None]]) -> str:
    """``web_registry.py`` source with the authoritative scope + present table set baked in.

    Bindings are inserted right after ``from __future__ import annotations`` (which
    must remain the first statement), not prepended, so the script compiles in Pyodide.
    """
    import web_registry

    source = Path(web_registry.__file__).read_text(encoding="utf-8")
    bindings = f"\n_SELECTION = {models.report_selection_to_dict(selection)!r}\n_PRESENT_TABLES = {present!r}\n"
    marker = "from __future__ import annotations\n"
    cut = source.index(marker) + len(marker)
    return source[:cut] + bindings + source[cut:]


def extra_modules() -> dict[str, str]:
    """Compute modules the graph script imports, written to the Pyodide FS."""
    import report

    return {
        "models.py": Path(models.__file__).read_text(encoding="utf-8"),
        "analysis.py": Path(analysis.__file__).read_text(encoding="utf-8"),
        "report.py": Path(report.__file__).read_text(encoding="utf-8"),
    }


def eval_live_page(data: dict[str, Any], name: str, graph_script: str, modules: dict[str, str]) -> bytes:
    """Build a self-contained eval-live HTML page that recomputes tables live.

    Internal tool: the report data is trusted, so the JSON is embedded directly.
    """
    import eval_live

    data_json = json.dumps(data)
    name_json = json.dumps(name)
    graph_json = json.dumps(graph_script)
    lib_json = json.dumps(eval_live.pyodide_lib())
    modules_json = json.dumps(modules)
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
    {eval_live.css()}
  </style>
  <script src="{PYODIDE_CDN}"></script>
</head>
<body>
  <div id="eval-live-root"></div>
  <script>
    {eval_live.js()}
    initEvalLive("eval-live-root", {data_json}, {name_json}, {graph_json}, {lib_json}, {modules_json});
  </script>
</body>
</html>"""
    return page.encode("utf-8")


def build_page(rows: DataFrame[ReportFrame], selection: ReportSelection, name: str) -> bytes:
    import web_registry

    web_registry.configure(selection)
    data = report_data(rows, selection)
    present = web_registry.present_tables(data)
    return eval_live_page(data, name, graph_script_source(selection, present), extra_modules())


def serve_report(
    console: Any,
    rows: DataFrame[ReportFrame],
    selection: ReportSelection,
    port: int,
    name: str = "egglog-encoding",
) -> None:
    """Serve the report as an eval-live page on 127.0.0.1:port until interrupted."""
    page_bytes = build_page(rows, selection, name)

    class Handler(http.server.BaseHTTPRequestHandler):
        def do_GET(self) -> None:
            self.send_response(200)
            self.send_header("Content-Type", "text/html; charset=utf-8")
            self.send_header("Content-Length", str(len(page_bytes)))
            self.end_headers()
            self.wfile.write(page_bytes)

        def log_message(self, format: str, *args: Any) -> None:
            pass  # keep request logs off the runner's stderr stream

    server = http.server.HTTPServer(("127.0.0.1", port), Handler)
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


def dump_report(console: Any, rows: DataFrame[ReportFrame], selection: ReportSelection, outdir: Path) -> None:
    """Render the registry's tables (JSON + LaTeX) into ``outdir``."""
    import eval_live

    import web_registry

    web_registry.configure(selection)
    data = report_data(rows, selection)
    reg = eval_live.Registry()
    web_registry._register(reg, web_registry.present_tables(data))
    written = reg.render_to_dir(data, str(outdir))
    console.print(f"Wrote {len(written)} eval-live artifact(s) to [bold]{outdir}[/bold]:")
    for path in written:
        console.print(f"  {path}")
