"""Write and open one single-file, embedded-data benchmark-report snapshot.

The exported HTML embeds the complete JSONL, the immediate all-sections report,
the eval-live catalog renderer, and the environment-neutral Python runtime. It performs
no collection and starts no server: opening the file renders the static catalog
first, then loads a pinned Pyodide/SciPy runtime for cache-only retargeting.
"""

from __future__ import annotations

import base64
import importlib
import json
import os
import re
import tempfile
import webbrowser
from contextlib import suppress
from pathlib import Path
from typing import Protocol, cast

from ..models import ComparisonSpec
from .interactive_runtime import InteractiveRuntime, JsonValue, scope_for_comparison
from .store import ReportStore, serialize_report_record

PYODIDE_VERSION = "314.0.2"
PYODIDE_BASE_URL = f"https://cdn.jsdelivr.net/pyodide/v{PYODIDE_VERSION}/full/"


class EvalLiveModule(Protocol):
    """The pinned dependency's two self-contained browser assets."""

    def css(self) -> str: ...

    def js(self) -> str: ...


_PYTHON_MODULES = (
    "benchmarking/__init__.py",
    "benchmarking/models.py",
    "benchmarking/reports/__init__.py",
    "benchmarking/reports/store.py",
    "benchmarking/reports/analysis.py",
    "benchmarking/reports/catalog.py",
    "benchmarking/reports/presentation.py",
    "benchmarking/reports/interactive_runtime.py",
)

_PYTHON_BOOTSTRAP = """\
from pathlib import Path

from benchmarking.reports.interactive_runtime import InteractiveRuntime

_egglog_runtime = InteractiveRuntime.from_path(
    Path(_egglog_report_path),
    _egglog_report_display_path,
    _egglog_initial_scope_json,
)

def _egglog_apply_scope(request_json):
    return _egglog_runtime.apply_json(request_json)
"""


def interactive_report_path(report_path: Path) -> Path:
    """Derive the sibling HTML snapshot path for one JSONL report path."""

    if report_path.suffix.lower() == ".jsonl":
        return report_path.with_suffix(".html")
    return report_path.with_name(report_path.name + ".html")


def write_interactive_report(
    store: ReportStore,
    comparison: ComparisonSpec,
    output_path: Path,
) -> Path:
    """Atomically write a complete cache-only browser artifact and return it."""

    destination = output_path.expanduser().resolve()
    if destination == store.path.expanduser().resolve():
        raise ValueError("interactive report path must differ from the JSONL report path")
    report_bytes = b"".join(serialize_report_record(record) + b"\n" for record in store.records)
    initial_scope = scope_for_comparison(comparison)
    runtime = InteractiveRuntime(store, initial_scope)
    page = _interactive_page(report_bytes, store.display_path, initial_scope, runtime.initial_payload(comparison))

    destination.parent.mkdir(parents=True, exist_ok=True)
    temporary: Path | None = None
    try:
        with tempfile.NamedTemporaryFile(
            mode="wb",
            dir=destination.parent,
            prefix=f".{destination.name}.",
            suffix=".tmp",
            delete=False,
        ) as handle:
            temporary = Path(handle.name)
            handle.write(page)
        os.replace(temporary, destination)
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)
    return destination


def open_interactive_report(path: Path) -> None:
    """Open one completed artifact best-effort without changing CLI success."""

    with suppress(Exception):
        webbrowser.open(path.expanduser().resolve().as_uri())


def _interactive_page(
    report_bytes: bytes,
    report_path: str,
    initial_scope: dict[str, JsonValue],
    initial_payload: dict[str, JsonValue],
) -> bytes:
    eval_live = cast(EvalLiveModule, importlib.import_module("eval_live"))
    envelope = {
        "report_path": report_path,
        "report_jsonl_base64": base64.b64encode(report_bytes).decode("ascii"),
        "initial_scope": initial_scope,
        "initial_payload": initial_payload,
        "pyodide_base_url": PYODIDE_BASE_URL,
        "python_bootstrap": _PYTHON_BOOTSTRAP,
        "python_modules": _python_module_sources(),
    }
    encoded_envelope = base64.b64encode(
        json.dumps(envelope, ensure_ascii=False, separators=(",", ":")).encode()
    ).decode("ascii")
    css = _style_text(eval_live.css() + "\n" + _asset_path("interactive.css").read_text(encoding="utf-8"))
    eval_live_js = _script_text(eval_live.js())
    application_js = _script_text(_asset_path("interactive.js").read_text(encoding="utf-8"))
    page = f"""<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>Benchmark Report</title>
  <link rel="icon" href="data:,">
  <style>{css}</style>
</head>
<body>
  <section id="scope-root" aria-label="Report scope"></section>
  <main id="eval-live-root"></main>
  <script id="report-envelope" type="application/octet-stream">{encoded_envelope}</script>
  <script>{eval_live_js}</script>
  <script>{application_js}</script>
</body>
</html>
"""
    return page.encode()


def _python_module_sources() -> dict[str, str]:
    root = Path(__file__).resolve().parents[2]
    return {name: (root / name).read_text(encoding="utf-8") for name in _PYTHON_MODULES}


def _asset_path(name: str) -> Path:
    return Path(__file__).with_name(name)


def _script_text(source: str) -> str:
    """Keep inline JavaScript from terminating its containing HTML element."""

    return re.sub(r"</script", r"<\\/script", source, flags=re.IGNORECASE)


def _style_text(source: str) -> str:
    """Keep inline CSS from terminating its containing HTML element."""

    return re.sub(r"</style", r"<\\/style", source, flags=re.IGNORECASE)
