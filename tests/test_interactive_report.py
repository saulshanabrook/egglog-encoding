"""Test the cache-only interactive runtime and embedded HTML artifact."""

from __future__ import annotations

import ast
import base64
import importlib.util
import json
from dataclasses import replace
from pathlib import Path
from typing import Any, cast

import pytest

from benchmarking import models
from benchmarking.reports import interactive
from benchmarking.reports.comparison import build_report_catalog
from benchmarking.reports.interactive_runtime import (
    InteractiveRuntime,
    JsonValue,
    _catalog_payload,
    scope_for_comparison,
)
from benchmarking.reports.records import ReportRecord
from benchmarking.reports.store import ReportStore

from .conftest import make_endpoint, make_record, write_report


def test_runtime_discovers_entire_cache_and_retargets_all_sections(tmp_path: Path) -> None:
    runtime, payload, _store, _comparison = _interactive_case(tmp_path)
    selectors = cast(dict[str, JsonValue], payload["selectors"])
    endpoints = cast(list[dict[str, JsonValue]], selectors["endpoints"])
    files = cast(list[dict[str, JsonValue]], selectors["files"])

    assert {endpoint["label"] for endpoint in endpoints} == {
        "alternative · abc123 · dd/proofs",
        "baseline · abc123 · main/off",
        "candidate · abc123 · main/proofs",
        "historical · abc123 · main/term",
    }
    assert {file["label"] for file in files} == {"one.egg", "two.egg", "three.egg"}
    assert selectors["timeouts_sec"] == [60, 120]
    assert selectors["rounds"] == 2
    assert selectors["max_rounds"] == 2
    assert _section_ids(payload) == ["selection", "summary", "files", "phases", "rulesets"]

    alternative = next(endpoint for endpoint in endpoints if endpoint["backend"] == "dd")
    baseline = next(endpoint for endpoint in endpoints if endpoint["treatment"] == "off")
    first_file = next(file for file in files if file["label"] == "one.egg")
    second_file = next(file for file in files if file["label"] == "two.egg")
    narrowed = runtime.apply(
        {
            "baseline_endpoint_id": alternative["id"],
            "candidate_endpoint_id": baseline["id"],
            "file_ids": [second_file["id"], first_file["id"]],
            "timeout_sec": 120,
            "rounds": 1,
        }
    )

    narrowed_selectors = cast(dict[str, JsonValue], narrowed["selectors"])
    assert narrowed_selectors["baseline_endpoint_id"] == alternative["id"]
    assert narrowed_selectors["candidate_endpoint_id"] == baseline["id"]
    assert narrowed_selectors["rounds"] == 1
    assert _section_ids(narrowed) == ["selection", "summary", "files", "phases", "rulesets"]
    sections = cast(list[dict[str, JsonValue]], narrowed["sections"])
    files_section = next(section for section in sections if section["id"] == "files")
    blocks = cast(list[dict[str, JsonValue]], files_section["blocks"])
    wall_time = next(block for block in blocks if block["name"] == "Wall time")
    rows = cast(list[dict[str, JsonValue]], wall_time["rows"])
    assert [row["file"] for row in rows] == ["two.egg", "one.egg"]


def test_incomplete_scope_publishes_missing_cells_but_invalid_scope_rolls_back(tmp_path: Path) -> None:
    runtime, payload, _store, _comparison = _interactive_case(tmp_path)
    selectors = cast(dict[str, JsonValue], payload["selectors"])
    endpoints = cast(list[dict[str, JsonValue]], selectors["endpoints"])
    files = cast(list[dict[str, JsonValue]], selectors["files"])
    alternative = next(endpoint for endpoint in endpoints if endpoint["backend"] == "dd")
    baseline = next(endpoint for endpoint in endpoints if endpoint["treatment"] == "off")
    first_file = next(file for file in files if file["label"] == "one.egg")

    incomplete = runtime.apply(
        {
            "baseline_endpoint_id": alternative["id"],
            "candidate_endpoint_id": baseline["id"],
            "file_ids": [first_file["id"]],
            "timeout_sec": 120,
            "rounds": 2,
        }
    )
    assert "missing 2 row(s)" in json.dumps(incomplete)
    assert runtime.payload() == incomplete

    with pytest.raises(ValueError, match="must not exceed cached maximum: 2"):
        runtime.apply(
            {
                "baseline_endpoint_id": alternative["id"],
                "candidate_endpoint_id": baseline["id"],
                "file_ids": [first_file["id"]],
                "timeout_sec": 120,
                "rounds": 3,
            }
        )
    assert runtime.payload() == incomplete

    with pytest.raises(ValueError, match="must be different"):
        runtime.apply(
            {
                "baseline_endpoint_id": baseline["id"],
                "candidate_endpoint_id": baseline["id"],
                "file_ids": [first_file["id"]],
                "timeout_sec": 120,
                "rounds": 2,
            }
        )
    assert runtime.payload() == incomplete

    result = json.loads(
        runtime.apply_json(
            json.dumps(
                {
                    "baseline_endpoint_id": baseline["id"],
                    "candidate_endpoint_id": baseline["id"],
                    "file_ids": [first_file["id"]],
                    "timeout_sec": 120,
                    "rounds": 2,
                }
            )
        )
    )
    assert result == {"ok": False, "error": "baseline and candidate endpoints must be different"}
    assert runtime.payload() == incomplete


def test_runtime_uses_loaded_snapshot_without_reparsing_jsonl(tmp_path: Path) -> None:
    runtime, payload, store, _comparison = _interactive_case(tmp_path)
    with store.path.open("a", encoding="utf-8") as report:
        report.write("not valid JSON\n")
    selectors = cast(dict[str, JsonValue], payload["selectors"])
    endpoints = cast(list[dict[str, JsonValue]], selectors["endpoints"])
    files = cast(list[dict[str, JsonValue]], selectors["files"])

    updated = runtime.apply(
        {
            "baseline_endpoint_id": endpoints[1]["id"],
            "candidate_endpoint_id": endpoints[0]["id"],
            "file_ids": [files[0]["id"]],
            "timeout_sec": 120,
            "rounds": 1,
        }
    )

    assert cast(dict[str, JsonValue], updated["selectors"])["rounds"] == 1


def test_html_embeds_exact_jsonl_initial_catalog_runtime_and_safe_data(tmp_path: Path) -> None:
    _runtime, _payload, store, comparison = _interactive_case(tmp_path)
    unsafe = make_record(
        99,
        started_at="2026-07-17T13:00:00Z",
        status="failure",
        target_label="unsafe",
        binary_sha256="sha256:unsafe",
        file_sha256="sha256:unsafe-file",
    )
    unsafe["file_path"] = "unsafe.egg"
    unsafe["error_message"] = "</script><script>globalThis.injected = true</script>"
    store.append(unsafe)
    destination = tmp_path / "nested" / "report.html"

    written = interactive.write_interactive_report(store, comparison, destination)

    assert written == destination.resolve()
    assert not list(destination.parent.glob(f".{destination.name}.*.tmp"))
    html = destination.read_text(encoding="utf-8")
    envelope = _embedded_envelope(html)
    assert base64.b64decode(cast(str, envelope["report_jsonl_base64"])) == store.path.read_bytes()
    assert cast(str, envelope["pyodide_base_url"]) == interactive.PYODIDE_BASE_URL
    assert set(cast(dict[str, str], envelope["python_modules"])) == {
        "benchmarking/__init__.py",
        "benchmarking/models.py",
        "benchmarking/reports/__init__.py",
        "benchmarking/reports/analysis.py",
        "benchmarking/reports/catalog.py",
        "benchmarking/reports/comparison.py",
        "benchmarking/reports/interactive_runtime.py",
        "benchmarking/reports/records.py",
        "benchmarking/reports/store.py",
    }
    initial_payload = cast(dict[str, JsonValue], envelope["initial_payload"])
    assert _section_ids(initial_payload) == ["selection", "summary", "files", "phases", "rulesets"]
    assert "</script><script>globalThis.injected" not in html
    assert "127.0.0.1" not in html
    assert "/api/" not in html
    assert "initEvalLiveCatalog(reportRoot, payload.sections)" in html
    assert "scope-timeout" in html
    assert "scope-rounds" in html
    assert "scope-detail" not in html


def test_initial_html_uses_native_provenance_file_order_and_selector_labels(tmp_path: Path) -> None:
    _runtime, _payload, store, cached_comparison = _interactive_case(tmp_path)

    def native_endpoint(
        endpoint: models.BenchmarkEndpoint,
        *,
        label: str | None,
        git_sha: str,
        dirty: bool,
    ) -> models.BenchmarkEndpoint:
        row = replace(endpoint.target.row, label=label, git_sha=git_sha, is_dirty=dirty)
        return replace(endpoint, target=replace(endpoint.target, row=row))

    baseline = native_endpoint(
        cached_comparison.baseline,
        label=None,
        git_sha="feedface0001",
        dirty=True,
    )
    candidate = native_endpoint(
        cached_comparison.candidate,
        label="working-candidate",
        git_sha="feedface0002",
        dirty=False,
    )
    comparison = models.ComparisonSpec(
        baseline,
        candidate,
        cached_comparison.files[::-1],
        cached_comparison.rounds,
        cached_comparison.timeout_sec,
    )
    destination = tmp_path / "native-comparison.html"

    interactive.write_interactive_report(store, comparison, destination)

    envelope = _embedded_envelope(destination.read_text(encoding="utf-8"))
    initial_scope = cast(dict[str, JsonValue], envelope["initial_scope"])
    initial_payload = cast(dict[str, JsonValue], envelope["initial_payload"])
    assert initial_payload["sections"] == _catalog_payload(build_report_catalog(store, comparison, "rulesets"))
    selectors = cast(dict[str, JsonValue], initial_payload["selectors"])
    endpoints = cast(list[dict[str, JsonValue]], selectors["endpoints"])
    assert endpoints[:2] == [
        {
            "id": initial_scope["baseline_endpoint_id"],
            "label": "feedface0001 dirty · main/off",
            "target": "feedface0001",
            "git_sha": "feedface0001",
            "dirty": True,
            "backend": "main",
            "treatment": "off",
        },
        {
            "id": initial_scope["candidate_endpoint_id"],
            "label": "working-candidate · feedface0002 · main/proofs",
            "target": "working-candidate",
            "git_sha": "feedface0002",
            "dirty": False,
            "backend": "main",
            "treatment": "proofs",
        },
    ]
    files = cast(list[dict[str, JsonValue]], selectors["files"])
    assert [file["label"] for file in files if file["selected"]] == ["two.egg", "one.egg"]


def test_interactive_path_and_best_effort_open(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    assert interactive.interactive_report_path(tmp_path / ".reports.jsonl") == tmp_path / ".reports.html"
    assert interactive.interactive_report_path(tmp_path / "report") == tmp_path / "report.html"
    assert interactive.interactive_report_path(tmp_path / "results.html") == tmp_path / "results.html.html"
    opened: list[str] = []
    monkeypatch.setattr(interactive.webbrowser, "open", lambda url: opened.append(url))

    interactive.open_interactive_report(tmp_path / "report with spaces.html")

    assert opened == [(tmp_path / "report with spaces.html").resolve().as_uri()]

    def fail_open(_url: str) -> None:
        raise RuntimeError("browser unavailable")

    monkeypatch.setattr(interactive.webbrowser, "open", fail_open)
    interactive.open_interactive_report(tmp_path / "report.html")


def test_write_rejects_the_jsonl_path_itself(tmp_path: Path) -> None:
    _runtime, _payload, store, comparison = _interactive_case(tmp_path)
    before = store.path.read_bytes()

    with pytest.raises(ValueError, match="must differ"):
        interactive.write_interactive_report(store, comparison, store.path)

    assert store.path.read_bytes() == before


def test_embedded_python_modules_include_transitive_local_imports() -> None:
    root = Path(interactive.__file__).resolve().parents[2]
    embedded = set(interactive._PYTHON_MODULES)
    missing: set[tuple[str, str]] = set()
    for filename in embedded:
        source = (root / filename).read_text(encoding="utf-8")
        for module in _imported_modules(ast.parse(source), filename):
            dependency = _local_module_path(root, module)
            if dependency is not None and dependency not in embedded:
                missing.add((filename, dependency))

    assert not missing


def _interactive_case(
    tmp_path: Path,
) -> tuple[InteractiveRuntime, dict[str, JsonValue], ReportStore, models.ComparisonSpec]:
    report_path = tmp_path / "interactive.jsonl"
    files = (
        models.FileSpec("benchmarks/one.egg", tmp_path / "one.egg", "sha256:file-one"),
        models.FileSpec("benchmarks/two.egg", tmp_path / "two.egg", "sha256:file-two"),
        models.FileSpec("archive/three.egg", tmp_path / "three.egg", "sha256:file-three"),
    )
    endpoints = (
        make_endpoint(target_label="baseline", binary_sha256="sha256:base", treatment="off"),
        make_endpoint(target_label="candidate", binary_sha256="sha256:candidate", treatment="proofs"),
        make_endpoint(
            target_label="alternative",
            binary_sha256="sha256:alternative",
            backend="dd",
            treatment="proofs",
        ),
        make_endpoint(target_label="historical", binary_sha256="sha256:historical", treatment="term"),
    )
    records: list[ReportRecord] = []

    def add(endpoint_order: int, file_order: int, round_index: int, *, timeout_sec: int = 120) -> None:
        endpoint = endpoints[endpoint_order]
        file = files[file_order]
        record = make_record(
            len(records),
            started_at=f"2026-07-17T12:{len(records):02d}:00Z",
            target_label=endpoint.target.row.label,
            binary_sha256=endpoint.target.binary_sha256,
            file_sha256=file.sha256,
            backend=endpoint.backend,
            treatment=endpoint.treatment,
            timeout_sec=timeout_sec,
            wall_sec=1.0 + endpoint_order * 0.2 + file_order * 0.1 + round_index * 0.01,
        )
        record["file_path"] = file.display_path
        records.append(record)

    for endpoint_order in (0, 1):
        for file_order in (0, 1):
            for round_index in (0, 1):
                add(endpoint_order, file_order, round_index)
    add(2, 1, 0)
    add(3, 2, 0, timeout_sec=60)
    write_report(report_path, *records)
    comparison = models.ComparisonSpec(endpoints[0], endpoints[1], files[:2], 2, 120)
    store = ReportStore(report_path)
    runtime = InteractiveRuntime(
        store,
        scope_for_comparison(comparison),
    )
    return runtime, runtime.payload(), store, comparison


def _section_ids(payload: dict[str, JsonValue]) -> list[JsonValue]:
    sections = cast(list[dict[str, JsonValue]], payload["sections"])
    return [section["id"] for section in sections]


def _embedded_envelope(html: str) -> dict[str, Any]:
    marker = '<script id="report-envelope" type="application/octet-stream">'
    encoded = html.split(marker, 1)[1].split("</script>", 1)[0]
    return cast(dict[str, Any], json.loads(base64.b64decode(encoded)))


def _imported_modules(tree: ast.AST, filename: str) -> set[str]:
    module_name = filename.removesuffix(".py").replace("/", ".").removesuffix(".__init__")
    package = module_name if filename.endswith("/__init__.py") else module_name.rpartition(".")[0]
    imported: set[str] = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            imported.update(alias.name for alias in node.names)
        elif isinstance(node, ast.ImportFrom):
            relative = "." * node.level + (node.module or "")
            base = importlib.util.resolve_name(relative, package) if node.level else relative
            imported.add(base)
            imported.update(f"{base}.{alias.name}" for alias in node.names)
    return imported


def _local_module_path(root: Path, module: str) -> str | None:
    relative = module.replace(".", "/")
    module_path = relative + ".py"
    if (root / module_path).is_file():
        return module_path
    package_path = relative + "/__init__.py"
    return package_path if (root / package_path).is_file() else None
