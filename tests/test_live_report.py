"""Test cache-only live retargeting, serialization, assets, and HTTP routes."""

from __future__ import annotations

import http.server
import json
import threading
import urllib.error
import urllib.request
from pathlib import Path
from typing import cast

import pytest

from benchmarking import models
from benchmarking.reports import live
from benchmarking.reports.catalog import ReportOptions
from benchmarking.reports.comparison import build_report_catalog
from benchmarking.reports.database import ReportDatabase
from benchmarking.reports.records import ReportRecord

from .conftest import make_endpoint, make_record, write_report


def test_session_discovers_atomic_cached_endpoints_and_retargets(tmp_path: Path) -> None:
    session, payload = _live_case(tmp_path)
    selectors = cast(dict[str, object], payload["selectors"])
    endpoints = cast(list[dict[str, object]], selectors["endpoints"])

    # The fourth endpoint has rows for only one of two files, so it cannot be
    # selected as an atomic endpoint in this session.
    assert len(endpoints) == 3
    assert {endpoint["label"] for endpoint in endpoints} == {
        "baseline · abc123 · main/off",
        "candidate · abc123 · main/proofs",
        "alternative · abc123 · dd/proofs",
    }
    assert selectors["rounds"] == 1
    assert selectors["timeout_sec"] == 120

    alternative = next(endpoint for endpoint in endpoints if endpoint["backend"] == "dd")
    baseline = next(endpoint for endpoint in endpoints if endpoint["treatment"] == "off")
    files = cast(list[dict[str, object]], selectors["files"])
    narrowed = session.apply(
        {
            "baseline_endpoint_id": alternative["id"],
            "candidate_endpoint_id": baseline["id"],
            "file_ids": [files[1]["id"]],
            "detail": "phases",
        }
    )

    narrowed_selectors = cast(dict[str, object], narrowed["selectors"])
    assert narrowed_selectors["baseline_endpoint_id"] == alternative["id"]
    assert narrowed_selectors["candidate_endpoint_id"] == baseline["id"]
    assert [file["selected"] for file in cast(list[dict[str, object]], narrowed_selectors["files"])] == [
        False,
        True,
    ]
    assert [section["id"] for section in cast(list[dict[str, object]], narrowed["sections"])] == [
        "selection",
        "summary",
        "files",
        "phases",
    ]


def test_invalid_apply_restores_the_published_request_and_catalog(tmp_path: Path) -> None:
    session, payload = _live_case(tmp_path)
    selectors = cast(dict[str, object], payload["selectors"])
    endpoint_id = selectors["baseline_endpoint_id"]
    file_ids = [file["id"] for file in cast(list[dict[str, object]], selectors["files"])]

    with pytest.raises(ValueError, match="must be different"):
        session.apply(
            {
                "baseline_endpoint_id": endpoint_id,
                "candidate_endpoint_id": endpoint_id,
                "file_ids": file_ids,
                "detail": "summary",
            }
        )
    assert session.payload() == payload

    with pytest.raises(ValueError, match="file_ids must not be empty"):
        session.apply(
            {
                "baseline_endpoint_id": selectors["baseline_endpoint_id"],
                "candidate_endpoint_id": selectors["candidate_endpoint_id"],
                "file_ids": [],
                "detail": "summary",
            }
        )
    assert session.payload() == payload


def test_http_routes_return_report_apply_errors_and_exact_assets(tmp_path: Path) -> None:
    session, payload = _live_case(tmp_path)
    assets = {
        "/": live.StaticAsset(b"index", "text/plain"),
        "/app.js": live.StaticAsset(b"script", "text/javascript"),
    }
    server = http.server.HTTPServer(("127.0.0.1", 0), live.live_handler(session, assets))
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    root = f"http://127.0.0.1:{server.server_port}"
    try:
        with urllib.request.urlopen(root + "/api/report") as response:
            assert json.load(response) == payload
            assert response.headers["Cache-Control"] == "no-store"
        with urllib.request.urlopen(root + "/") as response:
            assert response.read() == b"index"
        with pytest.raises(urllib.error.HTTPError) as missing:
            urllib.request.urlopen(root + "/missing")
        assert missing.value.code == 404

        bad_request = urllib.request.Request(
            root + "/api/scope",
            data=b"{}",
            method="PUT",
            headers={"Content-Type": "application/json"},
        )
        with pytest.raises(urllib.error.HTTPError) as bad:
            urllib.request.urlopen(bad_request)
        assert bad.value.code == 400
        assert "baseline_endpoint_id must be a string" in bad.value.read().decode()
    finally:
        server.shutdown()
        server.server_close()
        thread.join(timeout=2)


def test_browser_ui_exposes_pair_swap_files_detail_and_atomic_rollback() -> None:
    assert "scope-baseline" in live.APP_JS
    assert "scope-candidate" in live.APP_JS
    assert "Swap endpoints" in live.APP_JS
    assert "scope-detail" in live.APP_JS
    assert 'data-kind = "file"' not in live.APP_JS
    assert 'input.dataset.kind = "file"' in live.APP_JS
    assert "rounds:" not in live.APP_JS
    assert "timeout_sec:" not in live.APP_JS
    assert "renderScope(currentPayload.selectors" in live.APP_JS
    assert "initEvalLiveCatalog(reportRoot, payload.sections)" in live.APP_JS


def _live_case(tmp_path: Path) -> tuple[live.LiveReportSession, dict[str, live.JsonValue]]:
    report_path = tmp_path / "live.duckdb"
    files = (
        models.FileSpec("benchmarks/one.egg", tmp_path / "one.egg", "sha256:file-one"),
        models.FileSpec("benchmarks/two.egg", tmp_path / "two.egg", "sha256:file-two"),
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
    )
    records: list[ReportRecord] = []
    for endpoint_order, endpoint in enumerate(endpoints):
        for file_order, file in enumerate(files):
            records.append(
                make_record(
                    len(records),
                    started_at=f"2026-07-17T12:00:{len(records):02d}Z",
                    target_label=endpoint.target.row.label,
                    binary_sha256=endpoint.target.binary_sha256,
                    file_sha256=file.sha256,
                    backend=endpoint.backend,
                    treatment=endpoint.treatment,
                    wall_sec=1.0 + endpoint_order * 0.2 + file_order * 0.1,
                )
            )
    # Discoverability is endpoint-atomic: this incomplete target is excluded.
    records.append(
        make_record(
            len(records),
            started_at=f"2026-07-17T12:00:{len(records):02d}Z",
            target_label="incomplete",
            binary_sha256="sha256:incomplete",
            file_sha256=files[0].sha256,
            treatment="off",
        )
    )
    write_report(report_path, *records)
    comparison = models.ComparisonSpec(endpoints[0], endpoints[1], files, 1, 120)
    options = ReportOptions("summary")
    with ReportDatabase(report_path) as database:
        catalog = build_report_catalog(database, comparison, options)
    session = live.LiveReportSession(report_path, comparison, options, catalog)
    return session, session.payload()
