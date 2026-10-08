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
from benchmarking.reports.interactive_runtime import (
    InitialScope,
    InteractiveRuntime,
    JsonValue,
    _catalog_payload,
    scope_for_comparison,
)
from benchmarking.reports.presentation import build_report_catalog
from benchmarking.reports.store import ReportRecord, ReportStore, serialize_grouped_report

from .report_fixtures import make_endpoint, make_record, write_report


def test_runtime_discovers_entire_cache_and_retargets_all_sections(tmp_path: Path) -> None:
    runtime, payload, _store, _comparison = _interactive_case(tmp_path)
    selectors = cast(dict[str, JsonValue], payload["selectors"])
    endpoints = cast(list[dict[str, JsonValue]], selectors["endpoints"])
    files = cast(list[dict[str, JsonValue]], selectors["files"])

    assert {endpoint["label"] for endpoint in endpoints} == {
        "alternative · abc123 · proofs/nee",
        "baseline · abc123 · off/nee",
        "candidate · abc123 · proofs/nee",
        "historical · abc123 · term/nee",
    }
    assert {file["label"] for file in files} == {"one.egg", "two.egg", "three.egg"}
    assert selectors["timeouts_sec"] == [60, 120]
    assert selectors["rounds"] == 2
    assert selectors["max_rounds"] == 2
    assert _section_ids(payload) == ["selection", "summary", "files", "phases", "rulesets"]

    alternative = next(endpoint for endpoint in endpoints if endpoint["target"] == "alternative")
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
    alternative = next(endpoint for endpoint in endpoints if endpoint["target"] == "alternative")
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


def test_scope_request_rejects_invalid_field_types_without_changing_report(tmp_path: Path) -> None:
    runtime, payload, _store, comparison = _interactive_case(tmp_path)
    valid = scope_for_comparison(comparison)
    file_ids = cast(list[str], valid["file_ids"])
    invalid_requests = (
        (valid | {"baseline_endpoint_id": 1}, "endpoint ids must be strings"),
        (valid | {"file_ids": "not-a-list"}, "file_ids must be a list of strings"),
        (valid | {"file_ids": [1]}, "file_ids must be a list of strings"),
        (valid | {"file_ids": {file_ids[0]: True}}, "file_ids must be a list of strings"),
        (valid | {"timeout_sec": True}, "timeout_sec must be an integer"),
        (valid | {"timeout_sec": 120.0}, "timeout_sec must be an integer"),
        (valid | {"rounds": True}, "rounds must be an integer"),
        (valid | {"rounds": 1.0}, "rounds must be an integer"),
    )

    for request, message in invalid_requests:
        result = json.loads(runtime.apply_json(json.dumps(request)))
        assert result == {"ok": False, "error": message}
        assert runtime.payload() == payload


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


def test_suite_validation_survives_export_swaps_and_subsets_without_leaking_to_other_targets(tmp_path: Path) -> None:
    _runtime, _payload, store, comparison = _interactive_case(tmp_path)
    reason = "strict proof validation failed: invalid witness"
    comparison = replace(comparison, suite_mode=True, validation_issues=((comparison.files[0], reason),))
    destination = tmp_path / "suite.html"
    interactive.write_interactive_report(store.grouped_report(), comparison, destination)
    envelope = _embedded_envelope(destination.read_text(encoding="utf-8"))
    scope = cast(dict[str, JsonValue], envelope["initial_scope"])
    grouped_path = tmp_path / "grouped.json"
    grouped_path.write_bytes(serialize_grouped_report(store.grouped_report()))
    runtime = InteractiveRuntime.from_path(grouped_path, store.display_path, json.dumps(scope))

    assert reason in json.dumps(envelope["initial_payload"])
    assert reason in json.dumps(runtime.payload())
    swapped = scope | {
        "baseline_endpoint_id": scope["candidate_endpoint_id"],
        "candidate_endpoint_id": scope["baseline_endpoint_id"],
        "file_ids": cast(list[str], scope["file_ids"])[:1],
        "rounds": 1,
    }
    assert reason in json.dumps(runtime.apply(swapped))
    assert reason not in json.dumps(runtime.apply(scope | {"file_ids": cast(list[str], scope["file_ids"])[1:]}))
    unavailable = "strict validation unavailable for this selection"
    changed_timeout = json.dumps(runtime.apply(scope | {"timeout_sec": 60}))
    assert reason not in changed_timeout
    assert unavailable not in changed_timeout
    selectors = cast(dict[str, JsonValue], runtime.payload()["selectors"])
    alternative = next(
        endpoint
        for endpoint in cast(list[dict[str, JsonValue]], selectors["endpoints"])
        if endpoint["target"] == "alternative"
    )
    changed_endpoint = json.dumps(runtime.apply(scope | {"candidate_endpoint_id": alternative["id"]}))
    assert reason not in changed_endpoint
    assert unavailable not in changed_endpoint
    assert reason in json.dumps(runtime.apply(scope | {"validation_issues": {}}))


@pytest.mark.parametrize("change", ["endpoint", "timeout", "file"])
def test_suite_retargeting_reports_complete_measurements_without_validation_prerequisite(
    tmp_path: Path, change: str
) -> None:
    _runtime, _payload, store, comparison = _interactive_case(tmp_path)
    comparison = replace(comparison, suite_mode=True, files=comparison.files[:1], rounds=1)
    # Give every retargeted selection complete successful timings. Missing data
    # and absent correctness diagnostics must not suppress these performance ratios.
    for row in tuple(store.records):
        if row["file_sha256"] == comparison.files[0].sha256:
            store.append(row | {"timeout_sec": 60})
            if row["treatment"] == "proofs":
                store.append(row | {"binary_sha256": "sha256:alternative", "target_label": "alternative"})
    scope = scope_for_comparison(comparison)
    runtime = InteractiveRuntime(store.grouped_report(), scope)
    selectors = cast(dict[str, Any], runtime.payload()["selectors"])
    if change == "endpoint":
        scope["candidate_endpoint_id"] = next(e["id"] for e in selectors["endpoints"] if e["target"] == "alternative")
    elif change == "timeout":
        scope["timeout_sec"] = 60
    else:
        scope["file_ids"] = [next(f["id"] for f in selectors["files"] if f["label"] == "two.egg")]
    updated = runtime.apply(scope)
    sections = cast(list[dict[str, Any]], updated["sections"])
    wall = next(
        block
        for section in sections
        if section["id"] == "files"
        for block in section["blocks"]
        if block["name"] == "Wall time"
    )
    assert "strict validation" not in json.dumps(wall)
    assert "missing" not in json.dumps(wall)
    for row in wall["rows"]:
        assert row["ratio"]["value"] == pytest.approx(row["candidate"]["value"] / row["baseline"]["value"])


def test_suite_artifact_analyzes_all_available_rows_below_topup_target(tmp_path: Path) -> None:
    _runtime, _payload, store, comparison = _interactive_case(tmp_path)
    comparison = replace(comparison, suite_mode=True, rounds=30)
    runtime = InteractiveRuntime(store.grouped_report(), scope_for_comparison(comparison))
    payload = runtime.initial_payload(comparison)
    selectors = cast(dict[str, JsonValue], payload["selectors"])

    assert selectors["rounds"] == 30
    assert selectors["max_rounds"] == 30
    assert "missing 28 row(s)" not in json.dumps(payload)
    assert "all matching observations; top-up target 30" in json.dumps(payload)
    assert runtime.apply(scope_for_comparison(comparison))["sections"] == payload["sections"]


def test_standard_artifact_preserves_requested_rounds_above_cached_maximum(tmp_path: Path) -> None:
    _runtime, _payload, store, comparison = _interactive_case(tmp_path)
    comparison = replace(comparison, rounds=30)
    runtime = InteractiveRuntime(store.grouped_report(), scope_for_comparison(comparison))
    payload = runtime.initial_payload(comparison)
    selectors = cast(dict[str, JsonValue], payload["selectors"])

    assert selectors["rounds"] == selectors["max_rounds"] == 30
    assert "missing 28 row(s)" in json.dumps(payload)
    assert runtime.apply(scope_for_comparison(comparison))["sections"] == payload["sections"]


def test_empty_standard_artifact_retains_branch_and_main_proof_endpoints(tmp_path: Path) -> None:
    store = ReportStore(tmp_path / "empty.jsonl")
    comparison = models.ComparisonSpec(
        make_endpoint(target_label="main", binary_sha256="sha256:main", treatment="proofs"),
        make_endpoint(target_label="branch", binary_sha256="sha256:branch", treatment="proofs"),
        (models.FileSpec("file.egg", tmp_path / "file.egg", "sha256:file"),),
        3,
        300,
        report_notes=("Collection budget expired before either endpoint ran.",),
    )
    destination = tmp_path / "partial.html"

    interactive.write_interactive_report(store.grouped_report(), comparison, destination)
    envelope = _embedded_envelope(destination.read_text(encoding="utf-8"))
    scope = cast(InitialScope, envelope["initial_scope"])
    runtime = InteractiveRuntime(store.grouped_report(), scope)
    initial = runtime.initial_payload(comparison)
    selectors = cast(dict[str, Any], initial["selectors"])

    assert [(endpoint["target"], endpoint["treatment"]) for endpoint in selectors["endpoints"]] == [
        ("main", "proofs"),
        ("branch", "proofs"),
    ]
    assert selectors["baseline_endpoint_id"] != selectors["candidate_endpoint_id"]
    assert "missing 3 row(s)" in json.dumps(initial)
    swapped = runtime.apply(
        scope
        | {
            "baseline_endpoint_id": scope["candidate_endpoint_id"],
            "candidate_endpoint_id": scope["baseline_endpoint_id"],
            "rounds": 1,
        }
    )
    assert "missing 1 row(s)" in json.dumps(swapped)
    assert comparison.report_notes[0] in json.dumps(initial)
    assert comparison.report_notes[0] in json.dumps(swapped)
    assert "benchmarking/known_failures.py" in cast(dict[str, str], envelope["python_modules"])
    assert not store.path.exists()


def test_suite_artifact_displays_preparation_failures_without_measurement_rows(tmp_path: Path) -> None:
    store = ReportStore(tmp_path / "empty.jsonl")
    baseline = make_endpoint(target_label="baseline", binary_sha256="sha256:base", treatment="off")
    candidate = make_endpoint(target_label="candidate", binary_sha256="sha256:base", treatment="proof-extraction")
    file = models.FileSpec(
        "blocked.egg", tmp_path / "blocked.egg", "sha256:blocked", tmp_path / "facts", "sha256:facts"
    )
    reason = "strict proof validation failed before measurements"
    comparison = models.ComparisonSpec(
        baseline, candidate, (file,), 30, 120, validation_issues=((file, reason),), suite_mode=True
    )
    destination = tmp_path / "blocked.html"

    interactive.write_interactive_report(store.grouped_report(), comparison, destination)
    envelope = _embedded_envelope(destination.read_text(encoding="utf-8"))
    scope = cast(dict[str, JsonValue], envelope["initial_scope"])
    grouped_path = tmp_path / "grouped.json"
    grouped_path.write_bytes(serialize_grouped_report(store.grouped_report()))
    runtime = InteractiveRuntime.from_path(grouped_path, store.display_path, json.dumps(scope))
    updated = runtime.apply(scope | {"rounds": 1})

    assert json.loads(base64.b64decode(cast(str, envelope["report_grouped_base64"])))["groups"] == []
    assert reason in json.dumps(envelope["initial_payload"])
    assert reason in json.dumps(updated)
    assert "facts" in json.dumps(updated)
    assert not store.records
    assert not store.path.exists()


def test_runtime_discovers_native_egg_rows_alongside_egglog_rows(tmp_path: Path) -> None:
    _runtime, _payload, store, comparison = _interactive_case(tmp_path)
    store.append(
        make_record(
            20,
            started_at="2026-07-17T13:00:00Z",
            target_label="native",
            binary_sha256="sha256:native",
            file_sha256=comparison.files[0].sha256,
            treatment="egg",
        )
    )

    runtime = InteractiveRuntime(store.grouped_report(), scope_for_comparison(comparison))
    selectors = cast(dict[str, JsonValue], runtime.payload()["selectors"])
    endpoints = cast(list[dict[str, JsonValue]], selectors["endpoints"])
    native = next(endpoint for endpoint in endpoints if endpoint["treatment"] == "egg")
    updated = runtime.apply(scope_for_comparison(comparison) | {"candidate_endpoint_id": native["id"], "rounds": 1})

    assert "native" in json.dumps(updated)
    assert "missing" in json.dumps(updated)


def test_html_embeds_exact_grouped_snapshot_initial_catalog_runtime_and_safe_data(tmp_path: Path) -> None:
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

    written = interactive.write_interactive_report(store.grouped_report(), comparison, destination)

    assert written == destination.resolve()
    assert not list(destination.parent.glob(f".{destination.name}.*.tmp"))
    html = destination.read_text(encoding="utf-8")
    envelope = _embedded_envelope(html)
    assert base64.b64decode(cast(str, envelope["report_grouped_base64"])) == serialize_grouped_report(
        store.grouped_report()
    )
    assert cast(str, envelope["pyodide_base_url"]) == interactive.PYODIDE_BASE_URL
    assert set(cast(dict[str, str], envelope["python_modules"])) == {
        "benchmarking/__init__.py",
        "benchmarking/engines.py",
        "benchmarking/known_failures.py",
        "benchmarking/math_workloads.py",
        "benchmarking/models.py",
        "benchmarking/reports/__init__.py",
        "benchmarking/reports/analysis.py",
        "benchmarking/reports/catalog.py",
        "benchmarking/reports/interactive_runtime.py",
        "benchmarking/reports/presentation.py",
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

    interactive.write_interactive_report(store.grouped_report(), comparison, destination)

    envelope = _embedded_envelope(destination.read_text(encoding="utf-8"))
    initial_scope = cast(dict[str, JsonValue], envelope["initial_scope"])
    initial_payload = cast(dict[str, JsonValue], envelope["initial_payload"])
    assert initial_payload["sections"] == _catalog_payload(
        build_report_catalog(store.grouped_report(), comparison, "rulesets")
    )
    selectors = cast(dict[str, JsonValue], initial_payload["selectors"])
    endpoints = cast(list[dict[str, JsonValue]], selectors["endpoints"])
    assert endpoints[:2] == [
        {
            "id": initial_scope["baseline_endpoint_id"],
            "label": "feedface0001 dirty · off/nee",
            "target": "feedface0001",
            "git_sha": "feedface0001",
            "dirty": True,
            "treatment": "off",
        },
        {
            "id": initial_scope["candidate_endpoint_id"],
            "label": "working-candidate · feedface0002 · proofs/nee",
            "target": "working-candidate",
            "git_sha": "feedface0002",
            "dirty": False,
            "treatment": "proofs",
        },
    ]
    files = cast(list[dict[str, JsonValue]], selectors["files"])
    assert [file["label"] for file in files if file["selected"]] == ["two.egg", "one.egg"]


@pytest.mark.parametrize("native_only", [False, True], ids=["mixed", "native-only"])
def test_grouped_runtime_restores_logical_workload_physical_input_bindings(tmp_path: Path, native_only: bool) -> None:
    physical = models.FileSpec("source.in", tmp_path / "source.in", "sha256:native-input")
    logical = models.FileSpec(
        "source.egg",
        tmp_path / "source.egg",
        "sha256:egglog-input",
        engine_inputs=(("egg-de", physical), ("egg-ee", physical)),
    )
    baseline = make_endpoint(binary_sha256="sha256:baseline", treatment="off")
    if native_only:
        baseline = models.BenchmarkEndpoint(
            replace(baseline.target, engine_binaries=(models.EngineBinary("egg-ee", "sha256:baseline", None),)),
            "egg-ee",
        )
    target = replace(
        baseline.target,
        engine_binaries=(models.EngineBinary("egg-de", "sha256:native", None),),
    )
    candidate = models.BenchmarkEndpoint(target, "egg-de")
    comparison = models.ComparisonSpec(baseline, candidate, (logical,), 1, 120)
    path = tmp_path / "report.jsonl"
    records: list[ReportRecord] = []
    for endpoint, file in ((baseline, physical if native_only else logical), (candidate, physical)):
        record = make_record(
            len(records),
            started_at="2026-09-30T00:00:00Z",
            binary_sha256=endpoint.target.binary_sha256_for(endpoint.treatment),
            treatment=endpoint.treatment,
            file_sha256=file.sha256,
        )
        record["file_path"] = file.display_path
        records.append(record)
    write_report(path, *records)
    snapshot = ReportStore(path).grouped_report()
    if native_only:
        assert {group["key"]["file_sha256"] for group in snapshot.data["groups"]} == {physical.sha256}
    grouped_path = tmp_path / "grouped.json"
    grouped_path.write_bytes(serialize_grouped_report(snapshot))
    destination = tmp_path / "report.html"
    interactive.write_interactive_report(snapshot, comparison, destination)
    envelope = _embedded_envelope(destination.read_text())
    scope = cast(dict[str, JsonValue], envelope["initial_scope"])

    runtime = InteractiveRuntime.from_path(grouped_path, str(path), json.dumps(scope))

    expected = _catalog_payload(build_report_catalog(snapshot, comparison, "rulesets"))
    assert envelope["initial_payload"]["sections"] == expected
    assert runtime.payload()["sections"] == expected
    assert "missing 1 row(s)" not in json.dumps(runtime.payload())
    swapped = scope | {
        "baseline_endpoint_id": scope["candidate_endpoint_id"],
        "candidate_endpoint_id": scope["baseline_endpoint_id"],
    }
    assert runtime.apply(swapped)["sections"] == _catalog_payload(
        build_report_catalog(snapshot, replace(comparison, baseline=candidate, candidate=baseline), "rulesets")
    )
    assert runtime.apply(scope)["sections"] == expected
    assert grouped_path.read_bytes() == serialize_grouped_report(snapshot)


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
        interactive.write_interactive_report(store.grouped_report(), comparison, store.path)

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
        store.grouped_report(),
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
