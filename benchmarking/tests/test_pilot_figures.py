"""Pilot coverage, worker identity, executed proof evidence and offline replay."""

from __future__ import annotations

import io
import json
from copy import deepcopy
from dataclasses import replace
from pathlib import Path
from typing import Any, cast

import pytest
from rich.console import Console

from benchmarking import collection, models, pilot_figures, pilot_results, processes
from benchmarking.engines import TREATMENT_SPECS, Treatment
from benchmarking.reports.store import CacheKey, ProofSummaryRecord, ReportStore, serialize_report_record

from .report_fixtures import make_record, make_target


def snapshot_fixture() -> dict[str, Any]:
    names = (
        "math",
        "math-proofs",
        "slotted",
        "slotted-proofs",
        "slotted-complete",
        "slotted-complete-proofs",
        "disequality",
        "disequality-proofs",
        "corpus-congruence",
    )
    summary: ProofSummaryRecord = {
        "schema_version": 1,
        "success": True,
        "check_requests": 1,
        "extraction_requests": 2,
        "produced_certificates": 3,
        "verified_certificates": 3,
    }
    conditions = []
    for index, treatment in enumerate(("off", "term", "proof-extraction")):
        rows = [
            dict(
                make_record(
                    i,
                    started_at=f"2026-11-11T12:00:0{i}Z",
                    treatment=cast(Treatment, treatment),
                    wall_sec=0.001 * (index + 1) * (1 + i / 10),
                    max_rss_bytes=1048576,
                    threads=4,
                    requested_threads=4,
                ),
                row_index=3 * index + i,
            )
            for i in range(3)
        ]
        conditions.append(
            {
                "id": str(index),
                "logical_id": "sha256:file",
                "file_sha256": "sha256:file",
                "label": "Tiny workload",
                "path": "gone.egg",
                "project": "demo",
                "input_loc": 12,
                "ordinary_output_parity": "not-compared",
                "table_correspondence": "not-checked",
                "treatment": treatment,
                "binary_sha256": "sha256:bin",
                "threads": 4,
                "requested_threads": 4,
                "observations": rows,
                "exclusion": None,
                "validation": {"status": "passed", "issue": None, "summary": summary, "observation": None}
                if treatment == "proof-extraction"
                else None,
            }
        )
    comparisons = [
        {
            "scope": "composition" if name == "slotted-complete-proofs" else "extensions",
            "experiment": name,
            "series": f"{name} (extlog_cp)",
            "project": "demo",
            "logical_id": "sha256:file",
            "label": "Tiny workload",
            "candidate_label": "extlog_cp",
            "reference_label": "egglog",
            "baseline": "0",
            "candidate": "2" if "proof" in name else "1",
        }
        for name in names
    ]
    comparisons.extend(
        {
            **comparisons[-1],
            "scope": "applications",
            "candidate": candidate,
            "candidate_label": "extlog_cp" if candidate == "2" else "extlog_c",
            "series": "Demo",
        }
        for candidate in ("2",)
    )
    return {
        "pilot_data_version": 1,
        "rounds": 3,
        "requested_threads": 4,
        "timeout_sec": 500,
        "memory_limit_bytes": 17179869184,
        "experiments": [
            {
                "id": name,
                "label": name,
                "candidate_label": "extlog_cp",
                "color": f"#{i + 1:06x}",
                "scope": "composition" if name == "slotted-complete-proofs" else "extensions",
            }
            for i, name in enumerate(names)
        ],
        "projects": {
            "demo": {
                "id": "demo",
                "label": "Demo",
                "color": "#0072b2",
                "source": "https://example.com",
                "capture": "captured",
            }
        },
        "files": [{"logical_id": "sha256:file", "project": "demo", "input_loc": 12}],
        "conditions": conditions,
        "comparisons": comparisons,
        "provenance": {"target": {"git_sha": "frozen"}},
    }


def test_worker_counts_are_part_of_real_cache_selection(tmp_path: Path) -> None:
    store = ReportStore(tmp_path / "report.jsonl")
    for threads, value in ((1, 1.0), (4, 0.4)):
        store.append(make_record(0, started_at="2026-11-11T12:00:00Z", wall_sec=value, threads=threads))
    assert (
        store.latest_records(CacheKey("sha256:bin", "sha256:file", "off", 1), 1, 500, None)[0].record["wall_sec"] == 1
    )
    assert (
        store.latest_records(CacheKey("sha256:bin", "sha256:file", "off", 4), 1, 500, None)[0].record["wall_sec"] == 0.4
    )
    request = models.EndpointRequest(make_target().request, "egg", threads=4)
    assert (request.threads, request.requested_threads) == (1, 4)


def test_pilot_freezes_verified_executables_before_collection(tmp_path: Path) -> None:
    from benchmarking.targets import sha256_file

    binary = tmp_path / "egglog-experimental"
    binary.write_bytes(b"original executable")
    target = make_target(binary_path=binary, binary_sha256=sha256_file(binary))
    frozen = pilot_figures.freeze_target(target, tmp_path / "executables")
    assert frozen.binary_path != binary and frozen.binary_path is not None
    binary.write_bytes(b"later Cargo output")
    assert frozen.binary_path.read_bytes() == b"original executable"
    assert pilot_figures.freeze_target(target, tmp_path / "executables") == frozen
    with pytest.raises(ValueError, match="build output changed"):
        pilot_figures.freeze_target(target, tmp_path / "another-cache")
    cached = replace(target, binary_path=None)
    assert pilot_figures.freeze_target(cached, tmp_path / "unused").binary_path is None
    assert not (tmp_path / "unused").exists()


def test_four_worker_launch_omits_phase_timing_and_can_be_persisted(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    source = tmp_path / "input.egg"
    source.write_text("(check (= 1 1))")
    from benchmarking.targets import sha256_file

    file = models.FileSpec(str(source), source, sha256_file(source))
    commands = []

    def run(command: list[str], *_args: Any, **_kwargs: Any) -> processes.TimingResult:
        commands.append(command)
        return processes.TimingResult("success", processes.TimingRow(wall_sec=0.1, max_rss_bytes=100), None)

    monkeypatch.setattr(collection, "run_command", run)
    observed = collection.run_process(tmp_path / "binary", tmp_path, file, "off", 500, threads=4)
    assert "--timing-summary" not in commands[0]
    assert commands[0][commands[0].index("-j") + 1] == "4"
    target = make_target()
    plan = collection.BenchmarkRunPlan(file, "off", 3, (), 3, threads=4, requested_threads=4)
    row = collection.flat_report_record(
        started_at="2026-11-11T12:00:00Z", target=target, run=plan, timeout_sec=500, observation=observed
    )
    assert json.loads(serialize_report_record(row))["timing_summary"] is None


def test_checked_launch_counts_requests_without_repeating_timed_rounds(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    target = make_target(binary_path=tmp_path / "frozen")
    file = models.FileSpec("input.egg", tmp_path / "input.egg", "sha256:file")
    request = collection.BenchmarkRequest(
        models.EndpointRequest(target.request, "proof-extraction", threads=4), (file,)
    )
    store = ReportStore(tmp_path / "report.jsonl")
    calls = []
    summary: ProofSummaryRecord = {
        "schema_version": 1,
        "success": True,
        "check_requests": 1,
        "extraction_requests": 2,
        "produced_certificates": 3,
        "verified_certificates": 3,
    }

    def observe(*args: Any, **kwargs: Any) -> collection.ProcessObservation:
        calls.append((args, kwargs))
        return collection.ProcessObservation(
            processes.TimingResult("success", processes.TimingRow(wall_sec=1), None), None, summary
        )

    monkeypatch.setattr(collection, "run_process", observe)
    for _ in range(2):
        collection.validate_proof_requests(
            store, (request, request), {target.request: target}, 500, Console(file=io.StringIO())
        )
    assert len(calls) == 1
    assert calls[0][0][3:5] == ("proof-testing", 1500)
    assert calls[0][1] == {"threads": 4, "proof_summary": True}
    evidence = collection.select_proof_validation(
        store,
        models.BenchmarkEndpoint(
            target.row, target.binary_sha256_for("proof-extraction"), "proof-extraction", threads=4
        ),
        file,
        1500,
    )
    assert evidence["status"] == "passed" and evidence["summary"]["verified_certificates"] == 3


def test_runtime_and_speedup_views_share_samples_and_keep_tiny_inputs() -> None:
    snapshot = snapshot_fixture()
    runtime = pilot_results.pilot_results(snapshot, "extensions-runtime")
    speedup = pilot_results.pilot_results(snapshot, "extensions-speedup")
    assert runtime["selection_sha256"] == speedup["selection_sha256"]
    assert len(runtime["points"]) == len(speedup["points"]) == 8
    assert runtime["points"][0]["x"] < 0.2
    assert speedup["points"][0]["y"] == pytest.approx(0.5)
    assert all(point["x_low"] < point["x"] < point["x_high"] for point in runtime["points"])
    assert all(point["y_low"] < point["y"] < point["y_high"] for point in speedup["points"])
    spec = pilot_figures.bound_spec(runtime)
    color = spec["layer"][-1]["encoding"]["color"]["scale"]
    assert {point["series"] for point in runtime["points"]} == set(color["domain"])
    assert (
        spec["layer"][-1]["encoding"]["x"]["scale"]["domain"] == spec["layer"][-1]["encoding"]["y"]["scale"]["domain"]
    )


@pytest.mark.parametrize("state", ["missing", "failed", "excluded", "unknown-proof"])
def test_incomplete_conditions_remain_in_coverage_without_estimates(state: str) -> None:
    snapshot = snapshot_fixture()
    condition = snapshot["conditions"][2]
    if state == "missing":
        condition["observations"] = condition["observations"][:1]
    elif state == "failed":
        condition["observations"][0]["status"] = "timed-out"
    elif state == "excluded":
        condition["exclusion"] = {"kind": "resource", "reason": "historical resource failure", "evidence": "saved"}
    else:
        condition["validation"] = {
            "status": "unknown",
            "issue": "no executed proof counters",
            "summary": None,
            "observation": None,
        }
    result = pilot_results.pilot_results(snapshot, "extensions-runtime")
    assert len(result["coverage"]) == 8
    assert sum(row["planned"] for row in result["coverage"]) == 8
    proof_rows = [row for row in result["comparisons"] if row["candidate"] == "2"]
    assert proof_rows and all(row["ours"]["metrics"]["runtime"]["mean"] is None for row in proof_rows)
    assert len(result["points"]) < 8


def test_pilot_replay_never_opens_inputs_cache_or_collectors(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    source = tmp_path / "source"
    pilot_figures.export_pilot(snapshot_fixture(), source, Console(file=io.StringIO()), images=False)
    before = {path.name: path.read_bytes() for path in source.iterdir()}

    def forbidden(*_args: Any, **_kwargs: Any) -> Any:
        pytest.fail("offline replay touched live inputs or measurements")

    monkeypatch.setattr(pilot_figures, "load_experiments", forbidden)
    monkeypatch.setattr(pilot_figures, "ReportStore", forbidden)
    received = []
    monkeypatch.setattr(pilot_figures, "export_pilot", lambda snapshot, *_args: received.append(snapshot))
    assert pilot_figures.main(["--reuse-from", str(source), "--no-runs", "--output-dir", str(tmp_path / "out")]) == 0
    assert received == [snapshot_fixture()]
    assert before == {path.name: path.read_bytes() for path in source.iterdir()}


def test_late_export_failure_preserves_all_existing_pilot_files(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    snapshot = snapshot_fixture()
    destination = tmp_path / "output"
    pilot_figures.export_pilot(snapshot, destination, Console(file=io.StringIO()), images=False)
    before = {path.name: path.read_bytes() for path in destination.iterdir()}
    original = pilot_figures.bound_spec

    def fail_late(result: dict[str, Any]) -> dict[str, Any]:
        if result["figure"] == "applications-proof-runtime":
            raise ValueError("late render failure")
        return original(result)

    monkeypatch.setattr(pilot_figures, "bound_spec", fail_late)
    with pytest.raises(ValueError, match="late render failure"):
        pilot_figures.export_pilot(deepcopy(snapshot), destination, Console(file=io.StringIO()), images=False)
    assert before == {path.name: path.read_bytes() for path in destination.iterdir()}


def test_all_new_proof_endpoints_preserve_frozen_reference_modes() -> None:
    for mode in ("slotted-ref-multi-proofs", "slotted-ref-nested-proofs"):
        spec = TREATMENT_SPECS[mode]
        assert spec.binary_name == "slotted-reference-proofs"
        assert spec.flags[-2:] == ("--proof-mode", "extract")
        assert not spec.timing_summary


def test_pilot_catalog_preserves_full_corpus_complete_cases_and_reference_scope() -> None:
    config, files = pilot_figures.load_experiments(pilot_figures.DEFAULT_CONFIG)
    experiments = {row["id"]: row for row in config["experiments"]}
    assert len(experiments["corpus-congruence"]["files"]) == 486
    assert len(experiments["slotted-complete-proofs"]["files"]) == 10
    assert sum(row.get("scope", "extensions") == "extensions" for row in experiments.values()) == 8
    assert experiments["slotted-complete-proofs"]["reference"] == "slotted"
    assert experiments["disequality-proofs"]["reference"] == "egg-nee-proof-extraction"
    logical = files[experiments["disequality-proofs"]["files"][0]]
    assert logical.for_binary("egg-nee-proofs").absolute_path.suffix == ".in"
    spec = TREATMENT_SPECS["egg-nee-proof-extraction"]
    assert spec.allocator_limit and spec.build_args[-4:] == ("--features", "proof-driver", "--bin", "egg-nee-proofs")


def test_runtime_absence_is_pending_and_source_table_preserves_provenance() -> None:
    snapshot = snapshot_fixture()
    snapshot["conditions"][0]["observations"][0]["wall_sec"] = None
    result = pilot_results.pilot_results(snapshot, "extensions-runtime")
    assert not result["points"]
    assert all(row["state"] == "pending" for row in result["comparisons"])
    source = pilot_results.coverage_tables(snapshot)["corpus-sources.table.tex"]
    assert r"\href{https://example.com}{Demo}" in source and "captured" in source


def test_application_proof_views_omit_term_control_even_in_an_older_snapshot() -> None:
    snapshot = snapshot_fixture()
    snapshot["comparisons"].append({**snapshot["comparisons"][-1], "candidate": "1"})
    runtime = pilot_results.pilot_results(snapshot, "applications-proof-runtime")
    speedup = pilot_results.pilot_results(snapshot, "applications-proof-speedup")
    assert len(runtime["comparisons"]) == len(speedup["comparisons"]) == 1
    assert {row["treatment"] for row in runtime["conditions"]} == {"off", "proof-extraction"}
    assert runtime["selection_sha256"] == speedup["selection_sha256"]
    assert "shape" not in pilot_figures.bound_spec(runtime)["layer"][-1]["encoding"]
