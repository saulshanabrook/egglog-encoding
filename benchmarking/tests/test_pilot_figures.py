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

import bench
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
        "files": [
            {
                "logical_id": "sha256:file",
                "project": "demo",
                "input_loc": 12,
                "ordinary_output_parity": "not-compared",
            }
        ],
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


def test_public_entrypoint_dispatches_pilot_without_importing_it_from_legacy_figures(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    received = []

    def dispatch(argv: tuple[str, ...]) -> int:
        received.append(argv)
        return 7

    monkeypatch.setattr(pilot_figures, "main", dispatch)
    assert bench.main(["figures", "--pilot", "--threads", "4"]) == 7
    assert received == [("--threads", "4")]


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
    assert {point["configuration"] for point in runtime["points"]} <= set(color["domain"])
    assert set(color["domain"]) == {"corelog+c", "egglog+p", "egglog+d", "egglog+dp", "egglog+s", "egglog+sp"}
    assert all("extlog_" not in point["series"] for point in runtime["points"])
    axes = spec["layer"][-1]["encoding"]
    assert axes["y"]["title"] == "Our runtime (s)"
    assert axes["color"]["field"] == "configuration"
    assert axes["x"]["scale"]["domain"] != axes["y"]["scale"]["domain"]
    for axis in ("x", "y"):
        domain = axes[axis]["scale"]["domain"]
        values = [point[field] for point in runtime["points"] for field in (axis, f"{axis}_low", f"{axis}_high")]
        assert domain[0] < min(values) < max(values) < domain[1]
        assert axes[axis]["axis"]["grid"] is False
        assert len(axes[axis]["axis"]["values"]) <= 6
    for guide in spec["layer"][0]["data"]["values"]:
        for axis in ("x", "y"):
            low, high = axes[axis]["scale"]["domain"]
            assert low <= guide[axis] <= guide[f"{axis}2"] <= high
        assert guide["y"] / guide["x"] == pytest.approx(float(guide["factor"].removesuffix("×")))
        label = next(row for row in spec["layer"][1]["data"]["values"] if row["label"] == guide["factor"])
        assert guide["x"] < label["x"] < guide["x2"]
        assert label["x"] ** 2 > guide["x"] * guide["x2"]
        assert label["y"] / label["x"] == pytest.approx(guide["y"] / guide["x"])
    assert "5×" in {guide["factor"] for guide in spec["layer"][0]["data"]["values"]}


@pytest.mark.parametrize("scope", ["extensions", "applications-proof"])
def test_memory_views_reuse_runtime_observations_with_mib_axes_tables_and_numbers(scope: str) -> None:
    snapshot = snapshot_fixture()
    runtime = pilot_results.pilot_results(snapshot, f"{scope}-runtime")
    memory = pilot_results.pilot_results(snapshot, f"{scope}-memory")
    assert memory["selection_sha256"] == runtime["selection_sha256"]
    assert memory["coverage"] == runtime["coverage"]
    assert memory["metric"] == "memory" and memory["units"] == "MiB"
    assert memory["points"] and all(point["x"] == point["y"] == 1 for point in memory["points"])
    assert all(point["x_low"] == point["x_high"] == 1 for point in memory["points"])
    spec = pilot_figures.bound_spec(memory)
    assert spec["layer"][-1]["encoding"]["x"]["title"].endswith("peak RSS (MiB)")
    assert spec["layer"][-1]["encoding"]["y"]["title"] == (
        "egglog+p peak RSS (MiB)" if scope == "applications-proof" else "Our peak RSS (MiB)"
    )
    assert spec["layer"][-1]["encoding"]["color"] == pilot_figures.bound_spec(runtime)["layer"][-1]["encoding"]["color"]
    numbers, table = pilot_results.pilot_tex(memory)
    assert "/reference/memory/mean" in numbers and "/reference/runtime/mean" not in numbers
    assert "Reference (MiB) & Candidate (MiB)" in table and "Reference (s)" not in table


@pytest.mark.parametrize("rss", [None, 0])
def test_missing_rss_changes_memory_coverage_without_changing_observation_identity(rss: int | None) -> None:
    snapshot = snapshot_fixture()
    snapshot["conditions"][0]["observations"][0]["max_rss_bytes"] = rss
    runtime = pilot_results.pilot_results(snapshot, "extensions-runtime")
    memory = pilot_results.pilot_results(snapshot, "extensions-memory")
    assert memory["selection_sha256"] == runtime["selection_sha256"]
    assert len(runtime["points"]) == 8 and not memory["points"]
    assert all(row["complete"] == 1 for row in runtime["coverage"])
    assert all(row["pending"] == 1 and row["complete"] == 0 for row in memory["coverage"])
    assert all(row["reference"]["metrics"]["memory"]["mean"] is None for row in memory["comparisons"])


@pytest.mark.parametrize("state", ["missing", "failed", "excluded"])
def test_incomplete_conditions_remain_in_coverage_without_estimates(state: str) -> None:
    snapshot = snapshot_fixture()
    condition = snapshot["conditions"][2]
    if state == "missing":
        condition["observations"] = condition["observations"][:1]
    elif state == "failed":
        condition["observations"][0]["status"] = "timed-out"
    elif state == "excluded":
        condition["exclusion"] = {"kind": "resource", "reason": "historical resource failure", "evidence": "saved"}
    result = pilot_results.pilot_results(snapshot, "extensions-runtime")
    assert len(result["coverage"]) == 8
    assert sum(row["planned"] for row in result["coverage"]) == 8
    proof_rows = [row for row in result["comparisons"] if row["candidate"] == "2"]
    assert proof_rows and all(row["ours"]["metrics"]["runtime"]["mean"] is None for row in proof_rows)
    assert len(result["points"]) < 8


@pytest.mark.parametrize(
    "state",
    [
        "pending",
        "unknown",
        "timed-out",
        "memory-limited",
        "resource-limited",
        "stack-overflow",
        "infrastructure-unavailable",
        "semantic-failure",
    ],
)
def test_best_effort_validation_is_separate_from_production_timing(state: str) -> None:
    snapshot = snapshot_fixture()
    proof = snapshot["conditions"][2]
    proof["validation"] = {
        "status": state if state in ("pending", "unknown") else "failed",
        "issue": "verification unavailable" if state != "semantic-failure" else "certificate rejected",
        "summary": None,
        "observation": {"status": "failure" if state == "semantic-failure" else state},
    }
    result = pilot_results.pilot_results(snapshot, "applications-proof-runtime")
    condition = next(c for c in result["conditions"] if c["treatment"] == "proof-extraction")
    assert (condition["metrics"]["runtime"]["mean"] is None) == (state == "semantic-failure")
    assert (condition["state"] == "failed") == (state == "semantic-failure")
    if state != "semantic-failure":
        assert result["points"][0]["proof_validation_status"] != "passed"
    assert proof["validation"]["status"] != "passed"


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


def test_program_size_scope_never_collects_or_builds_runtime_endpoints(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    file = models.FileSpec("case.egg", tmp_path / "case.egg", "sha256:case")
    monkeypatch.setattr(
        pilot_figures,
        "load_experiments",
        lambda _path: ({"experiments": [{"id": "slotted", "files": ["case.egg"]}]}, {"case.egg": file}),
    )
    calls = []

    def sizes(files: tuple[models.FileSpec, ...], cache: Path, *, collect: bool) -> dict[str, Any]:
        calls.append((files, cache, collect))
        return {"status": "complete", "inputs": [], "records": []}

    def forbidden(*_args: Any, **_kwargs: Any) -> Any:
        pytest.fail("program-size scope touched timed endpoints")

    monkeypatch.setattr(pilot_figures, "program_size_snapshot", sizes)
    monkeypatch.setattr(pilot_figures, "resolve_requests", forbidden)
    monkeypatch.setattr(pilot_figures, "collect", forbidden)
    monkeypatch.setattr(pilot_figures, "validate_proof_requests", forbidden)
    monkeypatch.setattr(pilot_figures, "target_row_for_request", lambda *_args: make_target().row)
    snapshots = []

    def snapshot(*_args: Any, **kwargs: Any) -> dict[str, Any]:
        snapshots.append(kwargs["ast_snapshot"])
        return snapshot_fixture()

    monkeypatch.setattr(pilot_figures, "make_snapshot", snapshot)
    monkeypatch.setattr(pilot_figures, "export_pilot", lambda *_args: ())
    report = tmp_path / "report.jsonl"
    assert pilot_figures.main(["program-size", "--report", str(report)]) == 0
    assert calls == [((file,), tmp_path / "slotted-program-size.jsonl", True)]
    assert snapshots == [{"status": "complete", "inputs": [], "records": []}]


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
    batax = files["benchmarks/slotted/inputs/sdql/batax_2nd-44rules.egg"]
    checked = batax.exclusion_for("slotted-proof-testing", memory_limit_bytes=17179869184)
    assert checked is not None and checked.reason.startswith("Defer the full BATAX second-phase source proof")
    timed = batax.exclusion_for("slotted-proof-extraction", memory_limit_bytes=17179869184)
    assert timed is not None and "encoded multipattern mode" in timed.reason
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


@pytest.mark.parametrize(
    "missing_evidence",
    (None, "parity", "checked-input", "failed-validation", "missing-summary", "partial-certificates", "empty-project"),
)
def test_source_validation_requires_parity_and_verified_certificates_for_every_input(
    missing_evidence: str | None,
) -> None:
    snapshot = snapshot_fixture()
    first = snapshot["files"][0]
    first["ordinary_output_parity"] = "passed-c-and-cp"
    second = {**first, "logical_id": "sha256:second"}
    snapshot["files"].append(second)
    proof = deepcopy(snapshot["conditions"][2])
    proof.update(id="second-proof", logical_id=second["logical_id"])
    snapshot["conditions"].append(proof)
    if missing_evidence == "parity":
        second["ordinary_output_parity"] = "not-compared"
    elif missing_evidence == "checked-input":
        snapshot["conditions"].pop()
    elif missing_evidence == "failed-validation":
        proof["validation"]["status"] = "failed"
    elif missing_evidence == "missing-summary":
        proof["validation"]["summary"] = None
    elif missing_evidence == "partial-certificates":
        proof["validation"]["summary"]["verified_certificates"] = 1
    elif missing_evidence == "empty-project":
        snapshot["files"] = []
    source = pilot_results.coverage_tables(snapshot)["corpus-sources.table.tex"]
    assert " & Validated " in source
    assert (r"\ding{51}" in source) == (missing_evidence is None)
    assert (r"\textbf{TODO}" in source) == (missing_evidence is not None)


def test_application_proof_views_omit_term_control_even_in_an_older_snapshot() -> None:
    snapshot = snapshot_fixture()
    snapshot["comparisons"].append({**snapshot["comparisons"][-1], "candidate": "1"})
    runtime = pilot_results.pilot_results(snapshot, "applications-proof-runtime")
    speedup = pilot_results.pilot_results(snapshot, "applications-proof-speedup")
    assert len(runtime["comparisons"]) == len(speedup["comparisons"]) == 1
    assert {row["treatment"] for row in runtime["conditions"]} == {"off", "proof-extraction"}
    assert runtime["selection_sha256"] == speedup["selection_sha256"]
    assert "shape" not in pilot_figures.bound_spec(runtime)["layer"][-1]["encoding"]


def test_compact_capability_counts_execution_separately_from_timing_and_proof_validation() -> None:
    snapshot = snapshot_fixture()
    proof = snapshot["conditions"][2]
    proof["observations"] = proof["observations"][:1]
    proof["validation"] = {"status": "unknown", "issue": "no summary", "summary": None, "observation": None}
    proof["table_correspondence"] = "known-difference"
    tables = pilot_results.coverage_tables(snapshot)
    main = tables["experiment-coverage.table.tex"]
    details = tables["experiment-coverage-details.table.tex"]
    assert "math-proofs & 1 & 1/1; 1/1 & N/A; 0/1" in main
    assert "Existing programs + proofs & 1 & 1/1; 1/1 & N/A; 0/1" in main
    assert "not compared" not in main and "not checked" not in main
    assert "not compared" in details and "known difference" in details
    assert "math-proofs / ours & 0/1 & unknown & unknown & unknown & unknown & unknown 1/1" in details
    assert "math-proofs & 1 & 0 & 1 & 0 & 0" in details
    assert r"Tiny workload & \textbf{TODO} & \textbf{TODO}" in tables["composition-coverage.table.tex"]


@pytest.mark.parametrize(
    "proof_evidence",
    ("passed", "unknown", "failed", "missing-summary", "no-source-checks", "partial-certificates", "excluded"),
)
def test_composition_main_keeps_discoveries_pending_and_qualifies_source_proofs(proof_evidence: str) -> None:
    snapshot = snapshot_fixture()
    comparison = next(row for row in snapshot["comparisons"] if row["scope"] == "composition")
    comparison["label"] = "batax_2nd-44rules"
    validation = snapshot["conditions"][2]["validation"]
    if proof_evidence == "missing-summary":
        validation["summary"] = None
    elif proof_evidence == "no-source-checks":
        validation["summary"]["check_requests"] = 0
    elif proof_evidence == "partial-certificates":
        validation["summary"]["verified_certificates"] = 1
    else:
        validation["status"] = proof_evidence
    tables = pilot_results.coverage_tables(snapshot)
    main = tables["composition-coverage.table.tex"]
    marker = (
        r"\ding{51}"
        if proof_evidence == "passed"
        else "Excluded*"
        if proof_evidence == "excluded"
        else r"\textbf{TODO}"
    )
    assert r"BATAX / 2nd & \textbf{TODO} & " + marker in main
    assert "Overhead" not in main and "Executed" not in main
    assert "Overhead" in tables["composition-coverage-details.table.tex"]
    assert ("* Source-proof verification omitted for: BATAX / 2nd." in main) == (proof_evidence == "excluded")


def test_coverage_retains_reference_certificates_and_known_partial_counter_denominators() -> None:
    snapshot = snapshot_fixture()
    reference, proof = snapshot["conditions"][0], snapshot["conditions"][2]
    reference["treatment"] = "egg-proof-extraction"
    reference["validation"] = deepcopy(proof["validation"])
    proof["validation"]["status"] = "failed"
    proof["validation"]["summary"]["success"] = False
    proof["validation"]["summary"]["verified_certificates"] = 1
    tables = pilot_results.coverage_tables(snapshot)
    assert "math-proofs & 1 & 1/1; 1/1 & 1/1; 0/1" in tables["experiment-coverage.table.tex"]
    details = tables["experiment-coverage-details.table.tex"]
    assert "math-proofs / reference & 1/1 & 1 & 2 & 3 & 3 & passed 1/1" in details
    assert "math-proofs / ours & 1/1 & 1 & 2 & 3 & 1 & failed 1/1" in details
    assert "completed-prefix counters" in details
    unknown = deepcopy(proof)
    unknown["logical_id"] = "sha256:another-input"
    unknown["validation"] = {"status": "unknown", "issue": "no summary", "summary": None, "observation": None}
    partial = pilot_results._coverage_detail_row("partial / ours", [proof, unknown])
    assert "partial / ours & 1/2 & 1 & 2 & 3 & 1 & failed 1/2; unknown 1/2" in partial


def test_emitted_zero_counters_are_distinct_from_absent_summaries() -> None:
    snapshot = snapshot_fixture()
    proof = snapshot["conditions"][2]
    proof["validation"]["status"] = "failed"
    proof["validation"]["summary"] = {
        "schema_version": 1,
        "success": False,
        "check_requests": 0,
        "extraction_requests": 0,
        "produced_certificates": 0,
        "verified_certificates": 0,
    }
    detail = pilot_results.coverage_tables(snapshot)["experiment-coverage-details.table.tex"]
    assert "math-proofs / ours & 1/1 & 0 & 0 & 0 & 0 & failed 1/1" in detail
