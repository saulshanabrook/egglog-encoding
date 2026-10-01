"""Normal-mode selection must never condition membership on proof outcomes."""

from __future__ import annotations

import io
import json
from dataclasses import replace
from pathlib import Path
from typing import Any

import pytest
from rich.console import Console

from benchmarking import admission, benchmark, collection, models, pilot, processes, suites
from benchmarking import baseline_selection as selection
from benchmarking.reports.grouped import grouped_report_path
from benchmarking.reports.store import CacheKey, ReportStore, parse_grouped_report

from . import test_suite_preparation
from .report_fixtures import make_record, make_timing_summary

prepared_environment = test_suite_preparation.prepared_environment


@pytest.mark.parametrize(
    ("wall", "rss", "expected"),
    [
        (0.1, 1, "excluded"),
        (0.100001, 1, "selected"),
        (30, 1, "excluded"),
        (29.999, 1, "selected"),
        (1, 1024**3, "selected"),
        (1, 1024**3 - 1, "selected"),
        (None, 1, "failed"),
        (1, None, "selected"),
        (1, 0, "selected"),
        (float("nan"), 1, "failed"),
    ],
)
def test_time_only_mean_window_edges(wall: float | None, rss: int | None, expected: str) -> None:
    rows = [{"status": "success", "wall_sec": wall, "max_rss_bytes": rss}] * 10
    assert selection.classify_baseline(rows).status == expected


def test_mean_not_every_run_and_failures_not_filtered() -> None:
    rows: list[dict[str, Any]] = [{"status": "success", "wall_sec": 0.05, "max_rss_bytes": 100}] * 9
    rows.append({"status": "success", "wall_sec": 3, "max_rss_bytes": 2 * 1024**3})
    assert selection.classify_baseline(rows).status == "selected"
    assert selection.classify_baseline(rows[:1]).status == "pending"
    rows[0] = {"status": "timed-out", "error_message": "timed out", "wall_sec": None, "max_rss_bytes": None}
    assert selection.classify_baseline(rows).status == "failed"


@pytest.mark.parametrize("changed", [b'{"baseline_complete": false}\n', b'{"baseline_complete":'])
def test_selection_archive_rejects_changed_bytes_and_reuses_unchanged(tmp_path: Path, changed: bytes) -> None:
    path = tmp_path / "selection.json"
    snapshot = {"baseline_complete": True, "workloads": []}
    selection.write_selection_snapshot(path, snapshot)
    archive = next((tmp_path / "baseline-selections").glob("*.json"))
    assert archive.read_bytes() == path.read_bytes()
    before = {file: file.stat().st_mtime_ns for file in (path, archive)}
    selection.write_selection_snapshot(path, snapshot)
    assert before == {file: file.stat().st_mtime_ns for file in (path, archive)}

    archive.write_bytes(changed)
    with pytest.raises(ValueError, match="immutable baseline selection archive changed"):
        selection.write_selection_snapshot(path, snapshot)
    assert archive.read_bytes() == changed


@pytest.mark.parametrize("treatment", admission.PROOF_TREATMENTS)
def test_independent_off_collection_and_bulk_proof_collection_resume_without_validation(
    prepared_environment: tuple[Path, models.ResolvedTarget],
    monkeypatch: pytest.MonkeyPatch,
    treatment: admission.ProofTreatment,
) -> None:
    root, target = prepared_environment
    suite = suites.resolve_suite(("eggcc", "luminal"), root)
    file = suite.files[0]
    store = ReportStore(root / ".reports.jsonl")
    store.append(
        make_record(
            0,
            started_at="2026-01-01T00:00:00Z",
            binary_sha256=target.binary_sha256,
            file_sha256=file.sha256,
            wall_sec=0.2,
            max_rss_bytes=1000,
        )
    )
    calls: list[str] = []

    def measured(*args: Any) -> collection.ProcessObservation:
        calls.append(args[3])
        return collection.ProcessObservation(
            processes.TimingResult("success", processes.TimingRow(wall_sec=0.2, max_rss_bytes=1000), None),
            make_timing_summary(),
        )

    def strict(*_args: Any, **_kwargs: Any) -> None:
        pytest.fail("benchmark collection must not launch correctness validation")

    monkeypatch.setattr(collection, "run_process", measured)
    monkeypatch.setattr(selection, "preflight_collection", lambda *_args: None)
    monkeypatch.setattr(pilot, "run_bounded_command", strict)
    console = Console(file=io.StringIO())
    assert selection.run_baseline_campaign(suite, target, store, 120, console, baseline_only=True) is None
    assert calls == ["off"] * 9
    frozen = json.loads((root / selection.SELECTION_RELATIVE_PATH).read_text())
    assert frozen["baseline_complete"]
    assert frozen["workloads"][0]["aliases"] == ["one", "alias"]
    result = selection.run_baseline_campaign(suite, target, store, 120, console, treatment=treatment)
    assert result is not None and result.files == (file,)
    assert calls == ["off"] * 9 + [treatment] * 10
    assert not result.validation_issues
    assert not (root / admission.PILOT_RELATIVE_PATH).exists()
    assert (root / selection.SELECTION_RELATIVE_PATH).read_text() == json.dumps(frozen, indent=2, sort_keys=True) + "\n"
    before = store.row_count
    count_calls = len(calls)
    selection.run_baseline_campaign(suite, target, store, 120, console, treatment=treatment)
    assert store.row_count == before and len(calls) == count_calls


@pytest.mark.parametrize("failed_treatment", [None, *admission.PROOF_TREATMENTS])
def test_two_modes_reuse_baseline_and_keep_failures_independent_without_validation(
    prepared_environment: tuple[Path, models.ResolvedTarget],
    monkeypatch: pytest.MonkeyPatch,
    failed_treatment: admission.ProofTreatment | None,
) -> None:
    root, target = prepared_environment
    suite = suites.resolve_suite("expanded", root)
    store = ReportStore(root / "cache.jsonl")
    calls: list[str] = []

    def measured(*args: Any) -> collection.ProcessObservation:
        treatment = args[3]
        calls.append(treatment)
        if treatment == failed_treatment:
            return collection.ProcessObservation(
                processes.TimingResult("failure", processes.TimingRow(), processes.ErrorRow("mode failed")), None
            )
        return collection.ProcessObservation(
            processes.TimingResult("success", processes.TimingRow(wall_sec=0.2, max_rss_bytes=1000), None),
            make_timing_summary(),
        )

    def strict(_command: Any, _root: Path, prefix: Path, **_kwargs: Any) -> pilot.PilotProcessResult:
        calls.append("proof-testing")
        return pilot.PilotProcessResult("success", 0, 0.1, 100, prefix, prefix, None)

    monkeypatch.setattr(collection, "run_process", measured)
    monkeypatch.setattr(selection, "preflight_collection", lambda *_args: None)
    monkeypatch.setattr(pilot, "run_bounded_command", strict)
    console = Console(file=io.StringIO())
    # Exercise the failed mode first, so its pilot record must not block the other.
    treatments = sorted(admission.PROOF_TREATMENTS, key=lambda mode: mode != failed_treatment)
    frozen = None
    for treatment in treatments:
        result = selection.run_baseline_campaign(suite, target, store, 120, console, treatment=treatment)
        assert result is not None and result.files == suite.files
        assert result.candidate.treatment == treatment
        assert not result.validation_issues  # Fresh failures live in the measured rows.
        content = (root / selection.SELECTION_RELATIVE_PATH).read_bytes()
        assert frozen is None or content == frozen
        frozen = content
    assert calls.count("off") == 10
    assert calls.count("proof-testing") == 0
    for treatment in treatments:
        assert calls.count(treatment) == (1 if treatment == failed_treatment else 10)
    before = store.path.read_bytes(), list(calls)
    for treatment in treatments:
        selection.run_baseline_campaign(suite, target, store, 120, console, treatment=treatment)
    assert (store.path.read_bytes(), calls) == before

    coverage = suites.build_coverage(
        suite, root / admission.PILOT_RELATIVE_PATH, {"egglog": target.binary_sha256}, store.records
    )
    outcomes = coverage["cases"][0]["workloads"][0]["preparation_by_treatment"]
    assert {mode: outcome["status"] for mode, outcome in outcomes.items()} == {
        mode: "proof-error" if mode == failed_treatment else "ready" for mode in admission.PROOF_TREATMENTS
    }


def test_recording_cli_collects_only_its_requested_candidate(
    prepared_environment: tuple[Path, models.ResolvedTarget],
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    root, target = prepared_environment
    calls: list[str] = []

    def measured(*args: Any) -> collection.ProcessObservation:
        calls.append(args[3])
        return collection.ProcessObservation(
            processes.TimingResult("success", processes.TimingRow(wall_sec=0.2, max_rss_bytes=1000), None),
            make_timing_summary(),
        )

    def strict(_command: Any, _root: Path, prefix: Path, **_kwargs: Any) -> pilot.PilotProcessResult:
        calls.append("proof-testing")
        return pilot.PilotProcessResult("success", 0, 0.1, 100, prefix, prefix, None)

    monkeypatch.setattr(collection, "run_process", measured)
    monkeypatch.setattr(selection, "preflight_collection", lambda *_args: None)
    monkeypatch.setattr(pilot, "run_bounded_command", strict)
    monkeypatch.setattr(benchmark, "resolve_targets", lambda groups, *_args: {groups[0][0]: target})
    assert benchmark.main(["--suite", "expanded", "--baseline-window", "--target", ".", "--treatment", "proofs"]) == 0
    assert calls.count("off") == calls.count("proofs") == 10
    assert calls.count("proof-testing") == 0 and "proof-extraction" not in calls
    assert {row["treatment"] for row in ReportStore(root / ".reports.jsonl").records} == {"off", "proofs"}


def test_cached_proof_error_does_not_block_baseline_or_membership(
    prepared_environment: tuple[Path, models.ResolvedTarget], monkeypatch: pytest.MonkeyPatch
) -> None:
    root, target = prepared_environment
    suite = suites.resolve_suite("eggcc", root)
    file = suite.files[0]
    store = ReportStore(root / "cache.jsonl")
    store.append(
        make_record(
            0,
            started_at="2026-01-01T00:00:00Z",
            binary_sha256=target.binary_sha256,
            file_sha256=file.sha256,
            status="failure",
            treatment="proof-extraction",
        )
    )
    calls: list[str] = []

    def measured(*args: Any) -> collection.ProcessObservation:
        calls.append(args[3])
        return collection.ProcessObservation(
            processes.TimingResult("success", processes.TimingRow(wall_sec=0.2, max_rss_bytes=1000), None),
            make_timing_summary(),
        )

    monkeypatch.setattr(collection, "run_process", measured)
    monkeypatch.setattr(selection, "preflight_collection", lambda *_args: None)
    result = selection.run_baseline_campaign(suite, target, store, 120, Console(file=io.StringIO()))
    assert calls == ["off"] * 10
    assert result is not None and result.files == (file,) and len(result.validation_issues) == 1
    assert "proof-extraction" in result.validation_issues[0][1]


@pytest.mark.parametrize("guard_stop", [False, True])
def test_fresh_normal_failure_and_guard_stop_preserve_observation(
    prepared_environment: tuple[Path, models.ResolvedTarget], monkeypatch: pytest.MonkeyPatch, guard_stop: bool
) -> None:
    root, target = prepared_environment
    suite = suites.resolve_suite("eggcc", root)
    store = ReportStore(root / "cache.jsonl")
    calls: list[str] = []

    def measured(*args: Any) -> collection.ProcessObservation:
        calls.append(args[3])
        return collection.ProcessObservation(
            processes.TimingResult(
                "failure",
                processes.TimingRow(),
                processes.ErrorRow("resource guard: host pressure" if guard_stop else "unsupported operation"),
                resource_stopped=guard_stop,
            ),
            None,
        )

    monkeypatch.setattr(collection, "run_process", measured)
    monkeypatch.setattr(selection, "preflight_collection", lambda *_args: None)
    console = Console(file=io.StringIO())
    if guard_stop:
        with pytest.raises(ValueError, match="failed observation was retained"):
            selection.run_baseline_campaign(suite, target, store, 120, console)
    else:
        assert selection.run_baseline_campaign(suite, target, store, 120, console) is None
    assert calls == ["off"] and store.row_count == 1
    manifest = json.loads((root / selection.SELECTION_RELATIVE_PATH).read_text())
    assert manifest["workloads"][0]["baseline"]["status"] == "failed"
    selection.run_baseline_campaign(suite, target, store, 120, console)
    assert calls == ["off"]


def test_snapshot_uses_exact_current_identity_and_samples(
    prepared_environment: tuple[Path, models.ResolvedTarget],
) -> None:
    root, target = prepared_environment
    suite = suites.resolve_suite("eggcc", root)
    file = suite.files[0]
    store = ReportStore(root / "cache.jsonl")
    for index in range(10):
        store.append(
            make_record(
                index,
                started_at="2026-01-01T00:00:00Z",
                binary_sha256=target.binary_sha256,
                file_sha256=file.sha256,
                wall_sec=0.2,
                max_rss_bytes=1000,
                target_label="old",
            )
        )
    snapshot = selection.selection_snapshot(suite, target, store, 120)
    assert snapshot["workloads"][0]["baseline"]["status"] == "selected"
    assert snapshot["workloads"][0]["row_indices"] == list(range(10))
    assert not selection.selection_snapshot(suite, target, store, 121)["baseline_complete"]
    assert not selection.selection_snapshot(suite, replace(target, binary_sha256="new-binary"), store, 120)[
        "baseline_complete"
    ]
    for changed in (replace(file, sha256="new-input"), replace(file, fact_directory_sha256="new-facts")):
        changed_suite = replace(suite, files=(changed,))
        assert not selection.selection_snapshot(changed_suite, target, store, 120)["baseline_complete"]
    key = CacheKey.for_endpoint(models.BenchmarkEndpoint(target, "off"), file, 120)
    assert selection.classify_baseline([row.record for row in store.latest_records(key, 10)]).status == "selected"


def test_baseline_cli_is_opt_in_and_narrow() -> None:
    normal = benchmark.parse_benchmark_args([])
    assert not normal.baseline_window and not normal.baseline_only and normal.rounds == 6
    selected = benchmark.parse_benchmark_args(["--suite", "expanded", "--baseline-window", "--baseline-only"])
    assert selected.rounds == 10 and selected.compare_treatment == "off"
    for treatment in admission.PROOF_TREATMENTS:
        selected = benchmark.parse_benchmark_args(
            ["--suite", "expanded", "--baseline-window", "--treatment", treatment]
        )
        assert selected.treatment == treatment and selected.compare_treatment == "off"
    for args in (
        ["--baseline-window"],
        ["--baseline-only"],
        ["--suite", "eggcc", "--baseline-window", "--rounds", "1"],
        ["--suite", "eggcc", "--baseline-window", "--force-run"],
        ["--suite", "eggcc", "--baseline-window", "--treatment", "proof-testing"],
    ):
        with pytest.raises(SystemExit):
            benchmark.parse_benchmark_args(args)


def test_cli_runs_all_normal_samples_before_any_proof(
    prepared_environment: tuple[Path, models.ResolvedTarget], monkeypatch: pytest.MonkeyPatch
) -> None:
    root, target = prepared_environment
    launches: list[str] = []
    guards: list[str | None] = []

    def measured(*args: Any) -> collection.ProcessObservation:
        import os

        guards.append(os.environ.get("EGGLOG_BENCH_MEMORY_GUARD"))
        launches.append(args[3])
        return collection.ProcessObservation(
            processes.TimingResult("success", processes.TimingRow(wall_sec=0.2, max_rss_bytes=1000), None),
            make_timing_summary(),
        )

    monkeypatch.setattr(collection, "run_process", measured)
    monkeypatch.setattr(selection, "preflight_collection", lambda *_args: None)
    monkeypatch.setattr(benchmark, "resolve_targets", lambda groups, *_args: {groups[0][0]: target})
    assert benchmark.main(["--suite", "expanded", "--baseline-window", "--baseline-only", "--target", "."]) == 0
    assert launches == ["off"] * 10
    report = root / ".reports.jsonl"
    snapshot = parse_grouped_report(grouped_report_path(report).read_bytes(), str(report))
    assert len(snapshot.records) == 10
    assert {row["treatment"] for row in snapshot.records} == {"off"}
    assert guards == ["1"] * 10
    assert not (root / admission.PILOT_RELATIVE_PATH).exists()


def test_guard_halts_before_second_normal_workload(
    prepared_environment: tuple[Path, models.ResolvedTarget], monkeypatch: pytest.MonkeyPatch
) -> None:
    root, target = prepared_environment
    path = root / "benchmarks/catalog.json"
    catalog = json.loads(path.read_text())
    (root / "two.egg").write_text("(check (= 2 2))\n")
    catalog["cases"].append(
        {"id": "two", "family": "eggcc", "source": "two", "status": "captured", "workloads": ["two.egg"]}
    )
    path.write_text(json.dumps(catalog))
    suite = suites.resolve_suite("eggcc", root)
    store = ReportStore(root / "cache.jsonl")
    launches: list[str] = []

    def measured(*args: Any) -> collection.ProcessObservation:
        launches.append(args[2].display_path)
        return collection.ProcessObservation(
            processes.TimingResult(
                "failure",
                processes.TimingRow(),
                processes.ErrorRow("resource guard: host pressure"),
                resource_stopped=True,
            ),
            None,
        )

    monkeypatch.setattr(collection, "run_process", measured)
    monkeypatch.setattr(selection, "preflight_collection", lambda *_args: None)
    with pytest.raises(ValueError, match="failed observation was retained"):
        selection.run_baseline_campaign(suite, target, store, 120, Console(file=io.StringIO()))
    assert launches == ["one.egg"] and store.row_count == 1
    snapshot = json.loads((root / selection.SELECTION_RELATIVE_PATH).read_text())
    assert not snapshot["baseline_complete"]
    assert [row["baseline"]["status"] for row in snapshot["workloads"]] == ["failed", "pending"]


def test_normal_only_captures_enter_cohort_but_cannot_launch_proofs(
    prepared_environment: tuple[Path, models.ResolvedTarget], monkeypatch: pytest.MonkeyPatch
) -> None:
    root, target = prepared_environment
    path = root / "benchmarks/catalog.json"
    catalog = json.loads(path.read_text())
    (root / "normal.egg").write_text("(let x 1)\n")
    catalog["cases"] = [
        {
            "id": "one",
            "family": "dialegg",
            "source": "one",
            "status": "captured",
            "workloads": [],
            "normal_workloads": [
                {"path": "normal.egg", "proof_blocker": "derived query requires collections", "invocation": 0}
            ],
            "benchmark_selection": {"workloads": ["normal.egg"], "reason": "Complete source computation"},
        }
    ]
    path.write_text(json.dumps(catalog))
    suite = suites.resolve_suite("expanded", root, include_normal_only=True)
    store = ReportStore(root / "cache.jsonl")
    launches: list[str] = []

    def measured(*args: Any) -> collection.ProcessObservation:
        launches.append(args[3])
        return collection.ProcessObservation(
            processes.TimingResult("success", processes.TimingRow(wall_sec=0.2, max_rss_bytes=1000), None),
            make_timing_summary(),
        )

    monkeypatch.setattr(collection, "run_process", measured)
    monkeypatch.setattr(selection, "preflight_collection", lambda *_args: None)
    result = selection.run_baseline_campaign(suite, target, store, 120, Console(file=io.StringIO()))
    assert launches == ["off"] * 10
    assert result is not None and result.files == suite.files
    assert result.validation_issues == ((suite.files[0], "derived query requires collections"),)
    snapshot = json.loads((root / selection.SELECTION_RELATIVE_PATH).read_text())
    assert snapshot["workloads"][0]["baseline"]["status"] == "selected"
    assert snapshot["workloads"][0]["proof_query_blocked"] == "derived query requires collections"


def test_source_omissions_never_enter_cached_cohort_or_collection(
    prepared_environment: tuple[Path, models.ResolvedTarget], monkeypatch: pytest.MonkeyPatch
) -> None:
    root, target = prepared_environment
    path = root / "benchmarks/catalog.json"
    catalog = json.loads(path.read_text())
    catalog["cases"] = catalog["cases"][:1]
    (root / "helper.egg").write_text("(let x 1)\n")
    case = catalog["cases"][0]
    case["workloads"].append("helper.egg")
    path.write_text(json.dumps(catalog))
    original = suites.resolve_suite("eggcc", root)
    store = ReportStore(root / "cache.jsonl")
    helper = original.files[1]
    for i in range(10):
        store.append(
            make_record(
                i,
                started_at="2026-09-24T00:00:00Z",
                binary_sha256=target.binary_sha256,
                file_sha256=helper.sha256,
                wall_sec=0.2,
                max_rss_bytes=1000,
            )
        )
    case["benchmark_selection"] = {"workloads": ["one.egg"], "reason": "Skip setup-only calls"}
    path.write_text(json.dumps(catalog))
    suite = suites.resolve_suite("eggcc", root, include_normal_only=True)
    launches = []

    def measured(*args: Any) -> collection.ProcessObservation:
        launches.append((args[2].display_path, args[3]))
        return collection.ProcessObservation(
            processes.TimingResult("success", processes.TimingRow(wall_sec=0.2, max_rss_bytes=1000), None),
            make_timing_summary(),
        )

    monkeypatch.setattr(collection, "run_process", measured)
    monkeypatch.setattr(selection, "preflight_collection", lambda *_args: None)
    selection.run_baseline_campaign(suite, target, store, 120, Console(file=io.StringIO()), baseline_only=True)
    assert launches == [("one.egg", "off")] * 10
    snapshot = json.loads((root / selection.SELECTION_RELATIVE_PATH).read_text())
    assert [entry["file_path"] for entry in snapshot["workloads"]] == ["one.egg"]
    assert snapshot["source_exclusions"] == [
        {
            "id": "one",
            "family": "eggcc",
            "workloads": ["helper.egg"],
            "reason": "Skip setup-only calls",
        }
    ]
    assert store.row_count == 20  # Historical helper rows remain intact.


@pytest.mark.parametrize("peak", [None, 0, -1, float("nan"), float("inf")])
def test_unavailable_memory_does_not_disqualify_complete_valid_time(peak: float | None) -> None:
    rows: list[dict[str, Any]] = [{"status": "success", "wall_sec": 1, "max_rss_bytes": 5 * 1024**3} for _ in range(10)]
    rows[-1]["max_rss_bytes"] = peak
    result = selection.classify_baseline(rows)
    assert result.status == "selected"
    assert result.mean_wall_sec == 1 and result.mean_peak_rss_bytes is None
    del rows[-1]["max_rss_bytes"]
    assert selection.classify_baseline(rows).status == "selected"
    assert selection.classify_baseline(rows).mean_peak_rss_bytes is None


@pytest.mark.parametrize("complete", [False, True])
@pytest.mark.parametrize("width", [80, 120])
def test_family_counts_deduplicate_aliases_and_report_pending_without_final_exclusion_counts(
    prepared_environment: tuple[Path, models.ResolvedTarget],
    monkeypatch: pytest.MonkeyPatch,
    complete: bool,
    width: int,
) -> None:
    root, target = prepared_environment
    path = root / "benchmarks/catalog.json"
    catalog = json.loads(path.read_text())
    catalog["cases"].append(
        {
            "id": "same-family-alias",
            "family": "eggcc",
            "source": "alias",
            "status": "captured",
            "workloads": ["one.egg"],
        }
    )
    for index, name in enumerate(("fast", "slow", "pending", "failed"), 2):
        (root / f"{name}.egg").write_text(f"(check (= {index} {index}))\n")
        catalog["cases"].append(
            {"id": name, "family": "eggcc", "source": name, "status": "captured", "workloads": [f"{name}.egg"]}
        )
    path.write_text(json.dumps(catalog))
    suite = suites.resolve_suite("expanded", root)
    store = ReportStore(root / "cache.jsonl")
    for file in suite.files:
        name = Path(file.display_path).stem
        count = (10 if complete else 0) if name == "pending" else 1 if name == "failed" else 10
        for index in range(count):
            store.append(
                make_record(
                    index,
                    started_at="2026-01-01T00:00:00Z",
                    binary_sha256=target.binary_sha256,
                    file_sha256=file.sha256,
                    status="failure" if name == "failed" else "success",
                    wall_sec={"fast": 0.1, "slow": 30}.get(name, 1),
                    max_rss_bytes=5 * 1024**3,
                )
            )
    expected = {
        "selected": 2 if complete else 1,
        "too_fast": 1,
        "too_slow": 1,
        "pending": 0 if complete else 1,
        "failed": 1,
    }
    snapshot = selection.selection_snapshot(suite, target, store, 120)
    assert snapshot["counts"] == snapshot["family_counts"]["eggcc"] == expected
    assert snapshot["family_counts"]["luminal"] == {
        "selected": 1,
        "too_fast": 0,
        "too_slow": 0,
        "pending": 0,
        "failed": 0,
    }
    assert snapshot["workloads"][0]["aliases"] == ["one", "alias", "same-family-alias"]
    assert snapshot["workloads"][0]["families"] == ["eggcc", "luminal"]
    assert "max_mean_peak_rss_bytes_exclusive" not in snapshot["policy"]
    assert snapshot["baseline_complete"] is complete

    def preflight(_plan: Any, _timeout: int) -> None:
        if not complete:
            raise ValueError("resource guard before pending observations")

    def unexpected_run(*_args: Any) -> None:
        raise AssertionError("summary of cached or interrupted collection must not launch an engine")

    monkeypatch.setattr(selection, "preflight_collection", preflight)
    monkeypatch.setattr(collection, "run_process", unexpected_run)
    stream = io.StringIO()
    console = Console(file=stream, width=width)
    if complete:
        selection.run_baseline_campaign(suite, target, store, 120, console, baseline_only=True)
    else:
        with pytest.raises(ValueError, match="resource guard before pending"):
            selection.run_baseline_campaign(suite, target, store, 120, console, baseline_only=True)
    saved = json.loads((root / selection.SELECTION_RELATIVE_PATH).read_text())
    assert saved == snapshot
    output = stream.getvalue()
    assert "Too fast" in output and "Too slow" in output and "Pending" in output and "Failed" in output
    assert "Total (unique)" in output and "Shared workloads count once in each family" in output
    assert ("so far" in output) is not complete
    assert ("provisional" in output) is not complete


def test_math_campaign_does_not_build_egg_or_launch_parity_checks(
    prepared_environment: tuple[Path, models.ResolvedTarget], monkeypatch: pytest.MonkeyPatch
) -> None:
    from benchmarking import math_workloads

    root, target = prepared_environment
    target = replace(target, row=replace(target.row, path=str(root)))
    catalog_path = root / "benchmarks/catalog.json"
    catalog = json.loads(catalog_path.read_text())
    catalog["families"] = {"math-growth": {}}
    catalog["cases"] = [{**catalog["cases"][0], "id": "math-growth-011", "family": "math-growth"}]
    catalog_path.write_text(json.dumps(catalog))
    suite = suites.resolve_suite("expanded", root)
    calls: list[str] = []

    def measured(*args: Any) -> collection.ProcessObservation:
        calls.append(args[3])
        return collection.ProcessObservation(
            processes.TimingResult("success", processes.TimingRow(wall_sec=0.2, max_rss_bytes=1000), None),
            make_timing_summary(),
        )

    def unexpected(*_args: Any, **_kwargs: Any) -> None:
        pytest.fail("Math benchmarks must not build an unused engine or run correctness checks")

    monkeypatch.setattr(pilot, "build_target", unexpected)
    monkeypatch.setattr(selection, "preflight_collection", lambda *_args: None)
    monkeypatch.setattr(collection, "run_process", measured)
    monkeypatch.setattr(pilot, "run_bounded_command", unexpected)
    monkeypatch.setattr(math_workloads, "validate_math_workload", unexpected)
    report = root / "cache.jsonl"
    console = Console(file=io.StringIO())
    for treatment in admission.PROOF_TREATMENTS:
        result = selection.run_baseline_campaign(suite, target, ReportStore(report), 300, console, treatment=treatment)
        assert result is not None and not result.validation_issues
    assert calls == ["off"] * 10 + ["proofs"] * 10 + ["proof-extraction"] * 10
    assert not (root / admission.PILOT_RELATIVE_PATH).exists()
    assert not (root / "target/release/egg-math-benchmark").exists()
    original = report.read_bytes()
    before = list(calls)
    for treatment in admission.PROOF_TREATMENTS:
        selection.run_baseline_campaign(suite, target, ReportStore(report), 300, console, treatment=treatment)
    assert report.read_bytes() == original and calls == before


@pytest.mark.parametrize("failure", [None, "ordinary", "guard"])
def test_selected_workloads_share_one_round_robin_plan_and_stop_failures(
    prepared_environment: tuple[Path, models.ResolvedTarget],
    monkeypatch: pytest.MonkeyPatch,
    failure: str | None,
) -> None:
    root, target = prepared_environment
    (root / "two.egg").write_text("(check (= 2 2))\n")
    catalog_path = root / "benchmarks/catalog.json"
    catalog = json.loads(catalog_path.read_text())
    catalog["cases"][1]["workloads"] = ["two.egg"]
    catalog_path.write_text(json.dumps(catalog))
    suite = suites.resolve_suite("expanded", root)
    store = ReportStore(root / "cache.jsonl")
    plans: list[collection.CollectionPlan] = []
    calls: list[tuple[str, str]] = []
    collect = selection.collect_rows

    def collect_plan(*args: Any) -> None:
        plans.append(args[1])
        collect(*args)

    def measured(
        _binary: Path, _root: Path, file: models.FileSpec, treatment: str, _timeout: int, _encoding: str
    ) -> collection.ProcessObservation:
        calls.append((file.display_path, treatment))
        if treatment == "proofs" and file == suite.files[0] and failure:
            return collection.ProcessObservation(
                processes.TimingResult(
                    "failure",
                    processes.TimingRow(),
                    processes.ErrorRow("resource guard: host pressure" if failure == "guard" else "mode failed"),
                    resource_stopped=failure == "guard",
                ),
                None,
            )
        return collection.ProcessObservation(
            processes.TimingResult("success", processes.TimingRow(wall_sec=0.2), None), make_timing_summary()
        )

    monkeypatch.setattr(collection, "run_process", measured)
    monkeypatch.setattr(selection, "collect_rows", collect_plan)
    monkeypatch.setattr(selection, "preflight_collection", lambda *_args: None)
    console = Console(file=io.StringIO())
    if failure == "guard":
        with pytest.raises(ValueError, match="failed observation was retained"):
            selection.run_baseline_campaign(suite, target, store, 120, console, treatment="proofs")
    else:
        selection.run_baseline_campaign(suite, target, store, 120, console, treatment="proofs")
    assert len(plans) == 2
    assert all(len(plan.runs) == 2 and all(run.required_rows == 10 for run in plan.runs) for plan in plans)
    expected = [("one.egg", "off"), ("two.egg", "off")] * 10
    if failure == "guard":
        expected += [("one.egg", "proofs")]
    elif failure == "ordinary":
        expected += [("one.egg", "proofs")] + [("two.egg", "proofs")] * 10
    else:
        expected += [("one.egg", "proofs"), ("two.egg", "proofs")] * 10
    assert calls == expected
    assert not (root / admission.PILOT_RELATIVE_PATH).exists()


def test_known_strict_failure_stays_explicit_without_rerunning_validation(
    prepared_environment: tuple[Path, models.ResolvedTarget], monkeypatch: pytest.MonkeyPatch
) -> None:
    root, target = prepared_environment
    suite = suites.resolve_suite("eggcc", root)
    file = suite.files[0]
    store = ReportStore(root / "cache.jsonl")
    for index in range(10):
        store.append(
            make_record(
                index,
                started_at="2026-01-01T00:00:00Z",
                binary_sha256=target.binary_sha256,
                file_sha256=file.sha256,
                wall_sec=0.2,
            )
        )
    evidence = root / admission.PILOT_RELATIVE_PATH
    evidence.parent.mkdir(parents=True, exist_ok=True)
    evidence.write_text(
        json.dumps(
            {
                "identity": admission.pilot_identity(
                    file, "eggcc", {"egglog": target.binary_sha256}, admission.PilotPolicy(), root
                ),
                "status": "failure",
                "reason": "proof-testing: invalid proof",
            }
        )
        + "\n"
    )
    previous = evidence.read_bytes(), store.path.read_bytes()
    monkeypatch.setattr(selection, "preflight_collection", lambda *_args: None)
    monkeypatch.setattr(collection, "run_process", lambda *_args: pytest.fail("known invalid program must not rerun"))
    monkeypatch.setattr(
        pilot, "run_bounded_command", lambda *_args, **_kwargs: pytest.fail("validation belongs in tests")
    )
    result = selection.run_baseline_campaign(suite, target, store, 120, Console(file=io.StringIO()), treatment="proofs")
    assert result is not None and result.validation_issues == ((file, "proof-testing: invalid proof"),)
    assert (evidence.read_bytes(), store.path.read_bytes()) == previous


@pytest.mark.parametrize("cached", [3, 10, 30])
def test_ten_run_campaign_reuses_samples_and_tops_up_only_missing(
    prepared_environment: tuple[Path, models.ResolvedTarget], monkeypatch: pytest.MonkeyPatch, cached: int
) -> None:
    root, target = prepared_environment
    suite = suites.resolve_suite("eggcc", root)
    file = suite.files[0]
    store = ReportStore(root / "cache.jsonl")
    for treatment in ("off", "proofs"):
        for index in range(cached):
            store.append(
                make_record(
                    index,
                    started_at="2026-01-01T00:00:00Z",
                    treatment=treatment,
                    binary_sha256=target.binary_sha256,
                    file_sha256=file.sha256,
                    wall_sec=0.2,
                )
            )
    calls = []

    def measured(*args: Any) -> collection.ProcessObservation:
        calls.append(args[3])
        return collection.ProcessObservation(
            processes.TimingResult("success", processes.TimingRow(wall_sec=0.2), None), make_timing_summary()
        )

    monkeypatch.setattr(collection, "run_process", measured)
    monkeypatch.setattr(selection, "preflight_collection", lambda *_args: None)
    result = selection.run_baseline_campaign(suite, target, store, 120, Console(file=io.StringIO()), treatment="proofs")
    assert result is not None and result.rounds == 10
    missing = max(0, 10 - cached)
    assert calls == ["off"] * missing + ["proofs"] * missing
    assert store.row_count == 2 * max(10, cached)
    snapshot = json.loads((root / selection.SELECTION_RELATIVE_PATH).read_text())
    assert snapshot["policy"]["rounds"] == 10
    assert len(snapshot["workloads"][0]["row_indices"]) == 10


def test_ten_run_cohort_uses_latest_ten_but_keeps_prior_failure(
    prepared_environment: tuple[Path, models.ResolvedTarget],
) -> None:
    root, target = prepared_environment
    suite = suites.resolve_suite("eggcc", root)
    file = suite.files[0]
    store = ReportStore(root / "cache.jsonl")
    for index in range(30):
        store.append(
            make_record(
                index,
                started_at="2026-01-01T00:00:00Z",
                binary_sha256=target.binary_sha256,
                file_sha256=file.sha256,
                wall_sec=0.2 if index < 20 else 0.05,
            )
        )
    snapshot = selection.selection_snapshot(suite, target, store, 120)
    assert snapshot["workloads"][0]["baseline"]["status"] == "excluded"
    assert snapshot["workloads"][0]["row_indices"] == list(range(20, 30))
    # A failure just outside the new sample remains terminal in the old30 window.
    store.append(
        make_record(
            30,
            started_at="2026-01-01T00:00:00Z",
            binary_sha256=target.binary_sha256,
            file_sha256=file.sha256,
            status="failure",
        )
    )
    for index in range(31, 41):
        store.append(
            make_record(
                index,
                started_at="2026-01-01T00:00:00Z",
                binary_sha256=target.binary_sha256,
                file_sha256=file.sha256,
                wall_sec=0.2,
            )
        )
    snapshot = selection.selection_snapshot(suite, target, store, 120)
    assert snapshot["workloads"][0]["baseline"]["status"] == "failed"
    assert "failure" in snapshot["workloads"][0]["baseline"]["reason"]
