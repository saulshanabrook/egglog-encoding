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
from benchmarking.reports.store import CacheKey, ReportStore

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
    rows = [{"status": "success", "wall_sec": wall, "max_rss_bytes": rss}] * 30
    assert selection.classify_baseline(rows).status == expected


def test_mean_not_every_run_and_failures_not_filtered() -> None:
    rows: list[dict[str, Any]] = [{"status": "success", "wall_sec": 0.05, "max_rss_bytes": 100}] * 29
    rows.append({"status": "success", "wall_sec": 3, "max_rss_bytes": 2 * 1024**3})
    assert selection.classify_baseline(rows).status == "selected"
    assert selection.classify_baseline(rows[:1]).status == "pending"
    rows[0] = {"status": "timed-out", "error_message": "timed out", "wall_sec": None, "max_rss_bytes": None}
    assert selection.classify_baseline(rows).status == "failed"


@pytest.mark.parametrize("strict_status", ["success", "failure"])
@pytest.mark.parametrize("treatment", admission.PROOF_TREATMENTS)
def test_independent_off_collection_proof_preparation_and_resume(
    prepared_environment: tuple[Path, models.ResolvedTarget],
    monkeypatch: pytest.MonkeyPatch,
    strict_status: str,
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

    def strict(_command: Any, _root: Path, prefix: Path, **_kwargs: Any) -> pilot.PilotProcessResult:
        calls.append("proof-testing")
        return pilot.PilotProcessResult(
            "success" if strict_status == "success" else "failure",
            0,
            0.1,
            100,
            prefix.with_suffix(".stdout"),
            prefix.with_suffix(".stderr"),
            None if strict_status == "success" else "invalid proof",
        )

    monkeypatch.setattr(collection, "run_process", measured)
    monkeypatch.setattr(selection, "preflight_collection", lambda *_args: None)
    monkeypatch.setattr(pilot, "run_bounded_command", strict)
    console = Console(file=io.StringIO())
    assert selection.run_baseline_campaign(suite, target, store, 120, console, baseline_only=True) is None
    assert calls == ["off"] * 29
    frozen = json.loads((root / selection.SELECTION_RELATIVE_PATH).read_text())
    assert frozen["baseline_complete"]
    assert frozen["workloads"][0]["aliases"] == ["one", "alias"]
    result = selection.run_baseline_campaign(suite, target, store, 120, console, treatment=treatment)
    assert result is not None and result.files == (file,)
    assert calls[:31] == ["off"] * 29 + [treatment, "proof-testing"]
    assert calls.count(treatment) == (30 if strict_status == "success" else 1)
    assert bool(result.validation_issues) == (strict_status == "failure")
    assert (root / selection.SELECTION_RELATIVE_PATH).read_text() == json.dumps(frozen, indent=2, sort_keys=True) + "\n"
    before = store.row_count
    count_calls = len(calls)
    selection.run_baseline_campaign(suite, target, store, 120, console, treatment=treatment)
    assert store.row_count == before and len(calls) == count_calls
    if strict_status == "failure":
        other: admission.ProofTreatment = "proofs" if treatment == "proof-extraction" else "proof-extraction"
        result = selection.run_baseline_campaign(suite, target, store, 120, console, treatment=other)
        assert result is not None and result.files == (file,)
        assert "proof-testing" in result.validation_issues[0][1]
        assert store.row_count == before and len(calls) == count_calls


@pytest.mark.parametrize("failed_treatment", [None, *admission.PROOF_TREATMENTS])
def test_two_modes_reuse_baseline_and_strict_validation_but_keep_failures_independent(
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
        assert bool(result.validation_issues) == (treatment == failed_treatment)
        content = (root / selection.SELECTION_RELATIVE_PATH).read_bytes()
        assert frozen is None or content == frozen
        frozen = content
    assert calls.count("off") == 30
    assert calls.count("proof-testing") == 1
    for treatment in treatments:
        assert calls.count(treatment) == (1 if treatment == failed_treatment else 30)
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
    assert calls.count("off") == calls.count("proofs") == 30
    assert calls.count("proof-testing") == 1 and "proof-extraction" not in calls
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
    assert calls == ["off"] * 30
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
    for index in range(30):
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
    assert snapshot["workloads"][0]["row_indices"] == list(range(30))
    assert not selection.selection_snapshot(suite, target, store, 121)["baseline_complete"]
    assert not selection.selection_snapshot(suite, replace(target, binary_sha256="new-binary"), store, 120)[
        "baseline_complete"
    ]
    for changed in (replace(file, sha256="new-input"), replace(file, fact_directory_sha256="new-facts")):
        changed_suite = replace(suite, files=(changed,))
        assert not selection.selection_snapshot(changed_suite, target, store, 120)["baseline_complete"]
    key = CacheKey.for_endpoint(models.BenchmarkEndpoint(target, "off"), file, 120)
    assert selection.classify_baseline([row.record for row in store.latest_records(key, 30)]).status == "selected"


def test_baseline_cli_is_opt_in_and_narrow() -> None:
    normal = benchmark.parse_benchmark_args([])
    assert not normal.baseline_window and not normal.baseline_only and normal.rounds == 6
    selected = benchmark.parse_benchmark_args(["--suite", "expanded", "--baseline-window", "--baseline-only"])
    assert selected.rounds == 30 and selected.compare_treatment == "off"
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
    assert launches == ["off"] * 30
    assert guards == ["1"] * 30
    assert not (root / selection.PILOT_RELATIVE_PATH).exists()


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
    assert launches == ["off"] * 30
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
    for i in range(30):
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
    assert launches == [("one.egg", "off")] * 30
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
    assert store.row_count == 60  # Historical helper rows remain intact.


@pytest.mark.parametrize("peak", [None, 0, -1, float("nan"), float("inf")])
def test_unavailable_memory_does_not_disqualify_complete_valid_time(peak: float | None) -> None:
    rows: list[dict[str, Any]] = [{"status": "success", "wall_sec": 1, "max_rss_bytes": 5 * 1024**3} for _ in range(30)]
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
        count = (30 if complete else 0) if name == "pending" else 1 if name == "failed" else 30
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
