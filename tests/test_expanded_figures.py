"""Preserve unready Math observations and mark them unavailable for plotting."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest

from benchmarking import admission, suites
from benchmarking.baseline_selection import classify_baseline
from benchmarking.engines import TREATMENT_SPECS
from benchmarking.memory_guard import GROUP_LIMIT_BYTES
from benchmarking.reports.store import ReportRecord
from benchmarking.targets import sha256_file
from figures.prepare import ENDPOINTS, OVERHEAD_ENDPOINTS
from figures.prepare_expanded import prepare_expanded

from .report_fixtures import ROOT, make_record


@pytest.mark.parametrize("rejected_pilot", ["failed", "extraction-failed", "stale", "memory", "historical-memory"])
def test_unavailable_math_preserves_cached_rows_provenance_and_concise_reasons(
    tmp_path: Path, rejected_pilot: str, monkeypatch: pytest.MonkeyPatch
) -> None:
    if rejected_pilot in ("memory", "historical-memory"):
        monkeypatch.setenv("EGGLOG_BENCH_MEMORY_GUARD", "1")
    release = tmp_path / "target/release"
    release.mkdir(parents=True)
    binaries = {"egglog": "egglog-experimental", "egg": "egg-math-benchmark"}
    for name in binaries.values():
        (release / name).write_text(name)
    hashes = {engine: sha256_file(release / name) for engine, name in binaries.items()}
    cases = []
    for cutoff in range(1, 12):
        relative = f"benchmarks/math/math-{cutoff:02}.egg"
        destination = tmp_path / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        source = ROOT / ("egglog-experimental/tests/math-microbenchmark-rational.egg" if cutoff == 11 else relative)
        destination.write_bytes(source.read_bytes())
        cases.append(
            {
                "id": f"math-growth-{cutoff:03}",
                "family": "math-growth",
                "source": f"artifact Math cutoff {cutoff}",
                "status": "captured",
                "workloads": [relative],
            }
        )
    (tmp_path / "benchmarks/catalog.json").write_text(json.dumps({"families": {"math-growth": {}}, "cases": cases}))
    selection = suites.resolve_suite("expanded", tmp_path)
    failure_reason = "proof-testing: thread panicked while checking a proof\n" + "long diagnostic\n" * 300
    pilots = []
    measurements: list[ReportRecord] = []
    for cutoff, file in enumerate(selection.files, 1):
        identity = admission.pilot_identity(file, "math-growth", hashes, admission.PilotPolicy(), tmp_path)
        if cutoff == 6 and rejected_pilot in ("stale", "historical-memory"):
            identity["binary_hashes"] = {"egglog": "sha256:old-egglog", "egg": hashes["egg"]}
        pilots.append(
            {
                "identity": identity,
                "status": "failure" if cutoff == 6 and rejected_pilot == "failed" else "admitted",
                "reason": failure_reason if cutoff == 6 and rejected_pilot == "failed" else None,
                "checks": [{"peak_rss_bytes": GROUP_LIMIT_BYTES + 1}]
                if cutoff == 6 and rejected_pilot in ("memory", "historical-memory")
                else [],
            }
        )
        for _engine, _proof_mode, treatment in (*ENDPOINTS, OVERHEAD_ENDPOINTS[1]):
            measurements.extend(
                make_record(
                    round_index,
                    started_at="2026-09-21T00:00:00Z",
                    file_sha256=file.sha256,
                    binary_sha256=hashes[TREATMENT_SPECS[treatment].engine],
                    treatment=treatment,
                    max_rss_bytes=None if round_index == 1 else (round_index + 1) * 1024**2,
                )
                for round_index in range(30)
            )
            if cutoff == 6 and rejected_pilot == "extraction-failed" and treatment == "proof-extraction":
                measurements[-30].update(
                    {"status": "failure", "error_exit_code": 17, "error_message": "proof extraction failed"}
                )
    evidence = tmp_path / admission.PILOT_RELATIVE_PATH
    evidence.parent.mkdir(parents=True)
    evidence.write_text("".join(json.dumps(row) + "\n" for row in pilots))
    report = tmp_path / ".reports.jsonl"
    report.write_text("".join(json.dumps(row) + "\n" for row in measurements))
    original_cache = report.read_bytes()

    prepare_expanded(tmp_path)

    for relative, expected_conditions in (
        ("figures/expanded/math-growth.data.json", 4),
        ("figures/expanded/math-growth/proof-overhead.data.json", 3),
    ):
        data = json.loads((tmp_path / relative).read_text())
        groups = data["groups"]
        assert len(groups) == 11 * expected_conditions
        assert {group["workload"] for group in groups} == {case["id"] for case in cases}
        for group in groups:
            cutoff = int(group["workload"].rsplit("-", 1)[1])
            assert len(group["observations"]) == 30
            for observation in group["observations"]:
                assert observation["max_rss_bytes"] == measurements[observation["row_index"]]["max_rss_bytes"]
            unavailable = cutoff == 6 and (
                relative.endswith("math-growth.data.json")
                or group["treatment"] != "off"
                and (rejected_pilot != "extraction-failed" or group["treatment"] == "proof-extraction")
            )
            if unavailable:
                assert 0 < len(group["unavailable_reason"]) < 80
                for observation in group["observations"]:
                    source = data["sources"][observation["source_index"]]
                    original = measurements[observation["row_index"]]
                    assert observation["status"] == original["status"]
                    assert observation["wall_sec"] == original["wall_sec"]
                    assert source["file_path"] == original["file_path"]
                    assert source["target_git_sha"] == original["target_git_sha"]
                if rejected_pilot == "extraction-failed" and group["treatment"] == "proof-extraction":
                    assert group["observations"][0]["error_exit_code"] == 17
                    assert group["observations"][0]["error_message"] == "proof extraction failed"
                    assert group["unavailable_reason"] == "Proof extraction: error"
            else:
                assert "unavailable_reason" not in group
            if unavailable and rejected_pilot in ("memory", "historical-memory"):
                assert "cap" in group["unavailable_reason"]
                if rejected_pilot == "historical-memory":
                    assert "current unvalidated" in group["unavailable_reason"]
            if relative.endswith("math-growth.data.json"):
                assert group["iteration"] == cutoff
        if rejected_pilot == "failed":
            assert data["metadata"]["unavailable"][0]["pilot"][0]["reason"] == failure_reason
            assert all(
                group["unavailable_reason"] == "Strict proof: error"
                for group in groups
                if "unavailable_reason" in group
            )
    assert report.read_bytes() == original_cache
    if rejected_pilot in ("memory", "historical-memory"):
        coverage = suites.build_coverage(selection, evidence, hashes, measurements)
        deferred = coverage["cases"][5]["workloads"][0]
        assert deferred["admitted"] is (rejected_pilot == "memory")
        assert deferred["pilot_status"] == ("admitted" if rejected_pilot == "memory" else "not-validated")
        assert "cap" in deferred["collection_reason"]
        assert deferred["collection_reason"] in suites.render_coverage_markdown(coverage)


def test_uncaptured_cases_keep_one_order_per_workload_and_protect_cache_outputs(tmp_path: Path) -> None:
    release = tmp_path / "target/release"
    release.mkdir(parents=True)
    for binary in ("egglog-experimental", "egg-math-benchmark"):
        (release / binary).write_text(binary)
    (tmp_path / "benchmarks").mkdir()
    (tmp_path / "benchmarks/catalog.json").write_text(
        json.dumps(
            {
                "families": {"eggcc": {}},
                "cases": [
                    {
                        "id": f"eggcc-{name}",
                        "family": "eggcc",
                        "source": name,
                        "status": "blocked",
                        "reason": "export failed",
                        "workloads": [],
                    }
                    for name in ("first", "second")
                ],
            }
        )
    )
    report = tmp_path / ".reports.jsonl"
    report.write_text("")
    prepare_expanded(tmp_path)
    data_path = tmp_path / "figures/expanded/eggcc/proof-overhead.data.json"
    groups = json.loads(data_path.read_text())["groups"]
    assert [group["workload_order"] for group in groups] == [0, 0, 0, 1, 1, 1]
    assert all(group["unavailable_reason"] and not group["observations"] for group in groups)
    before = data_path.read_bytes()
    with pytest.raises(ValueError, match="must differ from the benchmark cache"):
        prepare_expanded(tmp_path, report=data_path)
    assert data_path.read_bytes() == before


def test_overview_preserves_each_family_and_rebases_observation_sources(tmp_path: Path) -> None:
    release = tmp_path / "target/release"
    release.mkdir(parents=True)
    for binary in ("egglog-experimental", "egg-math-benchmark"):
        (release / binary).write_text(binary)
    (tmp_path / "benchmarks").mkdir()
    cases = []
    records = []
    for index, family in enumerate(("eggcc", "luminal")):
        file = tmp_path / f"{family}.egg"
        file.write_text(f"(check (= {index} {index}))\n")
        cases.append({"id": family, "family": family, "source": family, "status": "captured", "workloads": [file.name]})
        records.append(
            make_record(
                index,
                started_at="2026-09-23T00:00:00Z",
                file_sha256=sha256_file(file),
                binary_sha256=sha256_file(release / "egglog-experimental"),
                treatment="off",
                status="failure" if index else "success",
            )
        )
        records[-1]["file_path"] = file.name
        records[-1]["error_message"] = "normal-mode error" if index else None
    (tmp_path / "benchmarks/catalog.json").write_text(json.dumps({"families": {}, "cases": cases}))
    cache = "".join(json.dumps(row) + "\n" for row in records)
    (tmp_path / ".reports.jsonl").write_text(cache)
    prepare_expanded(tmp_path)
    overview_path = tmp_path / "figures/expanded/overview.data.json"
    overview = json.loads(overview_path.read_text())
    assert len(overview["sources"]) == 2
    for page in ("eggcc", "other"):
        atlas = json.loads((tmp_path / f"figures/expanded/atlas/{page}/atlas.data.json").read_text())
        assert atlas["sources"] == overview["sources"]
        for original, display in zip(overview["groups"], atlas["groups"], strict=True):
            assert {k: v for k, v in display.items() if k != "atlas_visible"} == original
            assert display["atlas_visible"] is ((original["family"] == "eggcc") == (page == "eggcc"))
    for family in ("eggcc", "luminal"):
        data = json.loads((tmp_path / f"figures/expanded/{family}/proof-overhead.data.json").read_text())
        projected = [group for group in overview["groups"] if group["family"] == family]
        assert len(projected) == len(data["groups"])
        for original, combined in zip(data["groups"], projected, strict=True):
            assert {k: v for k, v in combined.items() if k not in ("family", "observations")} == {
                k: v for k, v in original.items() if k != "observations"
            }
            for before, after in zip(original["observations"], combined["observations"], strict=True):
                assert {**after, "source_index": before["source_index"]} == before
                assert overview["sources"][after["source_index"]] == data["sources"][before["source_index"]]
    mtime = overview_path.stat().st_mtime_ns
    prepare_expanded(tmp_path)
    assert overview_path.stat().st_mtime_ns == mtime
    assert (tmp_path / ".reports.jsonl").read_text() == cache


def test_partial_capture_keeps_missing_invocation_and_original_ordinal(tmp_path: Path) -> None:
    release = tmp_path / "target/release"
    release.mkdir(parents=True)
    for binary in ("egglog-experimental", "egg-math-benchmark"):
        (release / binary).write_text(binary)
    (tmp_path / "benchmarks").mkdir()
    (tmp_path / "third.egg").write_text("(check (= 1 1))\n")
    (tmp_path / "benchmarks/catalog.json").write_text(
        json.dumps(
            {
                "families": {"dialegg": {}},
                "cases": [
                    {
                        "id": "dialegg-input",
                        "family": "dialegg",
                        "source": "input.mlir",
                        "status": "captured",
                        "workloads": ["third.egg"],
                        "invocations": [
                            {"index": 0, "status": "blocked", "reason": "No derived work to prove: no matched inputs"},
                            {"index": 1, "status": "blocked", "reason": "Query deferred: collection operations (Vec)"},
                            {"index": 2, "status": "captured", "workload": "third.egg"},
                        ],
                    }
                ],
            }
        )
    )
    (tmp_path / ".reports.jsonl").write_text("")
    prepare_expanded(tmp_path)
    groups = json.loads((tmp_path / "figures/expanded/dialegg/proof-overhead.data.json").read_text())["groups"]
    assert len(groups) == 9
    assert {group["workload"] for group in groups} == {f"dialegg-input / call {i}" for i in (1, 2, 3)}
    assert all(not group["observations"] for group in groups)
    assert {group["unavailable_reason"] for group in groups if group["workload"].endswith("call 1")} == {
        "No derived work to prove"
    }
    assert {group["unavailable_reason"] for group in groups if group["workload"].endswith("call 2")} == {
        "Query deferred: collection operations"
    }


@pytest.mark.parametrize("query_blocked", [False, True])
def test_proof_error_does_not_hide_complete_normal_mode_sample(tmp_path: Path, query_blocked: bool) -> None:
    release = tmp_path / "target/release"
    release.mkdir(parents=True)
    for binary in ("egglog-experimental", "egg-math-benchmark"):
        (release / binary).write_text(binary)
    workload = tmp_path / "case.egg"
    workload.write_text("(check (= 1 1))\n")
    case: dict[str, Any] = {
        "id": "eggcc-case",
        "family": "eggcc",
        "source": "source.program",
        "status": "captured",
        "workloads": [workload.name],
    }
    if query_blocked:
        reason = "No derived work to prove: no result was created by the schedule"
        case.update(
            workloads=[],
            invocations=[{"index": 0, "status": "blocked", "reason": reason}],
            normal_workloads=[{"path": workload.name, "proof_blocker": reason, "invocation": 0}],
        )
    (tmp_path / "benchmarks").mkdir()
    (tmp_path / "benchmarks/catalog.json").write_text(
        json.dumps(
            {
                "families": {"eggcc": {}},
                "cases": [case],
            }
        )
    )
    identity: dict[str, Any] = {
        "started_at": "2026-09-24T00:00:00Z",
        "binary_sha256": sha256_file(release / "egglog-experimental"),
        "file_sha256": sha256_file(workload),
        "wall_sec": 0.2,
        "max_rss_bytes": 1024**2,
    }
    records = [make_record(i, treatment="off", **identity) for i in range(30)]
    if not query_blocked:
        records.append(make_record(0, treatment="proof-extraction", status="failure", **identity))
        records[-1]["error_message"] = "proof extraction failed"
    report = tmp_path / ".reports.jsonl"
    cache = "".join(json.dumps(row) + "\n" for row in records)
    report.write_text(cache)

    prepare_expanded(tmp_path)

    overview = json.loads((tmp_path / "figures/expanded/overview.data.json").read_text())
    off, record, on = overview["groups"]
    assert "unavailable_reason" not in off
    assert len(off["observations"]) == 30
    assert classify_baseline(off["observations"]).status == "selected"
    if query_blocked:
        assert on["observations"] == []
        assert on["unavailable_reason"] == "No proof-compatible query"
    else:
        assert len(on["observations"]) == 1
        assert on["observations"][0]["status"] == "failure"
        assert on["unavailable_reason"] == "Proof extraction: error"
    assert report.read_text() == cache


def test_overview_deduplicates_across_families_in_catalog_order_and_retains_aliases(tmp_path: Path) -> None:
    release = tmp_path / "target/release"
    release.mkdir(parents=True)
    for binary in ("egglog-experimental", "egg-math-benchmark"):
        (release / binary).write_text(binary)
    cases = []
    for family in ("luminal", "eggcc"):
        (tmp_path / f"{family}.egg").write_text("(check (= 1 1))\n")
        cases.append(
            {
                "id": f"{family}-alias",
                "family": family,
                "source": "one shared replay",
                "status": "captured",
                "workloads": [f"{family}.egg"],
            }
        )
    (tmp_path / "benchmarks").mkdir()
    (tmp_path / "benchmarks/catalog.json").write_text(json.dumps({"families": {}, "cases": cases}))
    (tmp_path / ".reports.jsonl").write_text("")

    prepare_expanded(tmp_path)

    overview = json.loads((tmp_path / "figures/expanded/overview.data.json").read_text())
    assert len(suites.resolve_suite("expanded", tmp_path).files) == 1
    assert len(overview["groups"]) == 3
    assert all(group["family"] == "luminal" and group["workload_id"] == "luminal.egg" for group in overview["groups"])
    assert overview["metadata"]["aliases"] == {
        "luminal.egg": [
            {"case": "luminal-alias", "family": "luminal", "path": "luminal.egg"},
            {"case": "eggcc-alias", "family": "eggcc", "path": "eggcc.egg"},
        ]
    }
    for family in ("luminal", "eggcc"):
        detail = json.loads((tmp_path / f"figures/expanded/{family}/proof-overhead.data.json").read_text())
        assert len(detail["groups"]) == 3


@pytest.mark.parametrize("helper_has_calls", [False, True])
@pytest.mark.parametrize("helper_status", ["captured", "blocked"])
@pytest.mark.parametrize("helper_has_replay", [False, True])
def test_source_omissions_do_not_reappear_as_missing_figure_rows(
    tmp_path: Path, helper_has_calls: bool, helper_status: str, helper_has_replay: bool
) -> None:
    release = tmp_path / "target/release"
    release.mkdir(parents=True)
    for binary in ("egglog-experimental", "egg-math-benchmark"):
        (release / binary).write_text(binary)
    hashes = {"egglog": sha256_file(release / "egglog-experimental")}
    for index, name in enumerate(("kernel", "paired-helper", "normal-helper", "normal-selected")):
        (tmp_path / f"{name}.egg").write_text(f"(let value {index})\n")
    old_reason = "No derived work to prove: helper is setup only"
    cases: list[dict[str, Any]] = [
        {
            "id": "kernel",
            "family": "dialegg",
            "source": "kernel",
            "status": "captured",
            "reason": old_reason,
            "workloads": ["kernel.egg", "paired-helper.egg"],
            "normal_workloads": [{"path": "normal-helper.egg", "invocation": 2, "proof_blocker": old_reason}],
            "invocations": [
                {"index": 0, "workload": "kernel.egg"},
                {"index": 1, "workload": "paired-helper.egg"},
                {"index": 2, "reason": old_reason},
            ],
            "benchmark_selection": {"workloads": ["kernel.egg"], "reason": "Keep the full computation"},
        },
        {
            "id": "helper-only",
            "family": "dialegg",
            "source": "helper",
            "status": helper_status,
            "reason": old_reason,
            "workloads": ["paired-helper.egg"] if helper_has_replay else [],
            "benchmark_selection": {"workloads": [], "reason": "Setup only"},
            "invocations": [{"index": 0, **({"workload": "paired-helper.egg"} if helper_has_replay else {})}]
            if helper_has_calls
            else [],
        },
        {
            "id": "normal-selected",
            "family": "dialegg",
            "source": "analysis",
            "status": "captured",
            "workloads": [],
            "normal_workloads": [{"path": "normal-selected.egg", "invocation": 0, "proof_blocker": "Missing query"}],
            "invocations": [{"index": 0, "reason": "Missing query"}],
            "benchmark_selection": {"workloads": ["normal-selected.egg"], "reason": "Complete analysis"},
        },
    ]
    (tmp_path / "benchmarks").mkdir()
    (tmp_path / "benchmarks/catalog.json").write_text(json.dumps({"families": {"dialegg": {}}, "cases": cases}))
    selected = suites.resolve_suite("expanded", tmp_path, include_normal_only=True)
    file = selected.files[0]
    evidence = tmp_path / admission.PILOT_RELATIVE_PATH
    evidence.parent.mkdir(parents=True)
    evidence.write_text(
        json.dumps(
            {
                "identity": admission.pilot_identity(file, "dialegg", hashes, admission.PilotPolicy(), tmp_path),
                "status": "admitted",
                "reason": None,
            }
        )
        + "\n"
    )
    rows = [
        make_record(
            i,
            started_at="2026-09-24T00:00:00Z",
            treatment=treatment,
            file_sha256=sha256_file(tmp_path / f"{name}.egg"),
            binary_sha256=hashes["egglog"],
            wall_sec=0.2,
            max_rss_bytes=1024**2,
        )
        for name in ("kernel", "paired-helper", "normal-helper", "normal-selected")
        for _engine, _proof_mode, treatment in OVERHEAD_ENDPOINTS
        for i in range(30)
    ]
    report = tmp_path / ".reports.jsonl"
    original_cache = "".join(json.dumps(row) + "\n" for row in rows)
    report.write_text(original_cache)
    prepare_expanded(tmp_path)
    overview = json.loads((tmp_path / "figures/expanded/overview.data.json").read_text())
    assert len(overview["groups"]) == 6
    assert {group["workload_id"] for group in overview["groups"]} == {"kernel.egg", "normal-selected.egg"}
    assert all(len(group["observations"]) == 30 for group in overview["groups"])
    metadata = overview["metadata"]["families"]["dialegg"]
    assert [entry["case"] for entry in metadata["source_exclusions"]] == (
        ["kernel", "helper-only"] if helper_has_replay else ["kernel"]
    )
    assert [entry["case"] for entry in metadata["unavailable"]] == ["normal-selected"]
    assert all(
        group.get("unavailable_reason") == "No proof-compatible query"
        for group in overview["groups"]
        if group["workload_id"] == "normal-selected.egg" and group["treatment"] == "proof-extraction"
    )
    assert report.read_text() == original_cache


@pytest.mark.parametrize("timeout_sec", [120, 300, 480])
def test_projection_keeps_recording_ready_when_extraction_fails(tmp_path: Path, timeout_sec: int) -> None:
    release = tmp_path / "target/release"
    release.mkdir(parents=True)
    for binary in ("egglog-experimental", "egg-math-benchmark"):
        (release / binary).write_text(binary)
    workload = tmp_path / "case.egg"
    workload.write_text("(check (= 1 1))\n")
    (tmp_path / "benchmarks").mkdir()
    (tmp_path / "benchmarks/catalog.json").write_text(
        json.dumps(
            {
                "families": {"eggcc": {}},
                "cases": [
                    {
                        "id": "eggcc-case",
                        "family": "eggcc",
                        "source": "program",
                        "status": "captured",
                        "workloads": [workload.name],
                    }
                ],
            }
        )
    )
    selection = suites.resolve_suite("expanded", tmp_path)
    hashes = {"egglog": sha256_file(release / "egglog-experimental")}
    evidence = tmp_path / admission.PILOT_RELATIVE_PATH
    evidence.parent.mkdir(parents=True)
    evidence.write_text(
        json.dumps(
            {
                "identity": admission.pilot_identity(
                    selection.files[0], "eggcc", hashes, admission.PilotPolicy(timeout_sec=timeout_sec), tmp_path
                ),
                "status": "admitted",
                "reason": None,
            }
        )
        + "\n"
    )
    rows = [
        make_record(
            index,
            treatment=treatment,
            binary_sha256=hashes["egglog"],
            file_sha256=sha256_file(workload),
            started_at="2026-09-24T00:00:00Z",
            wall_sec=0.2,
            max_rss_bytes=1024**2,
            timeout_sec=timeout_sec,
        )
        for _, _, treatment in OVERHEAD_ENDPOINTS
        for index in range(30)
    ]
    rows[-1]["status"] = "failure"
    rows[-1]["error_message"] = "extraction failed"
    rows[-1]["error_exit_code"] = 1
    # A different timeout is a different cache identity, even with newer rows.
    rows.extend({**row, "timeout_sec": 60, "started_at": "2026-09-25T00:00:00Z", "wall_sec": 99.0} for row in rows[:30])
    report = tmp_path / ".reports.jsonl"
    original = "".join(json.dumps(row) + "\n" for row in rows)
    report.write_text(original)
    prepare_expanded(tmp_path, timeout_sec=timeout_sec)
    payload = json.loads((tmp_path / "figures/expanded/overview.data.json").read_text())
    off, recording, extraction = payload["groups"]
    assert [group["treatment"] for group in payload["groups"]] == ["off", "proofs", "proof-extraction"]
    assert "unavailable_reason" not in off
    assert "unavailable_reason" not in recording
    assert extraction["unavailable_reason"] == "Proof extraction: error"
    assert all(len(group["observations"]) == 30 for group in payload["groups"])
    assert payload["metadata"]["families"]["eggcc"]["timeout_sec"] == timeout_sec
    assert all(run["wall_sec"] == 0.2 for group in payload["groups"] for run in group["observations"])
    assert classify_baseline(off["observations"]).status == "selected"
    assert report.read_text() == original
