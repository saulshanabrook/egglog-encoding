"""Exercise source coverage, hash-bound admission, and bounded pilot cleanup."""

from __future__ import annotations

import json
import os
import subprocess
import sys
import time
from pathlib import Path
from typing import Any

import pytest

from benchmarking import admission, benchmark, pilot, suites
from benchmarking.engines import Treatment
from benchmarking.reports.grouped import grouped_report_path
from benchmarking.reports.store import ReportStore, parse_grouped_report
from benchmarking.workloads import DEFAULT_WORKLOADS

from .report_fixtures import make_record, make_target


@pytest.fixture(autouse=True)
def isolate_pilot_cache(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """Keep the public pilot entrypoint and repository probes in temporary fixtures."""

    monkeypatch.chdir(tmp_path)
    monkeypatch.setattr(pilot, "git_sha", lambda _root: "fixture-sha")
    monkeypatch.setattr(pilot, "git_dirty", lambda _root: False)


def write_catalog(root: Path) -> suites.SuiteSelection:
    (root / "benchmarks").mkdir(exist_ok=True)
    (root / "one.egg").write_text("(check (= 1 1))\n")
    (root / "alias.egg").write_text("(check (= 1 1))\n")
    (root / "benchmarks/catalog.json").write_text(
        json.dumps(
            {
                "families": {"eggcc": {"commit": "pinned"}, "luminal": {}},
                "cases": [
                    {
                        "id": "one",
                        "family": "eggcc",
                        "source": "source-a",
                        "status": "captured",
                        "workloads": ["one.egg"],
                    },
                    {
                        "id": "alias",
                        "family": "eggcc",
                        "source": "source-b",
                        "status": "captured",
                        "workloads": ["alias.egg"],
                    },
                    {
                        "id": "blocked",
                        "family": "luminal",
                        "source": "source-c",
                        "status": "blocked",
                        "reason": "needs exporter",
                        "workloads": [],
                    },
                    {
                        "id": "excluded",
                        "family": "herbie",
                        "source": "source-d",
                        "status": "captured",
                        "workloads": ["one.egg"],
                    },
                ],
            }
        )
    )
    return suites.resolve_suite("expanded", root)


def test_suite_preserves_default_and_rejects_ambiguous_cli() -> None:
    assert len(DEFAULT_WORKLOADS) == 11
    assert benchmark.parse_benchmark_args([]).suite is None
    assert benchmark.parse_benchmark_args(["--suite", "expanded"]).files == []
    for args in (["--suite", "expanded", "file.egg"], ["--suite", "expanded", "--fact-directory", "facts"]):
        with pytest.raises(SystemExit):
            benchmark.parse_benchmark_args(args)


def test_capture_aliases_deduplicate_invocations_without_losing_cases(tmp_path: Path) -> None:
    selection = write_catalog(tmp_path)
    assert [case.id for case in selection.cases] == ["one", "alias", "blocked"]
    assert len(selection.files) == 1
    assert selection.case_files["alias"][0].display_path == "alias.egg"
    assert selection.case_files["one"][0].sha256 == selection.case_files["alias"][0].sha256
    assert not selection.case_files["blocked"]


@pytest.mark.parametrize(
    ("names", "case_ids"),
    [
        (("math-11",), ["math-growth-011"]),
        (("math-11", "math-11"), ["math-growth-011"]),
        (("math-growth",), ["math-growth-001", "math-growth-011", "math-growth-012"]),
        (("math-11", "math-growth"), ["math-growth-001", "math-growth-011", "math-growth-012"]),
        (("math-growth", "math-11"), ["math-growth-001", "math-growth-011", "math-growth-012"]),
        (("math-11", "luminal"), ["math-alias", "math-growth-011"]),
        (("luminal", "math-11"), ["math-alias", "math-growth-011"]),
        (("expanded",), ["math-alias", "math-growth-001", "math-growth-011", "math-growth-012"]),
        (("math-11", "expanded"), ["math-alias", "math-growth-001", "math-growth-011", "math-growth-012"]),
    ],
)
def test_math_11_suite_preserves_catalog_unions_and_math_admission(
    tmp_path: Path, names: tuple[str, ...], case_ids: list[str]
) -> None:
    (tmp_path / "benchmarks").mkdir()
    for name, value in (("math-1.egg", 1), ("math-11.egg", 11), ("alias.egg", 11)):
        (tmp_path / name).write_text(f"(check (= {value} {value}))\n")
    cases = [
        {"id": "math-alias", "family": "luminal", "workloads": ["alias.egg"]},
        {"id": "math-growth-001", "family": "math-growth", "workloads": ["math-1.egg"]},
        {"id": "math-growth-011", "family": "math-growth", "workloads": ["math-11.egg"]},
        {"id": "math-growth-012", "family": "math-growth", "workloads": [], "status": "deferred"},
        {"id": "not-expanded", "family": "herbie", "workloads": ["alias.egg"]},
    ]
    (tmp_path / "benchmarks/catalog.json").write_text(
        json.dumps(
            {
                "families": {"math-growth": {}, "luminal": {}, "herbie": {}},
                "cases": [{"source": "fixture", "status": "captured", **case} for case in cases],
            }
        )
    )
    validator = tmp_path / "benchmarking/math_workloads.py"
    validator.parent.mkdir()
    validator.write_text("# Math parity validator fixture\n")
    selection = suites.resolve_suite(names, tmp_path)
    assert [case.id for case in selection.cases] == case_ids
    assert len(selection.files) == (2 if "math-growth-001" in case_ids else 1)
    math_file = selection.case_files["math-growth-011"][0]
    identity = (math_file.sha256, math_file.fact_directory_sha256)
    assert selection.validation_families[identity] == "math-growth"
    hashes = {"egglog": "egglog-hash", "egg": "egg-hash"}
    policy = admission.PilotPolicy(timeout_sec=300)
    pilot_identity = admission.pilot_identity(
        math_file, selection.validation_families[identity], hashes, policy, tmp_path
    )
    full_math = suites.resolve_suite("math-growth", tmp_path)
    assert pilot_identity == admission.pilot_identity(
        full_math.case_files["math-growth-011"][0], "math-growth", hashes, policy, tmp_path
    )
    assert pilot_identity["binary_hashes"] == hashes
    assert pilot_identity["math_validator_sha256"] == suites.sha256_file(validator)
    assert benchmark.parse_benchmark_args(["--suite", "math-11"]).suite == ["math-11"]


@pytest.mark.parametrize("normal_only", [False, True])
def test_incomplete_parent_cannot_admit_a_prefix_but_complete_alias_survives(tmp_path: Path, normal_only: bool) -> None:
    write_catalog(tmp_path)
    path = tmp_path / "benchmarks/catalog.json"
    catalog = json.loads(path.read_text())
    catalog["cases"][0]["complete_reproduction"] = {"status": "blocked", "reason": "parent compiler failed later"}
    path.write_text(json.dumps(catalog))
    result = suites.resolve_suite("eggcc", tmp_path, include_normal_only=normal_only)
    assert not result.case_files["one"]
    assert len(result.files) == 1
    assert result.case_files["alias"]
    assert result.capture_errors["one"] == "parent compiler failed later"


def test_complete_reproduction_is_bound_to_receipt_and_replay_bytes(tmp_path: Path) -> None:
    selection = write_catalog(tmp_path)
    file = selection.files[0]
    receipt = tmp_path / "completion.json"
    receipt.write_text('{"source_completion": true}')
    path = tmp_path / "benchmarks/catalog.json"
    catalog = json.loads(path.read_text())
    catalog["cases"][0]["complete_reproduction"] = {
        "status": "complete",
        "receipt": "completion.json",
        "receipt_sha256": suites.sha256_file(receipt),
        "workloads": {"one.egg": {"file_sha256": file.sha256, "facts_sha256": file.fact_directory_sha256}},
    }
    path.write_text(json.dumps(catalog))
    assert suites.resolve_suite("eggcc", tmp_path).case_files["one"]
    (tmp_path / "one.egg").write_text("(check (= 2 2))")
    stale = suites.resolve_suite("eggcc", tmp_path)
    assert not stale.case_files["one"]
    assert "replay identity changed" in stale.capture_errors["one"]
    (tmp_path / "one.egg").write_text("(check (= 1 1))\n")
    receipt.write_text("changed evidence")
    stale = suites.resolve_suite("eggcc", tmp_path)
    assert not stale.case_files["one"]
    assert "receipt changed" in stale.capture_errors["one"]


@pytest.mark.parametrize("include_normal_only", [False, True])
def test_source_selection_filters_before_file_resolution_and_preserves_omissions(
    tmp_path: Path, include_normal_only: bool
) -> None:
    write_catalog(tmp_path)
    path = tmp_path / "benchmarks/catalog.json"
    catalog = json.loads(path.read_text())
    case = catalog["cases"][0]
    case["workloads"].append("helper.egg")
    case["normal_workloads"] = [{"path": "normal-helper.egg", "proof_blocker": "No derived query", "invocation": 2}]
    case["benchmark_selection"] = {"workloads": ["one.egg"], "reason": "Skip setup-only calls"}
    path.write_text(json.dumps(catalog))
    # Omitted replays need not be available locally and cannot cause capture errors.
    selection = suites.resolve_suite("expanded", tmp_path, include_normal_only=include_normal_only)
    assert len(selection.files) == 1
    assert selection.source_exclusions == {"one": ("helper.egg", "normal-helper.egg")}
    assert not selection.proof_blockers
    assert not selection.capture_errors
    assert selection.case_files["alias"][0].display_path == "alias.egg"
    coverage = suites.build_coverage(selection, tmp_path / "absent-pilot.jsonl")
    assert coverage["cases"][0]["excluded_workloads"] == ("helper.egg", "normal-helper.egg")
    markdown = suites.render_coverage_markdown(coverage)
    assert "Source-role omissions" in markdown
    assert "| one | helper.egg | Skip setup-only calls |" in markdown


@pytest.mark.parametrize("selected", [["stale.egg"], ["one.egg", "one.egg"]])
def test_invalid_source_selection_fails_closed(tmp_path: Path, selected: list[str]) -> None:
    write_catalog(tmp_path)
    path = tmp_path / "benchmarks/catalog.json"
    catalog = json.loads(path.read_text())
    catalog["cases"][0]["benchmark_selection"] = {"workloads": selected, "reason": "Substantive work"}
    path.write_text(json.dumps(catalog))
    with pytest.raises(ValueError, match="benchmark_selection"):
        suites.resolve_suite("expanded", tmp_path, include_normal_only=True)


def test_omitted_normal_only_case_is_not_a_missing_capture(tmp_path: Path) -> None:
    write_catalog(tmp_path)
    path = tmp_path / "benchmarks/catalog.json"
    catalog = json.loads(path.read_text())
    case = catalog["cases"][0]
    case["workloads"] = []
    case["normal_workloads"] = [{"path": "one.egg", "proof_blocker": "No derived query", "invocation": 0}]
    case["benchmark_selection"] = {"workloads": [], "reason": "Setup only"}
    path.write_text(json.dumps(catalog))
    selection = suites.resolve_suite("expanded", tmp_path)
    assert not selection.capture_errors
    assert selection.source_exclusions == {"one": ("one.egg",)}
    coverage = suites.build_coverage(selection, tmp_path / "absent-pilot.jsonl")
    assert "| eggcc | one | captured | excluded from benchmarks |" in suites.render_coverage_markdown(coverage)


@pytest.mark.parametrize("status", ["captured", "blocked"])
def test_explicit_empty_selection_without_recorded_paths_has_no_capture_error(tmp_path: Path, status: str) -> None:
    write_catalog(tmp_path)
    path = tmp_path / "benchmarks/catalog.json"
    catalog = json.loads(path.read_text())
    case = catalog["cases"][0]
    case.update(status=status, workloads=[], benchmark_selection={"workloads": [], "reason": "Setup only"})
    path.write_text(json.dumps(catalog))
    for include_normal_only in (False, True):
        selection = suites.resolve_suite("expanded", tmp_path, include_normal_only=include_normal_only)
        assert not selection.capture_errors
        assert not selection.case_files["one"]
        coverage = suites.build_coverage(selection, tmp_path / "absent-pilot.jsonl")
        markdown = suites.render_coverage_markdown(coverage)
        assert f"| eggcc | one | {status} | excluded from benchmarks |" in markdown
        family_row = next(line for line in markdown.splitlines() if line.startswith("| eggcc | 2 |"))
        assert family_row.endswith(" | 0 | 0 |")  # No blocked/deferred selected source cases.


def test_normal_only_captures_are_opt_in_and_preserve_aliases(tmp_path: Path) -> None:
    write_catalog(tmp_path)
    (tmp_path / "normal.egg").write_text("(run 1)\n")
    (tmp_path / "normal-alias.egg").write_text("(run 1)\n")
    path = tmp_path / "benchmarks/catalog.json"
    catalog = json.loads(path.read_text())
    for case, filename in zip(catalog["cases"][:2], ("normal.egg", "normal-alias.egg"), strict=True):
        case["normal_workloads"] = [{"path": filename, "proof_blocker": "No derived query", "invocation": 1}]
    path.write_text(json.dumps(catalog))

    ordinary = suites.resolve_suite("expanded", tmp_path)
    assert len(ordinary.files) == 1
    assert not ordinary.proof_blockers
    selection = suites.resolve_suite(("eggcc", "eggcc", "expanded"), tmp_path, include_normal_only=True)
    assert [case.id for case in selection.cases] == ["one", "alias", "blocked"]
    assert len(selection.files) == 2
    assert selection.case_files["one"][1].display_path == "normal.egg"
    assert selection.case_files["alias"][1].display_path == "normal-alias.egg"
    normal = selection.case_files["one"][1]
    assert selection.proof_blockers == {(normal.sha256, normal.fact_directory_sha256): "No derived query"}
    assert not selection.capture_errors


@pytest.mark.parametrize("normal_first", [False, True])
def test_paired_identity_overrides_normal_only_blocker(tmp_path: Path, normal_first: bool) -> None:
    write_catalog(tmp_path)
    path = tmp_path / "benchmarks/catalog.json"
    catalog = json.loads(path.read_text())
    normal_case = catalog["cases"].pop(2)
    normal_case["status"] = "captured"
    normal_case["normal_workloads"] = [{"path": "alias.egg", "proof_blocker": "No derived query", "invocation": 0}]
    catalog["cases"].insert(0 if normal_first else len(catalog["cases"]), normal_case)
    path.write_text(json.dumps(catalog))
    selection = suites.resolve_suite("expanded", tmp_path, include_normal_only=True)
    assert len(selection.files) == 1
    assert len(selection.case_files["blocked"]) == 1
    assert not selection.proof_blockers
    assert not selection.capture_errors


def test_normal_only_coverage_retains_measurements_without_claiming_proof_admission(tmp_path: Path) -> None:
    write_catalog(tmp_path)
    (tmp_path / "normal.egg").write_text("(run 1)\n")
    path = tmp_path / "benchmarks/catalog.json"
    catalog = json.loads(path.read_text())
    catalog["cases"][0]["normal_workloads"] = [
        {"path": "normal.egg", "proof_blocker": "Query deferred: collection operations", "invocation": 2}
    ]
    path.write_text(json.dumps(catalog))
    selection = suites.resolve_suite("expanded", tmp_path, include_normal_only=True)
    normal = selection.case_files["one"][1]
    hashes = {"egglog": "sha256:current"}
    evidence = tmp_path / "pilot.jsonl"
    evidence.write_text(
        json.dumps(
            {
                "identity": admission.pilot_identity(normal, "eggcc", hashes, admission.PilotPolicy(), tmp_path),
                "status": "admitted",
                "reason": None,
            }
        )
        + "\n"
    )
    rows = [
        make_record(
            0,
            started_at="2026-09-24T00:00:00Z",
            file_sha256=normal.sha256,
            binary_sha256=hashes["egglog"],
            treatment="off",
        )
    ]
    coverage = suites.build_coverage(selection, evidence, hashes, rows)
    result = coverage["cases"][0]["workloads"][1]
    assert result["preparation_status"] == "proof-query-blocked"
    assert result["preparation_reason"] == "Query deferred: collection operations"
    assert result["pilot_status"] == "proof-query-blocked"
    assert not result["admitted"]
    assert result["measurements"] == [{"treatment": "off", "status": "success", "timeout_sec": 120, "rows": 1}]
    markdown = suites.render_coverage_markdown(coverage)
    assert "Query deferred: collection operations" in markdown
    assert "off success (120s): 1" in markdown


def test_missing_capture_remains_visible_in_coverage(tmp_path: Path) -> None:
    write_catalog(tmp_path)
    (tmp_path / "one.egg").unlink()
    selection = suites.resolve_suite("expanded", tmp_path)
    coverage = suites.build_coverage(selection, tmp_path / "absent-pilot.jsonl")
    assert coverage["cases"][0]["capture_status"] == "missing"
    assert "does not exist" in coverage["cases"][0]["reason"]
    assert coverage["cases"][1]["workloads"][0]["pilot_status"] == "not-validated"
    rendered = suites.render_coverage_markdown(coverage)
    assert "needs exporter" in rendered
    assert not (tmp_path / "absent-pilot.jsonl").exists()


def test_collection_accepts_unscreened_inputs_and_keeps_failures_identity_bound(tmp_path: Path) -> None:
    selection = write_catalog(tmp_path)
    target = make_target(binary_sha256="sha256:binary")
    store = ReportStore(tmp_path / "measurements.jsonl")
    evidence = tmp_path / "pilot.jsonl"
    record: dict[str, Any] = {
        "identity": admission.pilot_identity(
            selection.files[0], "eggcc", {"egglog": "sha256:binary"}, admission.PilotPolicy(), tmp_path
        ),
        "status": "failure",
        "reason": "proof-testing: invalid proof",
    }
    files, diagnostics, issues = pilot.require_suite_admission(selection, (target,), evidence, store=store)
    assert files == selection.files
    assert diagnostics == ("blocked: needs exporter",)
    assert issues == ()
    assert not evidence.exists()
    evidence.write_text(json.dumps(record) + "\n")
    for treatment in ("off", "proof-extraction"):
        store.append(
            make_record(
                0,
                started_at="2026-09-22T00:00:00Z",
                file_sha256=selection.files[0].sha256,
                binary_sha256=target.binary_sha256,
                treatment=treatment,
            )
        )
    files, diagnostics, issues = pilot.require_suite_admission(selection, (target,), evidence, store=store)
    assert files == selection.files
    assert "retained outcome" in diagnostics[-1]
    assert issues == ((selection.files[0], "proof-testing: invalid proof"),)
    changed = make_target(binary_sha256="sha256:changed")
    files, _, issues = pilot.require_suite_admission(selection, (changed,), evidence, store=store)
    assert files == selection.files and not issues
    for name in ("one.egg", "alias.egg"):
        (tmp_path / name).write_text("(check (= 2 2))\n")
    changed_inputs = suites.resolve_suite("expanded", tmp_path)
    files, _, issues = pilot.require_suite_admission(changed_inputs, (target,), evidence, store=store)
    assert files == changed_inputs.files and not issues
    record["identity"]["policy"]["memory_limit_bytes"] = 42
    evidence.write_text(json.dumps(record) + "\n")
    files, _, issues = pilot.require_suite_admission(selection, (target,), evidence, store=store)
    assert files == selection.files and not issues


def test_failed_pilot_is_a_retained_outcome_without_invented_measurements(tmp_path: Path) -> None:
    selection = write_catalog(tmp_path)
    evidence = tmp_path / "pilot.jsonl"
    evidence.write_text(
        json.dumps(
            {
                "identity": admission.pilot_identity(
                    selection.files[0], "eggcc", {"egglog": "sha256:binary"}, admission.PilotPolicy(), tmp_path
                ),
                "status": "timed-out",
                "reason": "proof-testing exceeded 120s",
            }
        )
        + "\n"
    )
    coverage = suites.build_coverage(selection, evidence, {"egglog": "sha256:binary"})
    assert len(coverage["cases"]) == 3
    assert coverage["cases"][0]["workloads"][0]["pilot_status"] == "timed-out"
    assert not coverage["cases"][0]["workloads"][0]["admitted"]
    assert coverage["cases"][0]["workloads"][0]["measurements"] == []
    store = ReportStore(tmp_path / "measurements.jsonl")
    files, diagnostics, issues = pilot.require_suite_admission(
        selection, (make_target(binary_sha256="sha256:binary"),), evidence, store=store
    )
    assert files == selection.files
    assert issues == ((selection.files[0], "proof-testing exceeded 120s"),)
    assert "retained outcome" in diagnostics[-1]
    assert store.records == ()


@pytest.mark.parametrize("timeout_sec", [120, 300, 480])
def test_coverage_counts_exact_engine_endpoints_and_separates_raw_calls_from_replays(
    tmp_path: Path, timeout_sec: int
) -> None:
    write_catalog(tmp_path)
    catalog_path = tmp_path / "benchmarks/catalog.json"
    catalog = json.loads(catalog_path.read_text())
    for case in catalog["cases"][:2]:
        case.update(obtainable=True, invocations=[{"index": 0, "raw": case["workloads"][0]}])
    catalog["families"]["churchroad"] = {}
    catalog["cases"].append(
        {
            "id": "circuit",
            "family": "churchroad",
            "source": "circuit.v",
            "status": "captured",
            "obtainable": True,
            "workloads": ["one.egg"],
            "engine_sessions": 1,
            "ordered_calls": [{"index": i, "raw": f"fragment-{i}.egg"} for i in range(5)],
        }
    )
    catalog_path.write_text(json.dumps(catalog))
    selection = suites.resolve_suite("expanded", tmp_path)
    file = selection.files[0]
    hashes = {"egglog": "sha256:current-egglog", "egg": "sha256:current-egg"}
    evidence = tmp_path / "pilot.jsonl"
    evidence.write_text(
        json.dumps(
            {
                "identity": admission.pilot_identity(
                    file, "eggcc", hashes, admission.PilotPolicy(timeout_sec=timeout_sec), tmp_path
                ),
                "status": "admitted",
                "reason": None,
            }
        )
        + "\n"
    )
    store = ReportStore(tmp_path / "measurements.jsonl")
    conditions: tuple[tuple[Treatment, str, int, int], ...] = (
        ("off", hashes["egglog"], timeout_sec, 9),
        ("proof-extraction", hashes["egglog"], timeout_sec, 10),
        ("off", hashes["egg"], timeout_sec, 10),
        ("proof-extraction", hashes["egg"], timeout_sec, 10),
        ("off", "sha256:stale", timeout_sec, 10),
        ("off", hashes["egglog"], 60, 10),
        ("term", hashes["egglog"], timeout_sec, 10),
    )
    for treatment, binary, timeout, count in conditions:
        for index in range(count):
            store.append(
                make_record(
                    index,
                    started_at="2026-09-21T00:00:00Z",
                    file_sha256=file.sha256,
                    treatment=treatment,
                    binary_sha256=binary,
                    timeout_sec=timeout,
                )
            )
    original_cache = store.path.read_bytes()
    coverage = suites.build_coverage(selection, evidence, hashes, store.records, timeout_sec=timeout_sec)
    measurements = coverage["cases"][0]["workloads"][0]["measurements"]
    counts = {(row["treatment"], row["timeout_sec"]): row["rows"] for row in measurements}
    assert counts == {
        ("off", timeout_sec): 9,
        ("proof-extraction", timeout_sec): 10,
        ("off", 60): 10,
        ("term", timeout_sec): 10,
    }
    markdown = suites.render_coverage_markdown(coverage)
    assert f"off at {timeout_sec} seconds" in markdown
    assert "| eggcc | 2 | 2 | 2 | 1 | 0 / 1 | 0 | 0 | 0 | 0 |" in markdown
    assert "| churchroad | 1 | 1 | 5 | 1 | 0 / 1 | 0 | 0 | 0 | 0 |" in markdown
    assert "| Replay preparation |" in markdown
    assert "raw calls are not independent workloads" in markdown
    assert store.path.read_bytes() == original_cache

    store.append(
        make_record(
            9,
            started_at="2026-09-21T00:00:00Z",
            file_sha256=file.sha256,
            treatment="off",
            binary_sha256=hashes["egglog"],
            timeout_sec=timeout_sec,
        )
    )
    markdown = suites.render_coverage_markdown(
        suites.build_coverage(selection, evidence, hashes, store.records, timeout_sec=timeout_sec)
    )
    assert "| eggcc | 2 | 2 | 2 | 1 | 0 / 1 | 0 | 1 | 0 | 0 |" in markdown


def test_bounded_process_timeout_kills_descendants_and_retains_logs(tmp_path: Path) -> None:
    pid_path = tmp_path / "child.pid"
    command = [
        sys.executable,
        "-c",
        "import subprocess,sys,time,pathlib; "
        "p=subprocess.Popen([sys.executable,'-c','import time; time.sleep(30)']); "
        "pathlib.Path(sys.argv[1]).write_text(str(p.pid)); print('started',flush=True); time.sleep(30)",
        str(pid_path),
    ]
    result = pilot.run_bounded_command(command, tmp_path, tmp_path / "timeout", timeout_sec=0.5)
    assert result.status == "timed-out"
    assert result.wall_sec < 5
    assert result.stdout_path.read_text().strip() == "started"
    pid = int(pid_path.read_text())
    for _ in range(30):
        child = subprocess.run(["ps", "-p", str(pid), "-o", "stat="], capture_output=True, text=True)
        if not child.stdout.strip() or child.stdout.strip().startswith("Z"):
            break
        time.sleep(0.01)
    else:
        os.kill(pid, 9)
        pytest.fail("pilot timeout left a descendant alive")


def test_bounded_process_enforces_small_rss_threshold(tmp_path: Path) -> None:
    result = pilot.run_bounded_command(
        [sys.executable, "-c", "import time; data=bytearray(4*1024*1024); time.sleep(30)"],
        tmp_path,
        tmp_path / "memory",
        timeout_sec=5,
        memory_limit_bytes=1024,
    )
    assert result.status == "memory-limit"
    assert result.peak_rss_bytes > 1024
    assert result.wall_sec < 5


def test_strict_proof_failure_prevents_admission(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    selection = write_catalog(tmp_path)
    binary = tmp_path / "egglog"
    binary.write_text("binary")
    treatments: list[str] = []

    def run(command: list[str], cwd: Path, output_prefix: Path, **kwargs: Any) -> pilot.PilotProcessResult:
        treatment = output_prefix.name
        treatments.append(treatment)
        return pilot.PilotProcessResult(
            "failure" if treatment == "proof-testing" else "success",
            1 if treatment == "proof-testing" else 0,
            0.1,
            10,
            output_prefix.with_suffix(".out"),
            output_prefix.with_suffix(".err"),
            "invalid proof" if treatment == "proof-testing" else None,
        )

    monkeypatch.setattr(pilot, "run_bounded_command", run)
    binary_hash = pilot.sha256_file(binary)
    store = ReportStore(tmp_path / "measurements.jsonl")
    for treatment in ("off", "proof-extraction"):
        store.append(
            make_record(
                0,
                started_at="2026-09-22T00:00:00Z",
                file_sha256=selection.files[0].sha256,
                binary_sha256=binary_hash,
                treatment=treatment,
            )
        )
    measured_before = store.path.read_bytes()
    record = pilot.pilot_workload(
        selection.files[0],
        "eggcc",
        {"egglog": binary},
        {"egglog": pilot.sha256_file(binary)},
        tmp_path,
        tmp_path / "logs",
        admission.PilotPolicy(),
        store=store,
        target=make_target(binary_sha256=binary_hash, binary_path=binary),
    )
    assert treatments == ["proof-testing"]
    assert record["status"] == "failure"
    assert record["reason"] == "proof-testing: invalid proof"
    assert not (tmp_path / ".reports.jsonl").exists()
    assert store.path.read_bytes() == measured_before


@pytest.mark.parametrize("status", ["admitted", "failure"])
@pytest.mark.parametrize("allow_failures", [False, True])
def test_pilot_reuses_same_identity_without_running_or_touching_measured_cache(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: Any,
    status: str,
    allow_failures: bool,
) -> None:
    selection = write_catalog(tmp_path)
    binary = tmp_path / "egglog"
    binary.write_text("binary")
    evidence = tmp_path / "pilot.jsonl"
    evidence.write_text(
        json.dumps(
            {
                "identity": admission.pilot_identity(
                    selection.files[0],
                    "eggcc",
                    {"egglog": pilot.sha256_file(binary)},
                    admission.PilotPolicy(),
                    tmp_path,
                ),
                "status": status,
                "reason": "proof-testing: invalid proof" if status == "failure" else None,
            }
        )
        + "\n"
    )
    monkeypatch.setattr(pilot, "__file__", str(tmp_path / "benchmarking/pilot.py"))
    monkeypatch.setattr(pilot, "run_bounded_command", lambda *_args, **_kwargs: pytest.fail("must reuse admission"))
    store = ReportStore(tmp_path / ".reports.jsonl")
    for treatment in ("off", "proof-extraction"):
        store.append(
            make_record(
                0,
                started_at="2026-09-22T00:00:00Z",
                file_sha256=selection.files[0].sha256,
                binary_sha256=pilot.sha256_file(binary),
                treatment=treatment,
            )
        )
    measured_before = store.path.read_bytes()
    before = evidence.read_bytes()
    arguments = ["--suite", "expanded", "--egglog-binary", str(binary), "--evidence", str(evidence)]
    if allow_failures:
        arguments.append("--allow-classified-failures")
    assert pilot.main(arguments) == (1 if status == "failure" and not allow_failures else 0)
    assert "(reused)" in capsys.readouterr().err
    assert pilot.main([*arguments, "--timeout-sec", "0"]) == 2
    assert evidence.read_bytes() == before
    assert store.path.read_bytes() == measured_before


def test_latest_operational_stop_supersedes_prior_admission(tmp_path: Path) -> None:
    selection = write_catalog(tmp_path)
    hashes = {"egglog": "sha256:binary"}
    identity = admission.pilot_identity(selection.files[0], "eggcc", hashes, admission.PilotPolicy(), tmp_path)
    admitted = {"identity": identity, "status": "admitted"}
    stopped = {"identity": identity, "status": "resource-stopped", "operational_stop": True}
    assert (
        admission.find_pilot_record(
            [admitted, stopped], selection.files[0], "eggcc", hashes, admission.PilotPolicy(), tmp_path
        )
        is stopped
    )
    assert (
        admission.find_pilot_record([stopped], selection.files[0], "eggcc", hashes, admission.PilotPolicy(), tmp_path)
        is stopped
    )


def test_coverage_shows_latest_current_safety_stop_without_admitting_it(tmp_path: Path) -> None:
    selection = write_catalog(tmp_path)
    hashes = {"egglog": "sha256:binary"}
    identity = admission.pilot_identity(selection.files[0], "eggcc", hashes, admission.PilotPolicy(), tmp_path)
    stopped: dict[str, Any] = {
        "identity": identity,
        "status": "resource-stopped",
        "reason": "proof-extraction: host memory pressure level 2",
        "operational_stop": True,
    }
    records = [
        {**stopped, "reason": "off: earlier safety stop"},
        stopped,
        {**stopped, "identity": {**identity, "binary_hashes": {"egglog": "sha256:stale"}}, "reason": "stale stop"},
    ]
    evidence = tmp_path / "pilot.jsonl"
    evidence.write_text("".join(json.dumps(record) + "\n" for record in records))
    before = evidence.read_bytes()
    coverage = suites.build_coverage(selection, evidence, hashes)
    for case in coverage["cases"][:2]:
        workload = case["workloads"][0]
        assert workload["pilot_status"] == "resource-stopped"
        assert not workload["admitted"]
        assert workload["pilot_reason"] == stopped["reason"]
        assert workload["preparation_status"] == "resource-limited"
        assert workload["preparation_reason"] == stopped["reason"]
        assert workload["preparation_by_treatment"] == {
            "proofs": {"status": "resource-limited", "reason": "off: earlier safety stop"},
            "proof-extraction": {"status": "resource-limited", "reason": stopped["reason"]},
        }
        assert workload["measurements"] == []
    rendered = suites.render_coverage_markdown(coverage)
    assert stopped["reason"] in rendered
    assert "resource-limited" in rendered
    assert "off: earlier safety stop" in rendered
    assert "stale stop" not in rendered
    assert "run the pilot" not in rendered
    assert evidence.read_bytes() == before
    files, _diagnostics, issues = pilot.require_suite_admission(
        selection,
        (make_target(binary_sha256=hashes["egglog"]),),
        evidence,
        store=ReportStore(tmp_path / "measurements.jsonl"),
    )
    assert files == selection.files
    assert issues == ((selection.files[0], stopped["reason"]),)


def test_coverage_does_not_report_another_binary_safety_stop_as_current(tmp_path: Path) -> None:
    selection = write_catalog(tmp_path)
    evidence = tmp_path / "pilot.jsonl"
    evidence.write_text(
        json.dumps(
            {
                "identity": admission.pilot_identity(
                    selection.files[0], "eggcc", {"egglog": "sha256:stale"}, admission.PilotPolicy(), tmp_path
                ),
                "status": "resource-stopped",
                "reason": "proof-extraction: host memory pressure level 2",
                "operational_stop": True,
            }
        )
        + "\n"
    )
    for hashes in ({"egglog": "sha256:current"}, None):
        coverage = suites.build_coverage(selection, evidence, hashes)
        workload = coverage["cases"][0]["workloads"][0]
        assert workload["pilot_status"] == "not-validated"
        assert not workload["admitted"]
        assert workload["pilot_reason"] is None
        assert workload["collection_reason"] is None


@pytest.mark.parametrize("status, reason", [("admitted", None), ("failure", "proof validation failed")])
def test_coverage_preserves_later_safety_stop_over_prior_validation(
    tmp_path: Path, status: str, reason: str | None
) -> None:
    selection = write_catalog(tmp_path)
    hashes = {"egglog": "sha256:binary"}
    identity = admission.pilot_identity(selection.files[0], "eggcc", hashes, admission.PilotPolicy(), tmp_path)
    records = [
        {"identity": identity, "status": status, "reason": reason},
        {"identity": identity, "status": "resource-stopped", "reason": "host pressure", "operational_stop": True},
    ]
    evidence = tmp_path / "pilot.jsonl"
    evidence.write_text("".join(json.dumps(record) + "\n" for record in records))
    workload = suites.build_coverage(selection, evidence, hashes)["cases"][0]["workloads"][0]
    assert workload["pilot_status"] == "resource-stopped"
    assert not workload["admitted"]
    assert workload["pilot_reason"] == "host pressure"
    assert workload["preparation_status"] == "resource-limited"


@pytest.mark.parametrize("allow_failures", [False, True])
def test_pilot_operational_stop_is_written_then_halts(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, allow_failures: bool
) -> None:
    write_catalog(tmp_path)
    (tmp_path / "alias.egg").write_text("(check (= 2 2))\n")
    binary = tmp_path / "egglog"
    binary.write_text("binary")
    evidence = tmp_path / "pilot.jsonl"
    report = tmp_path / "measurements.jsonl"
    coverage = tmp_path / "coverage.json"
    coverage.write_text("stale coverage")
    coverage.with_suffix(".md").write_text("stale coverage")
    calls = 0

    def stopped(*args: Any, **_kwargs: Any) -> dict[str, Any]:
        nonlocal calls
        calls += 1
        file, family, _binaries, hashes, root, _directory, policy = args
        return {
            "identity": admission.pilot_identity(file, family, hashes, policy, root),
            "status": "resource-stopped",
            "reason": "host pressure",
            "operational_stop": True,
        }

    monkeypatch.setattr(pilot, "__file__", str(tmp_path / "benchmarking/pilot.py"))
    monkeypatch.setattr(pilot, "pilot_workload", stopped)
    assert (
        pilot.main(
            [
                "--suite",
                "expanded",
                "--egglog-binary",
                str(binary),
                "--evidence",
                str(evidence),
                "--report",
                str(report),
                "--coverage-output",
                str(coverage),
                *(["--allow-classified-failures"] if allow_failures else []),
            ]
        )
        == 2
    )
    assert calls == 1
    assert json.loads(evidence.read_text())["operational_stop"]
    cases = json.loads(coverage.read_text())["cases"]
    first = cases[0]["workloads"][0]
    assert first["pilot_status"] == "resource-stopped"
    assert first["preparation_status"] == "resource-limited"
    assert first["pilot_reason"] == "host pressure"
    assert cases[1]["workloads"][0]["preparation_status"] == "pending"
    assert all(not workload["measurements"] for case in cases for workload in case["workloads"])
    rendered = coverage.with_suffix(".md").read_text()
    assert "host pressure" in rendered and "stale coverage" not in rendered
    assert ReportStore(report).records == ()


@pytest.mark.parametrize("after_off", [False, True])
def test_pilot_preflight_refusal_refreshes_pending_coverage_without_fabricating_evidence(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, after_off: bool
) -> None:
    write_catalog(tmp_path)
    (tmp_path / "alias.egg").write_text("(check (= 2 2))\n")
    binary = tmp_path / "egglog"
    binary.write_text("binary")
    evidence = tmp_path / "pilot.jsonl"
    report = tmp_path / "measurements.jsonl"
    coverage = tmp_path / "coverage.json"
    coverage.write_text("stale coverage")
    coverage.with_suffix(".md").write_text("stale coverage")
    calls = 0

    def refused(*args: Any, **kwargs: Any) -> dict[str, Any]:
        nonlocal calls
        calls += 1
        if after_off:
            kwargs["store"].append(
                make_record(
                    0,
                    started_at="2026-09-22T00:00:00Z",
                    file_sha256=args[0].sha256,
                    binary_sha256=args[3]["egglog"],
                )
            )
        raise ValueError("resource guard refused to launch a workload: host memory pressure is not normal")

    monkeypatch.setattr(pilot, "__file__", str(tmp_path / "benchmarking/pilot.py"))
    monkeypatch.setattr(pilot, "pilot_workload", refused)
    assert (
        pilot.main(
            [
                "--suite",
                "expanded",
                "--egglog-binary",
                str(binary),
                "--evidence",
                str(evidence),
                "--report",
                str(report),
                "--coverage-output",
                str(coverage),
            ]
        )
        == 2
    )
    assert calls == 1
    assert not evidence.exists()
    cases = json.loads(coverage.read_text())["cases"]
    assert all(w["preparation_status"] == "pending" for case in cases for w in case["workloads"])
    assert not cases[1]["workloads"][0]["measurements"]
    rows = ReportStore(report).records
    snapshot = parse_grouped_report(grouped_report_path(report).read_bytes(), str(report))
    assert len(snapshot.records) == len(rows)
    assert len(rows) == int(after_off)
    assert all(row["status"] == "success" and row["treatment"] == "off" for row in rows)
    assert "stale coverage" not in coverage.with_suffix(".md").read_text()


def test_guard_defers_known_large_admitted_case_without_running(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    from benchmarking.memory_guard import GROUP_LIMIT_BYTES

    selection = write_catalog(tmp_path)
    evidence = tmp_path / "pilot.jsonl"
    record = {
        "identity": admission.pilot_identity(
            selection.files[0], "eggcc", {"egglog": "sha256:binary"}, admission.PilotPolicy(), tmp_path
        ),
        "status": "admitted",
        "reason": None,
        "checks": [{"peak_rss_bytes": GROUP_LIMIT_BYTES + 1}],
    }
    evidence.write_text(json.dumps(record) + "\n")
    target = make_target(binary_sha256="sha256:binary")
    store = ReportStore(tmp_path / "measurements.jsonl")
    for treatment in ("off", "proof-extraction"):
        store.append(
            make_record(
                0,
                started_at="2026-09-22T00:00:00Z",
                file_sha256=selection.files[0].sha256,
                binary_sha256=target.binary_sha256,
                treatment=treatment,
            )
        )
    monkeypatch.delenv("EGGLOG_BENCH_MEMORY_GUARD", raising=False)
    assert pilot.require_suite_admission(selection, (target,), evidence, store=store)[0] == selection.files
    monkeypatch.setenv("EGGLOG_BENCH_MEMORY_GUARD", "1")
    files, _diagnostics, issues = pilot.require_suite_admission(selection, (target,), evidence, store=store)
    assert files == selection.files
    assert "Deferred: pilot peak" in issues[0][1]
    assert len(store.records) == 2
    assert json.loads(evidence.read_text())["status"] == "admitted"


def test_historical_resource_deferral_allows_safe_cases_without_inventing_current_pilots(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: Any
) -> None:
    from benchmarking.memory_guard import GROUP_LIMIT_BYTES

    write_catalog(tmp_path)
    (tmp_path / "alias.egg").write_text("(check (= 2 2))\n")
    selection = suites.resolve_suite("expanded", tmp_path)
    unsafe, safe = selection.files
    binary = tmp_path / "egglog"
    binary.write_text("current binary")
    hashes = {"egglog": pilot.sha256_file(binary)}
    evidence = tmp_path / "pilot.jsonl"
    old = {
        "identity": admission.pilot_identity(
            unsafe, "eggcc", {"egglog": "sha256:old-binary"}, admission.PilotPolicy(), tmp_path
        ),
        "status": "failure",
        "reason": "unexpected SIGKILL; cause unknown",
        "checks": [{"peak_rss_bytes": GROUP_LIMIT_BYTES + 1}],
    }
    previous_line = json.dumps(old) + "\n"
    evidence.write_text(previous_line)
    launched = []

    def admit(file: Any, family: str, *_args: Any, store: ReportStore, **_kwargs: Any) -> dict[str, Any]:
        launched.append(file)
        for treatment in ("off", "proof-extraction"):
            store.append(
                make_record(
                    0,
                    started_at="2026-09-22T00:00:00Z",
                    file_sha256=file.sha256,
                    binary_sha256=hashes["egglog"],
                    treatment=treatment,
                )
            )
        return {
            "identity": admission.pilot_identity(file, family, hashes, admission.PilotPolicy(), tmp_path),
            "status": "admitted",
            "reason": None,
            "checks": [{"peak_rss_bytes": 1024}],
        }

    monkeypatch.setenv("EGGLOG_BENCH_MEMORY_GUARD", "1")
    monkeypatch.setattr(pilot, "__file__", str(tmp_path / "benchmarking/pilot.py"))
    monkeypatch.setattr(pilot, "pilot_workload", admit)
    args = ["--suite", "expanded", "--egglog-binary", str(binary), "--evidence", str(evidence)]
    assert pilot.main(args) == 1
    assert launched == [safe]
    assert evidence.read_text().startswith(previous_line)
    assert len(evidence.read_text().splitlines()) == 2
    before = evidence.read_bytes()
    assert pilot.main(args) == 1
    assert launched == [safe]
    assert evidence.read_bytes() == before
    assert "safety-deferred (reused)" in capsys.readouterr().err
    target = make_target(binary_sha256=hashes["egglog"])
    store = ReportStore(tmp_path / ".reports.jsonl")
    selected, diagnostics, issues = pilot.require_suite_admission(selection, (target,), evidence, store=store)
    assert selected == selection.files
    assert issues[0][0] == unsafe and "prior peak" in issues[0][1]
    assert any("prior peak" in reason for reason in diagnostics)
    coverage = suites.build_coverage(selection, evidence, hashes)
    excluded = coverage["cases"][0]["workloads"][0]
    assert excluded["pilot_status"] == "not-validated"
    assert not excluded["admitted"]
    assert excluded["pilot_reason"] is None
    assert "prior peak" in excluded["collection_reason"]
    assert excluded["collection_reason"] in suites.render_coverage_markdown(coverage)
    monkeypatch.delenv("EGGLOG_BENCH_MEMORY_GUARD")
    files, _, issues = pilot.require_suite_admission(selection, (target,), evidence, store=store)
    assert files == selection.files and not issues
    assert pilot.main([*args, "--refresh"]) == 0
    assert launched == [safe, unsafe, safe]
    monkeypatch.setenv("EGGLOG_BENCH_MEMORY_GUARD", "1")
    assert (
        pilot.require_suite_admission(selection, (target,), evidence, store=ReportStore(tmp_path / ".reports.jsonl"))[0]
        == selection.files
    )
    assert suites.build_coverage(selection, evidence, hashes)["cases"][0]["workloads"][0]["collection_reason"] is None


def test_checked_in_expansion_keeps_the_predeclared_source_population() -> None:
    from collections import Counter

    root = Path(__file__).resolve().parents[1]
    catalog = suites.load_catalog(root)
    assert Counter(case.family for case in catalog.cases) == {
        "math-growth": 100,
        "eggcc": 96,
        "luminal": 7,
        "hardboiled": 77,
        "misaal": 102,
        "churchroad": 23,
        "dialegg": 10,
        "speq": 10,
    }
    published = [case for case in catalog.cases if case.id.startswith("hardboiled-published-")]
    native = [case for case in catalog.cases if case.family == "hardboiled" and case not in published]
    assert len(published) == 42 and len(native) == 35
    assert all(case.provenance["benchmark_selection"]["workloads"] for case in published)
    assert all(case.provenance["benchmark_selection"]["workloads"] == [] for case in native)
    churchroad = [case for case in catalog.cases if case.family == "churchroad"]
    later = [case for case in churchroad if case.id.startswith("churchroad-later-")]
    assert {case.id for case in churchroad if case not in later} == {"churchroad-simple_mul", "churchroad-wide_mul"}
    assert len(later) == 21
    assert all(
        case.status == "captured"
        and case.provenance["complete_reproduction"]["status"] == "complete"
        and case.provenance["benchmark_selection"]["workloads"]
        and case.provenance["scope"] == "artifact-extra"
        and case.provenance["repository"] == "https://github.com/gussmith23/churchroad-evaluation"
        and case.provenance["revision"] == "af615fa460667a08228a7e8f7e3d345b310e39ac"
        and case.provenance["configuration"]["revision"] == case.provenance["revision"]
        for case in later
    )
    math = [case for case in catalog.cases if case.family == "math-growth"]
    assert [case.id for case in math if case.status != "deferred"] == [f"math-growth-{n:03}" for n in range(1, 12)]
    assert not {"herbie", "pointer-analysis"} & set(suites.EXPANDED_FAMILIES)
