"""Exercise measured preparation, terminal outcomes, and family selection."""

from __future__ import annotations

import io
import json
from pathlib import Path
from typing import Any

import pytest
from rich.console import Console

from benchmarking import admission, benchmark, collection, models, pilot, processes, suites, targets
from benchmarking.reports.store import ReportStore

from .report_fixtures import make_record, make_target, make_timing_summary


@pytest.fixture
def prepared_environment(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> tuple[Path, models.ResolvedTarget]:
    """Use a temporary catalog and mocked engine while retaining real cache writes."""

    monkeypatch.chdir(tmp_path)
    (tmp_path / "benchmarks").mkdir()
    (tmp_path / "one.egg").write_text("(check (= 1 1))\n")
    (tmp_path / "benchmarks/catalog.json").write_text(
        json.dumps(
            {
                "families": {"eggcc": {}, "luminal": {}},
                "cases": [
                    {"id": "one", "family": "eggcc", "source": "one", "status": "captured", "workloads": ["one.egg"]},
                    {
                        "id": "alias",
                        "family": "luminal",
                        "source": "alias",
                        "status": "captured",
                        "workloads": ["one.egg"],
                    },
                ],
            }
        )
    )
    binary = tmp_path / "target/release/egglog-experimental"
    binary.parent.mkdir(parents=True)
    binary.write_text("mocked engine")
    monkeypatch.setattr(pilot, "__file__", str(tmp_path / "benchmarking/pilot.py"))
    monkeypatch.setattr(pilot, "git_sha", lambda _root: "test-commit")
    monkeypatch.setattr(pilot, "git_dirty", lambda _root: False)
    monkeypatch.setattr(pilot, "preflight_collection", lambda *_args: None)
    monkeypatch.setattr(benchmark, "__file__", str(tmp_path / "benchmarking/benchmark.py"))
    monkeypatch.setattr(benchmark, "git_root_for_path", lambda _root: tmp_path)
    target = make_target(binary_path=binary, binary_sha256=targets.sha256_file(binary))
    return tmp_path, target


@pytest.mark.parametrize("strict_status", ["success", "failure"])
@pytest.mark.parametrize("treatment", admission.PROOF_TREATMENTS)
def test_screening_rows_count_and_strict_logs_stay_separate(
    prepared_environment: tuple[Path, models.ResolvedTarget],
    monkeypatch: pytest.MonkeyPatch,
    strict_status: str,
    treatment: admission.ProofTreatment,
) -> None:
    root, target = prepared_environment
    calls: list[str] = []

    def measured(
        _binary: Path, _root: Path, _file: models.FileSpec, treatment: str, _timeout: int, _encoding: str
    ) -> collection.ProcessObservation:
        calls.append(treatment)
        return collection.ProcessObservation(
            processes.TimingResult("success", processes.TimingRow(wall_sec=0.2), None), make_timing_summary()
        )

    def strict(_command: Any, _root: Path, prefix: Path, **_kwargs: Any) -> pilot.PilotProcessResult:
        calls.append(prefix.name)
        return pilot.PilotProcessResult(
            "success" if strict_status == "success" else "failure",
            0 if strict_status == "success" else 1,
            9.0,
            10,
            prefix.with_suffix(".stdout"),
            prefix.with_suffix(".stderr"),
            None if strict_status == "success" else "invalid proof",
        )

    monkeypatch.setattr(collection, "run_process", measured)
    monkeypatch.setattr(pilot, "run_bounded_command", strict)
    args = ["--suite", "luminal", "--suite", "eggcc", "--treatment", treatment]
    assert pilot.main(args) == (0 if strict_status == "success" else 1)
    assert calls == ["off", treatment, "proof-testing"]
    store = ReportStore(root / ".reports.jsonl")
    assert [row["treatment"] for row in store.records] == ["off", treatment]
    assert all(row["wall_sec"] == 0.2 for row in store.records)
    evidence = admission.load_pilot_records(root / admission.PILOT_RELATIVE_PATH)
    assert [check["treatment"] for check in evidence[0]["checks"]] == ["proof-testing"]
    selection = suites.resolve_suite(("luminal", "eggcc"), root)
    files, _, issues = pilot.require_suite_admission(selection, (target,), store=store, treatment=treatment)
    assert bool(issues) == (strict_status == "failure")
    plan = collection.build_collection_plan(
        store,
        target,
        (models.BenchmarkEndpoint(target, "off"), models.BenchmarkEndpoint(target, treatment)),
        files,
        30,
        120,
        False,
        True,
        tuple(file for file, _reason in issues),
    )
    assert plan.total_missing_observations == (58 if strict_status == "success" else 0)
    before = store.path.read_bytes()
    assert pilot.main(args) == (0 if strict_status == "success" else 1)
    assert calls == ["off", treatment, "proof-testing"]
    assert store.path.read_bytes() == before


@pytest.mark.parametrize("status", ["failure", "timed-out"])
def test_suite_failure_stops_pair_and_is_terminal_but_positional_keeps_attempt_policy(
    prepared_environment: tuple[Path, models.ResolvedTarget],
    monkeypatch: pytest.MonkeyPatch,
    status: models.Status,
) -> None:
    root, target = prepared_environment
    file = suites.resolve_suite("eggcc", root).files[0]
    store = ReportStore(root / "test.jsonl")
    calls: list[str] = []

    def measured(
        _binary: Path, _root: Path, _file: models.FileSpec, treatment: str, _timeout: int, _encoding: str
    ) -> collection.ProcessObservation:
        calls.append(treatment)
        return collection.ProcessObservation(
            processes.TimingResult(status, processes.TimingRow(), processes.ErrorRow("terminal error")), None
        )

    monkeypatch.setattr(collection, "run_process", measured)
    endpoints = (models.BenchmarkEndpoint(target, "off"), models.BenchmarkEndpoint(target, "proof-extraction"))
    plan = collection.build_collection_plan(store, target, endpoints, (file,), 30, 120, False, True)
    collection.collect_rows(store, plan, 120, Console(file=io.StringIO()))
    assert calls == ["off"]
    assert store.row_count == 1
    assert (
        collection.build_collection_plan(
            store, target, endpoints, (file,), 30, 120, False, True
        ).total_missing_observations
        == 0
    )
    assert (
        collection.build_collection_plan(store, target, endpoints, (file,), 30, 120, False).total_missing_observations
        == 59
    )
    assert (
        collection.build_collection_plan(
            store, target, endpoints, (file,), 1, 120, True, True
        ).total_missing_observations
        == 2
    )
    assert (
        collection.build_collection_plan(
            store, target, endpoints, (file,), 30, 121, False, True
        ).total_missing_observations
        == 60
    )


def test_any_selected_failure_prevents_automatic_topup(
    prepared_environment: tuple[Path, models.ResolvedTarget],
) -> None:
    root, target = prepared_environment
    file = suites.resolve_suite("eggcc", root).files[0]
    store = ReportStore(root / "test.jsonl")
    statuses: tuple[models.Status, ...] = ("timed-out", "success")
    for index, status in enumerate(statuses):
        row = make_record(
            index,
            started_at=f"2026-09-22T00:00:0{index}Z",
            status=status,
            binary_sha256=target.binary_sha256,
            file_sha256=file.sha256,
        )
        store.append(row)
    plan = collection.build_collection_plan(
        store, target, (models.BenchmarkEndpoint(target, "off"),), (file,), 30, 120, False, True
    )
    assert plan.total_missing_observations == 0
    assert plan.runs[0].cached_statuses == ("timed-out", "success")


def test_explicit_force_run_retries_normal_blocker_without_claiming_proof_validity(
    prepared_environment: tuple[Path, models.ResolvedTarget],
    monkeypatch: pytest.MonkeyPatch,
    capsys: Any,
) -> None:
    root, target = prepared_environment
    file = suites.resolve_suite("eggcc", root).files[0]
    store = ReportStore(root / ".reports.jsonl")
    failed = make_record(
        0,
        started_at="2026-09-22T00:00:00Z",
        status="failure",
        binary_sha256=target.binary_sha256,
        file_sha256=file.sha256,
    )
    failed["error_message"] = "normal-mode failure"
    store.append(failed)
    calls: list[str] = []

    def measured(
        _binary: Path, _root: Path, _file: models.FileSpec, treatment: str, _timeout: int, _encoding: str
    ) -> collection.ProcessObservation:
        calls.append(treatment)
        return collection.ProcessObservation(
            processes.TimingResult("success", processes.TimingRow(wall_sec=0.2), None), make_timing_summary()
        )

    monkeypatch.setattr(benchmark, "resolve_targets", lambda groups, *_args: {request: target for request, _ in groups})
    monkeypatch.setattr(benchmark, "preflight_collection", lambda *_args: None)
    monkeypatch.setattr(collection, "run_process", measured)
    args = ["--suite", "eggcc", "--rounds", "1", "--timeout-sec", "120", "--format", "markdown"]
    assert benchmark.main(args) == 0
    assert calls == []
    capsys.readouterr()
    assert benchmark.main([*args, "--force-run"]) == 0
    assert calls == ["off", "proof-extraction"]
    assert "normal-mode failure" in capsys.readouterr().out
    retained = ReportStore(store.path).records
    assert [row["status"] for row in retained] == ["failure", "success", "success"]
    # Successful fresh timings are reusable without a separate correctness pilot.
    assert benchmark.main(args) == 0
    assert "without current preparation" not in capsys.readouterr().err
    assert calls == ["off", "proof-extraction"]


def test_repeated_suites_preserve_catalog_order_and_do_not_change_positionals(
    prepared_environment: tuple[Path, models.ResolvedTarget],
) -> None:
    root, _target = prepared_environment
    selected = suites.resolve_suite(("luminal", "eggcc", "expanded", "eggcc"), root)
    assert [case.id for case in selected.cases] == ["one", "alias"]
    assert len(selected.files) == 1
    args = benchmark.parse_benchmark_args(["--suite", "luminal", "--suite", "eggcc"])
    assert args.suite == ["luminal", "eggcc"] and args.detail == "files"
    assert args.treatment == "proof-extraction"
    assert args.rounds == 10
    assert benchmark.parse_benchmark_args(["eggcc"]).files == ["eggcc"]
    assert benchmark.parse_benchmark_args([]).suite is None
    assert benchmark.parse_benchmark_args([]).treatment == "proofs"
    assert benchmark.parse_benchmark_args([]).rounds == 6
    explicit = benchmark.parse_benchmark_args(["--suite", "eggcc", "--treatment", "proofs", "--rounds", "2"])
    assert explicit.treatment == "proofs" and explicit.rounds == 2


def test_source_blocked_only_suite_renders_census_without_building(
    prepared_environment: tuple[Path, models.ResolvedTarget],
    monkeypatch: pytest.MonkeyPatch,
    capsys: Any,
) -> None:
    root, _target = prepared_environment
    catalog_path = root / "benchmarks/catalog.json"
    catalog = json.loads(catalog_path.read_text())
    for case in catalog["cases"]:
        case.update(status="blocked", workloads=[], reason="source unavailable")
    catalog_path.write_text(json.dumps(catalog))
    monkeypatch.setattr(benchmark, "resolve_targets", lambda *_args: pytest.fail("no runnable source needs a build"))
    assert benchmark.main(["--suite", "eggcc", "--format", "markdown"]) == 0
    assert "source unavailable" in capsys.readouterr().out


@pytest.mark.parametrize("treatment", admission.PROOF_TREATMENTS)
def test_fresh_host_stop_halts_but_later_invocation_skips_it_and_prepares_other_cases(
    prepared_environment: tuple[Path, models.ResolvedTarget],
    monkeypatch: pytest.MonkeyPatch,
    treatment: admission.ProofTreatment,
) -> None:
    root, _target = prepared_environment
    (root / "two.egg").write_text("(check (= 2 2))\n")
    catalog_path = root / "benchmarks/catalog.json"
    catalog = json.loads(catalog_path.read_text())
    catalog["cases"][1]["workloads"] = ["two.egg"]
    catalog_path.write_text(json.dumps(catalog))
    calls: list[tuple[str, str]] = []

    def measured(
        _binary: Path,
        _root: Path,
        file: models.FileSpec,
        endpoint_treatment: str,
        _timeout: int,
        _encoding: str,
    ) -> collection.ProcessObservation:
        calls.append((file.display_path, endpoint_treatment))
        if file.display_path == "one.egg" and endpoint_treatment == treatment:
            return collection.ProcessObservation(
                processes.TimingResult(
                    "failure",
                    processes.TimingRow(),
                    processes.ErrorRow("resource guard stopped workload: host memory pressure is not normal"),
                    resource_stopped=True,
                ),
                None,
            )
        return collection.ProcessObservation(
            processes.TimingResult("success", processes.TimingRow(wall_sec=0.2), None), make_timing_summary()
        )

    def strict(_command: Any, _root: Path, prefix: Path, **_kwargs: Any) -> pilot.PilotProcessResult:
        return pilot.PilotProcessResult("success", 0, 0.1, 10, prefix, prefix, None)

    monkeypatch.setattr(collection, "run_process", measured)
    monkeypatch.setattr(pilot, "run_bounded_command", strict)
    args = ["--suite", "expanded", "--treatment", treatment]
    assert pilot.main(args) == 2
    assert calls == [("one.egg", "off"), ("one.egg", treatment)]
    assert pilot.main(args) == 1
    assert calls == [
        ("one.egg", "off"),
        ("one.egg", treatment),
        ("two.egg", "off"),
        ("two.egg", treatment),
    ]
    store = ReportStore(root / ".reports.jsonl")
    assert store.row_count == 4
    assert store.records[1]["status"] == "failure"
    assert "host memory pressure" in str(store.records[1]["error_message"])


def test_suite_build_is_guarded_and_single_job(
    prepared_environment: tuple[Path, models.ResolvedTarget],
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from dataclasses import replace

    from benchmarking.memory_guard import MemoryGuard

    root, target = prepared_environment
    events: list[Any] = []

    class Guard:
        reason = None

        def start(self, pid: int) -> None:
            events.append(("guard", pid))

        def close(self) -> None:
            events.append("close")

    class Process:
        pid = 123

        def wait(self) -> int:
            events.append("wait")
            return 0

    def build(args: list[str], **kwargs: Any) -> Process:
        assert args == ["cargo", "build", "--release", "-p", "egglog-experimental", "--jobs", "1"]
        assert kwargs["start_new_session"] is True
        events.append("build")
        return Process()

    monkeypatch.setenv("EGGLOG_BENCH_MEMORY_GUARD", "1")
    monkeypatch.setattr(MemoryGuard, "from_environment", lambda: Guard())
    monkeypatch.setattr(targets.subprocess, "Popen", build)
    monkeypatch.setattr(processes, "terminate_process_group", lambda _process: events.append("cleanup"))
    path, identity = targets.build_target(replace(target.row, path=str(root)), Console(file=io.StringIO()))
    assert path == target.binary_path and identity == target.binary_sha256
    assert events == ["build", ("guard", 123), "wait", "close", "cleanup"]
