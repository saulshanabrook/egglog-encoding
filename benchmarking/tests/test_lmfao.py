"""Executable root/pushdown/sharing choices preserve natural-join bag queries."""

from __future__ import annotations

import itertools
import json
import os
import signal
import subprocess
import sys
import time
from collections import Counter, defaultdict
from contextlib import suppress
from fractions import Fraction
from pathlib import Path
from types import SimpleNamespace
from typing import Any

import pytest

from benchmarking.lmfao import cli, model
from benchmarking.lmfao.optimizer import extractor_path, seconds_summary

ROOT = Path(__file__).resolve().parents[2]
QUERIES = [
    model.Query(),
    model.Query((), ("unit_sales",)),
    model.Query((), ("unit_sales", "oilprize")),
    model.Query(("family",)),
    model.Query(("family",), ("unit_sales",)),
    model.Query(("city",), ("oilprize", "oilprize")),
]


def join(tables: list[list[dict[str, Any]]]) -> list[dict[str, Any]]:
    result: list[dict[str, Any]] = []
    for rows in itertools.product(*tables):
        merged: dict[str, Any] = {}
        for row in rows:
            if any(merged[k] != v for k, v in row.items() if k in merged):
                break
            merged.update(row)
        else:
            result.append(merged)
    return result


def evaluate(plan: dict[str, Any], data: dict[str, list[dict[str, Any]]]) -> list[dict[tuple[Any, ...], Fraction]]:
    attrs, schema = model.WORKLOAD.attributes, model.WORKLOAD.relations
    names, tables, functions = [a for a, _ in attrs], list(schema), model.WORKLOAD.functions
    computed: dict[int, list[dict[tuple[Any, ...], Fraction]]] = {}

    def view(i: int) -> list[dict[tuple[Any, ...], Fraction]]:
        if i in computed:
            return computed[i]
        v = plan["views"][i]
        columns = []
        for aggregate in v["aggregates"]:
            inputs = [data[tables[v["origin"]]]]
            for j, (child, col) in enumerate(aggregate["incoming"]):
                keys = [names[k] for k in plan["views"][child]["keys"]]
                inputs.append(
                    [
                        {**dict(zip(keys, key, strict=True)), f"weight{j}": weight}
                        for key, weight in view(child)[col].items()
                    ]
                )
            result: dict[tuple[Any, ...], Fraction] = defaultdict(Fraction)
            for row in join(inputs):
                weight = Fraction(1)
                for f in aggregate["functions"]:
                    name, power = functions[f]
                    weight *= row[name] ** power
                for j in range(len(aggregate["incoming"])):
                    weight *= row[f"weight{j}"]
                result[tuple(row[names[k]] for k in v["keys"])] += weight
            columns.append(result)
        computed[i] = columns
        return columns

    return [view(o["view"])[o["aggregate"]] for o in plan["outputs"]]


@pytest.fixture(scope="module")
def extractor_binary() -> Path:
    subprocess.run(["cargo", "build", "--locked", "-p", "lmfao-extract"], cwd=ROOT, check=True)
    return extractor_path("debug")


@pytest.mark.parametrize("target", [None, "custom-target", "/tmp/lmfao-custom-target"])
def test_extractor_path_honors_cargo_target_dir(target: str | None, monkeypatch: pytest.MonkeyPatch) -> None:
    if target is None:
        monkeypatch.delenv("CARGO_TARGET_DIR", raising=False)
    else:
        monkeypatch.setenv("CARGO_TARGET_DIR", target)
    assert extractor_path("release") == ROOT / (target or "target") / "release/lmfao-extract"


def test_fixed_workload_is_original_covariance_configuration() -> None:
    assert len(model.WORKLOAD.queries) == 140
    assert Counter(len(q.groups) for q in model.WORKLOAD.queries) == {0: 10, 1: 52, 2: 78}
    assert len(model.WORKLOAD.relations) == 6


def test_cli_limits(tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]) -> None:
    argv = ["--data", str(tmp_path), "--backend", str(tmp_path / "multifaq"), "--output-dir", str(tmp_path / "out")]
    args = cli.parse_args([*argv, "--rounds", "1", "--dag-timeout", "2", "--policy-file", "campaign.json"])
    assert args.samples == 1 and args.dag_timeout == 2
    assert args.policy_file == Path("campaign.json").resolve()
    for value in ["0", "-1", "nan", "inf"]:
        with pytest.raises(SystemExit):
            cli.main([*argv, "--dag-timeout", value])
    for option in ("--rounds", "--rewrite-rounds", "--timeout-sec", "--jobs"):
        with pytest.raises(SystemExit):
            cli.main([*argv, option, "0"])
    with pytest.raises(SystemExit):
        cli.main([*argv, "--report", "-"])
    monkeypatch.delattr(os, "sched_setaffinity", raising=False)
    with pytest.raises(SystemExit):
        cli.main([*argv, "--cpu", "0"])
    assert "--cpu is not supported on this platform" in capsys.readouterr().err
    assert seconds_summary([]) is None


def test_optimizer_report_keeps_failures_and_timing_scopes() -> None:
    from benchmarking.lmfao.optimizer import summarize_optimizer
    from benchmarking.tests.report_fixtures import make_record, make_timing_summary

    good = make_record(0, started_at="2026-11-06T00:00:00Z", wall_sec=2.0, timing_summary=make_timing_summary())
    failure = make_record(1, started_at="2026-11-06T00:00:01Z", status="timed-out", timeout_sec=60)
    result = summarize_optimizer([good, failure], 64, 3, "missing 1 row(s)")
    assert result["rewrite_round_budget"] == 64 and result["completed_samples"] == 1
    assert result["process_seconds"]["mean"]["point"] == 2
    assert result["ruleset_work_seconds"]["mean"]["point"] == 0.8
    assert result["failures"] == [failure] and result["issue"]


def test_proof_replay_uses_the_shared_store_and_selected_plan_identity(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    from benchmarking import collection, processes
    from benchmarking.lmfao.optimizer import OptimizerCollection, collect_replays
    from benchmarking.reports.store import ReportStore
    from benchmarking.targets import sha256_file
    from benchmarking.tests.report_fixtures import make_target, make_timing_summary

    store = ReportStore(tmp_path / "cache.jsonl")
    target = make_target(binary_path=tmp_path / "engine")
    selected = OptimizerCollection({}, {}, store, target)
    source = tmp_path / "proof.egg"
    source.write_text("(check (= 1 1))")
    launched = []

    def observe(*args: Any, **kwargs: Any) -> Any:
        launched.append(args)
        return collection.ProcessObservation(
            processes.TimingResult("success", processes.TimingRow(wall_sec=2, max_rss_bytes=1024**2), None),
            make_timing_summary(),
            {
                "schema_version": 1,
                "success": True,
                "check_requests": 1,
                "extraction_requests": 0,
                "produced_certificates": 1,
                "verified_certificates": 1,
            }
            if kwargs.get("proof_summary")
            else None,
        )

    monkeypatch.setattr(collection, "preflight_collection", lambda *_: None)
    monkeypatch.setattr(collection, "run_process", observe)
    first = collect_replays(selected, source, 2, 900, 16 * 1024**3, 192)
    assert len(launched) == store.row_count == 5
    assert set(first) == {"slotted", "slotted-proof-extraction"}
    assert {r["input_sha256"] for r in first.values()} == {sha256_file(source)}
    assert {r["binary_sha256"] for r in first.values()} == {target.binary_sha256}
    assert all(r["completed_samples"] == 2 and not r["failures"] for r in first.values())
    assert collect_replays(selected, source, 2, 900, 16 * 1024**3, 192) == first
    assert len(launched) == store.row_count == 5
    source.write_text("(check (= 2 2))")
    second = collect_replays(selected, source, 2, 900, 16 * 1024**3, 192)
    assert len(launched) == store.row_count == 10
    assert second["slotted"]["input_sha256"] != first["slotted"]["input_sha256"]


@pytest.mark.parametrize("missing", ["export", "import"])
def test_backend_rejects_missing_export_or_import(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, missing: str
) -> None:
    from benchmarking.lmfao import backend

    def fake_command(args: list[str], directory: Path, log: str, **kwargs: Any) -> float:
        (directory / log).write_text("ordinary compiler; ignored adapter variables\n")
        if missing != "export":
            cli.write_json(directory / "workload.json", model.WORKLOAD.document)
        return 0.0

    monkeypatch.setattr(backend, "command", fake_command)
    monkeypatch.setattr(backend, "optimize", lambda config, source, destination: destination.write_text("{}"))
    output = tmp_path / "out"
    output.mkdir()
    (output / "proof.egg").write_text("stale selected plan")
    with pytest.raises(ValueError, match="did not export" if missing == "export" else "did not acknowledge"):
        backend.generate(tmp_path / "multifaq", tmp_path, output, {})
    assert not (output / "proof.egg").exists()


@pytest.mark.parametrize("mode", ["original", "paper", "egraph"])
def test_generation_accounts_for_export_optimizer_and_import(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, mode: str
) -> None:
    from benchmarking.lmfao import backend

    now = 0.0
    calls = []
    monkeypatch.setattr(backend, "time", SimpleNamespace(perf_counter=lambda: now))
    monkeypatch.setenv("LMFAO_STALE_SETTING", "must be removed")

    def command(args: list[str], directory: Path, log: str, *, env: dict[str, str], **kwargs: Any) -> float:
        nonlocal now
        assert "LMFAO_STALE_SETTING" not in env
        calls.append(log)
        cli.write_json(directory / "workload.json", model.WORKLOAD.document)
        if log == "export.log":
            assert env["LMFAO_EXPORT_ONLY"] == "1"
            now += 2
        else:
            assert "LMFAO_EXPORT_ONLY" not in env
            if mode == "egraph":
                assert Path(env["LMFAO_IMPORT_PLAN"]).read_text() == "selected plan"
            cli.write_json(directory / "plan.json", {})
            (directory / "compiler-data.out").write_text("compiler counts")
            (directory / log).write_text(
                "LMFAO imported selected DAG: 1 views\nLMFAO paper coverage roots: 140 queries\n"
            )
            now += 3
        return 0.0  # generate measures the full preparation span, not this return value.

    def optimize(settings: dict[str, Any], source: Path, destination: Path) -> None:
        nonlocal now
        assert json.loads(source.read_text()) == model.WORKLOAD.document
        destination.write_text("selected plan")
        now += 5

    monkeypatch.setattr(backend, "command", command)
    monkeypatch.setattr(backend, "optimize", optimize)
    result = backend.generate(
        tmp_path / "multifaq",
        tmp_path,
        tmp_path / "out",
        {} if mode == "egraph" else None,
        root_policy="paper" if mode == "paper" else None,
    )
    assert result["generation_seconds"] == (10 if mode == "egraph" else 3)
    assert calls == (["export.log", "generate.log"] if mode == "egraph" else ["generate.log"])


def test_cpp_timing_retains_whole_process_and_upstream_scope(tmp_path: Path) -> None:
    from benchmarking.lmfao import backend

    program = tmp_path / "lmfao"
    program.write_text('#!/bin/sh\nprintf "Data loading: 9ms.\\nData sorting: 2ms.\\nData process: 37ms.\\n"\n')
    program.chmod(0o755)
    row = backend.execute(tmp_path, 0, 5)
    assert row["process_seconds"] > 0
    assert row["computation_seconds"] == 0.037
    assert (tmp_path / "run-0.log").read_text().endswith("Data process: 37ms.\n")


@pytest.mark.parametrize("nested_optimizer", [False, True])
def test_backend_timeout_stops_optimizer_and_compiler_children(tmp_path: Path, nested_optimizer: bool) -> None:
    from benchmarking.lmfao import backend

    script = (
        "import subprocess, sys, time; from pathlib import Path; "
        "child = subprocess.Popen([sys.executable, '-c', 'import time; time.sleep(60)']); "
        "Path('child.pid').write_text(str(child.pid)); print('started', flush=True); time.sleep(60)"
    )

    def invoke() -> None:
        if nested_optimizer:
            extractor = tmp_path / "extractor"
            extractor.write_text(f"#!{sys.executable}\n" + script + "\n")
            extractor.chmod(0o755)
            backend.optimize(
                dict(
                    rewrite_rounds=192,
                    treatment="slotted",
                    extractor=str(extractor),
                    timeout=2,
                    dag_timeout=5,
                    memory_limit_bytes=None,
                ),
                model.FIXTURES / "workload.json",
                tmp_path / "plan.json",
            )
        else:
            backend.command([sys.executable, "-c", script], tmp_path, "command.log", timeout=2)

    try:
        with pytest.raises(RuntimeError, match="failed; see") as error:
            invoke()
        assert isinstance(error.value.__cause__, subprocess.TimeoutExpired)
        if not nested_optimizer:
            assert (tmp_path / "command.log").read_text() == "started\n"
        pid = int((tmp_path / "child.pid").read_text())
        deadline = time.monotonic() + 2
        while time.monotonic() < deadline:
            state = subprocess.run(
                ["ps", "-o", "state=", "-p", str(pid)], capture_output=True, text=True, check=False
            ).stdout.strip()
            if not state or state.startswith("Z"):
                break
            time.sleep(0.01)
        else:
            pytest.fail("backend descendant survived timeout")
    finally:
        if (tmp_path / "child.pid").exists():
            with suppress(ProcessLookupError):
                os.kill(int((tmp_path / "child.pid").read_text()), signal.SIGKILL)


@pytest.mark.parametrize("defer_debruijn", [False, True])
def test_pipeline_charges_optimization_once_and_excludes_validation_and_diagnostics(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str], defer_debruijn: bool
) -> None:
    monkeypatch.delattr(os, "sched_getaffinity", raising=False)
    now = 0.0

    def spend(seconds: float) -> None:
        nonlocal now
        now += seconds

    monkeypatch.setattr(cli, "time", SimpleNamespace(perf_counter=lambda: now))
    documents: dict[str, Any] = {"slotted": {"treatment": "slotted"}, "debruijn": {"treatment": "off"}}
    if defer_debruijn:
        del documents["debruijn"]

    def collect(output: Path, *args: Any, **kwargs: Any) -> cli.OptimizerCollection:
        from benchmarking.reports.store import ReportStore
        from benchmarking.tests.report_fixtures import make_target

        spend(999)
        report: dict[str, Any] = {
            "optimizer": {
                label: {"process_seconds": seconds_summary([999, 999]), "completed_samples": 2} for label in documents
            },
            "rewrite_round_budget": 192,
            "optimizer_memory_limit_bytes": 16 * 1024**3,
            "extractor_path": "/lmfao-extract",
        }
        if defer_debruijn:
            report["optimizer"]["debruijn"] = {"issue": "excluded (resource): local host-pressure stop"}
        return cli.OptimizerCollection(documents, report, ReportStore(tmp_path / "cache.jsonl"), make_target())

    def collect_replays(collection: Any, source: Path, samples: int, timeout: int, *args: Any) -> dict[str, Any]:
        assert source.read_text().endswith("(check (= input selected_batch))\n")
        assert samples == 2 and timeout == 3 * cli.DEFAULT_TIMEOUT_SEC
        spend(5000)
        collection.report["proof_replay_validation"] = {
            "status": "passed",
            "issue": None,
            "observation": None,
            "summary": {
                "schema_version": 1,
                "success": True,
                "check_requests": 140,
                "extraction_requests": 0,
                "produced_certificates": 140,
                "verified_certificates": 140,
            },
        }
        return {
            mode: {
                "requested_samples": 2,
                "completed_samples": 2,
                "issue": None,
                "failures": [],
                "process_seconds": seconds_summary([seconds, seconds + 2]),
                "peak_rss_mib": seconds_summary([1024, 1026]),
            }
            for mode, seconds in [("slotted", 100), ("slotted-proof-extraction", 400)]
        }

    class Database:
        def close(self) -> None:
            spend(1)

    def load(directory: Path) -> tuple[Database, dict[str, Any]]:
        assert all((tmp_path / "out" / label / "plan.json").exists() for label in documents)
        spend(10)
        return Database(), {"input_rows": {"Sales": 2}}

    def oracle(db: Database) -> list[Any]:
        spend(2000)
        return []

    def generate(compiler: Path, data: Path, directory: Path, optimizer: Any, **kwargs: Any) -> dict[str, Any]:
        directory.mkdir()
        plan = {
            "views": [{"origin": 0, "destination": 0, "keys": [], "aggregates": [{"functions": [], "incoming": []}]}],
            "outputs": [{"view": 0, "aggregate": 0, "root": 0}] * len(model.WORKLOAD.queries),
        }
        cli.write_json(directory / "plan.json", plan)
        elapsed = 2 if optimizer is None else (27 if optimizer["treatment"] == "slotted" else 29)
        cli.write_json(
            directory / "extraction.json", {"estimated_cost": 3, "phases_seconds": {"rewriting": elapsed - 2}}
        )
        spend(elapsed)
        return {"generation_seconds": elapsed}

    def compile(directory: Path, **kwargs: Any) -> dict[str, Any]:
        (directory / "lmfao").touch()
        spend(40)
        return {"compilation_seconds": 40}

    def validate(*args: Any, **kwargs: Any) -> dict[str, Any]:
        spend(1000)
        return {"queries_checked": 140}

    def execute(directory: Path, repeat: int, timeout: int) -> dict[str, float]:
        elapsed = (1.0 if directory.name == "original" else 0.5) + repeat / 10
        spend(elapsed)
        return {"process_seconds": elapsed, "computation_seconds": elapsed / 2}

    monkeypatch.setattr(cli, "collect_optimizers", collect)
    monkeypatch.setattr(cli, "verify_backend", lambda _: {"lmfao_commit": model.COMMIT})
    monkeypatch.setattr(cli, "collect_replays", collect_replays)
    monkeypatch.setattr(cli, "load_data", load)
    monkeypatch.setattr(cli, "reference_results", oracle)
    monkeypatch.setattr(cli.backend, "generate", generate)
    monkeypatch.setattr(cli.backend, "compile", compile)
    monkeypatch.setattr(cli.backend, "validate", validate)
    monkeypatch.setattr(cli.backend, "execute", execute)
    compiler = tmp_path / "multifaq"
    compiler.touch()
    output = tmp_path / "out"
    assert (
        cli.main(
            [
                "--data",
                str(tmp_path),
                "--backend",
                str(compiler),
                "--output-dir",
                str(output),
                "--rounds",
                "2",
                "--format",
                "json",
            ]
        )
        == 0
    )
    report = json.loads(capsys.readouterr().out)
    assert report["metadata"]["cpu_affinity"] is None
    assert report == json.loads((output / "pipeline.json").read_text())
    replay = (output / "slotted" / "proof.egg").read_text()
    assert replay.startswith((model.FIXTURES / "inputs/slotted.egg").read_text())
    assert replay.count("(check (= input selected_batch))") == 1
    assert replay.endswith("(check (= input selected_batch))\n")
    costs = report["accounted_pipeline"]
    assert costs["original"]["one_time_phase_sum_seconds"] == 42
    assert costs["slotted"]["one_time_phase_sum_seconds"] == 67
    if not defer_debruijn:
        assert costs["debruijn"]["one_time_phase_sum_seconds"] == 69
        assert costs["debruijn"]["execution_label"] == "slotted"
    assert costs["original"]["optimization_and_generation_seconds"] == 2
    assert costs["slotted"]["optimization_and_generation_seconds"] == 27
    assert costs["slotted"]["compilation_seconds"] == 40
    assert report["metadata"]["validation_preparation_seconds"] == 2011
    assert len(report["builds"]) == (3 if defer_debruijn else 4) and len(report["validation"]) == 3
    if defer_debruijn:
        assert "debruijn" not in report["accounted_pipeline"] and "debruijn" not in report["builds"]
    else:
        assert "compilation_seconds" not in report["builds"]["debruijn"]
    assert "not a measured end-to-end" in report["phase_scope"]
    comparison = (output / "comparison.md").read_text()
    assert "Slotted egglog" in comparison and "Ordinary egglog (de Bruijn)" in comparison
    if defer_debruijn:
        assert "Ordinary egglog (de Bruijn) (excluded (resource): local host-pressure stop)" in comparison
    assert "27.000 | 40.000 | 0.524 [" in comparison
    assert "Samples" not in comparison and "Full planning (s)" in comparison
    assert "requests 2 observations" in comparison
    assert len([line for line in comparison.splitlines() if line.startswith("| Method")]) == 1
    assert all(line.count("|") == 7 for line in comparison.splitlines() if line.startswith("|"))
    assert "Slotted replay (proof production) | 401.000 [" in comparison
    assert "Slotted replay (proofs off) | 101.000 [" in comparison
    from benchmarking.lmfao.report import paper_results

    published = paper_results(report)
    assert len(published) == 5
    assert r"\csname egglogfigure@lmfao/rounds\endcsname{2}" in published["lmfao.numbers.tex"]
    assert json.loads(published["lmfao.results.json"]) == report
    table = published["lmfao.table.tex"]
    assert "Samples" not in table and r"\begin{tabular}{lrrrrr}" in table
    assert r"27.000 & 40.000 & \shortstack{0.524" in table
    assert published["lmfao.md"] == comparison
    checked = report["proof_replay"]["slotted-proof-extraction"]
    checked["failures"] = [{"status": "failure"}]
    with pytest.raises(ValueError, match="proof replay"):
        paper_results(report)
    checked.update(
        completed_samples=0, process_seconds=None, peak_rss_mib=None, failures=[{"status": "memory-limited"}]
    )
    assert "proof production) (memory-limited)" in paper_results(report)["lmfao.md"]
    del report["proof_replay"]["slotted-proof-extraction"]
    with pytest.raises(ValueError, match="proof replay"):
        paper_results(report)
    # A failed extraction must stop before publishing any paper artifacts.
    report["optimizer"]["slotted"]["pipeline_issue"] = "extractor failed"
    with pytest.raises(ValueError, match="incomplete"):
        paper_results(report)


def test_optimizer_rejects_workload_drift_before_rewriting(tmp_path: Path) -> None:
    from benchmarking.lmfao.backend import optimize

    source = tmp_path / "workload.json"
    changed = {**model.WORKLOAD.document, "root": "1"}
    source.write_text(json.dumps(changed))
    with pytest.raises(ValueError, match="frontend differs"):
        optimize({}, source, tmp_path / "plan.json")
    assert not (tmp_path / "plan.json").exists()


def test_report_distinguishes_replication_and_resource_failures() -> None:
    from benchmarking.lmfao.report import comparison_markdown

    result = comparison_markdown(
        {
            "rewrite_round_budget": 192,
            "optimizer": {"debruijn": {"failures": [{"status": "memory-limit"}]}},
            "optimizer_memory_limit_bytes": 16 * 1024**3,
            "accounted_pipeline": {},
            "execution": {"original": {"computation_seconds": seconds_summary([1])}},
        }
    )
    assert "LMFAO configured roots" in result
    assert "LMFAO + root heuristic" in result
    assert "Ordinary egglog (de Bruijn) (memory-limit)" in result
    assert "not the paper's full dataset (127M joined tuples)" in result
    assert "our implementation" in result and "allocator/address-space cap" in result


def test_frozen_inputs_match_generator_and_collection_does_not_regenerate(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    from benchmarking.lmfao import program
    from benchmarking.lmfao.optimizer import optimizer_inputs

    for mode in ("slotted", "debruijn"):
        assert (program.INPUTS / f"{mode}.egg").read_text() == (
            ";;; GENERATED: python -m benchmarking.lmfao.program\n" + program.program(mode)
        )
    monkeypatch.setattr(program, "program", lambda *a, **kw: pytest.fail("collection regenerated input"))
    files = optimizer_inputs(tmp_path, program.DEFAULT_ROUNDS)
    assert {f.absolute_path.parent for f in files.values()} == {program.INPUTS}
    assert not list(tmp_path.iterdir())


def test_campaign_policy_skips_only_debruijn_and_preserves_cache_identity(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    from benchmarking.collection import plan_collection
    from benchmarking.lmfao import optimizer, program
    from benchmarking.models import BenchmarkEndpoint
    from benchmarking.reports.store import CacheKey, ReportStore
    from benchmarking.targets import sha256_file
    from benchmarking.tests.report_fixtures import make_record, make_target

    policy = tmp_path / "campaign.json"
    rule = {
        "file": "lmfao/inputs/debruijn.egg",
        "treatments": ["off"],
        "kind": "resource",
        "reason": "local host-pressure stop",
        "evidence": "local guard packet; no allocator-limit claim",
    }
    policy.write_text(json.dumps([rule]))
    defaults = optimizer.optimizer_inputs(tmp_path, program.DEFAULT_ROUNDS)
    files = optimizer.optimizer_inputs(tmp_path, program.DEFAULT_ROUNDS, policy_file=policy)
    target = make_target()
    store = ReportStore(tmp_path / "cache.jsonl")
    requests = optimizer.optimizer_requests(files, target.request, 16 * 1024**3, threads=4)
    pending = plan_collection(store, requests, {target.request: target}, 3, 500, False)
    assert [(run.treatment, run.missing_observations) for plan in pending for run in plan.runs] == [("slotted", 3)]
    for mode, treatment in optimizer.MODES.items():
        endpoint = BenchmarkEndpoint(target.row, target.binary_sha256, treatment, 16 * 1024**3, 4)
        assert CacheKey.for_endpoint(endpoint, files[mode]) == CacheKey.for_endpoint(endpoint, defaults[mode])
        assert not defaults[mode].exclusions
    assert files["slotted"].exclusions == ()
    assert files["debruijn"].exclusion_for("slotted", memory_limit_bytes=16 * 1024**3) is None
    for index in range(3):
        store.append(
            make_record(
                index,
                started_at=f"2026-11-12T00:00:0{index}Z",
                file_sha256=files["slotted"].sha256,
                treatment="slotted",
                threads=4,
            )
        )
    extractor = tmp_path / "extractor"
    extractor.touch()
    monkeypatch.setattr(optimizer.subprocess, "run", lambda *a, **kw: None)
    monkeypatch.setattr(optimizer, "extractor_path", lambda _: extractor)
    selected = optimizer.optimizer_report(
        tmp_path, store, target, files, 3, 500, 16 * 1024**3, program.DEFAULT_ROUNDS, 4, policy_file=policy
    )
    assert selected.successful == {"slotted": {"treatment": "slotted"}}
    assert selected.report["optimizer"]["debruijn"]["issue"] == "excluded (resource): local host-pressure stop"
    assert selected.report["optimizer"]["debruijn"]["completed_samples"] == 0
    provenance = selected.report["optimizer_policy"]
    assert provenance["path"] == str(policy) and provenance["sha256"] == sha256_file(policy)
    assert provenance["exclusions"]["debruijn"][0]["evidence"] == rule["evidence"]
    assert json.loads((tmp_path / "optimizer-summary.json").read_text()) == selected.report
    policy.write_text(json.dumps([rule | {"kind": "invalid"}]))
    with pytest.raises(ValueError, match="invalid benchmark exclusion"):
        optimizer.optimizer_inputs(tmp_path, program.DEFAULT_ROUNDS, policy_file=policy)


def test_lmfao_intervals_use_sample_means_and_fieller_ratios() -> None:
    from scipy import stats

    from benchmarking.lmfao.report import execution_ratios
    from benchmarking.reports.analysis import _ratio_estimate, _sample_estimate

    a, b = [1.0, 2.0, 2.5], [0.6, 0.8, 0.9]
    critical = float(stats.t.ppf(0.975, 2))
    result = execution_ratios(
        {
            "execution": {
                label: {"computation_seconds": seconds_summary(values)}
                for label, values in [("original", a), ("slotted", b)]
            }
        }
    )
    expected = _ratio_estimate(_sample_estimate(a, None, critical), _sample_estimate(b, None, critical), critical)
    assert result["slotted"] == expected.estimate._asdict()
    assert result["original"] == {"point": 1, "ci_low": None, "ci_high": None}
    single = seconds_summary([2])
    assert single is not None
    assert single["mean"] == {"point": 2, "ci_low": None, "ci_high": None}
