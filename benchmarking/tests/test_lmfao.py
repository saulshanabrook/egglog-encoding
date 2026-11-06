"""Executable root/pushdown/sharing choices preserve natural-join bag queries."""

from __future__ import annotations

import itertools
import json
import os
import random
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
from benchmarking.native_memory import native_memory_command

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


@pytest.mark.parametrize(
    ("mode", "binding"),
    [
        ("single-root", "slotted"),
        ("roots", "slotted"),
        ("shared", "slotted"),
        ("shared", "named"),
        ("shared", "canonical"),
    ],
)
def test_extracted_dag_preserves_original_queries(
    mode: str, binding: str, extractor_binary: Path, tmp_path: Path
) -> None:
    from benchmarks.reproduction.slotted.lmfao import ordinary, workload

    plans = []
    roots = ["Sales"] if mode == "single-root" else list(model.WORKLOAD.relations)
    for root in [None, *roots]:
        source = tmp_path / "input.egg"
        program = workload(mode, qs=QUERIES, roots=None if root is None else [root]).program
        source.write_text(program if binding == "slotted" else ordinary(program, canonical=binding == "canonical"))
        destination = tmp_path / "plan.json"
        command, env = native_memory_command(
            [str(extractor_binary), "slotted" if binding == "slotted" else "off", str(source), str(destination), "5"],
            os.environ,
        )
        subprocess.run(command, env=env, check=True, timeout=30)
        plan = json.loads(destination.read_text())
        assert len(plan["outputs"]) == len(QUERIES)
        if root is not None:
            assert {o["root"] for o in plan["outputs"]} == {list(model.WORKLOAD.relations).index(root)}
        assert json.loads((tmp_path / "extraction.json").read_text())["solver"]["optimal"]
        plans.append(plan)
    rng = random.Random(804)
    for trial in range(8):
        data = {}
        for name, fields in model.WORKLOAD.relations.items():
            rows = [
                {
                    k: Fraction(rng.randrange(-3, 4), 2)
                    if k in {"unit_sales", "oilprize", "transactions"}
                    else rng.randrange(2)
                    for k in fields
                }
                for _ in range(trial % 4 + 1)
            ]
            data[name] = rows + [rows[0]]  # Preserve bag multiplicities in every relation.
        expected = []
        for q in QUERIES:
            answer: dict[tuple[Any, ...], Fraction] = defaultdict(Fraction)
            for row in join(list(data.values())):
                weight = Fraction(1)
                for f in q.factors:
                    weight *= row[f]
                answer[tuple(row[k] for k in q.groups)] += weight
            expected.append(answer)
        for plan in plans:
            assert evaluate(plan, data) == expected


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


def test_frozen_inputs_match_upstream_frontend_export() -> None:
    from benchmarks.reproduction.slotted.lmfao import frozen

    for folder, queries in [("inputs", None), ("correctness", QUERIES)]:
        for name, contents in frozen(qs=queries).items():
            assert (model.FIXTURES / folder / name).read_text() == contents


def test_cli_limits(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    calls: list[Any] = []
    monkeypatch.setattr(cli, "run", calls.append)
    argv = ["--data", str(tmp_path), "--backend", str(tmp_path / "multifaq"), "--output-dir", str(tmp_path / "out")]
    assert cli.main([*argv, "--rounds", "1", "--dag-timeout", "2"]) == 0
    assert calls[0].samples == 1 and calls[0].dag_timeout == 2
    for value in ["0", "-1", "nan", "inf"]:
        with pytest.raises(SystemExit):
            cli.main([*argv, "--dag-timeout", value])
    for name, value in [("treatment", "slotted"), ("variant", "shared"), ("binding-control", "named")]:
        with pytest.raises(SystemExit):
            cli.main([*argv, f"--{name}", value, f"--{name}", value])
    assert seconds_summary([]) is None


def test_optimizer_report_keeps_failures_and_timing_scopes() -> None:
    from benchmarking.lmfao.optimizer import summarize_optimizer
    from benchmarking.tests.report_fixtures import make_record, make_timing_summary

    good = make_record(0, started_at="2026-11-06T00:00:00Z", wall_sec=2.0, timing_summary=make_timing_summary())
    failure = make_record(1, started_at="2026-11-06T00:00:01Z", status="timed-out", timeout_sec=60)
    result = summarize_optimizer([good, failure], 64, 3, "missing 1 row(s)")
    assert result["rewrite_round_budget"] == 64 and result["completed_samples"] == 1
    assert result["process_seconds"]["median_seconds"] == 2
    assert result["ruleset_work_seconds"]["median_seconds"] == 0.8
    assert result["failures"] == [failure] and result["issue"]


def test_backend_requires_explicit_import_acknowledgement(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    from benchmarking.lmfao import backend

    def fake_command(args: list[str], directory: Path, log: str, **kwargs: Any) -> float:
        (directory / log).write_text("ordinary compiler; ignored plan environment variable\n")
        return 0.0

    monkeypatch.setattr(backend, "command", fake_command)
    with pytest.raises(ValueError, match="did not acknowledge"):
        backend.generate(tmp_path / "multifaq", tmp_path, tmp_path / "out", {})


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
    args = [sys.executable, "-c", script]
    env = {**os.environ, "PYTHONPATH": str(ROOT)}
    if nested_optimizer:
        extractor = tmp_path / "extractor"
        extractor.write_text(
            f"#!{sys.executable}\nimport os, time\nfrom pathlib import Path\n"
            f"Path({str(tmp_path / 'child.pid')!r}).write_text(str(os.getpid()))\ntime.sleep(60)\n"
        )
        extractor.chmod(0o755)
        config = tmp_path / "optimizer.json"
        config.write_text(
            json.dumps(
                dict(
                    variant="shared",
                    treatment="slotted",
                    extractor=str(extractor),
                    timeout=60,
                    dag_timeout=5,
                    memory_limit_bytes=None,
                )
            )
        )
        args = [
            sys.executable,
            "-m",
            "benchmarking.lmfao.optimize",
            str(config),
            str(model.FIXTURES / "workload.json"),
            str(tmp_path / "plan.json"),
        ]
    try:
        with pytest.raises(RuntimeError, match="failed; see") as error:
            backend.command(args, tmp_path, "command.log", env=env, timeout=2)
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


def test_pipeline_charges_hook_once_and_excludes_validation_and_diagnostics(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    now = 0.0

    def spend(seconds: float) -> None:
        nonlocal now
        now += seconds

    monkeypatch.setattr(cli, "time", SimpleNamespace(perf_counter=lambda: now))
    documents: dict[str, Any] = {"shared-slotted": {}, "shared-slotted-ref-multi": {}}

    def collect(output: Path, *args: Any, **kwargs: Any) -> tuple[dict[str, Any], dict[str, Any]]:
        spend(999)
        return documents, {
            "optimizer": {label: {"process_seconds": 999} for label in documents},
            "graph_collection": {label: {"seconds": 999} for label in documents},
            "binary_paths": {"slotted": "/encoded", "slotted-ref-multi": "/native"},
            "extractor_path": "/lmfao-extract",
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
            "outputs": [{"view": 0, "aggregate": 0, "root": 0}],
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
                "--binding-control",
                "named",
                "--binding-control",
                "canonical",
            ]
        )
        == 0
    )
    report = json.loads(capsys.readouterr().out)
    assert report == json.loads((output / "pipeline.json").read_text())
    costs = report["accounted_pipeline"]
    assert costs["original"]["one_time_phase_sum_seconds"] == 42
    assert costs["shared-slotted"]["one_time_phase_sum_seconds"] == 67
    assert costs["shared-slotted-ref-multi"]["one_time_phase_sum_seconds"] == 69
    assert costs["shared-slotted-ref-multi"]["execution_label"] == "shared-slotted"
    assert costs["original"]["optimization_and_generation_seconds"] == 2
    assert costs["shared-slotted"]["optimization_and_generation_seconds"] == 27
    assert costs["shared-slotted"]["compilation_seconds"] == 40
    assert report["metadata"]["validation_preparation_seconds"] == 2011
    assert len(report["builds"]) == 5 and len(report["validation"]) == 2
    for binding in ["named", "canonical"]:
        label = f"shared-ordinary-{binding}"
        assert costs[label]["execution_label"] == "shared-slotted"
        assert costs[label]["one_time_phase_sum_seconds"] == 69
        assert report["binding_controls"][label] == binding
    assert "compilation_seconds" not in report["builds"]["shared-slotted-ref-multi"]
    assert "not a measured end-to-end" in report["phase_scope"]
    comparison = (output / "comparison.md").read_text()
    assert "| shared / egglog | All six | Enabled | 0.2750 | 2 |" in comparison
    assert "| shared / native multipattern | All six | Enabled | 0.2750 | 2 |" in comparison
    assert "| shared / egglog | 27.0000 | 40.0000 |" in comparison


def test_optimizer_rejects_workload_drift_before_rewriting(tmp_path: Path) -> None:
    from benchmarking.lmfao.optimize import run

    source = tmp_path / "workload.json"
    changed = {**model.WORKLOAD.document, "root": "1"}
    source.write_text(json.dumps(changed))
    with pytest.raises(ValueError, match="frontend differs"):
        run({}, source, tmp_path / "plan.json")
    assert not (tmp_path / "plan.json").exists()


def test_comparison_caption_names_ablation_pairs_and_preserves_missing_results() -> None:
    from benchmarking.lmfao.report import comparison_markdown

    labels = ("original", "single-root-slotted", "roots-slotted", "shared-slotted-ref-multi")
    result = comparison_markdown(
        {
            "optimizer": dict.fromkeys(labels[1:]),
            "accounted_pipeline": {},
        }
    )
    assert "| single-root / egglog | Sales only | Enabled | unavailable | — |" in result
    assert "| roots / egglog | All six | Disabled | unavailable | — |" in result
    assert "| shared / native multipattern | All six | Enabled | unavailable | — |" in result
    assert "compare shared with single-root" in result and "shared with roots" in result
    assert "identical-subexpression reuse" in result and "loading and sorting" in result
    assert "N × execution" in result
