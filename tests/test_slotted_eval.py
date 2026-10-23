"""Standalone timing and correctness runners share inputs and treatment policies."""

from __future__ import annotations

import importlib
import json
import os
import subprocess
import sys
from pathlib import Path
from typing import Any

import pytest

E = importlib.import_module("slotted.eval")
C = importlib.import_module("slotted.check")
V = importlib.import_module("slotted.verify")
W = importlib.import_module("slotted.workloads")
T = importlib.import_module("slotted.treatments")
run = importlib.import_module("slotted.runner")
ROOT = Path(__file__).resolve().parents[1]


def rows_for(workload: Any = None) -> list[Any]:
    workload = workload or W.array_workload(0)
    rows = [
        run.Row(workload.study, workload.case, side, workload.rounds, workload.rules)
        for side in workload.supported_sides(T.SIDES)
    ]
    for row in rows:
        row.goal, row.classes, row.nodes, row.seconds = "yes", 2, 3, 0.125
        row.unsupported = workload.unsupported
    by_side = {row.side: row for row in rows}
    for enc, ref in T.EXACT_PAIRS.items():
        if enc in by_side:
            a, b = by_side[enc], by_side[ref]
            a.vs_ref[ref] = V.Comparison(a, b, "isomorphic")
    return rows


def test_treatment_definitions_keep_exact_and_timing_pairs_distinct() -> None:
    assert T.EXACT_PAIRS == {"encoding": "ref-multi", "encoding-no-aliasing": "ref-nested-snapshot"}
    assert T.TIMING_PAIRS == {"encoding": "ref-multi", "encoding-no-aliasing": "ref-nested"}
    assert set(T.SIDES) == {*T.EXACT_PAIRS, *T.EXACT_PAIRS.values(), *T.TIMING_PAIRS.values()}
    assert T.TREATMENTS["encoding"].flags == ("--slotted",)
    assert T.TREATMENTS["encoding-no-aliasing"].flags == ("--slotted", "--slotted-no-aliasing")
    for side in T.SIDES:
        expected = "syntactic" if side == "ref-nested" else "snapshot"
        assert T.TREATMENTS[side].substitution == expected
        assert side in T.description()
    workload = W.array_workload(0)
    assert workload.reference("ref-nested") == workload.reference("ref-nested-snapshot")
    assert workload.reference("ref-multi") != workload.reference("ref-nested")
    with pytest.raises(ValueError, match="not a reference"):
        workload.reference("encoding")


def test_default_workloads_include_the_paper_array_sweep_and_sdql_table() -> None:
    workloads = W.select(run.parser("test").parse_args([]))
    arrays = [w for w in workloads if w.study == "array"]
    assert [w.case for w in arrays] == [f"goal-2d-4f-N{n}" for n in range(11)]
    assert all(w.rounds == 6 for w in arrays)
    sdql = [w for w in workloads if w.study == "sdql"]
    assert [w.case for w in sdql] == [f"{kernel}_{phase}-44rules" for kernel, phase in W.pf.WORKLOADS]
    assert len(sdql) == 10
    assert {w.case for w in workloads if w.study == "logic"} == {
        p.stem for p in W.LOGIC_FIXTURES.glob("first-order-logic*.egg")
    }


@pytest.mark.parametrize("encoding,reference", T.EXACT_PAIRS.items())
@pytest.mark.parametrize(
    "problem", ["classes", "nodes", "missing-counts", "identity", "verdict", "certificate", "graph"]
)
def test_exact_gate_rejects_bad_evidence(encoding: str, reference: str, problem: str) -> None:
    rows = rows_for()
    enc = next(r for r in rows if r.side == encoding)
    ref = next(r for r in rows if r.side == reference)
    assert not V.assess(rows)[1]
    if problem in ("classes", "nodes"):
        setattr(enc, problem, getattr(enc, problem) + 1)
    elif problem == "missing-counts":
        enc.classes = None
    elif problem == "identity":
        # The same counts and label cannot transfer a verdict to a different run.
        enc.vs_ref[reference] = V.Comparison(enc, rows_for()[2], "isomorphic")
    elif problem == "verdict":
        enc.vs_ref[reference] = V.Comparison(enc, ref, "inconclusive: search cap")
    elif problem == "certificate":
        enc.vs_ref.clear()
    else:
        enc.graph_issue = "truncated graph"
    assert V.assess(rows)[1]


@pytest.mark.parametrize("encoding,reference", T.EXACT_PAIRS.items())
@pytest.mark.parametrize("phase", ["timed run", "graph dump"])
def test_reference_timeout_never_hides_encoding_failures_or_mismatches(
    encoding: str, reference: str, phase: str
) -> None:
    rows = rows_for()
    enc, ref = (next(r for r in rows if r.side == side) for side in (encoding, reference))
    ref.goal = "timeout" if phase == "timed run" else "yes"
    ref.classes = ref.nodes = None
    ref.graph_issue = f"reference {phase} exceeded timeout"
    enc.vs_ref[reference] = V.Comparison(enc, ref, "inconclusive: counts unavailable")
    verdicts, errors = V.assess(rows)
    assert not errors and (encoding, reference, "not compared: reference timeout") in verdicts
    enc.graph_issue = "encoding graph unreadable"
    assert V.assess(rows)[1]
    enc.graph_issue = None
    enc.nodes = None
    assert V.assess(rows)[1]
    enc.nodes = 3
    ref.classes, ref.nodes = 2, 4
    assert "different: nodes" in str(V.assess(rows)[1])
    ref.nodes = 3
    enc.vs_ref[reference] = V.Comparison(enc, ref, "different: symmetry groups")
    assert "different: symmetry groups" in str(V.assess(rows)[1])


def test_unsupported_treatments_do_not_waive_supported_checks() -> None:
    workload = W.prepare(("logic", "first-order-logic"))
    rows = rows_for(workload)
    assert [r.side for r in rows] == ["encoding", "ref-multi"]
    assert set(workload.unsupported) == {"encoding-no-aliasing", "ref-nested-snapshot", "ref-nested"}
    assert not V.assess(rows)[1]
    assert "missing ref-multi" in str(V.assess(rows[:1])[1])
    rows[0].nodes += 1
    assert "different: nodes" in str(V.assess(rows)[1])
    assert V.assess([])[1]


@pytest.mark.parametrize("study,case", [("array", 0), ("logic", "first-order-logic")])
def test_checker_runs_every_supported_treatment(study: str, case: str | int, monkeypatch: pytest.MonkeyPatch) -> None:
    workload = W.prepare((study, case))
    ran, graphed = [], []

    def execute(_workload: Any, side: str, *_args: Any, **_kwargs: Any) -> Any:
        ran.append(side)
        return next(r for r in rows_for(workload) if r.side == side)

    monkeypatch.setattr(run, "run", execute)
    monkeypatch.setattr(V, "collect_graph", lambda _w, r, *_a, **_k: graphed.append(r.side))
    monkeypatch.setattr(V, "compare", lambda *_a, **_k: None)
    rows = C.check_workload(workload)
    assert ran == graphed == list(workload.supported_sides(T.SIDES))
    assert all(row.unsupported == workload.unsupported for row in rows)


def test_benchmark_collects_fresh_samples_and_never_exports_graphs(monkeypatch: pytest.MonkeyPatch) -> None:
    workload = W.array_workload(0)
    calls = []

    def execute(_workload: Any, side: str, *_args: Any, **_kwargs: Any) -> Any:
        calls.append(side)
        return next(r for r in rows_for() if r.side == side)

    monkeypatch.setattr(run, "run", execute)
    monkeypatch.setattr(V, "collect_graph", lambda *_a, **_k: pytest.fail("benchmark exported a graph"))
    for _ in range(2):
        rows = E.benchmark(workload, samples=3)
        assert len(rows) == 3 * len(T.BENCHMARK_SIDES)
    assert calls == [side for _ in range(2) for side in T.BENCHMARK_SIDES for _ in range(3)]
    code = """
import slotted.eval, sys
assert not {
    'slotted.verify', 'slotted.xdiff.isomorphism', 'slotted.test_program',
    'slotted.xdiff.xarray', 'benchmarking',
} & sys.modules.keys()
"""
    result = subprocess.run([sys.executable, "-c", code], cwd=ROOT, capture_output=True, text=True)
    assert result.returncode == 0, result.stderr


def test_timing_tables_and_goal_status_are_separate(capsys: pytest.CaptureFixture[str]) -> None:
    workload = W.array_workload(0)
    rows = rows_for(workload)
    rows[0].goal, rows[0].seconds = "timeout", 300.125
    output = E.report([workload], [rows], T.BENCHMARK_SIDES)
    assert "| Array N=0 | timeout | 0.125 |" in output
    assert "ref-nested-snapshot" not in output
    assert "Classes" not in output and "Nodes" not in output
    rows[0].goal = "no"
    rows[0].seconds = 0.125
    assert E.timing_cell([rows[0]]) == "0.125"
    assert run.goal_errors(rows)
    assert C.report([workload], [rows])
    assert C.ERROR_TITLE in capsys.readouterr().out
    rows[0].goal = "yes"
    assert not C.report([workload], [rows])
    assert C.ERROR_TITLE not in capsys.readouterr().out


def test_logic_inputs_keep_fixture_budgets_and_source(tmp_path: Path) -> None:
    path = tmp_path / "logic.egg"
    path.write_text((ROOT / "egglog-experimental/benches/slotted/logic/first-order-logic2.egg").read_text())
    workload = W.logic_workload(path)
    assert workload.rounds == 5
    assert "(run 5)" in workload.program and workload.multi.startswith("rounds 5\n")
    zero = W.logic_workload(path, rounds=0)
    assert "(run 0)" in zero.program and zero.multi.startswith("rounds 0\n")
    assert "(check" not in zero.graph_program
    path.unlink()
    assert workload.lang.default_sort == "L" and "Forall" in workload.lang.ops
    with pytest.raises(ValueError, match="single nested pattern"):
        workload.reference("ref-nested")


def test_reference_environment_ignores_ambient_debug_and_substitution(monkeypatch: pytest.MonkeyPatch) -> None:
    flags = ("XMULTI_DEBUG", "XMULTI_DEBUG_RULE", "XMULTI_TRACE")
    for flag in flags:
        monkeypatch.setenv(flag, "1")
    monkeypatch.setenv("XMULTI_SUBST", "invalid")
    for side, treatment in T.TREATMENTS.items():
        if treatment.engine == "reference":
            env = run.oracle_env(side, 10)
            assert not any(flag in env for flag in flags)
            assert env["XMULTI_SUBST"] == treatment.substitution
            assert env["XMULTI_GROUP_LIMIT"] == "10"
            assert env["PATH"] == os.environ["PATH"]


def test_stale_graph_dump_cannot_certify_a_new_run(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    row = run.Row("array", "stale", "encoding", 0)
    stale = tmp_path / f"eval-stale-{os.getpid()}-counts.json"
    stale.write_text('{"nodes": {}}')
    monkeypatch.setattr(V, "SCRATCH", tmp_path)
    monkeypatch.setattr(subprocess, "run", lambda *_a, **_k: subprocess.CompletedProcess([], 0, "", ""))
    V.encoding_counts("", "stale", W.array_workload(0).lang, row, 1)
    assert row.graph is None and row.graph_issue == "encoding graph dump was not written"
    assert not list(tmp_path.iterdir())


@pytest.mark.parametrize("module", [E, C])
def test_build_failure_has_error_exit_status(module: Any, monkeypatch: pytest.MonkeyPatch) -> None:
    def fail_build() -> None:
        raise subprocess.CalledProcessError(1, ["cargo", "build"])

    monkeypatch.setattr(run, "build", fail_build)
    assert module.main(["array"]) == 2


def test_common_graph_export_preserves_duplicate_rows_empty_classes_and_slot_names() -> None:
    graph = V.ISO.Graph()
    graph.add_class("empty", [])
    graph.add_class("nonempty", [1, "1"])
    graph.nodes["nonempty"] = [("pair", (("slot", 1), ("slot", "1")))] * 2
    graph.close_groups()
    exported = V.ISO.serialized_graph(graph)
    assert len(exported["nodes"]) == 2
    assert len(exported["class_data"]) == 2
    slots = exported["slotted"]["classes"][json.dumps("nonempty")]["slots"]
    assert len(set(slots)) == 2
    graph.nodes["unrecorded-class"] = []
    with pytest.raises(ValueError, match="different classes"):
        V.ISO.serialized_graph(graph)


def test_reference_document_preserves_all_annotations() -> None:
    document = {
        "nodes": {"n": {"op": "constant", "eclass": "c", "children": [], "subsumed": True}},
        "class_data": {"c": {"type": "Integer"}},
        "root_eclasses": ["c"],
        "slotted": {"classes": {"c": {"slots": [], "group": [[]]}}, "nodes": {"n": {"arguments": []}}},
    }
    parsed = V.ISO.parse_reference("GRAPH " + json.dumps(document))
    assert parsed.summary() == (1, 1)
    assert V.ISO.serialized_graph(parsed) == document
    with pytest.raises(ValueError, match="one complete GRAPH"):
        V.ISO.parse_reference("GRAPH {}\nGRAPH {}")
