#!/usr/bin/env python3
"""Regressions for complete refinement and trustworthy evaluation verdicts."""

import argparse
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from slotted import check as C  # noqa: E402
from slotted import eval as E  # noqa: E402
from slotted import runner as run  # noqa: E402
from slotted import verify as V  # noqa: E402
from slotted import workloads as W  # noqa: E402
from slotted.treatments import EXACT_PAIRS, SIDES  # noqa: E402
from slotted.xdiff import xdiff as X  # noqa: E402

CHECK_CONFIG = run.Config(
    egglog=ROOT / "target" / "debug" / "egglog-experimental",
    xmulti=ROOT / "slotted" / "xmulti" / "target" / "debug" / "xmulti",
    checker=ROOT / "target/debug/egraph-isomorphism",
)


def successful(rows, sides=SIDES):
    return not V.assess(rows, sides)[1]


def graphs(name, program, spec, lang=X.LANG):
    enc, ref = (run.Row("regression", name, side, 1) for side in ("encoding", "ref-multi"))
    V.encoding_counts(program, name, lang, enc, 60, config=CHECK_CONFIG, encoded=True)
    run.run_reference(spec, ref, 60, config=CHECK_CONFIG)
    V.reference_counts(spec, ref, 60, config=CHECK_CONFIG)
    assert enc.graph is not None and ref.graph is not None, (name, enc.as_dict(), ref.as_dict())
    V.compare([enc, ref])
    return enc, ref


def source_graphs(name, rounds):
    """Compare a small SDQL fixture's start, unions, rewrites, and final goal."""
    path = ROOT / "egglog-experimental" / "tests" / "slotted" / f"{name}.egg"
    src = W.syntax.Source(path)
    lang = W.pf.reference_language()
    forms = W.syntax.parse(path.read_text())
    start = next(f[2] for f in forms if f[:2] == ["let", "start"])
    target = next(f[1][2] for f in forms if f[0] == "check")
    spec = (
        "\n".join(
            [
                f"rounds {rounds}",
                *W.ctor_lines(lang),
                f"term {lang.sexpr(src.term(start, ground=True))}",
                "term (var $0)",
                *(
                    "union " + " ".join(lang.sexpr(src.term(t, ground=True)) for t in f[1:])
                    for f in forms
                    if f[0] == "union"
                ),
                *W.rule_lines(lang, path, None, False),
                f"goal {lang.sexpr(src.term(target, ground=True))}",
            ]
        )
        + "\n"
    )
    return graphs(name, X.driver.compile_source(path.read_text()), spec, lang)


def substitution_refresh():
    enc, ref = source_graphs("subst-refresh", 2)
    assert ref.goal == "yes", ref.goal
    assert enc.graph.summary() == (5, 8) == (ref.classes, ref.nodes)
    assert enc.verdict(ref) == "isomorphic", enc.vs_ref


def coset_direction():
    enc, ref = source_graphs("coset-direction", 1)
    assert ref.goal == "yes", ref.goal
    assert enc.verdict(ref) == "isomorphic", enc.vs_ref


def symmetry_case(depth, swapped):
    left, right = ("var", 0), ("var", 1)
    term = ("F", left, right)
    chain = ("Null",)
    for _ in range(depth):
        chain = ("G", ("Null",), chain)
    terms = [term, chain]
    source = '(include "egglog-experimental/tests/slotted/languages/toy.egg")\n'
    source += "\n".join(f"(let seed{i} {X.driver.term(X.LANG, t)})" for i, t in enumerate(terms))
    program = X.driver.compile_source(source + "\n(run 0)")
    spec = "\n".join(f"term {X.sexpr(t)}" for t in terms) + "\n"
    if swapped:
        spec += f"union {X.sexpr(term)} {X.sexpr(('F', right, left))}\n"
    return graphs(f"symmetry-{depth}-{swapped}", program, spec)


def complete_refinement():
    atoms = [("root", "Null", [])]
    atoms += [(f"p{i}", "F", [("pv", f"a{i}"), ("pv", f"a{i}")]) for i in range(6)]
    rhs = ("pv", "a5")
    for i in reversed(range(5)):
        rhs = ("G", ("pv", f"a{i}"), rhs)
    source = '(include "egglog-experimental/tests/slotted/languages/toy.egg")\n'
    source += X.driver.rewrite(X.LANG, atoms, "root", rhs, name="all-refinements")
    program = X.driver.compile_source(source + "\n(let n (Null))\n(let f (F $0 $0))\n(run 1)")
    root, lines = X.syntax.atom_lines(X.LANG, "root", atoms)
    spec = "\n".join(
        [
            "rounds 1",
            "term (null)",
            "term (f (var $0) (var $0))",
            "rule",
            *lines,
            f"rhs {root} {X.syntax.pat_sexpr(X.LANG, rhs)}",
            "",
        ]
    )
    enc, ref = graphs("all-refinements", program, spec)
    assert enc.verdict(ref) == "isomorphic", enc.vs_ref
    assert enc.graph.summary() == (77, 280) == (ref.classes, ref.nodes)


def count_round_budget():
    """Graph collection must not execute another user round to probe saturation."""
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp) / "budget.egg"
        path.write_text(
            '(include "egglog-experimental/tests/slotted/languages/toy.egg")\n'
            "(rewrite (Null) (F $0 $0))\n(let start (Null))\n(run 1)\n"
        )
        program = X.driver.compile_source(path.read_text())
    # Installed after the requested run: any additional user-rule step is an error.
    program += '\n(rule () ((panic "graph collection exceeded the round budget")))\n'
    row = run.Row("regression", "count-budget", "encoding", 1)
    V.encoding_counts(program, "count-budget", X.LANG, row, 60, config=CHECK_CONFIG, encoded=True)
    assert row.graph is not None, row.graph_issue
    assert row.graph.summary() == (2, 3) == (row.classes, row.nodes)
    assert row.saturated == "?"


def independent_class_counts():
    """Cross-check the graph reader against counts computed inside egglog.

    Each slotted class has one minimal member among its linked egglog values.
    Count FreeVars rows minus nonminimal members, independently of the native
    exporter's component traversal. The isomorphism suite compares these same cases
    to the reference.
    """
    observer = f"""
(ruleset count-classes)
(relation Nonminimal (U))
; Links may be stored in either direction; count the larger endpoint once.
(rule (({X.SYM.renames} a m b) (!= a b) (= a (ordering-max a b)))
      ((Nonminimal a)) :ruleset count-classes)
(rule (({X.SYM.renames} a m b) (!= a b) (= b (ordering-max a b)))
      ((Nonminimal b)) :ruleset count-classes)
(run count-classes 1)
(print-size {X.SYM.free_vars})
(print-size Nonminimal)
"""
    with tempfile.TemporaryDirectory(prefix="slotted-class-counts-") as tmp:
        path = Path(tmp) / "counts.egg"
        for case in X.curated():
            path.write_text(
                case.egg_program(mult=3).replace("(print-function SameClass 100000)", observer)
                + "\n"
                + V.ISO.export_command(path.with_suffix(".json"), X.LANG)
            )
            path.with_suffix(".json").unlink(missing_ok=True)
            result = subprocess.run(
                [str(CHECK_CONFIG.egglog), "--slotted-encoded", str(path)],
                capture_output=True,
                text=True,
                check=True,
                cwd=ROOT,
                timeout=60,
            )
            total, nonminimal = [int(line.strip()) for line in result.stdout.splitlines() if line.strip().isdigit()]
            graph = V.ISO.read_export(json.loads(path.with_suffix(".json").read_text()))
            assert total - nonminimal == len(graph.ids()), (case.name, total, nonminimal, graph.summary())


def raw_node_counts():
    """Keep the independent count check when a document loses a constructor row."""
    builder = V.ISO.Graph()
    builder.add_class("constant", [])
    builder.nodes["constant"] = [("null", ())]
    builder.close_groups()
    doc = V.ISO.serialized_graph(builder)
    doc["counts"] = {"classes": 1, "nodes": 2}
    with patch.object(V.ISO, "validate_document", return_value=(1, 1)):
        try:
            V.ISO.read_export(doc)
        except ValueError as exc:
            assert "disagree" in str(exc)
        else:
            raise AssertionError("lost constructor row escaped the independent count check")


def verdicts():
    # Same class/node counts on both sides; only the symmetry group differs.
    # Exercise both sides of the former 40-class cutoff.
    for depth in (0, 41):
        enc, ref = symmetry_case(depth, True)
        assert (enc.classes, enc.nodes) == (ref.classes, ref.nodes)
        assert enc.verdict(ref).startswith("different:"), enc.vs_ref

    enc, ref = symmetry_case(41, False)
    assert enc.classes > 40 and enc.verdict(ref) == "isomorphic", enc.vs_ref
    V.compare([enc, ref], search_cap=0)
    assert enc.verdict(ref).startswith("inconclusive:"), enc.vs_ref
    assert V.compare_counts(enc, ref) == "same counts"

    witness, why = V.ISO.find_isomorphism(ref.graph, enc.graph)
    assert witness is not None, why
    # Even a broken checker that always accepts must not override the simple counts.
    for side in (enc, ref):
        for name in ("classes", "nodes"):
            for value in (getattr(side, name) + 1, None):
                with (
                    patch.object(side, name, value),
                    patch.object(V.ISO, "find_isomorphism", return_value=(witness, None)) as search,
                    patch.object(V.ISO, "verify", return_value=None) as verify,
                ):
                    V.compare([enc, ref])
                    prefix = "inconclusive: counts unavailable" if value is None else f"different: {name} "
                    assert enc.verdict(ref).startswith(prefix), enc.vs_ref
                    search.assert_not_called()
                    verify.assert_not_called()
    with (
        patch.object(V.ISO, "find_isomorphism", return_value=(witness, None)),
        patch.object(V.ISO, "verify", return_value="deliberately invalid witness"),
    ):
        V.compare([enc, ref])
    assert enc.verdict(ref).startswith("inconclusive: witness rejected"), enc.vs_ref

    with patch.object(ref, "graph", None):
        V.compare([enc, ref])
        assert enc.verdict(ref) == "inconclusive: no reference graph"
    enc.graph = None
    V.compare([enc, ref])
    assert enc.verdict(ref) == "inconclusive: no encoding graph"
    return enc, ref


def goal_reporting():
    # A short budget actually misses the goal on all sides. Equal graphs
    # alone must not turn this into a successful benchmark.
    rows = C.check_workload(W.array_workload(0, rounds=1), timeout=30, config=CHECK_CONFIG)
    assert all(r.goal == "no" for r in rows), [r.as_dict() for r in rows]
    by_side = {r.side: r for r in rows}
    assert set(by_side) == set(SIDES)
    for encoding, reference in EXACT_PAIRS.items():
        assert by_side[encoding].verdict(by_side[reference]) == "isomorphic"
    assert not successful(rows)


def substitution_policies():
    # The body was created as g, but f wins the snapshot's spelling tie-break.
    # Checking which substituted node actually appears catches using the wrong
    # policy even if the CONFIG line and report label claim the right one.
    head = """rounds 1
term (app (lam $0 (g (var $0) (null))) (null))
union (g (var $0) (null)) (f (var $0) (null))
rule
"""
    for side, lhs, policy, op in (
        ("ref-nested", "nested (app (lam $x ?body) ?t)", "syntactic", "g"),
        ("ref-nested-snapshot", "nested (app (lam $x ?body) ?t)", "snapshot", "f"),
        ("ref-multi", "atom root app lam t\natom lam lam $x body", "snapshot", "f"),
    ):
        spec = head + lhs + f"\nrhs root ?body[(var $x) := ?t]\ngoal ({op} (null) (null))\n"
        row = run.Row("regression", "substitution-policy", side, 1)
        with patch.dict(os.environ, {"XMULTI_SUBST": "invalid-ambient-policy"}):
            run.run_reference(spec, row, 30, config=CHECK_CONFIG)
            V.reference_counts(spec, row, 30, config=CHECK_CONFIG)
        assert row.goal == "yes", row.as_dict()
        assert row.substitution == policy
        graph = row.graph
        assert graph is not None, row.graph_issue
        assert (row.classes, row.nodes) == graph.summary()
        graph = V.ISO.fixture(graph)
        # Both the timed and counting runs chose the intended substituted node.
        other = "f" if op == "g" else "g"
        null = next(cid for cid, nodes in graph.nodes.items() if any(tag == "null" for tag, _ in nodes))
        substituted = {
            tag
            for nodes in graph.nodes.values()
            for tag, elems in nodes
            if elems == (("child", null, ()), ("child", null, ()))
        }
        assert op in substituted and other not in substituted, graph.nodes


def graph_failure_reasons():
    def row():
        return run.Row("regression", "diagnostics", "encoding", 1)

    with tempfile.TemporaryDirectory(prefix="slotted-eval-errors-") as tmp, patch.object(V, "SCRATCH", Path(tmp)):
        failed = row()
        with patch.object(subprocess, "run", side_effect=subprocess.TimeoutExpired("egglog", 1)):
            V.encoding_counts("", "timeout", X.LANG, failed, 1)
        assert "exceeded timeout" in failed.graph_issue
        assert failed.as_dict()["graph_issue"] == failed.graph_issue

        def dump(args, **_kwargs):
            Path(args[-1]).with_suffix(".json").write_text('{"nodes": {}, "counts": {"classes": 0, "nodes": 0}}')
            return subprocess.CompletedProcess(args, 0, "", "")

        with (
            patch.object(subprocess, "run", side_effect=dump),
            patch.object(V.ISO, "read_export", side_effect=RuntimeError("reader bug")),
        ):
            try:
                V.encoding_counts("", "bug", X.LANG, row(), 1)
            except RuntimeError as exc:
                assert str(exc) == "reader bug"
            else:
                raise AssertionError("a programming error was silently swallowed")
        assert not list(Path(tmp).iterdir())

    timed = subprocess.CompletedProcess([], 0, "GOAL yes\nCONFIG substitution=snapshot\n", "")
    real_run = subprocess.run
    for code, stdout, stderr, reason in (
        (1, "", "REFERENCE_LIMIT: group export limit exceeded", "group export limit"),
        (
            0,
            'GRAPH {"nodes":{},"slotted":{"classes":{"c":{"slots":["x"],"group":[]}},"nodes":{}}}\n',
            "",
            "reference graph unreadable",
        ),
        (0, 'GRAPH {"nodes":{},"slotted":{"classes":{},"nodes":{}}}\n', "", "reference graph dump is empty"),
    ):
        reference = run.Row("regression", "diagnostics", "ref-multi", 1)
        dump = subprocess.CompletedProcess([], code, stdout, stderr)
        responses = iter([timed, dump])

        def process(command, responses=responses, **kwargs):
            if Path(command[0]).name == "egraph-isomorphism":
                return real_run(command, **kwargs)
            return next(responses)

        with patch.object(subprocess, "run", side_effect=process):
            run.run_reference("", reference, 1)
            V.reference_counts("", reference, 1, config=CHECK_CONFIG)
        assert reference.goal == "yes" and reason in reference.graph_issue
        assert reference.graph is None and reference.classes is None and reference.nodes is None
        failed = row()
        V.compare([failed, reference])
        assert reason in failed.verdict(reference)

    # Direct sizes survive the dump's symmetry cap or a timeout after SIZES.
    for dump in (
        subprocess.CompletedProcess([], 2, "SIZES 10 20\n", "REFERENCE_LIMIT: symmetry cap"),
        subprocess.TimeoutExpired("xmulti", 1, output=b"SIZES 10 20\n"),
    ):
        reference = run.Row("regression", "diagnostics", "ref-nested-snapshot", 1)
        with patch.object(subprocess, "run", side_effect=[timed, dump]):
            run.run_reference("", reference, 1)
            V.reference_counts("", reference, 1)
        assert (reference.classes, reference.nodes) == (10, 20)
        assert reference.graph is None and reference.graph_issue
        failed = row()
        failed.classes, failed.nodes = 10, 20
        failed.graph = object()
        V.compare([failed, reference])
        assert failed.verdict(reference).startswith("inconclusive: no reference graph")


def combined_comparisons():
    rows = C.check_workload(W.sdql_workload("mmm_sum", "1st"), timeout=30, config=CHECK_CONFIG)
    assert successful(rows), [r.as_dict() for r in rows]
    by_side = {r.side: r for r in rows}
    for encoding, reference in EXACT_PAIRS.items():
        assert by_side[encoding].verdict(by_side[reference]) == "isomorphic"


def logic_case_studies():
    """Use the public collector for source-derived logic rules and exact evidence."""
    paths = sorted(W.LOGIC_FIXTURES.glob("first-order-logic*.egg"))
    assert len(paths) >= 2, "missing first-order logic fixtures"
    for path in paths:
        workload = W.logic_workload(path)
        rows = C.check_workload(workload, timeout=60, config=CHECK_CONFIG)
        assert [row.side for row in rows] == ["encoding", "ref-multi"]
        assert set(workload.unsupported) == {"encoding-no-aliasing", "ref-nested-snapshot", "ref-nested"}
        assert successful(rows), [row.as_dict() for row in rows]
        enc, ref = rows
        assert V.compare_counts(enc, ref) == "same counts"
        assert enc.verdict(ref) == "isomorphic"


def zero_round_budget():
    """An explicit zero must not silently run the paper's default budget."""
    args = argparse.Namespace(
        study="all",
        case=None,
        kernel=["mmm"],
        phase=["1st"],
        rules=44,
        rounds=0,
    )
    results = run.run_workloads(W.select(args), E.benchmark, config=CHECK_CONFIG, timeout=30, sides=("ref-multi",))
    rows = [row for group in results for row in group]
    assert len(rows) == 14
    assert all(r.rounds == 0 and r.goal == "no" for r in rows), rows


def parallel_collection():
    """Spawned workers preserve each workload's counts, verdicts, and configuration."""
    selected = [
        W.array_workload(0, rounds=2),
        W.sdql_workload("mmm_sum", "1st", rounds=2),
        *(W.logic_workload(path, rounds=2) for path in sorted(W.LOGIC_FIXTURES.glob("first-order-logic*.egg"))),
    ]

    def collect(jobs, sides=SIDES, config=CHECK_CONFIG):
        return run.run_workloads(selected, C.check_workload, jobs=jobs, sides=sides, config=config, timeout=60)

    serial, parallel = collect(1), collect(2)
    # The small budget misses the array goal, even though its graphs agree.
    assert not successful(serial[0]) and not successful(parallel[0])

    def evidence(results):
        return [[{k: v for k, v in row.as_dict().items() if k != "seconds"} for row in group] for group in results]

    assert evidence(serial) == evidence(parallel)
    assert all(row.graph is None for group in parallel for row in group)
    for group in parallel:
        by_side = {r.side: r for r in group}
        for encoding, reference in EXACT_PAIRS.items():
            if reference in by_side:
                # Pickling must keep comparison identities attached to the returned rows.
                assert by_side[encoding].verdict(by_side[reference]) == "isomorphic"

    # Spawned workers receive explicit configuration, not fresh defaults.
    selected = selected[:1]
    sides = ("encoding-no-aliasing", "ref-nested-snapshot")
    (limited,) = collect(
        2, sides, run.Config(CHECK_CONFIG.egglog, CHECK_CONFIG.xmulti, group_limit=0, checker=CHECK_CONFIG.checker)
    )
    enc, ref = limited
    assert enc.goal == ref.goal == "no"
    assert (enc.classes, enc.nodes) == (ref.classes, ref.nodes)
    assert "REFERENCE_LIMIT" in ref.graph_issue
    assert enc.verdict(ref).startswith("inconclusive:")
    assert not successful(limited, sides)


def import_without_compilation():
    """Workload definitions and reporting must not compile the test programs."""
    code = """
import importlib
import sys
from unittest.mock import patch

compiler = importlib.import_module("slotted.test_program")
with patch.object(compiler, "compile_source", side_effect=AssertionError("compiled during import")):
    importlib.import_module("slotted.eval")
    importlib.import_module("slotted.check")
    importlib.import_module("slotted.xdiff.xsdql")
"""
    result = subprocess.run([sys.executable, "-c", code], cwd=ROOT, capture_output=True, text=True, timeout=30)
    assert result.returncode == 0, result.stdout + result.stderr


def separate_timing_and_graph_runs():
    """Failed goals still get untimed evidence; failed processes never certify a graph."""
    workload = W.array_workload(0, rounds=0)
    sides = ("ref-multi",)
    timed = subprocess.CompletedProcess([], 0, "GOAL no\nCONFIG substitution=snapshot\n", "")
    dump = subprocess.CompletedProcess([], 2, "SIZES 10 20\n", "REFERENCE_LIMIT: symmetry cap")
    for counts in (False, True):
        worker = C.check_workload if counts else E.benchmark
        with patch.object(subprocess, "run", side_effect=[timed, dump]) as process:
            (row,) = worker(workload, sides=sides, config=CHECK_CONFIG, timeout=30)
        assert process.call_count == (2 if counts else 1)
        assert row.goal == "no" and row.seconds is not None
        assert (row.classes, row.nodes) == ((10, 20) if counts else (None, None))
        assert not successful([row], sides)

    for failed in (
        subprocess.TimeoutExpired("xmulti", 30),
        subprocess.CompletedProcess([], 1, "", "reference error"),
        subprocess.CompletedProcess([], 0, "GOAL yes\nCONFIG substitution=syntactic\n", ""),
    ):
        with patch.object(subprocess, "run", side_effect=[failed]) as process:
            (row,) = C.check_workload(workload, sides=sides, config=CHECK_CONFIG, timeout=30)
        assert process.call_count == 1
        assert row.graph_issue and row.classes is None and row.nodes is None
        assert successful([row], sides) == isinstance(failed, subprocess.TimeoutExpired)


def main():
    import_without_compilation()
    separate_timing_and_graph_runs()
    substitution_policies()
    combined_comparisons()
    logic_case_studies()
    graph_failure_reasons()
    goal_reporting()
    zero_round_budget()
    parallel_collection()
    substitution_refresh()
    coset_direction()
    complete_refinement()
    count_round_budget()
    independent_class_counts()
    raw_node_counts()
    verdicts()
    print("OK: complete refinement, separate count checks, exact graph verdicts, and evaluation exit statuses")


if __name__ == "__main__":
    main()
