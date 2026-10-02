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
sys.path[:0] = [str(ROOT / "slotted"), str(ROOT / "slotted" / "xdiff")]
import eval as E  # noqa: E402
import eval_report as R  # noqa: E402
import xdiff as X  # noqa: E402


def graphs(name, program, spec, lang=X.LANG):
    enc, ref = (E.Row("regression", name, side, 1) for side in ("encoding", "ref-multi"))
    E.encoding_counts(program, name, lang, enc, 60)
    E.run_reference(spec, ref, 60, True)
    assert enc.graph is not None and ref.graph is not None, (name, enc.as_dict("test"), ref.as_dict("test"))
    E.compare([enc, ref])
    return enc, ref


def source_graphs(name, rounds):
    """Compare a small SDQL fixture's start, unions, rewrites, and final goal."""
    path = ROOT / "slotted" / "tests" / f"{name}.egg"
    src = E.sc.Source(path)
    lang = E.pf.reference_language()
    forms = E.sc.parse(path.read_text())
    start = next(f[2] for f in forms if f[:2] == ["let", "start"])
    target = next(f[1][2] for f in forms if f[0] == "check")
    spec = (
        "\n".join(
            [
                f"rounds {rounds}",
                *E.ctor_lines(lang),
                f"term {lang.sexpr(src.term(start, ground=True))}",
                "term (var $0)",
                *(
                    "union " + " ".join(lang.sexpr(src.term(t, ground=True)) for t in f[1:])
                    for f in forms
                    if f[0] == "union"
                ),
                *E.rule_lines(lang, path, None, False),
                f"goal {lang.sexpr(src.term(target, ground=True))}",
            ]
        )
        + "\n"
    )
    return graphs(name, E.sc.compile_source(src), spec, lang)


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
    term = ("f", left, right)
    chain = ("null",)
    for _ in range(depth):
        chain = ("g", ("null",), chain)
    terms = [term, chain]
    program = X.machinery("toy") + "\n"
    program += "\n".join(f"(let seed{i} {X.enc(t)})" for i, t in enumerate(terms))
    program += f"\n(run-schedule {X.slotenc.MACHINERY_SCHEDULE})\n"
    spec = "\n".join(f"term {X.sexpr(t)}" for t in terms) + "\n"
    if swapped:
        spec += f"union {X.sexpr(term)} {X.sexpr(('f', right, left))}\n"
    return graphs(f"symmetry-{depth}-{swapped}", program, spec)


def complete_refinement():
    atoms = [("root", "null", [])]
    atoms += [(f"p{i}", "f", [("pv", f"a{i}"), ("pv", f"a{i}")]) for i in range(6)]
    rhs = ("pv", "a5")
    for i in reversed(range(5)):
        rhs = ("g", ("pv", f"a{i}"), rhs)
    program = X.machinery("toy") + "\n"
    program += X.slotenc.compile_rule(X.LANG, atoms, ("build", "root", rhs), name="all-refinements")
    program += f"\n(Null)\n{X.enc(('f', ('var', 0), ('var', 0)))}\n" + X.schedule(1)
    root, lines = X.slotenc.atom_lines(X.LANG, "root", atoms)
    spec = "\n".join(
        [
            "rounds 1",
            "term (null)",
            "term (f (var $0) (var $0))",
            "rule",
            *lines,
            f"rhs {root} {X.slotenc.pat_sexpr(X.LANG, rhs)}",
            "",
        ]
    )
    enc, ref = graphs("all-refinements", program, spec)
    assert enc.verdict(ref) == "isomorphic", enc.vs_ref
    assert enc.graph.summary() == (77, 280) == (ref.classes, ref.nodes)


def verdicts():
    # Same class/node counts on both sides; only the symmetry group differs.
    # Exercise both sides of the former 40-class cutoff.
    for depth in (0, 41):
        enc, ref = symmetry_case(depth, True)
        assert (enc.classes, enc.nodes) == (ref.classes, ref.nodes)
        assert enc.verdict(ref).startswith("different:"), enc.vs_ref

    enc, ref = symmetry_case(41, False)
    assert enc.classes > 40 and enc.verdict(ref) == "isomorphic", enc.vs_ref
    with patch.object(E.ISO, "SEARCH_CAP", 0):
        E.compare([enc, ref])
    assert enc.verdict(ref).startswith("inconclusive:"), enc.vs_ref
    assert E.compare_counts(enc, ref) == "same counts"
    assert f"{enc.classes}/{enc.nodes}" in R.graph_cell(enc)

    witness, why = E.ISO.find_isomorphism(ref.graph, enc.graph)
    assert witness is not None, why
    # Even a broken checker that always accepts must not override the simple counts.
    for side in (enc, ref):
        for name in ("classes", "nodes"):
            for value in (getattr(side, name) + 1, None):
                with (
                    patch.object(side, name, value),
                    patch.object(E.ISO, "find_isomorphism", return_value=(witness, None)) as search,
                    patch.object(E.ISO, "verify", return_value=None) as verify,
                ):
                    E.compare([enc, ref])
                    prefix = "inconclusive: counts unavailable" if value is None else f"different: {name} "
                    assert enc.verdict(ref).startswith(prefix), enc.vs_ref
                    search.assert_not_called()
                    verify.assert_not_called()
    with (
        patch.object(E.ISO, "find_isomorphism", return_value=(witness, None)),
        patch.object(E.ISO, "verify", return_value="deliberately invalid witness"),
    ):
        E.compare([enc, ref])
    assert enc.verdict(ref).startswith("inconclusive: witness rejected"), enc.vs_ref

    with patch.object(ref, "graph", None):
        E.compare([enc, ref])
        assert enc.verdict(ref) == "inconclusive: no reference graph"
    enc.graph = None
    E.compare([enc, ref])
    assert enc.verdict(ref) == "inconclusive: no encoding graph"
    return enc, ref


def exit_status(enc, ref):
    enc.goal = ref.goal = "yes"
    sides = ("encoding", "ref-multi")
    assert not E.successful([], sides, True)
    assert not E.successful([enc], sides, True)
    with tempfile.TemporaryDirectory(prefix="slotted-eval-check-") as tmp:
        path = Path(tmp) / "report.jsonl"
        for verdict in ("isomorphic", "different: symmetry group", "inconclusive: search cap", "same rows", None):
            enc.vs_ref = (
                {} if verdict is None else {"ref-multi": E.Comparison(enc.observation, ref.observation, verdict)}
            )
            assert E.successful([enc, ref], sides, True) == (verdict == "isomorphic")
            assert E.successful([enc, ref], sides, False)  # explicitly goal-only
            path.write_text("".join(json.dumps(row.as_dict("regression")) + "\n" for row in (enc, ref)))
            result = subprocess.run(
                [sys.executable, str(ROOT / "slotted" / "eval.py"), "--from", str(path), "--side", ",".join(sides)],
                capture_output=True,
                text=True,
                timeout=30,
            )
            assert result.returncode == (0 if verdict == "isomorphic" else 1), (verdict, result.stderr)
        # Loading a report also checks counts, even if its stored verdict is positive.
        enc.vs_ref = {"ref-multi": E.Comparison(enc.observation, ref.observation, "isomorphic")}
        for side in (enc, ref):
            for name in ("classes", "nodes"):
                for value in (getattr(side, name) + 1, None):
                    with patch.object(side, name, value):
                        assert not E.successful([enc, ref], sides, True)
                        assert E.successful([enc, ref], sides, False)
                        path.write_text("".join(json.dumps(row.as_dict("regression")) + "\n" for row in (enc, ref)))
                        result = subprocess.run(
                            [
                                sys.executable,
                                str(ROOT / "slotted" / "eval.py"),
                                "--from",
                                str(path),
                                "--side",
                                ",".join(sides),
                            ],
                            capture_output=True,
                            text=True,
                            timeout=30,
                        )
                        assert result.returncode == 1, (name, value, result.stdout, result.stderr)
    enc.vs_ref = {"ref-multi": E.Comparison(enc.observation, ref.observation, "isomorphic")}
    for enc_goal, ref_goal in (("yes", "no"), ("no", "yes"), ("no", "no")):
        enc.goal, ref.goal = enc_goal, ref_goal
        for counts in (True, False):
            assert not E.successful([enc, ref], sides, counts)


def goal_reporting():
    # A short budget actually misses the goal on all three sides. Equal graphs
    # alone must not turn this into a successful benchmark.
    rows = list(E.array_rows([0], 1, E.SIDES, True, 30))
    assert [r.goal for r in rows] == ["no", "no", "no"], [r.as_dict("test") for r in rows]
    assert rows[0].verdict(rows[1]) == "isomorphic"
    assert not E.successful(rows, E.SIDES, True)

    # Report outcomes independently: nested may miss a goal encoding reaches.
    # A timed failed run must never put "no (1.2)" in its elapsed-time column.
    enc, _, nested = rows
    enc.goal, enc.seconds = "yes", 2.3
    nested.seconds = 1.2
    for outcome in ("no", "timeout", "error"):
        nested.goal = outcome
        head, table = R.pivot([enc, nested], E.SIDES)
        cells = dict(zip(head, table[0], strict=True))
        enc_goal = next(k for k in head if k.startswith("encoding goal"))
        nested_goal = next(k for k in head if k.startswith("ref-nested goal"))
        assert cells[enc_goal] == "yes" and cells[nested_goal] == outcome
        assert cells["encoding elapsed (s)"] == "2.3"
        assert cells["ref-nested elapsed (s)"] == "1.2"
        assert cells["ref-multi goal"] == cells["ref-multi elapsed (s)"] == ""
        assert R.graph_cell(nested) in table[0]
        assert not E.successful([enc, nested], ("encoding", "ref-nested"), True)
        for rendered in (R.markdown(head, table), R.html([("Full report", "", head, table)])):
            assert "elapsed (s)" in rendered and "no (1.2)" not in rendered
        long = dict(zip(R.LONG_HEAD, R.long_cells(nested), strict=True))
        assert long["goal"] == outcome and long["seconds"] == "1.2"


def summary_reporting():
    enc = E.Row("sdql", "mmm_1st-44rules", "encoding", 30, 44)
    enc.goal, enc.seconds, enc.nodes, enc.classes, enc.saturated = "yes", 1.2, 1_234, 56, "yes"
    nested = E.Row("sdql", enc.case, "ref-nested", 30, 44)
    nested.goal, nested.seconds = "no", 0.5
    head, table = R.summary([nested, enc], E.SIDES)
    cells = [dict(zip(head, row, strict=True)) for row in table]
    assert [row["System"] for row in cells] == list(E.SIDES)
    assert [row["Goal"] for row in cells] == ["yes", "missing", "no"]
    assert [row["Elapsed (s)"] for row in cells] == ["1.2", "—", "0.5"]
    assert cells[0]["Nodes"] == "1,234" and cells[0]["Classes"] == "56"
    assert all(row["Budget"] == "30" for row in cells)
    assert cells[0]["Workload"] == "MMM (1st)" and not cells[1]["Workload"]
    assert cells[2]["Nodes"] == cells[2]["Sat."] == "—"

    # Missing/failed measurements stay explicit, including in a timing-only run.
    for goal in ("timeout", "error: detailed diagnostic", "?"):
        nested.goal = goal
        nested.seconds, nested.nodes, nested.classes = None, None, 0
        head, table = R.summary([nested], ("ref-nested",))
        cells = dict(zip(head, table[0], strict=True))
        assert cells["Goal"] == ("error" if goal.startswith("error") else goal)
        assert cells["Elapsed (s)"] == cells["Nodes"] == "—" and cells["Classes"] == "0"

    # Different round budgets and rule subsets cannot collapse into one group.
    small = E.Row("sdql", "batax_2nd-12rules", "encoding", 12, 12)
    full = E.Row("sdql", "batax_2nd-44rules", "encoding", 12, 44)
    longer = E.Row("sdql", full.case, "encoding", 30, 44)
    array = E.Row("array", "goal-2d-4f-N3", "encoding", 6)
    custom = E.Row("custom", "<case&>", "encoding", 1, 7)
    rows = [enc, nested, small, full, longer, array, custom]
    head, table = R.summary(rows, ("encoding",))
    labels = [row[0] for row in table]
    assert labels == [
        "MMM (1st)",
        "BATAX (2nd, 12 rules)",
        "BATAX (2nd)",
        "BATAX (2nd)",
        "Array N=3",
        "custom: <case&> (7 rules)",
    ]
    assert [row[2] for row in table[2:4]] == ["12", "30"]

    with tempfile.TemporaryDirectory(prefix="slotted-eval-summary-") as tmp:
        path, page = Path(tmp) / "report.jsonl", Path(tmp) / "report.html"
        record = "".join(json.dumps(row.as_dict("summary")) + "\n" for row in rows)
        path.write_text(record)
        summary = R.markdown(*R.summary(rows, E.SIDES))
        for long in (False, True):
            result = subprocess.run(
                [
                    sys.executable,
                    E.__file__,
                    "--from",
                    path,
                    "--side",
                    ",".join(E.SIDES),
                    "--html",
                    page,
                    *(["--long"] if long else []),
                ],
                capture_output=True,
                text=True,
                timeout=30,
            )
            assert result.returncode == 1, result.stderr
            assert result.stdout.startswith("## Summary\n\n" + summary)
            assert result.stdout.count("## Full report") == 1
            full_table = (R.LONG_HEAD, [R.long_cells(r) for r in rows]) if long else R.pivot(rows, E.SIDES)
            assert R.markdown(*full_table) in result.stdout
            markup = page.read_text()
            assert markup.count("<table>") == 2
            assert "<h2>Summary</h2>" in markup and "<h2>Full report</h2>" in markup
            assert "&lt;case&amp;&gt;" in markup and "<case&>" not in markup
            assert path.read_text() == record


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
        ("ref-multi", "atom root app lam t\natom lam lam $x body", "snapshot", "f"),
    ):
        spec = head + lhs + f"\nrhs root ?body[(var $x) := ?t]\ngoal ({op} (null) (null))\n"
        row = E.Row("regression", "substitution-policy", side, 1)
        with patch.dict(os.environ, {"XMULTI_SUBST": "invalid-ambient-policy"}):
            E.run_reference(spec, row, 30, True)
        assert row.goal == "yes", row.as_dict("test")
        assert row.substitution == policy
        graph = row.graph
        assert graph is not None, row.graph_issue
        assert (row.classes, row.nodes) == graph.summary()
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
        loaded = E.Row.from_dict(row.as_dict("test"))
        assert loaded.substitution == policy
        assert f"subst {policy}" in R.long_cells(loaded)[2]
        assert f"subst {policy}" in R.pivot([loaded], (side,))[0][4]


def merged_observations():
    enc, reference = symmetry_case(0, False)
    different, newer = symmetry_case(0, True)
    assert enc.verdict(reference) == "isomorphic"
    assert different.verdict(newer).startswith("different:")
    assert (enc.classes, enc.nodes) == (newer.classes, newer.nodes)
    for row in (enc, reference, newer):
        row.goal = "yes"
        row.case = "provenance"
    sides = ("encoding", "ref-multi")
    with tempfile.TemporaryDirectory(prefix="slotted-eval-merge-") as tmp:
        path = Path(tmp) / "report.jsonl"
        original = [enc.as_dict("first"), reference.as_dict("first")]
        for records, valid in (
            (original, True),
            ([enc.as_dict("first"), reference.as_dict("copied-observation")], True),
            (original + [newer.as_dict("reference-only")], False),
            ([enc.as_dict("first")], False),
        ):
            path.write_text("".join(json.dumps(row) + "\n" for row in records))
            rows, _ = E.load_rows(path, merged=True)
            assert E.successful(rows, sides, True) == valid
            for extra in ([], ["--long"]):
                result = subprocess.run(
                    [sys.executable, E.__file__, "--from", path, "--merged", "--side", ",".join(sides), *extra],
                    capture_output=True,
                    text=True,
                    timeout=30,
                )
                assert result.returncode == (0 if valid else 1), result.stderr
                assert ("isomorphic" in result.stdout) == valid, result.stdout
        replaced_encoding = E.Row.from_dict(enc.as_dict("test"))
        replaced_encoding.observation = "another-observation"
        assert not E.successful([replaced_encoding, reference], sides, True)
        old = enc.as_dict("old-schema")
        del old["schema"]
        path.write_text(json.dumps(old) + "\n")
        result = subprocess.run(
            [sys.executable, E.__file__, "--from", path],
            capture_output=True,
            text=True,
            timeout=30,
        )
        assert result.returncode != 0 and "recompute" in result.stderr

    small = E.Row("sdql", "batax", "ref-multi", 12, 12)
    full = E.Row("sdql", "batax", "ref-multi", 12, 44)
    small.checks, full.checks = "off", None
    small.substitution = full.substitution = "snapshot"
    head, table = R.pivot([small, full], ("ref-multi",))
    assert len(table) == 2 and {row[3] for row in table} == {"12", "44"}
    assert "subst snapshot" in head[4] and "checks off/unknown" in head[4]


def graph_failure_reasons():
    def row():
        return E.Row("regression", "diagnostics", "encoding", 1)

    with tempfile.TemporaryDirectory(prefix="slotted-eval-errors-") as tmp, patch.object(E, "SCRATCH", Path(tmp)):
        failed = row()
        with patch.object(E.subprocess, "run", side_effect=subprocess.TimeoutExpired("egglog", 1)):
            E.encoding_counts("", "timeout", X.LANG, failed, 1)
        assert "exceeded timeout" in failed.graph_issue
        assert E.Row.from_dict(failed.as_dict("test")).graph_issue == failed.graph_issue
        assert failed.graph_issue in R.graph_cell(failed)

        def dump(args, **_kwargs):
            Path(args[-1]).with_suffix(".json").write_text("{}")
            return subprocess.CompletedProcess(args, 0, "", "")

        with (
            patch.object(E.subprocess, "run", side_effect=dump),
            patch.object(E.ISO, "build_encoding_graph", side_effect=RuntimeError("reader bug")),
        ):
            try:
                E.encoding_counts("", "bug", X.LANG, row(), 1)
            except RuntimeError as exc:
                assert str(exc) == "reader bug"
            else:
                raise AssertionError("a programming error was silently swallowed")
        assert not list(Path(tmp).iterdir())

    timed = subprocess.CompletedProcess([], 0, "GOAL yes\nCONFIG substitution=snapshot\n", "")
    for code, stdout, stderr, reason in (
        (1, "", "REFERENCE_LIMIT: symmetry enumeration is capped", "symmetry enumeration"),
        (0, "CLASS c SLOTS x\nGROUP c ?\n", "", "reference graph unreadable"),
        (0, "", "", "reference graph dump is empty"),
    ):
        reference = E.Row("regression", "diagnostics", "ref-multi", 1)
        dump = subprocess.CompletedProcess([], code, stdout, stderr)
        with patch.object(E.subprocess, "run", side_effect=[timed, dump]):
            E.run_reference("", reference, 1, True)
        assert reference.goal == "yes" and reason in reference.graph_issue
        assert reference.graph is None and reference.classes is None and reference.nodes is None
        failed = row()
        E.compare([failed, reference])
        assert reason in failed.verdict(reference)


def zero_round_budget():
    """An explicit zero must not silently run the paper's default budget."""
    args = argparse.Namespace(
        no_build=True,
        study="all",
        params=[0],
        kernel=["mmm"],
        phase=["1st"],
        rules=44,
        rounds=0,
        counts=False,
        timeout=30,
    )
    rows = E.collect(args, ("ref-multi",), argparse.ArgumentParser())
    assert len(rows) == 2
    assert all(row.rounds == 0 and row.goal == "no" for row in rows), [vars(row) for row in rows]


def main():
    # The suite builds these checked debug binaries; performance eval uses release.
    E.EGGLOG = ROOT / "target" / "debug" / "egglog"
    E.XMULTI = ROOT / "slotted" / "xmulti" / "target" / "debug" / "xmulti"
    substitution_policies()
    merged_observations()
    graph_failure_reasons()
    goal_reporting()
    summary_reporting()
    zero_round_budget()
    substitution_refresh()
    coset_direction()
    complete_refinement()
    exit_status(*verdicts())
    print("OK: complete refinement, separate count checks, exact graph verdicts, and evaluation exit statuses")


if __name__ == "__main__":
    main()
