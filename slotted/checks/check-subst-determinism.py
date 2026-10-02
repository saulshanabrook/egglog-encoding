#!/usr/bin/env python3
"""The same program builds the same e-graph every run, `beta` included.

`slotted-subst` copies one representative of the body it substitutes into. It chooses
the smallest term, and among equal sizes the least canonical spelling -- never the e-node
the table scan happened to yield first -- because egglog's own processing order differs
between processes, and two runs that substituted different representatives would build
different e-graphs from then on. This runs one program that once did exactly that, MMM's
second-phase input under the thirteen rules of `slotted/tests/sdql-paper-mmm.egg`, several
times at two round counts, requiring equal counts and a verified isomorphism.
"""

import json
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "slotted"))
sys.path.insert(0, str(ROOT / "slotted" / "xdiff"))
import isomorphism as ISO  # noqa: E402

sc = __import__("slotted-egglog")
slotenc = __import__("slotted-encoder")
pf = __import__("paper_fixtures")

EGGLOG = ROOT / "target" / "debug" / "egglog"
TEST = ROOT / "slotted" / "tests" / "sdql-paper-mmm.egg"
SCRATCH = ROOT / "target" / "slotted"
RUNS = 4
ROUNDS = (4, 12)


def program(rounds):
    """The MMM subset test's rules and input, run for `rounds`, with the target added after."""
    forms = sc.parse(TEST.read_text())
    keep = [f for f in forms if isinstance(f, list) and f[0] in ("include", "rewrite")]
    inp, tgt = pf.workload("mmm", "2nd")
    keep += [["let", "paper-input", inp], ["run", str(rounds)], ["let", "paper-target", tgt], ["run", "0"]]
    SCRATCH.mkdir(parents=True, exist_ok=True)
    path = SCRATCH / f"subst-determinism-{rounds}.egg"
    path.write_text("\n".join(sc.render(f) for f in keep) + "\n")
    compiled = path.with_suffix(".compiled.egg")
    compiled.write_text(sc.compile_source(sc.Source(path)))
    return compiled


def compare_graphs(first, graph, issues):
    """Reject unreadable graphs, unequal counts, and missing/invalid witnesses."""
    if issues:
        return f"unreadable graph: {issues[:2]}"
    if first is None:
        return None
    if first.summary() != graph.summary():
        return f"class/node counts differ: {first.summary()} vs {graph.summary()}"
    try:
        witness, why = ISO.find_isomorphism(first, graph)
        if witness is None:
            return f"no isomorphism: {why}"
        bad = ISO.verify(first, graph, *witness)
        return f"invalid isomorphism: {bad}" if bad is not None else None
    except ISO.IsomorphismLimit as exc:
        return f"isomorphism inconclusive: {exc}"


def selftest():
    """The determinism gate must fail closed, even when counts agree."""
    from unittest.mock import patch

    def graph(op, cid):
        g = ISO.Graph()
        g.add_class(cid, [])
        g.nodes[cid] = [(op, ())]
        g.close_groups()
        return g

    first, renamed, different = graph("left", "a"), graph("left", "b"), graph("right", "b")
    assert compare_graphs(None, first, ["reader error"]) is not None
    assert compare_graphs(first, first, ["reader error"]) is not None
    assert compare_graphs(first, different, []) is not None
    assert compare_graphs(first, renamed, []) is None
    with patch.object(ISO, "find_isomorphism", side_effect=ISO.IsomorphismLimit("test bound")):
        assert compare_graphs(first, renamed, []) is not None
    with patch.object(ISO, "verify", return_value="test invalid witness"):
        assert compare_graphs(first, renamed, []) is not None


def main():
    selftest()
    if not EGGLOG.is_file():
        print(f"FAIL: {EGGLOG.relative_to(ROOT)} not built")
        return 1
    decls = pf.RULES.with_name("sdql.egg")
    ISO.use_language(slotenc.language(decls, decls.with_suffix(".ref")))
    bad = []
    for rounds in ROUNDS:
        compiled = program(rounds)
        json_path = compiled.with_suffix(".json")
        first = None
        for _ in range(RUNS):
            json_path.unlink(missing_ok=True)
            run = subprocess.run(
                [str(EGGLOG), "--to-json", *ISO.SERIALIZE_LIMITS, str(compiled)],
                capture_output=True,
                text=True,
                cwd=ROOT,
                timeout=900,
            )
            if run.returncode or not json_path.exists():
                detail = (run.stderr.strip().splitlines() or [f"exit {run.returncode}"])[-1]
                bad.append(f"{rounds} rounds: run failed: {detail[:120]}")
                break
            graph, issues = ISO.build_encoding_graph(json.loads(json_path.read_text()))
            issue = compare_graphs(first, graph, issues)
            if issue is not None:
                bad.append(f"{rounds} rounds: {issue}")
                break
            if first is None:
                first = graph
        compiled.unlink(missing_ok=True)
        json_path.unlink(missing_ok=True)
    if bad:
        for line in bad:
            print("FAIL:", line)
        return 1
    print(f"OK: {len(ROUNDS)}/{len(ROUNDS)} round counts match counts and verified isomorphism over {RUNS} runs each")
    return 0


if __name__ == "__main__":
    sys.exit(main())
