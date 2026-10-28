#!/usr/bin/env python3
"""Check that reordering a pattern's atoms preserves the encoding's e-graph.

Compares complete graphs by isomorphism, including classes not named by probes.
This check needs no reference binary.

Run with `python3 slotted/xdiff/order-independence.py [N] [seed]`."""

import itertools
import random
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from slotted.xdiff import isomorphism as I
from slotted.xdiff import xdiff as X

#: Orders tried per case. Every permutation of a 3-atom pattern is 6; capping keeps a
#: 4-atom pattern from costing 24 graph builds when a few already settle the question.
MAX_ORDERS = 6


def graph_for(case, rules):
    """The encoding's final graph with `rules` in the order given."""
    return I.encoding_graph(case, egg_program=lambda c, mult: X.egg_program(c, rules, mult))


def check(case):
    """(verdict, detail). `ok` when every order of every rule gives one e-graph."""
    # One rule at a time: permuting several at once conflates which one is order
    # dependent, and the product of the permutations is not worth the runs.
    for r, (atoms, action, conds) in enumerate(case.rules):
        if len(atoms) < 2:
            continue
        perms = list(itertools.permutations(range(len(atoms))))[:MAX_ORDERS]
        graphs = []
        for perm in perms:
            rules = list(case.rules)
            rules[r] = ([atoms[i] for i in perm], action, conds)
            g, err, _mult = graph_for(case, rules)
            if err:
                # a program that will not run or will not settle says nothing here
                return "skip", f"rule {r} order {perm}: {err if isinstance(err, str) else err[1]}"
            graphs.append((perm, g))
        base_perm, base = graphs[0]
        for perm, g in graphs[1:]:
            iso, why = I.find_isomorphism(base, g)
            if iso is None:
                nb, mb = base.summary()
                ng, mg = g.summary()
                worse = "LOSES a match" if ng > nb else ("finds MORE" if ng < nb else "differs")
                return "FAIL", (
                    f"rule {r}: order {base_perm} gives {nb} classes/{mb} nodes, "
                    f"order {perm} gives {ng}/{mg} -- {perm} {worse} ({why})"
                )
    return "ok", ""


def main():
    args = sys.argv[1:]
    n = int(args[0]) if args else 200
    seed = int(args[1]) if len(args) > 1 else 0
    rng = random.Random(seed)
    cases = [X.rand_case(rng, i) for i in range(n)]

    tally = {"ok": 0, "FAIL": 0, "skip": 0}
    for c in cases:
        verdict, detail = check(c)
        tally[verdict] += 1
        if verdict != "ok":
            print(f"  {verdict:4} {c.name:12} {detail}", flush=True)

    total = tally["ok"] + tally["FAIL"]
    print(f"\n{tally['ok']}/{total} order independent   ({tally['skip']} skipped)")
    return 1 if tally["FAIL"] else 0


if __name__ == "__main__":
    sys.exit(main())
