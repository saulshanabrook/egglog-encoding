#!/usr/bin/env python3
"""A pattern is a conjunction, so the order its atoms are written in cannot matter.

The reference satisfies that by construction -- `multi_ematch` keeps a slot flexible
and lets `unify` merge it later -- so the order an atom list is given in is invisible
to it. The encoding compiles a pattern into a CHAIN: one atom leads, fixing
slots(pattern), and each later atom's frame is solved against what the prefix already
named. A slot no earlier atom constrains is MINTED, and the mint is a commitment that
cannot be revisited, so a badly ordered chain loses matches. `connected_order` exists
to avoid that and requires every atom after the first to share a pattern variable with
the prefix.

That requirement is necessary and NOT SUFFICIENT, which is what this measures. A shared
variable bound to a class with no slots -- `null`, or any leaf whose class is slotless
-- carries no slot constraint, so the atom is connected on paper and unconstrained in
fact. Its slots get minted, and a later atom naming the same slot disagrees.

Two reasons this check is worth having beside the differential one:

  * The property is INTERNAL, so it needs no oracle and runs where the differential
    half cannot -- CI included. Two orders of one pattern disagreeing is a compiler bug
    whatever the reference says.
  * It is sharper than comparing partitions. The probes of a case only see the classes
    they name, and the bug this was written for is invisible to the probes of the very
    case that exposed it: the union it loses is between the variable class and a term,
    and a bare `(var $0)` cannot be a probe. So orders are compared by their whole
    e-graph, up to isomorphism, rather than by the probe partition.

    python3 slotted/xdiff/order-independence.py [N] [seed]
"""

import itertools
import random
import sys

sys.path.insert(0, "slotted/xdiff")
import isomorphism as I
import xdiff as X

#: Orders tried per case. Every permutation of a 3-atom pattern is 6; capping keeps a
#: 4-atom pattern from costing 24 graph builds when a few already settle the question.
MAX_ORDERS = 6


def graph_for(case, rules):
    """The encoding's final graph with `rules` in the order given."""
    I.EGG_PROGRAM = lambda c, mult: X.egg_program(c, rules, mult)
    try:
        return I.encoding_graph(case)
    finally:
        I.EGG_PROGRAM = None


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
            g, err = graph_for(case, rules)
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
