#!/usr/bin/env python3
"""Is the isomorphism checker actually discriminating, or does it just say yes?

Every other check in this tree rests on `isomorphism.py`: "N/N isomorphic" is only
worth as much as the checker's willingness to say no. `mutations.py` mutates the
COMPILER and asks whether the corpus notices; nothing mutated the CHECKER. `selftest`
does, with three hand-built graphs.

So: take real graphs, damage one copy, and require the checker to reject it. A
perturbation the checker accepts is a blind spot, and the ones here are chosen to be
the differences that matter in a slotted e-graph -- a lost node, a lost or invented
slot, a weakened symmetry group, an edge pointing somewhere else, a renaming rewired.

Two classes of mutation, treated differently on purpose:

  * STRICT ones change a count -- of classes, nodes, slots, or group elements -- so no
    graph can be isomorphic to its mutant and every single one must be caught. A miss
    here is a checker bug.
  * REWIRING ones keep every count and move an edge. Almost always that is a real
    difference, but a graph with an automorphism can absorb it, so these are reported
    as a rate rather than asserted. A LOW rate would be the interesting outcome.

    python3 slotted/xdiff/checker-mutations.py [N] [seed]
"""

import copy
import random
import sys
from collections import Counter

sys.path.insert(0, "slotted/xdiff")
import isomorphism as I
import xdiff as X


def classes_with_nodes(g):
    return [c for c in g.ids() if g.nodes[c]]


def edges_of(g):
    """(cid, node index, elem index) for every child edge in the graph."""
    return [
        (c, ni, ei) for c in g.ids() for ni, n in enumerate(g.nodes[c]) for ei, e in enumerate(n[1]) if e[0] == "child"
    ]


def set_elem(g, c, ni, ei, elem):
    op, elems = g.nodes[c][ni]
    lst = list(elems)
    lst[ei] = elem
    g.nodes[c][ni] = (op, tuple(lst))


# ------------------------------------------------------------------- mutations
def m_drop_node(g, rng):
    cs = classes_with_nodes(g)
    if not cs:
        return None
    c = rng.choice(cs)
    g.nodes[c].pop(rng.randrange(len(g.nodes[c])))
    return f"dropped a node from {c}"


def m_duplicate_node(g, rng):
    cs = classes_with_nodes(g)
    if not cs:
        return None
    c = rng.choice(cs)
    g.nodes[c].append(copy.deepcopy(rng.choice(g.nodes[c])))
    return f"duplicated a node in {c}"


def m_add_slot(g, rng):
    c = rng.choice(g.ids())
    fresh = "$mut"
    if fresh in g.slots[c]:
        return None
    g.slots[c] = g.slots[c] + (fresh,)
    g.group[c] = {p | {(fresh, fresh)} for p in g.group[c]}
    return f"added a slot to {c}"


def m_drop_slot(g, rng):
    cs = [c for c in g.ids() if g.slots[c]]
    if not cs:
        return None
    c = rng.choice(cs)
    s = rng.choice(g.slots[c])
    g.slots[c] = tuple(x for x in g.slots[c] if x != s)
    g.group[c] = {frozenset((a, b) for a, b in p if a != s and b != s) for p in g.group[c]}
    return f"dropped slot {s} from {c}"


def m_drop_symmetry(g, rng):
    cs = [c for c in g.ids() if len(g.group[c]) > 1]
    if not cs:
        return None
    c = rng.choice(cs)
    ident = frozenset((s, s) for s in g.slots[c])
    others = [p for p in g.group[c] if p != ident]
    if not others:
        return None
    g.group[c].discard(rng.choice(others))
    return f"dropped a symmetry from {c}"


def m_merge_classes(g, rng):
    if len(g.ids()) < 2:
        return None
    a, b = rng.sample(g.ids(), 2)
    if len(g.slots[a]) != len(g.slots[b]):
        return None  # merging classes of different width is not a clean count change
    g.nodes[a] = g.nodes[a] + g.nodes[b]
    for cid in list(g.slots):
        if cid == b:
            continue
        for ni, n in enumerate(g.nodes[cid]):
            g.nodes[cid][ni] = (
                n[0],
                tuple(("child", a, e[2]) if e[0] == "child" and e[1] == b else e for e in n[1]),
            )
    del g.slots[b], g.group[b], g.nodes[b]
    return f"merged {b} into {a}"


def m_redirect_edge(g, rng):
    es = edges_of(g)
    if not es or len(g.ids()) < 2:
        return None
    c, ni, ei = rng.choice(es)
    e = g.nodes[c][ni][1][ei]
    others = [x for x in g.ids() if x != e[1] and len(g.slots[x]) == len(g.slots[e[1]])]
    if not others:
        return None
    set_elem(g, c, ni, ei, ("child", rng.choice(others), e[2]))
    return f"redirected an edge in {c}"


def m_remap_edge(g, rng):
    es = [(c, ni, ei) for c, ni, ei in edges_of(g) if g.nodes[c][ni][1][ei][2]]
    if not es:
        return None
    c, ni, ei = rng.choice(es)
    e = g.nodes[c][ni][1][ei]
    pairs = list(e[2])
    k = rng.randrange(len(pairs))
    cs, ps = pairs[k]
    targets = [s for s in g.slots[c] if s != ps]
    if not targets:
        return None
    pairs[k] = (cs, rng.choice(targets))
    set_elem(g, c, ni, ei, ("child", e[1], tuple(sorted(pairs))))
    return f"rewired a renaming in {c}"


STRICT = [m_drop_node, m_duplicate_node, m_add_slot, m_drop_slot, m_drop_symmetry, m_merge_classes]
REWIRE = [m_redirect_edge, m_remap_edge]


def main():
    args = sys.argv[1:]
    n = int(args[0]) if args else 60
    seed = int(args[1]) if len(args) > 1 else 0
    rng = random.Random(seed)
    cases = [X.rand_case(rng, i) for i in range(n)]

    graphs = []
    for c in cases:
        g, err = I.reference_graph(c)
        if not err:
            graphs.append((c.name, g))
    print(f"{len(graphs)} graphs from {n} cases")

    strict = Counter()
    strict_missed = []
    rewire = Counter()
    for name, g in graphs:
        for mut in STRICT + REWIRE:
            bad = copy.deepcopy(g)
            what = mut(bad, rng)
            if what is None:
                continue  # not applicable to this graph
            got, _why = I.find_isomorphism(g, bad)
            caught = got is None
            tag = mut.__name__[2:]
            if mut in STRICT:
                strict[tag, "caught" if caught else "MISSED"] += 1
                if not caught:
                    strict_missed.append(f"{name}: {what} -- accepted as isomorphic")
            else:
                rewire[tag, "caught" if caught else "absorbed"] += 1

    print("\nSTRICT -- a count changed, so every one must be caught:")
    ok = True
    for tag in sorted({t for t, _ in strict}):
        c, m = strict[tag, "caught"], strict[tag, "MISSED"]
        ok &= m == 0
        print(f"  {tag:16} {c:5} caught  {m:5} missed{'   <-- BLIND SPOT' if m else ''}")
    print("\nREWIRING -- counts unchanged, an automorphism can absorb it:")
    for tag in sorted({t for t, _ in rewire}):
        c, a = rewire[tag, "caught"], rewire[tag, "absorbed"]
        tot = c + a
        print(f"  {tag:16} {c:5} caught  {a:5} absorbed   ({100 * c / tot:.1f}% caught)" if tot else "")
    for line in strict_missed[:20]:
        print(f"  {line}")

    total_strict = sum(v for (_, k), v in strict.items() if k in ("caught", "MISSED"))
    missed = sum(v for (_, k), v in strict.items() if k == "MISSED")
    print(f"\n{total_strict - missed}/{total_strict} count-changing mutations caught")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
