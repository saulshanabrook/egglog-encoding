"""Is the encoding's final e-graph *isomorphic* to the reference's?

Everything else here compares a projection -- the probe partition, node counts per
operator, one invariant. Two different e-graphs can agree on all of those. This
constructs a witness instead: a bijection between the two sides' e-classes, plus a
bijection between each matched pair's slots, under which the node sets are equal. If one
is found it is checked, so success is a proof; failure only means none was found within
the search cap, and is reported as such rather than as a difference.

Three things make the comparison non-trivial, and each is handled rather than assumed
away:

* **Slot names are unrelated.** The reference mints `$f0, $f1, ...` from a global
  counter; the encoding mints the smallest unused integer. So the per-class slot
  bijection is part of what is searched for, not read off.
* **A class's symmetry group is not in its node set.** A commutative class holds *one*
  node and a swap; a class without the swap holds the same one node. Comparing node sets
  alone cannot tell them apart, so the group is compared too -- recovered from the
  reference with `eq` on two invocations, and from the encoding as the idempotent-free
  self-loops `(RenamesToLeader c p c)` whose `p` permutes the class's slots.
* **A node is only defined up to those groups.** `k($0,$1)` and `k($1,$0)` are the same
  node of a commutative class, and the two sides need not store the same representative.
  So node equality quantifies over the parent's group and each child's group -- the
  reference's "strong shape" -- and over renamings of slots the node carries but its
  class does not, which is alpha-equivalence for a binder's bound slot.

Run: `python3 slotted/xdiff/isomorphism.py [name-prefix|fuzz N [seed]]`
"""

import itertools
import json
import os
import random
import subprocess
import sys

sys.path.insert(0, "slotted/xdiff")
import xdiff as X

SEARCH_CAP = 200_000

#: cases compared at a database fixpoint because the rules never stop firing
UNSATURATED = []


# --------------------------------------------------------------- s-expressions
def parse_sexpr(s, i=0):
    """Parse one s-expression, returning (tree, next index). Atoms stay strings."""
    while i < len(s) and s[i].isspace():
        i += 1
    if s[i] == "(":
        i += 1
        out = []
        while True:
            while i < len(s) and s[i].isspace():
                i += 1
            if s[i] == ")":
                return tuple(out), i + 1
            child, i = parse_sexpr(s, i)
            out.append(child)
    if s[i] == '"':
        j = s.index('"', i + 1)
        return s[i : j + 1], j + 1
    j = i
    while j < len(s) and not s[j].isspace() and s[j] not in "()":
        j += 1
    return s[i:j], j


def unparse(t):
    if isinstance(t, str):
        return t
    return "(" + " ".join(unparse(k) for k in t) + ")"


def as_map(t):
    """`(map-of 0 1 2 3)` / `(map-empty)` -> {0: 1, 2: 3}."""
    if isinstance(t, str) or t[0] == "map-empty":
        return {}
    xs = [int(v) for v in t[1:]]
    return dict(zip(xs[0::2], xs[1::2], strict=False))


# ------------------------------------------------------------------ the graphs
class Graph:
    """Classes, each with slots, a symmetry group, and a set of nodes.

    A node is `(op, elems)`; an elem is `("slot", s)` for a slot the node names
    directly, or `("child", cid, ((child_slot, parent_slot), ...))`.
    """

    def __init__(self):
        self.slots = {}  # cid -> tuple of slot names
        self.group = {}  # cid -> set of permutations, each a frozenset of pairs
        self.nodes = {}  # cid -> list of nodes

    def add_class(self, cid, slots):
        self.slots.setdefault(cid, tuple(slots))
        self.group.setdefault(cid, set())
        self.nodes.setdefault(cid, [])

    def close_groups(self):
        """Put the identity in every group.

        A group always contains it, but a slotless class's identity is the *empty*
        permutation, which the reference prints as an empty field -- indistinguishable
        from "no permutations" unless this is made explicit.
        """
        for cid, slots in self.slots.items():
            self.group[cid].add(frozenset((s, s) for s in slots))

    def ids(self):
        return sorted(self.slots)

    def summary(self):
        return (len(self.slots), sum(len(v) for v in self.nodes.values()))


def parse_reference(out):
    g = Graph()
    for line in out.splitlines():
        p = line.split()
        if not p:
            continue
        if p[0] == "CLASS":
            slots = p[3].split(",") if len(p) > 3 and p[3] else []
            g.add_class(p[1], [s for s in slots if s])
        elif p[0] == "GROUP":
            cid = p[1]
            g.add_class(cid, g.slots.get(cid, ()))
            if len(p) > 2 and p[2] != "?":
                for perm in p[2].split(";"):
                    if not perm:
                        continue
                    pairs = [tuple(x.split(">")) for x in perm.split("|")]
                    g.group[cid].add(frozenset(pairs))
            elif len(p) > 2:
                raise ValueError("group too large to enumerate")
        elif p[0] == "NODE":
            cid, op, elems = p[1], None, []
            for e in p[2:]:
                kind, _, rest = e.partition(":")
                if kind == "o":
                    op = rest if op is None else f"{op}/{rest}"
                elif kind == "s":
                    elems.append(("slot", rest))
                elif kind == "c":
                    child, _, mtext = rest.partition(":")
                    m = tuple(sorted(tuple(x.split(">")) for x in mtext.split("|") if x))
                    elems.append(("child", child, m))
            g.nodes[cid].append((op, tuple(elems)))
    g.close_groups()
    return g


def read_json_graph(doc):
    """The encoding's tables, out of egglog's serialized e-graph.

    Every row is a node with an `op`, the `eclass` it belongs to, and `children` naming other
    nodes. A class id is `{sort}-{canonical value}`, so it identifies a class instead of
    describing one -- which is the whole reason for reading the JSON rather than the printed
    tables. Renamings come back as `map-of` nodes over `i64` nodes, so their contents are
    readable too.
    """
    nodes = doc.get("nodes", {})

    def cls(node_id):
        return nodes[node_id]["eclass"]

    def is_renaming(node_id):
        return cls(node_id).startswith("Renaming-")

    # a renaming's contents, from the `map-of` node in its class
    maps = {}
    for n in nodes.values():
        if n.get("op") == "map-of" and n["eclass"].startswith("Renaming-"):
            xs = [int(nodes[c]["op"]) for c in n.get("children", [])]
            maps[n["eclass"]] = dict(zip(xs[0::2], xs[1::2], strict=False))

    def as_renaming(node_id):
        return maps.get(cls(node_id), {})

    slots_of, loops, rows, leaf = {}, [], [], {}
    for n in nodes.values():
        op, kids = n.get("op"), n.get("children", [])
        if op == "ClassSlots" and kids:
            slots_of[cls(kids[0])] = tuple(sorted(maps.get(n["eclass"], {})))
        elif op == "RenamesToLeader" and len(kids) == 3:
            loops.append((cls(kids[0]), as_renaming(kids[1]), cls(kids[2])))
        elif op == "Var":
            leaf["var"] = n["eclass"]
        elif op == "Null":
            leaf["null"] = n["eclass"]
        elif op in NODE_OPS:
            payloads, elems, i = [], [], 0
            while i < len(kids):
                if is_renaming(kids[i]) and i + 1 < len(kids):
                    elems.append(("child", cls(kids[i + 1]), as_renaming(kids[i])))
                    i += 2
                else:
                    payloads.append(nodes[kids[i]]["op"].strip('"'))
                    i += 1
            # A payload-headed row is named by its payload and a per-constructor row
            # by its tag. The payload needs the operator's `ref_prefix` in front of it,
            # because that is the spelling the REFERENCE writes and these two names are
            # about to be compared: sdql's symbols are `sym:mult` there and `mult` here,
            # and without the prefix two identical graphs refine to different colours.
            o = NODE_OPS[op]
            name = o.ref_prefix + "/".join(payloads) if payloads else (o.ref or o.ctor)
            rows.append((name, elems, n["eclass"]))
    return slots_of, loops, rows, leaf


def compose_maps(a, b):
    """`a . b`: apply `b` then `a`, dropping keys `b` sends outside `a`'s domain."""
    return {k: a[v] for k, v in b.items() if v in a}


def rename_image(u, m):
    """`m` with its image carried through `u`, leaving what `u` does not cover alone.

    Composing with `u` would *truncate*: `u` covers a class's slots, and a node may carry
    slots its class does not -- Def. 4 permits exactly that -- so the redundant ones are not in
    `u` and a plain compose drops them. They are node-local and quantified per node when nodes
    are matched, so they only need a name that cannot collide with a class slot, an int here.
    """
    return {k: u.get(v, f"~{v}") for k, v in m.items()}


def invert_map(m):
    inv = {v: k for k, v in m.items()}
    return inv if len(inv) == len(m) else None


def build_encoding_graph(doc):
    """One class per *slotted* class, merging the `U` values that make one up.

    Membership is a connected component of *any* `RenamesToLeader` link, partial ones
    included: a partial `m` in `a = m*b` is the redundancy relation, saying b's class does not
    depend on the slots `m` drops, and the reference models that as one class with the smaller
    slot set. `class-count.py` is the independent check on that reading.
    """
    slots_of, loops, rows, leaf = read_json_graph(doc)
    values = set(slots_of) | {c for _, _, c in rows} | set(leaf.values())
    for a, _m, b in loops:
        values |= {a, b}

    parent = {v: v for v in values}

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    linked = [(a, m, b) for a, m, b in loops if a != b]
    for a, _m, b in linked:
        ra, rb = find(a), find(b)
        if ra != rb:
            parent[ra] = rb

    members = {}
    for v in values:
        members.setdefault(find(v), []).append(v)

    rep_of, frame = {}, {}
    for root, group in members.items():
        # the member with the most slots is the one whose frame can express the others
        rep = max(sorted(group), key=lambda v: len(slots_of.get(v, ())))
        for v in group:
            rep_of[v] = rep
        frame[rep] = {s: s for s in slots_of.get(rep, ())}
        edges = [(a, m, b) for a, m, b in linked if find(a) == root]
        for _ in range(len(group) + 1):
            for a, m, b in edges:
                if b in frame and a not in frame:
                    frame[a] = compose_maps(m, frame[b])
                elif a in frame and b not in frame:
                    inv = invert_map(m)
                    if inv is not None:
                        frame[b] = compose_maps(inv, frame[a])
        # Where two paths disagree they differ by a symmetry of the class, and either is a
        # valid choice of frame; the group comparison accounts for it.

    unplaced = sorted(v for v in values if v not in frame)

    def up(v):
        return invert_map(frame[v]) or {}

    g = Graph()
    for rep in set(rep_of.values()):
        g.add_class(rep, slots_of.get(rep, ()))

    for a, m, b in loops:
        if a != b or a in unplaced:
            continue
        rep = rep_of[a]
        sym = compose_maps(up(a), compose_maps(m, frame[a]))
        if set(sym) == set(sym.values()) == set(g.slots[rep]):
            g.group[rep].add(frozenset(sym.items()))

    for kind, op in (("var", "var"), ("null", "null")):
        v = leaf.get(kind)
        if v is None or v in unplaced:
            continue
        u = up(v)
        elems = (("slot", u.get(0, "~0")),) if kind == "var" else ()
        g.nodes[rep_of[v]].append((op, elems))

    for name, elems, cid in rows:
        if cid in unplaced or any(c in unplaced for _, c, _ in elems):
            continue
        u = up(cid)
        moved = tuple(
            ("child", rep_of[c], tuple(sorted(rename_image(u, compose_maps(m, frame[c])).items()))) for _, c, m in elems
        )
        g.nodes[rep_of[cid]].append((name, moved))

    # rows that coincide after translating are one node, as in the reference, whose class
    # keys its nodes by shape
    for cid in list(g.nodes):
        seen, uniq = set(), []
        for n in g.nodes[cid]:
            if repr(n) not in seen:
                seen.add(repr(n))
                uniq.append(n)
        g.nodes[cid] = uniq

    g.close_groups()
    return g, unplaced


# ------------------------------------------------------- the encoding's own ops
#: The node constructors to read, mapped to the operator each belongs to, and the
#: BINDER rows mapped to what the reference calls them. Both are read off a language
#: rather than written here, so there is no list of constructor names to go stale. A
#: binder's bound slot rides in child column 0 as an edge to the var class, where the
#: reference has a `Bind`, i.e. a slot literal in that position.
NODE_OPS: dict = {}
ENC_BINDERS: dict = {}


def use_language(lang):
    """Read the two tables above off a `TermLang`.

    An operator with `ref is None` is a payload leaf, whose rows name themselves by
    their payload; anything else names itself by its tag, because a per-constructor
    language calls a row by its CONSTRUCTOR while the reference calls it by the tag.
    """
    global NODE_OPS, ENC_BINDERS
    NODE_OPS = {op.ctor: op for op in lang.ops.values()}
    # keyed by the row NAME `read_json_graph` gives a node of this operator, and
    # holding the operator itself because the rewrite needs its binder POSITIONS
    ENC_BINDERS = {op.ref or op.ctor: op for op in lang.ops.values() if op.binders}


use_language(X.LANG)  # the toy language; `xarray.py` passes its own


def to_reference_shape(g, var_class=None):
    """Rewrite the encoding's node forms into the reference's.

    Two things are spelled differently by construction, and both are documented
    where they are built (`enc` in xdiff.py / xarray.py, `define_language!` in
    xmulti):

      * a binder -- `lambda` is `lam` -- has each bound slot in a child edge to the
        var class rather than as a slot literal on the node. A node may bind SEVERAL,
        at positions the language declares: sdql's `Sum` binds its children 1 and 2 and
        its `Merge` binds 2, 3 and 4, so neither the count nor the position can be
        assumed.
      * a child edge is a dict here and a sorted pair tuple there.
    """
    out = Graph()
    for cid in g.ids():
        out.add_class(cid, g.slots[cid])
        out.group[cid] = g.group[cid]
    fresh = itertools.count()
    unfaithful = []
    for cid in g.ids():
        for op, elems in g.nodes[cid]:
            binder_op = ENC_BINDERS.get(op)
            if binder_op is not None:
                elems = list(elems)
                for i in binder_op.binders:
                    if i >= len(elems) or elems[i][0] != "child":
                        continue
                    child, m = elems[i][1], dict(elems[i][2])
                    # The bound slot rides in this edge. It can have been dropped -- a
                    # binder whose slot nothing uses -- and then there is no name left
                    # to carry over; any fresh one does, because a slot the node's
                    # class does not have is renamed freely when nodes are matched.
                    if 0 in m:
                        bound = m[0]
                    elif len(m) == 1:
                        bound = next(iter(m.values()))
                    else:
                        bound = f"_b{next(fresh)}"
                    # the position is a binder by the encoding's convention, but it
                    # still has to be the variable class, or the convention is not
                    # being followed
                    if var_class is not None and child != var_class:
                        unfaithful.append((cid, child))
                    elems[i] = ("slot", bound)
                elems = tuple(elems)
                op = binder_op.ref or binder_op.ctor
            fixed = []
            for e in elems:
                if e[0] == "child":
                    fixed.append(("child", e[1], tuple(sorted(e[2].items())) if isinstance(e[2], dict) else e[2]))
                else:
                    fixed.append(e)
            out.nodes[cid].append((op, tuple(fixed)))
    return out, unfaithful


# ------------------------------------------------------------- node equivalence
def node_slots(node, class_slots):
    """The parent-frame slots a node names, and which of them its class does not."""
    used = []
    for e in node[1]:
        if e[0] == "slot":
            used.append(e[1])
        else:
            used += [p for _, p in e[2]]
    seen, ordered = set(), []
    for s in used:
        if s not in seen:
            seen.add(s)
            ordered.append(s)
    return ordered, [s for s in ordered if s not in class_slots]


def apply_node(node, pmap, cmap, smap):
    """Rewrite a node: parent slots by `pmap`, child ids by `cmap`, child slots by
    `smap[cid]`. A slot `pmap` does not mention is left alone."""
    out = []
    for e in node[1]:
        if e[0] == "slot":
            out.append(("slot", pmap.get(e[1], e[1])))
        else:
            cid = cmap[e[1]]
            sm = smap[e[1]]
            out.append(("child", cid, tuple(sorted((sm.get(cs, cs), pmap.get(ps, ps)) for cs, ps in e[2]))))
    return (node[0], tuple(out))


def group_variants(node, gp, groups):
    """Every node equal to this one under the parent's group and the children's.

    This is the reference's "strong shape": an invocation `m` of a child class denotes
    the same thing as `m . h` for any `h` in that child's group, and the parent class
    asserting a permutation `g` means its node set is closed under applying `g`.
    """
    child_ids = [e[1] for e in node[1] if e[0] == "child"]
    # `sorted` on frozensets would use subset order, which is partial; sort by contents
    # so the enumeration is deterministic run to run
    per_child = [sorted(groups.get(c) or {frozenset()}, key=lambda p: sorted(map(str, p))) for c in child_ids]
    for g in sorted(gp or {frozenset()}, key=lambda p: sorted(map(str, p))):
        gd = dict(g)
        for combo in itertools.product(*per_child) if per_child else [()]:
            out, k = [], 0
            for e in node[1]:
                if e[0] == "slot":
                    out.append(("slot", gd.get(e[1], e[1])))
                else:
                    h = dict(combo[k])
                    k += 1
                    # m . h, then g on the parent side
                    inv = {v: kk for kk, v in h.items()}
                    m = {inv.get(cs, cs): gd.get(ps, ps) for cs, ps in e[2]}
                    out.append(("child", e[1], tuple(sorted(m.items()))))
            yield (node[0], tuple(out))


def match_nodes(src, dst, src_slots, dst_slots, pmap, cmap, smap, dst_groups):
    """Can `src`'s nodes be matched one-to-one onto `dst`'s?

    `pmap` fixes the class slots; slots the node carries but the class does not are
    existentially quantified, so every bijection between the two sides' extras is
    tried -- that is alpha-equivalence for a bound slot.
    """
    if len(src) != len(dst):
        return False
    variants = [set(group_variants(n, dst_groups[1], dst_groups[0])) for n in dst]

    def compatible(n, j):
        _, extra = node_slots(n, src_slots)
        _, dextra = node_slots(dst[j], dst_slots)
        if len(extra) != len(dextra):
            return False
        for perm in itertools.permutations(dextra):
            full = dict(pmap)
            full.update(dict(zip(extra, perm, strict=True)))
            if apply_node(n, full, cmap, smap) in variants[j]:
                return True
        return False

    # small bipartite matching
    pair = {}

    def augment(i, seen):
        for j in range(len(dst)):
            if j in seen or not compatible(src[i], j):
                continue
            seen.add(j)
            if j not in pair or augment(pair[j], seen):
                pair[j] = i
                return True
        return False

    return all(augment(i, set()) for i in range(len(src)))


# --------------------------------------------------------------- the refinement
def colors(g, rounds=6):
    col = {
        c: (len(g.slots[c]), len(g.group[c]), tuple(sorted((n[0], tuple(e[0] for e in n[1])) for n in g.nodes[c])))
        for c in g.ids()
    }
    for _ in range(rounds):
        nxt = {}
        for c in g.ids():
            sig = []
            for op, elems in g.nodes[c]:
                sig.append((op, tuple(e[0] if e[0] == "slot" else col[e[1]] for e in elems)))
            nxt[c] = (col[c], tuple(sorted(sig)))
        if all(
            len({nxt[a] for a in g.ids() if col[a] == col[c]}) == len({col[a] for a in g.ids() if col[a] == col[c]})
            for c in g.ids()
        ):
            return nxt
        col = nxt
    return col


# ---------------------------------------------------------------- the isomorphism
def find_isomorphism(ga, gb):
    """A (class bijection, per-class slot bijection) pair, or a reason there is none."""
    if len(ga.ids()) != len(gb.ids()):
        return None, (f"class count {len(ga.ids())} vs {len(gb.ids())}")
    ca, cb = colors(ga), colors(gb)
    from collections import Counter

    if Counter(ca.values()) != Counter(cb.values()):
        only_a = Counter(ca.values()) - Counter(cb.values())
        return None, f"refinement colors differ ({len(only_a)} class shapes unmatched)"

    cand = {a: [b for b in gb.ids() if cb[b] == ca[a]] for a in ga.ids()}
    order = sorted(ga.ids(), key=lambda a: len(cand[a]))
    budget = [SEARCH_CAP]

    def slot_bijections(a, b):
        sa, sb = ga.slots[a], gb.slots[b]
        if len(sa) != len(sb):
            return
        for perm in itertools.permutations(sb):
            m = dict(zip(sa, perm, strict=True))
            # the group has to correspond too, not just the slot count
            mapped = {frozenset((m[x], m[y]) for x, y in p) for p in ga.group[a]}
            if mapped == gb.group[b]:
                yield m

    phi, sig = {}, {}

    def rec(k):
        if budget[0] <= 0:
            return False
        if k == len(order):
            return verify(ga, gb, phi, sig) is None
        a = order[k]
        for b in cand[a]:
            if b in phi.values():
                continue
            for m in slot_bijections(a, b):
                budget[0] -= 1
                if budget[0] <= 0:
                    return False
                phi[a], sig[a] = b, m
                # check now if every child of every node of `a` is already assigned
                ready = all(e[0] == "slot" or e[1] in phi for n in ga.nodes[a] for e in n[1])
                if (
                    not ready
                    or match_nodes(
                        ga.nodes[a], gb.nodes[b], ga.slots[a], gb.slots[b], m, phi, sig, (gb.group, gb.group[b])
                    )
                ) and rec(k + 1):
                    return True
                del phi[a], sig[a]
        return False

    if rec(0):
        return (dict(phi), dict(sig)), None
    if budget[0] <= 0:
        return None, f"search cap ({SEARCH_CAP}) reached -- inconclusive"
    return None, "no isomorphism exists (search exhausted)"


def verify(ga, gb, phi, sig):
    """None if (phi, sig) really is an isomorphism, else the first thing wrong."""
    if sorted(phi) != ga.ids() or sorted(phi.values()) != gb.ids():
        return "not a bijection on classes"
    for a in ga.ids():
        b = phi[a]
        if len(ga.slots[a]) != len(gb.slots[b]):
            return f"{a}: slot count"
        # Checked rather than trusted: this is the proof step, and every claim it
        # rests on should be its own. A non-injective map here would let two of one
        # side's slots collapse onto one of the other's and still match nodes.
        if sorted(sig[a]) != sorted(ga.slots[a]) or sorted(sig[a].values()) != sorted(gb.slots[b]):
            return f"{a}: slot map is not a bijection"
        mapped = {frozenset((sig[a][x], sig[a][y]) for x, y in p) for p in ga.group[a]}
        if mapped != gb.group[b]:
            return f"{a}: symmetry group ({len(ga.group[a])} vs {len(gb.group[b])})"
        if not match_nodes(
            ga.nodes[a], gb.nodes[b], ga.slots[a], gb.slots[b], sig[a], phi, sig, (gb.group, gb.group[b])
        ):
            return f"{a}: node sets ({len(ga.nodes[a])} vs {len(gb.nodes[b])})"
    return None


# ------------------------------------------------------------------- the runners
#: The machinery seeds `(Var 0)` and `(Null)` unconditionally, so those two classes
#: exist on the encoding side whether or not the case mentions them. Adding the same two
#: terms to the reference makes the two graphs comparable as wholes, rather than needing
#: classes to be dropped from one side by a rule about which ones "do not count". They
#: are ordinary terms to the reference, so any rule that fires on them fires on the
#: encoding's copies too.
SEED = "term (null)\nterm (var $0)\n"

#: How the encoding's program is built. `xarray.py` swaps in the array language's
#: builder so the same isomorphism check can be run on its cases; the signature is
#: `(case, mult)`.
EGG_PROGRAM = None


def reference_graph(case):
    spec = case.spec() + SEED + "dump\n"
    r = subprocess.run(
        [str(X.XMULTI / "target" / "debug" / "xmulti")],
        input=spec,
        capture_output=True,
        text=True,
        timeout=X.RUN_TIMEOUT,
    )
    if r.returncode != 0:
        return None, f"reference error: {(r.stderr or '?').strip().splitlines()[-1]}"
    if any(line.startswith("SATURATED no") for line in r.stdout.splitlines()):
        return None, "reference did not saturate"
    return parse_reference(r.stdout), None


def canonical(g):
    """A string that determines the graph, for comparing two runs of one case."""
    return repr([(c, g.slots[c], sorted(map(sorted, g.group[c])), sorted(map(str, g.nodes[c]))) for c in g.ids()])


def _dump(case, mult, timeout):
    """The encoding's graph, from egglog's serialized e-graph.

    `--to-json` writes `<input>.json` and names a class `{sort}-{canonical value}`, an
    identity rather than a rendering, so a class whose rows have been deleted is still
    distinguishable -- where `print-function` renders every such class as the one word
    `Unextractable` and the graph cannot be rebuilt.
    """
    prog = (EGG_PROGRAM or X.egg_program)(case, mult=mult)
    prog = prog.replace("(print-function SameClass 100000)", "")
    p = X.ROOT / f"xdiff-tmp-iso-{os.getpid()}-{mult}.egg"
    j = p.with_suffix(".json")
    p.write_text(prog)
    try:
        r = subprocess.run(
            [str(X.EGGLOG), "--to-json", str(p)], capture_output=True, text=True, cwd=X.ROOT, timeout=timeout
        )
    except subprocess.TimeoutExpired:
        return None, "timeout"
    finally:
        p.unlink(missing_ok=True)
    try:
        if r.returncode != 0:
            err = [line for line in r.stderr.splitlines() if "ERROR" in line]
            return None, f"encoding error: {err[-1] if err else r.stderr[:120]}"
        if not j.exists():
            return None, "encoding produced no serialized e-graph"
        g, unplaced = build_encoding_graph(json.loads(j.read_text()))
    finally:
        j.unlink(missing_ok=True)
    if unplaced:
        return None, ("limit", f"{len(unplaced)} value(s) could not be placed in a frame: {unplaced[:2]}")
    leaf = {"var": None}
    for cid in g.ids():
        if any(n[0] == "var" for n in g.nodes[cid]):
            leaf["var"] = cid
    g, unfaithful = to_reference_shape(g, leaf.get("var"))
    if unfaithful:
        return None, f"binder position is not the variable class: {unfaithful[:2]}"
    return g, None


def encoding_graph(case):
    """The encoding's final graph, at the strongest fixpoint available to it.

    The harness's schedule saturates the `slotted` invariants between user-rule steps and
    gives the user rules a finite step count, since user rules are not expected to
    terminate. If that does not finish, the state is taken at a fixpoint of the *database*
    instead, established by two different step counts producing the same graph -- the same
    standard the partition comparison uses -- and reported separately.
    """
    g, err = _dump(case, 3, timeout=60)
    if err != "timeout":
        return g, err
    a, e1 = _dump(case, 6, timeout=180)
    if e1:
        return None, ("limit" if e1 == "timeout" else "FAIL", "encoding too slow to settle") if e1 == "timeout" else e1
    b, e2 = _dump(case, 12, timeout=180)
    if e2:
        return None, e2 if e2 != "timeout" else ("limit", "encoding too slow to settle")
    if canonical(a) != canonical(b):
        return None, "encoding has not settled: doubling the rounds changes the graph"
    UNSATURATED.append(case.name)
    return a, None


def check(case):
    # A reference that errors or will not settle gives nothing to compare against, so
    # the case is skipped. The encoding failing the same way is not a skip: the
    # reference reached a fixpoint, so not reaching one is itself a difference.
    ref, err = reference_graph(case)
    if err:
        return "skip", err
    enc, err = encoding_graph(case)
    if isinstance(err, tuple):
        return err[0], err[1]
    if err:
        return "FAIL", err
    iso, why = find_isomorphism(ref, enc)
    if iso is None:
        return "FAIL", f"{why}  [ref {ref.summary()} enc {enc.summary()}]"
    bad = verify(ref, enc, iso[0], iso[1])
    if bad:
        return "FAIL", f"witness rejected: {bad}"
    n, m = ref.summary()
    groups = sum(len(v) for v in ref.group.values())
    return "ok", (n, m, groups)


def selftest():
    """Hand-built graphs, exercising what the mutations may not reach.

    A checker that always answers "isomorphic" would pass every corpus, so the three
    answers that matter are pinned here: a pure relabelling must be *accepted*, and the
    two subtlest ways to differ -- a missing symmetry, and one edge moved -- must be
    *rejected*. No egglog and no reference, so this stays honest if either changes.
    """

    def build(spec):
        g = Graph()
        for cid, (slots, perms, nodes) in spec.items():
            g.add_class(cid, slots)
            for p in perms:
                g.group[cid].add(frozenset(p))
            g.nodes[cid] = nodes
        g.close_groups()
        return g

    def kn(child, *pairs):
        return ("k", tuple(("child", child, (p,)) for p in pairs))

    swap = [[("a", "b"), ("b", "a")]]
    base = build(
        {"v": (("x",), [], [("var", (("slot", "x"),))]), "K": (("a", "b"), swap, [kn("v", ("x", "a"), ("x", "b"))])}
    )
    cases = [
        # the same graph with every slot renamed
        (
            "relabelled",
            True,
            build(
                {
                    "w": (("q",), [], [("var", (("slot", "q"),))]),
                    "J": (("m", "n"), [[("m", "n"), ("n", "m")]], [kn("w", ("q", "m"), ("q", "n"))]),
                }
            ),
        ),
        # identical nodes, but the class does not prove the swap
        (
            "symmetry dropped",
            False,
            build(
                {
                    "w": (("q",), [], [("var", (("slot", "q"),))]),
                    "J": (("m", "n"), [], [kn("w", ("q", "m"), ("q", "n"))]),
                }
            ),
        ),
        # the swap, but both edges land on one slot
        (
            "edge moved",
            False,
            build(
                {
                    "w": (("q",), [], [("var", (("slot", "q"),))]),
                    "J": (("m", "n"), [[("m", "n"), ("n", "m")]], [kn("w", ("q", "m"), ("q", "m"))]),
                }
            ),
        ),
    ]
    bad = 0
    for name, want, other in cases:
        got, why = find_isomorphism(base, other)
        ok = (got is not None) == want
        if got is not None and verify(base, other, got[0], got[1]) is not None:
            ok = False
        bad += not ok
        print(
            f"  {'ok  ' if ok else 'FAIL'} {name:20} "
            f"isomorphic={got is not None}, expected={want}"
            f"{'' if got else '  (' + (why or '') + ')'}"
        )
    print(f"\n{len(cases) - bad}/{len(cases)} self-tests pass")
    return 1 if bad else 0


def known_groups():
    """Do BOTH readers recover a group whose size is known by hand?

    `checker-mutations.py` damages a graph AFTER it is extracted, so it shows the
    comparison discriminates -- not that either side read the graph right. A blind spot
    shared by the two readers is what it cannot see: if both lost a class's symmetries
    the checker would compare two trivial groups and pass. The corpus does not cover
    this well either. A 300-case fuzz run matches 2298 classes and 2314 group elements,
    and the identity is in every group, so only SIXTEEN non-identity permutations are
    ever compared.

    So: cases whose group is known, asked of each reader separately.
    """
    v0, v1, v2 = ("var", 0), ("var", 1), ("var", 2)

    def g(a, b):
        return ("g", a, b)

    cases = [
        # f($0,$1) = f($1,$0) -- the group is {id, swap}
        ("swap", 2, X.Case("swap", [("f", v0, v1), ("f", v1, v0)], [(("f", v0, v1), ("f", v1, v0))], [], None, [], rounds=0)),
        # g(g($0,$1),$2) = g(g($1,$2),$0) -- a 3-cycle generates three elements
        (
            "3-cycle",
            3,
            X.Case(
                "3cycle",
                [g(g(v0, v1), v2), g(g(v1, v2), v0)],
                [(g(g(v0, v1), v2), g(g(v1, v2), v0))],
                [],
                None,
                [],
                rounds=0,
            ),
        ),
    ]
    bad = 0
    for name, want, case in cases:
        ref, err = reference_graph(case)
        if err:
            print(f"  FAIL {name:9} reference: {err}")
            bad += 1
            continue
        enc, err = encoding_graph(case)
        if err:
            print(f"  FAIL {name:9} encoding: {err}")
            bad += 1
            continue
        rmax = max((len(v) for v in ref.group.values()), default=0)
        emax = max((len(v) for v in enc.group.values()), default=0)
        ok = rmax == want == emax
        bad += not ok
        print(f"  {'ok  ' if ok else 'FAIL'} {name:9} largest group: reference {rmax}, encoding {emax}, want {want}")
    print(f"\n{len(cases) - bad}/{len(cases)} groups recovered by both readers")
    return 1 if bad else 0


def main():
    args = sys.argv[1:]
    if args and args[0] == "selftest":
        return selftest()
    if args and args[0] == "known-groups":
        return known_groups()
    if args and args[0] == "fuzz":
        n = int(args[1]) if len(args) > 1 else 100
        rng = random.Random(int(args[2]) if len(args) > 2 else 0)
        cases = [X.rand_case(rng, i) for i in range(n)]
    elif args:
        cases = [c for c in X.curated() if c.name.startswith(args[0])]
    else:
        cases = X.curated()

    tally = {"ok": 0, "FAIL": 0, "skip": 0, "limit": 0}
    totals = [0, 0, 0]
    for c in cases:
        verdict, detail = check(c)
        tally[verdict] += 1
        if verdict == "ok":
            totals = [a + b for a, b in zip(totals, detail, strict=True)]
        else:
            print(f"  {verdict:4} {c.name:44} {detail}", flush=True)
    # the sizes are part of the result: a checker comparing nothing would also pass
    print(
        f"\n{tally['ok']}/{len(cases)} isomorphic"
        f"   ({tally['FAIL']} differ, {tally['skip']} skipped,"
        f" {tally['limit']} not comparable)"
    )
    print(f"matched {totals[0]} e-classes, {totals[1]} e-nodes, {totals[2]} symmetries")
    if UNSATURATED:
        print(
            f"{len(UNSATURATED)} compared at a database fixpoint, not a rule "
            f"fixpoint: {', '.join(UNSATURATED[:6])}"
            f"{' ...' if len(UNSATURATED) > 6 else ''}"
        )
    return 1 if tally["FAIL"] else 0


if __name__ == "__main__":
    sys.exit(main())
