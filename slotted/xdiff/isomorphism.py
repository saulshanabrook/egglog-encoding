"""Is the encoding's final e-graph *isomorphic* to the reference's?

Everything else here compares a projection -- the probe partition, node counts per
operator, one invariant. Two different e-graphs can agree on all of those. This
constructs a witness instead: a bijection between the two sides' e-classes, plus a
bijection between each matched pair's slots, under which the node sets are equal. A
candidate is rechecked against all class, slot, group, and node-set obligations before
success is reported. The checker deliberately has direct positive and negative tests
for each quotient operation; this recheck is not an independent proof implementation,
because it shares the node matcher with the search. Failure only means none was found
within the search cap, and is reported as such rather than as a difference.

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
import re
import subprocess
import sys

sys.path.insert(0, "slotted/xdiff")
import xdiff as X

SEARCH_CAP = 200_000
MATCH_VARIANT_CAP = 200_000


class IsomorphismLimit(RuntimeError):
    """The exact comparison exceeded a declared work bound."""


#: cases compared at a database fixpoint because the rules never stop firing
UNSATURATED = []

#: Raise egglog's serialization limits, which default to 40 and silently truncate -- see
#: `_dump`. Well past anything a generated case reaches, while still bounding the dump.
SERIALIZE_LIMITS = ["--max-functions", "1000000", "--max-calls-per-function", "1000000"]


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
    maps, issues = {}, []
    for n in nodes.values():
        if n.get("op") == "map-of" and n["eclass"].startswith("Renaming-"):
            xs = [int(nodes[c]["op"]) for c in n.get("children", [])]
            if len(xs) % 2:
                issues.append(f"odd map-of row in {n['eclass']}")
            maps[n["eclass"]] = dict(zip(xs[0::2], xs[1::2], strict=False))
            if len(set(maps[n["eclass"]].values())) != len(maps[n["eclass"]]):
                issues.append(f"non-injective renaming in {n['eclass']}")

    def as_renaming(node_id):
        cid = cls(node_id)
        if cid not in maps:
            issues.append(f"no map-of row for {cid}")
            return {}
        return maps[cid]

    slots_of, loops, rows, leaf = {}, [], [], {}
    leaf_rows = {"var": 0, "null": 0}
    for n in nodes.values():
        op, kids = n.get("op"), n.get("children", [])
        if op == "ClassSlots" and kids:
            m = maps.get(n["eclass"])
            if m is None:
                issues.append(f"no map-of row for ClassSlots result {n['eclass']}")
                m = {}
            if any(k != v for k, v in m.items()):
                issues.append(f"ClassSlots result {n['eclass']} is not an identity map: {m}")
            value, slots = cls(kids[0]), tuple(sorted(m))
            if value in slots_of and slots_of[value] != slots:
                issues.append(f"conflicting ClassSlots rows for {value}")
            slots_of[value] = slots
        elif op == "RenamesToLeader" and len(kids) == 3:
            loops.append((cls(kids[0]), as_renaming(kids[1]), cls(kids[2])))
        elif op == "Var":
            leaf_rows["var"] += 1
            if len(kids) != 1:
                issues.append(f"{n['eclass']} Var: {len(kids)} payloads, expected 1")
            else:
                try:
                    leaf["var_slot"] = int(nodes[kids[0]]["op"])
                    if leaf["var_slot"] != 0:
                        issues.append(f"{n['eclass']} Var: payload slot is not canonical 0")
                except (KeyError, TypeError, ValueError):
                    issues.append(f"{n['eclass']} Var: payload is not an i64 slot")
            if "var" in leaf and leaf["var"] != n["eclass"]:
                issues.append("Var rows occur in more than one U e-class")
            leaf["var"] = n["eclass"]
        elif op == "Null":
            leaf_rows["null"] += 1
            if kids:
                issues.append(f"{n['eclass']} Null: {len(kids)} payloads, expected 0")
            if "null" in leaf and leaf["null"] != n["eclass"]:
                issues.append("Null rows occur in more than one U e-class")
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
            rows.append((name, elems, n["eclass"], o))
    for kind, count in leaf_rows.items():
        if count != 1:
            issues.append(f"expected exactly one raw {kind.title()} row, found {count}")
    return slots_of, loops, rows, leaf, issues


def validate_encoding_rows(slots_of, rows, leaf, same_class=None):
    """Reject raw rows whose structure the reference-shape conversion would erase.

    In particular, converting a binder edge to a slot literal necessarily discards its
    child class and all keys but `0`.  Those are invariants, not irrelevant spelling:
    accepting a wrong child or an extra key here could make a malformed encoding graph
    look isomorphic after conversion.  Ordinary edges get Def. 4's exact-domain check
    for the same reason -- frame composition otherwise truncates an extra key.
    """
    issues = []
    var_class = leaf.get("var")
    for name, elems, cid, op in rows:
        if len(elems) != len(op.kid_cols):
            issues.append(f"{cid} {name}: {len(elems)} children, expected {len(op.kid_cols)}")
            continue
        for i, elem in enumerate(elems):
            if elem[0] != "child":
                issues.append(f"{cid} {name} child {i + 1}: not a child edge")
                continue
            child, m = elem[1], elem[2]
            if i in op.binders:
                if set(m) != {0}:
                    issues.append(f"{cid} {name} binder {i + 1}: domain {sorted(m)}, expected [0]")
                if same_class is not None and (var_class is None or not same_class(child, var_class)):
                    issues.append(f"{cid} {name} binder {i + 1}: child {child}, expected variable class {var_class}")
            elif child not in slots_of:
                issues.append(f"{cid} {name} child {i + 1}: no ClassSlots row for {child}")
            elif set(m) != set(slots_of[child]):
                issues.append(
                    f"{cid} {name} child {i + 1}: edge domain {sorted(m)}, child slots {sorted(slots_of[child])}"
                )

        # Def. 4 also requires the class slots to be a subset of every node's free
        # slots. Binder marker columns are private names, and all bound names are
        # removed only from the one covered child; uncovered columns retain them.
        bound = {elems[i][2].get(0) for i in op.binders if i < len(elems) and elems[i][0] == "child"}
        bound.discard(None)
        free = set()
        for i, elem in enumerate(elems):
            if elem[0] != "child" or i in op.binders:
                continue
            image = set(elem[2].values())
            free |= image - bound if i == op.covered else image
        if cid in slots_of and not set(slots_of[cid]).issubset(free):
            issues.append(
                f"{cid} {name}: class slots {sorted(slots_of[cid])} not contained in node slots {sorted(free)}"
            )
    return issues


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

    A CLASS WITH NO NODE IN IT IS A REAL SIGNAL, and nothing here hides one. The reference
    never produces one, and across a 1200-case sweep neither do we -- but only once the
    serialization limits `_dump` sets are in place. At egglog's defaults `RenamesToLeader`
    truncates at 40 rows, links go missing, components split, and the leftovers look
    exactly like classes the encoding failed to merge.
    """
    slots_of, loops, rows, leaf, issues = read_json_graph(doc)
    values = set(slots_of) | {c for _, _, c, _ in rows} | {leaf[k] for k in ("var", "null") if k in leaf}
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

    issues += [f"{v}: no ClassSlots row" for v in sorted(values) if v not in slots_of]
    issues += validate_encoding_rows(slots_of, rows, leaf, lambda a, b: find(a) == find(b))
    if "null" in leaf and slots_of.get(leaf["null"], ()):
        issues.append(f"{leaf['null']} Null: class slots must be empty")
    if "var" in leaf and "var_slot" in leaf:
        var_slots = set(slots_of.get(leaf["var"], ()))
        if not var_slots.issubset({leaf["var_slot"]}):
            issues.append(
                f"{leaf['var']} Var: class slots {sorted(var_slots)} are not a subset "
                f"of its payload slot {leaf['var_slot']}"
            )

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
    issues += [f"{v}: could not be placed in a class frame" for v in unplaced]

    # A frame is a bijection between the one slotted class's live slots as seen from
    # the chosen representative and from this member.  `invert_map(...) or {}` used to
    # turn a partial/non-injective frame into the empty map and keep going, which could
    # erase precisely the slot difference the isomorphism check is meant to observe.
    for v, m in frame.items():
        rep = rep_of[v]
        if set(m) != set(slots_of.get(rep, ())) or set(m.values()) != set(slots_of.get(v, ())) or invert_map(m) is None:
            issues.append(
                f"{v}: frame is not a bijection from {sorted(slots_of.get(rep, ()))} to {sorted(slots_of.get(v, ()))}"
            )

    # Everything below composes and inverts frames.  Once raw validation has shown
    # one malformed, reconstruction cannot add useful evidence and must not crash
    # while trying to interpret that malformed value.
    if issues:
        return Graph(), issues

    def up(v):
        return invert_map(frame[v])

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
        else:
            issues.append(f"{a}: framed self-loop is not a permutation of {sorted(g.slots[rep])}")

    # Matching consumes the ACTUAL self-loop facts, so do not repair a missing group
    # element in the reader. Require those rows to contain the identity and already be
    # closed, then require every non-self relation to be path-consistent modulo that
    # recorded group.
    for rep, perms in g.group.items():
        identity = frozenset((s, s) for s in g.slots[rep])
        if identity not in perms:
            issues.append(f"{rep}: no identity RenamesToLeader self-loop")
        closure = set(perms) | {identity}
        changed = True
        while changed:
            changed = False
            current = list(closure)
            for p in current:
                pd = dict(p)
                for q in current:
                    composed = frozenset(compose_maps(pd, dict(q)).items())
                    if composed not in closure:
                        closure.add(composed)
                        changed = True
        if closure != perms:
            issues.append(f"{rep}: self-loop permutations are not a closed group")

    for a, m, b in linked:
        if a in unplaced or b in unplaced:
            continue
        rep = rep_of[a]
        relative = frozenset(compose_maps(up(a), compose_maps(m, frame[b])).items())
        if relative not in g.group[rep]:
            issues.append(f"{a} = m*{b}: relation is inconsistent with recorded symmetry group")

    for kind, op in (("var", "var"), ("null", "null")):
        v = leaf.get(kind)
        if v is None or v in unplaced:
            continue
        u = up(v)
        raw_slot = leaf.get("var_slot", 0)
        elems = (("slot", u.get(raw_slot, f"~{raw_slot}")),) if kind == "var" else ()
        g.nodes[rep_of[v]].append((op, elems))

    for name, elems, cid, _op in rows:
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
    return g, issues


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
                        unfaithful.append((cid, f"missing binder child {i + 1}"))
                        continue
                    child, m = elems[i][1], dict(elems[i][2])
                    # The bound slot rides in this edge, and may be gone by the time it
                    # gets here -- so a fresh name stands in, which is sound because a
                    # slot the node's class does not have is renamed freely when nodes
                    # are matched.
                    #
                    # `validate_encoding_rows` has already checked the raw edge's exact
                    # domain and child before frame translation can erase either.  A
                    # missing name here is therefore the valid consequence of translating
                    # through the slotless variable class, and a fresh alpha-name is the
                    # reference shape it denotes.
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
    variant_work = 0
    variants = []
    for n in dst:
        current = set()
        for variant in group_variants(n, dst_groups[1], dst_groups[0]):
            variant_work += 1
            if variant_work > MATCH_VARIANT_CAP:
                raise IsomorphismLimit(f"node-variant cap ({MATCH_VARIANT_CAP}) reached -- inconclusive")
            current.add(variant)
        variants.append(current)

    def compatible(n, j):
        _, extra = node_slots(n, src_slots)
        _, dextra = node_slots(dst[j], dst_slots)
        if len(extra) != len(dextra):
            return False
        for perm in itertools.permutations(dextra):
            nonlocal variant_work
            variant_work += 1
            if variant_work > MATCH_VARIANT_CAP:
                raise IsomorphismLimit(f"node-variant cap ({MATCH_VARIANT_CAP}) reached -- inconclusive")
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
        if k == len(order):
            return verify(ga, gb, phi, sig) is None
        if budget[0] <= 0:
            return False
        a = order[k]
        for b in cand[a]:
            if b in phi.values():
                continue
            for m in slot_bijections(a, b):
                budget[0] -= 1
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

    try:
        if rec(0):
            return (dict(phi), dict(sig)), None
    except IsomorphismLimit as exc:
        return None, str(exc)
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
        # Checked rather than trusted: a non-injective map here would let two of one
        # side's slots collapse onto one of the other's and still match nodes. Node
        # equality below deliberately reuses the search matcher, so the surrounding
        # selftests independently exercise its group and redundant-slot quotients.
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


def reference_graph(case, mult=3):
    """The reference's graph after the SAME number of rounds the encoding gets steps.

    NOT SATURATION -- a fixed count, because a generated rule set need not have a fixpoint.
    A reference round applies every rule once and so does one `(run)` of the encoding's
    user rules, so at equal counts the two are answering the same question whether or not
    either has settled. `fuzz1152`, which never settles, is isomorphic at every budget from
    3 to 12 rounds. This used to skip a case the moment the reference reported
    `SATURATED no`, which threw away the only cases that test unbounded growth.

    The count is the ENCODING's, `rounds * mult`, since `_dump` runs
    `schedule(rounds * mult)`. Where the reference saturates the extra rounds change
    nothing, so it is safe for the whole corpus.

    Scaled by rewriting the spec's own `rounds` line rather than by rebuilding the case:
    `xarray` and `xsdql` bring their own case and rule types, and only the spec text is
    common to all three.
    """
    spec = case.spec()
    spec, subbed = re.subn(r"^rounds \d+$", f"rounds {case.rounds * mult}", spec, count=1, flags=re.M)
    assert subbed, f"{case.name}: spec has no `rounds` line to scale"
    try:
        r = subprocess.run(
            [str(X.XMULTI / "target" / "debug" / "xmulti")],
            input=spec + SEED + "dump\n",
            capture_output=True,
            text=True,
            timeout=X.RUN_TIMEOUT,
        )
    except subprocess.TimeoutExpired:
        # The reference running out of time is NOT a finding -- it is a case that cannot
        # be compared, which the encoding side has always reported that way. A rule with
        # unrelated atoms is a cross product, so some of those are simply too much work
        # for the reference; the small ones still finish and still get compared.
        return None, "reference timeout"
    if r.returncode != 0:
        if "REFERENCE_LIMIT:" in r.stderr:
            detail = next(line for line in r.stderr.splitlines() if "REFERENCE_LIMIT:" in line)
            return None, f"reference dump unavailable: {detail.strip()}"
        lines = (r.stderr or "?").strip().splitlines()
        detail = next(
            (line for line in lines if "panicked at" in line or "assertion" in line or "ERROR" in line),
            lines[-1],
        )
        return None, f"reference error: {detail}"
    try:
        return parse_reference(r.stdout), None
    except ValueError as exc:
        # The pinned oracle deliberately declines to enumerate symmetry groups above
        # six live slots.  That is a coverage limit, not evidence of agreement.
        return None, f"reference dump unavailable: {exc}"


def canonical(g):
    """A string that determines the graph, for comparing two runs of one case."""
    return repr([(c, g.slots[c], sorted(map(sorted, g.group[c])), sorted(map(str, g.nodes[c]))) for c in g.ids()])


def incomplete_serialization(stderr):
    """The successful CLI diagnostics that mean its JSON is only a prefix."""
    return [line.strip() for line in stderr.splitlines() if re.search(r"\b(?:Omitted|Truncated):", line)]


def _dump(case, mult, timeout):
    """The encoding's graph, from egglog's serialized e-graph.

    `--to-json` writes `<input>.json` and names a class `{sort}-{canonical value}`, an
    identity rather than a rendering, so a class whose rows have been deleted is still
    distinguishable -- where `print-function` renders every such class as the one word
    `Unextractable` and the graph cannot be rebuilt.

    THE LIMITS ARE NOT OPTIONAL. `--max-functions` and `--max-calls-per-function` default
    to 40 each -- documented as "maximum number of function nodes to render in dot/svg
    output", and `--to-json` inherits them. Any constructor with more than 40 rows is then
    TRUNCATED, and the graph stops growing while the e-graph does not, which reads as the
    encoding stalling against a reference that keeps going. Current egglog reports an
    incomplete serialization as `Omitted:` or `Truncated:` on stderr, even on exit zero;
    those diagnostics are therefore part of the reader's validity check.
    """
    prog = (EGG_PROGRAM or X.egg_program)(case, mult=mult)
    prog = prog.replace("(print-function SameClass 100000)", "")
    p = X.ROOT / f"xdiff-tmp-iso-{os.getpid()}-{mult}.egg"
    j = p.with_suffix(".json")
    p.write_text(prog)
    try:
        r = subprocess.run(
            [str(X.EGGLOG), "--to-json", *SERIALIZE_LIMITS, str(p)],
            capture_output=True,
            text=True,
            cwd=X.ROOT,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired:
        return None, "timeout"
    finally:
        p.unlink(missing_ok=True)
    try:
        if r.returncode != 0:
            err = [line for line in r.stderr.splitlines() if "ERROR" in line]
            return None, f"encoding error: {err[-1] if err else r.stderr[:120]}"
        incomplete = incomplete_serialization(r.stderr)
        if incomplete:
            return None, ("unreadable", f"incomplete encoding serialization: {incomplete[:2]}")
        if not j.exists():
            return None, "encoding produced no serialized e-graph"
        g, issues = build_encoding_graph(json.loads(j.read_text()))
    finally:
        j.unlink(missing_ok=True)
    if issues:
        # Its own outcome, not "not comparable": that bucket is for a run that ran out of
        # TIME, and this is a graph the reader could not rebuild -- a different thing,
        # and one that could be hiding an encoding defect rather than a budget.
        return None, ("unreadable", f"{len(issues)} encoding graph issue(s): {issues[:2]}")
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
        return g, err, 3
    a, e1 = _dump(case, 6, timeout=180)
    if e1:
        err = ("limit", "encoding too slow to settle") if e1 == "timeout" else e1
        return None, err, 6
    b, e2 = _dump(case, 12, timeout=180)
    if e2:
        err = e2 if e2 != "timeout" else ("limit", "encoding too slow to settle")
        return None, err, 12
    if canonical(a) != canonical(b):
        return None, "encoding has not settled: doubling the rounds changes the graph", 12
    UNSATURATED.append(case.name)
    return a, None, 6


def check(case, encoding_builder=None, reference_builder=None):
    # Only a reference that ERRORS is skipped. One that has not settled is compared
    # anyway, at the same fixed number of rounds the encoding gets steps -- see
    # `reference_graph`.
    encoding_builder = encoding_builder or encoding_graph
    reference_builder = reference_builder or reference_graph
    enc, err, mult = encoding_builder(case)
    if isinstance(err, tuple):
        return err[0], err[1]
    if err:
        return "FAIL", err
    # The timeout fallback may have selected a larger fixed-round graph.  Build the
    # reference at that exact multiplier; comparing ref@3 to enc@6 is not meaningful.
    ref, err = reference_builder(case, mult)
    if err:
        # A timeout or an oracle serialization ceiling is NOT COMPARABLE. An
        # unexpected oracle panic is a hard unreadable result: silently skipping it
        # could make the suite green by removing precisely the difficult cases.
        unavailable = err == "reference timeout" or err.startswith("reference dump unavailable:")
        return ("limit" if unavailable else "unreadable"), err
    iso, why = find_isomorphism(ref, enc)
    if iso is None:
        if why and why.endswith("-- inconclusive"):
            return "limit", why
        return "FAIL", f"{why}  [ref {ref.summary()} enc {enc.summary()}]"
    bad = verify(ref, enc, iso[0], iso[1])
    if bad:
        return "FAIL", f"witness rejected: {bad}"
    n, m = ref.summary()
    groups = sum(len(v) for v in ref.group.values())
    return "ok", (n, m, groups)


def selftest():
    """Hand-built graphs, exercising what the mutations may not reach.

    A checker that always answers "isomorphic" would pass every corpus, so direct graph
    answers are pinned here: relabelling, symmetry-equivalent child representatives,
    and redundant-slot alpha-renaming must be *accepted*; missing symmetries, moved
    edges, nonmember permutations, and broken repeated-slot sharing must be *rejected*.
    The raw encoding reader is tested too: it must not silently discard malformed
    binder structure or a Def. 4 edge-domain difference.  No egglog and no reference,
    so these stay honest if either changes.
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

    def cycle_edge_graph(prefix, second_edge):
        """A C3 child used twice, so one global slot map cannot hide its edge reps."""
        a, b, c = (f"{prefix}a", f"{prefix}b", f"{prefix}c")
        x, y, z = (f"{prefix}x", f"{prefix}y", f"{prefix}z")
        cycle = [(a, b), (b, c), (c, a)]
        cycle2 = [(a, c), (b, a), (c, b)]
        identity_edge = ((a, x), (b, y), (c, z))
        return build(
            {
                f"{prefix}C": (
                    (a, b, c),
                    [cycle, cycle2],
                    [("triple", (("slot", a), ("slot", b), ("slot", c)))],
                ),
                f"{prefix}P": (
                    (x, y, z),
                    [],
                    [
                        (
                            "pair",
                            (
                                ("slot", x),
                                ("slot", y),
                                ("slot", z),
                                ("child", f"{prefix}C", identity_edge),
                                ("child", f"{prefix}C", tuple(second_edge(a, b, c, x, y, z))),
                            ),
                        )
                    ],
                ),
            }
        )

    cycle_source = cycle_edge_graph("s", lambda a, b, c, x, y, z: ((a, x), (b, y), (c, z)))
    matcher_cases = [
        # The second child is stored under a different representative, reached by
        # the child's order-three symmetry.  The first edge prevents one global
        # class-slot bijection from absorbing that local representative choice.
        (
            "child 3-cycle representative",
            True,
            cycle_source,
            cycle_edge_graph("t", lambda a, b, c, x, y, z: ((c, x), (a, y), (b, z))),
        ),
        # A reflection is not in C3, even though it is a permutation of the same
        # three slots and conjugates C3 to itself.
        (
            "nonmember child representative",
            False,
            cycle_source,
            cycle_edge_graph("u", lambda a, b, c, x, y, z: ((a, x), (c, y), (b, z))),
        ),
        # Def. 8 extends the class-slot bijection independently for every e-node.
        # Thus one redundant name shared across two source nodes need not remain a
        # shared name across those two distinct target nodes.
        (
            "node-local redundant alpha",
            True,
            build({"r": ((), [], [("left", (("slot", "x"),)), ("right", (("slot", "x"),))])}),
            build({"q": ((), [], [("left", (("slot", "y"),)), ("right", (("slot", "z"),))])}),
        ),
        # Within one node, however, a bijection must preserve repeated-name
        # equality: alpha-renaming xx to yy is valid, but splitting xx into yz is not.
        (
            "redundant equality alpha",
            True,
            build({"r": ((), [], [("bind", (("slot", "x"), ("slot", "x")))])}),
            build({"q": ((), [], [("bind", (("slot", "y"), ("slot", "y")))])}),
        ),
        (
            "redundant equality split",
            False,
            build({"r": ((), [], [("bind", (("slot", "x"), ("slot", "x")))])}),
            build({"q": ((), [], [("bind", (("slot", "y"), ("slot", "z")))])}),
        ),
    ]
    for name, want, left, right in matcher_cases:
        got, why = find_isomorphism(left, right)
        ok = (got is not None) == want
        if got is not None and verify(left, right, got[0], got[1]) is not None:
            ok = False
        bad += not ok
        print(
            f"  {'ok  ' if ok else 'FAIL'} {name:32} "
            f"isomorphic={got is not None}, expected={want}"
            f"{'' if got else '  (' + (why or '') + ')'}"
        )

    lam, fop = X.LANG["lam"], X.LANG["f"]
    slots = {"var": (), "body": ()}
    valid = ("lam", [("child", "var", {0: 7}), ("child", "body", {})], "lc", lam)
    reader_cases = [
        ("valid binder row", False, [valid]),
        (
            "binder via leader",
            False,
            [("lam", [("child", "leader", {0: 7}), ("child", "body", {})], "lc", lam)],
        ),
        (
            "extra binder key",
            True,
            [("lam", [("child", "var", {0: 7, 1: 8}), ("child", "body", {})], "lc", lam)],
        ),
        (
            "wrong binder child",
            True,
            [("lam", [("child", "body", {0: 7}), ("child", "body", {})], "lc", lam)],
        ),
        (
            "wide ordinary edge",
            True,
            [("f", [("child", "body", {0: 7}), ("child", "body", {})], "fc", fop)],
        ),
    ]

    def same(a, b):
        return a == b or {a, b} == {"leader", "var"}

    for name, want_bad, rows in reader_cases:
        issues = validate_encoding_rows(slots, rows, {"var": "var"}, same)
        ok = bool(issues) == want_bad
        bad += not ok
        print(f"  {'ok  ' if ok else 'FAIL'} reader {name:20} rejected={bool(issues)}, expected={want_bad}")

    def null_doc(with_slots=True, slots=()):
        nodes = {
            "n": {"op": "Null", "eclass": "U-n", "children": []},
            "i0": {"op": "0", "eclass": "i64-0", "children": []},
            "v": {"op": "Var", "eclass": "U-v", "children": ["i0"]},
            "vm": {"op": "map-of", "eclass": "Renaming-var-id", "children": ["i0", "i0"]},
            "vcs": {"op": "ClassSlots", "eclass": "Renaming-var-id", "children": ["v"]},
            "vrtl": {"op": "RenamesToLeader", "eclass": "Unit-vrtl", "children": ["v", "vm", "v"]},
        }
        if with_slots:
            children = []
            for i, slot in enumerate(slots):
                key, val = f"k{i}", f"v{i}"
                nodes[key] = {"op": str(slot), "eclass": f"i64-k{i}", "children": []}
                nodes[val] = {"op": str(slot), "eclass": f"i64-v{i}", "children": []}
                children += [key, val]
            nodes["m"] = {"op": "map-of", "eclass": "Renaming-id", "children": children}
            nodes["cs"] = {"op": "ClassSlots", "eclass": "Renaming-id", "children": ["n"]}
            nodes["rtl"] = {"op": "RenamesToLeader", "eclass": "Unit-rtl", "children": ["n", "m", "n"]}
        return {"nodes": nodes}

    nonidentity_var = {
        "nodes": {
            "i0": {"op": "0", "eclass": "i64-0", "children": []},
            "i1": {"op": "1", "eclass": "i64-1", "children": []},
            "v": {"op": "Var", "eclass": "U-v", "children": ["i0"]},
            "m": {"op": "map-of", "eclass": "Renaming-weird", "children": ["i0", "i1"]},
            "cs": {"op": "ClassSlots", "eclass": "Renaming-weird", "children": ["v"]},
            "rtl": {"op": "RenamesToLeader", "eclass": "Unit-rtl", "children": ["v", "m", "v"]},
        }
    }
    inconsistent_cycle = {
        "nodes": {
            "i0": {"op": "0", "eclass": "i64-0", "children": []},
            "i1": {"op": "1", "eclass": "i64-1", "children": []},
            "mid": {"op": "map-of", "eclass": "Renaming-id", "children": ["i0", "i0", "i1", "i1"]},
            "mswap": {"op": "map-of", "eclass": "Renaming-swap", "children": ["i0", "i1", "i1", "i0"]},
            "a": {"op": "opaque-a", "eclass": "U-a", "children": []},
            "b": {"op": "opaque-b", "eclass": "U-b", "children": []},
            "csa": {"op": "ClassSlots", "eclass": "Renaming-id", "children": ["a"]},
            "csb": {"op": "ClassSlots", "eclass": "Renaming-id", "children": ["b"]},
            "aa": {"op": "RenamesToLeader", "eclass": "Unit-aa", "children": ["a", "mid", "a"]},
            "bb": {"op": "RenamesToLeader", "eclass": "Unit-bb", "children": ["b", "mid", "b"]},
            "ab-id": {"op": "RenamesToLeader", "eclass": "Unit-ab1", "children": ["a", "mid", "b"]},
            "ab-swap": {"op": "RenamesToLeader", "eclass": "Unit-ab2", "children": ["a", "mswap", "b"]},
        }
    }
    seeded = null_doc()["nodes"]
    seeded.update(inconsistent_cycle["nodes"])
    inconsistent_cycle = {"nodes": seeded}

    def noninjective_link(reverse=False):
        doc = null_doc()
        doc["nodes"].update(
            {
                "i1": {"op": "1", "eclass": "i64-1", "children": []},
                "wide-id": {
                    "op": "map-of",
                    "eclass": "Renaming-wide-id",
                    "children": ["i0", "i0", "i1", "i1"],
                },
                "bad": {
                    "op": "map-of",
                    "eclass": "Renaming-bad",
                    "children": ["i0", "i0", "i1", "i0"],
                },
                "a": {"op": "opaque-a", "eclass": "U-a", "children": []},
                "b": {"op": "opaque-b", "eclass": "U-b", "children": []},
                "csa": {"op": "ClassSlots", "eclass": "Renaming-wide-id", "children": ["a"]},
                "csb": {"op": "ClassSlots", "eclass": "Renaming-wide-id", "children": ["b"]},
                "aa": {"op": "RenamesToLeader", "eclass": "Unit-aa", "children": ["a", "wide-id", "a"]},
                "bb": {"op": "RenamesToLeader", "eclass": "Unit-bb", "children": ["b", "wide-id", "b"]},
                "bad-link": {
                    "op": "RenamesToLeader",
                    "eclass": "Unit-bad-link",
                    "children": ["b" if reverse else "a", "bad", "a" if reverse else "b"],
                },
            }
        )
        return doc

    full_reader_cases = [
        ("complete empty Null", False, null_doc()),
        ("missing ClassSlots", True, null_doc(with_slots=False)),
        ("nonidentity ClassSlots", True, nonidentity_var),
        ("slots on Null", True, null_doc(slots=(0,))),
        ("inconsistent RTL cycle", True, inconsistent_cycle),
        ("noninjective RTL forward", True, noninjective_link()),
        ("noninjective RTL reverse", True, noninjective_link(reverse=True)),
    ]
    var_one = null_doc()
    var_one["nodes"]["i1"] = {"op": "1", "eclass": "i64-1", "children": []}
    var_one["nodes"]["v"]["children"] = ["i1"]
    duplicate_var = null_doc()
    duplicate_var["nodes"]["v2"] = {"op": "Var", "eclass": "U-v", "children": ["i0"]}
    full_reader_cases += [
        ("noncanonical Var", True, var_one),
        ("duplicate Var row", True, duplicate_var),
    ]
    for name, want_bad, doc in full_reader_cases:
        _g, issues = build_encoding_graph(doc)
        ok = bool(issues) == want_bad
        bad += not ok
        print(f"  {'ok  ' if ok else 'FAIL'} full reader {name:20} rejected={bool(issues)}, expected={want_bad}")

    seen_multipliers = []

    def fake_encoding(_case):
        return base, None, 6

    def fake_reference(_case, mult):
        seen_multipliers.append(mult)
        return base, None

    verdict, _detail = check(object(), fake_encoding, fake_reference)
    fallback_ok = verdict == "ok" and seen_multipliers == [6]
    bad += not fallback_ok
    print(
        f"  {'ok  ' if fallback_ok else 'FAIL'} fallback round parity "
        f"reference multipliers={seen_multipliers}, expected=[6]"
    )

    old_search_cap = globals()["SEARCH_CAP"]
    globals()["SEARCH_CAP"] = 0
    try:
        verdict, detail = check(object(), fake_encoding, fake_reference)
    finally:
        globals()["SEARCH_CAP"] = old_search_cap
    cap_ok = verdict == "limit" and detail.endswith("-- inconclusive")
    bad += not cap_ok
    print(f"  {'ok  ' if cap_ok else 'FAIL'} search-cap verdict verdict={verdict}, expected=limit")

    def fake_broken_reference(_case, _mult):
        return None, "reference error: invariant failure"

    verdict, _detail = check(object(), fake_encoding, fake_broken_reference)
    oracle_error_ok = verdict == "unreadable"
    bad += not oracle_error_ok
    print(f"  {'ok  ' if oracle_error_ok else 'FAIL'} reference error verdict verdict={verdict}, expected=unreadable")

    warnings = incomplete_serialization("[WARN ] Omitted: Diff\n[WARN ] Truncated: App\nordinary warning")
    warning_ok = len(warnings) == 2
    bad += not warning_ok
    print(f"  {'ok  ' if warning_ok else 'FAIL'} serialization warnings detected={len(warnings)}, expected=2")

    total = len(cases) + len(matcher_cases) + len(reader_cases) + len(full_reader_cases) + 4
    print(f"\n{total - bad}/{total} self-tests pass")
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
        (
            "swap",
            2,
            X.Case("swap", [("f", v0, v1), ("f", v1, v0)], [(("f", v0, v1), ("f", v1, v0))], [], None, [], rounds=0),
        ),
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
        enc, err, mult = encoding_graph(case)
        if err:
            print(f"  FAIL {name:9} encoding: {err}")
            bad += 1
            continue
        if mult != 3:
            ref, err = reference_graph(case, mult)
            if err:
                print(f"  FAIL {name:9} reference@{mult}: {err}")
                bad += 1
                continue
        rmax = max((len(v) for v in ref.group.values()), default=0)
        emax = max((len(v) for v in enc.group.values()), default=0)
        ok = rmax == want == emax
        bad += not ok
        print(f"  {'ok  ' if ok else 'FAIL'} {name:9} largest group: reference {rmax}, encoding {emax}, want {want}")
    print(f"\n{len(cases) - bad}/{len(cases)} groups recovered by both readers")
    return 1 if bad else 0


def known_open_bugs():
    """Each reproduction of an open bug must STILL diverge.

    A bug that has been fixed makes its case agree, and that is reported rather than
    passed over: the entry is then stale and should come out, taking the reproduction
    into `curated()` where it will be held green from then on.
    """
    bad = []
    cases = X.known_divergences()
    for why, case in cases:
        verdict, detail = check(case)
        if verdict == "FAIL":
            print(f"  ok    {case.name}\n        {detail}\n        {why}")
        else:
            print(f"  STALE {case.name}: {verdict} -- it agrees now, so the bug is fixed?")
            bad.append(case.name)
    if not cases:
        print("  (none -- no open bug has a reproduction here, which is the good state)")
    print(f"\n{len(cases) - len(bad)}/{len(cases)} known divergences still diverge")
    return 1 if bad else 0


def main():
    args = sys.argv[1:]
    if args and args[0] == "selftest":
        return selftest()
    if args and args[0] == "known-groups":
        return known_groups()
    if args and args[0] == "known":
        return known_open_bugs()
    if args and args[0] == "fuzz":
        n = int(args[1]) if len(args) > 1 else 100
        rng = random.Random(int(args[2]) if len(args) > 2 else 0)
        cases = [X.rand_case(rng, i) for i in range(n)]
    elif args:
        cases = [c for c in X.curated() if c.name.startswith(args[0])]
    else:
        cases = X.curated()

    tally = {"ok": 0, "FAIL": 0, "skip": 0, "limit": 0, "unreadable": 0}
    totals = [0, 0, 0]
    for c in cases:
        verdict, detail = check(c)
        tally[verdict] += 1
        if verdict == "ok":
            totals = [a + b for a, b in zip(totals, detail, strict=True)]
        else:
            print(f"  {verdict:5} {c.name:44} {detail}", flush=True)
    # Out of what could be COMPARED, not out of what was generated. A run the reference
    # cannot finish is not a verdict either way, and counting it against the total made
    # one slow case look like a divergence. A rule whose atoms share nothing is a cross
    # product, so some of those are more work than the reference's budget -- the small
    # ones still finish, and those are the ones this number is about.
    #
    # The sizes are still part of the result: a checker that compared nothing would
    # otherwise pass, which is what the floor in `check-slotted.py` is for.
    comparable = tally["ok"] + tally["FAIL"]
    print(
        f"\n{tally['ok']}/{comparable} isomorphic"
        f"   ({tally['FAIL']} differ, {tally['skip']} skipped,"
        f" {tally['limit']} ran out of time, {tally['unreadable']} unreadable,"
        f" of {len(cases)} generated)"
    )
    print(f"matched {totals[0]} e-classes, {totals[1]} e-nodes, {totals[2]} symmetries")
    if UNSATURATED:
        print(
            f"{len(UNSATURATED)} compared at a database fixpoint, not a rule "
            f"fixpoint: {', '.join(UNSATURATED[:6])}"
            f"{' ...' if len(UNSATURATED) > 6 else ''}"
        )
    return 1 if tally["FAIL"] or tally["unreadable"] else 0


if __name__ == "__main__":
    sys.exit(main())
