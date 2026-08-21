#!/usr/bin/env python3
"""Compile the reference `sdql` rewrite rules into the slotted encoding.

The recipe is the one `tests/slotted-user-rules.egg` documents and
`slotted-experiments/xdiff/xdiff.py`'s `compile_rule` implements, generalised from
the harness's two-child `App2`/`App3` atoms to the per-language constructors of
`slotted-experiments/languages/sdql.egg`, which have one to six children and
payload columns.  The renaming solve is unchanged; the column walk and four cases
`sdql` needs and the harness's corpus does not are new:

  * a PAYLOAD LEAF in a child position -- `0`, `mult`.  Its row is never deleted
    or migrated, so it is a stable handle, but its class's canonical value need
    not be that row, so the atom joins `(RenamesToLeader (Num 0) _ C)` and uses
    `C` for the child rather than writing the leaf into the column;
  * a BUILT BINDER node.  Its slots are its edges' images MINUS what it binds,
    or the parent's edge to it names slots the child's class does not have;
  * an RHS slot the LHS never pinned -- `get-to-sum`'s `$k`, `$v`.  One
    `find-mapping-total` over a domain of that size mints them, avoiding every
    slot the pattern named;
  * an arity other than two, everywhere.

Atoms are compiled in pre-order from the LHS root, which is already the
connectivity the recipe requires.  `order_atoms`'s further preference -- a binder
is not the atom that fixes slots(pattern) -- is not followed: most `sdql` rules
are rooted at a binder, and taking the root first pins each bound slot off its
own edge instead of minting a name for it.  M7 in `tests/slotted-user-rules.egg`
is the same shape.

Per atom, in order, so each shares a variable with the prefix:

  * `(= V (Op m1 c1 ...))`, one egglog atom per e-node of the flattened LHS;
  * `dom`, the identity on the atom's node slots;
  * `mp`, the least renaming total on `dom` agreeing with everything already
    known -- the root if an earlier atom bound it, every child an earlier atom
    bound, every slot literal an earlier atom pinned.  The initial atom is the
    degenerate case, where `mp` is the identity on `dom`;
  * the avoid-set, accumulated so two atoms that both mint cannot collide;
  * each slot literal read out of its edge, binding on first use and
    constraining on every later one;
  * each child's renaming into pattern slots, narrowed by `ClassSlots` (M6b).

Terms in the tables below:

    "?x"            a pattern variable
    "$x"            a slot literal -- a binder column, or the reference's
                    `(var $x)` in an ordinary child column.  Both are the class
                    `(Var 0)` reached by an edge `0 -> $x`
    ("Op", ...)     a node; payload columns take Python literals, so `("Num", 0)`
                    and `("Symbol", "mult")` are the reference's `0` and `mult`

    python3 slotted-experiments/gen-sdql-rules.py
"""

import os
import pathlib
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
gen = __import__("gen-node-rules")
CHILD, BINDER = gen.CHILD, gen.BINDER

LANG = gen.read_language(pathlib.Path("slotted-experiments/languages/sdql.egg"))

OUT = pathlib.Path(os.environ.get("SDQL_OUT", "tests/slotted-sdql-rules.egg"))

# Re-introducible bugs, so the checks in `tests/slotted-sdql-rewrites.egg` can be
# shown to test what they were written for.  Same names and same meanings as
# `XDIFF_BUGS` in `slotted-experiments/xdiff/xdiff.py`.
#   SDQL_BUGS=slot-late   a slot literal checked after the renaming, not with it
#   SDQL_BUGS=root-only   an atom's renaming solved from its root alone
#   SDQL_BUGS=wide-kids   a variable used at the matched node's slots, not its class's
#   SDQL_BUGS=no-guard    the slot side conditions dropped
# Set SDQL_OUT to keep a mutant out of the tree.
BUGS = {b for b in os.environ.get("SDQL_BUGS", "").split(",") if b}


# ------------------------------------------------------------------- the rules
# `(name, lhs, rhs)`, optionally `conds` and `fresh`.  Each `conds` entry is
# `(slot, pvar)` reading "that slot is not among the variable's slots", the
# reference's `!subst[v].slots().contains(&Slot::named(s))`.  `fresh` names RHS
# slots the LHS never pinned, which have to be minted.
#
# Ported from `sdql_rules()` in `slotted-egraphs/benches/sdql.rs`, minus `beta`.
RULES = [
    ("mult-assoc1", ("Mult", ("Mult", "?a", "?b"), "?c"),
                    ("Mult", "?a", ("Mult", "?b", "?c"))),
    ("mult-assoc2", ("Mult", "?a", ("Mult", "?b", "?c")),
                    ("Mult", ("Mult", "?a", "?b"), "?c")),
    ("sub-identity", ("Sub", "?e", "?e"), ("Num", 0)),
    ("add-zero", ("Add", "?e", ("Num", 0)), "?e"),
    ("sub-zero", ("Sub", "?e", ("Num", 0)), "?e"),
    ("eq-comm", ("Equality", "?a", "?b"), ("Equality", "?b", "?a")),

    ("mult-app1", ("Mult", "?a", "?b"), ("Binop", ("Symbol", "mult"), "?a", "?b")),
    ("mult-app2", ("Binop", ("Symbol", "mult"), "?a", "?b"), ("Mult", "?a", "?b")),
    ("add-app1", ("Add", "?a", "?b"), ("Binop", ("Symbol", "add"), "?a", "?b")),
    ("add-app2", ("Binop", ("Symbol", "add"), "?a", "?b"), ("Add", "?a", "?b")),
    ("sub-app1", ("Sub", "?a", "?b"), ("Binop", ("Symbol", "sub"), "?a", "?b")),
    ("sub-app2", ("Binop", ("Symbol", "sub"), "?a", "?b"), ("Sub", "?a", "?b")),
    ("get-app1", ("Get", "?a", "?b"), ("Binop", ("Symbol", "getf"), "?a", "?b")),
    ("get-app2", ("Binop", ("Symbol", "getf"), "?a", "?b"), ("Get", "?a", "?b")),
    ("sing-app1", ("Sing", "?a", "?b"), ("Binop", ("Symbol", "singf"), "?a", "?b")),
    ("sing-app2", ("Binop", ("Symbol", "singf"), "?a", "?b"), ("Sing", "?a", "?b")),
    ("unique-app1", ("Unique", "?a"), ("App", ("Symbol", "uniquef"), "?a")),
    ("unique-app2", ("App", ("Symbol", "uniquef"), "?a"), ("Unique", "?a")),

    ("let-binop3", ("Let", "?e1", "$x", ("Binop", "?f", "?e2", "?e3")),
                   ("Binop", "?f", ("Let", "?e1", "$x", "?e2"),
                                   ("Let", "?e1", "$x", "?e3"))),
    ("let-binop4", ("Binop", "?f", ("Let", "?e1", "$x", "?e2"),
                                   ("Let", "?e1", "$x", "?e3")),
                   ("Let", "?e1", "$x", ("Binop", "?f", "?e2", "?e3"))),
    ("let-apply1", ("Let", "?e1", "$x", ("App", "?e2", "?e3")),
                   ("App", "?e2", ("Let", "?e1", "$x", "?e3"))),
    ("let-apply2", ("App", "?e2", ("Let", "?e1", "$x", "?e3")),
                   ("Let", "?e1", "$x", ("App", "?e2", "?e3"))),

    ("if-mult2", ("Mult", "?e1", ("IfThen", "?e2", "?e3")),
                 ("IfThen", "?e2", ("Mult", "?e1", "?e3"))),
    ("if-to-mult", ("IfThen", "?e1", "?e2"), ("Mult", "?e1", "?e2")),
    ("mult-to-if", ("Mult", ("Equality", "?e1_1", "?e1_2"), "?e2"),
                   ("IfThen", ("Equality", "?e1_1", "?e1_2"), "?e2")),

    ("sum-fact-1", ("Sum", "?R", "$x", "$y", ("Mult", "?e1", "?e2")),
                   ("Mult", "?e1", ("Sum", "?R", "$x", "$y", "?e2")),
     [("$x", "?e1"), ("$y", "?e1")]),
    ("sum-fact-2", ("Sum", "?R", "$x", "$y", ("Mult", "?e1", "?e2")),
                   ("Mult", ("Sum", "?R", "$x", "$y", "?e1"), "?e2"),
     [("$x", "?e2"), ("$y", "?e2")]),
    ("sum-fact-3", ("Sum", "?R", "$x", "$y", ("Sing", "?e1", "?e2")),
                   ("Sing", "?e1", ("Sum", "?R", "$x", "$y", "?e2")),
     [("$x", "?e1"), ("$y", "?e1")]),

    ("sing-mult-1", ("Sing", "?e1", ("Mult", "?e2", "?e3")),
                    ("Mult", ("Sing", "?e1", "?e2"), "?e3")),
    ("sing-mult-2", ("Sing", "?e1", ("Mult", "?e2", "?e3")),
                    ("Mult", "?e2", ("Sing", "?e1", "?e3"))),
    ("sing-mult-3", ("Mult", ("Sing", "?e1", "?e2"), "?e3"),
                    ("Sing", "?e1", ("Mult", "?e2", "?e3"))),
    ("sing-mult-4", ("Mult", "?e2", ("Sing", "?e1", "?e3")),
                    ("Sing", "?e1", ("Mult", "?e2", "?e3"))),

    ("sum-fact-inv-1", ("Mult", "?e1", ("Sum", "?R", "$k", "$v", "?e2")),
                       ("Sum", "?R", "$k", "$v", ("Mult", "?e1", "?e2"))),
    ("sum-fact-inv-3", ("Sing", "?e1", ("Sum", "?R", "$k", "$v", "?e2")),
                       ("Sum", "?R", "$k", "$v", ("Sing", "?e1", "?e2"))),

    ("sum-sum-vert-fuse-1",
     ("Sum", ("Sum", "?R", "$k2", "$v2", ("Sing", "$k2", "?body1")),
      "$k1", "$v1", "?body2"),
     ("Sum", "?R", "$k2", "$v2",
      ("Let", "$k2", "$k1", ("Let", "?body1", "$v1", "?body2")))),
    ("sum-sum-vert-fuse-2",
     ("Sum", ("Sum", "?R", "$k2", "$v2",
              ("Sing", ("Unique", "?key"), "?body1")), "$k1", "$v1", "?body2"),
     ("Sum", "?R", "$k2", "$v2",
      ("Let", ("Unique", "?key"), "$k1", ("Let", "?body1", "$v1", "?body2")))),

    ("sum-range-1",
     ("Sum", ("Range", "?st", "?en"), "$k", "$v",
      ("IfThen", ("Equality", "$v", "?key"), "?body")),
     ("Sum", ("Range", "?st", "?en"), "$k", "$v",
      ("IfThen", ("Equality", "$k", ("Sub", "?key", ("Sub", "?st", ("Num", 1)))),
       "?body"))),

    ("sum-merge",
     ("Sum", "?R", "$k1", "$v1",
      ("Sum", "?S", "$k2", "$v2",
       ("IfThen", ("Equality", "$v1", "$v2"), "?body"))),
     ("Merge", "?R", "?S", "$k1", "$k2", "$v1", ("Let", "$v1", "$v2", "?body"))),

    ("get-to-sum", ("Get", "?dict", "?key"),
     ("Sum", "?dict", "$k", "$v",
      ("IfThen", ("Equality", "$k", "?key"), "$v")),
     [], ["$k", "$v"]),
    ("sum-to-get",
     ("Sum", "?dict", "$k", "$v",
      ("IfThen", ("Equality", "$k", "?key"), "?body")),
     ("Let", "?key", "$k", ("Let", ("Get", "?dict", "$k"), "$v", "?body")),
     [("$k", "?key"), ("$v", "?key")]),

    ("get-range", ("Get", ("Range", "?st", "?en"), "?idx"),
                  ("Add", "?idx", ("Sub", "?st", ("Num", 1)))),
    ("sum-sing", ("Sum", "?e1", "$k", "$v", ("Sing", "$k", "$v")), "?e1"),
    ("unique-rm", ("Unique", "?e"), "?e"),
]


# ------------------------------------------------------------------ term shapes
def is_pvar(t):
    return isinstance(t, str) and t.startswith("?")


def is_slot(t):
    return isinstance(t, str) and t.startswith("$")


def is_node(t):
    return isinstance(t, tuple)


def child_terms(t):
    """The child arguments of a node, dropping payload columns."""
    args, out, i = list(t[1:]), [], 0
    for col in LANG[t[0]]:
        if col in (CHILD, BINDER):
            out.append(args[i])
        i += 1
    return out


def payloads_of(t):
    """A node's payload columns, already spelled as egglog literals."""
    args, out, i = list(t[1:]), [], 0
    for col in LANG[t[0]]:
        if col not in (CHILD, BINDER):
            out.append(f'"{args[i]}"' if col == "String" else str(args[i]))
        i += 1
    return out


def binder_positions(op):
    return [i for i, c in enumerate(k for k in LANG[op] if k in (CHILD, BINDER))
            if c is BINDER]


def is_leaf_node(t):
    """A node with no slotted children -- `Num` and `Symbol`, the payload leaves."""
    return is_node(t) and not child_terms(t)


def node_expr(op, edges, kids, pays=()):
    """`(Op p1 m1 c1 ...)`, interleaving payloads back into their columns."""
    cols, ci, pi = [], 0, 0
    for col in LANG[op]:
        if col in (CHILD, BINDER):
            cols += [edges[ci], kids[ci]]
            ci += 1
        else:
            cols.append(pays[pi])
            pi += 1
    return f"({op} {' '.join(cols)})"


def union_images(edges):
    if not edges:
        return "(map-empty)"
    out = f"(map-image {edges[-1]})"
    for e in reversed(edges[:-1]):
        out = f"(map-union (map-image {e}) {out})"
    return out


# --------------------------------------------------------------- flattening
def flatten(term):
    """The LHS as depth-1 atoms, pre-order, so every atom's root is a child of an
    earlier one -- which is the connectivity the recipe requires.

    Returns `(root, atoms)` with each atom `(root_pvar, Op, [(kind, value)])`,
    `kind` one of `var`, `slot`, `lit`.
    """
    atoms, ctr = [], [0]

    def go(t, name):
        descs, nested = [], []
        for c in child_terms(t):
            if is_slot(c):
                descs.append(("slot", c))
            elif is_pvar(c):
                descs.append(("var", c))
            elif is_leaf_node(c):
                descs.append(("lit", c))
            else:
                ctr[0] += 1
                nm = f"?_t{ctr[0]}"
                descs.append(("var", nm))
                nested.append((c, nm))
        atoms.append((name, t[0], descs))
        for c, nm in nested:
            go(c, nm)

    go(term, "?_p")
    return "?_p", atoms


# ---------------------------------------------------------------- the compiler
def compile_rule(name, lhs, rhs, conds=(), fresh=()):
    root, atoms = flatten(lhs)
    body, uid = [], [0]

    def new(p):
        uid[0] += 1
        return f"{p}{uid[0]}"

    mp_of, cls_of, slot_of, sym_of = {}, {}, {}, {}
    pat = None

    def narrow(m, cls):
        """Cut a renaming read off a node down to its class's slots -- M6b.

        A node may carry a slot its class does not depend on, and a pattern variable
        stands for the class, so the wider map would write a slot into a built node
        that the child does not have.
        """
        if "wide-kids" in BUGS:
            return m
        cs = new("cs")
        body.append(f"(= {cs} (ClassSlots {cls}))")
        return f"(compose {m} {cs})"

    def sym_for(pvar):
        if pvar not in sym_of:
            sv = new("sym")
            body.append(f"(RenamesToLeader {cls_of[pvar]} {sv} {cls_of[pvar]})")
            sym_of[pvar] = sv
        return sym_of[pvar]

    for idx, (aroot, op, descs) in enumerate(atoms):
        edges = [new("p") for _ in descs]
        rv = cls_of.setdefault(aroot, new("V"))
        kids, lits = [], []
        for (kind, val), e in zip(descs, edges):
            if kind == "slot":
                kids.append("(Var 0)")
            elif kind == "lit":
                cv = new("L")
                kids.append(cv)
                lits.append((val, cv))
            else:
                kids.append(cls_of.setdefault(val, new("C")))
        # No `sdql` constructor mixes a payload with a child, and an atom always has
        # children, so an atom never carries a payload column.
        body.append(f"(= {rv} {node_expr(op, edges, kids)})")
        # A payload leaf is never deleted or migrated, so its row is a stable
        # handle on its class -- but the class's canonical value need not be that
        # row, so reach the child through `RenamesToLeader` rather than writing
        # the leaf into the child column.
        for lit, cv in lits:
            body.append(f"(RenamesToLeader {node_expr(lit[0], [], [], payloads_of(lit))} "
                        f"{new('ml')} {cv})")

        dom = new("dom")
        body.append(f"(= {dom} {union_images(edges)})")

        firsts, seconds = [], []
        if aroot in mp_of:
            mv = mp_of[aroot]
            firsts.append(f"(compose {mv} {sym_for(aroot)})")
            seconds.append(f"(map-domain {mv})")
        bound_before = set(mp_of)
        for (kind, val), e in zip(descs, edges):
            if kind == "var" and val in bound_before and "root-only" not in BUGS:
                firsts.append(f"(compose {mp_of[val]} {sym_for(val)})")
                seconds.append(e)
        for (kind, val), e in zip(descs, edges):
            # A slot literal an earlier atom pinned constrains this atom's `mp`.
            # Checking it afterwards is too late: `mp` would already have minted a
            # different name for the same binder, and nothing revises a mint.
            if kind == "slot" and val in slot_of and "slot-late" not in BUGS:
                firsts.append(f"(map-insert (map-empty) 0 {slot_of[val]})")
                seconds.append(e)

        mp = new("mp")
        if idx == 0:
            body.append(f"(= {mp} {dom})")
        elif firsts:
            body.append(f"(= {mp} (find-mapping-total {pat} {dom} "
                        f"{' '.join(firsts + seconds)}))")
        else:
            body.append(f"(= {mp} (find-mapping-total {pat} {dom} "
                        f"(map-empty) (map-empty)))")

        idm = new("idm")
        body.append(f"(= {idm} (map-image {mp}))")
        if idx == 0:
            pat = idm
        else:
            av = new("av")
            body.append(f"(= {av} (map-union {pat} {idm}))")
            pat = av

        for (kind, val), e in zip(descs, edges):
            if kind == "slot":
                sv = slot_of.setdefault(val, "s" + val[1:])
                body.append(f"(= {sv} (map-get (compose {mp} {e}) 0))")

        for (kind, val), e in zip(descs, edges):
            if kind != "var":
                continue
            if val in mp_of:
                if val not in bound_before or "root-only" in BUGS:
                    # a repeat within THIS atom: the Def. 6 check, against the
                    # class's one symmetry
                    body.append(
                        f"(= (compose {mp} {e}) (compose {mp_of[val]} {sym_for(val)}))")
            else:
                m = new("m")
                body.append(f"(= {m} (compose {mp} {e}))")
                mp_of[val] = narrow(m, cls_of[val])
        if aroot not in mp_of:
            mp_of[aroot] = narrow(mp, rv)

    # RHS slots the LHS never pinned: mint them, avoiding every slot named so far.
    if fresh:
        fs = new("fs")
        dm = " ".join(f"{i} {i}" for i in range(len(fresh)))
        body.append(f"(= {fs} (find-mapping-total {pat} (map-of {dm}) "
                    f"(map-empty) (map-empty)))")
        for i, s in enumerate(fresh):
            sv = slot_of.setdefault(s, "s" + s[1:])
            body.append(f"(= {sv} (map-get {fs} {i}))")

    # A variable's slots in pattern space are the image of its renaming, so the
    # reference's `!subst[v].slots().contains($s)` is a `map-not-contains`.
    for slot, pvar in conds:
        if "no-guard" in BUGS:
            continue
        body.append(f"(map-not-contains (map-image {mp_of[pvar]}) {slot_of[slot]})")

    lets = []

    def build(t):
        """`(edge, class)` for an RHS term, one `let` per built node.

        An action is already in pattern slot space, so the edge from a built node
        to a built child is the identity on the child's slots -- no renaming
        between them.  A built binder node's slots are its edges' images MINUS the
        slots it binds, which is what keeps the parent's edge inside Def. 4.
        """
        if is_pvar(t):
            return mp_of[t], cls_of[t]
        if is_slot(t):
            return f"(map-insert (map-empty) 0 {slot_of[t]})", "(Var 0)"
        kids = [build(c) for c in child_terms(t)]
        node = node_expr(t[0], [e for e, _ in kids], [c for _, c in kids],
                         payloads_of(t))
        if not kids:
            return "(map-empty)", node          # a payload leaf has no slots
        nv = new("_rhs")
        lets.append(f"(let {nv} {node})")
        slots = union_images([e for e, _ in kids])
        for i in binder_positions(t[0]):
            slots = f"(map-remove {slots} {slot_of[child_terms(t)[i]]})"
        return slots, nv

    mr = mp_of[root]
    if is_pvar(rhs):
        # Equate two variables.  Both carry a renaming into pattern slots and
        # neither need be the identity, which is the one action egglog's `union`
        # cannot express -- so solve: from mr*Root = ma*A follows
        # Root = (mr^-1 . ma) * A, and let the machinery re-orient it.
        act = [f"(Equated {cls_of[root]} "
               f"(compose (inverse {mr}) {mp_of[rhs]}) {cls_of[rhs]})"]
    else:
        _, built = build(rhs)
        act = lets + [f"(Equated {built} {mr} {cls_of[root]})"]

    return ("(rule (" + "\n       ".join(body) + ")\n      ("
            + "\n       ".join(act) + f")\n      :ruleset sdql :name \"{name}\")")


HEADER = '''\
;;; GENERATED by slotted-experiments/gen-sdql-rules.py -- do not edit.
;;;
;;; The reference `sdql` rewrite rules -- `sdql_rules()` in
;;; `slotted-egraphs/benches/sdql.rs` -- compiled into the slotted encoding by the
;;; recipe in `tests/slotted-user-rules.egg`.
;;;
;;; `beta` is NOT here: it substitutes, which needs `slotted-subst` and frame
;;; plumbing rather than this compiler.  The other 43 are.
;;;
;;; These are USER rules, so they go in their own ruleset and the machinery is
;;; saturated between finite steps of them:
;;;
;;;     (run-schedule (saturate (run slotted))
;;;                   (repeat N (seq (run sdql 1) (saturate (run slotted)))))
;;;
;;; `tests/slotted-sdql-rewrites.egg` is what checks them.

(include "tests/slotted-lang-sdql.egg")

(ruleset sdql)
'''


def main():
    out = [HEADER]
    for spec in RULES:
        name, lhs, rhs = spec[0], spec[1], spec[2]
        conds = spec[3] if len(spec) > 3 else ()
        fresh = spec[4] if len(spec) > 4 else ()
        out.append(f"\n;; {name}\n" + compile_rule(name, lhs, rhs, conds, fresh))
    OUT.write_text("\n".join(out) + "\n")
    print(f"wrote {OUT} ({len(RULES)} rules)")


if __name__ == "__main__":
    main()
