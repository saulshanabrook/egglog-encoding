#!/usr/bin/env python3
"""The slotted encoding, in one place.

Several programs encode slotted rules and terms, and the recipe they encode is one
recipe: `slotted/tests/user-rules.egg` states it, section by section, and
`slotted-user-rules.md` argues it. This module is that recipe as code, so there is
one place for it to be right and one place to fix. The front-ends:

    slotted-egglog.py    a test written in the slotted language, compiled to run
    gen-node-rules.py     writes the machinery files
    gen-sdql-rules.py     the reference `sdql` rewrite rules
    xdiff/xdiff.py        the differential harness, toy language
    xdiff/xarray.py       the differential harness, the paper's array language
    xdiff/xsdql.py        the differential harness, `sdql`

None of them holds a rule. The rules live in `slotted/languages/sdql.egg` and
`slotted/languages/array.egg`, written in the slotted language, and each front-end reads
one -- so a rule has one spelling and the several things done with it cannot disagree
about what it says.

Four layers, in the order they build on each other.

LANGUAGE SPECS. A constructor's signature is a list of columns, each either

  * `CHILD`  -- a slotted child, which occupies two egglog columns, `Renaming U`,
               because reaching it requires a renaming;
  * `BINDER` -- a slotted child whose slot the node binds; or
  * a sort   -- `"i64"`, `"String"`, ... a payload, one column, no renaming, since
               a payload carries no slots.

So a node's slots come from its slotted columns alone, and payloads ride along
untouched. `(Num i64)` is then just the zero-child case rather than a special kind
of leaf, and mixed shapes like `(Index i64 CHILD)` work with no indirection.
`read_language` reads this off annotated egglog declarations.

MACHINERY. The per-constructor maintenance rules -- `class_slots`, `self_loop`,
`alpha_finder`, `symmetry_finder`, `migration`, `child_update`, `binder` -- which
have to name every column and so cannot be written once for all shapes in egglog.

TERMS. `TermLang` maps a high-level term onto the encoding: `node_expr` for the
low-level node form, and `slots` / `edge` / `enc` / `sexpr` / `shift` over whole
terms. An operator is an `Op`, which is where a language says that its `lambda`
binds its first child or that its head is a payload string rather than a
constructor.

RULES. `compile_rule` is the recipe: flatten the left-hand side to depth-1 atoms,
order them so each shares a variable with the ones before, one
`find-mapping-total` per atom against an accumulating avoid-set, the Def. 6 check
for a repeat inside one atom, `(compose m (ClassSlots X))` on every variable, slot
literals folded into the renaming rather than checked after it, and an `Equated`
conclusion.

WHERE THINGS ARE, since the layers do not sit in four contiguous blocks:

    language specs   `Op`, `CHILD`/`BINDER`, `signature`, `read_language`,
                     `read_language_form`, `language`, `read_correspondence`
    machinery        `emit` drives it; one function per maintenance rule --
                     `class_slots`, `self_loop`, `alpha_finder`, `symmetry_finder`,
                     `migration`, `child_update`, `binder` -- plus `declare` and
                     `pattern` for the shapes they all need
    terms            `TermLang`: `node_expr`, `slots`, `edge`, `enc`, `sexpr`,
                     `shift`; `pat_sexpr` and `rhs_of` for the pattern side
    rules            `flatten` (nested pattern -> atoms), `connected_order` (the
                     order they are emitted in), `compile_rule` (the emission
                     itself), `in_slotted_ruleset`

READING `compile_rule` AGAINST THE TUTORIAL. Its per-atom steps are the tutorial's
sections, and its docstring names which: the degenerate leading atom is M1, the
repeat-inside-one-atom check is M2, minting is M3, the chain is M4, the accumulating
avoid-set is M5, `narrow` is M8, and the conclusion is M10. A worked match with real
values for every one of those variables is at the top of
`slotted/tests/user-rules.egg`, asserted by
`slotted/encoding/user-rules-trace.egg`.
"""

import re

CHILD = object()  # a slotted child: `Renaming U`
BINDER = object()  # a slotted child that also binds its slot

SLOTTED = (CHILD, BINDER)


###############################################################################
# language specs
###############################################################################


def read_language(path):
    """Parse annotated constructor declarations.

        (constructor Lam (U U) U :binder 0)
        (constructor Sum (U U U U) U :binder 1 2)
        (constructor Num (i64) U)

    A `U` column is a slotted child and expands to `Renaming U`; anything else is a
    payload and passes through. `:binder` names the child positions -- counted over
    children, not over columns -- whose slot the node binds. This is the syntax the
    encoder recognises today; the intent is for egglog-experimental to accept it and
    strip it on the way down to core egglog, where nothing about a binder is
    primitive.
    """
    language = {}
    for raw in path.read_text().splitlines():
        line = raw.split(";")[0].strip()
        if not line.startswith("(constructor "):
            continue
        head, _, rest = line[len("(constructor ") :].partition("(")
        cols_text, _, tail = rest.partition(")")
        # the closing paren sticks to the last index, so scan for integers
        binders = [int(x) for x in re.findall(r"\d+", tail.split(":binder")[1])] if ":binder" in tail else []
        language[head.strip()] = signature(cols_text.split(), binders)
    return language


def signature(cols, binders):
    """Columns and the binding child positions as the encoder's signature."""
    sig, seen_kids = [], 0
    for col in cols:
        if col == "U":
            sig.append(BINDER if seen_kids in binders else CHILD)
            seen_kids += 1
        else:
            sig.append(col)
    return sig


def read_language_form(form):
    """One parsed `(constructor Name (U U) U :binder 0)` as `{name: signature}`.

    The list form, for a test that declares its language inline rather than pointing
    at a file. Same syntax, same meaning.
    """
    assert form[0] == "constructor" and isinstance(form[2], list), form
    name, cols = form[1], form[2]
    tail = form[4:]
    binders = [int(x) for x in tail[1:]] if tail and tail[0] == ":binder" else []
    return {name: signature(cols, binders)}


def read_correspondence(path):
    """Parse a `.ref` file: how a language's operators are spelled by the reference.

        app     App     app
        sym     Sym     =payload sym:

    Returns `{operator: (constructor, ref, prefix)}`, where `ref` is `None` for
    `=payload` -- an operator the reference writes as its payload rather than under a
    tag -- and `prefix` is what that payload needs in front of it, or `""`.

    This is deliberately not in the `.egg` language file: what the reference calls a
    constructor is a fact about the harness, not about the encoding.
    """
    out = {}
    for raw in path.read_text().splitlines():
        line = raw.split(";")[0].strip()
        if not line:
            continue
        op, ctor, ref, *rest = line.split()
        if ref == "=payload":
            assert len(rest) <= 1, f"{op}: one prefix at most, got {rest}"
            out[op] = (ctor, None, rest[0] if rest else "")
        else:
            assert not rest, f"{op}: a tag takes no further field, got {rest}"
            out[op] = (ctor, ref, "")
    return out


def language(spec, ref):
    """A `TermLang` from a language file and its correspondence file.

    The two must name the same constructors, so an operator added to one and not the
    other is an error here rather than a harness that quietly stops covering it.
    """
    sigs = read_language(spec)
    corr = read_correspondence(ref)
    named = {ctor for ctor, _, _ in corr.values()}
    assert named == set(sigs), (
        f"{spec.name} declares {sorted(set(sigs) - named)} that {ref.name} does not name, "
        f"and {ref.name} names {sorted(named - set(sigs))} that it does not declare"
    )
    ops = {op: Op(op, ctor, sigs[ctor], ref=tag, ref_prefix=prefix) for op, (ctor, tag, prefix) in corr.items()}
    # Also reachable by CONSTRUCTOR name. A slotted `.egg` writes the constructor it
    # declared, `(App ?a ?b)`, while a corpus written in Python names the operator,
    # `("app", a, b)`; both denote the same node, and the `.ref` already gives one
    # operator two names where a language wants them.
    for op in list(ops.values()):
        ops.setdefault(op.ctor, op)
    return TermLang(ops)


def cols_of(sig):
    """Column names for a signature: payload vars, and (edge, child) per child."""
    payloads, edges, kids, order = [], [], [], []
    for _i, col in enumerate(sig):
        if col in SLOTTED:
            e, k = f"m{len(kids) + 1}", f"c{len(kids) + 1}"
            edges.append(e)
            kids.append(k)
            order.append((e, k))
        else:
            p = f"p{len(payloads) + 1}"
            payloads.append(p)
            order.append((p,))
    return payloads, edges, kids, order


def pattern(name, sig, edges=None, kids=None, payloads=None):
    """`(Name p1 m1 c1 ...)`, with any column list overridden."""
    dp, de, dk, order = cols_of(sig)
    payloads, edges, kids = payloads or dp, edges or de, kids or dk
    out, pi, ci = [], 0, 0
    for slot in order:
        if len(slot) == 2:
            out += [edges[ci], kids[ci]]
            ci += 1
        else:
            out.append(payloads[pi])
            pi += 1
    return f"({name} {' '.join(out)})"


def declare(name, sig):
    """The `(constructor ...)` line for one signature: a slotted column becomes the
    two egglog columns `Renaming U`, a payload column stays as it is."""
    cols = " ".join("Renaming U" if c in SLOTTED else c for c in sig)
    return f"(constructor {name} ({cols}) U)\n"


def shape_of(col):
    """A column's kind as it is written in a generated file's comments."""
    return {CHILD: "child", BINDER: "binder"}.get(col, str(col))


# The two constructors `slotted/encoding/egraph-encoding-11.egg` declares and writes the
# rules for itself, because both are constructor-independent: `Var` is normalised into
# a renaming so one value stands for every variable, and `Null` is the nullary object.
# A language file may declare either for the record -- so that it names every
# constructor a program in it can contain -- and its rules are already there.
CORE = {"Var": ["i64"], "Null": []}

# The hand-written half, and the generated file that includes it. A language file
# includes the generated one, so it gets both.
MACHINERY = "slotted/encoding/egraph-encoding-11.egg"


###############################################################################
# machinery: the per-constructor maintenance rules
###############################################################################


def fold(op, xs, empty):
    """`xs` combined right-to-left with a binary egglog operator; `empty` for none."""
    if not xs:
        return empty
    out = xs[-1]
    for x in reversed(xs[:-1]):
        out = f"({op} {x} {out})"
    return out


def lex_greater(a, b, i=0):
    """`b` lexicographically greater than `a`, as tuples of renamings.

    The alpha-finder fires in one direction only, so that of two symmetric matches
    exactly one node is eliminated.
    """
    gt = f"(and (bool= (ordering-max {a[i]} {b[i]}) {b[i]}) (bool-!= {a[i]} {b[i]}))"
    if i == len(a) - 1:
        return gt
    return f"(or {gt}\n              (and (bool= {a[i]} {b[i]})\n                   {lex_greater(a, b, i + 1)}))"


def class_slots(name, sig):
    """A node's own slots, offered as an upper bound on its class's.

    `ClassSlots` intersects on merge, so a class ends up with the slots *every* one of
    its nodes has -- anything only some of them carry is redundant. That is the
    reference's `c.slots`, which starts as the creating node's slots and afterwards
    only shrinks. Deriving it from a node is safe here precisely because the merge can
    only narrow, unlike the self-loop rule, which asserts the node's slots outright.
    """
    _, edges, _, _ = cols_of(sig)
    slots = fold("map-union", [f"(map-image {m})" for m in edges], "(map-empty)")
    return f"""\
(rule ((= e1 {pattern(name, sig)}))
      ((set (ClassSlots e1) {slots})))
"""


def self_loop(name, sig):
    """A node's class gets the identity on the node's own slots."""
    _, edges, _, _ = cols_of(sig)
    slots = fold("map-union", [f"(map-image {m})" for m in edges], "(map-empty)")
    return f"""\
(rule ((= e1 {pattern(name, sig)})
       (= m {slots}))
      ((RenamesToLeader e1 m e1)))
"""


def alpha_finder(name, sig):
    """Two nodes equal up to renaming: keep one, record how the other renames to it.

    For `e1 = f(m1*c1, m1'*c2)` and `e2 = f(m2*c1, m2'*c2)`, the solve
    `(find-mapping m1 m1' m2 m2')` is the least `m` with `m*m2 = m1` and `m*m2' = m1'`, so

        m*e2 = f(m*m2*c1, m*m2'*c2) = f(m1*c1, m1'*c2) = e1

    which is the `RenamesToLeader` this records before deleting `e2`'s row.

    Payload columns are named by the same variable on both sides, so a difference
    there simply does not match -- no separate check needed.
    """
    payloads, edges, kids, _ = cols_of(sig)
    a_o = [f"{e}_o" for e in edges]
    a, b = list(edges), [f"b{i + 1}" for i in range(len(edges))]
    syms = [f"sym{i + 1}" for i in range(len(kids))]
    loops = "\n       ".join(f"(RenamesToLeader {kids[i]} {syms[i]} {kids[i]})" for i in range(len(kids)))
    composed = "\n       ".join(f"(= {a[i]} (compose {a_o[i]} {syms[i]}))" for i in range(len(edges)))
    return f"""\
(rule ((= e1 {pattern(name, sig, edges=a_o)})
       (= e2 {pattern(name, sig, edges=b)})
       (= e1 (ordering-max e1 e2))
       {loops}
       {composed}
       (= m (find-mapping {" ".join(a)} {" ".join(b)}))
       (guard
         (or (bool-!= e1 e2)
             (and (bool= e1 e2)
                  {lex_greater(a_o, b)}))))
      ((Equated e1 m e2)
       (delete {pattern(name, sig, edges=a_o)})))
"""


def symmetry_finder(name, sig):
    """The same solve, kept non-destructively as a symmetry of the class.

    Restricted to the class's slots. `sym_out` is solved from a *node's* edges, so its
    domain is the node's slots, and a node may carry slots its class does not depend on --
    so unrestricted it asserts a symmetry the class does not have. The shrinking rule then
    deletes that, this rule derives it again, and neither ever wins: four generated cases
    never reached a fixpoint of the rules for exactly this reason. `ClassSlots` only
    narrows, so restricting on both sides leaves nothing to shrink.

    This is the same mistake as the self-loop rule's, and the same one open question 2
    warns about -- do not derive a class-level fact from a node.
    """
    _, edges, kids, _ = cols_of(sig)
    a_o = [f"{e}_o" for e in edges]
    a = list(edges)
    syms = [f"sym{i + 1}" for i in range(len(kids))]
    loops = "\n       ".join(f"(RenamesToLeader {kids[i]} {syms[i]} {kids[i]})" for i in range(len(kids)))
    composed = "\n       ".join(f"(= {a[i]} (compose {a_o[i]} {syms[i]}))" for i in range(len(edges)))
    return f"""\
(rule ((= e {pattern(name, sig, edges=a_o)})
       {loops}
       {composed}
       (= sym_out (find-mapping {" ".join(a_o)} {" ".join(a)}))
       (= cs (ClassSlots e)))
      ((RenamesToLeader e (compose cs (compose sym_out cs)) e)))
"""


def migration(name, sig):
    """Rewrite a follower's node into its leader's frame.

    For `e2 = f(m1*c1, m2*c2)` and `e2 = m*e1`, rewriting into e1's frame gives

        e1 = m^-1*e2 = f(m^-1*m1*c1, m^-1*m2*c2)

    so each edge composes with `m^-1` and the original row goes.

    A node can use a slot its leader's frame cannot name -- a slot the class does not
    depend on. A name is invented for it, as the reference's `compose_fresh` does, which is
    what lets the node move at all: leaving it behind instead would mean follower classes
    are never emptied.

    Only ever toward the leader. `RenamesToLeader` holds both directions for a pair, so
    `(!= e1 e2)` alone lets a node be moved either way: it is deleted from one value,
    rebuilt on the other, and moved straight back, which is a fixpoint of the database
    but not of the rules. `ordering-min` is the orientation the single-parent rule
    already establishes, so following it here makes migration idempotent.
    """
    _, edges, _, _ = cols_of(sig)
    ns = [f"n{i + 1}" for i in range(len(edges))]
    node_slots = fold("map-union", [f"(map-image {m})" for m in edges], "(map-empty)")
    pulled = "\n       ".join(
        [
            f"(= nodeslots {node_slots})",
            "; R takes the node's slots to the leader's, agreeing with m inverse where",
            "; that is defined and minting a name where it is not",
            "(= R (find-mapping-total (map-domain m) nodeslots (map-domain m) m))",
        ]
        + [f"(= {ns[i]} (compose R {edges[i]}))" for i in range(len(edges))]
    )
    return f"""\
(rule ((RenamesToLeader e2 m e1)
       (= e2 {pattern(name, sig)})
       (!= e1 e2)
       (= e2 (ordering-max e1 e2))       ; toward the leader only
       {pulled})
      ((union e1 {pattern(name, sig, edges=ns)})
       (delete {pattern(name, sig)})))
"""


def child_update(name, sig, pos):
    """Replace child `pos` with its more canonical `m*c'`.

    One rule per child position, canonicalising that child to the class's representative:
    the stored edge composes with the child's renaming, `m1` becoming `m1 . m`.

    Only ever toward the leader, for the same reason migration needs it: a slotted class
    spans several values and `RenamesToLeader` holds both directions between them, so
    without an orientation the child pointer follows an edge one way, is rewritten back
    the next round, and the node row is deleted and rebuilt forever. `ordering-min` is
    the direction the single-parent rule already establishes. When the class is unchanged
    the atom holds trivially, so the self-symmetry case below is unaffected.
    """
    _, edges, kids, _ = cols_of(sig)
    new_e, new_k = list(edges), list(kids)
    new_e[pos] = f"(compose {edges[pos]} m)"
    new_k[pos] = "c'"
    return f"""\
(rule ((RenamesToLeader {kids[pos]} m c')
       (= node {pattern(name, sig)})
       (= {kids[pos]} (ordering-max {kids[pos]} c'))    ; toward the leader only
       ; if the class is unchanged then m must be idempotent: no self-symmetries
       (guard (or (bool-!= {kids[pos]} c') (bool= (compose m m) m)))
       ; and the new node must differ from the old one
       (guard (or (bool-!= {kids[pos]} c')
                  (bool-!= (compose {edges[pos]} m) {edges[pos]}))))
      ((union node {pattern(name, sig, edges=new_e, kids=new_k)})
       (delete {pattern(name, sig)})))
"""


def binder(name, sig, positions, head=None):
    """Take a bound slot out of the node's class's slot set, where it is bound.

    A bound slot rides in its child's edge, so it is a slot of the *node* but must
    not be one of the class: removing it from the edge to the leader is what makes
    two spellings of the same binder alpha-equivalent. `head` pins the operator
    string for the generic encoding, where the operator is a payload rather than
    the constructor.

    A binder covers ONE column -- the one right after the binder slots, which is
    what `Bind<T>` wrapping a single child means -- so the slot is removed only
    when no other child column names it. `Let(Bind<body>, value)` binds the slot
    in the body and leaves a `value` occurrence free, and stripping it from the
    whole node instead merges terms the reference keeps apart. Each bound slot
    gets its own rule, since one may be free in an uncovered column while another
    is not: `sdql`'s `Sum` binds two over one body, beside an uncovered range.
    """
    _, edges, kids, _ = cols_of(sig)
    e, k = list(edges), list(kids)
    for n, pos in enumerate(positions):
        e[pos], k[pos] = f"mvar{n}", "(Var 0)"
    payloads = [f'"{head}"'] if head is not None else None
    node = pattern(name, sig, edges=e, kids=k, payloads=payloads)

    covered = max(positions) + 1
    assert covered < len(kids), f"{name}: a binder must cover a following column"
    uncovered = [i for i in range(len(kids)) if i not in positions and i != covered]

    rules = []
    for n, pos in enumerate(positions):
        free_elsewhere = "".join(f"\n       (map-not-contains (map-image {edges[u]}) v{n})" for u in uncovered)
        rules.append(f"""\
(rule ((RenamesToLeader {node} ml l)
       (= v{n} (map-get mvar{n} 0)){free_elsewhere})
      ((Equated {node} (inverse (map-remove (inverse ml) v{n})) l)))
""")

        # A collision with an uncovered column blocks the strip above, which would
        # leave the bound slot in the class's slot set and stop it being renameable.
        # Move it to a slot the node does not use; the strip then applies. One rule
        # per uncovered column, so the guard stays a single fact.
        # built from the PATTERN's edge names: the binder columns are bound as
        # `mvarN` there, not by their positional name.
        union_of = f"(map-image {e[0]})"
        for x in e[1:]:
            union_of = f"(map-union {union_of} (map-image {x}))"
        for u in uncovered:
            fresh_e = list(e)
            fresh_e[pos] = f"(map-of 0 w{n})"
            fresh_e[covered] = f"(compose (map-insert (map-image {edges[covered]}) v{n} w{n}) {edges[covered]})"
            renamed = pattern(name, sig, edges=fresh_e, kids=k, payloads=payloads)
            rules.append(f"""\
(rule ((= node {node})
       (= v{n} (map-get mvar{n} 0))
       (map-contains (map-image {edges[u]}) v{n})   ; bound slot is free here too
       (= used {union_of})
       ; the smallest slot the node does not use
       (= fresh{n} (find-mapping-total used (map-of 0 0) (map-empty) (map-empty)))
       (= w{n} (map-get fresh{n} 0)))
      ((union node {renamed})
       (delete {node})))
""")
    return "\n".join(rules)


def banner(text):
    """A section header for a generated file."""
    bar = ";" * 78
    return [bar, f";;; {text}", bar, ""]


def emit(language, binders=(), provided=None, omit=()):
    """All the rules for one language: `{constructor: signature}`.

    `binders` pins binders by operator string, for the generic encoding where the
    operator is a payload rather than the constructor. A `BINDER` column declares
    one structurally and needs no entry.

    `provided` names constructors the machinery a language file includes already
    declares -- `CORE`, and whatever family that file holds. Re-declaring one is a
    duplicate binding, so its signature must match and then its rules are already there
    too.

    `omit` names constructors written out by hand in the file this output includes,
    so emitting them would be a duplicate binding too. Binders over them are left
    out with them.
    """
    out = []
    for name, sig in language.items():
        if name in omit:
            out += banner(
                f"{name} :: {' '.join(shape_of(c) for c in sig)} -- hand-written in egraph-encoding-11.egg"
            )
            continue
        if provided and name in provided:
            if provided[name] != sig:
                raise SystemExit(f"{name} clashes with the machinery at a different signature")
            out += banner(
                f"{name} :: {' '.join(shape_of(c) for c in sig)} -- declared by the machinery this file includes"
            )
            continue
        _, edges, kids, _ = cols_of(sig)
        out += banner(f"{name} :: {' '.join(shape_of(c) for c in sig)}")
        out += [
            declare(name, sig),
            ";; an upper bound on the class's slots; the merge narrows it",
            class_slots(name, sig),
            ";; every class holding a node has a self-loop, so a query can reach it",
            self_loop(name, sig),
        ]
        if not kids:
            continue  # nothing below touches a child
        out += [
            ";; alpha-finder: two nodes equal up to renaming, one eliminated",
            alpha_finder(name, sig),
            ";; the same solve kept as a symmetry, non-destructively",
            symmetry_finder(name, sig),
            ";; migration: move a follower's node into the leader's frame",
            migration(name, sig),
        ]
        for pos in range(len(kids)):
            out += [f";; child-update, child {pos + 1}", child_update(name, sig, pos)]

    binder_rules = []
    for name, sig in language.items():
        kid_cols = [c for c in sig if c in SLOTTED]
        bound = [i for i, c in enumerate(kid_cols) if c is BINDER]
        if bound and name not in omit:
            which = ", ".join(str(i + 1) for i in bound)
            binder_rules.append((f";; `{name}` binds child {which}, one rule per bound slot", binder(name, sig, bound)))
    for head, name in binders:
        if name in omit:
            continue
        binder_rules.append((f";; `{head}` binds its first child's slot", binder(name, language[name], [0], head=head)))
    if binder_rules:
        out += banner("binders")
        for comment, rule in binder_rules:
            out += [comment, rule]
    return out


#: The right-hand side head that is a call rather than a node.
SUBST = "subst"

#: What a `subst` right-hand side needs alongside the rules that use it, emitted once.
#:
#: The primitive answers with an INVOCATION -- `slotted-subst` the class and
#: `slotted-subst-frame` the renaming into the body's frame -- and the result's own
#: slots are not known until the machinery has seen its node. So the narrowing that M8
#: does inside one rule happens here instead, one phase later, and `Equated` lets the
#: machinery pick the orientation (M10).
SUBST_MACHINERY = """\
;; A substitution in flight: the class it answered with, the renaming into the body's
;; frame, and `q` carrying that frame into the root's own slots.
(relation SubstPending (U Renaming Renaming U))

(rule ((SubstPending root q mr r)
       (= cs (ClassSlots r)))
      ((Equated root (compose q (compose mr cs)) r))
      :ruleset slotted)
"""


# The constructor-independent half of the node machinery. Hand-written in
# `slotted/encoding/egraph-encoding-11.egg` along with a constructor or two, and kept
# here so a generator can state what that text has to say.
SHARED = """\
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; a class's slot set, held once
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The slots a class actually depends on, as an identity renaming. Held directly
;; rather than read off a self-loop: a self-loop is derived from a node, so it can
;; name more slots than the class has, and a rule that picks one to mean "the class's
;; slots" gets whichever the join happened to bind. This narrows on merge and so can
;; only ever shrink, which is what the reference's `c.slots` does.
(function ClassSlots (U) Renaming :merge (map-intersect old new))

;; the leaves, whose slots are known outright
(set (ClassSlots (Var 0)) (map-of 0 0))
(set (ClassSlots (Null)) (map-empty))

;; Carry a slot set along a `RenamesToLeader` edge, in both directions: `a = m*b`, so
;; `m` takes b's slots to a's. Transporting a set S through a renaming is the image of
;; the renaming restricted to S.
(rule ((RenamesToLeader a m b) (= S (ClassSlots a)))
      ((set (ClassSlots b) (map-image (compose (inverse m) S)))))
(rule ((RenamesToLeader a m b) (= S (ClassSlots b)))
      ((set (ClassSlots a) (map-image (compose m S)))))
"""

MACHINERY_HEADER = """\
;;; GENERATED by slotted/gen-node-rules.py -- do not edit.
;;;
;;; One block per constructor. A `child` column occupies `Renaming U` and
;;; contributes its slots; a payload column is one column and contributes none, so a
;;; zero-child constructor is just a payload leaf. A `binder` is a child whose slot
;;; the node binds.
;;;
;;; A binder COVERS one column -- the one right after the binder slots, which is what
;;; `Bind<T>` wrapping a single child means. Its slot is taken out of the class's slot
;;; set only where it is bound, so an occurrence in an uncovered column stays free:
;;; `let` binds in its body and leaves its value's occurrence alone. When the two
;;; collide the bound slot is first renamed to one the node does not use, which keeps
;;; it alpha-renameable.
"""


def in_slotted_ruleset(text):
    """Put every emitted rule in the `slotted` ruleset.

    These rules maintain the encoding's invariants, and they have to be *saturated*
    between the user's rule steps: a user rule that matches a node before the alpha- and
    slot-canonicalisation of that node has finished sees a spelling that is about to
    change, and then matches again when it does. `egraph-encoding-11.egg` says
    what schedule to write; this only puts the rules where a schedule can name them.
    """
    out, depth, form, buf = [], 0, [], []
    for line in text.splitlines(keepends=True):
        if depth == 0 and not line.lstrip().startswith("("):
            buf.append(line)
            continue
        depth += line.count("(") - line.count(")")
        form.append(line)
        if depth <= 0:
            body = "".join(form)
            head = body.lstrip()[:6]
            if head in ("(rule ", "(rule\n") and ":ruleset" not in body:
                i = body.rindex(")")
                body = body[:i] + " :ruleset slotted)" + body[i + 1 :]
            out.append("".join(buf) + body)
            buf, form, depth = [], [], 0
    return "".join(out) + "".join(buf)


###############################################################################
# terms
###############################################################################


def map_of(d):
    """A renaming literal, from a dict."""
    if not d:
        return "(map-empty)"
    return "(map-of " + " ".join(f"{k} {v}" for k, v in sorted(d.items())) + ")"


def union_images(edges):
    """The identity on the union of the edges' images -- a node's own slots."""
    if not edges:
        return "(map-empty)"
    out = f"(map-image {edges[-1]})"
    for e in reversed(edges[:-1]):
        out = f"(map-union (map-image {e}) {out})"
    return out


def node_expr(op, edges, kids, pays=()):
    """`(Ctor pay... m c ...)`: one node, payloads interleaved into their columns."""
    cols, ci, pi = [], 0, 0
    for col in op.sig:
        if col in SLOTTED:
            cols += [edges[ci], kids[ci]]
            ci += 1
        else:
            cols.append(pays[pi])
            pi += 1
    return f"({op.ctor} {' '.join(cols)})" if cols else f"({op.ctor})"


class Op:
    """One high-level operator, and the constructor column-walk it compiles to.

    `ctor`  the egglog constructor.
    `sig`   its columns in order: `CHILD`, `BINDER`, or a payload sort.
    `pays`  one entry per payload column: a literal already spelled for egglog,
            where the operator pins it -- the generic encoding's head string is one --
            or `None` to take the value from the term's argument in that column.
    `ref`   the operator's name in the oracle's syntax. `None` marks a payload leaf,
            which the oracle writes as the payload itself.
    `ref_prefix`
            what that payload needs in front of it for the oracle to read it as a
            payload rather than a tag.

    A term's arguments line up with the columns that consume one: a sub-term for a
    `CHILD`, a slot for a `BINDER`, a value for a payload the operator does not pin.
    """

    def __init__(self, name, ctor, sig=(), pays=None, ref=None, ref_prefix=""):
        self.name = name
        self.ctor = ctor
        self.sig = list(sig)
        npay = sum(1 for c in self.sig if c not in SLOTTED)
        self.pays = list(pays) if pays is not None else [None] * npay
        assert len(self.pays) == npay, f"{name}: {npay} payload column(s)"
        self.ref = ref
        self.ref_prefix = ref_prefix

    @property
    def kid_cols(self):
        """The slotted columns, in order."""
        return [c for c in self.sig if c in SLOTTED]

    @property
    def binders(self):
        """The child positions -- counted over children -- whose slot the node binds."""
        return [i for i, c in enumerate(self.kid_cols) if c is BINDER]

    @property
    def covered(self):
        """The one child column a binder scopes over: the next one along."""
        return max(self.binders) + 1 if self.binders else None

    def arg_kinds(self):
        """One entry per term argument: `CHILD`, `BINDER`, or the payload's sort."""
        out, pi = [], 0
        for col in self.sig:
            if col in SLOTTED:
                out.append(col)
            else:
                if self.pays[pi] is None:
                    out.append(col)
                pi += 1
        return out

    def split(self, args):
        """`(kids, pays)`: the arguments in slotted columns, and a literal per
        payload column -- the operator's own where it pins one, else the argument
        spelled for its sort."""
        kids, pays, ai, pi = [], [], 0, 0
        for col in self.sig:
            if col in SLOTTED:
                kids.append(args[ai])
                ai += 1
            else:
                lit = self.pays[pi]
                if lit is None:
                    lit = f'"{args[ai]}"' if col == "String" else str(args[ai])
                    ai += 1
                pays.append(lit)
                pi += 1
        assert ai == len(args), f"{self.name}: {len(args)} argument(s) for {ai} column(s)"
        return kids, pays


class TermLang:
    """A high-level term language over the encoding: `{operator: Op}`.

    A term is `(op, arg...)`. `("var", s)` is the one built-in: the encoding has a
    single variable class `(Var 0)`, and a variable is that class reached by an edge
    `0 -> s`, so a bare variable at top level would lose its slot.

    A binder column's argument is the slot it binds, written either bare or as the
    `("var", s)` term some corpora spell it with.
    """

    VAR = "var"

    def __init__(self, ops):
        self.ops = dict(ops)

    @classmethod
    def from_language(cls, language):
        """One `Op` per constructor of a `read_language` signature table -- the shape
        the reference crate's `define_language!` produces, with no head to indirect
        through, so the operator IS the constructor."""
        return cls({name: Op(name, name, sig, ref=name) for name, sig in language.items()})

    def __getitem__(self, name):
        return self.ops[name]

    def __contains__(self, name):
        return name in self.ops

    @staticmethod
    def slot(arg):
        """A binder column's argument as a bare slot."""
        return arg[1] if isinstance(arg, tuple) else arg

    def slots(self, t):
        """The term's FREE slots.

        A binder's slot is free in every column but the one it covers, which is what
        `Bind<T>` wrapping a single child means: `let x = x in b` keeps the value's
        occurrence free.
        """
        if t[0] == self.VAR:
            return {t[1]}
        op = self.ops[t[0]]
        kids, _ = op.split(t[1:])
        bound = {self.slot(kids[i]) for i in op.binders}
        free = set()
        for i, k in enumerate(kids):
            if i in op.binders:
                continue
            s = self.slots(k)
            free |= (s - bound) if i == op.covered else s
        return free

    def edge(self, t):
        """The stored renaming from a child's slots into its parent's slot space.

        A variable is stored as the canonical `(Var 0)`, so its edge names slot 0;
        anything else is built at its own slot names, so its edge is the identity on
        its free slots -- for a binder that is the node's slots minus the bound one,
        which is what the class has.
        """
        if t[0] == self.VAR:
            return {0: t[1]}
        return {s: s for s in self.slots(t)}

    def enc(self, t):
        """Encoding syntax.

        A binder column holds the bound slot as an edge `0 -> s` to `(Var 0)`. The
        covered child's own edge still names that slot: the node carries it, and only
        the class drops it.
        """
        if t[0] == self.VAR:
            return "(Var 0)"
        op = self.ops[t[0]]
        kids, pays = op.split(t[1:])
        edges, cs = [], []
        for i, k in enumerate(kids):
            if i in op.binders:
                edges.append(map_of({0: self.slot(k)}))
                cs.append("(Var 0)")
            else:
                edges.append(map_of(self.edge(k)))
                cs.append(self.enc(k))
        return node_expr(op, edges, cs, pays)

    def sexpr(self, t):
        """Reference / oracle syntax."""
        if t[0] == self.VAR:
            return f"(var ${t[1]})"
        op = self.ops[t[0]]
        kids, pays = op.split(t[1:])
        if op.ref is None:
            # a payload leaf, written as its payload
            return op.ref_prefix + pays[0].strip('"')
        assert not (kids and None in op.pays), f"{op.name}: no oracle syntax for a payload argument beside a child"
        parts = [f"${self.slot(k)}" if i in op.binders else self.sexpr(k) for i, k in enumerate(kids)]
        return f"({op.ref} {' '.join(parts)})" if parts else op.ref

    def shift(self, t, k):
        """Add `k` to every slot in a term. Slot names carry no meaning, so no answer
        may change."""
        if t[0] == self.VAR:
            return (t[0], t[1] + k)
        out = []
        for kind, a in zip(self.ops[t[0]].arg_kinds(), t[1:], strict=True):
            if kind is CHILD:
                out.append(self.shift(a, k))
            elif kind is BINDER:
                out.append(self.shift(a, k) if isinstance(a, tuple) else a + k)
            else:
                out.append(a)
        return (t[0], *out)


###############################################################################
# rules
###############################################################################
#
# An ATOM is `(root, op, [child...])`, one per e-node of the flattened left-hand
# side, with each child one of
#
#   ("pv",  name)   a pattern variable
#   ("sl",  "$x")   a slot literal -- a binder column, or the reference's `(var $x)`
#                   in an ordinary column. Both are the class `(Var 0)` reached by an
#                   edge `0 -> $x`
#   ("cls", term)   a ground leaf node, matched through `RenamesToLeader` so the
#                   column is compared against the leaf's CLASS. Writing the leaf
#                   into the column instead matches the same rows -- a slotless class
#                   is unioned with its leader -- but this is the one spelling
#                   `flatten` emits, so a rule reads the same however it was written
#
# A RIGHT-HAND SIDE is a `("pv", name)`, a `("sl", "$x")`, or `(op, arg...)` to build
# a node -- its arguments right-hand sides for the slotted columns and plain values
# for any payload column the operator does not pin, so a ground leaf is the case with
# no slotted columns.
#
# `rhs_of` converts a plain nested term into that grammar for a caller that writes
# its variables as bare strings.
#
# The markers are read as markers, so no operator may be named `pv`, `sl` or `cls`.


def pvars_of(atom):
    """An atom's pattern variables -- its root and every `pv` child.

    A slot literal is not one: its constraint is an equality on a single slot, applied
    after the atom's renaming is solved, so it does not help pin that renaming down
    and does not count as connectivity.
    """
    return {atom[0]} | {c[1] for c in atom[2] if c[0] == "pv"}


def connected_order(lang, atoms, first=None, bugs=frozenset()):
    """Reorder so every atom after the first shares a variable with the prefix.

    Required, not an optimisation. An atom sharing nothing has no constraint on its
    `mp`, so every slot it needs is *minted* -- and the mint is a commitment the
    encoding cannot revisit. If a later atom then shows that a minted slot is really
    one the pattern already named, the two disagree and `find-mapping` fails, losing a
    match the reference finds. The reference's `multi_ematch` does not have this
    problem: it keeps such a slot flexible and lets `unify` merge it later.

    `first` names the atom to lead with. `None` takes the first that is not a binder:
    the leading atom fixes slots(pattern), those are the pattern's *free* slots, and a
    binder's bound slot is not free -- which follows from what the terms mean rather
    than from a measurement, so no case observes it and there is no mutation for it.
    Callers that lead deliberately pass an index: to check that the answer does not
    depend on which atom leads, or because their rules are mostly rooted at a binder
    and taking the root first pins each bound slot off its own edge instead of minting
    a name for it.
    """
    atoms = list(atoms)
    if "unordered" in bugs:
        return atoms
    if first is None:
        first = next((j for j, a in enumerate(atoms) if not lang[a[1]].binders), 0)
    out = [atoms[first]]
    rest = [a for j, a in enumerate(atoms) if j != first]
    seen = pvars_of(atoms[first])
    while rest:
        i = next((j for j, a in enumerate(rest) if pvars_of(a) & seen), 0)
        a = rest.pop(i)
        out.append(a)
        seen |= pvars_of(a)
    return out


def flatten(lang, term, root="?_p", tmp="?_t"):
    """A nested pattern as depth-1 atoms, pre-order, so every atom's root is a child
    of an earlier one -- which is the connectivity the recipe requires.

    Returns `(root, atoms)`. A child written `$x` is a slot literal, a ground leaf
    node is reached through its class, and any other sub-term gets a name of its own.
    """
    atoms, ctr = [], [0]

    def go(t, name):
        kids, nested = [], []
        for c in lang[t[0]].split(t[1:])[0]:
            if isinstance(c, str):
                kids.append(("sl", c) if c.startswith("$") else ("pv", c))
            elif not lang[c[0]].kid_cols:
                kids.append(("cls", c))
            else:
                ctr[0] += 1
                nm = f"{tmp}{ctr[0]}"
                kids.append(("pv", nm))
                nested.append((c, nm))
        atoms.append((name, t[0], kids))
        for c, nm in nested:
            go(c, nm)

    go(term, root)
    return root, atoms


def rhs_of(lang, t):
    """A plain nested term as a right-hand side in the grammar above: a bare string
    is a pattern variable unless it starts with `$`, and a payload argument is left
    alone.

    `(subst body $x t)` is the one head that is not a constructor. It is a call, not a
    node, so it cannot be built -- see `compile_rule`.
    """
    if isinstance(t, str):
        return ("sl", t) if t.startswith("$") else ("pv", t)
    if t[0] == SUBST:
        assert len(t) == 4, f"{SUBST} takes a body, a slot and a term: {t}"
        return (SUBST, *(rhs_of(lang, a) for a in t[1:]))
    out = [rhs_of(lang, a) if kind in SLOTTED else a for kind, a in zip(lang[t[0]].arg_kinds(), t[1:], strict=True)]
    return (t[0], *out)


def atom_lines(lang, root, atoms, var="var"):
    """A flattened pattern as the oracle's `atom` lines, or `None` if it has none.

    `(root_name, lines)`, with the leading `?` stripped as those lines want. An atom's
    children are pattern variables and slot literals, so:

      * a slot literal in a BINDER column is the bare `$x` that `Bind` holds;
      * anywhere else it is the TERM `(var $x)`, which needs an atom of its own, since
        an atom's child has to be a pattern variable;
      * a child reached through its own class -- a payload leaf written literally --
        gets an ATOM OF ITS OWN, since it cannot sit in a child position either, and the
        child refers to that; its payload is marked `#` so it stays a payload.

    `None` is not returned today, but the caller still handles it: a shape with no
    spelling would have to fall back to the nested matcher, which answers a different
    question.

    Asking the reference the FLATTENED question is what makes the comparison
    like-for-like: the encoding compiles rules by flattening them, and a nested pattern
    is not the same pattern (it records which variables sit under a binder).
    """
    out, extra = [], [0]
    for name, op, kids in atoms:
        binders = set(lang[op].binders)
        spelled = []
        for i, (kind, c) in enumerate(kids):
            if kind == "pv":
                spelled.append(c.lstrip("?"))
            elif kind == "sl" and i in binders:
                spelled.append(c)
            elif kind == "sl":
                extra[0] += 1
                v = f"_sl{extra[0]}"
                out.append(f"atom {v} {var} {c}")
                spelled.append(v)
            else:
                # a leaf reached through its own class. It cannot sit in a child position
                # either -- an atom's child has to be a pattern variable -- so it gets an
                # atom of its own and the child refers to that. Its payload is marked `#`
                # so it stays a payload rather than becoming a variable.
                extra[0] += 1
                v = f"_cl{extra[0]}"
                leaf = lang.sexpr(c)
                if leaf.startswith("("):
                    head, *pays = leaf[1:-1].split()
                    out.append(f"atom {v} {head} " + " ".join(f"#{x}" for x in pays))
                else:
                    out.append(f"atom {v} {leaf}")
                spelled.append(v)
        out.append(f"atom {name.lstrip('?')} {lang[op].ref or op} {' '.join(spelled)}")
    return root.lstrip("?"), out


def pat_sexpr(lang, t, binder=False):
    """A pattern term -- an atom's child, or a right-hand side -- in the oracle's
    syntax.

    A slot literal renders two ways: in a binder column it is the bare `$x` that
    `Bind` holds, and anywhere else it is the term `(var $x)`. The encoding stores
    both as an edge to `(Var 0)`, which is why one child kind covers both.
    """
    if t[0] == "pv":
        return f"?{t[1]}"
    if t[0] == "sl":
        return t[1] if binder else f"(var {t[1]})"
    if t[0] == "cls":
        return lang.sexpr(t[1])
    if t[0] == SUBST:
        # The reference's own spelling of a substitution, `b[x := t]`, which its
        # `Pattern::parse` accepts on a right-hand side (`src/rewrite/pattern.rs`).
        # Not a constructor, so `lang[...]` below would not find it.
        b, sl, tt = t[1:]
        return f"{pat_sexpr(lang, b)}[(var {sl[1]}) := {pat_sexpr(lang, tt)}]"
    op = lang[t[0]]
    kids, pays = op.split(t[1:])
    if op.ref is None:
        # a payload leaf, written as its payload -- with the prefix the oracle needs to
        # read it as a payload rather than a tag, exactly as `TermLang.sexpr` does for
        # a ground term. The two renderers have to agree: one writes a rule's pattern
        # and the other the terms that rule has to match.
        return op.ref_prefix + pays[0].strip('"')
    assert not (kids and None in op.pays), f"{op.name}: no oracle syntax for a payload argument beside a child"
    parts = [pat_sexpr(lang, k, binder=(i in op.binders)) for i, k in enumerate(kids)]
    return f"({op.ref} {' '.join(parts)})" if parts else op.ref


def compile_rule(
    lang,
    atoms,
    action,
    conds=(),
    fresh=(),
    bugs=frozenset(),
    slot_prefix="s",
    fresh_batch=True,
    tail=")",
    refine=True,
):
    """Compile a flattened multipattern and its action into one egglog rule.

    The recipe `slotted/tests/user-rules.egg` states. Atoms are taken in the order
    given, which must be connected (see `connected_order`). Per atom, in order:

      * one egglog atom per e-node, `(= V (Op m1 c1 ...))`;
      * `dom`, the identity on the atom's node slots;
      * `mp`, the least renaming total on `dom` agreeing with everything already
        known -- the root if an earlier atom bound it, every child an earlier atom
        bound, every slot literal an earlier atom pinned. `find-mapping-total`, so a
        slot the constraints do not reach is minted rather than dropped (M3). The
        leading atom is the degenerate case, where `mp` is the identity on `dom`;
      * the avoid-set, accumulated, so two atoms that both mint cannot collide (M5);
      * each slot literal read out of its edge, binding on first use and constraining
        on every later one;
      * the Def. 6 check for a variable repeated inside THIS atom (M2), against the
        class's one symmetry;
      * each child's renaming into pattern slots, narrowed by `ClassSlots` (M8).

    Then any right-hand side slot the pattern never pinned, the side conditions, and
    the action.

    `conds` are `(want, slot, [pvar...])`, reading "that slot is (not) among the slots
    of any listed variable" -- the reference's `subst[v].slots().contains(...)`. They
    come last, so every variable is bound and every slot literal pinned.

    `fresh` names right-hand side slots the pattern never pinned, which have to be
    minted. `fresh_batch` mints them in one solve over a domain of that size, else one
    solve each with the avoid-set growing between them; both give the same distinct
    slots, since one injective solve cannot repeat a name and neither can a grown
    avoid-set.

    `action` is `("build", root, rhs)` or `("row", root, op, [pvar...])`.

    `bugs` re-introduces a past mistake, so a corpus can be shown to still catch it:
    `root-only` solves an atom's renaming from its root alone, `slot-late` checks a
    slot literal after the renaming instead of with it, `wide-kids` uses a variable at
    the matched node's slots rather than its class's, `no-guard` drops the side
    conditions, `union-id` unions classes where the action should equate renamed ids,
    and `unordered` (in `connected_order`) leaves the atoms as written.

    `tail` closes the rule, and is where a ruleset and a name go.
    """
    body, uid = [], [0]

    def new(p):
        uid[0] += 1
        return f"{p}{uid[0]}"

    slot_groups = []  # one per atom: the pattern slots its node occupies, pairwise apart
    mp_of = {}  # pvar -> egglog var holding its renaming into slots(pattern)
    cls_of = {}  # pvar -> egglog var holding its leader
    slot_of = {}  # "$v" -> egglog i64 var holding that pattern slot
    sym_of = {}  # pvar -> its symmetry variable
    pat = None  # identity on the pattern slots named so far

    def narrow(m, cls):
        """Cut `m` down from the matched node's slots to its class's -- M8.

        A renaming read off a node has the *node's* slots for its domain, and a node
        may carry slots its class does not depend on. A variable stands for a class,
        so the wider map writes a slot into a built node that the child does not
        have, breaking Def. 4.

        Restricting by `ClassSlots` rather than by a symmetry: a symmetry is whichever
        self-loop the join happens to bind, and one of those can itself be wider than
        the class, in which case it narrows nothing.
        """
        if "wide-kids" in bugs:
            return m
        cs = new("cs")
        body.append(f"(= {cs} (ClassSlots {cls}))")
        return f"(compose {m} {cs})"

    def sym_for(pv):
        """A symmetry of `pv`'s class, joined from `RenamesToLeader`.

        One per class, shared by every use, so all uses must agree on it -- which is
        also what makes restricting a root's renaming by the live slot set affordable.
        """
        if pv not in sym_of:
            sv = new("sym")
            body.append(f"(RenamesToLeader {cls_of[pv]} {sv} {cls_of[pv]})")
            sym_of[pv] = sv
        return sym_of[pv]

    for idx, (aroot, opname, kids) in enumerate(atoms):
        op = lang[opname]
        assert None not in op.pays, f"{opname}: an atom cannot carry a payload argument"
        edges = [new("p") for _ in kids]
        rv = cls_of.setdefault(aroot, new("V"))
        cols, reached = [], []
        for k in kids:
            if k[0] == "pv":
                cols.append(cls_of.setdefault(k[1], new("C")))
            elif k[0] == "sl":
                cols.append("(Var 0)")
            else:
                cv = new("L")
                cols.append(cv)
                reached.append((k[1], cv))
        body.append(f"(= {rv} {node_expr(op, edges, cols, op.pays)})")
        for t, cv in reached:
            body.append(f"(RenamesToLeader {lang.enc(t)} {new('ml')} {cv})")

        dom = new("dom")
        body.append(f"(= {dom} {union_images(edges)})")

        firsts, seconds = [], []
        # the root, if an earlier atom already named its slots
        if aroot in mp_of:
            mv = mp_of[aroot]
            firsts.append(f"(compose {mv} {sym_for(aroot)})")
            seconds.append(f"(map-domain {mv})")
        # every child an earlier atom already named
        bound_before = set(mp_of)
        for k, e in zip(kids, edges, strict=True):
            if k[0] == "pv" and k[1] in bound_before and "root-only" not in bugs:
                firsts.append(f"(compose {mp_of[k[1]]} {sym_for(k[1])})")
                seconds.append(e)
        # A slot literal an earlier atom pinned constrains this atom's `mp` too:
        # `mp . edge = {0 -> that slot}`. Checking it afterwards instead is too late --
        # `mp` would already have minted a different name for the same binder, and
        # nothing revises a mint.
        for k, e in zip(kids, edges, strict=True):
            if k[0] == "sl" and k[1] in slot_of and "slot-late" not in bugs:
                firsts.append(f"(map-insert (map-empty) 0 {slot_of[k[1]]})")
                seconds.append(e)

        mp = new("mp")
        pairs = " ".join(firsts + seconds) if firsts else "(map-empty) (map-empty)"
        if idx == 0:
            # the leading atom fixes slots(pattern); its `mp` is the identity
            body.append(f"(= {mp} {dom})")
        else:
            body.append(f"(= {mp} (find-mapping-total {pat} {dom} {pairs}))")

        # Accumulate the avoid-set. Passing only the leading atom's slots would let
        # two atoms that both mint choose the same slot, since the primitive is pure
        # and sees one atom at a time. Identity maps never conflict under `map-union`,
        # so the running union is always well defined.
        idm = new("idm")
        body.append(f"(= {idm} (map-image {mp}))")
        slot_groups.append(idm)
        if idx == 0:
            pat = idm
        else:
            av = new("av")
            body.append(f"(= {av} (map-union {pat} {idm}))")
            pat = av

        # A slot literal names one slot in pattern space. `(= v ...)` binds it on
        # first use and constrains it on every later one, which is how the same `$v`
        # written twice forces the two slots to agree.
        for k, e in zip(kids, edges, strict=True):
            if k[0] == "sl":
                sv = slot_of.setdefault(k[1], slot_prefix + k[1][1:])
                body.append(f"(= {sv} (map-get (compose {mp} {e}) 0))")

        # walk the children: bind the new ones, check the ones bound in THIS atom
        for k, e in zip(kids, edges, strict=True):
            if k[0] != "pv":
                continue
            if k[1] in mp_of:
                # A child bound by an EARLIER atom is already handled: it went into
                # the renaming as a constraint, so the equation holds by construction.
                # One bound in THIS atom still needs checking. Under `root-only` the
                # constraint was skipped, so the check is what that bug had in its
                # place -- emitting neither would be a different, more permissive
                # mutant.
                if k[1] not in bound_before or "root-only" in bugs:
                    body.append(f"(= (compose {mp} {e}) (compose {mp_of[k[1]]} {sym_for(k[1])}))")
            else:
                m = new("m")
                body.append(f"(= {m} (compose {mp} {e}))")
                mp_of[k[1]] = narrow(m, cls_of[k[1]])
        if aroot not in mp_of:
            mp_of[aroot] = narrow(mp, rv)

    if refine:
        # `final_refine`: every way the match's slots may be merged, decided once the
        # whole match is fixed rather than atom by atom. Minting above committed each
        # unreached slot to being apart from everything; this is where that is revisited.
        #
        # Two bounds come from the primitive, and both need what is in hand only once
        # every atom has been read: the slots the PATTERN writes are never merged with
        # each other, and each atom's own slots are pairwise apart, which is what keeps
        # every renaming below injective.
        #
        # This sits BEFORE the right-hand side's fresh slots on purpose. A `:fresh` slot
        # is fresh by definition, so it is not a candidate for merging and must not be
        # in the domain at all.
        #
        # Everything after this point -- the side conditions and the action -- reads the
        # REFINED renamings. The reference does the same: it applies a rewrite's
        # condition to the substitutions `multi_ematch` returns, which are the refined
        # ones. Nothing is lost by that, because the pattern-slot rule is what keeps a
        # condition honest, not the order.
        pinned = "(map-of " + " ".join(f"{v} {v}" for v in slot_of.values()) + ")" if slot_of else "(map-empty)"
        alts, i, mrg = new("alts"), new("ix"), new("mrg")
        body.append(f"(= {alts} (refine-namings {pat} {pinned} {' '.join(slot_groups)}))")
        body.append(f"(Idx {i})")
        body.append(f"(= {mrg} (vec-get {alts} {i}))")
        # Index 0 is the identity, so a rule reaching only `(Idx 0)` answers as it did
        # before refinement existed.
        mp_of = {k: f"(compose {mrg} {v})" for k, v in mp_of.items()}
        slot_of = {k: f"(map-get {mrg} {v})" for k, v in slot_of.items()}
        # Two slots that merged no longer occupy two names, so a fresh slot minted
        # below avoids the refined set rather than the pre-merge one.
        pat = f"(map-image {mrg})"

    # Right-hand side slots the pattern never pinned: mint them, avoiding every slot
    # named so far. The reference writes a literal `$x` there; on this side a name has
    # to be invented.
    groups = []
    if fresh:
        groups = [tuple(fresh)] if fresh_batch else [(f,) for f in fresh]
    for group in groups:
        fm = new("fs" if fresh_batch else "fm")
        domain = " ".join(f"{i} {i}" for i in range(len(group)))
        body.append(f"(= {fm} (find-mapping-total {pat} (map-of {domain}) (map-empty) (map-empty)))")
        for i, s in enumerate(group):
            # a fresh name reusing a pattern literal's would silently constrain it
            assert s not in slot_of, f"{s} is already pinned by the pattern"
            sv = slot_of.setdefault(s, slot_prefix + s[1:])
            body.append(f"(= {sv} (map-get {fm} {i}))")
        if not fresh_batch:
            av = new("av")
            body.append(f"(= {av} (map-union {pat} (map-image {fm})))")
            pat = av

    # A variable's slots in pattern space are the image of its renaming, so

    # `$s in slots(?x)` is membership in `(map-image mx)`. With one variable that is a
    # fact; with several the disjunction has to be a value, since a fact cannot be
    # combined with `or`.
    for want, slot, pvars in conds:
        if "no-guard" in bugs:
            continue
        sv = slot_of[slot]
        images = [f"(map-image {mp_of[v]})" for v in pvars]
        if len(images) == 1:
            kind = "map-contains" if want else "map-not-contains"
            body.append(f"({kind} {images[0]} {sv})")
        else:
            expr = "(or " + " ".join(f"(bool-map-contains {im} {sv})" for im in images) + ")"
            body.append(f"(guard {expr})" if want else f"(guard (bool= {expr} false))")

    lets = []

    def build(t):
        """`(edge, class)` for a right-hand side, one `let` per built node.

        An action is already in pattern slot space, so the edge from a built node to a
        built child is the identity on that child's slots -- there is no renaming
        between them, which is what makes this a bottom-up walk. A built binder node's
        slots are its edges' images MINUS the slots it binds, since the node carries a
        bound slot and the class does not, and an edge naming a slot its child does
        not have breaks Def. 4.
        """
        if t[0] == "pv":
            return mp_of[t[1]], cls_of[t[1]]
        if t[0] == "sl":
            # the machinery carries a bound slot as an edge to `(Var 0)`
            return f"(map-insert (map-empty) 0 {slot_of[t[1]]})", "(Var 0)"
        op = lang[t[0]]
        args, pays = op.split(t[1:])
        if not args:
            return map_of(lang.edge(t)), lang.enc(t)  # a leaf node has no slots
        kids = [build(a) for a in args]
        nv = new("_rhs")
        lets.append(f"(let {nv} {node_expr(op, [e for e, _ in kids], [c for _, c in kids], pays)})")
        slots = union_images([e for e, _ in kids])
        for i in op.binders:
            slots = f"(map-remove {slots} {slot_of[args[i][1]]})"
        return slots, nv

    root = action[1]
    mr = mp_of[root]
    if action[0] == "build":
        rhs = action[2]
        if rhs[0] == "pv":
            # Equate two variables. Both carry a renaming into pattern slots and
            # neither need be the identity, which is the one action egglog's `union`
            # cannot express -- so solve: from mr*Root = ma*A follows
            # Root = (mr^-1 . ma) * A, and let the machinery re-orient it (M10).
            act = [f"(Equated {cls_of[root]} (compose (inverse {mr}) {mp_of[rhs[1]]}) {cls_of[rhs[1]]})"]
        elif rhs[0] == SUBST:
            # A call, not a node, so there is nothing to build. Everything below is in
            # PATTERN slots; the primitive works in the body's own frame, so a bridge
            # between the two is the whole of the work.
            b, sl, tt = rhs[1:]
            assert b[0] == "pv" and tt[0] == "pv", f"{SUBST}: body and term must be variables, got {b}, {tt}"
            assert sl[0] == "sl", f"{SUBST}: the slot must be a slot literal, got {sl}"
            mb, mt, x = mp_of[b[1]], mp_of[tt[1]], slot_of[sl[1]]
            need, rb, xb, tren, q = (new(p) for p in ("need", "rb", "xb", "tren", "q"))
            call = f"{cls_of[b[1]]} {xb} (Var 0) {tren} {cls_of[tt[1]]}"
            act = [
                # the pattern slots that must have a name in the body's frame. `t`'s
                # slots are the ones the body may not use, which is why a bridge is
                # needed at all -- `(compose (inverse mb) mt)` would drop them, since
                # `compose` truncates.
                f"(let {need} (map-union (map-image {mb}) (map-union (map-image {mt}) (map-of {x} {x}))))",
                # `rb . mb = id`, so `rb` runs pattern slots into the body's frame,
                # minting a name for each one the body does not use.
                f"(let {rb} (find-mapping-total (map-domain {mb}) {need} (map-domain {mb}) {mb}))",
                f"(let {xb} (map-get {rb} {x}))",
                # total, not truncating: this asserts the bridge is wide enough for `t`
                # rather than silently dropping one of its slots.
                f"(let {tren} (compose-total {rb} {mt}))",
                f"(let {q} (compose (inverse {mr}) (inverse {rb})))",
                f"(SubstPending {cls_of[root]} {q} (slotted-subst-frame {call}) (slotted-subst {call}))",
            ]
        else:
            _, built = build(rhs)
            act = lets + [f"(Equated {built} {mr} {cls_of[root]})"]
    else:
        # The flat build: one depth-1 node over bound variables. The built node lives
        # in pattern slots, so the equation to assert is `built = mr * Root` -- a union
        # over renamed ids, which egglog's `union` cannot express, since it equates
        # e-classes, i.e. only the case where both renamings are the identity. That
        # union is the `union-id` mutant, and it shows up as spurious redundancy.
        #
        # `Equated`, not `RenamesToLeader`, for the reason M10 gives. This one used to
        # write the oriented row directly, and `let` is lookup-or-insert: when the node
        # already exists it can sort BELOW the root, which makes the row backwards, and
        # the stale-row deleter then removes a fact with no `Equated` behind it to
        # re-derive. The corpus never built that state, so nothing caught it.
        pvs = action[3]
        node = node_expr(lang[action[2]], [mp_of[v] for v in pvs], [cls_of[v] for v in pvs], lang[action[2]].pays)
        if "union-id" in bugs:
            act = [f"(union {cls_of[root]} {node})"]
        else:
            act = [f"(let _hn {node})", f"(Equated _hn {mr} {cls_of[root]})"]

    return "(rule (" + "\n       ".join(body) + ")\n      (" + "\n       ".join(act) + ")" + tail
