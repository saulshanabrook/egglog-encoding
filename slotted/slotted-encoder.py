#!/usr/bin/env python3
"""Generate the slotted e-graph encoding from typed constructors and rules.

The implementation has four layers: constructor signatures, invariant-maintenance
rules, term encoding, and MultiPattern rule encoding. Each equality-sort carrier has
its own `CarrierSymbols`; renaming maps and layout metadata are shared.

The executable derivation and worked examples live in
`slotted/encoding/user-rules.egg`; `slotted-user-rules.md` contains the longer design
rationale. This module keeps only the invariants needed beside their implementation.
"""

from dataclasses import dataclass

CHILD = object()  # a slotted child: `Renaming U`
BINDER = object()  # a slotted child that also binds its slot

SLOTTED = (CHILD, BINDER)


@dataclass(frozen=True)
class CarrierSymbols:
    """Generated constructor and relation names for one equality sort."""

    sort: str
    var: str
    renames: str
    equated: str
    class_slots: str
    subst_pending: str

    @classmethod
    def create(cls, sort, index=None):
        suffix = "" if index is None else f"_{index}"
        return cls(
            sort,
            f"SlottedVar{suffix}" if suffix else "Var",
            f"RenamesToLeader{suffix}",
            f"Equated{suffix}",
            f"ClassSlots{suffix}",
            f"SubstPending{suffix}",
        )


def carrier_symbols(sorts):
    """One symbol family per declared equality sort, in declaration order."""
    sorts = tuple(sorts)
    if len(sorts) == 1:
        return {sorts[0]: CarrierSymbols.create(sorts[0])}
    return {sort: CarrierSymbols.create(sort, i) for i, sort in enumerate(sorts)}


###############################################################################
# language specs
###############################################################################


def read_language(path, sorts=("U",)):
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
        name = head.strip()
        # `tail` is the output sort, then the options, then the closing paren
        tokens = tail.rstrip(")").split()
        opts = next((i for i, t in enumerate(tokens) if t.startswith(":")), len(tokens))
        language[name] = signature(cols_text.split(), constructor_options(name, tokens[opts:]), sorts, name)
    return language


#: egglog's own `(constructor ...)` options. Recognised so they can be refused by name
#: rather than ignored: extraction here does not honour them, and a silently dropped
#: `:cost` leaves a program doing something other than what it says.
EGGLOG_CTOR_OPTIONS = (":cost", ":unextractable", ":internal-term-constructor")


def constructor_options(name, tokens):
    """The binder positions a constructor's options declare.

    `:binder <pos>...` is this language's one addition to egglog's constructor options,
    and may stand anywhere among them. egglog's own are refused by name.
    """
    binders, seen = [], None
    for tok in tokens:
        if isinstance(tok, str) and tok.startswith(":"):
            if tok in EGGLOG_CTOR_OPTIONS:
                raise SystemExit(
                    f"constructor {name}: `{tok}` is egglog's and is not implemented here. "
                    "Extraction over the encoding would not honour it, so it is refused "
                    "rather than dropped in silence."
                )
            if tok != ":binder":
                raise SystemExit(f"constructor {name}: unknown option `{tok}`")
            seen = tok
            continue
        if seen == ":binder":
            binders.append(int(tok))
    return binders


def signature(cols, binders, sorts=("U",), name="constructor"):
    """Columns and the binding child positions as the encoder's signature.

    A column whose sort is one the program DECLARED is a slotted child and expands to
    `Renaming <sort>`; anything else -- `i64`, `String`, a primitive -- is a payload and
    passes through. `sorts` defaults to the carrier the hand-written core declares.
    """
    child_count = sum(col in sorts for col in cols)
    if len(set(binders)) != len(binders):
        raise SystemExit(f"constructor {name}: duplicate `:binder` position")
    if any(pos < 0 or pos >= child_count for pos in binders):
        raise SystemExit(f"constructor {name}: `:binder` position is outside its {child_count} child columns")
    if binders:
        lo, hi = min(binders), max(binders)
        if sorted(binders) != list(range(lo, hi + 1)):
            raise SystemExit(f"constructor {name}: `:binder` positions must be contiguous")
        if hi + 1 >= child_count:
            raise SystemExit(f"constructor {name}: `:binder` columns must be followed by the child they cover")

    sig, seen_kids = [], 0
    for col in cols:
        if col in sorts:
            sig.append(BINDER if seen_kids in binders else CHILD)
            seen_kids += 1
        else:
            sig.append(col)
    return sig


def read_language_form(form, sorts=("U",)):
    """One parsed `(constructor Name (U U) U :binder 0)` as `{name: signature}`.

    The list form, for a test that declares its language inline rather than pointing
    at a file. Same syntax, same meaning.
    """
    assert form[0] == "constructor" and isinstance(form[2], list), form
    name, cols = form[1], form[2]
    return {name: signature(cols, constructor_options(name, form[4:]), sorts, name)}


def read_typed_language_form(form, sorts=("U",)):
    """One constructor declaration with the sort information the generic recipe erases.

    Returns ``(name, signature, output_sort, child_sorts)``.  ``signature`` remains
    the historical CHILD/BINDER/payload walk, while ``child_sorts`` records the
    equality sort of each slotted column.  Keeping both lets the existing term and
    rule algorithms stay structural while multi-sort emission selects the right
    per-sort tables at every edge.
    """
    assert form[0] == "constructor" and isinstance(form[2], list), form
    name, cols, output = form[1], form[2], form[3]
    if output not in sorts:
        raise SystemExit(
            f"constructor {name}: output sort {output!r} is not one of the declared equality sorts ({', '.join(sorts)})"
        )
    sig = signature(cols, constructor_options(name, form[4:]), sorts, name)
    return name, sig, output, tuple(col for col in cols if col in sorts)


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


def declare(name, sig, sort="U"):
    """The `(constructor ...)` line for one signature: a slotted column becomes the two
    egglog columns `Renaming <sort>`, a payload column stays as it is.

    `sort` is the carrier -- the sort a node has and a slotted child is reached through.
    It defaults to the one the hand-written core declares, and is the program's own when
    it declared one."""
    cols = " ".join(f"Renaming {sort}" if c in SLOTTED else c for c in sig)
    return f"(constructor {name} ({cols}) {sort})\n"


def layout(name, sig, heads=()):
    """Runtime layout metadata for ``slotted-subst``.

    The primitive cannot distinguish an equality-sort column from a container by
    looking at egglog's erased ``Id`` column type.  The compiler therefore records
    every physical edge column explicitly.  Binder rows additionally say which edge
    is the marker, which later edge it covers, and (for the generic string-headed
    encoding) the payload value that activates the binder.

    Column indices are zero-based indices into the encoded constructor inputs, after
    every slotted source column has expanded to ``Renaming <carrier>``.
    """
    physical, edges, payloads = 0, [], []
    child_positions = []
    for col in sig:
        if col in SLOTTED:
            edges.append(physical)
            child_positions.append(col)
            physical += 2
        else:
            payloads.append(physical)
            physical += 1

    out = [f'(set (SlottedNodeLayout "{name}" {physical}) ())']
    out += [f'(set (SlottedEdgeLayout "{name}" {edge}) ())' for edge in edges]

    bound = [i for i, col in enumerate(child_positions) if col is BINDER]
    if bound:
        covered = max(bound) + 1
        out += [f'(set (SlottedBinderLayout "{name}" {edges[pos]} {edges[covered]} -1 "") ())' for pos in bound]

    if heads:
        assert payloads, f"{name}: a string-headed binder needs a payload discriminator"
        assert len(edges) >= 2, f"{name}: a binder needs a covered child"
        discriminator = payloads[0]
        out += [
            f'(set (SlottedBinderLayout "{name}" {edges[0]} {edges[1]} {discriminator} "{head}") ())' for head in heads
        ]
    return out


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


def _symbols(symbols):
    """The historical single-sort names when a caller needs no namespace."""
    return symbols or CarrierSymbols.create("U")


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


#: WHAT A BINDER COLUMN IS, and why three rules have to know.
#:
#: `Lam([0 -> x] * Var, m2*c2)` is `lam $x. m2*c2`. The `[0 -> x]` is the name the node
#: BINDS, and the `Var` under it is only how the encoding spells a slot -- not a child the
#: node uses. That distinction is invisible in the columns, which is why it has to be
#: written into the rules that rewrite them, and it matters because the variable class
#: goes SLOTLESS as soon as two of its invocations are equated. From then on every
#: renaming it offers is the empty map, and composing a binder edge with one erases the
#: bound name. Once erased, every later match of a binder pattern -- which reads that slot
#: out of the edge -- silently fails, and the reference, whose `Bind` holds a `Slot`
#: outright, keeps making unions we no longer make.
#:
#: The two rules that compose an edge do it for different reasons, so they need different
#: answers:
#:
#:   `child_update` follows the child's renaming toward its LEADER, which a binder column
#:      does need -- reaching `[0 -> x] * Var(0)` from `[x -> x] * Var(x)` is how two
#:      spellings of one binder are seen to be alpha-equivalent. So the rule stays and
#:      asks for the bound name in the result: renaming it passes, losing it does not.
#:
#:   `alpha_finder` and `symmetry_finder` compose with the child's own SYMMETRY, to try
#:      the other spellings of the same invocation. A binder column has no other
#:      spelling, so they skip it. Asking for the name to survive would not do here: the
#:      shrinking rule deletes a slotless class's identity self-loop, leaving the empty
#:      map as the only symmetry on offer, and the rule would simply stop firing.
BOUND_NAME_KEPT = "\n       ; a bound name may be renamed but not lost\n       (= bound{i} (map-get {edge} 0))"


def class_slots(name, sig, symbols=None):
    """A node's own slots, offered as an upper bound on its class's.

    `ClassSlots` intersects on merge, so a class ends up with the slots *every* one of
    its nodes has -- anything only some of them carry is redundant. That is the
    reference's `c.slots`, which starts as the creating node's slots and afterwards
    only shrinks. Deriving it from a node is safe here precisely because the merge can
    only narrow, unlike the self-loop rule, which asserts the node's slots outright.
    """
    symbols = _symbols(symbols)
    _, edges, _, _ = cols_of(sig)
    slots = fold("map-union", [f"(map-image {m})" for m in edges], "(map-empty)")
    return f"""\
(rule ((= e1 {pattern(name, sig)}))
      ((set ({symbols.class_slots} e1) {slots})))
"""


def self_loop(name, sig, symbols=None):
    """A node's class gets the identity on the node's own slots."""
    symbols = _symbols(symbols)
    _, edges, _, _ = cols_of(sig)
    slots = fold("map-union", [f"(map-image {m})" for m in edges], "(map-empty)")
    return f"""\
(rule ((= e1 {pattern(name, sig)})
       (= m {slots}))
      (({symbols.renames} e1 m e1)))
"""


def alpha_finder(name, sig, bound=(), exempt=(), head=None, symbols=None):
    """Two nodes equal up to renaming: keep one, record how the other renames to it.

    For `e1 = f(m1*c1, m1'*c2)` and `e2 = f(m2*c1, m2'*c2)`, the solve
    `(find-mapping m1 m1' m2 m2')` is the least `m` with `m*m2 = m1` and `m*m2' = m1'`, so

        m*e2 = f(m*m2*c1, m*m2'*c2) = f(m1*c1, m1'*c2) = e1

    which is the `RenamesToLeader` this records before deleting `e2`'s row.

    Payload columns are named by the same variable on both sides, so a difference
    there simply does not match -- no separate check needed.

    `bound` names binder columns, which are compared as stored rather than composed with a
    symmetry of their child; see `BOUND_NAME_KEPT`. What the solve then has to find is the
    renaming carrying one bound name to the other, which is what makes `lam $1. e` and
    `lam $2. e` alpha-equivalent once neither name is free in `e`. `head` and `exempt`
    split the rule by operator string, which the string-headed encoding needs and a
    structural binder does not; see `emit`.
    """
    symbols = _symbols(symbols)
    payloads, edges, kids, _ = cols_of(sig)
    a_o = [f"{e}_o" for e in edges]
    a = [a_o[i] if i in bound else e for i, e in enumerate(edges)]
    b = [f"b{i + 1}" for i in range(len(edges))]
    syms = [f"sym{i + 1}" for i in range(len(kids))]
    pays = [f'"{head}"'] if head is not None else None
    loops = "\n       ".join(
        f"({symbols.renames} {kids[i]} {syms[i]} {kids[i]})" for i in range(len(kids)) if i not in bound
    )
    composed = "\n       ".join(f"(= {a[i]} (compose {a_o[i]} {syms[i]}))" for i in range(len(edges)) if i not in bound)
    not_binder = "".join(f'\n       (!= {payloads[0]} "{h}")' for h in exempt)
    return f"""\
(rule ((= e1 {pattern(name, sig, edges=a_o, payloads=pays)})
       (= e2 {pattern(name, sig, edges=b, payloads=pays)})
       (= e1 (ordering-max e1 e2)){not_binder}
       {loops}
       {composed}
       (= m (find-mapping {" ".join(a)} {" ".join(b)}))
       (guard
         (or (bool-!= e1 e2)
             (and (bool= e1 e2)
                  {lex_greater(a_o, b)}))))
      (({symbols.equated} e1 m e2)
       (delete {pattern(name, sig, edges=a_o, payloads=pays)})))
"""


def symmetry_finder(name, sig, bound=(), exempt=(), head=None, symbols=None):
    """The same solve, kept non-destructively as a symmetry of the class.

    Restricted to the class's slots. `sym_out` is solved from a *node's* edges, so its
    domain is the node's slots, and a node may carry slots its class does not depend on --
    so unrestricted it asserts a symmetry the class does not have. The shrinking rule then
    deletes that, this rule derives it again, and neither ever wins: four generated cases
    never reached a fixpoint of the rules for exactly this reason. `ClassSlots` only
    narrows, so restricting on both sides leaves nothing to shrink.

    This is the same mistake as the self-loop rule's, and the same one open question 2
    warns about -- do not derive a class-level fact from a node.

    `bound`, `head` and `exempt` mean what they do in `alpha_finder`. A symmetry that moved
    a bound name would say nothing anyway: `cs` has had it removed by the binder rule.
    """
    symbols = _symbols(symbols)
    payloads, edges, kids, _ = cols_of(sig)
    a_o = [f"{e}_o" for e in edges]
    a = [a_o[i] if i in bound else e for i, e in enumerate(edges)]
    syms = [f"sym{i + 1}" for i in range(len(kids))]
    pays = [f'"{head}"'] if head is not None else None
    loops = "\n       ".join(
        f"({symbols.renames} {kids[i]} {syms[i]} {kids[i]})" for i in range(len(kids)) if i not in bound
    )
    composed = "\n       ".join(f"(= {a[i]} (compose {a_o[i]} {syms[i]}))" for i in range(len(edges)) if i not in bound)
    not_binder = "".join(f'\n       (!= {payloads[0]} "{h}")' for h in exempt)
    return f"""\
(rule ((= e {pattern(name, sig, edges=a_o, payloads=pays)}){not_binder}
       {loops}
       {composed}
       (= sym_out (find-mapping {" ".join(a_o)} {" ".join(a)}))
       (= cs ({symbols.class_slots} e)))
      (({symbols.renames} e (compose cs (compose sym_out cs)) e)))
"""


def migration(name, sig, symbols=None):
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
    symbols = _symbols(symbols)
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
(rule (({symbols.renames} e2 m e1)
       (= e2 {pattern(name, sig)})
       (!= e1 e2)
       (= e2 (ordering-max e1 e2))       ; toward the leader only
       {pulled})
      ((union e1 {pattern(name, sig, edges=ns)})
       (delete {pattern(name, sig)})))
"""


def child_update(name, sig, pos, exempt=(), head=None, bound_name=False, symbols=None):
    """Replace child `pos` with its more canonical `m*c'`.

    One rule per child position, canonicalising that child to the class's representative:
    the stored edge composes with the child's renaming, `m1` becoming `m1 . m`.

    `bound_name` says this column holds a name the node binds rather than a child it uses,
    and adds the one condition that makes the rewrite safe there: the bound slot must
    survive the composition. See `BOUND_NAME_KEPT`.

    `head` pins the operator string and `exempt` rules operator strings out, both for the
    string-headed encoding, where one constructor serves every operator of an arity and
    so a column is a bound name or not depending on the row's payload.

    Only ever toward the leader, for the same reason migration needs it: a slotted class
    spans several values and `RenamesToLeader` holds both directions between them, so
    without an orientation the child pointer follows an edge one way, is rewritten back
    the next round, and the node row is deleted and rebuilt forever. `ordering-min` is
    the direction the single-parent rule already establishes. When the class is unchanged
    the atom holds trivially, so the self-symmetry case below is unaffected.
    """
    symbols = _symbols(symbols)
    payloads, edges, kids, _ = cols_of(sig)
    new_e, new_k = list(edges), list(kids)
    new_e[pos] = f"(compose {edges[pos]} m)"
    new_k[pos] = "c'"
    pays = [f'"{head}"'] if head is not None else None
    conds = "".join(f'\n       (!= {payloads[0]} "{h}")' for h in exempt)
    if bound_name:
        conds += BOUND_NAME_KEPT.format(i=pos, edge=new_e[pos])
    return f"""\
(rule (({symbols.renames} {kids[pos]} m c')
       (= node {pattern(name, sig, payloads=pays)}){conds}
       (= {kids[pos]} (ordering-max {kids[pos]} c'))    ; toward the leader only
       ; if the class is unchanged then m must be idempotent: no self-symmetries
       (guard (or (bool-!= {kids[pos]} c') (bool= (compose m m) m)))
       ; and the new node must differ from the old one
       (guard (or (bool-!= {kids[pos]} c')
                  (bool-!= (compose {edges[pos]} m) {edges[pos]}))))
      ((union node {pattern(name, sig, edges=new_e, kids=new_k, payloads=pays)})
       (delete {pattern(name, sig, payloads=pays)})))
"""


def binder(name, sig, positions, head=None, symbols=None):
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
    symbols = _symbols(symbols)
    _, edges, kids, _ = cols_of(sig)
    e, k = list(edges), list(kids)
    for n, pos in enumerate(positions):
        e[pos], k[pos] = f"mvar{n}", f"({symbols.var} 0)"
    payloads = [f'"{head}"'] if head is not None else None
    node = pattern(name, sig, edges=e, kids=k, payloads=payloads)

    covered = max(positions) + 1
    assert covered < len(kids), f"{name}: a binder must cover a following column"
    uncovered = [i for i in range(len(kids)) if i not in positions and i != covered]

    rules = []
    for n, pos in enumerate(positions):
        free_elsewhere = "".join(f"\n       (map-not-contains (map-image {edges[u]}) v{n})" for u in uncovered)
        rules.append(f"""\
(rule (({symbols.renames} {node} ml l)
       (= v{n} (map-get mvar{n} 0)){free_elsewhere})
      (({symbols.equated} {node} (inverse (map-remove (inverse ml) v{n})) l)))
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


def binder_variants(emit_rule, name, sig, comment, bound, heads, symbols=None):
    """`emit_rule` for the ordinary case, plus a head-pinned copy per string-headed binder.

    `bound` are the columns that are binder columns structurally, and `heads` the operator
    strings whose first slotted column is a bound name -- which only the string-headed
    encoding has, since there one constructor serves every operator. Each returned rule is
    preceded by its comment.
    """
    which = ", ".join(str(i + 1) for i in bound)
    note = f", leaving child {which} alone -- a bound name has no other spelling" if bound else ""
    out = [comment + note, emit_rule(name, sig, bound=bound, exempt=heads, symbols=symbols)]
    pinned = tuple(sorted({*bound, 0}))
    for head in heads:
        out += [
            f"{comment}, for `{head}`, whose child 1 is a bound name",
            emit_rule(name, sig, bound=pinned, head=head, symbols=symbols),
        ]
    return out


def emit(language, binders=(), provided=None, omit=(), sort="U", symbols=None):
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

    THREE RULES TREAT A BINDER COLUMN DIFFERENTLY -- the alpha-finder, the symmetry-finder
    and child-update -- because a bound name is not a child. `BOUND_NAME_KEPT` above says
    what goes wrong when they do not, and which answer each one needs.

    Where the binder is declared by the head string rather than the signature -- the
    string-headed encoding, where one constructor serves every operator of an arity -- the
    same column is a bound name in some rows and a child in others, so each of the three
    is emitted twice: once with those heads ruled out, once with the head pinned. A
    structurally declared binder needs only the second.
    """
    symbols = _symbols(symbols)
    out = []
    for name, sig in language.items():
        if name in omit:
            out += banner(f"{name} :: {' '.join(shape_of(c) for c in sig)} -- hand-written in egraph-encoding-11.egg")
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
        heads = [head for head, ctor in binders if ctor == name]
        out += [
            declare(name, sig, sort),
            ";; complete physical layout for the substitution primitive",
            *layout(name, sig, heads),
            ";; an upper bound on the class's slots; the merge narrows it",
            class_slots(name, sig, symbols),
            ";; every class holding a node has a self-loop, so a query can reach it",
            self_loop(name, sig, symbols),
        ]
        if not kids:
            continue  # nothing below touches a child
        kid_cols = [c for c in sig if c in SLOTTED]
        structural = tuple(i for i, c in enumerate(kid_cols) if c is BINDER)
        # a head-pinned binder always covers the first slotted column
        out += binder_variants(
            alpha_finder,
            name,
            sig,
            ";; alpha-finder: two nodes equal up to renaming, one eliminated",
            structural,
            heads,
            symbols,
        )
        out += binder_variants(
            symmetry_finder,
            name,
            sig,
            ";; the same solve kept as a symmetry, non-destructively",
            structural,
            heads,
            symbols,
        )
        out += [";; migration: move a follower's node into the leader's frame", migration(name, sig, symbols)]
        for pos in range(len(kids)):
            if kid_cols[pos] is BINDER:
                out += [
                    f";; child-update, child {pos + 1} -- a bound name",
                    child_update(name, sig, pos, bound_name=True, symbols=symbols),
                ]
                continue
            exempt = heads if pos == 0 else ()
            out += [
                f";; child-update, child {pos + 1}",
                child_update(name, sig, pos, exempt=exempt, symbols=symbols),
            ]
            for head in exempt:
                out += [
                    f";; child-update, child {pos + 1} of `{head}` -- a bound name there",
                    child_update(name, sig, pos, head=head, bound_name=True, symbols=symbols),
                ]

    binder_rules = []
    for name, sig in language.items():
        kid_cols = [c for c in sig if c in SLOTTED]
        bound = [i for i, c in enumerate(kid_cols) if c is BINDER]
        if bound and name not in omit:
            which = ", ".join(str(i + 1) for i in bound)
            binder_rules.append(
                (
                    f";; `{name}` binds child {which}, one rule per bound slot",
                    binder(name, sig, bound, symbols=symbols),
                )
            )
    for head, name in binders:
        if name in omit:
            continue
        binder_rules.append(
            (
                f";; `{head}` binds its first child's slot",
                binder(name, language[name], [0], head=head, symbols=symbols),
            )
        )
    if binder_rules:
        out += banner("binders")
        for comment, rule in binder_rules:
            out += [comment, rule]
    return out


#: The right-hand side head that is a call rather than a node.
SUBST = "subst"


# The constructor-independent half of the node machinery. Hand-written in
# `slotted/encoding/egraph-encoding-11.egg` along with a constructor or two, and kept
# here so a generator can state what that text has to say.
SHARED = """\
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; complete physical constructor layouts for `slotted-subst`
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Custom Unit-valued functions keep metadata out of the encoded e-graph.  A
;; relation would mint an equality-sort value and appear as another constructor.
;; The primitive validates these schemas and refuses constructors without a complete
;; row, so an erased Id column is never guessed to be an edge or a payload.
(function SlottedNodeLayout (String i64) Unit :no-merge :internal-hidden)
(function SlottedEdgeLayout (String i64) Unit :no-merge :internal-hidden)
(function SlottedBinderLayout (String i64 i64 i64 String) Unit :no-merge :internal-hidden)

(set (SlottedNodeLayout "Var" 1) ())
(set (SlottedNodeLayout "Null" 0) ())

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
;; `m` takes b's slots to a's. Transporting a slot set through a renaming is the image of
;; the renaming restricted to that set.
(rule ((RenamesToLeader a m b) (= slots (ClassSlots a)))
      ((set (ClassSlots b) (map-image (compose (inverse m) slots)))))
(rule ((RenamesToLeader a m b) (= slots (ClassSlots b)))
      ((set (ClassSlots a) (map-image (compose m slots)))))
"""


def carrier_core(symbols):
    """Constructor-independent rules for one carrier."""
    s = symbols
    return "\n".join(
        [
            ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;",
            f";;; carrier {s.sort}: {s.renames}, {s.equated}, {s.class_slots}",
            ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;",
            "",
            f"(sort {s.sort})",
            f"(constructor {s.var} (i64) {s.sort})",
            f"(relation {s.renames} ({s.sort} Renaming {s.sort}))",
            f"(relation {s.equated} ({s.sort} Renaming {s.sort}))",
            f"(function {s.class_slots} ({s.sort}) Renaming :merge (map-intersect old new))",
            f"(relation {s.subst_pending} ({s.sort} Renaming Renaming {s.sort}))",
            "",
            f'(set (SlottedNodeLayout "{s.var}" 1) ())',
            f"(set ({s.class_slots} ({s.var} 0)) (map-of 0 0))",
            "",
            # Orient equations toward the smaller leader.
            f"""(rule (({s.equated} a m b)
       (!= a b)
       (= a (ordering-max a b)))
      (({s.renames} a m b)) :ruleset slotted)""",
            "",
            f"""(rule (({s.equated} a m b)
       (!= a b)
       (= b (ordering-max a b)))
      (({s.renames} b (inverse m) a)) :ruleset slotted)""",
            "",
            f"""(rule (({s.equated} a m a))
      (({s.renames} a m a)) :ruleset slotted)""",
            "",
            # Remove an edge whose leader changed after a native union.
            f"""(rule (({s.renames} f m l)
       (!= f l)
       (= l (ordering-max f l)))
      ((delete ({s.renames} f m l))) :ruleset slotted)""",
            "",
            # Transport the exact class-slot set in either direction.
            f"""(rule (({s.renames} a m b) (= slots ({s.class_slots} a)))
      ((set ({s.class_slots} b) (map-image (compose (inverse m) slots))))
      :ruleset slotted)""",
            f"""(rule (({s.renames} a m b) (= slots ({s.class_slots} b)))
      ((set ({s.class_slots} a) (map-image (compose m slots))))
      :ruleset slotted)""",
            "",
            # Close paths and reconcile competing leaders.
            f"""(rule (({s.renames} e1 m12 e2)
       ({s.renames} e2 m23 e3)
       (guard (or (bool-!= e2 e3)
                  (bool= (compose m23 m23) m23)
                  (bool= e1 e3))))
      (({s.equated} e1 (compose m12 m23) e3)) :ruleset slotted)""",
            "",
            f"""(rule (({s.renames} a m1 b)
       ({s.renames} a m2 c)
       (!= a c)
       (!= a b)
       (= (ordering-max b c) b)
       (guard (or (bool-!= b c)
                  (and (bool= b c)
                       (bool-!= m1 m2)
                       (bool= (ordering-max m1 m2) m1)))))
      ((delete ({s.renames} a m1 b))
       ({s.equated} b (compose (inverse m1) m2) c)) :ruleset slotted)""",
            "",
            # Keep one canonical idempotent self-loop.
            f"""(rule (({s.renames} a m1 a)
       ({s.renames} a m a)
       (= m (compose m m))
       (= m2 (compose m (compose m1 m)))
       (!= m1 m2))
      ((delete ({s.renames} a m1 a))
       ({s.renames} a m2 a)) :ruleset slotted)""",
            "",
            # Store every variable as a renamed invocation of slot zero.
            f"""(rule ((= e ({s.var} v))
       (!= v 0))
      (({s.equated} e (map-insert (map-empty) 0 v) ({s.var} 0))
       (delete ({s.var} v))) :ruleset slotted)""",
            "",
            f"({s.renames} ({s.var} 0) (map-insert (map-empty) 0 0) ({s.var} 0))",
            "",
            # Native-union two values that denote the same invocation.
            f"""(rule (({s.renames} a m1_o c)
       ({s.renames} b m2 c)
       ({s.renames} c sym c)
       (= m1 (compose m1_o sym))
       (= m (compose m1 (inverse m2)))
       (= (compose m m) m))
      ((union a b)) :ruleset slotted)""",
            "",
            # Move a primitive substitution result back into the root frame.
            f"""(rule (({s.subst_pending} root q mr r)
       (= cs ({s.class_slots} r)))
      (({s.equated} root (compose q (compose mr cs)) r))
      :ruleset slotted)""",
            "",
        ]
    )


def multi_sort_core(carriers):
    """Shared declarations followed by one isolated core per carrier."""
    header = "\n".join(
        [
            ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;",
            ";;; multi-sort slotted machinery",
            ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;",
            "",
            "(ruleset slotted)",
            "",
            "(function SlottedNodeLayout (String i64) Unit :no-merge :internal-hidden)",
            "(function SlottedEdgeLayout (String i64) Unit :no-merge :internal-hidden)",
            "(function SlottedBinderLayout (String i64 i64 i64 String) Unit :no-merge :internal-hidden)",
            "",
        ]
    )
    return "\n".join([header, *(carrier_core(symbols) for symbols in carriers.values())])


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


def pay_text(op, pay):
    """A payload as the ORACLE spells it.

    A pattern tags its payloads, and the oracle's syntax has a place for a literal but
    not for a variable: its patterns bind slots and applied ids, not payload values. So
    a variable there is refused rather than mis-spelled.
    """
    if isinstance(pay, tuple):
        if pay[0] == "ppv":
            raise SystemExit(
                f"{op.name}: the oracle cannot be asked about a payload VARIABLE "
                f"({pay[1]!r}); its patterns have no place for one."
            )
        pay = pay[1]
    return pay.strip('"')


def node_expr(op, edges, kids, pays=(), pay_var=None):
    """`(Ctor pay... m c ...)`: one node, payloads interleaved into their columns.

    A payload arrives either already spelled -- a literal the operator pins, or a ground
    term's value -- or TAGGED by a pattern: `("plit", value)` to spell here against the
    column's sort, or `("ppv", name)` for a variable, which `pay_var` turns into the
    egglog name that binds it. Spelling in one place is what keeps a string from being
    quoted twice.
    """
    cols, ci, pi = [], 0, 0
    for col in op.sig:
        if col in SLOTTED:
            cols += [edges[ci], kids[ci]]
            ci += 1
        else:
            p = pays[pi]
            if isinstance(p, tuple):
                if p[0] == "ppv":
                    if pay_var is None:
                        raise SystemExit(f"{op.name}: a payload variable ({p[1]!r}) where no pattern binds one")
                    p = pay_var(p[1])
                else:
                    p = f'"{p[1]}"' if col == "String" else str(p[1])
            cols.append(p)
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

    def __init__(
        self,
        name,
        ctor,
        sig=(),
        pays=None,
        ref=None,
        ref_prefix="",
        sort="U",
        kid_sorts=None,
    ):
        self.name = name
        self.ctor = ctor
        self.sig = list(sig)
        self.sort = sort
        self.kid_sorts = list(kid_sorts) if kid_sorts is not None else [sort] * sum(c in SLOTTED for c in self.sig)
        assert len(self.kid_sorts) == sum(c in SLOTTED for c in self.sig), (
            f"{name}: {len(self.kid_sorts)} child sort(s) for {sum(c in SLOTTED for c in self.sig)} slotted column(s)"
        )
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
                    a = args[ai]
                    # a pattern's payload arrives tagged and is spelled by `compile_rule`
                    lit = a if isinstance(a, tuple) else (f'"{a}"' if col == "String" else str(a))
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

    def __init__(self, ops, carriers=None):
        self.ops = dict(ops)
        declared = []
        for op in self.ops.values():
            for sort in (op.sort, *op.kid_sorts):
                if sort not in declared:
                    declared.append(sort)
        self.carriers = carriers or carrier_symbols(declared or ("U",))
        self.default_sort = next(iter(self.carriers))

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

    def symbols_for(self, sort):
        return self.carriers[sort]

    def sort_of(self, t, expected=None):
        """The equality sort of a term; a bare variable inherits its context."""
        if t[0] == self.VAR:
            return expected
        return self.ops[t[0]].sort

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

    def refresh_shadowed_binders(self, t):
        """Give repeated binder columns the reference language's `Bind` meaning.

        `Sum(A, Bind<Bind<A>>)` and `Merge(A, A, Bind<Bind<Bind<A>>>)` are
        lexically nested binders even though the encoding flattens their names into
        sibling columns.  If two layers use the same source name, the innermost one
        shadows the outer one.  Leaving both columns equal instead identifies two
        private slots and produces a different e-node.  Alpha-refresh only the
        shadowed OUTER column; occurrences in the covered body continue to name the
        innermost binder.

        Fresh names avoid every slot written anywhere in this term, including
        uncovered columns.  Running this over the whole tree before recursive
        encoding also avoids colliding with an enclosing binder.
        """

        def all_slots(x):
            if isinstance(x, str):
                return {x} if x.startswith("$") else set()
            if x[0] == self.VAR:
                return {x[1]}
            if x[0] not in self.ops:  # a front-end's opaque, already-bound name
                return set()
            op = self.ops[x[0]]
            out = set()
            for kind, arg in zip(op.arg_kinds(), x[1:], strict=True):
                if kind is BINDER:
                    out.add(self.slot(arg))
                elif kind is CHILD:
                    out |= all_slots(arg)
            return out

        used = all_slots(t)
        pattern_slots = any(isinstance(s, str) and s.startswith("$") for s in used)
        fresh_index = [0]

        def fresh():
            if pattern_slots:
                while True:
                    s = f"$__shadow{fresh_index[0]}"
                    fresh_index[0] += 1
                    if s not in used:
                        used.add(s)
                        return s
            s = 0
            while s in used:
                s += 1
            used.add(s)
            return s

        def go(x):
            if isinstance(x, str):
                return x
            if x[0] == self.VAR or x[0] not in self.ops:
                return x
            op = self.ops[x[0]]
            args = [
                go(a) if kind is CHILD and isinstance(a, tuple) else a
                for kind, a in zip(op.arg_kinds(), x[1:], strict=True)
            ]
            kids, _pays = op.split(args)
            seen = set()
            for i in reversed(op.binders):
                name = self.slot(kids[i])
                if name in seen:
                    # `args` and child positions differ when fixed payload columns are
                    # present; find this child column in the argument walk.
                    child_index = -1
                    for ai, kind in enumerate(op.arg_kinds()):
                        if kind in SLOTTED:
                            child_index += 1
                            if child_index == i:
                                args[ai] = fresh()
                                break
                else:
                    seen.add(name)
            return (x[0], *args)

        return go(t)

    def enc(self, t, expected_sort=None):
        """Encoding syntax.

        A binder column holds the bound slot as an edge `0 -> s` to `(Var 0)`. The
        covered child's own edge still names that slot: the node carries it, and only
        the class drops it.
        """
        t = self.refresh_shadowed_binders(t)
        if t[0] == self.VAR:
            sort = expected_sort or self.default_sort
            return f"({self.symbols_for(sort).var} 0)"
        op = self.ops[t[0]]
        if expected_sort is not None and op.sort != expected_sort:
            raise SystemExit(f"{op.name} produces {op.sort}, but this position requires {expected_sort}")
        kids, pays = op.split(t[1:])
        edges, cs = [], []
        for i, k in enumerate(kids):
            if i in op.binders:
                edges.append(map_of({0: self.slot(k)}))
                cs.append(f"({self.symbols_for(op.kid_sorts[i]).var} 0)")
            else:
                edges.append(map_of(self.edge(k)))
                cs.append(self.enc(k, op.kid_sorts[i]))
        return node_expr(op, edges, cs, pays)

    def sexpr(self, t):
        """Reference / oracle syntax."""
        if t[0] == self.VAR:
            return f"(var ${t[1]})"
        op = self.ops[t[0]]
        kids, pays = op.split(t[1:])
        if op.ref is None:
            # a payload leaf, written as its payload
            return op.ref_prefix + pay_text(op, pays[0])
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

    def kids_of(a):
        return {c[1] for c in a[2] if c[0] == "pv"}

    out = [atoms[first]]
    rest = [a for j, a in enumerate(atoms) if j != first]
    seen = pvars_of(atoms[first])
    roots = {atoms[first][0]}
    kids = kids_of(atoms[first])
    while rest:
        # A PARENT/CHILD link first, and a sibling one only if there is none. Sharing a
        # variable is necessary and not sufficient: where the shared variable is a CHILD
        # of both atoms, the constraint reaches only that child's slots and the rest of
        # the new atom's frame is minted -- and a mint is a commitment. Where it is one
        # atom's ROOT and the other's child, the share is a stored EDGE, which relates
        # the two frames whole.
        #
        # `K2` is the case: of the six orders of its three atoms, the two that left the
        # parent atom last lost a match and the other four did not.
        i = next(
            (j for j, a in enumerate(rest) if a[0] in kids or kids_of(a) & roots),
            None,
        )
        if i is None:
            i = next((j for j, a in enumerate(rest) if pvars_of(a) & seen), 0)
        a = rest.pop(i)
        out.append(a)
        seen |= pvars_of(a)
        roots.add(a[0])
        kids |= kids_of(a)
    return out


def slot_literals(t, out=None):
    """Every slot literal a term mentions, as the `$x` strings a pattern writes."""
    out = set() if out is None else out
    if isinstance(t, tuple):
        if len(t) == 2 and t[0] == "sl":
            out.add(t[1])
        else:
            for a in t:
                slot_literals(a, out)
    return out


def has_pay_var(t):
    """Does this sub-term bind a payload VARIABLE anywhere?

    Such a term is not ground, so it cannot be reached through its class -- it has to be
    matched like any other atom.
    """
    if not isinstance(t, tuple):
        return False
    if len(t) == 2 and t[0] == "ppv":
        return True
    return any(has_pay_var(a) for a in t)


def plain_pays(t):
    """This sub-term with its payload literals untagged, for the ground spellers.

    A pattern tags its payloads; a term named by its class is ground, so every payload
    in it is a literal and the tag has no more work to do.
    """
    if not isinstance(t, tuple):
        return t
    if len(t) == 2 and t[0] == "plit":
        return t[1]
    if len(t) == 2 and t[0] in ("pv", "sl", "cls", "var", "name"):
        return t
    return tuple(plain_pays(a) for a in t)


def flatten(lang, term, root="?_p", tmp="?_t"):
    """A nested pattern as depth-1 atoms, pre-order, so every atom's root is a child
    of an earlier one -- which is the connectivity the recipe requires.

    Returns `(root, atoms)`. A child written `$x` is a slot literal, a ground leaf
    node is reached through its class, and any other sub-term gets a name of its own.

    An atom is `(root, op, kids, pays)`. The payloads ride along because a pattern may
    match on one or bind it, and dropping them here is what made an operator with a
    payload column unusable in any rule.
    """
    term = lang.refresh_shadowed_binders(term)
    atoms, ctr = [], [0]

    def go(t, name):
        kids, nested = [], []
        cs, pays = lang[t[0]].split(t[1:])
        for c in cs:
            if isinstance(c, str):
                kids.append(("sl", c) if c.startswith("$") else ("pv", c))
            elif not lang[c[0]].kid_cols and not has_pay_var(c):
                kids.append(("cls", plain_pays(c)))
            else:
                ctr[0] += 1
                nm = f"{tmp}{ctr[0]}"
                kids.append(("pv", nm))
                nested.append((c, nm))
        atoms.append((name, t[0], kids, pays))
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
    t = lang.refresh_shadowed_binders(t)
    if isinstance(t, str):
        return ("sl", t) if t.startswith("$") else ("pv", t)
    if t[0] == SUBST:
        assert len(t) == 4, f"{SUBST} takes a body, a slot and a term: {t}"
        return (SUBST, *(rhs_of(lang, a) for a in t[1:]))
    out = [rhs_of(lang, a) if kind in SLOTTED else a for kind, a in zip(lang[t[0]].arg_kinds(), t[1:], strict=True)]
    return (t[0], *out)


def atom_lines(lang, root, atoms, var="var"):
    """A flattened pattern as the oracle's `MultiPattern` atom lines.

    `(root_name, lines)`, with the leading `?` stripped as those lines want. An atom's
    children are pattern variables and slot literals, so:

      * a slot literal in a BINDER column is the bare `$x` that `Bind` holds;
      * anywhere else it is the TERM `(var $x)`, which needs an atom of its own, since
        an atom's child has to be a pattern variable;
      * a child reached through its own class -- a payload leaf written literally --
        gets an ATOM OF ITS OWN, since it cannot sit in a child position either, and the
        child refers to that; its payload is marked `#` so it stays a payload.

    Asking the reference the flattened question makes the comparison like-for-like:
    the encoding implements `MultiPattern`, not the reference's distinct nested
    pattern language.
    """
    out, extra = [], [0]
    for name, op, kids, *_pays in atoms:
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
        return op.ref_prefix + pay_text(op, pays[0])
    assert not (kids and None in op.pays), f"{op.name}: no oracle syntax for a payload argument beside a child"
    parts = [pat_sexpr(lang, k, binder=(i in op.binders)) for i, k in enumerate(kids)]
    return f"({op.ref} {' '.join(parts)})" if parts else op.ref


def infer_pattern_sorts(lang, atoms):
    """Infer each MultiPattern variable's carrier from its atom positions."""
    sorts = {}

    def bind(pvar, sort):
        previous = sorts.setdefault(pvar, sort)
        if previous != sort:
            raise SystemExit(f"pattern variable {pvar!r} is used at both equality sorts {previous} and {sort}")

    for root, opname, kids, *_payloads in atoms:
        op = lang[opname]
        bind(root, op.sort)
        for kid, child_sort in zip(kids, op.kid_sorts, strict=True):
            if kid[0] == "pv":
                bind(kid[1], child_sort)
            elif kid[0] == "cls":
                actual = lang.sort_of(kid[1], child_sort)
                if actual != child_sort:
                    raise SystemExit(f"{opname}: a {child_sort} child cannot contain a {actual} term")
    return sorts


def build_rhs(lang, term, expected_sort, pvar_sorts, mp_of, cls_of, slot_of, new, pay_name):
    """Build an RHS bottom-up and return its emitted lets, slot map, and class."""
    lets = []

    def go(t, sort):
        if t[0] == "pv":
            actual = pvar_sorts[t[1]]
            if actual != sort:
                raise SystemExit(f"right-hand side uses {t[1]!r} as {sort}, but the pattern binds it as {actual}")
            return mp_of[t[1]], cls_of[t[1]]
        if t[0] == "sl":
            var = lang.symbols_for(sort).var
            return f"(map-insert (map-empty) 0 {slot_of[t[1]]})", f"({var} 0)"

        op = lang[t[0]]
        if op.sort != sort:
            raise SystemExit(f"right-hand side builds {op.name}, which produces {op.sort}, where {sort} is required")
        args, pays = op.split(t[1:])
        if not args:
            if has_pay_var(t):
                value = new("_rhs")
                lets.append(f"(let {value} {node_expr(op, [], [], pays, pay_name)})")
                return "(map-empty)", value
            return map_of(lang.edge(t)), lang.enc(t, sort)

        kids = [go(arg, child_sort) for arg, child_sort in zip(args, op.kid_sorts, strict=True)]
        value = new("_rhs")
        lets.append(
            f"(let {value} {node_expr(op, [edge for edge, _ in kids], [cls for _, cls in kids], pays, pay_name)})"
        )

        # Binder slots are absent from their marker and covered child, but remain
        # free in every uncovered child.
        bound = [slot_of[args[i][1]] for i in op.binders]
        slot_maps = []
        for i, (edge, _cls) in enumerate(kids):
            slots = f"(map-image {edge})"
            if i in op.binders or i == op.covered:
                for slot in bound:
                    slots = f"(map-remove {slots} {slot})"
            slot_maps.append(slots)
        slots = "(map-empty)"
        for child_slots in reversed(slot_maps):
            slots = f"(map-union {child_slots} {slots})"
        return slots, value

    edge, cls = go(term, expected_sort)
    return lets, edge, cls


def lower_substitution(lang, root, rhs, pvar_sorts, mp_of, cls_of, slot_of, new):
    """Lower `(subst body $x replacement)` through the body's local frame."""
    root_sort = pvar_sorts[root]
    symbols = lang.symbols_for(root_sort)
    body, slot, replacement = rhs[1:]
    assert body[0] == "pv" and replacement[0] == "pv", (
        f"{SUBST}: body and term must be variables, got {body}, {replacement}"
    )
    assert slot[0] == "sl", f"{SUBST}: the slot must be a slot literal, got {slot}"
    for pvar in (body[1], replacement[1]):
        if pvar_sorts[pvar] != root_sort:
            raise SystemExit(
                f"{SUBST}: {pvar!r} has sort {pvar_sorts[pvar]}, but the rewritten root has sort {root_sort}"
            )

    body_map, replacement_map, x = mp_of[body[1]], mp_of[replacement[1]], slot_of[slot[1]]
    needed, into_body, body_x, replacement_renaming, back_to_root = (
        new(name) for name in ("need", "rb", "xb", "tren", "q")
    )
    table_arg = f' "{symbols.class_slots}"' if len(lang.carriers) > 1 else ""
    primitive_args = (
        f"{cls_of[body[1]]} {body_x} ({symbols.var} 0) {replacement_renaming} {cls_of[replacement[1]]}{table_arg}"
    )
    return [
        f"(let {needed} (map-union (map-image {body_map}) (map-union (map-image {replacement_map}) (map-of {x} {x}))))",
        f"(let {into_body} (find-mapping-total (map-domain {body_map}) {needed} (map-domain {body_map}) {body_map}))",
        f"(let {body_x} (map-get {into_body} {x}))",
        f"(let {replacement_renaming} (compose-total {into_body} {replacement_map}))",
        f"(let {back_to_root} (compose (inverse {mp_of[root]}) (inverse {into_body})))",
        f"({symbols.subst_pending} {cls_of[root]} {back_to_root} "
        f"(slotted-subst-frame {primitive_args}) (slotted-subst {primitive_args}))",
    ]


def compile_rule(
    lang,
    atoms,
    action,
    conds=(),
    diseq=(),
    same=(),
    fresh=(),
    bugs=frozenset(),
    slot_prefix="s",
    fresh_batch=True,
    tail=")",
    refine=True,
):
    """Compile a flattened multipattern and its action into one egglog rule.

    Connected atoms are solved in order into one shared pattern frame. Each step
    preserves M1--M8 from `encoding/user-rules.egg`; final refinement, conditions,
    and the action implement M9--M11. `bugs` deliberately restores past mistakes for
    mutation testing.
    """
    body, uid = [], [0]

    pvar_sorts = infer_pattern_sorts(lang, atoms)

    def new(p):
        uid[0] += 1
        return f"{p}{uid[0]}"

    slot_groups = []  # one per atom: the pattern slots its node occupies, pairwise apart
    mp_of = {}  # pvar -> egglog var holding its renaming into slots(pattern)
    cls_of = {}  # pvar -> egglog var holding its leader
    slot_of = {}  # "$v" -> egglog i64 var holding that pattern slot
    # A slot literal in an ordinary child is the flattened spelling of a `(Var
    # $v)` pattern. The reference gives that child its own substitution entry, so
    # its slot participates in final refinement even when every surrounding class
    # has made it redundant. Binder-column literals are stored directly in the
    # pattern node and do not add such an entry.
    carried_slot_literals = set()
    pat = None  # identity on the pattern slots named so far

    def narrow(m, cls, sort):
        """Restrict a node-frame renaming to the class's exact slots (M8)."""
        if "wide-kids" in bugs:
            return m
        cs = new("cs")
        body.append(f"(= {cs} ({lang.symbols_for(sort).class_slots} {cls}))")
        return f"(compose {m} {cs})"

    def sym_for(pv):
        """Give each repeated occurrence an independent class symmetry."""
        sv = new("sym")
        table = lang.symbols_for(pvar_sorts[pv]).renames
        body.append(f"({table} {cls_of[pv]} {sv} {cls_of[pv]})")
        return sv

    pay_of = {}  # a payload variable's egglog name, shared so two atoms join on it
    binding = [True]  # only a PATTERN introduces one; the action may only read them

    def pay_name(n):
        if n not in pay_of:
            if not binding[0]:
                raise SystemExit(
                    f"the right-hand side names the payload variable {n!r}, which no "
                    "pattern binds -- there is nothing to take its value from"
                )
            pay_of[n] = new("pay")
        return pay_of[n]

    for idx, atom in enumerate(atoms):
        aroot, opname, kids = atom[0], atom[1], atom[2]
        op = lang[opname]
        if len(atom) > 3:
            pays = atom[3]
        else:
            if None in op.pays:
                raise SystemExit(
                    f"{opname}: a payload column with no value. An atom built by hand must "
                    "pin every payload its operator does not."
                )
            pays = op.pays
        edges = [new("p") for _ in kids]
        rv = cls_of.setdefault(aroot, new("V"))
        cols, reached = [], []
        for k, kid_sort in zip(kids, op.kid_sorts, strict=True):
            if k[0] == "pv":
                cols.append(cls_of.setdefault(k[1], new("C")))
            elif k[0] == "sl":
                cols.append(f"({lang.symbols_for(kid_sort).var} 0)")
            else:
                cv = new("L")
                cols.append(cv)
                reached.append((k[1], cv, kid_sort))
        body.append(f"(= {rv} {node_expr(op, edges, cols, pays, pay_name)})")
        for t, cv, kid_sort in reached:
            table = lang.symbols_for(kid_sort).renames
            body.append(f"({table} {lang.enc(t, kid_sort)} {new('ml')} {cv})")

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
        carried_slot_literals.update(k[1] for i, k in enumerate(kids) if k[0] == "sl" and i not in op.binders)

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
                mp_of[k[1]] = narrow(m, cls_of[k[1]], pvar_sorts[k[1]])
        if aroot not in mp_of:
            mp_of[aroot] = narrow(mp, rv, pvar_sorts[aroot])

    binding[0] = False  # every atom is read, so a payload variable can only be read now

    if refine:
        # Reconsider minted distinctions after the whole match is known. Only slots
        # carried by substitutions may merge; written slots and slots within one atom
        # remain distinct. Conditions and actions consume the refined frame.
        pinned = "(map-of " + " ".join(f"{v} {v}" for v in slot_of.values()) + ")" if slot_of else "(map-empty)"
        cand = pat
        carried = [f"(map-image {v})" for v in mp_of.values()]
        carried.extend(f"(map-of {slot_of[s]} {slot_of[s]})" for s in sorted(carried_slot_literals))
        if carried:
            cand = new("carr")
            expr = carried[0]
            for im in carried[1:]:
                expr = f"(map-union {im} {expr})"
            body.append(f"(= {cand} {expr})")
        alts, i, mrg = new("alts"), new("ix"), new("mrg")
        body.append(f"(= {alts} (refine-namings {cand} {pinned} {' '.join(slot_groups)}))")
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
    # A right-hand-side slot the pattern never pins is FRESH BY DEFINITION, so it is
    # inferred rather than declared -- the reference mints one on the spot
    # (`Slot::fresh()` in rewrite/ematch.rs) with nothing written by the author. An
    # explicit `fresh` is still honoured and adds nothing an inferred set does not hold.
    pinned = {k[1] for a in atoms for k in a[2] if isinstance(k, tuple) and k[0] == "sl"}
    fresh = sorted(set(fresh) | (slot_literals(action) - pinned))

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

    # `(= x y)` between two variables: the same class reached by the same renaming,
    # which is what `=` means here, so both halves are asserted.
    for a, b in same:
        for v in (a, b):
            if v not in mp_of:
                raise SystemExit(f"`=` names {v!r}, which no pattern binds")
        if pvar_sorts[a] != pvar_sorts[b]:
            raise SystemExit(f"`=` cannot identify {a!r} ({pvar_sorts[a]}) with {b!r} ({pvar_sorts[b]})")
        body.append(f"(= {cls_of[a]} {cls_of[b]})")
        body.append(f"(= {mp_of[a]} {mp_of[b]})")

    # Invocations differ when their class or their renaming differs. Like egglog's
    # native `!=`, this condition is non-monotonic across later unions.
    for a, b in diseq:
        for v in (a, b):
            if v not in mp_of:
                raise SystemExit(f"`!=` names {v!r}, which no pattern binds")
        if pvar_sorts[a] != pvar_sorts[b]:
            raise SystemExit(f"`!=` cannot compare {a!r} ({pvar_sorts[a]}) with {b!r} ({pvar_sorts[b]})")
        same_cls = f"(bool= {cls_of[a]} {cls_of[b]})"
        same_ren = f"(bool= {mp_of[a]} {mp_of[b]})"
        body.append(f"(guard (or (not {same_cls}) (not {same_ren})))")

    root = action[1]
    root_sort = pvar_sorts[root]
    root_symbols = lang.symbols_for(root_sort)
    mr = mp_of[root]
    if action[0] == "build":
        rhs = action[2]
        if rhs[0] == "pv":
            # Equate two variables. Both carry a renaming into pattern slots and
            # neither need be the identity, which is the one action egglog's `union`
            # cannot express -- so solve: from mr*Root = ma*A follows
            # Root = (mr^-1 . ma) * A, and let the machinery re-orient it (M10).
            if pvar_sorts[rhs[1]] != root_sort:
                raise SystemExit(
                    f"a {root_sort} rewrite cannot return pattern variable {rhs[1]!r} of sort {pvar_sorts[rhs[1]]}"
                )
            act = [f"({root_symbols.equated} {cls_of[root]} (compose (inverse {mr}) {mp_of[rhs[1]]}) {cls_of[rhs[1]]})"]
        elif rhs[0] == SUBST:
            act = lower_substitution(lang, root, rhs, pvar_sorts, mp_of, cls_of, slot_of, new)
        else:
            lets, _, built = build_rhs(lang, rhs, root_sort, pvar_sorts, mp_of, cls_of, slot_of, new, pay_name)
            act = lets + [f"({root_symbols.equated} {built} {mr} {cls_of[root]})"]
    else:
        # A depth-one action writes `Equated`: the built node and root may use
        # different frames, which native `union` cannot express (M10).
        pvs = action[3]
        action_op = lang[action[2]]
        if action_op.sort != root_sort:
            raise SystemExit(f"a {root_sort} rule cannot build {action_op.name}, which produces {action_op.sort}")
        for pv, kid_sort in zip(pvs, action_op.kid_sorts, strict=True):
            if pvar_sorts[pv] != kid_sort:
                raise SystemExit(f"{action_op.name}: child {pv!r} has sort {pvar_sorts[pv]}, not {kid_sort}")
        node = node_expr(action_op, [mp_of[v] for v in pvs], [cls_of[v] for v in pvs], action_op.pays)
        if "union-id" in bugs:
            act = [f"(union {cls_of[root]} {node})"]
        else:
            act = [f"(let _hn {node})", f"({root_symbols.equated} _hn {mr} {cls_of[root]})"]

    return "(rule (" + "\n       ".join(body) + ")\n      (" + "\n       ".join(act) + ")" + tail
