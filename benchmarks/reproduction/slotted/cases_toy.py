"""Frozen regression case data and renderers, retained for explicit reproduction."""

from . import ROOT
from . import differential_source as driver
from . import reference as syntax

BINOPS = ["Add", "F", "G", "H", "K", "Sub", "Sub2"]

PERM_CAP = 4


LANG_DIR = ROOT / "egglog-experimental" / "tests" / "slotted" / "languages"

LANG = syntax.language(LANG_DIR / "toy.egg", LANG_DIR / "toy.ref")

assert sorted(op for op, o in LANG.ops.items() if len(o.kid_cols) == 2 and not o.binders) == BINOPS, (
    f"BINOPS and toy.egg disagree: {BINOPS}"
)

slots, sexpr, shift_term = LANG.slots, LANG.sexpr, LANG.shift

SYM = LANG.symbols_for(LANG.default_sort)


def swap_slots(t, s1, s2):
    """`t` with slots `s1` and `s2` exchanged."""
    if t[0] == "var":
        return ("var", s2 if t[1] == s1 else s1 if t[1] == s2 else t[1])
    if t[0] in ("Null", "Num"):
        return t
    return (t[0], *(swap_slots(x, s1, s2) for x in t[1:]))


def shift_case(case, k):
    """The same case with every slot in the program renamed by `+k`.

    Slot names carry no meaning, so this must not change any answer. It is a
    per-side property, needing no cross-system comparison, and it is a different
    question from agreeing with the reference: a side could be consistently wrong
    and still shift-invariant, or right on one naming and wrong on another. The
    reference's own suite checks it (`props.rs`).
    """
    return Case(
        case.name,
        [shift_term(t, k) for t in case.terms],
        [(shift_term(a, k), shift_term(b, k)) for a, b in case.unions],
        None,
        None,
        [shift_term(t, k) for t in case.probes],
        case.rounds,
        rules=case.rules,
    )


class Case:
    """One e-graph, one rule *set*, and the probes whose partition is compared.

    A rule is `(atoms, action)` or `(atoms, action, conds)`, where a condition is
    `(want, slot, pvars)`: `want` says whether the slot should be among the slots of
    any listed variable. Pass `rules=[...]` for a set, or the single-rule
    `atoms, action` form; `case.atoms` and `case.action` then read rule 0, which is
    what the single-rule checks and `show` use.
    """

    lang = LANG

    def egg_program(self, *, mult):
        return egg_program(self, mult=mult)

    def __init__(self, name, terms, unions, atoms, action, probes, rounds=10, rules=None):
        self.name = name
        self.terms = terms  # [term]
        self.unions = unions  # [(term, term)]
        # [(atoms, action, conds)]; atoms are [(root, op, c1, c2)] over pvar names
        rules = list(rules) if rules is not None else [(atoms, action)]
        rules = [r if len(r) == 3 else (r[0], r[1], []) for r in rules]
        # Two identical rules are one rule, and emitting both makes egglog reject the
        # program: it names a rule by its text, so the second is a duplicate name.
        seen, deduped = set(), []
        for r in rules:
            if repr(r) not in seen:
                seen.add(repr(r))
                deduped.append(r)
        self.rules = deduped
        self.probes = probes  # [term]
        self.rounds = rounds

    @property
    def atoms(self):
        return self.rules[0][0]

    @property
    def action(self):
        return self.rules[0][1]

    @property
    def conds(self):
        return self.rules[0][2]

    def spec(self, rules=None):
        rules = self.rules if rules is None else rules
        out = []
        for atoms, action, conds in rules:
            if not atoms:
                continue
            # the separator is only needed from the second rule on, but emitting it
            # always keeps the spec readable
            out.append("rule")
            # `atom_lines` rather than one line per atom: a child that is neither a
            # pattern variable nor a binder's slot -- a PAYLOAD LEAF written literally --
            # cannot sit in a child position on the oracle's side, and needs an atom of
            # its own. That is the same spelling `xarray` and `xsdql` use, so the two
            # cannot drift.
            enc_atoms = [(r, o, [_child(c1), _child(c2)]) for (r, o, c1, c2) in atoms]
            out += syntax.atom_lines(LANG, enc_atoms[0][0], enc_atoms)[1]
            for want, slot, pvars in conds:
                kind = "in" if want else "notin"
                out.append(f"cond {kind} {slot} {' '.join(pvars)}")
            if action and len(action) == 2:
                out.append(f"rhs {action[0]} {rhs_text(action[1])}")
            elif action:
                root, ctor, a, b = action
                tag = "=" if ctor == "=" else LANG[ctor].ref
                out.append(f"action {root} {tag} {a} {b}")
        return driver.reference_spec(LANG, self.rounds, self.terms, self.unions, out, self.probes)


def rhs_text(t):
    """An RHS tree as reference pattern text: `(h (g ?a ?b) ?b)`."""
    return syntax.pat_sexpr(LANG, syntax.rhs_of(LANG, t))


def _child(c):
    """An atom's child, in the encoder's grammar.

    A child written `$v` names a variable occurrence, or a rigid Var in a binder
    position. The source renderer adds the declared variable constructor only
    in a term position. One written `#k` is the PAYLOAD LEAF `k`, reached through its own class --
    the same spelling the oracle's `atom` line uses for one.
    """
    if c.startswith("#"):
        return ("cls", ("Num", int(c[1:])))
    return ("sl", c) if c.startswith("$") else ("pv", c)


def source_rule(atoms, action, conds=()):
    atoms = [(r, o, [_child(c1), _child(c2)]) for r, o, c1, c2 in atoms]
    if len(action) == 2:
        root, rhs = action
        rhs = syntax.rhs_of(LANG, rhs)
    elif action[1] == "=":
        root, rhs = action[0], ("pv", action[2])
    else:
        root, op, a, b = action
        rhs = (op, _child(a), _child(b))
    return driver.rewrite(LANG, atoms, root, rhs, conds=conds)


def egg_program(case, rules=None, mult=3):
    rules = case.rules if rules is None else rules
    return driver.program(
        "toy",
        LANG,
        [source_rule(a, act, cs) for a, act, cs in rules if a],
        case.terms,
        case.unions,
        case.probes,
        case.rounds * mult,
    )


V0, V1, V2 = ("var", 0), ("var", 1), ("var", 2)

LEAF0 = ("Sub", V0, V0)

NUL = ("Null",)


def curated():
    cs = []

    cs.append(
        Case(
            "literal-variable-names",
            [("F", ("G", V0, V1), V2)],
            [],
            [("x", "F", "?x", "??x"), ("?x", "G", "a", "b")],
            ("x", "H", "??x", "a"),
            [("F", ("G", V0, V1), V2), ("H", V2, V0), ("H", V0, V2)],
        )
    )

    # C1 -- plain repeated variable, live slots
    cs.append(
        Case(
            "C1-repeat-live",
            [("F", V0, V1), ("F", V0, V0)],
            [],
            [("p", "F", "x", "x")],
            ("p", "H", "x", "x"),
            [("F", V0, V1), ("F", V0, V0), ("H", V0, V0)],
        )
    )

    # C2 -- chain
    cs.append(
        Case(
            "C2-chain",
            [("F", V0, ("G", V0, V1))],
            [],
            [("p", "F", "a", "b"), ("b", "G", "c", "d")],
            ("p", "H", "c", "d"),
            [("F", V0, ("G", V0, V1)), ("H", V0, V1), ("H", V1, V0)],
        )
    )

    # C3 -- join on two shared variables
    cs.append(
        Case(
            "C3-join",
            [("F", V0, V1), ("G", V0, V1)],
            [],
            [("p", "F", "x", "y"), ("q", "G", "x", "y")],
            ("p", "H", "x", "y"),
            [("F", V0, V1), ("G", V0, V1), ("H", V0, V1)],
        )
    )

    # C4 -- symmetry: the two occurrences agree only through a swap
    cs.append(
        Case(
            "C4-symmetry",
            [("F", ("K", V0, V1), ("K", V1, V0))],
            [(("K", V0, V1), ("K", V1, V0))],
            [("p", "F", "x", "x")],
            ("p", "H", "x", "x"),
            [("F", ("K", V0, V1), ("K", V1, V0)), ("H", ("K", V0, V1), ("K", V0, V1))],
        )
    )

    # C5 -- R1: one redundant-slot node reached through two atoms
    cs.append(
        Case(
            "C5-redundant-same-node",
            [("Add", NUL, NUL)],
            [(("Sub", V0, V0), NUL)],
            [("p", "Add", "a", "b"), ("a", "Sub", "u", "u"), ("b", "Sub", "u", "u")],
            ("p", "H", "u", "u"),
            [("Add", NUL, NUL), ("H", V0, V0), NUL],
        )
    )

    # C6 -- R2: two different redundant-slot nodes, ?u forced across them
    cs.append(
        Case(
            "C6-redundant-two-nodes",
            [("Add", NUL, NUL)],
            [(("Sub", V0, V0), NUL), (("Sub2", V1, V1), NUL)],
            [("p", "Add", "a", "b"), ("a", "Sub", "u", "u"), ("b", "Sub2", "u", "u")],
            ("p", "H", "u", "u"),
            [("Add", NUL, NUL), ("H", V0, V0), NUL],
        )
    )

    # C7 -- same, but the two atoms use DISTINCT variables
    cs.append(
        Case(
            "C7-redundant-distinct-vars",
            [("Add", NUL, NUL)],
            [(("Sub", V0, V0), NUL), (("Sub2", V1, V1), NUL)],
            [("p", "Add", "a", "b"), ("a", "Sub", "u", "u"), ("b", "Sub2", "v", "v")],
            ("p", "H", "u", "v"),
            [("Add", NUL, NUL), ("H", V0, V0), ("H", V0, V1), NUL],
        )
    )

    # C8 -- a variable reached by two different paths, no redundancy
    cs.append(
        Case(
            "C8-two-paths",
            [("F", ("G", V0, V1), ("K", V0, V1))],
            [],
            [("p", "F", "a", "b"), ("a", "G", "x", "y"), ("b", "K", "x", "y")],
            ("p", "H", "x", "y"),
            [("F", ("G", V0, V1), ("K", V0, V1)), ("H", V0, V1), ("H", V1, V0)],
        )
    )

    # C9 -- redundancy meeting a live slot
    cs.append(
        Case(
            "C9-redundancy-and-live",
            [("F", V0, V1)],
            [(("G", V0, V1), ("G", V0, V2))],
            [("p", "F", "x", "y"), ("q", "G", "x", "y")],
            ("p", "H", "x", "y"),
            [("F", V0, V1), ("G", V0, V1), ("H", V0, V1)],
        )
    )

    # C10 -- three atoms, chain then join
    cs.append(
        Case(
            "C10-chain-then-join",
            [("F", V0, ("G", V0, V1)), ("K", V0, V0)],
            [],
            [("p", "F", "a", "b"), ("b", "G", "c", "d"), ("q", "K", "c", "a")],
            ("p", "H", "c", "d"),
            [("F", V0, ("G", V0, V1)), ("K", V0, V0), ("H", V0, V1)],
        )
    )

    # C11 -- the action must not assert an identity renaming (FIXED). A plain
    # `(union root built)` asserts an equation whose two renamings are the identity, and
    # the root's renaming here is {0->3, 2->2}, so it conflated slot 0 with slot 3. The
    # e-graph absorbed that as spurious redundancy -- `(Var 0)` went from one live slot
    # to none -- and child-update then emptied every edge, collapsing h(x,y) with
    # h(x,x). The reference refuses that by Def. 8's per-lookup injectivity, and pins it
    # as `regress::same_node_redundant_slots_stay_distinct`.
    #
    # A `BadEdge` width check does not catch it: by the end the children have gone
    # slotless too and the widths agree again.
    cs.append(
        Case(
            "C11-action-renamed-id-union",
            [NUL],
            [(("G", ("Sub2", NUL, NUL), ("Sub", V1, V0)), NUL), (("Add", ("K", V2, NUL), ("K", V0, NUL)), LEAF0)],
            [("x3", "K", "x1", "x2"), ("x6", "K", "x4", "x5"), ("x7", "Add", "x3", "x6")],
            ("x7", "H", "x3", "x6"),
            [
                NUL,
                ("G", ("Sub2", NUL, NUL), ("Sub", V1, V0)),
                ("Add", ("K", V2, NUL), ("K", V0, NUL)),
                ("H", V0, V1),
                ("H", V0, V0),
                NUL,
                LEAF0,
            ],
            rounds=6,
        )
    )

    # C12 -- regression for atom ordering, found by `fuzz 250 555` as fuzz61.
    #
    # As written, atom 2 shares no variable with atom 1, so nothing constrains
    # its mp and every slot it needs is minted. Atom 3 then shows that k2's slot
    # 0 and k1's slot 0 are the *same* slot of the h node, while the mint had
    # already sent them to different pattern slots -- the constraints conflict,
    # find-mapping fails, and a match the reference finds is lost.
    #
    # Reordering to atom 1, atom 3, atom 2 keeps every atom connected to the
    # prefix, so nothing is minted and the match comes back. `multi_ematch` never
    # had the problem: it keeps such a slot flexible and lets `unify` merge it.
    cs.append(
        Case(
            "C12-atom-order-must-stay-connected",
            [("H", ("K", V0, V0), ("K", V2, V0))],
            [],
            [("x3", "K", "x1", "x2"), ("x6", "K", "x4", "x5"), ("x7", "H", "x3", "x6")],
            ("x7", "H", "x2", "x4"),
            [("H", ("K", V0, V0), ("K", V2, V0)), ("H", V0, V1), ("H", V0, V0), NUL, LEAF0],
            rounds=6,
        )
    )

    # C13 -- a three-atom body mixing a binder, a chain and a join.
    #
    # Found as a witness that the first atom must not be a binder, back when the atom
    # order was a meaning rather than a hint. It is NOT that witness any more,
    # and probably never was a clean one: its discrimination came from a union
    # whose operand was a bare leaf, which the encoding cannot represent
    # faithfully. With the leaf replaced no ordering disagrees, and 200
    # binder-dense generated cases with the restriction lifted found nothing. The
    # restriction is kept as conservative -- a bound slot in the pattern's slot
    # space is a real oddity, see open question 3 -- but it is unwitnessed.
    cs.append(
        Case(
            "C13-binder-chain-and-join",
            [("H", ("K", V2, NUL), ("Lam", V0, V1))],
            [(("G", ("H", V2, NUL), ("Lam", V2, V1)), LEAF0), (("H", NUL, V2), ("Add", NUL, NUL))],
            [("x3", "K", "x1", "x2"), ("x5", "Lam", "$s5", "x4"), ("x6", "H", "x3", "x5")],
            ("x6", "H", "x4", "x4"),
            [
                ("H", ("K", V2, NUL), ("Lam", V0, V1)),
                ("G", ("H", V2, NUL), ("Lam", V2, V1)),
                ("H", NUL, V2),
                ("H", V0, V1),
                ("H", V0, V0),
                NUL,
                LEAF0,
            ],
            rounds=6,
        )
    )

    # ---- ported from the reference's own test suite (tests/multipat) ----------
    # A test that is not portable is left out rather than approximated here.

    # regress::same_node_redundant_slots_stay_distinct. Unioning f's two-slot
    # term into a slotless one makes both slots redundant. A pattern that would
    # have to identify them must not match; one that keeps them apart must.
    red = [(("F", V0, V1), NUL)]
    cs.append(
        Case(
            "P1a-redundant-slots-may-not-collapse",
            [NUL],
            red,
            [("p", "F", "a", "a")],
            ("p", "H", "a", "a"),
            [NUL, ("F", V0, V1), ("H", V0, V0), ("H", V0, V1)],
        )
    )
    cs.append(
        Case(
            "P1b-redundant-slots-kept-apart",
            [NUL],
            red,
            [("p", "F", "a", "b")],
            ("p", "H", "a", "b"),
            [NUL, ("F", V0, V1), ("H", V0, V0), ("H", V0, V1)],
        )
    )

    # regress::live_slots_of_one_class_stay_distinct. Same question with no
    # redundancy at all: a class's own live slots are distinct.
    cs.append(
        Case(
            "P2a-live-slots-may-not-collapse",
            [("K", V0, V1)],
            [],
            [("p", "K", "u", "u")],
            ("p", "H", "u", "u"),
            [("K", V0, V1), ("H", V0, V0), ("H", V0, V1)],
        )
    )
    cs.append(
        Case(
            "P2b-live-slots-kept-apart",
            [("K", V0, V1)],
            [],
            [("p", "K", "u", "v")],
            ("p", "H", "u", "v"),
            [("K", V0, V1), ("H", V0, V0), ("H", V0, V1)],
        )
    )

    # C14 -- regression for `union-id`, found by mutation testing after C11
    # stopped catching it. The action's root is a CHILD variable, so its renaming
    # is the stored edge {$0 -> $2} rather than the identity, and unioning
    # classes instead of invocations asserts a different equation.
    #
    # C11 was the original witness for this and no longer discriminates: after
    # minting changed to smallest-unused, C11's root renaming came out as the
    # identity, where the two spellings agree. Kept as a lesson -- a case written
    # against one policy can quietly stop testing what it was written for.
    cs.append(
        Case(
            "C14-action-root-with-a-nonidentity-renaming",
            [("F", V2, NUL), ("K", V2, NUL)],
            [(("G", V1, NUL), ("K", NUL, V0))],
            [("x3", "F", "x1", "x2")],
            ("x1", "H", "x3", "x2"),
            [("F", V2, NUL), ("K", V2, NUL), ("G", V1, NUL), ("H", V0, V1), ("H", V0, V0), NUL, LEAF0],
            rounds=6,
        )
    )

    # C15 -- an action whose variables are wider than their classes. Two unions through a
    # shared `sub($0,$0)` drive the `h` class's slot set down, so a renaming read off an `h`
    # node names a slot the class no longer has. Its root is a child variable and its other
    # child is a variable too, so narrowing only the root would not cover it.
    cs.append(
        Case(
            "C15-action-child-narrowed-to-its-class",
            [],
            [(("H", NUL, V0), ("Sub", V0, V0)), (("G", NUL, V2), ("Sub", V0, V0))],
            [("x3", "H", "x1", "x2")],
            ("x1", "H", "x2", "x1"),
            [("H", NUL, V0), ("G", NUL, V2), ("Sub", V0, V0), ("H", V0, V1), ("H", V0, V0), NUL, LEAF0],
            rounds=6,
        )
    )

    # C16 -- a SLOTLESS child leaves the pattern variable it binds unpinned, and the
    # action builds with it. `f($x,$x)` is unioned with itself at another slot, so its
    # class depends on nothing and `?a` can be the variable class at ANY slot -- which
    # is what the rule fires at, once per slot, dragging `g`'s own slot into redundancy
    # too. So the answer is a slotless class, `h` at $0 and `h` at $1 are one
    # invocation, and nothing names a node at either spelling in particular.
    #
    # It is the shape behind `redundancy-tests.egg`'s claim about a term the machinery
    # never stored: there the answer is `GG` and the claim is `(check (= g (GG $0)))`.
    cs.append(
        Case(
            "C16-slotless-child-unpins-the-action",
            [("F", V0, V0), ("F", V1, V1), ("G", ("F", V0, V0), V0)],
            [(("F", V0, V0), ("F", V1, V1))],
            [("p", "G", "c", "$0"), ("c", "F", "a", "a")],
            ("p", "H", "a", "a"),
            [("G", ("F", V0, V0), V0), ("H", V0, V0), ("H", V1, V1), ("F", V0, V0), LEAF0],
        )
    )

    # X1 -- migration must not truncate a child edge (FIXED). The encoding merged
    # h(x,y) with h(x,x), which the reference refuses: a node whose two slots are
    # distinct cannot represent h(x,x), by Def. 8's per-lookup injectivity.
    #
    # The action asserts `?x1 = h(?x3, ?x1)`, a node equal to its own child. Both sides
    # merge the h class into the variable class; only the reference still keeps h(x,x)
    # apart afterwards. `X2` is the minimal form and carries the mechanism.
    cs.append(
        Case(
            "X1-migration-must-not-truncate",
            [("Add", ("Sub2", V0, V0), NUL)],
            [(("H", V0, V2), NUL)],
            [("x3", "H", "x1", "x2")],
            ("x1", "H", "x3", "x1"),
            [("Add", ("Sub2", V0, V0), NUL), ("H", V0, V2), ("H", V0, V1), ("H", V0, V0), NUL, ("Sub", V0, V0)],
            rounds=6,
        )
    )

    # X2 -- the same bug at its smallest (FIXED), one term and no unions:
    #
    #     term   h(var $2, var $1)
    #     rule   ?c == (h ?a ?b)  =>  union ?a (h ?b ?c)
    #
    # CAUSE. The machinery's migration rule rewrote `e2 = f(m1*c1, m2*c2)` with
    # `e2 = m*e1` into `e1 = f((m^-1.m1)*c1, ...)`, and `compose` keeps only the keys
    # whose value lies in the left map's domain. Where m1 reaches outside im(m) -- when
    # e2 has a slot that is redundant in e1 -- the edge narrowed instead: here
    # m = {0->0} and m1 = {0->1} compose to the EMPTY map, and an empty edge to
    # (Var 0) asserts the variable class has no slots, after which every h(var, var)
    # collapses. The same dropped-slot bug as the `M3` case below, inside the machinery.
    #
    # Migration now declines when it would truncate -- sound but incomplete, like M3(b);
    # minting a fresh name would be the complete fix.
    cs.append(
        Case(
            "X2-migration-truncation-minimal",
            [("H", V2, V1)],
            [],
            [("x3", "H", "x1", "x2")],
            ("x1", "H", "x2", "x3"),
            [("H", V2, V1), ("H", V0, V1), ("H", V0, V0), NUL, ("Sub", V0, V0)],
            rounds=6,
        )
    )

    # K1 -- a bound slot in a condition, across disconnected atoms (FIXED):
    #
    #     terms  (lam $0 (var $2)),  (sub2 (var $0) (var $1))
    #     rule   r0 == (lam $s0 v0),  r1 == (sub2 a b),  free $s0 a
    #            =>  union v0 (h r1 r1)
    #
    # The atoms share no variable, so the condition is the only thing relating them --
    # a BOUND slot against a class in the other atom. The reference does not fire,
    # because a binder's bound slot is renamable and can always be moved off `a`'s
    # slots. The encoding did, and over-merged: refinement was offered every slot
    # in play as a merge candidate rather than only those the substitution carries, and
    # a pattern slot may be a merge TARGET. See frame refinement in the Rust query compiler.
    #
    # No condition, a condition on the binder's own body, and joining the two atoms all
    # agreed even before the fix, which is what isolated it.
    K1_ATOMS = [("r0", "Lam", "$s0", "v0"), ("r1", "Sub2", "a", "b")]
    cs.append(
        Case(
            "K1-bound-slot-condition-across-disconnected-atoms",
            [("Lam", V0, V2), ("Sub2", V0, V1)],
            [],
            K1_ATOMS,
            ("v0", "H", "r1", "r1"),
            [("Lam", V0, V2), ("Sub2", V0, V1), ("H", V0, V1), ("H", V0, V0), NUL],
            rounds=6,
            rules=[(K1_ATOMS, ("v0", "H", "r1", "r1"), [(True, "$s0", ["a"])])],
        )
    )

    # K2 -- a sibling link is not enough to order a chain by (FIXED). Reduced from
    # `fuzz538`, which the wider pattern generator reached.
    #
    #     term   (f (h null (var $2)) (f (var $2) null))
    #     union  that  =  (sub (var $0) (var $0))
    #     rule   x3 == (h x5 x2), x6 == (f x4 x5), x7 == (f x3 x6)
    #            =>  union x7 (h x2 x6)
    #
    # The encoding lost the match, so the node its own action builds was absent: ref 7
    # classes / 9 nodes against 7 / 8. The probe partition AGREED, which is why nothing
    # about the equalities looked wrong -- only a node was missing.
    #
    # ORDER DEPENDENT, which makes it a compiler bug with no reference needed: of the six
    # orders of these three atoms, the two that put the PARENT atom `x7` last lost the
    # match and the four that did not found it. `x5` is shared as a CHILD of two atoms,
    # and that constrains only the shared child's slots, leaving the rest of the second
    # atom's frame minted; a parent/child share is a stored EDGE and relates whole
    # frames. `connected_order` now prefers the latter.
    K2_ATOMS = [("x3", "H", "x5", "x2"), ("x6", "F", "x4", "x5"), ("x7", "F", "x3", "x6")]
    K2_LHS = ("F", ("H", NUL, V2), ("F", V2, NUL))
    cs.append(
        Case(
            "K2-sibling-link-is-not-an-order",
            [K2_LHS],
            [(K2_LHS, ("Sub", V0, V0))],
            K2_ATOMS,
            ("x7", "H", "x2", "x6"),
            [K2_LHS, ("Sub", V0, V0), ("H", V0, V1), ("H", V0, V0), NUL],
            rounds=6,
        )
    )

    # ---- branching in unify --------------------------------------------------
    # The reference's `unify` returns SEVERAL states when two invocations of one
    # class differ in two or more slots and more than one pairing is legal. A
    # primitive returns one answer and `find-mapping` takes the least, so this is
    # where the encoding could lose a match.
    #
    # `f(k(v0,v1), g(v0,v1))` unioned into `null` makes both of f's slots
    # redundant, so every lookup mints new names for them; two atoms over that
    # node see two different pairs, and `?x` must be unified across them with two
    # candidate pairings. The second children are bound to DIFFERENT variables so
    # which pairing was taken is visible in the action.
    #
    # Both sides agree here, so this does not force the difference -- see the
    # doc. Kept because it exercises the shape.
    BR = ("F", ("K", V0, V1), ("G", V0, V1))
    cs.append(
        Case(
            "U1-two-pairings-across-two-lookups",
            [BR],
            [(BR, NUL)],
            [("p", "F", "x", "y"), ("q", "F", "x", "z")],
            ("p", "H", "y", "z"),
            [BR, NUL, ("H", ("G", V0, V1), ("G", V0, V1)), ("H", ("G", V0, V1), ("G", V1, V0))],
        )
    )

    # ---- actions that equate two invocations ---------------------------------
    # `action <root> = <x> <x>` equates two pattern variables rather than building
    # a node, so both sides carry a renaming and neither need be the identity.

    # E1 -- equate the two CHILDREN of one node, so both are stored edges. This
    # asserts (var $1) = (var $2) -- the statement a top-level term cannot express
    # in the encoding, since a `U` value is a node rather than an invocation, but
    # an action can. It makes the variable class slotless.
    cs.append(
        Case(
            "E1-equate-two-children",
            [("F", V1, V2), ("F", V1, V1)],
            [],
            [("p", "F", "a", "b")],
            ("a", "=", "b", "b"),
            [("F", V1, V2), ("F", V1, V1), ("H", V0, V1), ("H", V0, V0)],
        )
    )

    # E2 -- the same, one atom deeper, through a chain.
    cs.append(
        Case(
            "E2-equate-through-a-chain",
            [("F", V0, ("K", V1, V2)), ("K", V1, V1)],
            [],
            [("p", "F", "a", "b"), ("b", "K", "c", "d")],
            ("c", "=", "d", "d"),
            [("F", V0, ("K", V1, V2)), ("K", V1, V1), ("K", V1, V2), ("H", V0, V0)],
        )
    )

    # E3 -- eta's shape: equate a binder with its own body, so one side is the
    # identity and the other carries the bound slot. Unsound as maths; the point
    # is that both sides derive the same thing from it.
    cs.append(
        Case(
            "E3-equate-binder-with-body",
            [("Lam", V0, V0), ("F", V0, V1)],
            [],
            [("p", "Lam", "$v", "b")],
            ("p", "=", "b", "b"),
            [("Lam", V0, V0), ("F", V0, V1), ("F", V0, V0), ("H", V0, V0)],
        )
    )

    # ---- symmetries ----------------------------------------------------------
    # The encoding keeps a class's symmetries as rows of `Symmetry`, and a
    # repeated variable is checked by computing the symmetry it would need
    # and looking it up. That only works if the stored set is CLOSED, not just a
    # set of generators: a lookup for a composite element has to succeed.
    #
    # `a` below has three slots and is given one 3-cycle. The parent then holds
    # `a` at the identity beside `a` at the cycle's SQUARE, which is never
    # unioned in, so `(f ?x ?x)` matches only if the square is stored too.
    A3 = ("K", ("G", V0, V1), V2)  # a, at the identity
    A3s = ("K", ("G", V1, V2), V0)  # a, under 0->1->2->0
    A3ss = ("K", ("G", V2, V0), V1)  # a, under the square of that
    cs.append(
        Case(
            "S1-symmetry-group-is-closed",
            [("F", A3, A3ss)],
            [(A3, A3s)],
            [("p", "F", "x", "x")],
            ("p", "H", "x", "x"),
            [("F", A3, A3ss), ("H", A3, A3), ("H", A3, A3s)],
        )
    )
    # control: without the 3-cycle there is no symmetry to find, so no match
    cs.append(
        Case(
            "S1b-no-symmetry-no-match",
            [("F", A3, A3ss)],
            [],
            [("p", "F", "x", "x")],
            ("p", "H", "x", "x"),
            [("F", A3, A3ss), ("H", A3, A3), ("H", A3, A3s)],
        )
    )

    # S2 -- symmetry and redundancy at once. A redundant slot is recorded as a
    # *partial* symmetry, so the rows are not a group but an inverse monoid. The
    # worry is a computed symmetry that came out short (composition truncates)
    # matching one of those partial maps and being accepted wrongly.
    # `a` keeps two live slots with a swap between them, and a third slot that a
    # union has made redundant. The parent holds `a` at the identity beside `a`
    # under the swap, so the match needs the real symmetry while a partial
    # symmetry is also present to be confused with it.
    Ar = ("K", ("G", V0, V1), V2)
    Arsw = ("K", ("G", V1, V0), V2)
    cs.append(
        Case(
            "S2-symmetry-beside-redundancy",
            [("F", Ar, Arsw)],
            [(Ar, Arsw), (Ar, ("K", ("G", V0, V1), NUL))],
            [("p", "F", "x", "x")],
            ("p", "H", "x", "x"),
            [("F", Ar, Arsw), ("H", Ar, Ar), ("H", Ar, Arsw)],
        )
    )

    # ---- binders -------------------------------------------------------------
    # The point of slotted e-graphs, and untested until now. `$v` is a slot
    # literal: the reference's `Bind` has no room for a pattern variable there.

    # B1 -- reading a binder's body, and chaining through it.
    cs.append(
        Case(
            "B1-binder-chain",
            [("Lam", V0, ("F", V0, V1))],
            [],
            [("p", "Lam", "$v", "b"), ("b", "F", "x", "y")],
            ("p", "H", "x", "y"),
            [("Lam", V0, ("F", V0, V1)), ("H", V0, V1), ("H", V0, V0)],
        )
    )

    # B2 -- alpha-equivalence: two spellings of the identity function are one
    # class, so a rule matching one must fire for both.
    cs.append(
        Case(
            "B2-alpha-equivalent-binders",
            [("Lam", V0, V0), ("Lam", V1, V1)],
            [],
            [("p", "Lam", "$v", "b")],
            ("p", "H", "b", "b"),
            [("Lam", V0, V0), ("Lam", V1, V1), ("H", V0, V0), ("H", V0, V1)],
        )
    )

    # B3 -- known_bugs::lambda_bug_reaches_the_goal_under_multipat. The pattern
    # writes `$x` for two binders that have nothing to do with each other. Each
    # equation looks its node up separately and may map that node's private bound
    # name to the same `$x` pattern coordinate, so the concrete names need not agree.
    cs.append(
        Case(
            "B3-same-slot-literal-two-binders",
            [("F", ("Lam", V0, V0), ("Lam", V0, V0))],
            [],
            [("p", "F", "a", "b"), ("a", "Lam", "$x", "c"), ("b", "Lam", "$x", "d")],
            ("p", "H", "c", "d"),
            [("F", ("Lam", V0, V0), ("Lam", V0, V0)), ("H", V0, V0), ("H", V0, V1)],
        )
    )

    # B4 -- the same, with the two binders over different bodies.
    cs.append(
        Case(
            "B4-same-slot-literal-different-bodies",
            [("F", ("Lam", V0, V0), ("Lam", V0, ("F", V0, V1)))],
            [],
            [("p", "F", "a", "b"), ("a", "Lam", "$x", "c"), ("b", "Lam", "$x", "d")],
            ("p", "H", "c", "d"),
            [("F", ("Lam", V0, V0), ("Lam", V0, ("F", V0, V1))), ("H", V0, V0), ("H", V0, V1)],
        )
    )

    # ---- shapes taught by egglog-experimental/tests/slotted/multipattern.egg ---------------------
    # That file states what a multipattern means, in the surface syntax, and checks it
    # with its own claims. Claims are not the reference, so each shape it teaches is
    # also asked of the reference here -- in the toy language, since that is what the
    # differential speaks. Names are `MP<n>`, and `isomorphism.py MP` runs just these.
    #
    # All five FIRE, which is what makes agreement evidence: blocking each rule's
    # pattern changes the encoding's graph, measured as (classes, nodes) fired vs
    # blocked -- MP1 (7,8)/(7,7), MP2 (4,5)/(5,5), MP3 (6,7)/(7,7), MP4 (7,8)/(7,7),
    # MP5 (6,7)/(7,7). Cases that deliberately do NOT fire exist here too and are
    # labelled as controls (`S1b`, `CD2`, `P1a`, `P2a`); these are not those.

    # MP1 -- a premise joined on a child the left-hand side binds, the premise being a
    # BINDER: "match `f`, and only where its first child is a lam". The shape of
    # multipattern.egg's guarded beta, without the `subst` that file's version uses --
    # the join is what is under test here, not the primitive.
    cs.append(
        Case(
            "MP1-premise-on-a-bound-child",
            [("F", ("Lam", V0, ("Add", V0, V0)), NUL)],
            [],
            [("p", "F", "a", "b"), ("a", "Lam", "$v", "body")],
            ("p", "H", "body", "b"),
            [("F", ("Lam", V0, ("Add", V0, V0)), NUL), ("H", V0, V0), ("H", V0, V1)],
        )
    )

    # MP2 -- TWO variables shared between the atoms, so both halves of the join have to
    # hold. One shared variable is `M3` above; this is the case where a second one can
    # refuse a match the first would allow.
    cs.append(
        Case(
            "MP2-join-on-two-variables",
            [("F", V0, V1), ("G", V0, V1), ("G", V1, V0)],
            [],
            [("p", "F", "x", "y"), ("q", "G", "x", "y")],
            ("p", "H", "x", "y"),
            [("F", V0, V1), ("G", V0, V1), ("G", V1, V0), ("H", V0, V1), ("H", V1, V0)],
        )
    )

    # MP3 -- four atoms, chained two deep, whose deepest variables are shared only with
    # each other and occur nowhere in the atom the action is rooted at.
    cs.append(
        Case(
            "MP3-four-atom-chain",
            [("K", ("Add", ("F", V0, V1), ("F", V0, V1)), NUL)],
            [],
            [("p", "K", "e", "z"), ("e", "Add", "l", "r"), ("l", "F", "a", "b"), ("r", "F", "a", "b")],
            ("p", "H", "a", "b"),
            [("K", ("Add", ("F", V0, V1), ("F", V0, V1)), NUL), ("H", V0, V1), ("H", V0, V0)],
        )
    )

    # MP4 -- a variable shared under TWO BINDERS. `B3` and `B4` above share a slot
    # LITERAL between two binders, which constrains nothing; this shares the BODY, which
    # does, and has to hold up to renaming rather than by pointer.
    cs.append(
        Case(
            "MP4-body-shared-under-two-binders",
            [("F", ("Lam", V0, ("G", V1, V1)), ("Lam", V2, ("G", V1, V1)))],
            [],
            [("p", "F", "a", "b"), ("a", "Lam", "$v", "body"), ("b", "Lam", "$w", "body")],
            ("p", "H", "body", "body"),
            [
                ("F", ("Lam", V0, ("G", V1, V1)), ("Lam", V2, ("G", V1, V1))),
                ("H", V0, V0),
                ("H", V0, V1),
            ],
        )
    )

    # MP5 -- THREE ATOMS SHARING NOTHING, with the action rooted at the one variable the
    # pattern constrains. The fuzzer reaches disconnected atoms only under `XDIFF_DISC`,
    # and every divergence it has found there roots its action at a disconnected variable
    # -- whose renaming is minted outright. This case separates the two: the pattern is a
    # cross product, and the action is not minted. If it agrees, disconnection alone is
    # not what those divergences are about.
    cs.append(
        Case(
            "MP5-three-unrelated-atoms",
            [("F", V0, V1), ("G", V0, NUL), ("K", V1, NUL)],
            [],
            [("p", "F", "x", "y"), ("d0", "G", "d0a", "d0b"), ("d1", "K", "d1a", "d1b")],
            ("p", "H", "x", "y"),
            [("F", V0, V1), ("G", V0, NUL), ("K", V1, NUL), ("H", V0, V1), ("H", V0, V0)],
        )
    )

    # ---- shapes taught by egglog-experimental/src/slotted/ENCODING.md --------------------
    # That file is the readable form of this compiler's recipe, so every shape it
    # teaches should be checked here too. The mapping is in its header; these two
    # were the shapes it had that nothing here covered.

    # M1 -- commutativity: one atom, no repeated variable, and an action that
    # rebuilds the node with its children swapped. The cheapest slotted rule
    # there is, and the only one whose action reuses both children in new
    # positions.
    cs.append(
        Case(
            "M1-commutativity",
            [("F", V0, V1)],
            [],
            [("p", "F", "a", "b")],
            ("p", "F", "b", "a"),
            [("F", V0, V1), ("F", V1, V0), ("H", V0, V1)],
        )
    )

    # M3 -- only ONE variable shared, across two different operators, so the
    # second atom's renaming is pinned on part of its node and must mint a name
    # for the rest. `U1` has this shape with one operator; two make the join
    # unambiguous.
    cs.append(
        Case(
            "M3-one-shared-var-two-ops",
            [("F", V0, V1), ("G", V0, V2)],
            [],
            [("p", "F", "x", "y"), ("q", "G", "x", "z")],
            ("p", "H", "y", "z"),
            [("F", V0, V1), ("G", V0, V2), ("H", V1, V2), ("H", V1, V1)],
        )
    )

    # ---- rule sets ----------------------------------------------------------
    # Until now every case ran a single rule. The paper's experiments are sets run
    # to a common fixpoint, so the rules interact: one produces what another
    # matches. `rules=` takes a list of (atoms, action).

    # MR1 -- a chain: f becomes g, then g becomes h with its children swapped, so
    # the answer needs both rules and the order they fire in must not matter.
    cs.append(
        Case(
            "MR1-rule-chain",
            [("F", V0, V1)],
            [],
            None,
            None,
            [("F", V0, V1), ("G", V0, V1), ("H", V0, V1), ("H", V1, V0)],
            rules=[([("p", "F", "a", "b")], ("p", "G", "a", "b")), ([("q", "G", "x", "y")], ("q", "H", "y", "x"))],
        )
    )

    # MR2 -- commutativity beside a renaming rule, so the second keeps feeding the
    # first new nodes to commute.
    cs.append(
        Case(
            "MR2-comm-plus-rename",
            [("Add", LEAF0, ("G", V1, V1))],
            [],
            None,
            None,
            [
                ("Add", LEAF0, ("G", V1, V1)),
                ("Add", ("G", V1, V1), LEAF0),
                ("Add", LEAF0, ("K", V1, V1)),
                ("K", V1, V1),
            ],
            rules=[([("p", "Add", "a", "b")], ("p", "Add", "b", "a")), ([("q", "G", "x", "y")], ("q", "K", "x", "y"))],
        )
    )

    # MR3 -- two rules over one shared operator, reaching the same class by
    # different routes.
    cs.append(
        Case(
            "MR3-two-routes",
            [("F", V0, V1), ("G", V0, V1)],
            [],
            None,
            None,
            [("F", V0, V1), ("G", V0, V1), ("H", V0, V1), ("H", V1, V0)],
            rules=[([("p", "F", "a", "b")], ("p", "H", "a", "b")), ([("q", "G", "x", "y")], ("q", "H", "y", "x"))],
        )
    )

    # ---- conditional rewrites -----------------------------------------------
    # The paper's rules that are guarded by a slot condition: `my_let_unused` and
    # `eta` need `$1 not in slots(?b)`, `let_lam_diff` needs it in, and `let_app`
    # needs it in either of two variables. A condition asks about the *slots* of what
    # a variable matched, which is why it cannot be folded into the pattern.

    # CD1 -- `notin`, with a match on each side of the condition: one body ignores
    # the bound slot and is equated with its binder, the other uses it and must not
    # be. Both are present so that dropping the condition changes the answer.
    cs.append(
        Case(
            "CD1-notin-decides",
            [("Lam", V0, ("G", V1, V1)), ("Lam", V0, ("G", V0, V0))],
            [],
            None,
            None,
            [("Lam", V0, ("G", V1, V1)), ("G", V1, V1), ("Lam", V0, ("G", V0, V0)), ("G", V0, V0)],
            rules=[([("p", "Lam", "$s", "b")], ("p", "=", "b", "b"), [(False, "$s", ["b"])])],
        )
    )

    # CD2 -- the same rule where the condition fails: the body does use the bound
    # slot, so nothing may fire.
    cs.append(
        Case(
            "CD2-notin-blocks",
            [("Lam", V0, ("G", V0, V0))],
            [],
            None,
            None,
            [("Lam", V0, ("G", V0, V0)), ("G", V0, V0), ("G", V1, V1), NUL],
            rules=[([("p", "Lam", "$s", "b")], ("p", "=", "b", "b"), [(False, "$s", ["b"])])],
        )
    )

    # CD3 -- `in`, the other direction.
    cs.append(
        Case(
            "CD3-in-fires",
            [("Lam", V0, ("G", V0, V0)), ("Lam", V0, ("G", V1, V1))],
            [],
            None,
            None,
            [("Lam", V0, ("G", V0, V0)), ("Lam", V0, ("G", V1, V1)), ("H", ("G", V0, V0), ("G", V0, V0)), NUL],
            rules=[([("p", "Lam", "$s", "b")], ("p", "H", "b", "b"), [(True, "$s", ["b"])])],
        )
    )

    # CD4 -- a disjunction over two variables, which needs the condition as a value
    # rather than a fact. Again one match satisfies it and one does not.
    cs.append(
        Case(
            "CD4-in-either-decides",
            [("Lam", V0, ("F", ("G", V0, V0), ("K", V1, V1))), ("Lam", V0, ("F", ("G", V1, V1), ("K", V1, V1)))],
            [],
            None,
            None,
            [
                ("Lam", V0, ("F", ("G", V0, V0), ("K", V1, V1))),
                ("H", ("G", V0, V0), ("K", V1, V1)),
                ("Lam", V0, ("F", ("G", V1, V1), ("K", V1, V1))),
                ("H", ("G", V1, V1), ("K", V1, V1)),
            ],
            rules=[([("p", "Lam", "$s", "x"), ("x", "F", "a", "b")], ("p", "H", "a", "b"), [(True, "$s", ["a", "b"])])],
        )
    )

    # ---- nested right-hand sides --------------------------------------------
    # Until now an action built one depth-1 node. The paper's `let_app` and the
    # associativity rules build a *tree*, so intermediate nodes have to be created
    # and referenced. An action is already in pattern slot space, so a built node's
    # edge to another built node is the identity on that child's slots.

    # NR1 -- one level of nesting: f(a,b) becomes h(g(a,b), b), so `g` must be built
    # before `h` can point at it.
    cs.append(
        Case(
            "NR1-nested-build",
            [("F", V0, V1)],
            [],
            None,
            None,
            [("F", V0, V1), ("H", ("G", V0, V1), V1), ("G", V0, V1), ("H", ("G", V1, V0), V0)],
            rules=[([("p", "F", "a", "b")], ("p", ("H", ("G", "a", "b"), "b")))],
        )
    )

    # NR2 -- two levels, and the same variable reused at different depths, which is
    # where a wrong slot set for an intermediate node would show up.
    cs.append(
        Case(
            "NR2-two-levels",
            [("F", V0, V1)],
            [],
            None,
            None,
            [("F", V0, V1), ("H", ("G", ("K", V0, V1), V0), V1), ("G", ("K", V0, V1), V0), ("K", V0, V1)],
            rules=[([("p", "F", "a", "b")], ("p", ("H", ("G", ("K", "a", "b"), "a"), "b")))],
        )
    )

    # NR3 -- associativity, the shape the paper's arith rules use: the right-hand
    # side regroups the same three variables.
    cs.append(
        Case(
            "NR3-assoc",
            [("Add", LEAF0, ("Add", ("G", V1, V1), ("K", V2, V2)))],
            [],
            None,
            None,
            [
                ("Add", LEAF0, ("Add", ("G", V1, V1), ("K", V2, V2))),
                ("Add", ("Add", LEAF0, ("G", V1, V1)), ("K", V2, V2)),
                ("Add", LEAF0, ("G", V1, V1)),
                NUL,
            ],
            rules=[([("p", "Add", "a", "x"), ("x", "Add", "b", "c")], ("p", ("Add", ("Add", "a", "b"), "c")))],
        )
    )

    # UN1 -- a shared variable reached through two REDUNDANT slots (FIXED).
    #
    #     terms  (k (g (f (var $0) null) null) (h (var $1) null))
    #     union  (g (f (var $0) null) null)  =  (g (f (var $5) null) null)   slot 0 redundant in g's class
    #     union  the k term  =  (k (g ...) (h (var $6) null))                slot 1 redundant in k's class
    #     rule   p == (k q d2), q == (g d1 n), d1 == (f x n2), d2 == (h x n3)
    #            =>  union p (sub d1 d2)
    #
    # Neither class carries the slot its node hands to `x`, so at each atom that
    # reaches `x` the slot is a placeholder, and the two placeholders meet at the
    # second occurrence. The reference's `unify` identifies them and the rule fires;
    # so does the frame's join, where the two occurrences simply fall into one class.
    # A solve that read its equations as facts about two distinct names declined, and
    # never fired. `UN2` below is the bound-slot version of the same shape.
    UN1_ATOMS = [("p", "K", "q", "d2"), ("q", "G", "d1", "n"), ("d1", "F", "x", "n2"), ("d2", "H", "x", "n3")]
    UN1_Q = ("G", ("F", V0, NUL), NUL)
    UN1_P = ("K", UN1_Q, ("H", V1, NUL))
    cs.append(
        Case(
            "UN1-shared-var-through-two-redundant-slots",
            [UN1_P],
            [(UN1_Q, ("G", ("F", ("var", 5), NUL), NUL)), (UN1_P, ("K", UN1_Q, ("H", ("var", 6), NUL)))],
            UN1_ATOMS,
            ("p", "Sub", "d1", "d2"),
            [UN1_P, ("Sub", ("F", V0, NUL), ("H", V1, NUL)), ("Sub", ("F", V0, NUL), ("H", V0, NUL)), NUL],
            rounds=6,
        )
    )

    # UN2 -- Rudi's `unify-redundant-and-symmetric-appid`: a shared body under two
    # BINDER chains, with the body's class carrying the swap symmetry.
    #
    #     term   (f L L)  where L = (lam $0 (lam $1 (f (var $0) (var $1))))
    #     union  (f (var $0) (var $1))  =  (f (var $1) (var $0))
    #     rule   out == (f l1 l2), l1 == (lam $x b1), b1 == (lam $y a), l2 == (lam $x b2), b2 == (lam $y a)
    #            =>  union out (sub (var $x) (var $x))
    #     rule   ... l2 == (lam $y b2), b2 == (lam $x a)  =>  union out (sub (var $x) (var $y))
    #
    # The second occurrence of `a` has to identify the second chain's bound slots with the
    # first chain's -- either straight or, through the symmetry, swapped. A binder is a
    # slot literal, rigid on both sides, so each pairing is its own rule: one literal in
    # both chains for the straight reading, the two literals swapped for the other. Both
    # fire, so `(sub x x)` and `(sub x y)` with two slots join `out`'s class; written with
    # two different literals per chain and no swap, nothing matches on either side.
    UN2_L = ("Lam", V0, ("Lam", V1, ("F", V0, V1)))
    UN2_TERMS = [("F", UN2_L, UN2_L)]
    UN2_UNIONS = [(("F", V0, V1), ("F", V1, V0))]
    UN2_PROBES = [("F", UN2_L, UN2_L), ("Sub", V0, V0), ("Sub", V0, V1), NUL]
    UN2_STRAIGHT = [
        ("out", "F", "l1", "l2"),
        ("l1", "Lam", "$x", "b1"),
        ("b1", "Lam", "$y", "a"),
        ("l2", "Lam", "$x", "b2"),
        ("b2", "Lam", "$y", "a"),
    ]
    UN2_SWAPPED = [
        ("out", "F", "l1", "l2"),
        ("l1", "Lam", "$x", "b1"),
        ("b1", "Lam", "$y", "a"),
        ("l2", "Lam", "$y", "b2"),
        ("b2", "Lam", "$x", "a"),
    ]
    cs.append(
        Case(
            "UN2-shared-body-under-two-binder-chains",
            UN2_TERMS,
            UN2_UNIONS,
            UN2_STRAIGHT,
            ("out", ("Sub", "$x", "$x")),
            UN2_PROBES,
            rounds=6,
            rules=[
                (UN2_STRAIGHT, ("out", ("Sub", "$x", "$x")), []),
                (UN2_SWAPPED, ("out", ("Sub", "$x", "$y")), []),
            ],
        )
    )

    # CLQ1 -- one variable in both columns of a node whose two slots differ, inside a
    # class that has made both slots redundant.
    #
    #     term   (g (f (var $0) (var $1)) null)
    #     union  (f (var $0) (var $1)) = null
    #     rule   r == (g n z), n == (f a a)   =>  union r (h a a)
    #
    # `a` is the variable class, one slot, reached at node slot 0 and again at slot 1 of
    # the `f` node; the two occurrences would have to be one invocation, which identifies
    # two slots of one e-node, and the reference's disjointness constraint refuses the
    # match. The frame's node clique refuses it the same way. The `f` class is slotless
    # so that nothing else notices: with the clique dropped the identified slots are
    # redundant in `r`, the action goes through, and `(h a a)` joins `r`'s class --
    # which this case must reject.
    cs.append(
        Case(
            "CLQ1-one-variable-two-node-slots",
            [("G", ("F", V0, V1), NUL)],
            [(("F", V0, V1), NUL)],
            [("r", "G", "n", "z"), ("n", "F", "a", "a")],
            ("r", "H", "a", "a"),
            [("G", ("F", V0, V1), NUL), ("H", V0, V0), NUL],
            rounds=3,
        )
    )

    # LIT1 -- two DIFFERENT slot literals in binder columns, sharing a body that uses the
    # bound variable (FIXED). Found by the deep campaign, seed 1006 case 37.
    #
    #     term   (lam $2 (var $2))
    #     rule   r0 == (lam $s0 b), r1 == (lam $s1 b)   =>  union b (h r0 r0)
    #
    # Both atoms match the identity lambda. `$s0` and `$s1` are two pattern slots, and
    # the reference never identifies two of those, so `b` cannot be one term in both
    # atoms and the rule does not fire. The encoding solves a literal as a name and used
    # to read `$s1` off the slot the shared body had already pinned; the rule fired,
    # unioned the variable class with a slotless term, and every variable became one.
    # The frame's literal clique states that a rule's different literals are different
    # slots. With ONE literal in
    # both binders the two sides always agreed: that spelling names both bound slots.
    cs.append(
        Case(
            "LIT1-two-literals-one-bound-slot",
            [("Lam", V2, V2)],
            [],
            [("r0", "Lam", "$s0", "b"), ("r1", "Lam", "$s1", "b")],
            ("b", "H", "r0", "r0"),
            [("Lam", V2, V2), ("H", V0, V1), ("H", V0, V0), NUL],
            rounds=4,
        )
    )

    # CAP1 -- a binder the right-hand side rebinds over a variable matched outside it,
    # with the guard the rule owes (FIXED, in the rule). Reduced from the paper's array
    # study at zero parameters, where an unguarded `let-lam-diff` did this six rounds in
    # and every class became one.
    #
    #     term   (f (lam $0 (sub (var $0) (var $0))) (var $2))
    #     rule   p == (f l e), l == (lam $y body), $y not free in e
    #            =>  union p (lam $y (f body e))
    #
    # The lambda's bound slot may be read as `$2`, a fine alpha-variant of the term and
    # a reading both matchers offer on purpose. The right-hand side then rebinds `$y`
    # over `e`, and that reading builds the closed `(lam $2 (f (sub $2 $2) $2))`,
    # capturing `e`. So the rule says `e` and `$y` do not alias, and only the plain
    # reading fires; `checks/language.py guards` holds the rule libraries to this. The
    # probes ask for the sound result, the captured one, and a term the union must not
    # reach. `CAP0` is the same rule without its guard.
    CAP_TERM = ("F", ("Lam", V0, ("Sub", V0, V0)), V2)
    CAP_ATOMS = [("p", "F", "l", "e"), ("l", "Lam", "$y", "body")]
    CAP_PROBES = [
        CAP_TERM,
        ("Lam", V1, ("F", ("Sub", V1, V1), V2)),
        ("Lam", V1, ("F", ("Sub", V1, V1), V1)),
        NUL,
    ]
    cs.append(
        Case(
            "CAP1-rhs-binder-over-outside-variable-guarded",
            [CAP_TERM],
            [],
            CAP_ATOMS,
            ("p", ("Lam", "$y", ("F", "body", "e"))),
            CAP_PROBES,
            rounds=3,
            rules=[(CAP_ATOMS, ("p", ("Lam", "$y", ("F", "body", "e"))), [(False, "$y", ["e"])])],
        )
    )

    # CAP0 -- the same rule with no guard: the aliasing reading fires on BOTH sides and
    # the captured term joins the class. Not a divergence -- the two agree -- but the
    # statement of what an unguarded rule means here, kept beside the guarded one.
    cs.append(
        Case(
            "CAP0-rhs-binder-over-outside-variable-unguarded",
            [CAP_TERM],
            [],
            CAP_ATOMS,
            ("p", ("Lam", "$y", ("F", "body", "e"))),
            CAP_PROBES,
            rounds=3,
        )
    )

    return cs
