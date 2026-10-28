#!/usr/bin/env python3
"""SDQL differential regression cases using the shared test runner and graph checker.

Rules come from `languages/sdql-rules.egg`: Rust compiles them for the encoding,
and `reference.py` translates them to the reference's MultiPattern syntax.
`check-reference-rules.py` separately checks the library against the pinned paper
artifact. The cases below cover selected rules, guards, binding, and substitution;
they do not provide a firing witness for every library rule.

The known-encoding-limitations mode pins the remaining scope-erasing flattening
divergence separately from the ordinary agreement suite.

Usage:
    ./xsdql.py                partition, expected-result, and slot-renaming checks
    ./xsdql.py iso [prefix]   the stronger check: a witnessed isomorphism of the two
                              final e-graphs, via `isomorphism.py`
    ./xsdql.py show <name>    one case's spec, its egg program, and both answers
    ./xsdql.py list           the cases and the rules they exercise
    ./xsdql.py known-encoding-limitations
                              executable witnesses for known encoding gaps
"""

import os
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from slotted import reference as syntax  # noqa: E402
from slotted import test_program as driver  # noqa: E402

RUN_TIMEOUT = int(os.environ.get("XSDQL_TIMEOUT", "180"))


# The source-level regression fixtures.  Python supplies the differential-test
# orchestration and expected partitions, but the terms and the two scope-sensitive
# patterns below come from these runnable `.egg` files rather than being restated as
# Python tuples.
BETA_FIXTURE = ROOT / "egglog-experimental" / "tests" / "slotted" / "sdql-beta.egg"
BINDER_FIXTURE = ROOT / "egglog-experimental" / "tests" / "slotted" / "sdql-binders.egg"


# Constructor signatures and reference names are data, shared with evaluation.
# sdql.ref documents the reference's `let` tag and symbol-payload naming constraints.
SDQL_SRC = ROOT / "egglog-experimental" / "tests" / "slotted" / "languages" / "sdql.egg"
SDQL_SRC_RULES = ROOT / "egglog-experimental" / "tests" / "slotted" / "languages" / "sdql-rules.egg"
LANG = syntax.language(SDQL_SRC, SDQL_SRC.with_suffix(".ref"))
sexpr, shift = LANG.sexpr, LANG.shift
RULES = driver.load_rules(SDQL_SRC_RULES, LANG)
SOURCE = syntax.Source(SDQL_SRC_RULES)

# Substitution fixtures and the library must exercise the same beta rewrite.
_beta_src, _beta_forms = driver.fixture_rewrites(BETA_FIXTURE, "beta")
BETA_RULE = driver.Rule(_beta_src, LANG, _beta_forms["beta"])
if BETA_RULE.spec_lines() != RULES["beta"].spec_lines():
    raise ValueError(f"{BETA_FIXTURE.name}: beta no longer matches {SDQL_SRC_RULES.name}")


# ---------------------------------------------------------------------- the cases
class Case:
    lang = LANG

    def egg_program(self, *, mult):
        return egg_program(self, mult=mult)

    def __init__(
        self,
        name,
        rule,
        terms,
        probes,
        want,
        rounds=3,
        ref_want=None,
        why=None,
        unions=(),
        ref_rule=None,
    ):
        self.name = name
        self.rule = rule
        self.terms = list(terms)
        self.unions = list(unions)
        self.probes = list(probes)
        # the partition both sides must report, so a case that agrees on a
        # collapsed or empty answer still fails
        self.want = want
        self.rounds = rounds
        # A RECORDED DIVERGENCE: the reference is expected to answer `ref_want`
        # while the encoding answers `want`, for the reason in `why`. Both sides
        # are pinned, so either one moving is still a failure -- this documents a
        # known difference, it does not stop comparing.
        self.ref_want = ref_want
        self.why = why
        assert (ref_want is None) == (why is None), "a divergence needs its reason"
        # A different reference rule is allowed only for an explicitly pinned limitation.
        assert ref_rule is None or ref_want is not None
        self.ref_rule = ref_rule

    def spec(self, with_rule=True):
        rule = self.ref_rule or self.rule
        return driver.reference_spec(
            LANG,
            self.rounds,
            self.terms,
            self.unions,
            rule.spec_lines() if with_rule else [],
            self.probes,
        )

    def shifted(self, k):
        return Case(
            self.name + f"+{k}",
            self.rule,
            [shift(t, k) for t in self.terms],
            [shift(t, k) for t in self.probes],
            self.want,
            self.rounds,
            self.ref_want,
            self.why,
            unions=[(shift(a, k), shift(b, k)) for a, b in self.unions],
            ref_rule=self.ref_rule,
        )


def egg_program(case, with_rule=True, mult=3):
    rules = [case.rule.source()] if with_rule else []
    return driver.program("sdql", LANG, rules, case.terms, case.unions, case.probes, case.rounds * mult)


def run_reference(case, with_rule=True):
    return driver.run_reference(case.spec(with_rule), RUN_TIMEOUT)


def run_encoding(case, with_rule=True, keep=None, mult=3):
    return driver.run_encoding(egg_program(case, with_rule, mult), len(case.probes), RUN_TIMEOUT, keep=keep)


def check_case(case, shift_check=True):
    """Compare both sides. Returns a list of failure strings."""
    fails = []
    # 1. the machinery alone: with no rule the two must already agree, so a
    #    difference below is attributable to the rule and not to the encoding.
    rs, rv = run_reference(case, with_rule=False)
    es, ev = run_encoding(case, with_rule=False)
    if rs != "OK" or es != "OK":
        return [f"{case.name}: baseline ref={rs}:{rv} enc={es}:{ev}"]
    if rv != ev:
        return [f"{case.name}: BASELINE differs (machinery, not the rule)\n    ref {rv}\n    enc {ev}"]
    baseline = rv

    rs, rv = run_reference(case)
    es, ev = run_encoding(case)
    if rs == "TIMEOUT" or es == "TIMEOUT":
        return [f"{case.name}: timeout ref={rs} enc={es}"]
    if rs == "UNSATURATED":
        fails.append(f"{case.name}: reference hit its round cap (bounded comparison)")
    elif rs != "OK":
        return [f"{case.name}: reference crashed: {rv}"]
    if es != "OK":
        return fails + [f"{case.name}: encoding crashed: {ev}"]
    recorded = case.ref_want is not None
    if rv != ev and not (recorded and rv == case.ref_want and ev == case.want):
        fails.append(f"{case.name}: MISMATCH vs reference\n    ref {rv}\n    enc {ev}")
    if recorded and rv == ev:
        fails.append(f"{case.name}: the recorded divergence is GONE -- both sides now say {rv}")
    if case.want is not None and ev != case.want and not fails:
        fails.append(
            f"{case.name}: the encoding agrees, but not on the expected partition\n    want {case.want}\n    got  {ev}"
        )
    # A case whose rule never changed the partition compared the machinery, not the
    # rule -- and a "blocked" case that changed it never blocked anything.
    fired = ev != baseline
    if not fails and (case.want == FIRED) != fired:
        fails.append(
            f"{case.name}: the rule "
            f"{'fired' if fired else 'did not fire'}, which is not what "
            f"the case tests\n    baseline  {baseline}\n"
            f"    with rule {rv}"
        )

    # 2. the encoding at twice the steps: a moving answer means it had not settled,
    #    so the comparison was between two different amounts of work.
    if not fails:
        ds, dv = run_encoding(case, mult=6)
        if ds == "OK" and dv != ev:
            fails.append(
                f"{case.name}: encoding not settled or nondeterministic\n"
                f"    {case.rounds * 3} steps {ev}\n"
                f"    {case.rounds * 6} steps {dv}"
            )

    # 3. slot-renaming invariance, per side.
    if shift_check and not fails:
        sh = case.shifted(40)
        xs, xv = run_reference(sh)
        ys, yv = run_encoding(sh)
        if xs in ("OK", "UNSATURATED") and xv != rv:
            fails.append(f"{case.name}: REFERENCE not slot-renaming invariant\n    {rv}\n    {xv}")
        if ys == "OK" and yv != ev:
            fails.append(f"{case.name}: ENCODING not slot-renaming invariant\n    {ev}\n    {yv}")
    if not fails:
        tag = f"  DIVERGES, ref {rv}" if recorded else ""
        print(f"  ok  {case.name:<24} {'fired' if fired else 'NO-OP':<6} {ev}{tag}")
    return fails


# --------------------------------------------------------------------- shorthands
def V(n):
    return ("var", n)


FIRED = "[0,1][2] missing[[]]"
BLOCKED = "[0][1][2] missing[[]]"


def compiler_regression_cases():
    """Synthetic MultiPatterns that directly exercise the generic compiler.

    They use SDQL constructors only as a convenient shared language.  Keeping the
    generated source rewrite on the encoding side makes these positive tests of
    compiler behavior rather than generated-artifact coverage.
    """
    out = []

    # An ordinary-child slot literal is flattened from `(var $x)`. The reference
    # carries that variable in its substitution, even after the surrounding class
    # has made the slot redundant, so final refinement may merge another carried
    # slot onto `$x`. The side condition makes that alternative load-bearing.
    atoms = [
        ("?r", "Add", [("sl", "$x"), ("pv", "b0")], []),
        ("?r", "Mult", [("pv", "a1"), ("pv", "b1")], []),
        ("?r", "Sub", [("pv", "a2"), ("pv", "b2")], []),
    ]
    conds = [(True, "$x", ["a2"])]
    multi_egg = driver.rewrite(
        LANG,
        atoms,
        "?r",
        ("Unique", ("pv", "a2")),
        conds=conds,
        name="compiler-carried-slot-refinement",
    )
    multi_rule = driver.Rule(SOURCE, LANG, syntax.parse(multi_egg)[0])
    n = ("Num", 99)
    redundant_nodes = [
        ("Add", V(0), V(1)),
        ("Mult", V(2), V(3)),
        ("Sub", V(4), V(5)),
    ]
    out.append(
        Case(
            "carried-slot-refinement",
            multi_rule,
            redundant_nodes,
            [n, ("Unique", V(4)), ("Null",)],
            FIRED,
            rounds=2,
            unions=[(node, n) for node in redundant_nodes],
        )
    )

    # Repeated occurrences of one pvar independently unify modulo the class's
    # symmetry group. The middle occurrence needs the swap, while the first and
    # third need the identity; sharing one symmetry witness cannot match this row.
    a = ("Add", V(0), V(1))
    swapped = ("Add", V(1), V(0))
    symmetry_source = ("Add", V(2), V(3))
    symmetry_target = ("Add", V(3), V(2))
    repeated = ("SubArray", a, swapped, a)
    atoms = [("?r", "SubArray", [("pv", "x"), ("pv", "x"), ("pv", "x")], [])]
    repeated_egg = driver.rewrite(
        LANG,
        atoms,
        "?r",
        ("Unique", ("pv", "x")),
        name="compiler-repeated-pvar-symmetry",
    )
    repeated_rule = driver.Rule(SOURCE, LANG, syntax.parse(repeated_egg)[0])
    out.append(
        Case(
            "repeated-pvar-symmetry",
            repeated_rule,
            [repeated],
            [repeated, ("Unique", a), ("Null",)],
            FIRED,
            rounds=2,
            unions=[(symmetry_source, symmetry_target)],
        )
    )
    return out


def cases():
    out = []

    # --- Repeated names in nested Bind layers mean lexical shadowing, not one
    # simultaneous binder. The innermost layer captures the body occurrence.  This
    # baseline comparison caught the flattened encoding leaving the private binder
    # columns identified with each other.
    out.append(
        Case(
            "nested-binder-shadowing",
            RULES["eq-comm"],
            [],
            [
                ("Sum", ("Null",), 5, 5, V(5)),
                ("Sum", ("Null",), 6, 7, V(7)),
                ("Sum", ("Null",), 6, 7, V(6)),
                ("Merge", ("Null",), ("Null",), 5, 5, 5, V(5)),
                ("Merge", ("Null",), ("Null",), 6, 7, 8, V(8)),
                ("Merge", ("Null",), ("Null",), 6, 7, 8, V(6)),
            ],
            "[0,1][2][3,4][5] missing[[]]",
        )
    )

    # --- a plain binary rule, and the symmetry it puts on the class.
    # The second child is a payload leaf, not a second variable: `(eq (var $1)
    # (var $2))` and `(eq (var $2) (var $1))` are ONE class before any rule runs,
    # since swapping two free slots is a renaming and the partition compares class
    # identity. That case tests nothing, so the children are made distinguishable.
    out.append(
        Case(
            "eq-comm",
            RULES["eq-comm"],
            [("Equality", V(1), ("Num", 5))],
            [("Equality", V(1), ("Num", 5)), ("Equality", ("Num", 5), V(1)), ("Get", V(1), ("Num", 5))],
            FIRED,
        )
    )

    # --- a payload literal the RIGHT-hand side builds: `(binop mult ?a ?b)`
    out.append(
        Case(
            "mult-app1",
            RULES["mult-app1"],
            [("Mult", V(1), V(2))],
            [("Mult", V(1), V(2)), ("Binop", ("Symbol", "mult"), V(1), V(2)), ("Binop", ("Symbol", "add"), V(1), V(2))],
            FIRED,
        )
    )

    # --- the payload symbol `add`, which is also an operator tag in `xmulti`'s
    # array language: without the symbol prefix in sdql.ref the reference cannot parse this rule.
    out.append(
        Case(
            "add-app1",
            RULES["add-app1"],
            [("Add", V(1), V(2))],
            [("Add", V(1), V(2)), ("Binop", ("Symbol", "add"), V(1), V(2)), ("Binop", ("Symbol", "sub"), V(1), V(2))],
            FIRED,
        )
    )

    # --- a payload literal in a LEFT-hand child position, on a 3-child node
    out.append(
        Case(
            "mult-app2",
            RULES["mult-app2"],
            [("Binop", ("Symbol", "mult"), V(1), V(2))],
            [("Binop", ("Symbol", "mult"), V(1), V(2)), ("Mult", V(1), V(2)), ("Binop", ("Symbol", "add"), V(1), V(2))],
            FIRED,
        )
    )

    # --- and the same rule blocked by the payload: `add` is not `mult`.
    # The control cannot be the `mult` binop -- the rule fires on that one and it
    # would land in probe 1's class.
    out.append(
        Case(
            "mult-app2-blocked",
            RULES["mult-app2"],
            [("Binop", ("Symbol", "add"), V(1), V(2))],
            [("Binop", ("Symbol", "add"), V(1), V(2)), ("Mult", V(1), V(2)), ("Binop", ("Symbol", "sub"), V(1), V(2))],
            BLOCKED,
        )
    )

    # --- a `Num` literal in a left-hand child position, firing and blocked
    out.append(
        Case(
            "add-zero",
            RULES["add-zero"],
            [("Add", V(1), ("Num", 0))],
            [("Add", V(1), ("Num", 0)), V(1), ("Add", V(1), ("Num", 1))],
            FIRED,
        )
    )
    out.append(
        Case(
            "add-zero-blocked",
            RULES["add-zero"],
            [("Add", V(1), ("Num", 1))],
            [("Add", V(1), ("Num", 1)), V(1), ("Add", V(1), ("Num", 2))],
            BLOCKED,
        )
    )

    # --- arity 1, and a `Symbol` the right-hand side builds
    out.append(
        Case(
            "unique-app1",
            RULES["unique-app1"],
            [("Unique", V(1))],
            [("Unique", V(1)), ("App", ("Symbol", "uniquef"), V(1)), ("App", ("Symbol", "uniquefx"), V(1))],
            FIRED,
        )
    )

    # --- a nested left-hand side and a nested right-hand side over a `Num`
    out.append(
        Case(
            "get-range",
            RULES["get-range"],
            [("Get", ("Range", V(3), V(4)), V(7))],
            [
                ("Get", ("Range", V(3), V(4)), V(7)),
                ("Add", V(7), ("Sub", V(3), ("Num", 1))),
                ("Add", V(7), ("Sub", ("Num", 1), V(3))),
            ],
            FIRED,
        )
    )

    # --- a binder on the left AND two on the right, with `?f` over a payload class
    out.append(
        Case(
            "let-binop3",
            RULES["let-binop3"],
            [("Let", V(1), 2, ("Binop", ("Symbol", "mult"), V(2), V(3)))],
            [
                ("Let", V(1), 2, ("Binop", ("Symbol", "mult"), V(2), V(3))),
                ("Binop", ("Symbol", "mult"), ("Let", V(1), 2, V(2)), ("Let", V(1), 2, V(3))),
                ("Binop", ("Symbol", "add"), ("Let", V(1), 2, V(2)), ("Let", V(1), 2, V(3))),
            ],
            FIRED,
        )
    )

    # --- `let-binop4`: `$x` is written for two sibling binders. MultiPattern has one
    # global pattern frame, but each atom may map its alpha-renameable private binder
    # name to that same `$x` coordinate; the concrete names need not agree. This is the
    # pattern language the encoding compiles and the reference oracle runs. The second
    # case makes the no-capture consequence observable rather than relying only on the
    # positive firing case.
    out.append(
        Case(
            "let-binop4-fires",
            RULES["let-binop4"],
            [("Binop", ("Symbol", "mult"), ("Let", V(1), 2, V(2)), ("Let", V(1), 2, V(1)))],
            [
                ("Binop", ("Symbol", "mult"), ("Let", V(1), 2, V(2)), ("Let", V(1), 2, V(1))),
                ("Let", V(1), 2, ("Binop", ("Symbol", "mult"), V(2), V(1))),
                ("Let", V(1), 2, ("Binop", ("Symbol", "add"), V(2), V(1))),
            ],
            FIRED,
        )
    )
    # The capture case: the FIRST `let` binds $2 and the SECOND one's body has $2
    # FREE. Identifying the two binders on the name $2 would capture it and give
    # `mult (var $1) (var $1)`; a name free in neither body is sound. Probe 1 is the
    # sound answer and probe 2 is the captured one, so the partition says which the
    # encoding picked -- and it picks the sound one, because the minted binder avoids
    # the accumulated slots.
    out.append(
        Case(
            "let-binop4-no-capture",
            RULES["let-binop4"],
            [("Binop", ("Symbol", "mult"), ("Let", V(1), 2, V(2)), ("Let", V(1), 3, V(2)))],
            [
                ("Binop", ("Symbol", "mult"), ("Let", V(1), 2, V(2)), ("Let", V(1), 3, V(2))),
                ("Let", V(1), 9, ("Binop", ("Symbol", "mult"), V(9), V(2))),
                ("Let", V(1), 2, ("Binop", ("Symbol", "mult"), V(2), V(2))),
            ],
            FIRED,
        )
    )

    # --- `Sum`: two binders on one node, and slot literals in child positions.
    # The control swaps the two `(var $)` children, which is a DIFFERENT term:
    # the bound slots are ordered, so no renaming turns one into the other.
    out.append(
        Case(
            "sum-sing",
            RULES["sum-sing"],
            [("Sum", V(9), 5, 6, ("Sing", V(5), V(6)))],
            [("Sum", V(9), 5, 6, ("Sing", V(5), V(6))), V(9), ("Sum", V(9), 5, 6, ("Sing", V(6), V(5)))],
            FIRED,
        )
    )

    # --- a right-hand side that builds a `Sum`, i.e. re-binds its two slots
    out.append(
        Case(
            "sum-fact-inv-1",
            RULES["sum-fact-inv-1"],
            [("Mult", V(7), ("Sum", V(1), 2, 3, ("Get", V(2), V(3))))],
            [
                ("Mult", V(7), ("Sum", V(1), 2, 3, ("Get", V(2), V(3)))),
                ("Sum", V(1), 2, 3, ("Mult", V(7), ("Get", V(2), V(3)))),
                ("Sum", V(1), 2, 3, ("Mult", ("Get", V(2), V(3)), V(7))),
            ],
            FIRED,
        )
    )

    # --- `Merge`: three binders on one node, six children, and a built `let`
    lhs = ("Sum", V(1), 2, 3, ("Sum", V(4), 5, 6, ("IfThen", ("Equality", V(3), V(6)), ("Get", V(2), V(5)))))
    rhs = ("Merge", V(1), V(4), 2, 5, 3, ("Let", V(3), 6, ("Get", V(2), V(5))))
    # NOT the two ranges swapped: that is the free-slot renaming $1 <-> $4 of
    # probe 1, i.e. the same class. The two key binders swapped reorders the bound
    # slots against the body, which no renaming undoes.
    ctl = ("Merge", V(1), V(4), 5, 2, 3, ("Let", V(3), 6, ("Get", V(2), V(5))))
    out.append(Case("sum-merge", RULES["sum-merge"], [lhs], [lhs, rhs, ctl], FIRED))

    # --- a slot-conditional rule, firing: `$x`,`$y` are not in `?e1`'s slots
    out.append(
        Case(
            "sum-fact-1-fires",
            RULES["sum-fact-1"],
            [("Sum", V(1), 2, 3, ("Mult", V(7), V(2)))],
            [
                ("Sum", V(1), 2, 3, ("Mult", V(7), V(2))),
                ("Mult", V(7), ("Sum", V(1), 2, 3, V(2))),
                ("Mult", V(2), ("Sum", V(1), 2, 3, V(7))),
            ],
            FIRED,
        )
    )

    # --- and blocked: `?e1` is the first bound slot's variable
    out.append(
        Case(
            "sum-fact-1-blocked",
            RULES["sum-fact-1"],
            [("Sum", V(1), 2, 3, ("Mult", V(2), V(7)))],
            [
                ("Sum", V(1), 2, 3, ("Mult", V(2), V(7))),
                ("Mult", V(2), ("Sum", V(1), 2, 3, V(7))),
                ("Mult", V(7), ("Sum", V(1), 2, 3, V(2))),
            ],
            BLOCKED,
        )
    )

    # --- blocked on the SECOND bound slot, which is the one an off-by-one misses
    out.append(
        Case(
            "sum-fact-1-blocked-y",
            RULES["sum-fact-1"],
            [("Sum", V(1), 2, 3, ("Mult", V(3), V(7)))],
            [
                ("Sum", V(1), 2, 3, ("Mult", V(3), V(7))),
                ("Mult", V(3), ("Sum", V(1), 2, 3, V(7))),
                ("Mult", V(7), ("Sum", V(1), 2, 3, V(3))),
            ],
            BLOCKED,
        )
    )

    out.extend(binder_collision_cases())
    out.extend(compiler_regression_cases())
    out.extend(substitution_regression_cases())
    return out


def binder_collision_cases():
    """Legitimate binder collisions repaired in the pinned reference.

    In each term the bound name is also free in an uncovered column. `Bind<T>` scopes
    only over the body, so the free occurrence must remain.  The encoding is checked
    on a parent pair that would collapse if it lost that occurrence. The former
    reference implementation overwrote and then removed the outer/free weak-shape
    mapping; these cases now run as ordinary comparisons so a regression fails the
    main differential suite.
    """
    shapes = {
        "let": ("Let", V(5), 5, ("Num", 0)),
        "sum": ("Sum", V(5), 5, 6, ("Num", 0)),
        "merge": ("Merge", V(5), ("Num", 0), 5, 6, 7, ("Num", 0)),
    }
    return [
        Case(
            f"{name}-free-uncovered",
            RULES["eq-comm"],
            [],
            [("App", term, V(5)), ("App", term, V(8))],
            "[0][1] missing[[]]",
        )
        for name, term in shapes.items()
    ]


def substitution_regression_cases():
    """Binder-aware substitution cases read from the runnable source fixture."""
    ref_subst = "[0,1][2] missing[[]]"

    # Capture avoidance must refresh the lambda's private slot, not the free slot in
    # the substituted term.
    _, capture, capture_unions = driver.fixture_block(BETA_FIXTURE, "e")
    out = [
        Case(
            "subst-capture",
            BETA_RULE,
            [capture["e"]],
            [capture[name] for name in ("e", "capture-avoiding", "captured")],
            ref_subst,
            rounds=2,
            unions=capture_unions,
        )
    ]

    # A nested binder for the same slot shadows the outer substitution target. The
    # primitive must leave the covered subtree alone.
    _, shadow, shadow_unions = driver.fixture_block(BETA_FIXTURE, "f")
    out.append(
        Case(
            "subst-shadowed-target",
            BETA_RULE,
            [shadow["f"]],
            [shadow[name] for name in ("f", "shadowed", "pierced")],
            FIRED,
            rounds=2,
            unions=shadow_unions,
        )
    )

    # The two bodies are one e-class. The pinned oracle's SynExprSubst keeps the source
    # body, and the reference's ExtractionSubst would choose it too: a Bind slot is
    # data in its enclosing e-node, not an AST child, so its costs are 3 versus 4. In
    # the encoding each binder is another edge to Var; counting those markers as
    # children used to reverse the costs to 5 versus 4 and therefore the result beta
    # built. Binder layout metadata now keeps marker edges out of AstSize.
    _, cost, cost_unions = driver.fixture_block(BETA_FIXTURE, "g")
    out.append(
        Case(
            "subst-binder-cost",
            BETA_RULE,
            [cost["g"]],
            [cost[name] for name in ("g", "want", "wrong")],
            ref_subst,
            rounds=2,
            unions=cost_unions,
        )
    )
    return out


def known_encoding_limitations():
    """Small witnesses for semantic gaps that must not be mistaken for coverage.

    Each case pins both partitions. Agreement is reported as stale rather than as a
    pass: these belong in the ordinary differential suite once the encoding implements
    the reference behavior.
    """
    out = []

    # MultiPattern's slot tokens live in one rule-global namespace, while the slotted
    # source language gives a binder and its covered child a lexical identity. In
    # `let x = x in x`, the value's x is free and the body's x is bound despite their
    # shared surface spelling. The reference atoms below are still a MultiPattern;
    # they merely perform the scope-preserving lowering first by giving the binder and
    # covered body a private token. The compiler currently preserves the spelling and
    # therefore asks one e-node renaming to identify its distinct free and bound slots.
    #
    # This does not prohibit the behavior Rudi called out in issue #48: an
    # unconstrained pvar outside a binder may carry the same printed slot. It is only
    # about two explicit slot occurrences whose binding roles the source already says.
    # https://github.com/saulshanabrook/egglog-encoding/issues/81 tracks the fix.
    scope_src, scope_forms = driver.fixture_rewrites(
        BINDER_FIXTURE,
        "binder-free-distinct-spellings",
        "binder-free-same-spelling-known-limit",
    )
    reference = scope_forms["binder-free-distinct-spellings"]
    naive = scope_forms["binder-free-same-spelling-known-limit"]
    if reference[2] != naive[2]:
        raise ValueError(f"{BINDER_FIXTURE.name}: the paired scope witnesses must have the same right-hand side")
    scope_rule = driver.Rule(scope_src, LANG, naive)
    reference_rule = driver.Rule(scope_src, LANG, reference)
    scope_fixture, scoped, scoped_unions = driver.fixture_block(BINDER_FIXTURE, "same-spelling")
    scoped_target = scoped["same-spelling"]
    scoped_result = scope_fixture.term(naive[2])
    out.append(
        Case(
            "flat-binder-free",
            scope_rule,
            [scoped_target],
            [scoped_target, scoped_result],
            "[0][1] missing[[]]",
            rounds=2,
            ref_want="[0,1] missing[[]]",
            why=(
                "the compiler erases the distinct binding identities of explicit "
                "free and bound occurrences with one spelling"
            ),
            unions=scoped_unions,
            ref_rule=reference_rule,
        )
    )

    return out


def run_known_encoding_limitations():
    limited = known_encoding_limitations()
    bad = 0
    for case in limited:
        baseline = "".join(f"[{i}]" for i in range(len(case.probes))) + " missing[[]]"
        brs, brv = run_reference(case, with_rule=False)
        bes, bev = run_encoding(case, with_rule=False)
        rs, rv = run_reference(case)
        es, ev = run_encoding(case)
        base_ok = brs == bes == "OK" and brv == bev == baseline
        ok = base_ok and rs == es == "OK" and rv == case.ref_want and ev == case.want and rv != ev
        bad += not ok
        if ok:
            print(f"  ok   {case.name:<24} ref {rv}  encoding {ev}")
        elif not base_ok:
            print(f"  FAIL {case.name}: baseline ref={brs}:{brv}, encoding={bes}:{bev}, expected both {baseline}")
        elif rs == es == "OK" and rv == ev:
            print(f"  STALE {case.name}: implementations agree now ({rv}); move it to the ordinary suite")
        else:
            print(
                f"  FAIL {case.name}: ref={rs}:{rv}, expected {case.ref_want}; encoding={es}:{ev}, expected {case.want}"
            )
    print(f"\n{len(limited) - bad}/{len(limited)} known encoding limitations reproduced")
    return 1 if bad else 0


def run_iso(args):
    """A witnessed isomorphism of the two final e-graphs, not just the partition.

    The partition check compares what the PROBES say about each other; this compares
    the whole graph -- every class's slot set, every symmetry group, and a witness
    mapping that has to survive `verify`. sdql is where it matters most: its nodes
    have up to six children and two bound slots, so a structural difference has more
    room to hide behind a probe answer that happens to agree.

    A recorded encoding divergence cannot be compared this way. Those cases disagree
    on purpose, so an isomorphism is not expected to exist and finding none says
    nothing; they are reported as such rather than skipped silently.
    """
    from slotted.xdiff import isomorphism as I

    cases_ = [c for c in cases() if not args or c.name.startswith(args[0])]
    tally = {"ok": 0, "FAIL": 0, "skip": 0, "limit": 0, "unreadable": 0}
    diverging = []
    for c in cases_:
        if c.ref_want is not None:
            diverging.append(c.name)
            continue
        verdict, detail = I.check(c)
        tally[verdict] += 1
        print(f"  {verdict:4} {c.name:24} {detail}", flush=True)
    n = sum(tally.values())
    print(
        f"\n{tally['ok']}/{n} isomorphic   ({tally['FAIL']} differ, {tally['skip']} skipped,"
        f" {tally['limit']} not comparable, {tally['unreadable']} unreadable)"
        + (f"\n{len(diverging)} recorded divergence(s) not comparable: {', '.join(diverging)}" if diverging else "")
    )
    return 1 if tally["FAIL"] or tally["unreadable"] else 0


def main():
    argv = sys.argv[1:]
    if argv and argv[0] == "iso":
        return run_iso(argv[1:])

    if argv and argv[0] in ("known-encoding-limitations", "known-substitution-limitations"):
        return run_known_encoding_limitations()

    if argv and argv[0] == "list":
        for c in cases():
            print(f"{c.name:<24} {c.want}")
            print(f"    {c.rule.source()}")
        return 0
    if argv and argv[0] == "show":
        c = next(x for x in cases() if x.name == argv[1])
        print("---- spec")
        print(c.spec(), end="")
        print("---- egg")
        print(egg_program(c))
        print("---- reference     ", run_reference(c))
        print("---- encoding      ", run_encoding(c))
        print("---- ref  baseline ", run_reference(c, with_rule=False))
        print("---- enc  baseline ", run_encoding(c, with_rule=False))
        return 0

    cs = cases()
    bad = 0
    for c in cs:
        f = check_case(c)
        if f:
            bad += 1
        for x in f:
            print("FAIL " + x)
    print(f"\n{len(cs) - bad}/{len(cs)} cases agree")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
