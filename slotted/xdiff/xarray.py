#!/usr/bin/env python3
"""Differential tester for the paper's S4.1 functional array language.

The paper's Listing 1 language and 8 of its 9 rules, compiled into the egglog
slotted encoding and compared against the reference `slotted-egraphs`
implementation, exactly as `xdiff.py` does for the toy language.

The direct-substitution `beta` is excluded from this benchmark rule set.  Both the
oracle and this compiler now support it (SDQL's `beta` exercises the compiled
`subst` action), but the paper's array experiment deliberately uses the let-based
explicit-substitution alternative (footnote 4): `let-intro` followed by the let
rules.  The remaining 8 are therefore the rules that benchmark actually runs.

Both sides use the source rules in `languages/array-rules.egg`. Rust compiles
those rewrites for the encoding; `reference.py` translates them to MultiPattern
atoms. `test_program.py` runs both binaries, and `isomorphism.py` compares graphs.

Usage:
    ./xarray.py                each of the 8 rules firing, and each guard blocking
    ./xarray.py vac            drop each guard and check the answer changes, so a
                               blocked case is testing the guard and not nothing
    ./xarray.py extra          shapes next to the 8 rules, where the two may differ
    ./xarray.py iso [prefix]   the stronger check: a witnessed isomorphism of the two
                               final e-graphs, via `isomorphism.py`
    ./xarray.py goal [N...]    the paper's (A) -> (B), with N extra parameters
    ./xarray.py show <name>    one case's spec, its compiled rules, and both answers
"""

import os
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from slotted import reference as syntax  # noqa: E402
from slotted import test_program as driver  # noqa: E402
from slotted.benchmarks import array as benchmark  # noqa: E402

RUN_TIMEOUT = int(os.environ.get("XARRAY_TIMEOUT", "120"))

# Constructor signatures, binder columns, and reference names come from these files.
ARRAY_SRC = benchmark.SOURCE
ARRAY_SRC_RULES = benchmark.RULES
LANG = benchmark.LANG


sexpr, shift = LANG.sexpr, LANG.shift

MAP = ("Sym", "map")


# ----------------------------------------------------------------------- cases
class Case:
    lang = LANG

    def egg_program(self, *, mult):
        return egg_program(self, mult=mult)

    def __init__(self, name, terms, rules, probes, rounds=8, unions=()):
        self.name = name
        self.terms = list(terms)
        self.rules = list(rules)
        self.probes = list(probes)
        self.rounds = rounds
        self.unions = list(unions)

    def spec(self, include_probes=True):
        return driver.reference_spec(
            LANG,
            self.rounds,
            self.terms,
            self.unions,
            [line for r in self.rules for line in r.spec_lines()],
            self.probes if include_probes else [],
        )

    def shifted(self, k):
        return Case(
            self.name + f"+{k}",
            [shift(t, k) for t in self.terms],
            self.rules,
            [shift(t, k) for t in self.probes],
            self.rounds,
            [(shift(a, k), shift(b, k)) for a, b in self.unions],
        )


def egg_program(case, atom_order=None, mult=3, defer_probes=False):
    return driver.program(
        "array",
        LANG,
        [r.source(first_atom=atom_order) for r in case.rules],
        case.terms,
        case.unions,
        case.probes,
        case.rounds * mult,
        defer_probes=defer_probes,
    )


def run_reference(case):
    return driver.run_reference(case.spec(), RUN_TIMEOUT)


def run_reference_goal(case):
    """Run the artifact criterion without inserting the expected target."""
    spec = case.spec(include_probes=False) + f"goal {sexpr(case.probes[1])}\n"
    return driver.run_reference(spec, RUN_TIMEOUT, result="GOAL")


def run_encoding(case, atom_order=None, keep=None, mult=3):
    return driver.run_encoding(egg_program(case, atom_order, mult), len(case.probes), RUN_TIMEOUT, keep=keep)


def run_encoding_goal(case, keep=None):
    """Run user rules with only A present, then observe whether deferred B joins it."""
    status, partition = driver.run_encoding(
        egg_program(case, mult=1, defer_probes=True), len(case.probes), RUN_TIMEOUT, keep=keep
    )
    if status != "OK":
        return status, partition
    return "OK", "yes" if partition.startswith("[0,1]") else "no"


def check_case(case, order_check=True, shift_check=True):
    """Compare both sides. Returns a list of failure strings."""
    fails = []
    # 1. the machinery on its own: with no rule, the two must already agree, so a
    #    difference is attributed to matching rather than to the encoding.
    bare = Case(case.name, case.terms, [], case.probes, case.rounds, case.unions)
    rs, rv = run_reference(bare)
    es, ev = run_encoding(bare)
    if rs != "OK" or es != "OK":
        return [f"{case.name}: baseline ref={rs}:{rv} enc={es}:{ev}"]
    if rv != ev:
        return [f"{case.name}: BASELINE differs (machinery, not matching)\n    ref {rv}\n    enc {ev}"]
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
    if rv != ev:
        fails.append(f"{case.name}: MISMATCH vs reference\n    ref {rv}\n    enc {ev}")
    fired = rv != baseline
    if not fails:
        print(f"  ok  {case.name:<44} {'fired' if fired else 'NO-OP'}  {rv}")

    # 2. order independence of the compiled query: which atom leads must not matter.
    #    The reference receives the same unordered MultiPattern atoms each time.
    if order_check and not fails:
        for k in range(1, max(len(r.atoms) for r in case.rules)):
            ys, y = run_encoding(case, atom_order=k)
            if ys != "OK":
                fails.append(f"{case.name}: atom {k} first: encoding {ys}: {y}")
            elif y != ev:
                fails.append(
                    f"{case.name}: ENCODING depends on the leading atom "
                    f"({k})\n    atom 0 first {ev}\n    atom {k} first {y}"
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
    return fails


# Both sides derive their rules from the same source library.
RULES = driver.load_rules(ARRAY_SRC_RULES, LANG)
ALL_RULES = list(RULES.values())


# ------------------------------------------------------------------ the corpus
def V(n):
    return ("var", n)


def S(n):
    return ("Sym", n)


def A(*xs):
    """Left-nested application: A(f, a, b) = (app (app f a) b)."""
    out = xs[0]
    for x in xs[1:]:
        out = ("App", out, x)
    return out


def MAPPED(f, arg):
    return A(MAP, f, arg)


def per_rule_cases():
    """Each of the 8 rules firing on a small term, and each guarded rule blocked.

    The probes are always the pattern instance and the term the rule would produce,
    so a rule that fires merges them and a rule that is blocked does not. Symbol
    names avoid `f`, `g`, `h`, `k`, `sub`, `sub2`, `add`: those are operators of the
    oracle's existing toy language, and the reference's parser tries them as
    operators before it tries `Symbol`.
    """
    cs = []

    # -- eta ---------------------------------------------------------------
    #  (lam $0 (app f1 (var $0))) = f1
    cs.append(
        Case(
            "eta-fires",
            [("Lam", 0, ("App", S("f1"), V(0)))],
            [RULES["eta"]],
            [("Lam", 0, ("App", S("f1"), V(0))), S("f1"), S("f2")],
        )
    )
    # blocked: the bound slot is free in the function position, so eta would
    # capture it
    cs.append(
        Case(
            "eta-blocked",
            [("Lam", 0, ("App", ("App", S("f1"), V(0)), V(0)))],
            [RULES["eta"]],
            [("Lam", 0, ("App", ("App", S("f1"), V(0)), V(0))), ("App", S("f1"), V(0)), ("App", S("f1"), S("cc"))],
        )
    )

    # -- let-intro ---------------------------------------------------------
    cs.append(
        Case(
            "let-intro",
            [("App", ("Lam", 0, ("App", S("f1"), V(0))), S("aa"))],
            [RULES["let-intro"]],
            [
                ("App", ("Lam", 0, ("App", S("f1"), V(0))), S("aa")),
                ("Let", 0, ("App", S("f1"), V(0)), S("aa")),
                ("Let", 0, ("App", S("f1"), V(0)), S("bb")),
            ],
        )
    )

    # -- let-unused --------------------------------------------------------
    cs.append(
        Case(
            "let-unused-fires",
            [("Let", 0, ("App", S("f1"), S("cc")), S("aa"))],
            [RULES["let-unused"]],
            [("Let", 0, ("App", S("f1"), S("cc")), S("aa")), ("App", S("f1"), S("cc")), ("App", S("f1"), S("dd"))],
        )
    )
    cs.append(
        Case(
            "let-unused-blocked",
            [("Let", 0, ("App", S("f1"), V(0)), S("aa"))],
            [RULES["let-unused"]],
            [("Let", 0, ("App", S("f1"), V(0)), S("aa")), ("App", S("f1"), V(0)), ("App", S("f1"), S("cc"))],
        )
    )

    # -- let-var-same ------------------------------------------------------
    cs.append(
        Case(
            "let-var-same-fires",
            [("Let", 0, V(0), S("aa"))],
            [RULES["let-var-same"]],
            [("Let", 0, V(0), S("aa")), S("aa"), S("bb")],
        )
    )
    # blocked: `$x` is written twice, so the binder and the body's variable have
    # to be the same slot -- here they are not
    cs.append(
        Case(
            "let-var-same-blocked",
            [("Lam", 1, ("Let", 0, V(1), S("aa")))],
            [RULES["let-var-same"]],
            [("Lam", 1, ("Let", 0, V(1), S("aa"))), ("Lam", 1, S("aa")), ("Lam", 1, V(1))],
        )
    )

    # -- let-app -----------------------------------------------------------
    cs.append(
        Case(
            "let-app-fires",
            [("Let", 0, ("App", V(0), S("cc")), S("aa"))],
            [RULES["let-app"]],
            [
                ("Let", 0, ("App", V(0), S("cc")), S("aa")),
                ("App", ("Let", 0, V(0), S("aa")), ("Let", 0, S("cc"), S("aa"))),
                ("App", S("cc"), S("aa")),
            ],
        )
    )
    # blocked: the bound slot is free in NEITHER child of the application
    cs.append(
        Case(
            "let-app-blocked",
            [("Let", 0, ("App", S("dd"), S("cc")), S("aa"))],
            [RULES["let-app"]],
            [
                ("Let", 0, ("App", S("dd"), S("cc")), S("aa")),
                ("App", ("Let", 0, S("dd"), S("aa")), ("Let", 0, S("cc"), S("aa"))),
                ("App", S("dd"), S("cc")),
            ],
        )
    )

    # -- let-lam-diff ------------------------------------------------------
    cs.append(
        Case(
            "let-lam-diff-fires",
            [("Let", 0, ("Lam", 1, ("App", V(1), V(0))), S("aa"))],
            [RULES["let-lam-diff"]],
            [
                ("Let", 0, ("Lam", 1, ("App", V(1), V(0))), S("aa")),
                ("Lam", 1, ("Let", 0, ("App", V(1), V(0)), S("aa"))),
                ("Lam", 1, ("App", V(1), S("aa"))),
            ],
        )
    )
    # blocked: the outer bound slot is not free in the inner lambda's body
    cs.append(
        Case(
            "let-lam-diff-blocked",
            [("Let", 0, ("Lam", 1, ("App", V(1), S("cc"))), S("aa"))],
            [RULES["let-lam-diff"]],
            [
                ("Let", 0, ("Lam", 1, ("App", V(1), S("cc"))), S("aa")),
                ("Lam", 1, ("Let", 0, ("App", V(1), S("cc")), S("aa"))),
                ("Lam", 1, ("App", V(1), S("cc"))),
            ],
        )
    )

    # -- map-fusion --------------------------------------------------------
    cs.append(
        Case(
            "map-fusion",
            [MAPPED(S("f1"), MAPPED(S("f2"), S("arr")))],
            [RULES["map-fusion"]],
            [
                MAPPED(S("f1"), MAPPED(S("f2"), S("arr"))),
                MAPPED(("Lam", 0, ("App", S("f1"), ("App", S("f2"), V(0)))), S("arr")),
                MAPPED(("Lam", 0, ("App", S("f2"), ("App", S("f1"), V(0)))), S("arr")),
            ],
            rounds=4,
        )
    )

    # -- map-fission -------------------------------------------------------
    cs.append(
        Case(
            "map-fission-fires",
            [("App", MAP, ("Lam", 0, ("App", S("f1"), ("App", S("f2"), V(0)))))],
            [RULES["map-fission"]],
            [
                ("App", MAP, ("Lam", 0, ("App", S("f1"), ("App", S("f2"), V(0))))),
                ("Lam", 1, MAPPED(S("f1"), MAPPED(("Lam", 0, ("App", S("f2"), V(0))), V(1)))),
                ("Lam", 1, MAPPED(S("f2"), MAPPED(("Lam", 0, ("App", S("f1"), V(0))), V(1)))),
            ],
            rounds=3,
        )
    )
    # blocked: the lambda's bound slot is free in ?f, so fissioning there would
    # let it escape -- probe 1 is exactly the term with the escaped slot
    cs.append(
        Case(
            "map-fission-blocked",
            [("App", MAP, ("Lam", 0, ("App", ("App", S("f1"), V(0)), S("f2"))))],
            [RULES["map-fission"]],
            [
                ("App", MAP, ("Lam", 0, ("App", ("App", S("f1"), V(0)), S("f2")))),
                ("Lam", 1, MAPPED(("App", S("f1"), V(0)), MAPPED(("Lam", 0, S("f2")), V(1)))),
                ("App", MAP, ("Lam", 0, ("App", ("App", S("f1"), V(0)), S("f3")))),
            ],
            rounds=3,
        )
    )

    return cs


def goal_cases(n_params=(0, 1), rounds=8, wrap_lams=True, nfun=4, dims=2):
    """Test wrappers around the shared Figure 8 input and target generator."""
    cases = []
    for n in n_params:
        start, target = benchmark.goal(n, wrap_lams=wrap_lams, nfun=nfun, dims=dims)
        tag = "" if wrap_lams else "-free"
        name = f"goal{tag}-{dims}d-{nfun}f-N{n}"
        cases.append(Case(name, [start], list(ALL_RULES), [start, target], rounds=rounds))
    return cases


def _artifact_goal_text(o):
    """Literal transcription of artifact commit 83f2e5b's `gen.py` for N=2,M=2."""
    fresh = [0]

    def fresh_slot():
        fresh[0] += 1
        return f"${fresh[0]}"

    def fn_with_args(f):
        for i in range(1, o + 1):
            f = f"(app {f} (var $p{i}))"
        return f

    def chained(indices):
        fs = [fn_with_args(f"(var $fn{i})") for i in indices]
        if len(fs) == 1:
            return fs[0]
        x = fresh_slot()
        out = f"(var {x})"
        for fn in fs:
            out = f"(app {fn} {out})"
        return f"(lam {x} {out})"

    def maps(t):
        for _ in range(2):
            t = f"(app map {t})"
        return t

    def wrap(t):
        for i in reversed(range(1, o + 1)):
            t = f"(lam $p{i} {t})"
        for i in reversed(range(1, 5)):
            t = f"(lam $fn{i} {t})"
        return t

    lhs = wrap(maps(chained(range(1, 5))))
    left, right = maps(chained(range(3, 5))), maps(chained(range(1, 3)))
    x = fresh_slot()
    rhs = wrap(f"(lam {x} (app {left} (app {right} (var {x}))))")
    return lhs, rhs


def _alpha_shape(text):
    """A binder-name-free tree, sufficient to compare closed artifact terms."""
    tree = syntax.parse(text)[0]
    counter = [0]

    def go(term, env):
        if not isinstance(term, list):
            return term
        if term and term[0] == "lam":
            counter[0] += 1
            name = f"b{counter[0]}"
            nested = dict(env)
            nested[term[1]] = name
            return "lam", name, go(term[2], nested)
        if term and term[0] == "var":
            return "var", env.get(term[1], f"free:{term[1]}")
        return tuple(go(part, env) for part in term)

    return go(tree, {})


def check_artifact_goal_port():
    """Hold all eleven Figure-8 parameter shapes against the artifact generator."""
    bad = []
    for o in range(11):
        case = goal_cases([o], rounds=6, wrap_lams=True, nfun=4, dims=2)[0]
        expected = _artifact_goal_text(o)
        actual = tuple(sexpr(t) for t in case.probes)
        if tuple(map(_alpha_shape, actual)) != tuple(map(_alpha_shape, expected)):
            bad.append(o)
    if bad:
        print(f"FAIL artifact parameter shapes differ for O={bad}")
    print(f"\n{11 - len(bad)}/11 array artifact goal shapes match")
    return 1 if bad else 0


def report_goal(case):
    """The paper's criterion: does each side put (A) and (B) in one class?

    Neither side saturates -- `map-fusion`/`map-fission` and `let-app` keep
    producing work -- so this is a bounded comparison, and a `no` means "not within
    this budget", not "never".
    """
    rs, rv = run_reference_goal(case)
    es, ev = run_encoding_goal(case)

    def reached(status, val):
        if status in ("TIMEOUT", "ERROR"):
            return status
        return "YES" if val == "yes" else "no"

    r_ok, e_ok = reached(rs, rv), reached(es, ev)
    reached_both = r_ok == e_ok == "YES"
    verdict = "REACHED" if reached_both else "FAILED"
    print(f"  {case.name:<26} rounds={case.rounds:<3} ref {rs}/{r_ok:<7} enc {es}/{e_ok:<7} {verdict}")
    if r_ok in ("TIMEOUT", "ERROR") or e_ok in ("TIMEOUT", "ERROR"):
        print(f"      ref {rv}\n      enc {ev}")
    return reached_both


def unbound_cases():
    """Small shapes that are not one of the 8 rules but sit next to them, where
    the two sides might reasonably differ."""
    cs = []
    # A `let` whose bound slot is ALSO free in the value. `Bind` hides the slot
    # from the body only, so both implementations must keep it free and agree.
    #   let x = x in f1 x      -- the value's `x` is the AMBIENT one, the body's is
    # the bound one. `Bind` covers the body column only. Probing that needs a parent
    # that can see the difference: two applications that differ only in whether the
    # `let`'s slot and the argument's slot coincide.
    B = ("App", S("f1"), V(0))
    L = ("Let", 0, B, V(0))
    cs.append(
        Case(
            "let-slot-free-in-value",
            [("App", L, V(0)), ("App", L, V(1))],
            [RULES["let-unused"]],
            [("App", L, V(0)), ("App", L, V(1)), ("App", L, S("cc"))],
        )
    )
    return cs


SYMS = ["map", "f1", "f2", "aa", "cc"]


def rand_term(rng, depth, pool, ctr):
    """A random array term over the slots in `pool`.

    A `let` gets a value built from `pool` WITHOUT its bound slot. That is not a
    convenience: a value that mentions the bound slot is the one shape where the
    reference's `Let(Bind<body>, value)` and the encoding's whole-node binder
    disagree, and `unbound_cases` covers it deliberately rather than having every
    fuzz case trip over it.
    """
    if depth == 0 or rng.random() < 0.25:
        if pool and rng.random() < 0.55:
            return ("var", rng.choice(sorted(pool)))
        return ("Sym", rng.choice(SYMS))

    def sub(extra=()):
        return rand_term(rng, depth - 1, pool | set(extra), ctr)

    def slot():
        ctr[0] += 1
        return ctr[0]

    # Half the time plant one of the rules' own left-hand shapes, so the sweep
    # actually reaches the rules instead of generating terms none of them match.
    if rng.random() < 0.5:
        which = rng.randrange(6)
        if which == 0:  # map-fusion
            return ("App", ("App", MAP, sub()), ("App", ("App", MAP, sub()), sub()))
        if which == 1:  # map-fission
            s = slot()
            return ("App", MAP, ("Lam", s, ("App", sub(), sub([s]))))
        if which == 2:  # let-intro / beta shape
            s = slot()
            return ("App", ("Lam", s, sub([s])), sub())
        if which == 3:  # eta
            s = slot()
            return ("Lam", s, ("App", sub(), ("var", s)))
        if which == 4:  # let-var-same
            s = slot()
            return ("Let", s, ("var", s), sub())
        s = slot()  # a plain let
        return ("Let", s, sub([s]), sub())

    r = rng.random()
    if r < 0.55:
        return ("App", sub(), sub())
    s = slot()
    if r < 0.85:
        return ("Lam", s, sub([s]))
    return ("Let", s, sub([s]), sub())


def subterms(t):
    """Every subterm, root first."""
    out = [t]
    if t[0] == "app":
        out += subterms(t[1]) + subterms(t[2])
    elif t[0] == "lam":
        out += subterms(t[2])
    elif t[0] == "let":
        out += subterms(t[2]) + subterms(t[3])
    return out


def rand_case(rng, i):
    ctr = [0]
    while True:
        t = rand_term(rng, rng.randrange(2, 5), set(), ctr)
        # a bare `(var $k)` at top level loses its slot in the encoding: a `U` value
        # is an e-node, and every var node is the one canonical `(Var 0)`
        if t[0] != "var":
            break
    rules = rng.sample(ALL_RULES, rng.randrange(1, 3))
    # Probing every subterm is what makes the sweep observe anything: `eta`,
    # `let-unused` and `let-var-same` equate a term with one of its own subterms,
    # and the constructive rules feed those. A bare `(var $k)` is left out -- the
    # encoding cannot carry its slot at top level.
    probes, seen = [], set()
    for s in subterms(t):
        if s[0] == "var" or s in seen:
            continue
        seen.add(s)
        probes.append(s)
        if len(probes) == 9:
            break
    probes += [("Lam", 90, ("App", S("f1"), V(90))), S("f1")]
    return Case(f"fuzz{i}", [t], list(rules), probes, rounds=3)


def check_vacuity(case):
    """A blocked case only tests the guard if dropping the guard changes the answer.

    Returns a failure string when it does not -- i.e. when the case would pass
    just as well with the condition deleted, which means it is testing nothing.
    """
    stripped = [r.without_guards() for r in case.rules]
    if not any(r.conds for r in case.rules):
        return f"{case.name}: no condition to drop"
    off = Case(case.name, case.terms, stripped, case.probes, case.rounds, case.unions)
    _, rv = run_reference(case)
    _, ev = run_encoding(case)
    xs, xv = run_reference(off)
    ys, yv = run_encoding(off)
    bad = []
    if xs == "OK" and xv == rv:
        bad.append(f"reference unchanged without the guard ({rv})")
    if ys == "OK" and yv == ev:
        bad.append(f"encoding unchanged without the guard ({ev})")
    if bad:
        return f"{case.name}: VACUOUS -- " + "; ".join(bad)
    print(f"  ok  {case.name:<44} guard matters: ref {rv} -> {xv}   enc {ev} -> {yv}")
    return None


# ------------------------------------------------------------------------ main
def main():
    args = sys.argv[1:]
    if args and args[0] == "artifact-shapes":
        return check_artifact_goal_port()
    if args and args[0] == "show":
        cases = (
            per_rule_cases()
            + unbound_cases()
            + goal_cases([0], 10, wrap_lams=False, nfun=2, dims=1)
            + goal_cases([0], 10, wrap_lams=False, nfun=4, dims=2)
            + goal_cases([0, 1], 10, wrap_lams=True, nfun=4, dims=2)
        )
        case = next(c for c in cases if c.name.startswith(args[1]))
        print("=== spec ===")
        print(case.spec(), end="")
        for r in case.rules:
            print(f"=== rule {r.name} ===")
            print(r.source())
        keep = ROOT / f"xarray-show-{case.name}.egg"
        print("=== reference ===", run_reference(case))
        print("=== encoding  ===", run_encoding(case, keep=keep))
        return 0

    if args and args[0] == "fuzz":
        import random

        n = int(args[1]) if len(args) > 1 else 40
        rng = random.Random(int(args[2]) if len(args) > 2 else 0)
        fails, ok, skipped = [], 0, 0
        for i in range(n):
            c = rand_case(rng, i)
            # A case where the reference does not settle ran a different amount of
            # work on the two sides, so comparing them says nothing: skip it rather
            # than reporting a difference that is really a round-count artefact.
            st, _ = run_reference(c)
            if st != "OK":
                skipped += 1
                print(f"  skip {c.name:<12} reference {st}", flush=True)
                continue
            fs = check_case(c)
            if fs:
                fails += fs
                for f in fs:
                    print("FAIL " + f, flush=True)
            else:
                ok += 1
        print(f"\n{ok}/{n - skipped} comparable cases agree ({skipped} skipped)")
        return 1 if fails else 0

    if args and args[0] == "iso":
        # The stronger check: not just the probe partition but a witnessed
        # isomorphism of the two final e-graphs, which also compares class slot
        # sets and symmetry groups.
        from slotted.xdiff import isomorphism as I

        cases = per_rule_cases() + unbound_cases()
        if len(args) > 1:
            cases = [c for c in cases if c.name.startswith(args[1])]
        tally = {"ok": 0, "FAIL": 0, "skip": 0, "limit": 0, "unreadable": 0}
        for c in cases:
            verdict, detail = I.check(c)
            tally[verdict] += 1
            print(f"  {verdict:4} {c.name:36} {detail}", flush=True)
        print(
            f"\n{tally['ok']}/{len(cases)} isomorphic   "
            f"({tally['FAIL']} differ, {tally['skip']} skipped, "
            f"{tally['limit']} not comparable, {tally['unreadable']} unreadable)"
        )
        return 1 if tally["FAIL"] or tally["unreadable"] else 0

    if args and args[0] == "vac":
        cases = [c for c in per_rule_cases() if c.name.endswith("blocked") and any(r.conds for r in c.rules)]
        fails = [f for f in (check_vacuity(c) for c in cases) if f]
        for f in fails:
            print("FAIL " + f)
        print(f"\n{len(cases) - len(fails)}/{len(cases)} guards are load-bearing")
        return 1 if fails else 0

    if args and args[0] in ("goal", "goal-smoke"):
        rounds = int(os.environ.get("XARRAY_ROUNDS", "10"))
        ns = [int(x) for x in args[1:]] or [0, 1]
        cases = goal_cases([0], rounds, wrap_lams=False, nfun=2, dims=1)
        # graded, easiest first: the free-symbol 1-D two-function version is the
        # smallest shape that still needs the whole rule set, then the paper's own
        # 2-D four-function program, first with free symbols and then with the
        # functions bound at the top as Listing 1 has them.
        if args[0] == "goal":
            cases += goal_cases(ns, rounds, wrap_lams=False, nfun=4, dims=2)
            cases += goal_cases(ns, rounds, wrap_lams=True, nfun=4, dims=2)
        reached = sum(1 for c in cases if report_goal(c))
        print(f"\n{reached}/{len(cases)} goal cases reached on both sides")
        return 0 if reached == len(cases) else 1
    cases = unbound_cases() if args and args[0] == "extra" else per_rule_cases()

    fails, ok = [], 0
    for c in cases:
        fs = check_case(c)
        if fs:
            fails += fs
            for f in fs:
                print("FAIL " + f)
        else:
            ok += 1
    print(f"\n{ok}/{len(cases)} cases agree")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
