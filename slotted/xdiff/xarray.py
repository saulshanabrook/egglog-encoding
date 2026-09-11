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

The two sides:

  reference   the rules flattened to `MultiPattern` atoms. This is the pattern
              language implemented by the encoding; nested `ematch_all` has different
              semantics and is not used as an oracle here. The rule source follows
              `tests/rise`, which has Listing 1's binding language and guard polarity;
              `tests/array/mod.rs` instead has a non-binding `Lam(Slot, AppliedId)` and
              an oppositely-polarized `slot_free_in` helper.
  encoding    a generated .egg file, each rule flattened into depth-1 atoms and
              compiled by `slotted/slotted-encoder.py`, which is the
              recipe in `slotted/encoding/user-rules.egg`.

Usage:
    ./xarray.py                each of the 8 rules firing, and each guard blocking
    ./xarray.py vac            drop each guard and check the answer changes, so a
                               blocked case is testing the guard and not nothing
    ./xarray.py extra          shapes next to the 8 rules, where the two may differ
    ./xarray.py iso [prefix]   the stronger check: a witnessed isomorphism of the two
                               final e-graphs, via `isomorphism.py`
    ./xarray.py goal [N...]    the paper's (A) -> (B), with N extra parameters
    ./xarray.py egg            regenerate `target/slotted/slotted-array-rules.egg`
    ./xarray.py show <name>    one case's spec, its compiled rules, and both answers
"""

import os
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from xdiff import EGGLOG, ROOT, XMULTI, parse_same_class, slotenc  # noqa: E402

sc = __import__("slotted-egglog")

RUN_TIMEOUT = int(os.environ.get("XARRAY_TIMEOUT", "120"))

# ---------------------------------------------------------------- array terms
# term := ('var', slot) | ('sym', name) | ('num', n)
#       | ('app', a, b) | ('lam', slot, body) | ('let', slot, body, val)
#
# The language is `slotted/languages/array.egg` -- the paper's Listing 1,
# one constructor per operator, the shape `define_language!` produces -- with
# `array.ref` beside it saying what the reference calls each one. Nothing here
# restates a signature or a binder column: `Lam` and `Let` bind their column 0 because
# that file's `:binder` says so, so this cannot disagree with the rules generated for
# them.
#
# `let` takes its columns in the reference's order -- binder, body, value. The paper's
# Listing 1 writes the same constructor as `Let(RenamedId, Bind<RenamedId>)`, i.e.
# `(let ?e $x ?body)`.
# The language is declared where its rules are: `slotted/languages/array.egg` holds
# both, and `array.ref` beside it says what the reference calls each constructor.
ARRAY_SRC = ROOT / "slotted" / "languages" / "array.egg"
LANG = slotenc.language(ARRAY_SRC, ARRAY_SRC.with_suffix(".ref"))

# the per-language machinery, not the generic string-headed one
MACHINERY = "target/slotted/slotted-lang-array.egg"

enc, sexpr, shift = LANG.enc, LANG.sexpr, LANG.shift

MAP = ("sym", "map")


# ------------------------------------------------------------- rule descriptions
class Rule:
    """One rewrite, in the encoder's grammar.

    `atoms` are `(root, op, [child...])` with each child `("pv", name)`,
    `("sl", "$x")` or `("cls", term)`; a right-hand side is one of those or
    `(op, arg...)` to build a node. `conds` are `(want, "$slot", [pvar...])`, and
    `fresh` names slots the right-hand side binds that the pattern never mentions.
    """

    def __init__(self, name, atoms, rhs_root, rhs, conds=(), fresh=()):
        self.name = name
        self.atoms = list(atoms)
        self.rhs_root = rhs_root
        self.rhs = rhs
        self.conds = list(conds)
        self.fresh = list(fresh)

    def atom_lines(self):
        """The pattern as `MultiPattern` atom lines."""
        return slotenc.atom_lines(LANG, self.atoms[0][0], self.atoms)

    def spec_lines(self):
        pat = slotenc.pat_sexpr(LANG, self.rhs)
        spelled = self.atom_lines()
        # an `atom`/`rhs` root is written bare; xmulti supplies the `?`
        out = ["rule", *spelled[1], f"rhs {self.rhs_root.lstrip('?')} {pat}"]
        for want, slot, pvars in self.conds:
            out.append(f"cond {'in' if want else 'notin'} {slot} {' '.join(pvars)}")
        return out


def compile_array_rule(rule, atom_order=None):
    """One array rule, through the encoder, which is the recipe in
    `slotted/encoding/user-rules.egg`.

    `atom_order` names the atom that leads; the encoding's answer must not depend on
    which, and `check_case` varies it. The leader is named rather than inferred
    because `atoms[0]` -- the pattern's outermost node -- is a binder for most of
    these rules, and taking it first pins the bound slot off its own edge.

    The slot variables are `s_x` rather than `sx`, and a minted right-hand side slot
    gets a solve of its own with the avoid-set growing after it, rather than one solve
    over the whole batch. Both are spellings, not constructions:
    `target/slotted/slotted-array-rules.egg` is build output, so they are kept as they were
    written.
    """
    lead = 0 if atom_order is None else min(atom_order, len(rule.atoms) - 1)
    return slotenc.compile_rule(
        LANG,
        slotenc.connected_order(LANG, rule.atoms, first=lead),
        ("build", rule.rhs_root, rule.rhs),
        conds=rule.conds,
        fresh=rule.fresh,
        slot_prefix="s_",
        fresh_batch=False,
    )


# ----------------------------------------------------------------------- cases
class Case:
    def __init__(self, name, terms, rules, probes, rounds=8, unions=()):
        self.name = name
        self.terms = list(terms)
        self.rules = list(rules)
        self.probes = list(probes)
        self.rounds = rounds
        self.unions = list(unions)

    def spec(self, include_probes=True):
        out = [f"rounds {self.rounds}"]
        out += [f"term {sexpr(t)}" for t in self.terms]
        out += [f"union {sexpr(a)} {sexpr(b)}" for a, b in self.unions]
        for r in self.rules:
            out += r.spec_lines()
        if include_probes:
            out += [f"probe {sexpr(t)}" for t in self.probes]
        return "\n".join(out) + "\n"

    def shifted(self, k):
        return Case(
            self.name + f"+{k}",
            [shift(t, k) for t in self.terms],
            self.rules,
            [shift(t, k) for t in self.probes],
            self.rounds,
            [(shift(a, k), shift(b, k)) for a, b in self.unions],
        )


def schedule(steps):
    return (
        f"(run-schedule (saturate (run slotted))\n              (repeat {steps} (seq (run) (saturate (run slotted)))))"
    )


def egg_program(case, atom_order=None, mult=3, defer_probes=False):
    out = [
        f'(include "{MACHINERY}")',
        "(ruleset probe)",
        "(relation ProbeId (U i64))",
        "(relation SameClass (i64 i64))",
        "(rule ((ProbeId a i) (ProbeId b j)\n"
        "       (RenamesToLeader a m1 l) (RenamesToLeader b m2 l))\n"
        "      ((SameClass i j)) :ruleset probe)",
    ]
    for r in case.rules:
        out.append(f";; {r.name}")
        out.append(compile_array_rule(r, atom_order))
    for i, t in enumerate(case.terms):
        out.append(f"(let _t{i} {enc(t)})")
    for i, (a, b) in enumerate(case.unions):
        out.append(f"(let _ua{i} {enc(a)})")
        out.append(f"(let _ub{i} {enc(b)})")
        out.append(f"(union _ua{i} _ub{i})")
    if not defer_probes:
        for i, t in enumerate(case.probes):
            out.append(f"(let _p{i} {enc(t)})")
    out.append(schedule(case.rounds * mult))
    if defer_probes:
        # Goal terms are observational: build them only after the user-rule budget.
        # The following schedule runs invariant maintenance and the probe relation,
        # never the user rules, so the expected target cannot seed rewrite search.
        for i, t in enumerate(case.probes):
            out.append(f"(let _p{i} {enc(t)})")
    for i, _ in enumerate(case.probes):
        out.append(f"(ProbeId _p{i} {i})")
    # Do not give the encoding a second user-rule budget after installing probes.
    # The reference runs exactly `rounds * mult`; only invariant maintenance and the
    # observational rule remain here.
    out.append("(run-schedule (saturate (run slotted)) (saturate (run probe)))")
    out.append("(print-function SameClass 100000)")
    return "\n".join(out) + "\n"


def run_reference(case):
    try:
        r = subprocess.run(
            [str(XMULTI / "target" / "debug" / "xmulti")],
            input=case.spec(),
            capture_output=True,
            text=True,
            timeout=RUN_TIMEOUT,
        )
    except subprocess.TimeoutExpired:
        return ("TIMEOUT", f">{RUN_TIMEOUT}s")
    if r.returncode != 0:
        return ("ERROR", (r.stderr.strip().splitlines() or ["?"])[-1])
    part, sat = None, True
    for line in r.stdout.splitlines():
        if line.startswith("PARTITION "):
            part = line[len("PARTITION ") :].strip()
        elif line.startswith("SATURATED "):
            sat = line.split()[1] == "yes"
    if part is None:
        return ("ERROR", "no PARTITION line")
    return ("OK" if sat else "UNSATURATED", part)


def run_reference_goal(case):
    """Run the artifact criterion without inserting the expected target."""
    spec = case.spec(include_probes=False) + f"goal {sexpr(case.probes[1])}\n"
    try:
        r = subprocess.run(
            [str(XMULTI / "target" / "debug" / "xmulti")],
            input=spec,
            capture_output=True,
            text=True,
            timeout=RUN_TIMEOUT,
        )
    except subprocess.TimeoutExpired:
        return "TIMEOUT", f">{RUN_TIMEOUT}s"
    if r.returncode != 0:
        return "ERROR", (r.stderr.strip().splitlines() or ["?"])[-1]
    goals = [line.split()[1] for line in r.stdout.splitlines() if line.startswith("GOAL ")]
    if len(goals) != 1:
        return "ERROR", "no unique GOAL line"
    saturated = all(not line.startswith("SATURATED no") for line in r.stdout.splitlines())
    return ("OK" if saturated else "UNSATURATED"), goals[0]


def run_encoding(case, atom_order=None, keep=None, mult=3):
    prog = egg_program(case, atom_order, mult)
    path = keep or (ROOT / f"xarray-tmp-{os.getpid()}-{mult}.egg")
    path.write_text(prog)
    try:
        r = subprocess.run([str(EGGLOG), str(path)], capture_output=True, text=True, timeout=RUN_TIMEOUT, cwd=ROOT)
    except subprocess.TimeoutExpired:
        return ("TIMEOUT", f">{RUN_TIMEOUT}s (kept at {path})")
    if r.returncode != 0:
        err = [line for line in r.stderr.splitlines() if "ERROR" in line]
        msg = err[-1] if err else r.stderr.strip()[:600]
        return ("ERROR", f"{msg}\n    (kept at {path})")
    if not keep:
        path.unlink(missing_ok=True)
    return ("OK", parse_same_class(r.stdout, len(case.probes)))


def run_encoding_goal(case, keep=None):
    """Run user rules with only A present, then observe whether deferred B joins it."""
    prog = egg_program(case, mult=1, defer_probes=True)
    path = keep or (ROOT / f"xarray-goal-tmp-{os.getpid()}.egg")
    path.write_text(prog)
    try:
        r = subprocess.run([str(EGGLOG), str(path)], capture_output=True, text=True, timeout=RUN_TIMEOUT, cwd=ROOT)
    except subprocess.TimeoutExpired:
        return "TIMEOUT", f">{RUN_TIMEOUT}s (kept at {path})"
    if r.returncode != 0:
        err = [line for line in r.stderr.splitlines() if "ERROR" in line]
        return "ERROR", err[-1] if err else r.stderr[:160]
    if keep is None:
        path.unlink(missing_ok=True)
    partition = parse_same_class(r.stdout, len(case.probes))
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
            if ys == "OK" and y != ev:
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


# ------------------------------------------------------------------- the 8 rules
#
# Read from `slotted/languages/array.egg`, written in the slotted language, so the rules a
# reader sees are the rules that run here. `slotted-egglog.py` compiles the same file
# for `run-slotted-tests.py`; neither restates a rule.
#
# The atoms come from `flatten`, which emits the pattern's outermost node first.
def _load_rules():
    src = sc.Source(ARRAY_SRC)
    out = []
    for form in sc.parse(ARRAY_SRC.read_text()):
        if not (isinstance(form, list) and form and form[0] == "rewrite"):
            continue
        r = sc.rewrite_parts(src, form)
        assert r["name"], f"a rewrite with no :name in {ARRAY_SRC.name}"
        # `:when (= ...)` contributes PATTERN ATOMS, and this builds its own rule object
        # from `lhs`/`conds` alone, so one would be dropped in silence and the reference
        # would be asked a different question than the encoding. Teach `Rule` about extra
        # atoms before using one in this language.
        assert not r["equalities"], f"{r['name']}: `:when (= ...)` is not supported here yet"
        root, atoms = slotenc.flatten(LANG, src.term(r["lhs"], ground=False))
        rhs = slotenc.rhs_of(LANG, src.term(r["rhs"], ground=False))
        out.append(Rule(r["name"], atoms, root, rhs, conds=r["conds"], fresh=r["fresh"]))
    return out


#: name -> rule, and the same rules as a list. The per-rule cases below ask for one by
#: name, which reads as the rule it is rather than as an index. Both sides receive the
#: same flattened MultiPattern query.
RULES = {r.name: r for r in _load_rules()}
ALL_RULES = list(RULES.values())


# ------------------------------------------------------------------ the corpus
def V(n):
    return ("var", n)


def S(n):
    return ("sym", n)


def A(*xs):
    """Left-nested application: A(f, a, b) = (app (app f a) b)."""
    out = xs[0]
    for x in xs[1:]:
        out = ("app", out, x)
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
            [("lam", 0, ("app", S("f1"), V(0)))],
            [RULES["eta"]],
            [("lam", 0, ("app", S("f1"), V(0))), S("f1"), S("f2")],
        )
    )
    # blocked: the bound slot is free in the function position, so eta would
    # capture it
    cs.append(
        Case(
            "eta-blocked",
            [("lam", 0, ("app", ("app", S("f1"), V(0)), V(0)))],
            [RULES["eta"]],
            [("lam", 0, ("app", ("app", S("f1"), V(0)), V(0))), ("app", S("f1"), V(0)), ("app", S("f1"), S("cc"))],
        )
    )

    # -- let-intro ---------------------------------------------------------
    cs.append(
        Case(
            "let-intro",
            [("app", ("lam", 0, ("app", S("f1"), V(0))), S("aa"))],
            [RULES["let-intro"]],
            [
                ("app", ("lam", 0, ("app", S("f1"), V(0))), S("aa")),
                ("let", 0, ("app", S("f1"), V(0)), S("aa")),
                ("let", 0, ("app", S("f1"), V(0)), S("bb")),
            ],
        )
    )

    # -- let-unused --------------------------------------------------------
    cs.append(
        Case(
            "let-unused-fires",
            [("let", 0, ("app", S("f1"), S("cc")), S("aa"))],
            [RULES["let-unused"]],
            [("let", 0, ("app", S("f1"), S("cc")), S("aa")), ("app", S("f1"), S("cc")), ("app", S("f1"), S("dd"))],
        )
    )
    cs.append(
        Case(
            "let-unused-blocked",
            [("let", 0, ("app", S("f1"), V(0)), S("aa"))],
            [RULES["let-unused"]],
            [("let", 0, ("app", S("f1"), V(0)), S("aa")), ("app", S("f1"), V(0)), ("app", S("f1"), S("cc"))],
        )
    )

    # -- let-var-same ------------------------------------------------------
    cs.append(
        Case(
            "let-var-same-fires",
            [("let", 0, V(0), S("aa"))],
            [RULES["let-var-same"]],
            [("let", 0, V(0), S("aa")), S("aa"), S("bb")],
        )
    )
    # blocked: `$x` is written twice, so the binder and the body's variable have
    # to be the same slot -- here they are not
    cs.append(
        Case(
            "let-var-same-blocked",
            [("lam", 1, ("let", 0, V(1), S("aa")))],
            [RULES["let-var-same"]],
            [("lam", 1, ("let", 0, V(1), S("aa"))), ("lam", 1, S("aa")), ("lam", 1, V(1))],
        )
    )

    # -- let-app -----------------------------------------------------------
    cs.append(
        Case(
            "let-app-fires",
            [("let", 0, ("app", V(0), S("cc")), S("aa"))],
            [RULES["let-app"]],
            [
                ("let", 0, ("app", V(0), S("cc")), S("aa")),
                ("app", ("let", 0, V(0), S("aa")), ("let", 0, S("cc"), S("aa"))),
                ("app", S("cc"), S("aa")),
            ],
        )
    )
    # blocked: the bound slot is free in NEITHER child of the application
    cs.append(
        Case(
            "let-app-blocked",
            [("let", 0, ("app", S("dd"), S("cc")), S("aa"))],
            [RULES["let-app"]],
            [
                ("let", 0, ("app", S("dd"), S("cc")), S("aa")),
                ("app", ("let", 0, S("dd"), S("aa")), ("let", 0, S("cc"), S("aa"))),
                ("app", S("dd"), S("cc")),
            ],
        )
    )

    # -- let-lam-diff ------------------------------------------------------
    cs.append(
        Case(
            "let-lam-diff-fires",
            [("let", 0, ("lam", 1, ("app", V(1), V(0))), S("aa"))],
            [RULES["let-lam-diff"]],
            [
                ("let", 0, ("lam", 1, ("app", V(1), V(0))), S("aa")),
                ("lam", 1, ("let", 0, ("app", V(1), V(0)), S("aa"))),
                ("lam", 1, ("app", V(1), S("aa"))),
            ],
        )
    )
    # blocked: the outer bound slot is not free in the inner lambda's body
    cs.append(
        Case(
            "let-lam-diff-blocked",
            [("let", 0, ("lam", 1, ("app", V(1), S("cc"))), S("aa"))],
            [RULES["let-lam-diff"]],
            [
                ("let", 0, ("lam", 1, ("app", V(1), S("cc"))), S("aa")),
                ("lam", 1, ("let", 0, ("app", V(1), S("cc")), S("aa"))),
                ("lam", 1, ("app", V(1), S("cc"))),
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
                MAPPED(("lam", 0, ("app", S("f1"), ("app", S("f2"), V(0)))), S("arr")),
                MAPPED(("lam", 0, ("app", S("f2"), ("app", S("f1"), V(0)))), S("arr")),
            ],
            rounds=4,
        )
    )

    # -- map-fission -------------------------------------------------------
    cs.append(
        Case(
            "map-fission-fires",
            [("app", MAP, ("lam", 0, ("app", S("f1"), ("app", S("f2"), V(0)))))],
            [RULES["map-fission"]],
            [
                ("app", MAP, ("lam", 0, ("app", S("f1"), ("app", S("f2"), V(0))))),
                ("lam", 1, MAPPED(S("f1"), MAPPED(("lam", 0, ("app", S("f2"), V(0))), V(1)))),
                ("lam", 1, MAPPED(S("f2"), MAPPED(("lam", 0, ("app", S("f1"), V(0))), V(1)))),
            ],
            rounds=3,
        )
    )
    # blocked: the lambda's bound slot is free in ?f, so fissioning there would
    # let it escape -- probe 1 is exactly the term with the escaped slot
    cs.append(
        Case(
            "map-fission-blocked",
            [("app", MAP, ("lam", 0, ("app", ("app", S("f1"), V(0)), S("f2"))))],
            [RULES["map-fission"]],
            [
                ("app", MAP, ("lam", 0, ("app", ("app", S("f1"), V(0)), S("f2")))),
                ("lam", 1, MAPPED(("app", S("f1"), V(0)), MAPPED(("lam", 0, S("f2")), V(1)))),
                ("app", MAP, ("lam", 0, ("app", ("app", S("f1"), V(0)), S("f3")))),
            ],
            rounds=3,
        )
    )

    return cs


def _chain(fs, arg):
    """fs = [f1, f2, ...] applied innermost-first: f_n (... (f1 arg))."""
    for g in fs:
        arg = ("app", g, arg)
    return arg


def goal_cases(n_params=(0, 1), rounds=8, wrap_lams=True, nfun=4, dims=2):
    """The paper artifact's S4.1 transformation: (A) -> (B).

        (A)  \\f1. ... \\f4. map (map (\\x. f4 (f3 (f2 (f1 x)))))
        (B)  \\f1. ... \\f4. \\y. map (map (\\x. f4 (f3 x)))
                                      (map (map (\\x. f2 (f1 x))) y)

    The artifact varies parameters `p1 ... pN` applied to each function. This port
    follows its `functional-array-language/gen.py`, including two details the prior
    hand-written case got wrong: (A) is eta-reduced and has no matrix binder, while
    (B) introduces `y`; and the function binders are outside the parameter binders.
    `wrap_lams=False` is a smaller diagnostic with those names left free.
    """
    cs = []
    for n in n_params:
        ps = [V(1 + i) for i in range(n)]
        fn_slots = [1000 + i for i in range(nfun)]
        fs = [A(V(slot), *ps) for slot in fn_slots] if wrap_lams else [A(S(f"f{i + 1}"), *ps) for i in range(nfun)]
        half = nfun // 2
        fresh_slot = iter(range(100, 1000)).__next__

        def maps(fn):
            out = fn
            for _ in range(dims):
                out = ("app", MAP, out)
            return out

        def chained(parts, fresh_slot=fresh_slot):
            if len(parts) == 1:
                return parts[0]
            x = fresh_slot()
            return ("lam", x, _chain(parts, V(x)))

        a_body = maps(chained(fs))
        left, right = maps(chained(fs[half:])), maps(chained(fs[:half]))
        y = fresh_slot()
        b_body = ("lam", y, ("app", left, ("app", right, V(y))))

        def wrap(t, n=n, fn_slots=fn_slots):
            if not wrap_lams:
                return t
            # Artifact `nest_lams`: parameters inside function binders.
            for i in reversed(range(n)):
                t = ("lam", 1 + i, t)
            for slot in reversed(fn_slots):
                t = ("lam", slot, t)
            return t

        A_, B_ = wrap(a_body), wrap(b_body)
        tag = "" if wrap_lams else "-free"
        nm = f"goal{tag}-{dims}d-{nfun}f-N{n}"
        cs.append(Case(nm, [A_], list(ALL_RULES), [A_, B_], rounds=rounds))
    return cs


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
    tree = sc.parse(text)[0]
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
    B = ("app", S("f1"), V(0))
    L = ("let", 0, B, V(0))
    cs.append(
        Case(
            "let-slot-free-in-value",
            [("app", L, V(0)), ("app", L, V(1))],
            [RULES["let-unused"]],
            [("app", L, V(0)), ("app", L, V(1)), ("app", L, S("cc"))],
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
        return ("sym", rng.choice(SYMS))

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
            return ("app", ("app", MAP, sub()), ("app", ("app", MAP, sub()), sub()))
        if which == 1:  # map-fission
            s = slot()
            return ("app", MAP, ("lam", s, ("app", sub(), sub([s]))))
        if which == 2:  # let-intro / beta shape
            s = slot()
            return ("app", ("lam", s, sub([s])), sub())
        if which == 3:  # eta
            s = slot()
            return ("lam", s, ("app", sub(), ("var", s)))
        if which == 4:  # let-var-same
            s = slot()
            return ("let", s, ("var", s), sub())
        s = slot()  # a plain let
        return ("let", s, sub([s]), sub())

    r = rng.random()
    if r < 0.55:
        return ("app", sub(), sub())
    s = slot()
    if r < 0.85:
        return ("lam", s, sub([s]))
    return ("let", s, sub([s]), sub())


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
    probes += [("lam", 90, ("app", S("f1"), V(90))), S("f1")]
    return Case(f"fuzz{i}", [t], list(rules), probes, rounds=3)


def check_vacuity(case):
    """A blocked case only tests the guard if dropping the guard changes the answer.

    Returns a failure string when it does not -- i.e. when the case would pass
    just as well with the condition deleted, which means it is testing nothing.
    """
    stripped = [Rule(r.name, r.atoms, r.rhs_root, r.rhs, conds=(), fresh=r.fresh) for r in case.rules]
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


# ------------------------------------------------------- the runnable .egg form
EGG_HEADER = """;;; GENERATED by `python3 slotted/xdiff/xarray.py egg` -- do not edit.
;;;
;;; The paper's S4.1 functional array language (Listing 1) and 8 of its 9 rules,
;;; compiled into the encoding by the recipe in `slotted/encoding/user-rules.egg`.
;;; `slotted/xdiff/xarray.py` runs the same rules against the reference
;;; `slotted-egraphs` crate; this file is the runnable, self-checking half.
;;;
;;; The language and the rules are `slotted/languages/array.egg`, written in the slotted
;;; language -- one constructor per operator, the shape the reference's
;;; `define_language!` produces -- with `array.ref` beside it saying what the reference
;;; calls each one:
;;;
;;;   Lam(Bind<body>)          (lam $x b)      (Lam {0->x} (Var 0) mb b)
;;;   App(a, b)                (app a b)       (App ma a mb b)
;;;   Let(Bind<body>, value)   (let $x b e)    (Let {0->x} (Var 0) mb b me e)
;;;   Var(Slot)                (var $x)        an edge {0->x} to the `(Var 0)` class
;;;   Symbol / Number          map, f1, 7      (Sym "map"), (Num 7)
;;;
;;; `Lam` and `Let` bind their column 0 because that file's `:binder` says so, so the
;;; binder rules below are generated from the same declaration these terms are.
;;;
;;; Direct-substitution `beta` is left out because the paper's own array benchmark
;;; uses the let-based explicit-substitution rules instead (footnote 4). Both sides do
;;; support the substitution action; SDQL's `beta` compares that path separately.
;;;
;;; Each section is its own (push)/(pop). Two terms are in one slotted e-class when
;;; they reach a common leader, which is what every `check` below asks.

(include "@MACHINERY@")
"""


def egg_section(title, comment, case, want, atom_order=None):
    """One (push)/(pop) block: the rules, the term, the probes, and the check that
    probe 0 and probe 1 do (or do not) reach a common leader."""
    out = ["", ";" * 78, f";;; {title}"]
    for line in comment.strip().splitlines():
        out.append(f";;; {line.strip()}")
    out += [";" * 78, "(push)", ""]
    for r in case.rules:
        out.append(f";; {r.name}")
        out.append(compile_array_rule(r, atom_order))
        out.append("")
    for i, t in enumerate(case.terms):
        if t in case.probes[:2]:
            continue  # already added below, under its own name
        out.append(f";; {sexpr(t)}")
        out.append(f"(let $t{i} {enc(t)})")
    for i, t in enumerate(case.probes[:2]):
        out.append(f";; {sexpr(t)}")
        out.append(f"(let $p{i} {enc(t)})")
    out.append("")
    out.append(schedule(case.rounds * 3))
    chk = "(check (RenamesToLeader $p0 m1 l)\n       (RenamesToLeader $p1 m2 l))"
    out.append(chk if want else f"(fail {chk})")
    out += ["", "(pop)"]
    return "\n".join(out)


def drop_conds(case):
    return Case(
        case.name,
        case.terms,
        [Rule(r.name, r.atoms, r.rhs_root, r.rhs, (), r.fresh) for r in case.rules],
        case.probes,
        case.rounds,
        case.unions,
    )


def emit_egg():
    out = [EGG_HEADER.replace("@MACHINERY@", MACHINERY)]
    for c in per_rule_cases():
        blocked = c.name.endswith("blocked")
        out.append(
            egg_section(
                c.name,
                "probe 0 is the rule's left-hand side, probe 1 what it produces."
                if not blocked
                else "the rule must NOT fire here, so the two probes stay apart.",
                c,
                want=not blocked,
            )
        )
        if blocked and any(r.conds for r in c.rules):
            # the negative above is only a test if the guard is what stops it
            out.append(
                egg_section(
                    c.name + "-without-the-guard",
                    "the same e-graph with the side condition deleted: now it does\n"
                    "fire, which is what makes the negative above non-vacuous.",
                    drop_conds(c),
                    want=True,
                )
            )
    # the leading atom must not matter
    c = next(x for x in per_rule_cases() if x.name == "map-fission-fires")
    out.append(
        egg_section(
            "map-fission-fires-from-atom-2",
            "the same rule flattened with a different atom leading. The reference\n"
            "receives the same unordered MultiPattern atoms.",
            c,
            want=True,
            atom_order=2,
        )
    )
    # the paper's transformation, on the smallest program that needs all 8 rules
    g = goal_cases([0], 10, wrap_lams=False, nfun=2, dims=1)[0]
    out.append(
        egg_section(
            g.name,
            "the paper's (A) -> (B): map over a fused pipeline becomes two maps with\n"
            "an intermediate. Needs all 8 rules -- fission introduces the binder and\n"
            "the let-rules push the resulting application through it.",
            g,
            want=True,
        )
    )
    out.append("""
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; A `let` whose bound slot is also free in its VALUE.
;;;
;;; `let x = x in f1 x`.  The paper's `Let(RenamedId, Bind<RenamedId>)` -- and the
;;; reference's `Let(Bind<AppliedId>, AppliedId)` -- puts the `Bind` on the body
;;; column alone, so the value's `x` is the ambient one and the class keeps the
;;; slot.  Stripping the bound slot from the node's whole slot set instead would leave
;;; the class with no slots and merge two terms the reference keeps apart, and it
;;; disagreed before any rule ran.  `:binder` covers ONE column -- the one after the
;;; binder slots,
;;; which is what `Bind<T>` wrapping a single child means -- so a bound slot is
;;; removed only where it is bound, and an occurrence in an uncovered column stays
;;; free.  `xarray.py extra` is the comparison this came from.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(push)

(let $B (App (map-empty) (Sym "f1") (map-of 0 0) (Var 0)))
(let $L (Let (map-of 0 0) (Var 0) (map-of 0 0) $B (map-of 0 0) (Var 0)))
(run-schedule (saturate (run slotted)))

;; the value's occurrence keeps the slot free, so the class has exactly one
(check (= (ClassSlots $L) (map-of 0 0)))
(check (RenamesToLeader $L m $L) (= (map-length m) 1))

;; and the two applications below stay apart, as they do in the reference
;; the edge to $L must cover its slot now that it has one
(let $a0 (App (map-of 0 0) $L (map-of 0 0) (Var 0)))
(let $a1 (App (map-of 0 0) $L (map-of 0 1) (Var 0)))
(run-schedule (saturate (run slotted)))
(fail (check (RenamesToLeader $a0 m1 l) (RenamesToLeader $a1 m2 l)))

(pop)
""")
    return "\n".join(out) + "\n"


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
            print(compile_array_rule(r))
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
        import isomorphism as I

        I.EGG_PROGRAM = egg_program
        I.use_language(LANG)
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

    if args and args[0] == "egg":
        dest = ROOT / "target" / "slotted" / "slotted-array-rules.egg"
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_text(emit_egg())
        print(f"wrote {dest}")
        return 0

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
