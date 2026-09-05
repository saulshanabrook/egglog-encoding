#!/usr/bin/env python3
"""Differential tester: the egglog slotted encoding's multipattern matching
against the reference `slotted-egraphs` implementation.

For each generated case it builds one spec, runs it through both sides, and
compares the resulting partition of the probe terms:

  reference   slotted/xmulti  (reads the spec on stdin)
  encoding    a generated .egg file run through target/debug/egglog

It also checks two things that need no cross-system comparison:

  order independence  the encoding's answer must not depend on the order the
                      atoms are compiled in (the reference's does not)
  machinery baseline  with no rule at all, both sides must already agree, so a
                      mismatch is attributed to matching rather than to the
                      encoding of union/congruence/redundancy

Usage:
    ./xdiff.py            run the curated cases
    ./xdiff.py fuzz 200   run 200 random cases
"""

import itertools
import os
import random
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "slotted"))
slotenc = __import__("slotted-encoder")
EGGLOG = ROOT / "target" / "debug" / "egglog"
XMULTI = ROOT / "slotted" / "xmulti"
MACHINERY = "target/slotted/slotted-lang-toy.egg"

BINOPS = ["add", "f", "g", "h", "k", "sub", "sub2"]

# Permutations tried per case in the order-independence check. Each costs a full
# saturation on both sides, so this is the main knob on runtime.
PERM_CAP = 4

# Some generated e-graphs blow the machinery up, so every run is bounded and a
# timeout is reported as its own category rather than stalling the sweep.
RUN_TIMEOUT = 25

# Past bugs, re-introducible so the corpus can be checked for still catching
# them. A bug nothing fails under is a bug that could come back unnoticed.
#   XDIFF_BUGS=root-only   an atom's renaming solved from its root alone
#   XDIFF_BUGS=slot-late   a slot literal checked after the renaming, not with it
#   XDIFF_BUGS=unordered   atoms compiled in the order written
#   XDIFF_BUGS=union-id    the action unions classes instead of invocations
#
# `mutations.py` asserts that each of these still breaks the corpus by a recorded amount, so
# a mutation that stops discriminating is a failure rather than a quiet gap. Two were removed
# once they stopped: `wide-kids` (only the root narrowed to its class's slots), whose property
# `def4-edges.py` checks directly, and `binder-1st` (a binder allowed to fix the pattern's
# slot space), which violates a definition rather than an observable.
BUGS = {b for b in os.environ.get("XDIFF_BUGS", "").split(",") if b}


# How often a generated subterm is a binder. Raise it to search binder-heavy
# ground: XDIFF_LAM=0.55
LAM_PROB = float(os.environ.get("XDIFF_LAM", "0.2"))

# How often a union equates a term with its own slot-swap, which is what gives a class
# a non-trivial symmetry group. Raise it to search symmetry-heavy ground: XDIFF_SYM=0.9
SYM_PROB = float(os.environ.get("XDIFF_SYM", "0.35"))

# ---------------------------------------------------------------- neutral terms
# term := ('var', n) | ('null',) | (op, t1, t2) | ('lam', ('var', n), body)
#
# The language is `slotted/languages/toy.egg`, one constructor per
# operator, with `toy.ref` beside it saying what the reference calls each one. Nothing
# here restates a signature or a binder column: `Lam` binds its column 0 because that
# file's `:binder` says so, so this cannot disagree with the rules generated for it.
LANG_DIR = ROOT / "slotted" / "languages"
LANG = slotenc.language(LANG_DIR / "toy.egg", LANG_DIR / "toy.ref")

# `BINOPS` is what generated terms are built from, so it must be every operator that
# takes two children and binds neither -- read off the language rather than restated.
# `op == o.name` skips the constructor aliases `language()` adds, so this compares
# operator names with operator names.
assert sorted(op for op, o in LANG.ops.items() if op == o.name and len(o.kid_cols) == 2 and not o.binders) == BINOPS, (
    f"BINOPS and toy.egg disagree: {BINOPS}"
)

slots, enc, sexpr, shift_term = LANG.slots, LANG.enc, LANG.sexpr, LANG.shift


def swap_slots(t, s1, s2):
    """`t` with slots `s1` and `s2` exchanged."""
    if t[0] == "var":
        return ("var", s2 if t[1] == s1 else s1 if t[1] == s2 else t[1])
    if t[0] == "null":
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


# ------------------------------------------------------------------------ specs


class Case:
    """One e-graph, one rule *set*, and the probes whose partition is compared.

    A rule is `(atoms, action)` or `(atoms, action, conds)`, where a condition is
    `(want, slot, pvars)`: `want` says whether the slot should be among the slots of
    any listed variable. Pass `rules=[...]` for a set, or the single-rule
    `atoms, action` form; `case.atoms` and `case.action` then read rule 0, which is
    what the single-rule checks and `show` use.
    """

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
        out = [f"rounds {self.rounds}"]
        out += [f"term {sexpr(t)}" for t in self.terms]
        out += [f"union {sexpr(a)} {sexpr(b)}" for a, b in self.unions]
        for atoms, action, conds in rules:
            if not atoms:
                continue
            # the separator is only needed from the second rule on, but emitting it
            # always keeps the spec readable
            out.append("rule")
            out += [f"atom {r} {o} {c1} {c2}" for (r, o, c1, c2) in atoms]
            for want, slot, pvars in conds:
                kind = "in" if want else "notin"
                out.append(f"cond {kind} {slot} {' '.join(pvars)}")
            if action and len(action) == 2:
                out.append(f"rhs {action[0]} {rhs_text(action[1])}")
            elif action:
                out.append("action {} {} {} {}".format(*action))
        out += [f"probe {sexpr(t)}" for t in self.probes]
        return "\n".join(out) + "\n"


def rhs_text(t):
    """An RHS tree as reference pattern text: `(h (g ?a ?b) ?b)`."""
    return slotenc.pat_sexpr(LANG, slotenc.rhs_of(LANG, t))


# Cases with an accepted invariant violation, and how many. Def. 4 says an edge's
# domain is exactly its child's slot set -- the reference asserts it outright, in
# `check_internal_applied_id`. The encoding does not enforce it, and `X1` reaches a
# state that breaks it; that is recorded here so a *new* violation still fails.
# An idempotent self-loop on the child is a partial identity, so the child's live
# slots are inside its domain: one with fewer keys than the edge proves the edge names
# slots the child does not have. Only narrower witnesses are used, which is what makes
# this immune to the too-wide self-loops of open question 2.
INVARIANT_OBS = """
(ruleset inv)
(relation WideEdge (String Renaming U Renaming))
(relation NotInjective (Renaming))
"""


def _invariant_rules():
    out = [INVARIANT_OBS]
    for n in (2, 3, 4):
        cols = " ".join(f"m{i} c{i}" for i in range(1, n + 1))
        for i in range(1, n + 1):
            out.append(
                f"(rule ((= v (App{n} f {cols}))\n"
                f"       (RenamesToLeader c{i} s c{i})\n"
                f"       (= s (compose s s))\n"
                f"       (< (map-length s) (map-length m{i})))\n"
                f"      ((WideEdge f m{i} c{i} s)) :ruleset inv)"
            )
            out.append(
                f"(rule ((= v (App{n} f {cols}))\n"
                f"       (!= (map-length m{i}) (map-length (map-image m{i}))))\n"
                f"      ((NotInjective m{i})) :ruleset inv)"
            )
    out.append(
        "(rule ((RenamesToLeader a m b)"
        " (!= (map-length m) (map-length (map-image m))))"
        " ((NotInjective m)) :ruleset inv)"
    )
    out += ["(run inv 1)", "(print-size WideEdge)", "(print-size NotInjective)"]
    return "\n".join(out)


def check_invariants(case):
    """Wide edges and non-injective renamings, observed after a user step.

    The observers run in their own ruleset so they see a snapshot rather than a history: a
    relation keeps an observation after the row that caused it is deleted.

    One extra user step runs first, *without* the machinery saturation that normally
    follows it. Saturating the invariant rules repairs a malformed edge, so observing after
    that would report a clean state whatever the action wrote. The contract being checked is
    the stronger one: an action must not write an edge that breaks Def. 4, even transiently.
    """
    prog = egg_program(case).replace("(print-function SameClass 100000)", "(run-schedule (run))\n" + _invariant_rules())
    path = ROOT / f"xdiff-inv-{os.getpid()}.egg"
    path.write_text(prog)
    try:
        r = subprocess.run([str(EGGLOG), str(path)], capture_output=True, text=True, timeout=RUN_TIMEOUT, cwd=ROOT)
    except subprocess.TimeoutExpired:
        return None
    finally:
        path.unlink(missing_ok=True)
    if r.returncode != 0:
        return None
    nums = [int(x.strip()) for x in r.stdout.splitlines() if x.strip().isdigit()]
    return tuple(nums[-2:]) if len(nums) >= 2 else None


def check_encodable(case):
    """Reject a case the encoding cannot represent faithfully.

    A `U` value is an e-node, not an invocation, so a bare `(var $k)` at top level
    encodes as `(Var 0)` for every k -- the slot is lost. Such a case is not a
    faithful translation, and it is not shift-equivalent either, since shifting
    changes what it means on one side only. Slots inside a compound term ride in
    the stored edges and are fine; `null` has no slot to lose.

    This has been mistaken for a machinery bug twice. Use a compound term with the
    same slots instead -- `LEAF0` below.
    """
    tops = list(case.terms) + list(case.probes)
    for a, b in case.unions:
        tops += [a, b]
    bad = [t for t in tops if t[0] == "var"]
    if bad:
        raise AssertionError(
            f"{case.name}: bare leaf at top level {bad} -- the encoding cannot "
            f"carry its slot; use a compound term with the same slots"
        )


# -------------------------------------------------------------- rule compiler
def _child(c):
    """An atom's child, in the encoder's grammar. A child written `$v` is a slot
    literal, not a pattern variable: the encoding stores a binder's slot as an edge
    to `(Var 0)`, so the child position is that literal class."""
    return ("sl", c) if c.startswith("$") else ("pv", c)


def compile_rule(atoms, action, conds=()):
    """Compile a flattened multipattern into an egglog rule, through the encoder.

    Nothing here is the recipe -- `slotted-encoder.compile_rule` is. This is the
    harness's spelling of a rule translated into the encoder's: an atom is written
    `(root, op, c1, c2)` over bare names, and an action either `(root, rhs-tree)` or
    the flat `(root, op, a, b)`, whose `=` equates two variables.

    The flat form builds one depth-1 node over bound variables; `union-id` is the
    mutation that concludes it with egglog's `union` instead, which is only correct
    when both renamings are the identity.
    """
    atoms = slotenc.connected_order(LANG, [(r, o, [_child(c1), _child(c2)]) for r, o, c1, c2 in atoms], bugs=BUGS)
    if len(action) == 2:
        root, rhs = action
        act = ("build", root, slotenc.rhs_of(LANG, rhs))
    elif action[1] == "=":
        act = ("build", action[0], ("pv", action[2]))
    else:
        root, op, a, b = action
        act = ("row", root, op, [a, b])
    return slotenc.compile_rule(LANG, atoms, act, conds=conds, bugs=BUGS)


# -------------------------------------------------------------- egg generation
def schedule(steps):
    """`steps` user-rule iterations, with the slotted invariants saturated between them.

    The invariant rules maintain the encoding, and a user rule that matches a node before
    its alpha- and slot-canonicalisation has finished sees a spelling about to change --
    and matches again when it does, so neither settles. User rules are not expected to
    terminate, so they get a finite step count while the machinery gets `saturate`. This
    is the shape egglog's proof encoding uses for its own maintenance rulesets, where
    `instrument_schedule` wraps every user run as `(seq <run> <rebuild>)`.
    """
    return (
        f"(run-schedule (saturate (run slotted))\n              (repeat {steps} (seq (run) (saturate (run slotted)))))"
    )


def egg_program(case, rules=None, mult=3):
    rules = case.rules if rules is None else rules
    out = [f'(include "{MACHINERY}")']
    # A slotted e-class is NOT one egglog e-class: the alpha-finder relates
    # equal-up-to-renaming nodes with `RenamesToLeader` and deletes one, rather
    # than unioning them. So two probes are in the same slotted class when they
    # reach a common leader, which is also what the machinery's own tests check.
    out.append("(relation ProbeId (U i64))")
    out.append("(relation SameClass (i64 i64))")
    out.append(
        "(rule ((ProbeId a i) (ProbeId b j)\n"
        "       (RenamesToLeader a m1 l) (RenamesToLeader b m2 l))\n"
        "      ((SameClass i j)))"
    )
    # Two of a case's rules can compile to the SAME text -- the generator draws each
    # independently -- and egglog rejects a rule it already has, panicking with "was
    # already present" and taking the whole case down. A repeated rule means nothing
    # extra anyway, so emit each once.
    seen_rules = set()
    for atoms, action, conds in rules:
        if not atoms:
            continue
        text = compile_rule(atoms, action, conds)
        if text not in seen_rules:
            seen_rules.add(text)
            out.append(text)
    for i, t in enumerate(case.terms):
        out.append(f"(let _t{i} {enc(t)})")
    for i, (a, b) in enumerate(case.unions):
        out.append(f"(let _ua{i} {enc(a)})")
        out.append(f"(let _ub{i} {enc(b)})")
        out.append(f"(union _ua{i} _ub{i})")
    for i, t in enumerate(case.probes):
        out.append(f"(let _p{i} {enc(t)})")
    out.append(schedule(case.rounds * mult))
    for i, _ in enumerate(case.probes):
        out.append(f"(ProbeId _p{i} {i})")
    out.append(schedule(case.rounds * mult))
    out.append("(print-function SameClass 100000)")
    return "\n".join(out) + "\n"


def parse_same_class(stdout, n):
    """Turn the printed SameClass rows into the same canonical string the
    reference prints."""
    pairs = set()
    for line in stdout.splitlines():
        line = line.strip()
        if not line.startswith("(SameClass "):
            continue
        nums = line[len("(SameClass ") :].split(")")[0].split()
        pairs.add((int(nums[0]), int(nums[1])))
    parent = list(range(n))

    def find(x):
        while parent[x] != x:
            x = parent[x]
        return x

    for i, j in pairs:
        a, b = find(i), find(j)
        if a != b:
            parent[max(a, b)] = min(a, b)
    groups = {}
    for i in range(n):
        groups.setdefault(find(i), []).append(i)
    gs = sorted("[" + ",".join(str(i) for i in sorted(v)) + "]" for v in groups.values())
    # every probe is added, so nothing is ever missing on this side
    return "".join(gs) + " missing[[]]"


# ------------------------------------------------------------------ the runners
def run_reference(case, rules=None):
    try:
        r = subprocess.run(
            [str(XMULTI / "target" / "debug" / "xmulti")],
            input=case.spec(rules),
            capture_output=True,
            text=True,
            timeout=RUN_TIMEOUT,
        )
    except subprocess.TimeoutExpired:
        return ("TIMEOUT", f">{RUN_TIMEOUT}s")
    if r.returncode != 0:
        return ("ERROR", r.stderr.strip().splitlines()[-1] if r.stderr else "?")
    part, sat = None, True
    for line in r.stdout.splitlines():
        if line.startswith("PARTITION "):
            part = line[len("PARTITION ") :].strip()
        elif line.startswith("SATURATED "):
            sat = line.split()[1] == "yes"
    if part is None:
        return ("ERROR", "no PARTITION line")
    return ("OK" if sat else "UNSATURATED", part)


def run_encoding(case, rules=None, keep=None, mult=3):
    prog = egg_program(case, rules, mult)
    # per-process, so two harness runs cannot clobber each other
    path = keep or (ROOT / f"xdiff-tmp-{os.getpid()}.egg")
    path.write_text(prog)
    try:
        r = subprocess.run(
            [str(EGGLOG), str(path)],
            capture_output=True,
            text=True,
            timeout=RUN_TIMEOUT,
            cwd=ROOT,
        )
    except subprocess.TimeoutExpired:
        return ("TIMEOUT", f">{RUN_TIMEOUT}s (program kept at {path})")
    if r.returncode != 0:
        err = [line for line in r.stderr.splitlines() if "ERROR" in line]
        msg = err[-1] if err else r.stderr.strip()[:400]
        return ("ERROR", f"{msg}\n    (program kept at {path})")
    return ("OK", parse_same_class(r.stdout, len(case.probes)))


# ------------------------------------------------------------------ the checks
def check_case(case, verbose=False, stats=None):
    """Returns a list of failure strings (empty when the case agrees).

    `stats` accumulates counters: how many cases had a usable baseline, and of
    those, how many had the rule actually change something -- a case where the
    rule never fires tests nothing about matching.
    """
    fails = []
    if stats is None:
        stats = {}
    check_encodable(case)

    # 1. machinery baseline: no rule, both sides must already agree
    bare = Case(case.name, case.terms, case.unions, [], None, case.probes, case.rounds)
    rs, rv = run_reference(bare, rules=[])
    es, ev = run_encoding(bare, rules=[])
    if rs == "TIMEOUT" or es == "TIMEOUT":
        return [f"{case.name}: baseline timeout ref={rs} enc={es}"]
    if rs != "OK" or es != "OK":
        return [f"{case.name}: baseline crashed ref={rs}:{rv} enc={es}:{ev}"]
    if rv != ev:
        return [f"{case.name}: BASELINE differs (machinery, not matching)\n    ref {rv}\n    enc {ev}"]

    stats["baseline_ok"] = stats.get("baseline_ok", 0) + 1
    baseline = rv

    # 2. the rule, in the written atom order
    rs, rv = run_reference(case)
    es, ev = run_encoding(case)
    if rs == "OK" and rv != baseline:
        stats["fired"] = stats.get("fired", 0) + 1
    if rs == "TIMEOUT" or es == "TIMEOUT":
        return [f"{case.name}: rule timeout ref={rs} enc={es}"]
    if rs == "UNSATURATED":
        return [f"{case.name}: unsaturated, excluded (reference hit its round cap)"]
    if rs != "OK":
        return [f"{case.name}: reference crashed: {rv}"]
    if es != "OK":
        fails.append(f"{case.name}: encoding crashed: {ev}")
        return fails
    if rv != ev:
        fails.append(f"{case.name}: MISMATCH vs reference\n    ref {rv}\n    enc {ev}")

    # 3. did both sides reach a fixpoint? If not, they ran different amounts of
    # work and comparing them says nothing, so the case is excluded. The
    # reference reports this itself; the encoding is checked by running twice as
    # many iterations and requiring the same answer -- which doubles as a
    # determinism check.
    ds, dv = run_encoding(case, mult=6)
    if rs == "UNSATURATED" or ds == "UNSATURATED":
        return [f"{case.name}: unsaturated, excluded (ref={rs} enc={ds})"]
    if ds == "OK" and dv != ev:
        return [
            f"{case.name}: unsaturated or nondeterministic in the encoding\n"
            f"    {case.rounds * 3} iterations {ev}\n"
            f"    {case.rounds * 6} iterations {dv}"
        ]

    # 4. order independence, both sides. Every distinct reordering for 2-3 atoms;
    # a sample beyond that, since each costs a full saturation on both sides. The
    # original order is excluded -- rerunning it would test determinism, not order.
    # With a rule set, the same permutation index is applied to every rule rather
    # than taking the product of their orderings.
    widest = max(len(a) for a, _, _ in case.rules) if case.rules else 0
    if widest > 1:
        perms = [p for p in itertools.permutations(range(widest)) if list(p) != list(range(widest))]
        if len(perms) > PERM_CAP:
            perms = random.Random(0).sample(perms, PERM_CAP)
        ref_vals, enc_vals = {rv}, {ev}
        for p in perms:
            reordered = [([a[k] for k in p if k < len(a)], act, cs) for a, act, cs in case.rules]
            xs, x = run_reference(case, rules=reordered)
            ys, y = run_encoding(case, rules=reordered)
            # A timeout or crash is not a partition; folding it into the value
            # set would report spurious order dependence.
            if xs == "OK":
                ref_vals.add(x)
            if ys == "OK":
                enc_vals.add(y)
        if len(ref_vals) > 1:
            fails.append(f"{case.name}: REFERENCE is order dependent: {sorted(ref_vals)}")
        if len(enc_vals) > 1:
            fails.append(f"{case.name}: ENCODING is order dependent: {sorted(enc_vals)}")

    # 5. slot-renaming invariance: shifting every slot in the program must not
    # change either side's answer.
    shifted = shift_case(case, 40)
    xs, xv = run_reference(shifted)
    ys, yv = run_encoding(shifted)
    if xs == "OK" and xv != rv:
        fails.append(f"{case.name}: REFERENCE is not slot-renaming invariant\n    as written {rv}\n    slots +40  {xv}")
    if ys == "OK" and yv != ev:
        fails.append(f"{case.name}: ENCODING is not slot-renaming invariant\n    as written {ev}\n    slots +40  {yv}")

    # 6. the encoding's own well-formedness: an edge's domain is its child's slot
    # set (Def. 4), and a stored renaming is injective. Neither is visible in a
    # partition, so agreeing with the reference does not imply either.
    got = check_invariants(case)
    if got is not None:
        wide, noninj = got
        allowed = 0
        if wide > allowed:
            fails.append(f"{case.name}: INVARIANT wide edges {wide}, expected at most {allowed}")
        if noninj:
            fails.append(f"{case.name}: INVARIANT non-injective renamings {noninj}")

    if verbose and not fails:
        print(f"  ok  {case.name}  {rv}")
    return fails


# ------------------------------------------------------------- curated corpus
V0, V1, V2 = ("var", 0), ("var", 1), ("var", 2)
# A compound term whose only slot is V0, for the top-level positions
# where a bare leaf would lose its slot (see check_encodable).
LEAF0 = ("sub", V0, V0)
NUL = ("null",)


def curated():
    cs = []

    # C1 -- plain repeated variable, live slots
    cs.append(
        Case(
            "C1-repeat-live",
            [("f", V0, V1), ("f", V0, V0)],
            [],
            [("p", "f", "x", "x")],
            ("p", "h", "x", "x"),
            [("f", V0, V1), ("f", V0, V0), ("h", V0, V0)],
        )
    )

    # C2 -- chain
    cs.append(
        Case(
            "C2-chain",
            [("f", V0, ("g", V0, V1))],
            [],
            [("p", "f", "a", "b"), ("b", "g", "c", "d")],
            ("p", "h", "c", "d"),
            [("f", V0, ("g", V0, V1)), ("h", V0, V1), ("h", V1, V0)],
        )
    )

    # C3 -- join on two shared variables
    cs.append(
        Case(
            "C3-join",
            [("f", V0, V1), ("g", V0, V1)],
            [],
            [("p", "f", "x", "y"), ("q", "g", "x", "y")],
            ("p", "h", "x", "y"),
            [("f", V0, V1), ("g", V0, V1), ("h", V0, V1)],
        )
    )

    # C4 -- symmetry: the two occurrences agree only through a swap
    cs.append(
        Case(
            "C4-symmetry",
            [("f", ("k", V0, V1), ("k", V1, V0))],
            [(("k", V0, V1), ("k", V1, V0))],
            [("p", "f", "x", "x")],
            ("p", "h", "x", "x"),
            [("f", ("k", V0, V1), ("k", V1, V0)), ("h", ("k", V0, V1), ("k", V0, V1))],
        )
    )

    # C5 -- R1: one redundant-slot node reached through two atoms
    cs.append(
        Case(
            "C5-redundant-same-node",
            [("add", NUL, NUL)],
            [(("sub", V0, V0), NUL)],
            [("p", "add", "a", "b"), ("a", "sub", "u", "u"), ("b", "sub", "u", "u")],
            ("p", "h", "u", "u"),
            [("add", NUL, NUL), ("h", V0, V0), NUL],
        )
    )

    # C6 -- R2: two different redundant-slot nodes, ?u forced across them
    cs.append(
        Case(
            "C6-redundant-two-nodes",
            [("add", NUL, NUL)],
            [(("sub", V0, V0), NUL), (("sub2", V1, V1), NUL)],
            [("p", "add", "a", "b"), ("a", "sub", "u", "u"), ("b", "sub2", "u", "u")],
            ("p", "h", "u", "u"),
            [("add", NUL, NUL), ("h", V0, V0), NUL],
        )
    )

    # C7 -- same, but the two atoms use DISTINCT variables
    cs.append(
        Case(
            "C7-redundant-distinct-vars",
            [("add", NUL, NUL)],
            [(("sub", V0, V0), NUL), (("sub2", V1, V1), NUL)],
            [("p", "add", "a", "b"), ("a", "sub", "u", "u"), ("b", "sub2", "v", "v")],
            ("p", "h", "u", "v"),
            [("add", NUL, NUL), ("h", V0, V0), ("h", V0, V1), NUL],
        )
    )

    # C8 -- a variable reached by two different paths, no redundancy
    cs.append(
        Case(
            "C8-two-paths",
            [("f", ("g", V0, V1), ("k", V0, V1))],
            [],
            [("p", "f", "a", "b"), ("a", "g", "x", "y"), ("b", "k", "x", "y")],
            ("p", "h", "x", "y"),
            [("f", ("g", V0, V1), ("k", V0, V1)), ("h", V0, V1), ("h", V1, V0)],
        )
    )

    # C9 -- redundancy meeting a live slot
    cs.append(
        Case(
            "C9-redundancy-and-live",
            [("f", V0, V1)],
            [(("g", V0, V1), ("g", V0, V2))],
            [("p", "f", "x", "y"), ("q", "g", "x", "y")],
            ("p", "h", "x", "y"),
            [("f", V0, V1), ("g", V0, V1), ("h", V0, V1)],
        )
    )

    # C10 -- three atoms, chain then join (the M7 shape)
    cs.append(
        Case(
            "C10-chain-then-join",
            [("f", V0, ("g", V0, V1)), ("k", V0, V0)],
            [],
            [("p", "f", "a", "b"), ("b", "g", "c", "d"), ("q", "k", "c", "a")],
            ("p", "h", "c", "d"),
            [("f", V0, ("g", V0, V1)), ("k", V0, V0), ("h", V0, V1)],
        )
    )

    # C11 -- regression for the action bug, found by `fuzz 150 2024` as fuzz56.
    #
    # The compiled action used to emit a plain `(union root built)`, which
    # asserts an equation whose two renamings are the identity. The root's
    # renaming here is {0->3, 2->2}, so that equation was false: it conflated
    # slot 0 with slot 3. The e-graph absorbed it as spurious redundancy -- the
    # `(Var 0)` class went from 1 live slot to 0 -- and child-update then emptied
    # every edge, collapsing h(x,y) with h(x,x). The reference refuses that, and
    # is right to: Def. 8 makes each lookup's renaming injective, so a node with
    # two distinct slots cannot represent h(x,x) (the crate pins this as
    # `regress::same_node_redundant_slots_stay_distinct`).
    #
    # It was also the only order-dependent case in 150, which fits: the two atoms
    # share no variable, so one of them mints, and the root's renaming -- hence
    # how wrong the union was -- depended on which atom went first.
    #
    # Worth knowing for the next such hunt: a `BadEdge` width check does NOT
    # catch this, because by the end the children's classes have gone slotless
    # too and the widths agree again.
    cs.append(
        Case(
            "C11-action-renamed-id-union",
            [NUL],
            [(("g", ("sub2", NUL, NUL), ("sub", V1, V0)), NUL), (("add", ("k", V2, NUL), ("k", V0, NUL)), LEAF0)],
            [("x3", "k", "x1", "x2"), ("x6", "k", "x4", "x5"), ("x7", "add", "x3", "x6")],
            ("x7", "h", "x3", "x6"),
            [
                NUL,
                ("g", ("sub2", NUL, NUL), ("sub", V1, V0)),
                ("add", ("k", V2, NUL), ("k", V0, NUL)),
                ("h", V0, V1),
                ("h", V0, V0),
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
            [("h", ("k", V0, V0), ("k", V2, V0))],
            [],
            [("x3", "k", "x1", "x2"), ("x6", "k", "x4", "x5"), ("x7", "h", "x3", "x6")],
            ("x7", "h", "x2", "x4"),
            [("h", ("k", V0, V0), ("k", V2, V0)), ("h", V0, V1), ("h", V0, V0), NUL, LEAF0],
            rounds=6,
        )
    )

    # C13 -- a three-atom body mixing a binder, a chain and a join.
    #
    # Found as a witness that the first atom must not be a binder, and
    # `connected_order` still avoids choosing one. It is NOT that witness any more,
    # and probably never was a clean one: its discrimination came from a union
    # whose operand was a bare leaf, which the encoding cannot represent
    # faithfully. With the leaf replaced no ordering disagrees, and 200
    # binder-dense generated cases with the restriction lifted found nothing. The
    # restriction is kept as conservative -- a bound slot in the pattern's slot
    # space is a real oddity, see open question 3 -- but it is unwitnessed.
    cs.append(
        Case(
            "C13-binder-chain-and-join",
            [("h", ("k", V2, NUL), ("lam", V0, V1))],
            [(("g", ("h", V2, NUL), ("lam", V2, V1)), LEAF0), (("h", NUL, V2), ("add", NUL, NUL))],
            [("x3", "k", "x1", "x2"), ("x5", "lam", "$s5", "x4"), ("x6", "h", "x3", "x5")],
            ("x6", "h", "x4", "x4"),
            [
                ("h", ("k", V2, NUL), ("lam", V0, V1)),
                ("g", ("h", V2, NUL), ("lam", V2, V1)),
                ("h", NUL, V2),
                ("h", V0, V1),
                ("h", V0, V0),
                NUL,
                LEAF0,
            ],
            rounds=6,
        )
    )

    # ---- ported from the reference's own test suite (tests/multipat) ----------
    # Where a test is not portable, it is listed under "Not ported" in
    # slotted-user-rules.md rather than approximated here.

    # regress::same_node_redundant_slots_stay_distinct. Unioning f's two-slot
    # term into a slotless one makes both slots redundant. A pattern that would
    # have to identify them must not match; one that keeps them apart must.
    red = [(("f", V0, V1), NUL)]
    cs.append(
        Case(
            "P1a-redundant-slots-may-not-collapse",
            [NUL],
            red,
            [("p", "f", "a", "a")],
            ("p", "h", "a", "a"),
            [NUL, ("f", V0, V1), ("h", V0, V0), ("h", V0, V1)],
        )
    )
    cs.append(
        Case(
            "P1b-redundant-slots-kept-apart",
            [NUL],
            red,
            [("p", "f", "a", "b")],
            ("p", "h", "a", "b"),
            [NUL, ("f", V0, V1), ("h", V0, V0), ("h", V0, V1)],
        )
    )

    # regress::live_slots_of_one_class_stay_distinct. Same question with no
    # redundancy at all: a class's own live slots are distinct.
    cs.append(
        Case(
            "P2a-live-slots-may-not-collapse",
            [("k", V0, V1)],
            [],
            [("p", "k", "u", "u")],
            ("p", "h", "u", "u"),
            [("k", V0, V1), ("h", V0, V0), ("h", V0, V1)],
        )
    )
    cs.append(
        Case(
            "P2b-live-slots-kept-apart",
            [("k", V0, V1)],
            [],
            [("p", "k", "u", "v")],
            ("p", "h", "u", "v"),
            [("k", V0, V1), ("h", V0, V0), ("h", V0, V1)],
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
            [("f", V2, NUL), ("k", V2, NUL)],
            [(("g", V1, NUL), ("k", NUL, V0))],
            [("x3", "f", "x1", "x2")],
            ("x1", "h", "x3", "x2"),
            [("f", V2, NUL), ("k", V2, NUL), ("g", V1, NUL), ("h", V0, V1), ("h", V0, V0), NUL, LEAF0],
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
            [(("h", NUL, V0), ("sub", V0, V0)), (("g", NUL, V2), ("sub", V0, V0))],
            [("x3", "h", "x1", "x2")],
            ("x1", "h", "x2", "x1"),
            [("h", NUL, V0), ("g", NUL, V2), ("sub", V0, V0), ("h", V0, V1), ("h", V0, V0), NUL, LEAF0],
            rounds=6,
        )
    )

    # X1 -- regression for the migration-truncation bug (FIXED). Found by
    # `fuzz 250 6161` as fuzz85, in the over-deriving direction: the encoding
    # merged h(x,y) with h(x,x), which the reference refuses because a node whose
    # two slots are distinct cannot represent h(x,x) (Def. 8's per-lookup
    # injectivity). See X2 for the minimal form and the mechanism.
    #
    # The action asserts ?x1 = h(?x3, ?x1) -- a node equal to its own child --
    # which merges the h class into the variable class. BOTH sides assert that
    # and both merge; the difference is only that the reference still keeps
    # h(x,x) apart afterwards. The encoding finishes with an h node whose two
    # edges are identical, `{2->2}` and `{2->2}`, to the same child class.
    #
    # Localised as far as: the encoding drives the VARIABLE class slotless (its
    # self-map reaches length 0) where the reference keeps its slot. Once the
    # variable class has no slots, collapsing h(x,y) with h(x,x) is *consistent* --
    # both are then h over the one slotless invocation -- so the error is upstream,
    # in whatever makes it slotless.
    #
    # Matching is not implicated: the reference matches the same things, including
    # both children at one invocation, and still saturates keeping h(x,x) apart.
    # The two sides agree after one round and diverge in the second.
    #
    # A length-TWO self-map is observed on the one-slot variable class along the
    # way, which is the "self-edges are derived from nodes" problem the doc lists
    # as an open question and calls probably harmless. This is evidence against
    # "harmless" and is the first thing to check.
    cs.append(
        Case(
            "X1-migration-must-not-truncate",
            [("add", ("sub2", V0, V0), NUL)],
            [(("h", V0, V2), NUL)],
            [("x3", "h", "x1", "x2")],
            ("x1", "h", "x3", "x1"),
            [("add", ("sub2", V0, V0), NUL), ("h", V0, V2), ("h", V0, V1), ("h", V0, V0), NUL, ("sub", V0, V0)],
            rounds=6,
        )
    )

    # X2 -- the minimal form, and the one that produced the diagnosis (FIXED).
    # `fuzz 250 6161` as fuzz206, which the per-use scheme had been hiding behind
    # a timeout. It needs ONE term and no unions; the h(v0,v0) probe is not even
    # required to drive the collapse.
    #
    # CAUSE, found by stepping the minimal case one iteration at a time: the
    # machinery's MIGRATION rule truncates a child edge. It rewrites
    # `e2 = f(m1*c1, m2*c2)` with `e2 = m*e1` into `e1 = f((m^-1.m1)*c1, ...)`,
    # and `compose` keeps only the keys whose value lies in the left map's domain.
    # When m1 reaches outside im(m) -- exactly when e2 has a slot that is
    # redundant in e1 -- the edge silently narrows. Here m = {0->0} and
    # m1 = {0->1} compose to the EMPTY map, and an empty edge to (Var 0) asserts
    # the variable class has no slots, after which every h(var, var) collapses.
    #
    # It is the same dropped-slot bug as M3, inside the machinery: the redundant
    # slot has no name in e1's space and gets dropped rather than named. Fixed by
    # guarding migration to decline when it would truncate -- sound but
    # incomplete, like M3(b); minting a fresh name would be the complete fix.
    #
    #     term   h(var $2, var $1)
    #     rule   ?c == (h ?a ?b)  =>  union ?a (h ?b ?c)
    #
    # The reference merges h(v2,v1) with h(v0,v1), which are alpha-variants, and
    # keeps h(v0,v0) apart. The encoding merges all three. As in X1 the variable
    # class goes slotless where the reference keeps its slot, and once it has no
    # slots the merge is consistent -- so the error is in whatever makes it
    # slotless.
    #
    # Unlike X1 no over-wide self-map appears here, which rules out "self-edges
    # are derived from nodes" as the cause. Both cases share one shape: the
    # action's root is a CHILD and the node it builds contains that child's own
    # parent, so the assertion relates a class to a node built over it.
    #
    # TRIGGER, minimised by varying only the action over one e-graph and pattern:
    #
    #     union ?a (h ?b ?c)   OVER-MERGES
    #     union ?a (h ?c ?b)   agrees          <- same variables, swapped
    #     union ?a (h ?b ?b)   agrees
    #     union ?a (h ?a ?b)   agrees
    #     union ?c (h ?a ?b)   agrees
    #     union ?a ?b          agrees
    #     union ?a ?c          agrees
    #
    # The reference gives the SAME answer for both argument orders; the encoding
    # does not. So the encoding is sensitive to which child position a class sits
    # in, and it over-merges only when the atom root -- the class the assertion is
    # about -- is the SECOND child. The machinery has separate child-update rules
    # for the first and second child, which is where to look.
    #
    # Ruled out along the way: malformed self-loops are a symptom (deleting them
    # does not help, and neither does guarding transitivity, which is what derives
    # them); it is not the refinement gap (writing the refinement into the pattern
    # makes both sides agree, and both keep the slots apart); and it is not
    # "self-edges derived from nodes" (no over-wide self-map appears here).
    #
    # Timeline: the variable class holds its slot for six egglog iterations and
    # loses it on about the seventh. Both sides do reach a fixpoint -- the
    # encoding agrees with itself at N and 2N iterations -- so this is not the
    # encoding being run longer than the reference. They saturate at DIFFERENT
    # fixpoints, which means the encoding has a derivation the reference does not,
    # reached only after the rule has fired on nodes the rule itself built.
    cs.append(
        Case(
            "X2-migration-truncation-minimal",
            [("h", V2, V1)],
            [],
            [("x3", "h", "x1", "x2")],
            ("x1", "h", "x2", "x3"),
            [("h", V2, V1), ("h", V0, V1), ("h", V0, V0), NUL, ("sub", V0, V0)],
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
    BR = ("f", ("k", V0, V1), ("g", V0, V1))
    cs.append(
        Case(
            "U1-two-pairings-across-two-lookups",
            [BR],
            [(BR, NUL)],
            [("p", "f", "x", "y"), ("q", "f", "x", "z")],
            ("p", "h", "y", "z"),
            [BR, NUL, ("h", ("g", V0, V1), ("g", V0, V1)), ("h", ("g", V0, V1), ("g", V1, V0))],
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
            [("f", V1, V2), ("f", V1, V1)],
            [],
            [("p", "f", "a", "b")],
            ("a", "=", "b", "b"),
            [("f", V1, V2), ("f", V1, V1), ("h", V0, V1), ("h", V0, V0)],
        )
    )

    # E2 -- the same, one atom deeper, through a chain.
    cs.append(
        Case(
            "E2-equate-through-a-chain",
            [("f", V0, ("k", V1, V2)), ("k", V1, V1)],
            [],
            [("p", "f", "a", "b"), ("b", "k", "c", "d")],
            ("c", "=", "d", "d"),
            [("f", V0, ("k", V1, V2)), ("k", V1, V1), ("k", V1, V2), ("h", V0, V0)],
        )
    )

    # E3 -- eta's shape: equate a binder with its own body, so one side is the
    # identity and the other carries the bound slot. Unsound as maths; the point
    # is that both sides derive the same thing from it.
    cs.append(
        Case(
            "E3-equate-binder-with-body",
            [("lam", V0, V0), ("f", V0, V1)],
            [],
            [("p", "lam", "$v", "b")],
            ("p", "=", "b", "b"),
            [("lam", V0, V0), ("f", V0, V1), ("f", V0, V0), ("h", V0, V0)],
        )
    )

    # ---- symmetries ----------------------------------------------------------
    # The encoding keeps a class's symmetries as self-loops in RenamesToLeader,
    # and a repeated variable is checked by computing the symmetry it would need
    # and looking it up. That only works if the stored set is CLOSED, not just a
    # set of generators: a lookup for a composite element has to succeed.
    #
    # `a` below has three slots and is given one 3-cycle. The parent then holds
    # `a` at the identity beside `a` at the cycle's SQUARE, which is never
    # unioned in, so `(f ?x ?x)` matches only if the square is stored too.
    A3 = ("k", ("g", V0, V1), V2)  # a, at the identity
    A3s = ("k", ("g", V1, V2), V0)  # a, under 0->1->2->0
    A3ss = ("k", ("g", V2, V0), V1)  # a, under the square of that
    cs.append(
        Case(
            "S1-symmetry-group-is-closed",
            [("f", A3, A3ss)],
            [(A3, A3s)],
            [("p", "f", "x", "x")],
            ("p", "h", "x", "x"),
            [("f", A3, A3ss), ("h", A3, A3), ("h", A3, A3s)],
        )
    )
    # control: without the 3-cycle there is no symmetry to find, so no match
    cs.append(
        Case(
            "S1b-no-symmetry-no-match",
            [("f", A3, A3ss)],
            [],
            [("p", "f", "x", "x")],
            ("p", "h", "x", "x"),
            [("f", A3, A3ss), ("h", A3, A3), ("h", A3, A3s)],
        )
    )

    # S2 -- symmetry and redundancy at once. A redundant slot is recorded as a
    # *partial* self-loop, so the self-loops are not a group but an inverse
    # monoid. The worry is a computed symmetry that came out short (composition
    # truncates) matching one of those partial maps and being accepted wrongly.
    # `a` keeps two live slots with a swap between them, and a third slot that a
    # union has made redundant. The parent holds `a` at the identity beside `a`
    # under the swap, so the match needs the real symmetry while a partial
    # self-loop is also present to be confused with it.
    Ar = ("k", ("g", V0, V1), V2)
    Arsw = ("k", ("g", V1, V0), V2)
    cs.append(
        Case(
            "S2-symmetry-beside-redundancy",
            [("f", Ar, Arsw)],
            [(Ar, Arsw), (Ar, ("k", ("g", V0, V1), NUL))],
            [("p", "f", "x", "x")],
            ("p", "h", "x", "x"),
            [("f", Ar, Arsw), ("h", Ar, Ar), ("h", Ar, Arsw)],
        )
    )

    # ---- binders -------------------------------------------------------------
    # The point of slotted e-graphs, and untested until now. `$v` is a slot
    # literal: the reference's `Bind` has no room for a pattern variable there.

    # B1 -- reading a binder's body, and chaining through it.
    cs.append(
        Case(
            "B1-binder-chain",
            [("lam", V0, ("f", V0, V1))],
            [],
            [("p", "lam", "$v", "b"), ("b", "f", "x", "y")],
            ("p", "h", "x", "y"),
            [("lam", V0, ("f", V0, V1)), ("h", V0, V1), ("h", V0, V0)],
        )
    )

    # B2 -- alpha-equivalence: two spellings of the identity function are one
    # class, so a rule matching one must fire for both.
    cs.append(
        Case(
            "B2-alpha-equivalent-binders",
            [("lam", V0, V0), ("lam", V1, V1)],
            [],
            [("p", "lam", "$v", "b")],
            ("p", "h", "b", "b"),
            [("lam", V0, V0), ("lam", V1, V1), ("h", V0, V0), ("h", V0, V1)],
        )
    )

    # B3 -- known_bugs::lambda_bug_reaches_the_goal_under_multipat. The pattern
    # writes `$x` for two binders that have nothing to do with each other. Each
    # equation looks its node up separately and gets its own name for that node's
    # bound slot, so setting both to `$x` constrains nothing and it matches --
    # which the nested matcher does not do.
    cs.append(
        Case(
            "B3-same-slot-literal-two-binders",
            [("f", ("lam", V0, V0), ("lam", V0, V0))],
            [],
            [("p", "f", "a", "b"), ("a", "lam", "$x", "c"), ("b", "lam", "$x", "d")],
            ("p", "h", "c", "d"),
            [("f", ("lam", V0, V0), ("lam", V0, V0)), ("h", V0, V0), ("h", V0, V1)],
        )
    )

    # B4 -- the same, with the two binders over different bodies.
    cs.append(
        Case(
            "B4-same-slot-literal-different-bodies",
            [("f", ("lam", V0, V0), ("lam", V0, ("f", V0, V1)))],
            [],
            [("p", "f", "a", "b"), ("a", "lam", "$x", "c"), ("b", "lam", "$x", "d")],
            ("p", "h", "c", "d"),
            [("f", ("lam", V0, V0), ("lam", V0, ("f", V0, V1))), ("h", V0, V0), ("h", V0, V1)],
        )
    )

    # ---- shapes taught by slotted/tests/user-rules.egg -----------------------
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
            [("f", V0, V1)],
            [],
            [("p", "f", "a", "b")],
            ("p", "f", "b", "a"),
            [("f", V0, V1), ("f", V1, V0), ("h", V0, V1)],
        )
    )

    # M3 -- only ONE variable shared, across two different operators, so the
    # second atom's renaming is pinned on part of its node and must mint a name
    # for the rest. `U1` has this shape with one operator; two make the join
    # unambiguous, which is what the doc's M3 discusses.
    cs.append(
        Case(
            "M3-one-shared-var-two-ops",
            [("f", V0, V1), ("g", V0, V2)],
            [],
            [("p", "f", "x", "y"), ("q", "g", "x", "z")],
            ("p", "h", "y", "z"),
            [("f", V0, V1), ("g", V0, V2), ("h", V1, V2), ("h", V1, V1)],
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
            [("f", V0, V1)],
            [],
            None,
            None,
            [("f", V0, V1), ("g", V0, V1), ("h", V0, V1), ("h", V1, V0)],
            rules=[([("p", "f", "a", "b")], ("p", "g", "a", "b")), ([("q", "g", "x", "y")], ("q", "h", "y", "x"))],
        )
    )

    # MR2 -- commutativity beside a renaming rule, so the second keeps feeding the
    # first new nodes to commute.
    cs.append(
        Case(
            "MR2-comm-plus-rename",
            [("add", LEAF0, ("g", V1, V1))],
            [],
            None,
            None,
            [
                ("add", LEAF0, ("g", V1, V1)),
                ("add", ("g", V1, V1), LEAF0),
                ("add", LEAF0, ("k", V1, V1)),
                ("k", V1, V1),
            ],
            rules=[([("p", "add", "a", "b")], ("p", "add", "b", "a")), ([("q", "g", "x", "y")], ("q", "k", "x", "y"))],
        )
    )

    # MR3 -- two rules over one shared operator, reaching the same class by
    # different routes.
    cs.append(
        Case(
            "MR3-two-routes",
            [("f", V0, V1), ("g", V0, V1)],
            [],
            None,
            None,
            [("f", V0, V1), ("g", V0, V1), ("h", V0, V1), ("h", V1, V0)],
            rules=[([("p", "f", "a", "b")], ("p", "h", "a", "b")), ([("q", "g", "x", "y")], ("q", "h", "y", "x"))],
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
            [("lam", V0, ("g", V1, V1)), ("lam", V0, ("g", V0, V0))],
            [],
            None,
            None,
            [("lam", V0, ("g", V1, V1)), ("g", V1, V1), ("lam", V0, ("g", V0, V0)), ("g", V0, V0)],
            rules=[([("p", "lam", "$s", "b")], ("p", "=", "b", "b"), [(False, "$s", ["b"])])],
        )
    )

    # CD2 -- the same rule where the condition fails: the body does use the bound
    # slot, so nothing may fire.
    cs.append(
        Case(
            "CD2-notin-blocks",
            [("lam", V0, ("g", V0, V0))],
            [],
            None,
            None,
            [("lam", V0, ("g", V0, V0)), ("g", V0, V0), ("g", V1, V1), NUL],
            rules=[([("p", "lam", "$s", "b")], ("p", "=", "b", "b"), [(False, "$s", ["b"])])],
        )
    )

    # CD3 -- `in`, the other direction.
    cs.append(
        Case(
            "CD3-in-fires",
            [("lam", V0, ("g", V0, V0)), ("lam", V0, ("g", V1, V1))],
            [],
            None,
            None,
            [("lam", V0, ("g", V0, V0)), ("lam", V0, ("g", V1, V1)), ("h", ("g", V0, V0), ("g", V0, V0)), NUL],
            rules=[([("p", "lam", "$s", "b")], ("p", "h", "b", "b"), [(True, "$s", ["b"])])],
        )
    )

    # CD4 -- a disjunction over two variables, which needs the condition as a value
    # rather than a fact. Again one match satisfies it and one does not.
    cs.append(
        Case(
            "CD4-in-either-decides",
            [("lam", V0, ("f", ("g", V0, V0), ("k", V1, V1))), ("lam", V0, ("f", ("g", V1, V1), ("k", V1, V1)))],
            [],
            None,
            None,
            [
                ("lam", V0, ("f", ("g", V0, V0), ("k", V1, V1))),
                ("h", ("g", V0, V0), ("k", V1, V1)),
                ("lam", V0, ("f", ("g", V1, V1), ("k", V1, V1))),
                ("h", ("g", V1, V1), ("k", V1, V1)),
            ],
            rules=[([("p", "lam", "$s", "x"), ("x", "f", "a", "b")], ("p", "h", "a", "b"), [(True, "$s", ["a", "b"])])],
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
            [("f", V0, V1)],
            [],
            None,
            None,
            [("f", V0, V1), ("h", ("g", V0, V1), V1), ("g", V0, V1), ("h", ("g", V1, V0), V0)],
            rules=[([("p", "f", "a", "b")], ("p", ("h", ("g", "a", "b"), "b")))],
        )
    )

    # NR2 -- two levels, and the same variable reused at different depths, which is
    # where a wrong slot set for an intermediate node would show up.
    cs.append(
        Case(
            "NR2-two-levels",
            [("f", V0, V1)],
            [],
            None,
            None,
            [("f", V0, V1), ("h", ("g", ("k", V0, V1), V0), V1), ("g", ("k", V0, V1), V0), ("k", V0, V1)],
            rules=[([("p", "f", "a", "b")], ("p", ("h", ("g", ("k", "a", "b"), "a"), "b")))],
        )
    )

    # NR3 -- associativity, the shape the paper's arith rules use: the right-hand
    # side regroups the same three variables.
    cs.append(
        Case(
            "NR3-assoc",
            [("add", LEAF0, ("add", ("g", V1, V1), ("k", V2, V2)))],
            [],
            None,
            None,
            [
                ("add", LEAF0, ("add", ("g", V1, V1), ("k", V2, V2))),
                ("add", ("add", LEAF0, ("g", V1, V1)), ("k", V2, V2)),
                ("add", LEAF0, ("g", V1, V1)),
                NUL,
            ],
            rules=[([("p", "add", "a", "x"), ("x", "add", "b", "c")], ("p", ("add", ("add", "a", "b"), "c")))],
        )
    )

    return cs


# ------------------------------------------------------------------- the fuzzer
def rand_term(rng, depth):
    if depth == 0 or rng.random() < 0.3:
        return rng.choice([("var", rng.randrange(3)), ("null",)])
    if rng.random() < LAM_PROB:
        return ("lam", ("var", rng.randrange(3)), rand_term(rng, depth - 1))
    op = rng.choice(BINOPS)
    return (op, rand_term(rng, depth - 1), rand_term(rng, depth - 1))


def flatten_to_atoms(t, ctr, rng=None):
    """Flatten a term into depth-1 atoms with fresh pvars, so the resulting
    multipattern is guaranteed to match that term. Leaves become bare pvars,
    which is what a multipattern does with them anyway."""
    if t[0] in ("var", "null"):
        ctr[0] += 1
        return f"x{ctr[0]}", []
    if t[0] == "lam":
        pb, ab = flatten_to_atoms(t[2], ctr, rng)
        ctr[0] += 1
        root = f"x{ctr[0]}"
        # a binder's slot must be a literal; reuse one sometimes, so that two
        # binders written with the same slot get exercised
        sl = "$s0" if rng is not None and rng.random() < 0.3 else f"$s{ctr[0]}"
        return root, ab + [(root, "lam", sl, pb)]
    op, a, b = t
    pa, aa = flatten_to_atoms(a, ctr, rng)
    pb, ab = flatten_to_atoms(b, ctr, rng)
    ctr[0] += 1
    root = f"x{ctr[0]}"
    return root, aa + ab + [(root, op, pa, pb)]


def rand_top(rng, depth):
    """A term safe to use at top level.

    A bare leaf cannot be encoded faithfully: an encoding `U` value is a *node*,
    not an invocation, so `(var $n)` collapses to `(Var 0)` and loses `n`. Then
    `union (var $0) (var $2)` -- a real statement about the variable class in the
    reference -- becomes a no-op in the encoding, and the two sides diverge for
    reasons that have nothing to do with matching. Slots inside a compound term
    ride in the stored edges and survive.
    """
    t = rand_term(rng, depth)
    if t[0] in ("var", "null"):
        t = (rng.choice(BINOPS), t, rand_term(rng, 0))
    return t


def rand_rule(rng, terms, unions):
    """One random rule: a pattern read off a term that is in the e-graph,
    then perturbed, plus an action over its bound variables."""
    # The pattern is read off a term that is actually in the e-graph, so it
    # matches by construction; then it is perturbed.
    seed_term = rng.choice(terms + [a for a, _ in unions])
    _, atoms = flatten_to_atoms(seed_term, [0], rng)
    if not atoms:
        atoms = [("r0", rng.choice(BINOPS), "u", "v")]

    # Perturbations make the pattern more interesting but often stop it matching
    # at all, and a case that never fires tests nothing. Half are left alone so
    # the sweep keeps a healthy share of firing cases.
    if rng.random() < 0.5:
        pvs = sorted({v for at in atoms for v in (at[2], at[3]) if not v.startswith("$")})
        # identify two child pvars (tests repeated-variable semantics)
        if pvs and rng.random() < 0.5:
            keep, drop = rng.choice(pvs), rng.choice(pvs)
            atoms = [(r, o, keep if c1 == drop else c1, keep if c2 == drop else c2) for (r, o, c1, c2) in atoms]
        # drop a trailing atom (leaves a pvar unconstrained)
        if len(atoms) > 1 and rng.random() < 0.3:
            atoms = atoms[:-1]
        # swap an atom's children -- never a binder's, whose slot has to stay
        # first: `(lam ?x $s)` is not valid syntax on the reference side.
        swappable = [j for j, a in enumerate(atoms) if a[1] != "lam"]
        if swappable and rng.random() < 0.4:
            j = rng.choice(swappable)
            r, o, c1, c2 = atoms[j]
            atoms[j] = (r, o, c2, c1)

    allv = sorted({v for at in atoms for v in (at[0], at[2], at[3]) if not v.startswith("$")})
    # Any bound variable can be the action's root, and it matters which: an atom
    # ROOT often has the identity for its renaming, so an action rooted there
    # cannot tell a union of classes from a union of invocations. A CHILD's
    # renaming is its stored edge, which generally is not the identity.
    r = rng.random()
    if r < 0.3:
        x, y = rng.choice(allv), rng.choice(allv)
        action = (x, "=", y, y)  # equate two invocations
    elif r < 0.55:
        # a nested right-hand side, which has to build an intermediate node before
        # the outer one can point at it. Binders are excluded: their first child has
        # to be a slot literal. Operators the pattern itself matches are avoided too
        # -- rebuilding one makes the rule feed itself forever, and a case that never
        # saturates is excluded from the comparison, so it would test nothing.
        used = {at[1] for at in atoms}
        fresh_ops = [o for o in BINOPS if o not in used] or BINOPS
        inner = (rng.choice(fresh_ops), rng.choice(allv), rng.choice(allv))
        action = (rng.choice(allv), (rng.choice(fresh_ops), inner, rng.choice(allv)))
    else:
        action = (rng.choice(allv), "h", rng.choice(allv), rng.choice(allv))
    return atoms, action


def rand_case(rng, i):
    # A small term set over few ops, so patterns and terms collide often.
    terms = [rand_top(rng, rng.randrange(1, 3)) for _ in range(rng.randrange(1, 3))]

    # Unions biased towards creating redundancy: equating a term that has slots
    # with one that has fewer forces the difference to become redundant, which
    # is where matching gets interesting.
    unions = []
    for _ in range(rng.randrange(0, 3)):
        a = rand_top(rng, rng.randrange(1, 3))
        sa = sorted(slots(a))
        if len(sa) >= 2 and rng.random() < SYM_PROB:
            # A term equated with its own slot-swap: the class then proves a
            # permutation of its own slots, which is the symmetry group of Def. 6.
            # Without this the generated corpus has only identity groups, so the
            # group half of the machinery -- and of the checker -- goes untested.
            s1, s2 = rng.sample(sa, 2)
            b = swap_slots(a, s1, s2)
        elif rng.random() < 0.5 and sa:
            # `LEAF0` rather than a bare `(var $0)`: a bare leaf loses its slot
            # (see check_encodable), and although slot 0 happens to survive, the
            # slot-renaming check shifts it to one that would not.
            b = ("null",) if rng.random() < 0.5 else LEAF0
        else:
            b = rand_top(rng, rng.randrange(0, 2))
        unions.append((a, b))

    # Mostly one rule. Sometimes two, so the sweep covers rules interacting -- one
    # producing what the other matches -- which a single rule cannot exercise.
    rules = [rand_rule(rng, terms, unions) for _ in range(2 if rng.random() < 0.25 else 1)]
    probes = terms + [a for a, _ in unions] + [("h", V0, V1), ("h", V0, V0), ("null",), LEAF0]
    return Case(f"fuzz{i}", terms, unions, None, None, probes, rounds=6, rules=rules)


# ------------------------------------------------------------------------ main
def main():
    args = sys.argv[1:]
    if args and args[0] == "show":
        # ./xdiff.py show <index> <seed> [perm...]  -- dump one fuzz case
        if not args[1].isdigit():
            # a curated case, by name prefix
            case = next(c for c in curated() if c.name.startswith(args[1]))
            i = case.name
        else:
            i, seed = int(args[1]), int(args[2] if len(args) > 2 else 0)
            rng = random.Random(seed)
            case = [rand_case(rng, k) for k in range(i + 1)][i]
        order = [int(x) for x in args[3:]]
        rules = [([a[k] for k in order if k < len(a)] if order else a, act, cs) for a, act, cs in case.rules]
        print("=== spec ===")
        print(case.spec(rules), end="")
        # its own scratch file, so `show` can be used while a sweep is running
        keep = ROOT / f"xdiff-show-{i}.egg"
        print("=== reference ===", run_reference(case, rules))
        print("=== encoding  ===", run_encoding(case, rules, keep=keep))
        for n, (atoms, act, cs) in enumerate(rules):
            print(f"=== rule {n} ===")
            print(compile_rule(atoms, act, cs))
        return 0
    if args and args[0] == "fuzz":
        n = int(args[1]) if len(args) > 1 else 100
        seed = int(args[2]) if len(args) > 2 else 0
        rng = random.Random(seed)
        cases = [rand_case(rng, i) for i in range(n)]
    else:
        cases = curated()

    # Categories, most-interesting last: a baseline difference is the machinery
    # disagreeing before any rule runs, so it says nothing about matching.
    cats = {
        "timeout (excluded)": ["timeout"],
        "unsaturated (excluded)": ["unsaturated"],
        "harness/crash": ["crashed"],
        "machinery baseline": ["BASELINE differs"],
        "nondeterminism": ["nondeterministic"],
        "order dependence": ["order dependent"],
        "slot-renaming": ["not slot-renaming invariant"],
        "encoding invariant": ["INVARIANT"],
        "MATCHING mismatch": ["MISMATCH vs reference"],
    }
    counts = {k: 0 for k in cats}
    stats = {}
    all_fails, ok = [], 0
    for c in cases:
        fs = check_case(c, verbose=True, stats=stats)
        if fs:
            all_fails += fs
            for f in fs:
                print("FAIL " + f)
                for k, pats in cats.items():
                    if any(p in f for p in pats):
                        counts[k] += 1
                        break
        else:
            ok += 1

    print(f"\n{ok}/{len(cases)} cases agree")
    for k in cats:
        print(f"  {counts[k]:>4}  {k}")
    b, f = stats.get("baseline_ok", 0), stats.get("fired", 0)
    print(f"\n  {b}/{len(cases)} had a usable baseline (matching was compared)")
    print(f"  {f}/{b} of those had the rule actually change the partition")
    return 1 if all_fails else 0


if __name__ == "__main__":
    sys.exit(main())
