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
slotcc = __import__("slotted-egglog")
EGGLOG = ROOT / "target" / "debug" / "egglog"
XMULTI = ROOT / "slotted" / "xmulti"


def machinery(lang):
    """A language's machinery, compiled here rather than read from a build artifact.

    The harness writes its programs as text, so it can hold the machinery as text too:
    nothing has to be staged on disk for an `(include ...)` to find.
    """
    return slotcc.compile_source(slotcc.Source(ROOT / "slotted" / "languages" / f"{lang}.egg"))


BINOPS = ["add", "f", "g", "h", "k", "sub", "sub2"]

# Permutations tried per case in the order-independence check. Each costs a full
# saturation on both sides, so this is the main knob on runtime.
PERM_CAP = 4

# Some generated e-graphs blow the machinery up, so every run is bounded and a
# timeout is reported as its own category rather than stalling the sweep.
RUN_TIMEOUT = 25

# How often a generated subterm is a binder. Raise it to search binder-heavy
# ground: XDIFF_LAM=0.55
LAM_PROB = float(os.environ.get("XDIFF_LAM", "0.2"))

# How often a union equates a term with its own slot-swap, which is what gives a class
# a non-trivial symmetry group. Raise it to search symmetry-heavy ground: XDIFF_SYM=0.9
SYM_PROB = float(os.environ.get("XDIFF_SYM", "0.35"))

# How often a generated leaf is the PAYLOAD leaf `num`. The language had no payload
# column at all, so no pattern could hold one and that whole grammar went unsearched --
# a payload literal is what `(= x (Num 2))` is made of. The oracle can be asked about a
# literal (its `Pattern::ENode` carries a concrete node) but NOT about a payload
# variable, so only the literal half is compared here.
NUM_PROB = float(os.environ.get("XDIFF_NUM", "0.3"))

# How often a rule gets a DISCONNECTED atom -- root and children all fresh, so it shares
# no variable with the rest of the pattern. Such an atom is unconstrained: it matches
# every node of its operator and the rule becomes a cross product, which is why the
# extra atoms below draw their children from the bound set instead, and why this is rare
# rather than either off or common.
#
# It earns its place: with it off, no generated rule had more than two disconnected
# pieces, so three atoms whose slots are all placeholders -- kept apart only by the
# cliques, and offered to refinement together (C8) -- went unsearched. That is the
# shape that found `K1`.
#
# A reference that runs out of time is reported as such and left out of the ratio rather
# than counted as a divergence, since a cross product is sometimes more work than its
# budget. Raise this to search the ground harder: XDIFF_DISC=0.5
DISCONNECT_PROB = float(os.environ.get("XDIFF_DISC", "0.08"))

# How often a rule's pattern is drawn DIRECTLY as a conjunctive query rather than read
# off a term -- see `rand_general_rule` for the shapes only that reaches. Most such
# patterns match nothing, so this trades firing rate for coverage; measure both before
# moving it. XDIFF_GENERAL=1 makes every rule general.
GENERAL_PROB = float(os.environ.get("XDIFF_GENERAL", "0.25"))

# How DEEP a generated term may be, and how often a binary node's two children are ONE
# subterm. The unify shapes -- `UN1`, `UN2` -- need a body shared under two chains that
# are themselves equal, which is a depth-3 term with a repeated subterm; at the default
# depth of 2 and with children drawn independently the generator cannot build one, so
# those cases are curated rather than found. Raise both to search that ground:
# XDIFF_DEPTH=3 XDIFF_DUP=0.3, best with XDIFF_SYM=0.9 and XDIFF_LAM=0.55 as well. A
# deeper term is a bigger e-graph and a slower case, which is why the default stays.
MAX_DEPTH = int(os.environ.get("XDIFF_DEPTH", "2"))
DUP_PROB = float(os.environ.get("XDIFF_DUP", "0"))

# How often two EQUAL subterms of a seed term are read off as ONE pattern variable.
# `flatten_to_atoms` gives every subterm a fresh variable, so a term with a repeated
# subterm yields a pattern with two unrelated variables and the join that a shared
# body would make is never written -- which is the other half of why the unify
# shapes were never generated. With this on, a repeated body becomes a shared variable
# and the rule says the two occurrences are the same term. A binder is never shared
# this way: sharing two equal lambda chains as one variable would be the repeated
# variable the perturbations already write, and it would hide the shape sharing exists
# for -- two chains whose BODIES are one variable, so that the chains' bound slots have
# to be identified. XDIFF_SHARE=0.7
SHARE_PROB = float(os.environ.get("XDIFF_SHARE", "0"))

# How often a variable leaf under a binder is one of the ENCLOSING binders' variables.
# Leaves and binders are otherwise drawn independently, so most generated lambdas never
# mention their own variable, and a body that ignores its binders puts no slot on the
# inner class -- the shape unify exists for needs the body to reach back to the outer
# binder. Off by default so the default case numbering is unchanged. XDIFF_USEBIND=0.6
USEBIND_PROB = float(os.environ.get("XDIFF_USEBIND", "0"))

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

# The machinery's table names are the carrier's, so they are read off the language
# rather than written out: a program compiles to `RenamesToLeader_0` and friends, and
# a second declared sort would get its own set of tables.
SYM = LANG.symbols_for(LANG.default_sort)


def swap_slots(t, s1, s2):
    """`t` with slots `s1` and `s2` exchanged."""
    if t[0] == "var":
        return ("var", s2 if t[1] == s1 else s1 if t[1] == s2 else t[1])
    if t[0] in ("null", "num"):
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
            # `atom_lines` rather than one line per atom: a child that is neither a
            # pattern variable nor a binder's slot -- a PAYLOAD LEAF written literally --
            # cannot sit in a child position on the oracle's side, and needs an atom of
            # its own. That is the same spelling `xarray` and `xsdql` use, so the two
            # cannot drift.
            enc_atoms = [(r, o, [_child(c1), _child(c2)]) for (r, o, c1, c2) in atoms]
            out += slotenc.atom_lines(LANG, enc_atoms[0][0], enc_atoms)[1]
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
    """An atom's child, in the encoder's grammar.

    A child written `$v` is a slot literal, not a pattern variable: the encoding stores
    a binder's slot as an edge to `(Var 0)`, so the child position is that literal
    class. One written `#k` is the PAYLOAD LEAF `k`, reached through its own class --
    the same spelling the oracle's `atom` line uses for one.
    """
    if c.startswith("#"):
        return ("cls", ("num", int(c[1:])))
    return ("sl", c) if c.startswith("$") else ("pv", c)


def compile_rule(atoms, action, conds=()):
    """Compile a flattened multipattern into an egglog rule, through the encoder.

    Nothing here is the recipe -- `slotted-encoder.compile_rule` is. This is the
    harness's spelling of a rule translated into the encoder's: an atom is written
    `(root, op, c1, c2)` over bare names, and an action either `(root, rhs-tree)` or
    the flat `(root, op, a, b)`, whose `=` equates two variables.

    The flat form builds one depth-1 node over bound variables.
    """
    atoms = slotenc.connected_order(LANG, [(r, o, [_child(c1), _child(c2)]) for r, o, c1, c2 in atoms])
    if len(action) == 2:
        root, rhs = action
        act = ("build", root, slotenc.rhs_of(LANG, rhs))
    elif action[1] == "=":
        act = ("build", action[0], ("pv", action[2]))
    else:
        root, op, a, b = action
        act = ("row", root, op, [a, b])
    return slotenc.compile_rule(LANG, atoms, act, conds=conds)


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
    return slotenc.round_schedule(steps)


def egg_program(case, rules=None, mult=3):
    rules = case.rules if rules is None else rules
    out = [machinery("toy")]
    # A slotted e-class is NOT one egglog e-class: the alpha-finder relates
    # equal-up-to-renaming nodes with `RenamesToLeader` and deletes one, rather
    # than unioning them. So two probes are in the same slotted class when they
    # reach a common leader, which is also what the machinery's own tests check.
    # In its own ruleset, so reading the probes costs no user-rule steps: a reference
    # round applies every rule once, so a round here must mean one `(run)` and no more.
    out.append("(ruleset probes)")
    out.append("(relation ProbeId (U i64))")
    out.append("(relation SameClass (i64 i64))")
    out.append(
        "(rule ((ProbeId a i) (ProbeId b j)\n"
        f"       ({SYM.renames} a m1 l) ({SYM.renames} b m2 l))\n"
        "      ((SameClass i j)) :ruleset probes)"
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
    # Named after the rules have run, then read WITHOUT running them again: a second
    # `schedule(...)` here would hand the encoding twice the user-rule steps its budget
    # names, and a reference round would look worth two of them.
    for i, _ in enumerate(case.probes):
        out.append(f"(ProbeId _p{i} {i})")
    out.append(f"(run-schedule {slotenc.MACHINERY_SCHEDULE} (saturate (run probes)))")
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

    # Raw-row invariants are checked by invariants.py and def4-edges.py.

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

    # C10 -- three atoms, chain then join
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
    # A test that is not portable is left out rather than approximated here.

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
            [("f", V0, V0), ("f", V1, V1), ("g", ("f", V0, V0), V0)],
            [(("f", V0, V0), ("f", V1, V1))],
            [("p", "g", "c", "$0"), ("c", "f", "a", "a")],
            ("p", "h", "a", "a"),
            [("g", ("f", V0, V0), V0), ("h", V0, V0), ("h", V1, V1), ("f", V0, V0), LEAF0],
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
            [("add", ("sub2", V0, V0), NUL)],
            [(("h", V0, V2), NUL)],
            [("x3", "h", "x1", "x2")],
            ("x1", "h", "x3", "x1"),
            [("add", ("sub2", V0, V0), NUL), ("h", V0, V2), ("h", V0, V1), ("h", V0, V0), NUL, ("sub", V0, V0)],
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
            [("h", V2, V1)],
            [],
            [("x3", "h", "x1", "x2")],
            ("x1", "h", "x2", "x3"),
            [("h", V2, V1), ("h", V0, V1), ("h", V0, V0), NUL, ("sub", V0, V0)],
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
    # a pattern slot may be a merge TARGET. See `final_refine` in `slotted-encoder.py`.
    #
    # No condition, a condition on the binder's own body, and joining the two atoms all
    # agreed even before the fix, which is what isolated it.
    K1_ATOMS = [("r0", "lam", "$s0", "v0"), ("r1", "sub2", "a", "b")]
    cs.append(
        Case(
            "K1-bound-slot-condition-across-disconnected-atoms",
            [("lam", V0, V2), ("sub2", V0, V1)],
            [],
            K1_ATOMS,
            ("v0", "h", "r1", "r1"),
            [("lam", V0, V2), ("sub2", V0, V1), ("h", V0, V1), ("h", V0, V0), NUL],
            rounds=6,
            rules=[(K1_ATOMS, ("v0", "h", "r1", "r1"), [(True, "$s0", ["a"])])],
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
    K2_ATOMS = [("x3", "h", "x5", "x2"), ("x6", "f", "x4", "x5"), ("x7", "f", "x3", "x6")]
    K2_LHS = ("f", ("h", NUL, V2), ("f", V2, NUL))
    cs.append(
        Case(
            "K2-sibling-link-is-not-an-order",
            [K2_LHS],
            [(K2_LHS, ("sub", V0, V0))],
            K2_ATOMS,
            ("x7", "h", "x2", "x6"),
            [K2_LHS, ("sub", V0, V0), ("h", V0, V1), ("h", V0, V0), NUL],
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
    # The encoding keeps a class's symmetries as rows of `Symmetry`, and a
    # repeated variable is checked by computing the symmetry it would need
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
    # *partial* symmetry, so the rows are not a group but an inverse monoid. The
    # worry is a computed symmetry that came out short (composition truncates)
    # matching one of those partial maps and being accepted wrongly.
    # `a` keeps two live slots with a swap between them, and a third slot that a
    # union has made redundant. The parent holds `a` at the identity beside `a`
    # under the swap, so the match needs the real symmetry while a partial
    # symmetry is also present to be confused with it.
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
    # equation looks its node up separately and may map that node's private bound
    # name to the same `$x` pattern coordinate, so the concrete names need not agree.
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

    # ---- shapes taught by slotted/tests/multipattern.egg ---------------------
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
            [("f", ("lam", V0, ("add", V0, V0)), NUL)],
            [],
            [("p", "f", "a", "b"), ("a", "lam", "$v", "body")],
            ("p", "h", "body", "b"),
            [("f", ("lam", V0, ("add", V0, V0)), NUL), ("h", V0, V0), ("h", V0, V1)],
        )
    )

    # MP2 -- TWO variables shared between the atoms, so both halves of the join have to
    # hold. One shared variable is `M3` above; this is the case where a second one can
    # refuse a match the first would allow.
    cs.append(
        Case(
            "MP2-join-on-two-variables",
            [("f", V0, V1), ("g", V0, V1), ("g", V1, V0)],
            [],
            [("p", "f", "x", "y"), ("q", "g", "x", "y")],
            ("p", "h", "x", "y"),
            [("f", V0, V1), ("g", V0, V1), ("g", V1, V0), ("h", V0, V1), ("h", V1, V0)],
        )
    )

    # MP3 -- four atoms, chained two deep, whose deepest variables are shared only with
    # each other and occur nowhere in the atom the action is rooted at.
    cs.append(
        Case(
            "MP3-four-atom-chain",
            [("k", ("add", ("f", V0, V1), ("f", V0, V1)), NUL)],
            [],
            [("p", "k", "e", "z"), ("e", "add", "l", "r"), ("l", "f", "a", "b"), ("r", "f", "a", "b")],
            ("p", "h", "a", "b"),
            [("k", ("add", ("f", V0, V1), ("f", V0, V1)), NUL), ("h", V0, V1), ("h", V0, V0)],
        )
    )

    # MP4 -- a variable shared under TWO BINDERS. `B3` and `B4` above share a slot
    # LITERAL between two binders, which constrains nothing; this shares the BODY, which
    # does, and has to hold up to renaming rather than by pointer.
    cs.append(
        Case(
            "MP4-body-shared-under-two-binders",
            [("f", ("lam", V0, ("g", V1, V1)), ("lam", V2, ("g", V1, V1)))],
            [],
            [("p", "f", "a", "b"), ("a", "lam", "$v", "body"), ("b", "lam", "$w", "body")],
            ("p", "h", "body", "body"),
            [
                ("f", ("lam", V0, ("g", V1, V1)), ("lam", V2, ("g", V1, V1))),
                ("h", V0, V0),
                ("h", V0, V1),
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
            [("f", V0, V1), ("g", V0, NUL), ("k", V1, NUL)],
            [],
            [("p", "f", "x", "y"), ("d0", "g", "d0a", "d0b"), ("d1", "k", "d1a", "d1b")],
            ("p", "h", "x", "y"),
            [("f", V0, V1), ("g", V0, NUL), ("k", V1, NUL), ("h", V0, V1), ("h", V0, V0)],
        )
    )

    # ---- shapes taught by slotted/ENCODING.md --------------------
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
    # unambiguous.
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
    UN1_ATOMS = [("p", "k", "q", "d2"), ("q", "g", "d1", "n"), ("d1", "f", "x", "n2"), ("d2", "h", "x", "n3")]
    UN1_Q = ("g", ("f", V0, NUL), NUL)
    UN1_P = ("k", UN1_Q, ("h", V1, NUL))
    cs.append(
        Case(
            "UN1-shared-var-through-two-redundant-slots",
            [UN1_P],
            [(UN1_Q, ("g", ("f", ("var", 5), NUL), NUL)), (UN1_P, ("k", UN1_Q, ("h", ("var", 6), NUL)))],
            UN1_ATOMS,
            ("p", "sub", "d1", "d2"),
            [UN1_P, ("sub", ("f", V0, NUL), ("h", V1, NUL)), ("sub", ("f", V0, NUL), ("h", V0, NUL)), NUL],
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
    UN2_L = ("lam", V0, ("lam", V1, ("f", V0, V1)))
    UN2_TERMS = [("f", UN2_L, UN2_L)]
    UN2_UNIONS = [(("f", V0, V1), ("f", V1, V0))]
    UN2_PROBES = [("f", UN2_L, UN2_L), ("sub", V0, V0), ("sub", V0, V1), NUL]
    UN2_STRAIGHT = [
        ("out", "f", "l1", "l2"),
        ("l1", "lam", "$x", "b1"),
        ("b1", "lam", "$y", "a"),
        ("l2", "lam", "$x", "b2"),
        ("b2", "lam", "$y", "a"),
    ]
    UN2_SWAPPED = [
        ("out", "f", "l1", "l2"),
        ("l1", "lam", "$x", "b1"),
        ("b1", "lam", "$y", "a"),
        ("l2", "lam", "$y", "b2"),
        ("b2", "lam", "$x", "a"),
    ]
    cs.append(
        Case(
            "UN2-shared-body-under-two-binder-chains",
            UN2_TERMS,
            UN2_UNIONS,
            UN2_STRAIGHT,
            ("out", ("sub", "$x", "$x")),
            UN2_PROBES,
            rounds=6,
            rules=[
                (UN2_STRAIGHT, ("out", ("sub", "$x", "$x")), []),
                (UN2_SWAPPED, ("out", ("sub", "$x", "$y")), []),
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
            [("g", ("f", V0, V1), NUL)],
            [(("f", V0, V1), NUL)],
            [("r", "g", "n", "z"), ("n", "f", "a", "a")],
            ("r", "h", "a", "a"),
            [("g", ("f", V0, V1), NUL), ("h", V0, V0), NUL],
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
            [("lam", V2, V2)],
            [],
            [("r0", "lam", "$s0", "b"), ("r1", "lam", "$s1", "b")],
            ("b", "h", "r0", "r0"),
            [("lam", V2, V2), ("h", V0, V1), ("h", V0, V0), NUL],
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
    # reading fires; `check-capture-guards.py` holds the rule libraries to this. The
    # probes ask for the sound result, the captured one, and a term the union must not
    # reach. `CAP0` is the same rule without its guard.
    CAP_TERM = ("f", ("lam", V0, ("sub", V0, V0)), V2)
    CAP_ATOMS = [("p", "f", "l", "e"), ("l", "lam", "$y", "body")]
    CAP_PROBES = [
        CAP_TERM,
        ("lam", V1, ("f", ("sub", V1, V1), V2)),
        ("lam", V1, ("f", ("sub", V1, V1), V1)),
        NUL,
    ]
    cs.append(
        Case(
            "CAP1-rhs-binder-over-outside-variable-guarded",
            [CAP_TERM],
            [],
            CAP_ATOMS,
            ("p", ("lam", "$y", ("f", "body", "e"))),
            CAP_PROBES,
            rounds=3,
            rules=[(CAP_ATOMS, ("p", ("lam", "$y", ("f", "body", "e"))), [(False, "$y", ["e"])])],
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
            ("p", ("lam", "$y", ("f", "body", "e"))),
            CAP_PROBES,
            rounds=3,
        )
    )

    return cs


# ------------------------------------------------------------------- the fuzzer
def rand_term(rng, depth, bound=()):
    """A random term; `bound` is the binders it sits under, outermost first."""
    if depth == 0 or rng.random() < 0.3:
        leaves = [("var", rng.randrange(3)), ("null",)]
        if USEBIND_PROB and bound and rng.random() < USEBIND_PROB:
            leaves[0] = ("var", rng.choice(bound))
        if rng.random() < NUM_PROB:
            # a payload leaf, so a term -- and the patterns read off it -- can hold one
            leaves.append(("num", rng.randrange(3)))
        return rng.choice(leaves)
    if rng.random() < LAM_PROB:
        v = rng.randrange(3)
        return ("lam", ("var", v), rand_term(rng, depth - 1, (*bound, v)))
    op = rng.choice(BINOPS)
    a = rand_term(rng, depth - 1, bound)
    b = a if DUP_PROB and rng.random() < DUP_PROB else rand_term(rng, depth - 1, bound)
    return (op, a, b)


def flatten_to_atoms(t, ctr, rng=None, memo=None):
    """Flatten a term into depth-1 atoms with fresh pvars, so the resulting
    multipattern is guaranteed to match that term. Leaves become bare pvars,
    which is what a multipattern does with them anyway.

    `memo` remembers the variable a subterm was read off as, so an equal subterm met
    again may reuse it (`SHARE_PROB`) and the pattern joins the two occurrences."""
    if memo is None:
        memo = {}
    if SHARE_PROB and t in memo and t[0] != "lam" and rng is not None and rng.random() < SHARE_PROB:
        return memo[t], []
    root, atoms = _flatten_fresh(t, ctr, rng, memo)
    memo[t] = root
    return root, atoms


def _flatten_fresh(t, ctr, rng, memo):
    if t[0] == "num":
        # A payload leaf is either kept LITERALLY in the child position -- `#k`, which is
        # a pattern about the payload -- or read as a plain variable like any other leaf.
        # Both are shapes worth generating, and only the first tests the payload grammar.
        if rng is not None and rng.random() < 0.6:
            return f"#{t[1]}", []
        ctr[0] += 1
        return f"x{ctr[0]}", []
    if t[0] in ("var", "null"):
        ctr[0] += 1
        return f"x{ctr[0]}", []
    if t[0] == "lam":
        pb, ab = flatten_to_atoms(t[2], ctr, rng, memo)
        ctr[0] += 1
        root = f"x{ctr[0]}"
        # A binder's slot is a literal. One is reused sometimes, so that two binders
        # written with the same slot get exercised beside two written with different ones.
        r = rng.random() if rng is not None else 1.0
        sl = "$s0" if r < 1 / 3 else f"$s{ctr[0]}"
        return root, ab + [(root, "lam", sl, pb)]
    op, a, b = t
    pa, aa = flatten_to_atoms(a, ctr, rng, memo)
    pb, ab = flatten_to_atoms(b, ctr, rng, memo)
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
        pvs = sorted({v for at in atoms for v in (at[2], at[3]) if not v.startswith(("$", "#"))})
        # identify two child pvars (tests repeated-variable semantics)
        if pvs and rng.random() < 0.5:
            keep, drop = rng.choice(pvs), rng.choice(pvs)
            atoms = [(r, o, keep if c1 == drop else c1, keep if c2 == drop else c2) for (r, o, c1, c2) in atoms]
        # drop a trailing atom (leaves a pvar unconstrained)
        if len(atoms) > 1 and rng.random() < 0.3:
            atoms = atoms[:-1]
        # swap an atom's children -- never a binder's, whose bound slot or variable has
        # to stay first: the body is not a binder position on either side.
        swappable = [j for j, a in enumerate(atoms) if a[1] != "lam"]
        if swappable and rng.random() < 0.4:
            j = rng.choice(swappable)
            r, o, c1, c2 = atoms[j]
            atoms[j] = (r, o, c2, c1)

    # ATOMS THAT ARE NOT PART OF THE SEED'S SHAPE. Everything above descends from one
    # term's flattening, so the only patterns reachable were that shape and shapes with a
    # piece removed. These two forms are what a multipattern can say and a single term
    # cannot, and they are what `:when (= v (Ctor a b))` spells in the surface syntax:
    #
    #   * rooted at a variable the pattern ALREADY binds -- "and that one also looks like
    #     this", which is Rudi's `(= x (Succ (Succ y)))`;
    #   * rooted at a FRESH variable over children it already binds -- an atom joined to
    #     the rest only through its children.
    #
    # Children come from the bound set either way. An atom whose children were fresh
    # would be unconstrained, and the cross product costs a sweep more than the extra
    # shape is worth. `lam` is excluded: its first child has to be a slot literal.
    if rng.random() < 0.35:
        plain = [o for o in BINOPS if o != "lam"]
        for k in range(rng.randint(1, 2)):
            pvs = sorted({v for at in atoms for v in (at[0], at[2], at[3]) if not v.startswith(("$", "#"))})
            if len(pvs) < 2:
                break
            root = rng.choice(pvs) if rng.random() < 0.5 else f"w{k}"
            atoms.append((root, rng.choice(plain), rng.choice(pvs), rng.choice(pvs)))

    # A DISCONNECTED atom, sharing nothing with the rest. Kept rare because it is a cross
    # product: the case runs longer and the graph grows faster for one extra shape.
    if rng.random() < DISCONNECT_PROB:
        plain = [o for o in BINOPS if o != "lam"]
        for k in range(rng.randint(1, 2)):
            atoms.append((f"d{k}", rng.choice(plain), f"d{k}a", f"d{k}b"))

    allv = sorted({v for at in atoms for v in (at[0], at[2], at[3]) if not v.startswith(("$", "#"))})
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

    # SIDE CONDITIONS, which were never generated: `free`/`not-free` had only the four
    # curated `CD*` cases, so the one part of a rule that is about a match's SLOTS rather
    # than its shape went unfuzzed. A condition needs a slot literal to talk about, and
    # only a binder atom puts one in a pattern.
    conds = []
    slots = sorted({c for at in atoms for c in (at[2], at[3]) if c.startswith("$")})
    if slots and rng.random() < 0.3:
        conds.append((rng.random() < 0.5, rng.choice(slots), [rng.choice(allv)]))
    return atoms, action, conds


def rand_general_rule(rng, terms, unions):
    """A multipattern drawn DIRECTLY, rather than read off a term.

    `rand_rule` flattens ONE seed term and perturbs it, and any atom it adds afterwards
    takes its children from the variables already bound. That guarantees the pattern
    matches, and it is why the sweep finds anything at all -- but it is a corner of what
    a multipattern is. Three shapes it cannot reach:

      * a pattern that is not any term's shape -- atoms whose operators and joins were
        never a tree;
      * arbitrary sharing -- one variable in four atoms, two atoms rooted at the same
        variable, a child that is also its own atom's root;
      * a pattern whose joins form a cycle rather than a tree.

    So this builds `k` atoms outright: each operator free, each root and child drawn
    from the variables bound so far or a fresh one. Most such patterns match nothing,
    which is why it is mixed with the seeded generator rather than replacing it -- but a
    pattern that matches nothing still has to match nothing on BOTH sides, and the ones
    that do match are shapes nothing else reaches.

    A SLOT stands only where the language has one, which here is `lam`'s first column.
    Putting one anywhere else is not an unexplored shape but an ill-typed term: the
    reference's binary operators take applied ids, and it rejects `(k $s0 $s0)` with
    `FromSyntaxFailed`. That is why `rand_rule` draws children from the non-`$`
    variables, and it is kept. The converse holds too: `lam`'s first column takes a
    slot literal only, which the compiler enforces.
    """
    ops = list(BINOPS)
    atoms, bound, nslot = [], [], 0
    for k in range(rng.randint(1, 5)):
        op = rng.choice(ops) if rng.random() < 0.75 else "lam"

        def pick(k=k):
            if bound and rng.random() < 0.55:
                return rng.choice(bound)
            return f"v{k}_{rng.randrange(3)}"

        root = rng.choice(bound) if bound and rng.random() < 0.3 else f"r{k}"
        if op == "lam":
            # A binder column holds a slot literal. Reusing an earlier binder's slot name
            # is allowed: it constrains nothing, and that is itself a shape worth
            # generating; two different names are two slots that can never be one.
            if nslot and rng.random() < 0.3:
                c1 = f"$s{rng.randrange(nslot)}"
            else:
                nslot += 1
                c1 = f"$s{nslot - 1}"
            c2 = pick()
        else:
            c1, c2 = pick(), pick()
        atoms.append((root, op, c1, c2))
        for v in (root, c1, c2):
            if not v.startswith(("$", "#")) and v not in bound:
                bound.append(v)

    allv = sorted(bound)
    if not allv:  # every column was a slot, so there is nothing for an action to name
        return rand_rule(rng, terms, unions)

    r = rng.random()
    if r < 0.3:
        x, y = rng.choice(allv), rng.choice(allv)
        action = (x, "=", y, y)
    elif r < 0.55:
        used = {at[1] for at in atoms}
        fresh_ops = [o for o in BINOPS if o not in used] or BINOPS
        inner = (rng.choice(fresh_ops), rng.choice(allv), rng.choice(allv))
        action = (rng.choice(allv), (rng.choice(fresh_ops), inner, rng.choice(allv)))
    else:
        action = (rng.choice(allv), "h", rng.choice(allv), rng.choice(allv))

    conds = []
    slots_seen = sorted({c for at in atoms for c in (at[2], at[3]) if c.startswith("$")})
    if slots_seen and rng.random() < 0.3:
        conds.append((rng.random() < 0.5, rng.choice(slots_seen), [rng.choice(allv)]))
    return atoms, action, conds


def rand_case(rng, i):
    # A small term set over few ops, so patterns and terms collide often.
    terms = [rand_top(rng, rng.randrange(1, MAX_DEPTH + 1)) for _ in range(rng.randrange(1, 3))]

    # Unions biased towards creating redundancy: equating a term that has slots
    # with one that has fewer forces the difference to become redundant, which
    # is where matching gets interesting.
    unions = []
    for _ in range(rng.randrange(0, 3)):
        a = rand_top(rng, rng.randrange(1, MAX_DEPTH + 1))
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
    draw = (
        (lambda: rand_general_rule(rng, terms, unions))
        if rng.random() < GENERAL_PROB
        else (lambda: rand_rule(rng, terms, unions))
    )
    rules = [draw() for _ in range(2 if rng.random() < 0.25 else 1)]
    probes = terms + [a for a, _ in unions] + [("h", V0, V1), ("h", V0, V0), ("null",), LEAF0]
    return Case(f"fuzz{i}", terms, unions, None, None, probes, rounds=6, rules=rules)


# ------------------------------------------------------------- known divergences
#: Reproductions of OPEN bugs. Deliberately NOT part of `curated()`, which every green
#: check shares: a case known to diverge would turn those red, and silencing it there
#: would hide a real one. `isomorphism.py known` runs these and requires each to STILL
#: diverge -- one that starts agreeing is news, because the bug was fixed and the entry
#: is stale, and its case then belongs in `curated()` where it is held green from then on.
#:
#: EMPTY is the good state. `K1`, `K2` and `LIT1` all lived here and now sit in `curated()`.


def known_divergences():
    """`(why, case)` for each open bug the corpus carries a reproduction of."""
    return []


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
