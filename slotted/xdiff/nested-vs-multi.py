"""Does the multipattern matcher prove more than the single-pattern one?

The reference's own property test only requires *inclusion*: every equality the
nested single pattern proves must also be proved by the flattened depth-1 form, and
"the converse is deliberately not required -- the depth-1 matcher sees through
redundant slots that `ematch_all` does not, which is the point of it".

So the two are not interchangeable, and the paper's experiments are written as nested
single patterns while this encoding matches the flattened form. This measures where
that actually diverges: for every curated case whose atoms reconstruct into one
nested pattern, run the reference both ways and compare.
"""

import subprocess
import sys

sys.path.insert(0, "slotted/xdiff")
import xdiff as X


def nest(atoms, action):
    """The atoms as one nested pattern, or None if they are not a tree.

    A rewrite rewrites the root of its pattern, so the action's root has to be the
    top atom's. An atom root used as a child twice is a shared subterm, which a
    single pattern cannot express -- that is the whole reason for multipatterns.
    """
    if not atoms or not action:
        return None
    by_root = {}
    for a in atoms:
        if a[0] in by_root:
            return None  # two atoms on one root
        by_root[a[0]] = a
    used = [c for a in atoms for c in a[2:]]
    tops = [a[0] for a in atoms if a[0] not in used]
    if len(tops) != 1 or action[0] != tops[0]:
        return None
    if any(used.count(r) > 1 for r in by_root):
        return None  # a shared subterm

    def build(name, seen):
        if name not in by_root:
            return name if name.startswith("$") else f"?{name}"
        if name in seen:
            return None  # cyclic
        a = by_root[name]
        kids = [build(c, seen | {name}) for c in a[2:]]
        if any(k is None for k in kids):
            return None
        return f"({a[1]} {' '.join(kids)})"

    return build(tops[0], set())


def _rhs_vars(t):
    """Pattern variables in an RHS tree."""
    if isinstance(t, str):
        return set() if t.startswith("$") else {t}
    out = set()
    for k in t[1:]:
        out |= _rhs_vars(k)
    return out


def spec_with(case, rules, nested_for):
    """The case's spec, with `nested`/`rhs` lines for the rules that have them."""
    out = [f"rounds {case.rounds}"]
    out += [f"term {X.sexpr(t)}" for t in case.terms]
    out += [f"union {X.sexpr(a)} {X.sexpr(b)}" for a, b in case.unions]
    for i, (_atoms, action, _) in enumerate(rules):
        out.append("rule")
        out.append(f"nested {nested_for[i]}")
        rhs = X.rhs_text(action[1]) if len(action) == 2 else f"({action[1]} ?{action[2]} ?{action[3]})"
        out.append(f"rhs {action[0]} {rhs}")
    out += [f"probe {X.sexpr(t)}" for t in case.probes]
    return "\n".join(out) + "\n"


def run(text):
    r = subprocess.run(
        [str(X.XMULTI / "target" / "debug" / "xmulti")],
        input=text,
        capture_output=True,
        text=True,
        timeout=X.RUN_TIMEOUT,
    )
    if r.returncode != 0:
        return "CRASH " + r.stderr.strip().splitlines()[-1][:70]
    return next((line for line in r.stdout.splitlines() if line.startswith("PARTITION")), "?")


eligible = differ = 0
skipped = []
for c in X.curated():
    nested_for = {}
    ok = True
    for i, (atoms, action, conds) in enumerate(c.rules):
        # a side condition is not expressible on this path, and `=` actions rewrite
        # a variable rather than the matched root
        if conds or (action and len(action) == 4 and action[1] == "="):
            ok = False
            break
        n = nest(atoms, action)
        if n is None:
            ok = False
            break
        # Nesting absorbs the intermediate atom roots, so an action naming one has
        # no variable to refer to -- the RHS would be unbound.
        bound = {w[1:] for w in n.replace("(", " ").replace(")", " ").split() if w.startswith("?")}
        used = {action[2], action[3]} if len(action) == 4 else set(_rhs_vars(action[1]))
        if not used <= bound:
            ok = False
            break
        nested_for[i] = n
    if not ok:
        skipped.append(c.name)
        continue
    eligible += 1
    multi = run(c.spec())
    single = run(spec_with(c, c.rules, nested_for))
    if multi != single:
        differ += 1
        print(f"  {c.name}")
        print(f"      multipattern  {multi}")
        print(f"      single nested {single}")

print(f"\n{eligible} cases run both ways, {differ} differ")
print(f"{len(skipped)} not expressible as one nested pattern (shared subterm, side condition, or an `=` action)")
