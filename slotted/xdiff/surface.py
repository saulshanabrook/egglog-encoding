"""Compare nested and flat source spellings through the Rust compiler.

Renders generated rules with one left-hand pattern and the remaining atoms as
`:when` equality patterns, then compares probe partitions with the equivalent flat source rewrite.
No reference binary is needed. Different generated rule text is permitted.

The nested spelling acts on its left-hand root; cases whose actions require a
root absent from every atom are checked by the flat differential suite instead. References to the matched root are
expressed by rebuilding the left-hand pattern. Reports distinguish unsupported
cases from execution limits, and include multipattern counts and maximum width.

Usage:
    python3 slotted/xdiff/surface.py            200 generated cases
    python3 slotted/xdiff/surface.py 500 7      500 cases, seed 7"""

import random
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from slotted.xdiff import xdiff as X


class NoNestedForm(Exception):
    """A rule without the nested spelling used by this metamorphic check."""


def rhs_text(t, ref):
    """A right-hand side as surface text; `ref` renders a variable."""
    if isinstance(t, str):
        return ref(t)
    return "(" + t[0] + " " + " ".join(rhs_text(a, ref) for a in t[1:]) + ")"


def render(atoms, action, conds):
    """A `(rewrite ...)` for this rule. Raises `NoNestedForm` when there is none.

    Bare variables throughout, on purpose: egglog's spelling.
    """
    root = action[0]
    lead = next((i for i, a in enumerate(atoms) if a[0] == root), None)
    if lead is None:
        raise NoNestedForm("the conclusion is about a variable no atom roots")
    if sum(1 for a in atoms if a[0] == root) > 1:
        # a second atom rooted there would have to be written `:when (= <call> ...)`,
        # and an equality's left side must be a variable
        raise NoNestedForm("two atoms are rooted at the conclusion's variable")

    def pay(c):
        """A `#k` child is the harness's spelling of the PAYLOAD LEAF `k`, shared with
        the oracle; the surface writes the node itself, `(Num k)`. A bare `#` would read
        as this language's global sigil."""
        if isinstance(c, str) and c.startswith("#"):
            return f"(Num {c[1:]})"
        return c

    head = atoms[lead]
    lhs = f"({head[1]} {pay(head[2])} {pay(head[3])})"

    def ref(c):
        """A child, with the matched root written out.

        A `rewrite` gives the matched root NO NAME, so every other mention of it -- on
        the right, and as another atom's child -- rebuilds the pattern instead. Two
        occurrences of one pattern over the same variables are the same class by
        congruence, so this says what the atom list says.
        """
        return lhs if c == root else pay(c)

    if len(action) == 2:
        rhs = rhs_text(action[1], ref)
    elif action[1] == "=":
        rhs = ref(action[2])
    else:
        rhs = f"({action[1]} {ref(action[2])} {ref(action[3])})"

    facts = [f"(= {a[0]} ({a[1]} {ref(a[2])} {ref(a[3])}))" for i, a in enumerate(atoms) if i != lead]
    for want, slot, pvars in conds:
        # `ref` may render the matched root as the pattern itself, and a condition takes a
        # call where a variable goes for exactly this reason
        args = " ".join(ref(v) for v in pvars)
        facts.append(f"({'free' if want else 'not-free'} {slot} {args})")
    parts = [f"(rewrite {lhs} {rhs}"]
    if facts:
        # ONE `:when`, holding every fact -- egglog's spelling, and the only one it
        # accepts. Several clauses would be refused, and mean only the last one there.
        parts.append("         :when (" + "\n                ".join(facts) + ")")
    return "\n".join(parts) + ")"


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 200
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 0
    rng = random.Random(seed)

    direct = X.source_rule
    compared = agreed = 0
    # skips have two very different reasons and lumping them hid how much was skipped
    # for being inexpressible rather than for being too big to run
    no_rewrite = too_big = 0
    # how wide a multipattern each compared case actually carried. `1` is a single
    # pattern; the interesting rows are the rest, and a run whose widest is 1 has tested
    # nothing about multipatterns however many cases it agreed on
    widths = {}
    bad = []
    for i in range(n):
        case = X.rand_case(rng, i)
        if not any(atoms for atoms, _, _ in case.rules):
            continue
        try:
            texts = [render(a, act, c) for a, act, c in case.rules if a]
        except NoNestedForm:
            no_rewrite += 1
            continue

        want = X.run_encoding(case)
        try:
            X.source_rule = render
            got = X.run_encoding(case)
        finally:
            X.source_rule = direct

        if want[0] != "OK" or got[0] != "OK":
            # an error on ONE side is a finding; on both it is the case being too big
            if want[0] != got[0]:
                bad.append((case.name, texts, f"{want[0]} vs {got[0]}: {str(got[1])[:200]}"))
            else:
                too_big += 1
            continue
        compared += 1
        width = max(len(atoms) for atoms, _, _ in case.rules if atoms)
        widths[width] = widths.get(width, 0) + 1
        if want[1] == got[1]:
            agreed += 1
        else:
            bad.append((case.name, texts, f"partition {want[1]} vs {got[1]}"))

    for name, texts, why in bad[:3]:
        print(f"  FAIL {name}: {why}")
        for t in texts:
            for line in t.splitlines():
                print(f"      {line}")
    # the counts are part of the result: a renderer that expressed nothing would agree
    multi = sum(c for w, c in widths.items() if w > 1)
    shape = ", ".join(f"{w} atom{'s' if w > 1 else ''}: {widths[w]}" for w in sorted(widths))
    print(f"\n{agreed}/{compared} cases agree through the surface syntax")
    print(f"  multipatterns: {multi}/{compared} carried more than one atom   ({shape})")
    print(f"  skipped: {no_rewrite} no nested spelling, {too_big} too big to run either way")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
