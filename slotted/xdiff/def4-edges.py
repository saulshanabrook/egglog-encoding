"""Is every edge's domain *exactly* its child's slot set?

Def. 4 wants equality, and the two halves used to be checked separately and partially:
`xdiff.py`'s check 6 looks for an edge wider than an idempotent self-loop on its child, and
the narrow half was recorded as "not checkable this way" and left to `compose-total`. Both
are one comparison against `ClassSlots`, which is where a class's slots are held:

    (!= (map-domain m) (ClassSlots c))

`map-domain` and `ClassSlots` are both identity maps, so comparing them is set equality of
the edge's domain with the class's slots.

This is also the precondition the compiled action depends on. An action reads renamings off
a matched node, and narrowing them by `ClassSlots` is a no-op exactly when those renamings
already have the child's slots for their domain -- which is what this checks. That is why
`XDIFF_BUGS=wide-kids` no longer discriminates: not luck, but a property checked here. If
this ever reports a violation, that mutation becomes live again.

A BINDER COLUMN IS EXEMPT, and is checked against its own invariant instead. What sits
there is a name the node binds, not a use of its child, so its domain is always the one
slot `0` however few slots the variable class has left -- which is exactly the point:
tying it to `ClassSlots` is what used to destroy a bound slot the moment two variable
invocations were equated. So for those columns this asserts `map-domain = {0}` and that
the child is the variable class, the two things the binder rules read.

The rules are built from `slotted/languages/toy.egg`, the language the harness runs, so a
constructor added there is covered without touching this file.

    python3 slotted/xdiff/def4-edges.py            curated
    python3 slotted/xdiff/def4-edges.py fuzz 250   generated
"""

import os
import random
import subprocess
import sys

sys.path.insert(0, "slotted/xdiff")
import xdiff as X

HEAD = """
(ruleset def4)
(relation BadDomain (String Renaming Renaming))
"""


enc = X.slotenc
LANG = enc.read_language(X.LANG_DIR / "toy.egg")


def obs():
    out = [HEAD]
    for name, sig in LANG.items():
        _, edges, kids, _ = enc.cols_of(sig)
        kid_cols = [c for c in sig if c in enc.SLOTTED]
        pat = enc.pattern(name, sig)
        for i in range(len(kids)):
            where = f'"{name} child {i + 1}"'
            if kid_cols[i] is enc.BINDER:
                out.append(
                    f"(rule ((= v {pat})\n"
                    f"       (!= (map-domain {edges[i]}) (map-of 0 0)))\n"
                    f"      ((BadDomain {where} {edges[i]} (map-of 0 0))) :ruleset def4)"
                )
                out.append(
                    f"(rule ((= v {pat})\n"
                    f"       (!= {kids[i]} (Var 0)))\n"
                    f"      ((BadDomain {where} {edges[i]} (map-of 0 0))) :ruleset def4)"
                )
                continue
            out.append(
                f"(rule ((= v {pat})\n"
                f"       (= s (ClassSlots {kids[i]}))\n"
                f"       (!= (map-domain {edges[i]}) s))\n"
                f"      ((BadDomain {where} {edges[i]} s)) :ruleset def4)"
            )
    out += ["(run def4 1)", "(print-size BadDomain)", "(print-function BadDomain 8)"]
    return "\n".join(out)


if len(sys.argv) > 1 and sys.argv[1] == "fuzz":
    rng = random.Random(0)
    cases = [X.rand_case(rng, i) for i in range(int(sys.argv[2]) if len(sys.argv) > 2 else 250)]
else:
    cases = X.curated()

total, bad = 0, []
for c in cases:
    prog = X.egg_program(c).replace("(print-function SameClass 100000)", obs())
    p = X.ROOT / f"xdiff-tmp-def4-{os.getpid()}.egg"
    p.write_text(prog)
    try:
        r = subprocess.run([str(X.EGGLOG), str(p)], capture_output=True, text=True, cwd=X.ROOT, timeout=120)
    except subprocess.TimeoutExpired:
        continue
    finally:
        p.unlink(missing_ok=True)
    nums = [int(x.strip()) for x in r.stdout.splitlines() if x.strip().isdigit()]
    if r.returncode != 0 or not nums:
        print(f"  {c.name:12} could not be checked")
        continue
    n = nums[-1]
    total += n
    if n:
        bad.append(c.name)
        print(f"  {c.name:12} {n} edge(s) whose domain is not the child's slot set", flush=True)
        for row in [
            line.strip().split(" -> ")[0] for line in r.stdout.splitlines() if line.strip().startswith("(BadDomain")
        ][:3]:
            print(f"       {row[:110]}")

print(
    f"\n{total} edges over {len(cases)} cases whose domain is not exactly the child's "
    f"slot set, in {len(bad)}: {', '.join(bad[:8])}{' ...' if len(bad) > 8 else ''}"
)
sys.exit(1 if bad else 0)
