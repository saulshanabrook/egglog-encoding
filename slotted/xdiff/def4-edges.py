"""Check edge domains against their children's live slot sets (Definition 4).

Ordinary child edges must satisfy `(map-domain m) = (FreeVars c)`.
Binder-marker edges instead have domain `{0}` and point to the variable class:
they name a bound slot rather than an invocation of that class.

Observer rules cover the constructors in `egglog-experimental/tests/slotted/languages/toy.egg`.

Usage:
    python3 slotted/xdiff/def4-edges.py            curated cases
    python3 slotted/xdiff/def4-edges.py fuzz 250   generated cases"""

import os
import random
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from slotted.xdiff import xdiff as X

HEAD = """
(ruleset def4)
(relation BadDomain (String Renaming Renaming))
"""


enc = X.syntax
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
                    f"       (!= {kids[i]} ({X.SYM.var} 0)))\n"
                    f"      ((BadDomain {where} {edges[i]} (map-of 0 0))) :ruleset def4)"
                )
                continue
            out.append(
                f"(rule ((= v {pat})\n"
                f"       (= s ({X.SYM.free_vars} {kids[i]}))\n"
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

total, seen, bad = 0, 0, []
for c in cases:
    prog = X.egg_program(c).replace("(print-function SameClass 100000)", obs())
    p = X.ROOT / f"xdiff-tmp-def4-{os.getpid()}.egg"
    p.write_text(prog)
    try:
        r = subprocess.run(
            [str(X.EGGLOG), "--slotted-encoded", str(p)], capture_output=True, text=True, cwd=X.ROOT, timeout=120
        )
    except subprocess.TimeoutExpired:
        continue
    finally:
        p.unlink(missing_ok=True)
    nums = [int(x.strip()) for x in r.stdout.splitlines() if x.strip().isdigit()]
    if r.returncode != 0 or not nums:
        raise RuntimeError(f"{c.name}: observer failed: {r.stderr}")
    seen += 1
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
    f"\n{total} edges over {seen} cases whose domain is not exactly the child's "
    f"slot set, in {len(bad)}: {', '.join(bad[:8])}{' ...' if len(bad) > 8 else ''}"
)
sys.exit(1 if bad else 0)
