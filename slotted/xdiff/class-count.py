"""Does the encoding have the same number of *slotted* classes as the reference?

A slotted class spans several `U` values, so counting `ClassSlots` rows over-counts. Two
values are the same class when *any* `RenamesToLeader` relates them -- including a partial
one, which is the redundancy relation (`a = m*b` with `m` dropping slots says b's class does
not depend on them) and which the reference also models as one class. Requiring a bijection
instead leaves the encoding with one extra class on `C13` and on 4 of 250 generated cases,
all of which agree under this criterion; that is how it was settled. Counting the values
that have a strictly smaller peer gives the number of non-canonical members, and

    slotted classes  =  ClassSlots rows  -  non-canonical members

which needs no value names, so it is immune to several classes printing as `Unextractable`.

Worth checking on its own: merging two classes the reference keeps apart is invisible to the
probe partition, which only compares the terms it was given, and can be invisible to node
counts too. This is the cheap version of the isomorphism check's class bijection.

    python3 slotted/xdiff/class-count.py            curated
    python3 slotted/xdiff/class-count.py fuzz 250   generated
"""

import os
import random
import subprocess
import sys

sys.path.insert(0, "slotted/xdiff")
import xdiff as X

OBS = """
(ruleset cc)
(relation NotCanon (U))
;; Both directions, because a link is not always stored both ways: marking only the `a`
;; side misses a pair whose row happens to name the smaller value first, which showed up as
;; a class with no non-canonical members even though it plainly had a peer.
(rule ((RenamesToLeader a m b) (!= a b) (= a (ordering-max a b)))
      ((NotCanon a)) :ruleset cc)
(rule ((RenamesToLeader a m b) (!= a b) (= b (ordering-max a b)))
      ((NotCanon b)) :ruleset cc)
(run cc 3)
(print-size ClassSlots)
(print-size NotCanon)
"""


def encoding_classes(case):
    prog = X.egg_program(case).replace("(print-function SameClass 100000)", OBS)
    p = X.ROOT / f"xdiff-tmp-cc-{os.getpid()}.egg"
    p.write_text(prog)
    try:
        r = subprocess.run([str(X.EGGLOG), str(p)], capture_output=True, text=True, cwd=X.ROOT, timeout=120)
    except subprocess.TimeoutExpired:
        return None
    finally:
        p.unlink(missing_ok=True)
    nums = [int(x.strip()) for x in r.stdout.splitlines() if x.strip().isdigit()]
    if r.returncode != 0 or len(nums) < 2:
        return None
    return nums[-2] - nums[-1]


def reference_classes(case):
    r = subprocess.run(
        [str(X.XMULTI / "target" / "debug" / "xmulti")],
        input=case.spec() + "term (null)\nterm (var $0)\ndump\n",
        capture_output=True,
        text=True,
        timeout=X.RUN_TIMEOUT,
    )
    if r.returncode != 0:
        return None
    if any(line.startswith("SATURATED no") for line in r.stdout.splitlines()):
        return None
    return sum(1 for line in r.stdout.splitlines() if line.startswith("CLASS "))


if len(sys.argv) > 1 and sys.argv[1] == "fuzz":
    rng = random.Random(0)
    cases = [X.rand_case(rng, i) for i in range(int(sys.argv[2]) if len(sys.argv) > 2 else 250)]
else:
    cases = X.curated()

agree = differ = skipped = 0
for c in cases:
    ref, enc = reference_classes(c), encoding_classes(c)
    if ref is None or enc is None:
        skipped += 1
        continue
    if ref == enc:
        agree += 1
    else:
        differ += 1
        arrow = "encoding has FEWER (over-merged?)" if enc < ref else "encoding has MORE"
        print(f"  {c.name:14} reference {ref}, encoding {enc}   {arrow}", flush=True)

print(f"\n{agree} agree on slotted-class count, {differ} differ, {skipped} skipped")
sys.exit(1 if differ else 0)
