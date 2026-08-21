"""Are the invariants the primitives and Def. 4 rely on actually maintained?

Two checks, both sound -- no proxy, no false positives.

`inverse` is total on injective input only, and nothing checks that. A composition
of injective maps is injective, so it is enough to ask whether every renaming the
machinery *stores* is injective. Non-injectivity is detectable without a new
primitive: for injective `m`, `(map-image m)` has as many keys as `m`; for a
non-injective one the image is smaller.

Def. 4 requires an edge's domain to be exactly its child's slot set. The too-wide
direction is provable: an idempotent self-loop `s` on the child is a partial
identity, so `child = s*child` and every slot outside `dom(s)` is redundant --
the child's live slots are contained in `dom(s)`. An idempotent self-loop with
FEWER keys than the edge therefore proves the edge names slots the child does not
have. Looking only for narrower witnesses is what makes this immune to the too-wide
self-loops of open question 2, which an earlier version of this probe mistook for
bad edges.

The too-narrow direction is not checked here: it is what `compose-total` now
prevents where it was reachable.
"""
import subprocess
import sys
sys.path.insert(0, "slotted-experiments/xdiff")
import xdiff as X

OBS = """
;; Observers live in their own ruleset and are run ALONE, so the machinery cannot
;; churn while they look. Running them alongside it would answer a question about
;; history instead: these are relations, and a row deleted later still leaves its
;; observation behind.
(ruleset obs)

;; a stored renaming that is not injective
(relation NotInjective (Renaming))
(rule ((RenamesToLeader a m b) (!= (map-length m) (map-length (map-image m))))
      ((NotInjective m)) :ruleset obs)
(rule ((= n (App2 f m1 c1 m2 c2)) (!= (map-length m1) (map-length (map-image m1))))
      ((NotInjective m1)) :ruleset obs)
(rule ((= n (App2 f m1 c1 m2 c2)) (!= (map-length m2) (map-length (map-image m2))))
      ((NotInjective m2)) :ruleset obs)

;; an edge naming more slots than its child has
(relation WideEdge (String Renaming U Renaming))
(rule ((= n (App2 f m1 c1 m2 c2))
       (RenamesToLeader c1 s c1)
       (= s (compose s s))
       (< (map-length s) (map-length m1)))
      ((WideEdge f m1 c1 s)) :ruleset obs)
(rule ((= n (App2 f m1 c1 m2 c2))
       (RenamesToLeader c2 s c2)
       (= s (compose s s))
       (< (map-length s) (map-length m2)))
      ((WideEdge f m2 c2 s)) :ruleset obs)

(run obs 1)
(print-size NotInjective)
(print-function WideEdge 200)
"""


def probe(case):
    prog = X.egg_program(case).replace("(print-function SameClass 100000)", OBS)
    p = X.ROOT / f"inv-{abs(hash(case.name)) % 99999}.egg"
    p.write_text(prog)
    try:
        r = subprocess.run([str(X.EGGLOG), str(p)], capture_output=True,
                           text=True, cwd=X.ROOT, timeout=300)
    except subprocess.TimeoutExpired:
        return None
    finally:
        p.unlink(missing_ok=True)
    ni = next((int(x.strip()) for x in r.stdout.splitlines()
               if x.strip().isdigit()), None)
    wide = [l.strip().split(" -> ")[0][len("(WideEdge "):-1]
            for l in r.stdout.splitlines() if l.strip().startswith("(WideEdge ")]
    return ni, wide


tot_ni = tot_wide = 0
for c in X.curated():
    got = probe(c)
    if got is None:
        print(f"  {c.name:34} timeout")
        continue
    ni, wide = got
    tot_ni += ni or 0
    tot_wide += len(wide)
    if ni or wide:
        print(f"  {c.name:34} non-injective {ni}  wide edges {len(wide)}")
        for w in wide[:4]:
            print(f"       {w[:120]}")
print(f"\ntotals: non-injective {tot_ni}, edges wider than their child {tot_wide}")
