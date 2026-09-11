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

sys.path.insert(0, "slotted/xdiff")
import xdiff as X

OBS_TEMPLATE = """
;; Observers live in their own ruleset and are run ALONE, so the machinery cannot
;; churn while they look. Running them alongside it would answer a question about
;; history instead: these are relations, and a row deleted later still leaves its
;; observation behind.
(ruleset obs)

;; a stored renaming that is not injective
(relation NotInjective (Renaming))
(rule ((RenamesToLeader a m b) (!= (map-length m) (map-length (map-image m))))
      ((NotInjective m)) :ruleset obs)

;; an edge naming more slots than its child has
(relation WideEdge (String Renaming U Renaming))
<<NODE RULES>>

(run obs 1)
(print-size NotInjective)
(print-function WideEdge 200)
"""

enc = X.slotenc
LANG = enc.read_language(X.LANG_DIR / "toy.egg")


def node_rules():
    """The per-constructor half of the observer, over the language the harness runs.

    Written over `App2` -- the string-headed constructor, which no generated case builds --
    they matched nothing, leaving only the `RenamesToLeader` rule above them live while the
    edge checks reported nothing whatever the state was. `def4-edges.py` and `stranded.py`
    share the shape and the trap.

    A BINDER column is left out of the wide-edge check, for the reason `def4-edges.py`
    gives: what sits there is a name the node binds, so its width is not its child's
    business. Its injectivity is still checked -- a renaming is a renaming.
    """
    out = []
    for name, sig in LANG.items():
        _, edges, kids, _ = enc.cols_of(sig)
        kid_cols = [c for c in sig if c in enc.SLOTTED]
        pat = enc.pattern(name, sig)
        for i in range(len(kids)):
            out.append(
                f"(rule ((= n {pat}) (!= (map-length {edges[i]}) (map-length (map-image {edges[i]}))))\n"
                f"      ((NotInjective {edges[i]})) :ruleset obs)"
            )
            if kid_cols[i] is enc.BINDER:
                continue
            out.append(
                f"(rule ((= n {pat})\n"
                f"       (RenamesToLeader {kids[i]} s {kids[i]})\n"
                f"       (= s (compose s s))\n"
                f"       (< (map-length s) (map-length {edges[i]})))\n"
                f'      ((WideEdge "{name} child {i + 1}" {edges[i]} {kids[i]} s)) :ruleset obs)'
            )
    return "\n".join(out)


OBS = OBS_TEMPLATE.replace("<<NODE RULES>>", node_rules())


def probe(case):
    prog = X.egg_program(case).replace("(print-function SameClass 100000)", OBS)
    p = X.ROOT / f"inv-{abs(hash(case.name)) % 99999}.egg"
    p.write_text(prog)
    try:
        r = subprocess.run([str(X.EGGLOG), str(p)], capture_output=True, text=True, cwd=X.ROOT, timeout=300)
    except subprocess.TimeoutExpired:
        return None
    finally:
        p.unlink(missing_ok=True)
    ni = next((int(x.strip()) for x in r.stdout.splitlines() if x.strip().isdigit()), None)
    wide = [
        line.strip().split(" -> ")[0][len("(WideEdge ") : -1]
        for line in r.stdout.splitlines()
        if line.strip().startswith("(WideEdge ")
    ]
    return ni, wide


tot_ni = tot_wide = seen = 0
for c in X.curated():
    got = probe(c)
    if got is None:
        print(f"  {c.name:34} timeout")
        continue
    seen += 1
    ni, wide = got
    tot_ni += ni or 0
    tot_wide += len(wide)
    if ni or wide:
        print(f"  {c.name:34} non-injective {ni}  wide edges {len(wide)}")
        for w in wide[:4]:
            print(f"       {w[:120]}")
# the case count is part of the result: a probe that looked at nothing would also read 0
print(f"\n{seen} cases checked, non-injective {tot_ni}, edges wider than their child {tot_wide}")
sys.exit(1 if tot_ni or tot_wide else 0)
