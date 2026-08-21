"""Do any e-nodes sit on a follower class, at the fixpoint?

It decides whether an isomorphism check can enumerate leader classes only. A value
prints as `Unextractable` when its defining `App` rows have all been deleted, and both
rules that delete -- the alpha-finder and migration -- delete on the *follower* side.
So leaders keep their rows and stay printable. That is only useful if followers hold no
nodes, since otherwise leader-only enumeration would miss structure.

A value is a follower when a peer of its slotted class is strictly *smaller*, which is
the orientation the single-parent rule establishes. "Has an edge to a different value"
is not the test: `RenamesToLeader` holds both directions for a pair, so that is true of
the leader as well, and an earlier version of this probe counted both -- reporting a
follower holding a node where the node was on the leader.
"""
import random
import re
import subprocess
import sys
sys.path.insert(0, "slotted-experiments/xdiff")
import xdiff as X

OBS_HEAD = """
(ruleset obs)
(relation FollowerWithNode (U))
(relation Follower (U))
(rule ((RenamesToLeader a m l) (!= a l) (= a (ordering-max a l)))
      ((Follower a)) :ruleset obs)
"""


def obs():
    out = [OBS_HEAD]
    for n in (2, 3, 4):
        cols = " ".join(f"m{i} c{i}" for i in range(1, n + 1))
        out.append(f"(rule ((= v (App{n} f {cols}))\n"
                   f"       (Follower v))\n"
                   f"      ((FollowerWithNode v)) :ruleset obs)")
    out += ["(run obs 2)", "(print-size Follower)", "(print-size FollowerWithNode)"]
    return "\n".join(out)


# The curated corpus reports zero, and that is not the same as the property holding:
# `fuzz 250` finds three cases where a follower still holds a node, so run both.
#     python3 slotted-experiments/xdiff/follower-nodes.py            curated
#     python3 slotted-experiments/xdiff/follower-nodes.py fuzz 250   generated
if len(sys.argv) > 1 and sys.argv[1] == "fuzz":
    n = int(sys.argv[2]) if len(sys.argv) > 2 else 250
    rng = random.Random(0)
    cases = [X.rand_case(rng, i) for i in range(n)]
else:
    cases = X.curated()

total_followers = total_with_nodes = 0
for c in cases:
    prog = X.egg_program(c, mult=6).replace("(print-function SameClass 100000)", obs())
    p = X.ROOT / f"fn-{abs(hash(c.name)) % 99999}.egg"
    p.write_text(prog)
    try:
        r = subprocess.run([str(X.EGGLOG), str(p)], capture_output=True,
                           text=True, timeout=X.RUN_TIMEOUT, cwd=X.ROOT)
    except subprocess.TimeoutExpired:
        print(f"  {c.name:38} timeout")
        continue
    finally:
        p.unlink(missing_ok=True)
    nums = [int(x.strip()) for x in r.stdout.splitlines() if x.strip().isdigit()]
    if len(nums) < 2:
        print(f"  {c.name:38} no output")
        continue
    followers, with_nodes = nums[-2], nums[-1]
    total_followers += followers
    total_with_nodes += with_nodes
    if with_nodes:
        print(f"  {c.name:38} followers {followers}, of those holding a node "
              f"{with_nodes}")

print(f"\n{total_followers} follower classes over {len(cases)} cases, "
      f"{total_with_nodes} of them holding an e-node")
