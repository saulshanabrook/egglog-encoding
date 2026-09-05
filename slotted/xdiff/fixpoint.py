"""Does the machinery reach a fixpoint of its own rules?

Every other probe here reads the state after `(run N)`, which stops after N rounds
whether or not anything is still firing. A rule that deletes a row another rule rebuilds
therefore looks settled: the row counts are constant from some round on, and semi-naive
never re-runs the derivation. `saturate` asks the question directly, and a run that will
not terminate is the oscillation.

Open question 2 raised this for the self-loop rules, where it turned out to converge
whenever the program does. It then caught a second, real instance: `RenamesToLeader`
holds both directions for a pair, so migration had no fixed target and moved a node onto
the leader and straight back, forever. `MR1` was the only case that showed it, which is
why this runs the whole corpus -- the five hand-picked cases it used to check did not
include it.
"""

import subprocess
import sys
import time

sys.path.insert(0, "slotted/xdiff")
import xdiff as X

TIMEOUT = 60

# The generated corpus is where the second instance turned up, so it has to be reachable
# from here -- checking only the curated cases is what let it hide.
#     python3 slotted/xdiff/fixpoint.py            curated
#     python3 slotted/xdiff/fixpoint.py fuzz 250    generated
if len(sys.argv) > 1 and sys.argv[1] == "fuzz":
    import random

    rng = random.Random(0)
    cases = [X.rand_case(rng, i) for i in range(int(sys.argv[2]) if len(sys.argv) > 2 else 250)]
else:
    cases = X.curated()

bad = []
for case in cases:
    # The harness's schedule already saturates the `slotted` ruleset between user steps,
    # so the program only fails to finish if that saturation does not converge. User rules
    # get a finite step count and are not expected to.
    prog = X.egg_program(case)
    prog = prog.replace("(print-function SameClass 100000)", "(print-size App2)")
    p = X.ROOT / f"sat-{abs(hash(case.name)) % 99999}.egg"
    p.write_text(prog)
    t = time.time()
    try:
        r = subprocess.run([str(X.EGGLOG), str(p)], capture_output=True, text=True, cwd=X.ROOT, timeout=TIMEOUT)
        verdict = None if r.returncode == 0 else f"error: {r.stderr.strip()[:70]}"
    except subprocess.TimeoutExpired:
        verdict = f"DOES NOT TERMINATE under saturate ({TIMEOUT}s)"
    finally:
        p.unlink(missing_ok=True)
    if verdict:
        bad.append(case.name)
        print(f"  {case.name:44} {verdict}  {time.time() - t:.0f}s", flush=True)

print(f"\n{len(cases) - len(bad)}/{len(cases)} reach a fixpoint")
sys.exit(1 if bad else 0)
