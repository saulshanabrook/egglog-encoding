"""Does the corpus still catch each bug it was built to catch?

Coverage is a property, so it is asserted rather than inspected. Each mutation puts a past
bug back into the compiler and the corpus must still break by the recorded amount: fewer
means the corpus has stopped testing something, more means a case newly disagrees and wants
looking at either way.

A mutation earns its place by *failing* here when reintroduced. One that stops discriminating
is not kept as decoration -- `wide-kids` and `binder-1st` were both removed once they stopped,
the first because `def4-edges.py` checks the property it stood for and the second because the
rule it violated is definitional rather than empirical.

`unordered` went the same way, and for a better reason than the others: compiling the atoms
in the order written used to lose matches, and a rule that tries every naming recovers them,
so the mutation no longer breaks a single case. That is the property `order-independence.py`
measures directly, which is where it is checked now.

    python3 slotted/xdiff/mutations.py
"""

import os
import re
import subprocess
import sys

sys.path.insert(0, "slotted/xdiff")
import xdiff as X

#: mutation -> cases of the curated corpus that must disagree with the reference
EXPECTED = {
    # 2 rather than 10: a rule now tries every naming an atom's renaming could take,
    # so solving one from its root alone loses far fewer matches -- most of the corpus
    # recovers on another index. It still discriminates, so it stays.
    # 2 before the end-of-rule refinement. With minting single-valued again, solving
    # an atom's renaming from its root alone genuinely under-constrains, and the
    # refinement no longer papers over it -- so the mutant is MORE visible, not less.
    "root-only": 11,  # an atom's renaming solved from its root alone
    "union-id": 2,  # the action unions classes instead of invocations
    "slot-late": 1,  # a slot literal checked after the renaming, not with it
}


def mismatches(bugs):
    """Curated cases whose matching disagrees with the reference, under `bugs`."""
    env = dict(os.environ, XDIFF_BUGS=bugs)
    r = subprocess.run(
        [sys.executable, "slotted/xdiff/xdiff.py"],
        capture_output=True,
        text=True,
        cwd=X.ROOT,
        env=env,
        timeout=3600,
    )
    m = re.search(r"^\s*(\d+)\s+MATCHING mismatch", r.stdout, re.M)
    return int(m.group(1)) if m else None


bad = []
clean = mismatches("")
print(f"  {'(no mutation)':14} {clean} mismatches, expected 0")
if clean != 0:
    bad.append("the unmutated corpus does not agree with the reference")

for bug, want in EXPECTED.items():
    got = mismatches(bug)
    note = (
        ""
        if got == want
        else ("  <-- STOPPED DISCRIMINATING" if got is not None and got < want else "  <-- more than recorded")
    )
    print(f"  {bug:14} {got} mismatches, expected {want}{note}", flush=True)
    if got != want:
        bad.append(f"{bug}: {got} != {want}")

print(f"\n{len(EXPECTED) - len([b for b in bad if not b.startswith('the')])}/{len(EXPECTED)} mutations still caught")
for b in bad:
    print(f"  FAIL {b}")
sys.exit(1 if bad else 0)
