"""Which cases does PR #45's multipat fix actually change?

`multipat.rs` is in `main` too, so the bug -- `extend_subst` storing a child
`AppliedId` without canonicalising it through the slot union-find -- was in the
original. PR #45 adds the one-line fix. The encoding is compared against the fixed
version, so this asks which of our cases can tell the two apart: those are the ones
whose agreement is evidence about the *fixed* semantics rather than either.
"""

import subprocess
import sys

sys.path.insert(0, "slotted/xdiff")
# A second oracle built against another slotted-egraphs revision. To make one:
#
#   D=/tmp/slotted-main
#   git -C <slotted-egraphs> archive main | tar -x -C $D
#   cp -r slotted/xmulti /tmp/xmulti-main && rm -rf /tmp/xmulti-main/target
#   sed -i "s|path = .*slotted-egraphs.|path = \"$D\"|" /tmp/xmulti-main/Cargo.toml
#   cargo build --manifest-path /tmp/xmulti-main/Cargo.toml
#
# then point OTHER_XMULTI at its binary.
import os

import xdiff as X

OTHER = os.environ.get("OTHER_XMULTI")
if not OTHER:
    sys.exit("set OTHER_XMULTI to a second oracle binary (see the comment above)")


def run(binary, case):
    try:
        r = subprocess.run([binary], input=case.spec(), capture_output=True, text=True, timeout=X.RUN_TIMEOUT)
    except subprocess.TimeoutExpired:
        return "TIMEOUT"
    if r.returncode != 0:
        return "CRASH " + r.stderr.strip().splitlines()[-1][:60]
    for line in r.stdout.splitlines():
        if line.startswith("PARTITION"):
            return line
    return "?"


fixed_bin = str(X.XMULTI / "target" / "debug" / "xmulti")
differ, same, broken = [], 0, []
for c in X.curated():
    a, b = run(fixed_bin, c), run(OTHER, c)
    if a.startswith("CRASH") or b.startswith("CRASH"):
        broken.append((c.name, a[:40], b[:40]))
    elif a != b:
        differ.append((c.name, a, b))
    else:
        same += 1

print(f"{same} cases identical under both, {len(differ)} differ, {len(broken)} crashed\n")
for name, a, b in differ:
    print(f"  {name}")
    print(f"      this oracle  {a}")
    print(f"      other oracle {b}")
for name, a, b in broken:
    print(f"  {name}: this={a} other={b}")
