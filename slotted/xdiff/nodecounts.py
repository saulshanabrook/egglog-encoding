"""Compare the two sides on e-node counts per operator, not just the probe partition.

A probe partition only sees what someone thought to probe: it says which of a handful
of terms ended up together, and nothing about the rest of the e-graph. Counting nodes
per operator sees the whole thing, so a spurious node, a missing one, or a merge that
should not have happened shows up whether or not a probe was aimed at it.

`var` and `null` are excluded. The reference holds a variable as a `var` *node* in its
own class; the encoding holds it as the nullary constructor `(Var 0)`, which is a
value rather than an `App` row. Both are canonical singletons, so counting them would
compare bookkeeping rather than content.
"""

import collections
import re
import subprocess
import sys

sys.path.insert(0, "slotted/xdiff")
import xdiff as X

SKIP = {"var", "null"}
# the encoding's name for the binder differs; see `LANG` in xdiff.py
UNMAP = {"lambda": "lam"}


def reference_counts(case):
    r = subprocess.run(
        [str(X.XMULTI / "target" / "debug" / "xmulti")],
        input="dump\n" + case.spec(),
        capture_output=True,
        text=True,
        timeout=X.RUN_TIMEOUT,
    )
    if r.returncode != 0:
        return None, "crash"
    if "SATURATED no" in r.stdout:
        return None, "unsaturated"
    counts = collections.Counter()
    for line in r.stdout.splitlines():
        if not line.startswith("NODE "):
            continue
        op = next(w[2:] for w in line.split()[2:] if w.startswith("o:"))
        if op not in SKIP:
            counts[op] += 1
    return counts, None


def encoding_counts(case):
    prog = X.egg_program(case).replace(
        "(print-function SameClass 100000)", "\n".join(f"(print-function App{n} 100000)" for n in (2, 3, 4))
    )
    p = X.ROOT / f"nc-{abs(hash(case.name)) % 99999}.egg"
    p.write_text(prog)
    try:
        r = subprocess.run([str(X.EGGLOG), str(p)], capture_output=True, text=True, cwd=X.ROOT, timeout=X.RUN_TIMEOUT)
    except subprocess.TimeoutExpired:
        return None, "timeout"
    finally:
        p.unlink(missing_ok=True)
    if r.returncode != 0:
        return None, "crash"
    counts = collections.Counter()
    for line in r.stdout.splitlines():
        line = line.strip()
        m = re.match(r'\(App\d "([^"]+)"', line)
        if m:
            op = UNMAP.get(m.group(1), m.group(1))
            if op not in SKIP:
                counts[op] += 1
    return counts, None


agree = differ = skipped = 0
# The curated corpus is not where a surplus alpha-variant row would first show up, so this
# takes `fuzz N` as well:
#     python3 slotted/xdiff/nodecounts.py            curated
#     python3 slotted/xdiff/nodecounts.py fuzz 250   generated
if len(sys.argv) > 1 and sys.argv[1] == "fuzz":
    import random

    _rng = random.Random(0)
    _cases = [X.rand_case(_rng, i) for i in range(int(sys.argv[2]) if len(sys.argv) > 2 else 250)]
else:
    _cases = X.curated()

for c in _cases:
    ref, why = reference_counts(c)
    if ref is None:
        skipped += 1
        print(f"  {c.name:38} skipped ({why})")
        continue
    enc, why = encoding_counts(c)
    if enc is None:
        skipped += 1
        print(f"  {c.name:38} skipped (encoding {why})")
        continue
    if ref == enc:
        agree += 1
    else:
        differ += 1
        only_ref = {k: v for k, v in ref.items() if enc.get(k) != v}
        only_enc = {k: v for k, v in enc.items() if ref.get(k) != v}
        print(f"  {c.name:38} DIFFER")
        print(f"      reference {dict(sorted(only_ref.items()))}")
        print(f"      encoding  {dict(sorted(only_enc.items()))}")

print(f"\n{agree} agree on node counts, {differ} differ, {skipped} skipped")
