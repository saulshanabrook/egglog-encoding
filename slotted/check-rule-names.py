"""Does a rule's `:name` survive into the generated egglog?

egglog reports a rule by its name -- in `print-stats`, in per-rule timings, in the panic
when two rules share one. Rules compiled here were anonymous: `:name` was parsed off the
surface rewrite and then never emitted, so every generated rule was nameless and none of
that output could be read.

Nothing noticed, because a missing name changes no answer. So it is asserted here: every
name a test's source gives a rule appears on a rule in that test's snapshot.

Reads the committed snapshots rather than recompiling, so it is nearly free.

    python3 slotted/check-rule-names.py
"""

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TESTS = ROOT / "slotted/tests"
SNAPSHOTS = TESTS / "snapshots"

NAME = re.compile(r':name\s+"([^"]+)"')
BARE = re.compile(r":name\s+([^\s()\"]+)")


def main():
    checked = missing = 0
    bad = []
    for src in sorted(TESTS.glob("*.egg")):
        snap = SNAPSHOTS / src.name
        if not snap.exists():
            continue
        text = re.sub(r";[^\n]*", "", src.read_text())  # a name in prose is not a rule
        want = set(NAME.findall(text))
        # a bare `:name x` is accepted by this compiler and rejected by egglog, so it is
        # reported rather than counted -- the corpus is meant to be written egglog's way
        loose = {n for n in BARE.findall(text) if n not in want and not n.startswith('"')}
        got = set(NAME.findall(snap.read_text()))
        for n in sorted(want - got):
            bad.append(f"{src.name}: rule {n!r} has no `:name` in the generated egglog")
        for n in sorted(loose):
            bad.append(f"{src.name}: rule {n!r} is named without quotes, which egglog rejects")
        checked += len(want)
        missing += len(want - got)
    for line in bad:
        print(f"  FAIL {line}")
    print(f"\n{checked - missing}/{checked} rule names reach the generated egglog")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
