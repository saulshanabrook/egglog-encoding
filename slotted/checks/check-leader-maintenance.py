#!/usr/bin/env python3
"""A native union reversing a leader edge must preserve the new leader's state."""

import itertools
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path[:0] = [str(ROOT / "slotted"), str(ROOT / "slotted" / "xdiff")]
import xdiff as X  # noqa: E402


def program(constructors, reverse_union, symmetric):
    maintenance = X.slotenc.machinery_schedule()
    # Values start in order a < b < c. First c follows b under a swap. Unioning
    # c into a then leaves the obsolete edge a -> b, while a is the new leader.
    # Clearing followers in that same rule batch used to delete a's identity and
    # group. Unchanged ClassSlots/Equated rows do not re-fire to restore them.
    lines = [X.machinery("toy"), "(let $v (SlottedVar_0 0))"]
    lines += [
        f"(let ${name} ({ctor} (map-of 0 0) $v (map-of 0 1) $v))"
        for name, ctor in zip("abc", constructors, strict=True)
    ]
    lines += [maintenance, "(Equated_0 $c (map-of 0 1 1 0) $b)", maintenance]
    if symmetric:
        lines += ["(Equated_0 $a (map-of 0 1 1 0) $a)", maintenance]
    lines += [
        "(union $c $a)" if reverse_union else "(union $a $c)",
        maintenance,
        "(check (RenamesToLeader_0 $a (map-of 0 0 1 1) $a))",
        "(check (= g (EclassGroup_0 $a)) (set-contains g (map-of 0 0 1 1)))",
    ]
    if symmetric:
        lines.append("(check (= g (EclassGroup_0 $a)) (set-contains g (map-of 0 1 1 0)))")
    return "\n".join(lines)


def main():
    cases = 0
    with tempfile.TemporaryDirectory(prefix="slotted-leader-maintenance-") as scratch:
        path = Path(scratch) / "case.egg"
        for args in itertools.product(itertools.permutations("FGH"), (False, True), (False, True)):
            path.write_text(program(*args))
            result = subprocess.run([str(X.EGGLOG), str(path)], capture_output=True, text=True, timeout=30, cwd=ROOT)
            assert result.returncode == 0, (args, result.stderr)
            cases += 1
    print(f"OK: {cases} leader reversals preserve identities and symmetries")


if __name__ == "__main__":
    main()
