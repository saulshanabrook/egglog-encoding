#!/usr/bin/env python3
"""A native child union must not restore obsolete cached shapes or symmetries."""

import itertools
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path[:0] = [str(ROOT / "slotted"), str(ROOT / "slotted" / "xdiff")]
import xdiff as X  # noqa: E402


def program(reverse, order):
    maintenance = X.slotenc.machinery_schedule()
    children = [
        "(let $a (F (map-of 0 0) $v (map-of 0 1) $v))",
        "(let $b (G (map-of 0 0) $v (map-of 0 1) $v))",
    ]
    if reverse:
        children.reverse()
    parents = [
        "(H (map-of 0 1 1 0) $a (map-of 0 0) $v)",
        "(H (map-of 0 0 1 1) $b (map-of 0 0) $v)",
        "(H (map-of 0 1 1 0) $b (map-of 0 0) $v)",
    ]
    # Cache shapes for two different children, only one of which has a swap.
    # The native union makes the old row-based cache keys collide. In the failing
    # order an obsolete shape overwrote a fresh one after its producer had run.
    lines = [
        X.machinery("toy"),
        "(let $v (SlottedVar_0 0))",
        *children,
        maintenance,
        "(Equated_0 $b (map-of 0 1 1 0) $b)",
        maintenance,
        *(parents[i] for i in order),
        maintenance,
        "(union $a $b)",
        maintenance,
        # Reinsert an equivalent parent. Stale shapes used to leave two H rows.
        parents[1].replace("$b", "$a"),
        maintenance,
        "(print-size H)",
    ]
    cached = X.slotenc.shapeof_call("H", ["m1", "m2"], ["g1", "g2"])
    lines.append(f"""
(ruleset observe)
(relation Fresh ())
(relation ObservedReadings ())
(relation StaleReadings ())
(rule ((= c (H m1 c1 m2 c2))
       (= g1 (EclassGroup_0 c1)) (= g2 (EclassGroup_0 c2))
       (= direct (node-shape (vec-of m1 m2) (vec-of g1 g2)))
       (= (values s1 s2 back syms) {cached})
       (= s1 (vec-get direct 0)) (= s2 (vec-get direct 1))
       (= back (vec-get direct 2)) (= syms (symmetries-of direct 3)))
      ((Fresh)) :ruleset observe)
(rule ((= stored (CosetReps_0 c pinned))) ((ObservedReadings)) :ruleset observe)
(rule ((= stored (CosetReps_0 c pinned)) (= grp (EclassGroup_0 c))
       (!= stored (group-coset-reps grp pinned)))
      ((StaleReadings)) :ruleset observe)
(run observe 1)
(check (Fresh))
(check (ObservedReadings))
(print-size StaleReadings)
""")
    return "\n".join(lines)


def main():
    cases = 0
    with tempfile.TemporaryDirectory(prefix="slotted-shape-cache-") as scratch:
        path = Path(scratch) / "case.egg"
        for reverse, order in itertools.product((False, True), itertools.permutations(range(3))):
            path.write_text(program(reverse, order))
            result = subprocess.run([str(X.EGGLOG), str(path)], capture_output=True, text=True, timeout=30, cwd=ROOT)
            assert result.returncode == 0, (reverse, order, result.stderr)
            assert result.stdout.split() == ["1", "0"], (reverse, order, result.stdout)
            cases += 1
    print(f"OK: {cases} child-union orders preserve fresh shapes and leave one parent node")


if __name__ == "__main__":
    main()
