#!/usr/bin/env python3
"""Run one of the fuzz drivers wide, many seeds at once, and total the answers.

The harness runs `iso-fuzz` at 60 cases because it has to finish alongside eighteen
other checks. Sixty is not a confidence statement, and treating it as one was the gap
this exists to close: at 60 the sweep is clean, and the divergences below start at
case 66.

WHAT A DEEP RUN FINDS (24000 cases, 48 seeds, `iso` mode), and WHICH ORACLE MATTERS.

Against upstream b90adca, the oracle we pin, which HAS `final_refine`:

    23707/24000 isomorphic -- 278 divergences

      202  the encoding built FEWER nodes: a rule fired on the reference, not on us
       39  same counts, the SHAPE differs: slot sets or symmetry groups
       27  same nodes, the encoding has MORE classes: a union we did not make
       10  the encoding built MORE nodes: a rule fired on us, not on the reference

    229 of the 278 are clearly ours. Against the PREVIOUS oracle -- PR #45 before
    `final_refine` landed -- the same 24000 cases gave 23976/24000 and 17 divergences,
    12 of them ours. Nothing in the encoding changed between those two numbers. The
    oracle got sharper and revealed a gap that was always there, so the jump from 12 to
    229 is the SIZE of the gap rather than a regression.

    They are also not 278 bugs. Every one examined traced to the same cause, which
    `connected_order` documents and `xdiff.FINAL_REFINE_GAP` explains in full: the
    encoding compiles a pattern into a chain, a slot no earlier atom constrains is
    MINTED, and the mint cannot be revisited. A fresh name differs from everything, so
    the encoding only ever takes the "these slots are apart" branch. `final_refine`
    takes both. `order-independence.py` isolates the same cause without any oracle.

    The 39 shape-only divergences are the family the symmetry-generating unions
    exposed; before those existed the corpus had only identity groups and could not
    state such a case at all.

    Also measured, and NOT a divergence: ten cases died with egglog's "Rule ... was
    already present". The generator draws each rule independently and two can compile
    to the same text. Deduping them in `egg_program` fixed it; they had been counted as
    disagreements.

WHY THE SEED RANGE MATTERS. Cases are `(seed, index)` and the generator is
deterministic, so a divergence is quotable and re-runnable -- `isomorphism.py fuzz 4
1061` is the whole reproduction of one. Changing `rand_case` renumbers everything,
which is why nothing here records an index as if it were a name.

    python3 slotted/xdiff/campaign.py [mode] [--cases N] [--seeds K] [--jobs J]

`mode` is `iso` (default, the differential isomorphism sweep), `order`
(order-independence, no oracle), or `checker` (mutate the checker itself).
"""

import argparse
import re
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent

MODES = {
    "iso": (HERE / "isomorphism.py", ["fuzz"], r"(\d+)/(\d+) isomorphic"),
    "order": (HERE / "order-independence.py", [], r"(\d+)/(\d+) order independent"),
    "checker": (HERE / "checker-mutations.py", [], r"(\d+)/(\d+) count-changing mutations caught"),
}


def run_seed(script, prefix, cases, seed):
    r = subprocess.run(
        [sys.executable, str(script), *prefix, str(cases), str(seed)],
        capture_output=True,
        text=True,
        cwd=ROOT,
    )
    return seed, r.stdout + r.stderr


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("mode", nargs="?", default="iso", choices=sorted(MODES))
    ap.add_argument("--cases", type=int, default=500, help="cases per seed")
    ap.add_argument("--seeds", type=int, default=32, help="how many seeds")
    ap.add_argument("--jobs", type=int, default=0, help="parallel processes (default: one per seed)")
    ap.add_argument("--first-seed", type=int, default=1000)
    args = ap.parse_args()

    script, prefix, pattern = MODES[args.mode]
    seeds = range(args.first_seed, args.first_seed + args.seeds)
    jobs = args.jobs or args.seeds

    # Each process is serial and names its scratch files by PID, so the only shared
    # state is the read-only egglog binary.
    ok = total = 0
    findings = []
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        for seed, out in pool.map(lambda s: run_seed(script, prefix, args.cases, s), seeds):
            m = re.search(pattern, out)
            if not m:
                findings.append(f"seed {seed}: no summary line -- {out.strip().splitlines()[-1:]}")
                continue
            ok += int(m.group(1))
            total += int(m.group(2))
            for line in out.splitlines():
                if re.match(r"\s+(FAIL|limit)\s", line):
                    findings.append(f"seed={seed} {line.strip()}")

    print(f"\n{ok}/{total} pass   ({args.mode}, {args.seeds} seeds x {args.cases} cases)")
    if findings:
        print(f"\n{len(findings)} findings:")
        for line in findings:
            print(f"  {line}")
    return 1 if ok != total else 0


if __name__ == "__main__":
    sys.exit(main())
