#!/usr/bin/env python3
"""Run one of the fuzz drivers wide, many seeds at once, and total the answers.

The harness keeps its CI sweep deliberately small; this command is for wider manual
campaigns. The executable and reference revision come from the current checkout and
`slotted/xmulti/Cargo.toml` respectively. Each worker reports its own failures.

Cases are identified by `(seed, index)`. Keep both when recording a failing case;
changing the generator changes those identities.

    python3 slotted/xdiff/campaign.py [mode] [--cases N] [--seeds K] [--jobs J]

`mode` is `iso` (default, the differential isomorphism sweep), `order`
(order-independence, no oracle), or `checker` (mutate the checker itself).

DEEP GROUND. The generator's knobs are environment variables and reach every worker,
so a wider search is a knob set in front of the same command. This one puts terms at
depth three with repeated subterms, shares a repeated body as one pattern variable,
and has lambda bodies use their binders:

    XDIFF_DEPTH=3 XDIFF_DUP=0.4 XDIFF_SHARE=0.7 XDIFF_LAM=0.55 XDIFF_USEBIND=0.6 \
    python3 slotted/xdiff/campaign.py iso --cases 300 --seeds 8

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
