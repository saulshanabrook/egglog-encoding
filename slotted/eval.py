#!/usr/bin/env python3
"""Benchmark the slotted paper workloads, without caching or graph verification.

    python3 slotted/eval.py array
    python3 slotted/eval.py sdql --kernel batax --phase 1st
    python3 slotted/eval.py --samples 3 --jobs 4

Use check.py with the same workload selectors for counts and exact isomorphism.
Release builds, rewrite budgets, and treatment configuration are shared. Timings
include source transformation and goal checks, but no graph export or search.
"""

import statistics
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))

from slotted import runner as run  # noqa: E402
from slotted import workloads as workloads  # noqa: E402
from slotted.treatments import BENCHMARK_SIDES, SIDES, TIMING_PAIRS, TREATMENTS  # noqa: E402


def benchmark(workload, *, sides=BENCHMARK_SIDES, samples=1, timeout=300, config=None, progress=run.quiet_progress):
    rows = []
    for side in workload.supported_sides(sides):
        for _ in range(samples):
            row = run.run(workload, side, timeout, progress, config=config)
            progress(row, "done")
            rows.append(row)
    return rows


def timing_cell(rows):
    if not rows:
        return "—"
    if any(row.goal == "timeout" for row in rows):
        return "timeout"
    if any(row.seconds is None for row in rows):
        return "—"
    return f"{statistics.median(row.seconds for row in rows):.3g}"


def report(selected, results, sides):
    tables = []
    groups = [
        ("Multipattern matching" if TREATMENTS[enc].matcher == "multi" else "Nested matching", (enc, ref))
        for enc, ref in TIMING_PAIRS.items()
    ]
    extra = tuple(side for side in sides if side not in BENCHMARK_SIDES)
    if extra:
        groups.append(("Additional treatments", extra))
    for title, pair in groups:
        shown = [side for side in pair if side in sides]
        if not shown:
            continue
        cells = []
        for workload, rows in zip(selected, results, strict=True):
            cells.append(
                [
                    workloads.workload_label(workload.study, workload.case, workload.rules),
                    *(
                        "unsupported"
                        if side in workload.unsupported
                        else timing_cell([r for r in rows if r.side == side])
                        for side in shown
                    ),
                ]
            )
        tables.append(title + "\n\n" + run.table(["Benchmark", *(TREATMENTS[s].label for s in shown)], cells))
    return "\n\n".join(tables)


def main(argv=None):
    parser = run.parser(__doc__.splitlines()[0])
    parser.add_argument(
        "--samples", type=run.positive_int, default=1, help="fresh timed samples per treatment (default 1)"
    )
    parser.add_argument(
        "--treatments",
        nargs="+",
        choices=SIDES,
        default=BENCHMARK_SIDES,
        help="default: both encoding variants and their timing baselines",
    )
    args = parser.parse_args(argv)
    if len(set(args.treatments)) != len(args.treatments):
        parser.error("duplicate treatments selected")
    try:
        selected = workloads.select(args)
        config = run.setup(args, selected, args.treatments)
        results = run.run_workloads(
            selected,
            benchmark,
            jobs=args.jobs,
            config=config,
            timeout=args.timeout,
            sides=args.treatments,
            samples=args.samples,
        )
        print(report(selected, results, args.treatments))
        print(f"\nElapsed seconds (median of {args.samples} fresh sample(s)); timeout if any sample times out.")
        print("Completed runs include missed goals. Parallel timings include contention.")
        budget = "paper/fixture defaults" if args.rounds is None else str(args.rounds)
        print(f"Rewrite iterations: {budget}. Timeout: {args.timeout}s. Concurrent workloads: {args.jobs}.")
        print("Graph correctness is checked separately by slotted/check.py.")
        print()
        for side in args.treatments:
            print(f"- {TREATMENTS[side].label}: {TREATMENTS[side].description}")
        for workload in selected:
            for side, reason in workload.unsupported.items():
                if side in args.treatments:
                    print(f"- {workload.case} / {side}: unsupported: {reason}")
        errors = list(dict.fromkeys(run.goal_errors([row for group in results for row in group])))
        if errors:
            print("\nBENCHMARK GOALS FAILED\n" + "\n".join(errors))
        return int(bool(errors))
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        print(f"slotted benchmark failed: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
