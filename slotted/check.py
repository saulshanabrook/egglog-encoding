#!/usr/bin/env python3
"""Check every supported treatment on the slotted paper workloads.

    python3 slotted/check.py array
    python3 slotted/check.py sdql --kernel mmm_sum --phase 1st
    python3 slotted/check.py logic

Uses the same workload selectors, release binaries, and treatment configuration
as eval.py. Each treatment gets a goal check and a separate input-only graph
export. Counts and independently verified isomorphism are both required for the
exact pairs defined in treatments.py. Other pairs are diagnostic. Reference
timeouts are explicitly unverified; errors and inconclusive non-timeout evidence
fail the command. Rust isomorphism checks use work limits, not wall-clock timeouts.
"""

import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))

from slotted import runner as run  # noqa: E402
from slotted import verify as verification  # noqa: E402
from slotted import workloads as workloads  # noqa: E402
from slotted.treatments import EXACT_PAIRS, SIDES, TREATMENTS  # noqa: E402

ERROR_TITLE = "SLOTTED CORRECTNESS CHECKS FAILED OR INCOMPLETE"


def check_workload(workload, *, sides=SIDES, timeout=300, config=None, progress=run.quiet_progress):
    rows = []
    for side in workload.supported_sides(sides):
        row = run.run(workload, side, timeout, progress, config=config)
        verification.collect_graph(workload, row, timeout, progress, config=config)
        progress(row, "done")
        rows.append(row)
    verification.compare(rows, progress, checker=config.checker if config else None)
    for row in rows:
        # Comparisons retain the paired rows, but no large graphs leave this worker.
        row.graph = None
    return rows


def report(selected, results):
    sizes, comparisons, diagnostics, errors, unsupported = [], [], [], [], []
    for workload, rows in zip(selected, results, strict=True):
        label = workloads.workload_label(workload.study, workload.case, workload.rules)
        for row in rows:
            sizes.append(
                (label, TREATMENTS[row.side].label, row.rounds, row.goal, row.classes, row.nodes, row.saturated)
            )
            if row.graph_issue:
                diagnostics.append((label, TREATMENTS[row.side].label, row.graph_issue))
        verdicts, failures = verification.assess(rows)
        comparisons += [
            (label, TREATMENTS[enc].label, ref, "required" if EXACT_PAIRS[enc] == ref else "diagnostic", verdict)
            for enc, ref, verdict in verdicts
        ]
        errors += [f"{label}: {failure}" for failure in failures]
        unsupported += [f"{label} / {side}: unsupported: {reason}" for side, reason in workload.unsupported.items()]
    print(run.table(("Benchmark", "Treatment", "Rounds", "Goal", "Classes", "Nodes", "Saturated"), sizes))
    print("\n" + run.table(("Benchmark", "Encoding", "Reference", "Requirement", "Verdict"), comparisons))
    if diagnostics:
        print("\n" + run.table(("Benchmark", "Treatment", "Graph diagnostic"), diagnostics))
    if unsupported:
        print("\n" + "\n".join(unsupported))
    if errors:
        print("\n" + ERROR_TITLE + "\n" + "\n".join(errors))
    else:
        skipped = sum(verdict == "not compared: reference timeout" for *_, verdict in comparisons)
        print(f"\nNo failures; {skipped} comparison(s) unverified due to reference timeouts.")
    return errors


def main(argv=None):
    parser = run.parser(__doc__.splitlines()[0])
    parser.add_argument(
        "--group-limit",
        type=int,
        default=run.GROUP_LIMIT,
        help="maximum exported symmetries per reference class (default 100000)",
    )
    args = parser.parse_args(argv)
    if args.group_limit < 0:
        parser.error("--group-limit must be nonnegative")
    try:
        selected = workloads.select(args)
        config = run.setup(args, selected, config=run.Config(group_limit=args.group_limit))
        if not args.no_build:
            subprocess.run(
                ["cargo", "build", "--release", "-p", "egraph-isomorphism"], cwd=run.ROOT, check=True, stdout=sys.stderr
            )
        if not config.checker.is_file():
            raise ValueError(f"missing {config.checker}; run without --no-build")
        print(f"isomorphism {config.checker}", file=sys.stderr)
        results = run.run_workloads(selected, check_workload, jobs=args.jobs, config=config, timeout=args.timeout)
        return int(bool(report(selected, results)))
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        print(f"slotted checks failed: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
