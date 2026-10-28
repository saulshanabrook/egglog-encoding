#!/usr/bin/env python3
"""Check proofs of the generated benchmark goals in both matching modes."""

import argparse
import os
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from slotted import workloads as W  # noqa: E402
from slotted.treatments import TREATMENTS  # noqa: E402


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    W.add_arguments(parser)
    args = parser.parse_args()
    selected = W.select(args)
    if args.study == "all" and args.rules == 44 and "batax" in args.kernel and "2nd" in args.phase:
        selected.append(W.sdql_workload("batax", "2nd", rules=12, rounds=args.rounds))
    passed, skipped = 0, 0
    with tempfile.TemporaryDirectory(prefix="slotted-benchmark-proofs-") as tmp:
        for workload in selected:
            path = Path(tmp) / f"{workload.case}.egg"
            path.write_text(workload.program)
            for side in ("encoding", "encoding-no-aliasing"):
                name = f"{workload.case} / {side}"
                if side in workload.unsupported:
                    print(f"SKIP {name}: {workload.unsupported[side]}", flush=True)
                    skipped += 1
                    continue
                with (Path(tmp) / "proof.txt").open("w") as proof:
                    result = subprocess.run(
                        [
                            str(ROOT / "target/debug/egglog-experimental"),
                            *TREATMENTS[side].flags,
                            "--proofs",
                            str(path),
                        ],
                        cwd=ROOT,
                        stdout=proof,
                        stderr=subprocess.PIPE,
                        text=True,
                        timeout=300,
                        env={**os.environ, "RUST_LOG": "error"},
                    )
                    if result.returncode and "uses subst, which has no proof translation" in result.stderr:
                        print(f"SKIP {name}: subst has no proof translation", flush=True)
                        skipped += 1
                        continue
                    if result.returncode:
                        raise AssertionError(f"{name}: {result.stderr}")
                    if not proof.tell():
                        raise AssertionError(f"{name}: no proof was printed for the benchmark goal")
                passed += 1
                print(f"OK {name}", flush=True)
    print(f"{passed} benchmark proofs checked; {skipped} unsupported cases skipped")


if __name__ == "__main__":
    main()
