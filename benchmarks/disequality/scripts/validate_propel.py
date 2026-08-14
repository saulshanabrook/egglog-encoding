#!/usr/bin/env python3
"""Check semantic parity across Propel's native and egglog backends."""

from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import json
import platform
import subprocess
import sys
from dataclasses import asdict, dataclass
from datetime import UTC, datetime
from pathlib import Path

ALL_VARIANTS = (
    "de",
    "ee",
    "nee",
    "egglog-ee",
    "egglog-oee",
    "egglog-nee",
    "egglog-de",
)


@dataclass(frozen=True)
class Result:
    benchmark: str
    variant: str
    result: str
    egraphs: float | None = None
    eclasses: float | None = None
    enodes: float | None = None
    detail: str | None = None


def run_benchmark(
    binary: Path,
    benchmark: Path,
    variant: str,
    timeout: float,
) -> Result:
    try:
        process = subprocess.run(
            [str(binary), "-f", str(benchmark), "--variant", variant],
            check=False,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired:
        return Result(benchmark.name, variant, "timeout")

    lines = process.stdout.splitlines()
    status = next(
        (
            "success" if "Check successful." in line else "failure"
            for line in reversed(lines)
            if "Check successful." in line or "Check failed." in line
        ),
        None,
    )
    stats_line = next((line for line in reversed(lines) if line.startswith("sum;")), None)
    if process.returncode != 0 or status is None or stats_line is None:
        detail = "\n".join(lines[-12:])
        return Result(
            benchmark.name,
            variant,
            "error",
            detail=f"exit {process.returncode}: {detail}",
        )

    try:
        _, egraphs, eclasses, enodes = stats_line.split(";")
        return Result(
            benchmark.name,
            variant,
            status,
            float(egraphs),
            float(eclasses),
            float(enodes),
        )
    except ValueError:
        return Result(
            benchmark.name,
            variant,
            "error",
            detail=f"invalid stats line: {stats_line}",
        )


def git_provenance(repository: Path) -> tuple[str, list[str]]:
    revision = subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=repository,
        check=True,
        stdout=subprocess.PIPE,
        text=True,
    ).stdout.strip()
    status = subprocess.run(
        ["git", "status", "--short", "--untracked-files=all"],
        cwd=repository,
        check=True,
        stdout=subprocess.PIPE,
        text=True,
    ).stdout.splitlines()
    return revision, status


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", type=Path, required=True)
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--glob", default="*.propel")
    parser.add_argument("--timeout", type=float, default=60.0)
    parser.add_argument("--jobs", type=int, default=4)
    parser.add_argument("--reference", choices=ALL_VARIANTS, default="de")
    parser.add_argument(
        "--variants",
        nargs="+",
        choices=ALL_VARIANTS,
        default=list(ALL_VARIANTS),
    )
    parser.add_argument("--output", type=Path)
    parser.add_argument("--allow-timeouts", action="store_true")
    parser.add_argument(
        "--repository",
        type=Path,
        default=Path(__file__).resolve().parents[3],
        help="Git checkout whose source produced the binary",
    )
    args = parser.parse_args()

    binary = args.binary.resolve()
    input_directory = args.input.resolve()
    if not binary.is_file():
        parser.error(f"Propel binary does not exist: {binary}")
    benchmarks = sorted(input_directory.glob(args.glob))
    if not benchmarks:
        parser.error(f"no files matching {args.glob!r} found in {input_directory}")
    variants = tuple(dict.fromkeys((args.reference, *args.variants)))
    repository = args.repository.resolve()
    if not (repository / ".git").exists():
        parser.error(f"repository is not a Git checkout: {repository}")
    code_revision, code_status = git_provenance(repository)

    jobs = [(binary, benchmark, variant, args.timeout) for benchmark in benchmarks for variant in variants]
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as executor:
        results = list(executor.map(lambda job: run_benchmark(*job), jobs))
    results.sort(key=lambda result: (result.benchmark, variants.index(result.variant)))

    by_benchmark = {
        benchmark.name: {result.variant: result for result in results if result.benchmark == benchmark.name}
        for benchmark in benchmarks
    }
    mismatches = []
    incomplete = []
    comparable_count = 0
    fully_complete_count = 0
    for benchmark, variant_results in by_benchmark.items():
        reference = variant_results[args.reference]
        if all(result.result not in {"timeout", "error"} for result in variant_results.values()):
            fully_complete_count += 1
        for variant, result in variant_results.items():
            if result.result in {"timeout", "error"}:
                incomplete.append({"benchmark": benchmark, "variant": variant, "result": result.result})
            elif reference.result in {"success", "failure"} and result.result != reference.result:
                comparable_count += 1
                mismatches.append(
                    {
                        "benchmark": benchmark,
                        "reference": args.reference,
                        "reference_result": reference.result,
                        "variant": variant,
                        "variant_result": result.result,
                    }
                )
            elif variant != args.reference and reference.result in {"success", "failure"}:
                comparable_count += 1

    result_counts = {
        variant: {
            result: sum(row.variant == variant and row.result == result for row in results)
            for result in ("success", "failure", "timeout", "error")
        }
        for variant in variants
    }

    corpus_hash = hashlib.sha256()
    for benchmark in benchmarks:
        corpus_hash.update(benchmark.name.encode())
        corpus_hash.update(b"\0")
        corpus_hash.update(benchmark.read_bytes())
        corpus_hash.update(b"\0")
    report = {
        "schema_version": 2,
        "generated_at": datetime.now(UTC).isoformat(),
        "platform": platform.platform(),
        "python_version": platform.python_version(),
        "code_revision": code_revision,
        "code_dirty": bool(code_status),
        "code_status": code_status,
        "binary_sha256": hashlib.sha256(binary.read_bytes()).hexdigest(),
        "corpus_sha256": corpus_hash.hexdigest(),
        "benchmark_count": len(benchmarks),
        "reference": args.reference,
        "variants": list(variants),
        "timeout_seconds": args.timeout,
        "summary": {
            "run_count": len(results),
            "fully_complete_benchmark_count": fully_complete_count,
            "comparable_count": comparable_count,
            "matched_count": comparable_count - len(mismatches),
            "mismatch_count": len(mismatches),
            "incomplete_count": len(incomplete),
            "result_counts_by_variant": result_counts,
        },
        "mismatches": mismatches,
        "incomplete": incomplete,
        "results": [asdict(result) for result in results],
    }
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")

    print(
        f"{len(benchmarks)} benchmarks x {len(variants)} variants: "
        f"{comparable_count - len(mismatches)}/{comparable_count} comparable runs matched, "
        f"{fully_complete_count} benchmarks fully complete, {len(incomplete)} incomplete runs"
    )
    for mismatch in mismatches:
        print(
            f"mismatch: {mismatch['benchmark']}: {mismatch['reference']}="
            f"{mismatch['reference_result']}, {mismatch['variant']}={mismatch['variant_result']}",
            file=sys.stderr,
        )
    for row in incomplete:
        print(
            f"incomplete: {row['benchmark']}: {row['variant']}={row['result']}",
            file=sys.stderr,
        )
    has_errors = any(row["result"] == "error" for row in incomplete)
    has_disallowed_timeouts = any(row["result"] == "timeout" for row in incomplete) and not args.allow_timeouts
    return int(bool(mismatches or has_errors or has_disallowed_timeouts))


if __name__ == "__main__":
    raise SystemExit(main())
