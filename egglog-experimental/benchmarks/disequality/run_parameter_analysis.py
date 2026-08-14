#!/usr/bin/env python3
"""Benchmark the relational Egglog parameter analysis against the native artifact."""

from __future__ import annotations

import argparse
import csv
import json
import subprocess
import tempfile
import time
from collections.abc import Sequence
from pathlib import Path
from typing import Any

FIELDS = (
    "engine",
    "encoding",
    "load_mode",
    "trial",
    "ratio",
    "wall_ms",
    "native_full_ms",
    "term_rules_ms",
    "pair_rules_ms",
    "disequality_rules_ms",
    "other_rules_ms",
    "non_ruleset_wall_ms",
    "total_nodes",
    "total_classes",
)


def duration_ms(value: str) -> float:
    """Convert the Rust debug duration printed by the native artifact to milliseconds."""

    units = (
        ("ns", 1e-6),
        ("us", 1e-3),
        ("\N{MICRO SIGN}s", 1e-3),
        ("ms", 1.0),
        ("s", 1e3),
    )
    for suffix, multiplier in units:
        if value.endswith(suffix):
            return float(value[: -len(suffix)]) * multiplier
    raise ValueError(f"unsupported duration {value!r}")


def native_row(stdout: str) -> dict[str, str]:
    """Parse the native artifact's one-row CSV output."""

    rows = list(csv.DictReader(stdout.splitlines()))
    if len(rows) != 1:
        raise ValueError(f"expected one native CSV row, got {len(rows)}:\n{stdout}")
    return rows[0]


def ruleset_ms(summary: dict[str, Any]) -> dict[str, float]:
    """Collapse supported timing-summary phases to milliseconds by ruleset."""

    schema_version = summary.get("schema_version")
    if schema_version == 2:
        fields = ("search_ns", "apply_ns", "unattributed_ns", "merge_ns", "rebuild_ns")
    elif schema_version == 4:
        fields = ("assembly_ns", "search_ns", "apply_ns", "execution_ns", "merge_ns")
    else:
        raise ValueError(f"unexpected timing summary schema: {schema_version!r}")
    result: dict[str, float] = {}
    for row in summary.get("rulesets", []):
        name = str(row["name"])
        nanoseconds = sum(int(row[field]) for field in fields)
        result[name] = nanoseconds / 1_000_000.0
    return result


def validate_facts(facts: Path, ratio: str) -> None:
    """Require the runner's ratio to match the committed generated configuration."""

    manifest = json.loads((facts / "manifest.json").read_text(encoding="utf-8"))
    if float(manifest["generation"]["ratio_f32"]) != float(ratio):
        raise ValueError(
            f"fact ratio {manifest['generation']['ratio_text']} does not match requested ratio {ratio}"
        )


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--egglog", type=Path, required=True, help="egglog-experimental binary")
    parser.add_argument("--program", type=Path, required=True, help="parameter-analysis.egg")
    parser.add_argument("--facts", type=Path, required=True, help="generated fact directory")
    parser.add_argument("--native-ee", type=Path, required=True)
    parser.add_argument("--native-de", type=Path, required=True)
    parser.add_argument("--native-input", type=Path, required=True, help="artifact exprs.in for native programs")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--ratio", default="0.5")
    parser.add_argument("--trials", type=int, default=5)
    args = parser.parse_args(argv)
    if args.trials < 1:
        parser.error("--trials must be positive")
    validate_facts(args.facts, args.ratio)

    endpoints = [("egglog", encoding, args.egglog) for encoding in ("ee", "oee", "nee", "de")] + [
        ("native", "ee", args.native_ee),
        ("native", "de", args.native_de),
    ]
    observations: list[dict[str, str | int]] = []
    for trial in range(1, args.trials + 1):
        offset = (trial - 1) % len(endpoints)
        for engine, encoding, executable in endpoints[offset:] + endpoints[:offset]:
            with tempfile.TemporaryDirectory(prefix="disequality-parameter-") as directory:
                summary_path = Path(directory) / "timing-summary.json"
                if engine == "egglog":
                    command = [
                        str(executable),
                        "--disequality-encoding",
                        encoding,
                        "--threads",
                        "1",
                        "--fact-directory",
                        str(args.facts),
                        "--timing-summary",
                        str(summary_path),
                        str(args.program),
                    ]
                else:
                    command = [str(executable), str(args.native_input), args.ratio]
                started = time.perf_counter()
                completed = subprocess.run(command, check=True, capture_output=True, text=True)
                wall_ms = (time.perf_counter() - started) * 1_000.0

                if engine == "egglog":
                    timings = ruleset_ms(json.loads(summary_path.read_text(encoding="utf-8")))
                    required = {
                        "parameter-analysis-terms",
                        "parameter-analysis-pairs",
                        "@disequality",
                    }
                    missing = required - timings.keys()
                    if missing:
                        raise ValueError(f"egglog timing summary omitted rulesets: {sorted(missing)}")
                    term_ms = timings.pop("parameter-analysis-terms")
                    pair_ms = timings.pop("parameter-analysis-pairs")
                    disequality_ms = timings.pop("@disequality")
                    other_ms = sum(timings.values())
                    measured_rules_ms = term_ms + pair_ms + disequality_ms + other_ms
                    observations.append(
                        {
                            "engine": "egglog",
                            "encoding": encoding,
                            "load_mode": "relational-input",
                            "trial": trial,
                            "ratio": args.ratio,
                            "wall_ms": f"{wall_ms:.3f}",
                            "native_full_ms": "",
                            "term_rules_ms": f"{term_ms:.3f}",
                            "pair_rules_ms": f"{pair_ms:.3f}",
                            "disequality_rules_ms": f"{disequality_ms:.3f}",
                            "other_rules_ms": f"{other_ms:.3f}",
                            "non_ruleset_wall_ms": f"{max(0.0, wall_ms - measured_rules_ms):.3f}",
                            "total_nodes": "",
                            "total_classes": "",
                        }
                    )
                else:
                    row = native_row(completed.stdout)
                    if row["method"] != encoding:
                        raise ValueError(f"unexpected native result: {row}")
                    if float(row["ratio"]) != float(args.ratio):
                        raise ValueError(f"native result used the wrong ratio: {row}")
                    if row["contradiction"] != "N":
                        raise ValueError(f"native result reported a contradiction: {row}")
                    observations.append(
                        {
                            "engine": "native",
                            "encoding": encoding,
                            "load_mode": "native-api",
                            "trial": trial,
                            "ratio": row["ratio"],
                            "wall_ms": f"{wall_ms:.3f}",
                            "native_full_ms": f"{duration_ms(row['full_time']):.3f}",
                            "term_rules_ms": "",
                            "pair_rules_ms": "",
                            "disequality_rules_ms": "",
                            "other_rules_ms": "",
                            "non_ruleset_wall_ms": "",
                            "total_nodes": row["number_nodes"],
                            "total_classes": row["number_classes"],
                        }
                    )

    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("w", newline="") as output:
        writer = csv.DictWriter(output, fieldnames=FIELDS, lineterminator="\n")
        writer.writeheader()
        writer.writerows(observations)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
