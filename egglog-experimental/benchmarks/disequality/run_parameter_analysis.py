#!/usr/bin/env python3
"""Run the artifact parameter analysis with interleaved egglog/native trials."""

from __future__ import annotations

import argparse
import csv
import io
import subprocess
import time
from collections.abc import Sequence
from pathlib import Path

FIELDS = (
    "engine",
    "encoding",
    "load_mode",
    "trial",
    "ratio",
    "artifact_parse_ms",
    "source_render_ms",
    "source_parse_ms",
    "load_or_full_ms",
    "schedule_ms",
    "total_ms",
    "wall_ms",
    "encoding_rows",
    "total_tuples",
    "total_nodes",
    "total_classes",
)


def duration_ms(value: str) -> float:
    """Convert the Rust debug duration printed by the native artifact to ms."""

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


def csv_row(stdout: str) -> dict[str, str]:
    rows = list(csv.DictReader(io.StringIO(stdout)))
    if len(rows) != 1:
        raise ValueError(f"expected one CSV row, got {len(rows)}:\n{stdout}")
    return rows[0]


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--egglog-driver", type=Path, required=True)
    parser.add_argument("--native-ee", type=Path, required=True)
    parser.add_argument("--native-de", type=Path, required=True)
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--ratio", default="0.5")
    parser.add_argument("--trials", type=int, default=5)
    args = parser.parse_args(argv)
    if args.trials < 1:
        parser.error("--trials must be positive")

    endpoints = [
        ("egglog", encoding, args.egglog_driver)
        for encoding in ("ee", "oee", "nee", "de")
    ] + [
        ("native", "ee", args.native_ee),
        ("native", "de", args.native_de),
    ]
    observations: list[dict[str, str | float | int]] = []
    for trial in range(1, args.trials + 1):
        offset = (trial - 1) % len(endpoints)
        for engine, encoding, executable in endpoints[offset:] + endpoints[:offset]:
            command = [str(executable), str(args.input), args.ratio]
            if engine == "egglog":
                command.extend((encoding, "batched-api"))
            started = time.perf_counter()
            completed = subprocess.run(
                command,
                check=True,
                capture_output=True,
                text=True,
            )
            wall_ms = (time.perf_counter() - started) * 1_000.0
            row = csv_row(completed.stdout)
            if engine == "egglog":
                if (row["engine"], row["encoding"], row["load_mode"]) != (
                    "egglog",
                    encoding,
                    "batched-api",
                ):
                    raise ValueError(f"unexpected egglog result: {row}")
                observations.append(
                    {
                        "engine": "egglog",
                        "encoding": encoding,
                        "load_mode": row["load_mode"],
                        "trial": trial,
                        "ratio": row["ratio"],
                        "artifact_parse_ms": row["artifact_parse_ms"],
                        "source_render_ms": row["source_render_ms"],
                        "source_parse_ms": row["source_parse_ms"],
                        "load_or_full_ms": row["load_ms"],
                        "schedule_ms": row["schedule_ms"],
                        "total_ms": row["total_ms"],
                        "wall_ms": f"{wall_ms:.3f}",
                        "encoding_rows": row["encoding_rows"],
                        "total_tuples": row["tuples"],
                        "total_nodes": "",
                        "total_classes": "",
                    }
                )
            else:
                if row["method"] != encoding:
                    raise ValueError(f"unexpected native result: {row}")
                full_ms = duration_ms(row["full_time"])
                observations.append(
                    {
                        "engine": "native",
                        "encoding": encoding,
                        "load_mode": "native-api",
                        "trial": trial,
                        "ratio": row["ratio"],
                        "artifact_parse_ms": "",
                        "source_render_ms": "",
                        "source_parse_ms": "",
                        "load_or_full_ms": f"{full_ms:.3f}",
                        "schedule_ms": "",
                        "total_ms": f"{full_ms:.3f}",
                        "wall_ms": f"{wall_ms:.3f}",
                        "encoding_rows": "",
                        "total_tuples": "",
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
