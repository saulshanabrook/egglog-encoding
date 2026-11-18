"""Named paper headlines from the same snapshot as the evaluation figures."""

from __future__ import annotations

import math
import statistics
from collections import Counter
from typing import Any

from .pilot_results import pilot_results

# Separate comparisons: never pool the four suites or include the corpus control.
EXTENSION_COMPARISONS = {
    "math-proofs": "MathProofs",
    "slotted": "SlottedRestricted",
    "slotted-complete": "SlottedComplete",
    "disequality": "Disequality",
}


def headline_results(snapshot: dict[str, Any]) -> dict[str, Any]:
    """Summarize matched workload means; retain exclusions and pending evidence."""
    runtime = pilot_results(snapshot, "extensions-runtime")
    comparisons: dict[str, Any] = {}
    numbers: dict[str, int | float | None] = {}
    for experiment, macro in EXTENSION_COMPARISONS.items():
        rows = [row for row in runtime["comparisons"] if row["experiment"] == experiment]
        counts = Counter(row["state"] for row in rows)
        matched = [row for row in rows if row["state"] == "complete"]
        # Explicit exclusions may narrow a suite. Missing/failed measurements
        # must not silently turn it into a successful-only headline.
        available = bool(matched) and not (counts["pending"] or counts["failed"])
        reference_mean = ours_mean = ratio = geometric = None
        if available:
            reference = [row["reference"]["metrics"]["runtime"]["mean"] for row in matched]
            ours = [row["ours"]["metrics"]["runtime"]["mean"] for row in matched]
            reference_mean, ours_mean = statistics.fmean(reference), statistics.fmean(ours)
            ratio = reference_mean / ours_mean
            geometric = math.exp(
                statistics.fmean(math.log(b) - math.log(o) for b, o in zip(reference, ours, strict=True))
            )
        comparisons[experiment] = {
            "coverage": {"planned": len(rows), **{s: counts[s] for s in ("complete", "excluded", "pending", "failed")}},
            "reference_mean_runtime_sec": reference_mean,
            "ours_mean_runtime_sec": ours_mean,
            "speedup_ratio_of_mean_runtimes": ratio,
            "speedup_geometric_mean": geometric,
            "workloads": [
                {
                    "logical_id": row["logical_id"],
                    "label": row["label"],
                    "state": row["state"],
                    "issue": row["issue"],
                    "reference_condition": row["baseline"],
                    "ours_condition": row["candidate"],
                    "reference_mean_runtime_sec": row["reference"]["metrics"]["runtime"]["mean"],
                    "ours_mean_runtime_sec": row["ours"]["metrics"]["runtime"]["mean"],
                }
                for row in rows
            ],
        }
        numbers[f"Eval{macro}SpeedupRatioOfMeanRuntimes"] = ratio
        numbers[f"Eval{macro}SpeedupGeometricMean"] = geometric
        numbers[f"Eval{macro}MatchedWorkloadCount"] = len(matched)

    for field, macro in (
        ("speedup_ratio_of_mean_runtimes", "RatioOfMeanRuntimes"),
        ("speedup_geometric_mean", "GeometricMean"),
    ):
        values = [row[field] for row in comparisons.values()]
        complete = all(value is not None for value in values)
        numbers[f"EvalExtensionSpeedup{macro}Min"] = min(values) if complete else None
        numbers[f"EvalExtensionSpeedup{macro}Max"] = max(values) if complete else None

    inputs = {(f["project"], f["logical_id"]) for f in snapshot["files"] if f["project"] in snapshot["projects"]}
    checked = set()
    for condition in snapshot["conditions"]:
        identity = (condition["project"], condition["logical_id"])
        if identity not in inputs or condition["treatment"] != "proof-extraction":
            continue
        validation = condition["validation"]
        summary = validation["summary"] if validation is not None else None
        if (
            validation is not None
            and validation["status"] == "passed"
            and summary is not None
            and summary["success"]
            and 0 < summary["produced_certificates"] == summary["verified_certificates"]
        ):
            checked.add(identity)
    corpus: dict[str, Any] = {
        "program_count": len(inputs),
        "project_count": len({project for project, _ in inputs}),
        "checked_program_count": len(checked),
        "checked_project_count": len({project for project, _ in checked}),
        "inputs": [
            {"project": project, "logical_id": logical_id, "checked": (project, logical_id) in checked}
            for project, logical_id in sorted(inputs)
        ],
    }
    for field, macro in (
        ("program_count", "ProgramCount"),
        ("project_count", "ProjectCount"),
        ("checked_program_count", "CheckedProgramCount"),
        ("checked_project_count", "CheckedProjectCount"),
    ):
        # A zero count remains visible in JSON; a pending paper claim gets a TODO.
        numbers[f"EvalCorpus{macro}"] = corpus[field] or None
    return {
        "selection_sha256": runtime["selection_sha256"],
        "provenance": snapshot["provenance"],
        "rounds": snapshot["rounds"],
        "statistics": {
            "workload_runtime": "Arithmetic mean of the requested repeated runs, in seconds.",
            "speedup_ratio_of_mean_runtimes": "mean(reference_i) / mean(ours_i) = sum(reference_i) / sum(ours_i)",
            "speedup_geometric_mean": "exp(mean(log(reference_i) - log(ours_i)))",
            "range": "Min/max across the four separate extension comparisons, not a pooled suite speedup.",
            "coverage": "Both aggregations use identical matched workloads; exclusions are explicit. "
            "Any pending/failed timing suppresses its comparison and the cross-comparison range.",
            "checked": "Distinct captured programs with a passed separate validation replay and nonzero "
            "fully verified certificates; counts do not imply user adoption or ordinary-output parity.",
        },
        "comparisons": comparisons,
        "corpus": corpus,
        "numbers": numbers,
    }


def headline_tex(results: dict[str, Any]) -> str:
    """Use explicit aggregation names; never substitute a number for missing data."""
    lines = [
        "% Generated by ./bench.py figures --pilot; see headline.results.json for full precision and coverage.",
        "% Speedups are reference/ours (>1 is faster); per-workload times are means over repeated runs.",
        "% RatioOfMeanRuntimes = sum(reference times)/sum(our times) on the same matched inputs.",
        "% GeometricMean = exp(mean(log(reference time)-log(our time))) on those inputs.",
    ]
    for name, value in results["numbers"].items():
        content = (
            r"\todo{" + name.removeprefix("Eval") + "}"
            if value is None
            else f"{value:.3g}"
            if isinstance(value, float)
            else str(value)
        )
        lines.append("\\providecommand{\\" + name + "}{" + content + "}")
    return "\n".join(lines) + "\n"
