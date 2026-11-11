"""Paper numbers and TeX from exactly the observations bound into each figure.

Vega remains the inspectable plotting implementation. These exports reuse the
report analysis estimators; executed-Vega tests guard their numerical parity.
"""

from __future__ import annotations

import math
import re
import statistics
from collections import defaultdict
from pathlib import Path
from typing import Any

from .reports.analysis import _ratio_estimate, _sample_estimate
from .reports.store import GroupedReport

METRICS = (("wall_sec", "runtime", "s", 1), ("max_rss_bytes", "memory", "MiB", 1048576))


def figure_results(
    name: str,
    inputs: list[dict[str, Any]],
    grouped: GroupedReport,
    rounds: int,
    t_critical: float | None,
) -> dict[str, Any]:
    """Estimate selected conditions and the figure's explicitly defined pairs.

    Input row IDs, physical identities, quarantine decisions and strict validation
    come from the same binding used for Vega, without a second cache selection.
    """
    records: dict[int, dict[str, Any]] = {
        row["row_index"]: dict(row) for group in grouped.data["groups"] for row in group["samples"]
    }
    conditions = []
    estimates = {}
    workloads: dict[str, list[dict[str, Any]]] = defaultdict(list)
    semantic_ids: dict[str, str] = {}
    for item in inputs:
        # Labels identify the published case rather than its content-addressed
        # prepared filename; custom inputs use their readable file stem.
        label = item["label"]
        workload = re.sub(r"[^a-z0-9]+", "-", label.lower()).strip("-")
        if Path(label).suffix in (".egg", ".ref", ".in"):
            workload = re.sub(r"[^a-z0-9]+", "-", Path(label).stem.lower()).strip("-")
        if not workload:
            raise ValueError(f"figure workload needs a semantic label: {label!r}")
        previous = semantic_ids.setdefault(workload, item["logical_id"])
        if previous != item["logical_id"]:
            raise ValueError(f"ambiguous figure export workload label: {label}; use distinct case names")
        selected = [records[index] for index in item["selected_row_indices"]]
        condition: dict[str, Any] = {
            **item,
            "workload": workload,
            "sample_n": len(selected),
            "failed_n": sum(row["status"] != "success" for row in selected),
            "observations": [
                {
                    **records[i],
                    **{
                        field: value if value is None or math.isfinite(value) else None
                        for field in ("wall_sec", "max_rss_bytes")
                        if (value := records[i][field]) is not None
                    },
                }
                for i in item["selected_row_indices"]
            ],
            "metrics": {},
        }
        for field, metric, unit, divisor in METRICS:
            values = [
                float(value) / divisor
                for row in selected
                if row["status"] == "success"
                and (value := row[field]) is not None
                and math.isfinite(value)
                and (value >= 0 if metric == "runtime" else value > 0)
            ]
            issue = (
                f"excluded ({item['exclusion']['kind']}): {item['exclusion']['reason']}"
                if item["exclusion"]
                else item.get("validation_issue")
                or (f"{condition['failed_n']} failed observations" if condition["failed_n"] else None)
                or (f"{len(selected)}/{rounds} observations" if len(selected) != rounds else None)
                or ("measurement unavailable" if len(values) != len(selected) else None)
            )
            estimate = _sample_estimate(values, issue, t_critical)
            estimates[(item["logical_id"], item["treatment"], metric)] = estimate
            condition["metrics"][metric] = {
                "unit": unit,
                "valid_n": len(values),
                "values": values,
                "mean": estimate.estimate.point,
                "ci_low": estimate.estimate.ci_low,
                "ci_high": estimate.estimate.ci_high,
                "issue": issue or ("CI undefined for n < 2" if rounds == 1 else None),
            }
        conditions.append(condition)
        workloads[item["logical_id"]].append(condition)
    comparisons = []
    for logical_id, rows in workloads.items():
        by_treatment = {row["treatment"]: row for row in rows}
        treatments = list(by_treatment)
        if name == "disequality-runtime":
            pairs = [("egg-de", t) for t in treatments if t != "egg-de"]
        elif name == "math-runtime":
            pairs = [("egg", "egg-proof-testing"), ("off", "proof-testing")]
        elif name in ("slotted-runtime", "slotted-multipattern-runtime"):
            pairs = [(b, c) for b in treatments if "ref-" in b for c in treatments if "ref-" not in c]
        else:
            pairs = [("off", t) for t in treatments if t != "off"]
        for baseline, candidate in pairs:
            if baseline not in by_treatment or candidate not in by_treatment:
                continue
            comparison = {
                "workload": rows[0]["workload"],
                "label": rows[0]["label"],
                "family": rows[0]["family"],
                "logical_id": logical_id,
                "baseline": baseline,
                "candidate": candidate,
                "metrics": {},
            }
            for _, metric, _, _ in METRICS:
                b = estimates[(logical_id, baseline, metric)]
                c = estimates[(logical_id, candidate, metric)]
                ratio = _ratio_estimate(b, c, t_critical)
                comparison["metrics"][metric] = {
                    "ratio": ratio.estimate.point,
                    "ci_low": ratio.estimate.ci_low,
                    "ci_high": ratio.estimate.ci_high,
                    "issue": ratio.issue,
                    "baseline_n": by_treatment[baseline]["sample_n"],
                    "candidate_n": by_treatment[candidate]["sample_n"],
                }
            if name.startswith("corpus-"):
                # Cohort membership uses baseline wall time for both metrics,
                # independently of missing RSS. Exclusions remain in coverage.
                baseline_row = by_treatment[baseline]
                wall = [
                    r["wall_sec"]
                    for r in baseline_row["observations"]
                    if r["status"] == "success"
                    and r["wall_sec"] is not None
                    and math.isfinite(r["wall_sec"])
                    and r["wall_sec"] >= 0
                ]
                resolved = len(wall) == rounds and baseline_row["sample_n"] == rounds
                comparison["cohort"] = (
                    "selected" if resolved and sum(wall) / rounds >= 0.2 else "too-fast" if resolved else "unresolved"
                )
                comparison["excluded"] = bool(baseline_row["exclusion"] or by_treatment[candidate]["exclusion"])
                comparison["failed"] = bool(
                    by_treatment[candidate]["failed_n"] or by_treatment[candidate].get("validation_issue")
                )
            comparisons.append(comparison)
    coverage = {}
    if name.startswith("corpus-"):
        cohort = [row for row in comparisons if row["cohort"] == "selected"]
        for _, metric, _, _ in METRICS:
            ratios = sorted(
                row["metrics"][metric]["ratio"] for row in cohort if row["metrics"][metric]["ratio"] is not None
            )
            coverage[metric] = {
                "saved_n": len(comparisons),
                "cohort_n": len(cohort),
                "measured_n": len(ratios),
                "too_fast_n": sum(row["cohort"] == "too-fast" for row in comparisons),
                "unresolved_n": sum(row["cohort"] == "unresolved" for row in comparisons),
                "failed_n": sum(row["failed"] for row in cohort),
                "excluded_n": sum(row["excluded"] for row in comparisons),
                "missing_n": sum(
                    row["metrics"][metric]["ratio"] is None and not row["failed"] and not row["excluded"]
                    for row in cohort
                ),
                "q50": next((value for i, value in enumerate(ratios, 1) if i / len(cohort) >= 0.5), None),
                "q95": next((value for i, value in enumerate(ratios, 1) if i / len(cohort) >= 0.95), None),
                "maximum": max(ratios, default=None),
            }
    return {
        "figure": name,
        "rounds": rounds,
        "confidence": 0.95,
        "statistics": (
            "Arithmetic means; Student-t mean intervals; independent Fieller ratio intervals. "
            "CDF thresholds use the selected cohort denominator, without a population confidence band."
        ),
        "conditions": conditions,
        "comparisons": comparisons,
        "coverage": coverage,
    }


def corpus_view_domains(result: dict[str, Any]) -> dict[str, dict[str, float]]:
    """Choose readable detail windows without adding a marginal-tail overview.

    This is layout policy over exported per-file ratios, never a filter on the
    CDF population. Vega retains the statistical transforms and empirical ranks.
    """
    domains = {}
    for metric, label in (("runtime", "Runtime"), ("memory", "Peak RSS")):
        ratios = [
            row["metrics"][metric]["ratio"]
            for row in result["comparisons"]
            if row["cohort"] == "selected" and row["metrics"][metric]["ratio"] is not None
        ]
        maximum = max([1, *ratios])
        full_step = 10 ** (math.floor(math.log10(maximum)) - 1)
        full = max(1.1, math.ceil(maximum / full_step) * full_step)
        target = max(1.1, min(full, 2 * (statistics.median(ratios) if ratios else 1)))
        zoom_step = 10 ** (math.floor(math.log10(target)) - 1)
        zoom = min(full, math.ceil(target / zoom_step) * zoom_step)
        domains[label] = {
            "min": math.floor(min(1, min(ratios)) * 10) / 10 if ratios else 0,
            "zoom": full if full <= 1.2 * zoom else zoom,
            "full": full,
        }
    return domains


def latex_results(result: dict[str, Any]) -> tuple[str, str]:
    """Produce stable numeric macros and a standalone, escaped LaTeX table."""
    escapes = {
        "\\": r"\textbackslash{}",
        "&": r"\&",
        "%": r"\%",
        "$": r"\$",
        "#": r"\#",
        "_": r"\_",
        "{": r"\{",
        "}": r"\}",
        "~": r"\textasciitilde{}",
        "^": r"\textasciicircum{}",
        "Σ": r"$\Sigma$",
    }
    header = (
        f"%% GENERATED FILE: ./bench.py figures {result['figure']}\n"
        f"%% Requested observations per condition: {result['rounds']}; 95% intervals.\n"
        f"%% Provenance and availability issues: {result['figure']}.results.json\n"
    )
    figure_key = re.sub(r"[^a-z0-9]+", "-", result["figure"].lower()).strip("-")
    macros = [
        r"\providecommand{\EgglogFigureNumber}[1]{\ifcsname egglogfigure@#1\endcsname"
        r"\csname egglogfigure@#1\endcsname\else\textnormal{unavailable}\fi}"
    ]
    display_treatments = {"off": "extlog", "egg-de": "Reference"} if result["figure"] == "disequality-runtime" else {}
    slotted = result["figure"] in ("slotted-runtime", "slotted-multipattern-runtime")
    table = [
        r"\begin{tabular}{lrr}" if slotted else r"\begin{tabular}{llrr}",
        r"Kernel/phase & Reference time (s) [95\% CI] & extlog time (s) [95\% CI] \\"
        if slotted
        else r"Workload & Comparison & Runtime ratio [95\% CI] & Peak RSS ratio [95\% CI] \\",
        r"\hline",
    ]
    table_rows = []
    conditions = {(row["logical_id"], row["treatment"]): row for row in result["conditions"]}
    numbers: dict[str, Any] = {
        f"{figure_key}/rounds": result["rounds"],
        f"{figure_key}/workload-count": len({row["logical_id"] for row in result["conditions"]}),
    }
    for row in result["conditions"]:
        prefix = f"{figure_key}/{row['workload']}/{row['treatment']}"
        numbers[f"{prefix}/n"] = row["sample_n"]
        for metric, values in row["metrics"].items():
            for field in ("mean", "ci_low", "ci_high", "valid_n"):
                numbers[f"{prefix}/{metric}/{field.replace('_', '-')}"] = values[field]
    for row in result["comparisons"]:
        cells = []
        for metric, values in row["metrics"].items():
            prefix = f"{figure_key}/{row['workload']}/{row['candidate']}-over-{row['baseline']}/{metric}"
            for field in ("ratio", "ci_low", "ci_high", "baseline_n", "candidate_n"):
                numbers[f"{prefix}/{field.replace('_', '-')}"] = values[field]
        estimates = (
            [
                conditions[(row["logical_id"], row[endpoint])]["metrics"]["runtime"]
                for endpoint in ("baseline", "candidate")
            ]
            if slotted
            else row["metrics"].values()
        )
        for values in estimates:
            point = values["mean"] if slotted else values["ratio"]
            if point is None:
                cell = "unavailable"
            elif values["ci_low"] is None:
                cell = f"{point:.3g} [CI unavailable]"
            else:
                cell = f"{point:.3g} [{values['ci_low']:.3g}, {values['ci_high']:.3g}]"
            cells.append("".join(escapes.get(ch, ch) for ch in cell))
        label = Path(row["label"]).stem if Path(row["label"]).suffix in (".egg", ".ref", ".in") else row["label"]
        if slotted:
            label = label.removesuffix("-44rules")
            for kernel, publication in (
                ("batax", "BATAX"),
                ("mmm_sum", "ΣMMM"),
                ("mmm", "MMM"),
                ("mttkrp", "MTTKRP"),
                ("ttm", "TTM"),
            ):
                if label.startswith(kernel + "_"):
                    label = publication + label[len(kernel) :]
                    break
            label = label.replace("_1st", " / 1st").replace("_2nd", " / 2nd")
        pair = " / ".join(
            display_treatments.get(row[endpoint], row[endpoint]) for endpoint in ("candidate", "baseline")
        )
        table_rows.append(
            (
                row["metrics"]["runtime"]["ratio"],
                " & ".join(
                    [
                        *(
                            "".join(escapes.get(ch, ch) for ch in text)
                            for text in ((label,) if slotted else (label, pair))
                        ),
                        *cells,
                    ]
                )
                + r" \\",
            )
        )
    if slotted:
        table_rows.sort(key=lambda row: row[0] if row[0] is not None else math.inf)
        memory_ratios = [
            value
            for row in result["comparisons"]
            if (value := row["metrics"]["memory"]["ratio"]) is not None and math.isfinite(value)
        ]
        numbers[f"{figure_key}/memory/ratio-min"] = min(memory_ratios, default=None)
        numbers[f"{figure_key}/memory/ratio-max"] = max(memory_ratios, default=None)
    table.extend(line for _, line in table_rows)
    speedup_pairs: list[tuple[str, str, str, str]] = []
    workloads = {row["logical_id"]: row["workload"] for row in result["conditions"]}
    if result["figure"] in ("disequality-runtime", "math-runtime"):
        reference, candidate = (
            ("egg-de", "off") if result["figure"] == "disequality-runtime" else ("egg-proof-testing", "proof-testing")
        )
        speedup_pairs = [(logical_id, workload, reference, candidate) for logical_id, workload in workloads.items()]
    elif result["figure"] == "slotted-multipattern-runtime":
        speedup_pairs = [
            (row["logical_id"], row["workload"], row["baseline"], row["candidate"]) for row in result["comparisons"]
        ]
    faster_speedups = []
    for logical_id, workload, reference, candidate in speedup_pairs:
        reference_condition = conditions.get((logical_id, reference))
        candidate_condition = conditions.get((logical_id, candidate))
        speedup = None
        if (
            reference_condition is not None
            and candidate_condition is not None
            and all(
                not endpoint["exclusion"]
                and not endpoint.get("validation_issue")
                and not endpoint["failed_n"]
                and endpoint["sample_n"] == endpoint["metrics"]["runtime"]["valid_n"] == result["rounds"]
                for endpoint in (reference_condition, candidate_condition)
            )
        ):
            numerator = reference_condition["metrics"]["runtime"]["mean"]
            denominator = candidate_condition["metrics"]["runtime"]["mean"]
            if (
                numerator is not None
                and denominator is not None
                and math.isfinite(numerator)
                and math.isfinite(denominator)
                and numerator >= 0
                and denominator > 0
            ):
                # Divide full-precision absolute means, including both checked
                # engines for Math; printed overhead ratios are not inputs.
                speedup = numerator / denominator
                if not math.isfinite(speedup):
                    speedup = None
        if result["figure"] == "slotted-multipattern-runtime":
            if speedup is not None and speedup > 1:
                faster_speedups.append(speedup)
        else:
            numbers[f"{figure_key}/{workload}/{reference}-over-{candidate}/runtime/speedup"] = speedup
    if result["figure"] == "slotted-multipattern-runtime":
        numbers[f"{figure_key}/runtime/speedup-max"] = max(faster_speedups, default=None)
    for metric, values in result["coverage"].items():
        for field, value in values.items():
            numbers[f"{figure_key}/coverage/{metric}/{field.replace('_', '-')}"] = value
        if metric == "runtime":
            numbers[f"{figure_key}/coverage/runtime/project-n"] = len(
                {row["family"] for row in result["comparisons"] if row["cohort"] == "selected"}
            )
    for key, value in numbers.items():
        rendered = (
            r"\textnormal{unavailable}"
            if value is None
            else str(value)
            if isinstance(value, int)
            else format(value, ".3g")
        )
        macros.append(r"\expandafter\def\csname egglogfigure@" + key + r"\endcsname{" + rendered + "}")
    table.append(r"\end{tabular}")
    return header + "\n".join(macros) + "\n", header + "\n".join(table) + "\n"
