"""Estimate the claims-aligned pilot from one portable observation snapshot.

The same selected observations drive both scatter views, coverage, and paper
numbers. Incomplete or unvalidated conditions remain explicit without receiving
finite estimates. No calculation here selects a baseline-runtime cohort.
"""

from __future__ import annotations

import hashlib
import json
import math
import re
import statistics
from collections import Counter
from typing import Any

from scipy import stats

from .reports.analysis import _ratio_estimate, _sample_estimate

PILOT_DATA_VERSION = 1
BUNDLE_NAMES = (
    "extensions-runtime",
    "extensions-speedup",
    "applications-proof-runtime",
    "applications-proof-speedup",
)


def condition_estimates(condition: dict[str, Any], rounds: int) -> dict[str, Any]:
    """Qualify one endpoint using actual execution and separate proof evidence."""
    rows = condition["observations"]
    failures = Counter(row["status"] for row in rows if row["status"] != "success")
    validation = condition["validation"]
    issue = condition["exclusion"]["reason"] if condition["exclusion"] else None
    if issue is None and failures:
        issue = ", ".join(f"{count} {status}" for status, count in sorted(failures.items()))
    if issue is None and len(rows) != rounds:
        issue = f"{len(rows)}/{rounds} observations"
    if issue is None and any(row["wall_sec"] is None or not math.isfinite(row["wall_sec"]) for row in rows):
        issue = "runtime measurement unavailable"
    if issue is None and validation is not None and validation["status"] != "passed":
        issue = validation["issue"] or "proof validation pending"
    if condition["exclusion"]:
        state = "excluded"
    elif failures or (validation is not None and validation["status"] == "failed"):
        state = "failed"
    elif issue is not None:
        state = "pending"
    else:
        state = "complete"
    critical = None if rounds < 2 else float(stats.t.ppf(0.975, rounds - 1))
    estimates = {}
    for field, metric, divisor in (("wall_sec", "runtime", 1), ("max_rss_bytes", "memory", 1048576)):
        values = [
            float(row[field]) / divisor
            for row in rows
            if row["status"] == "success" and row[field] is not None and math.isfinite(row[field])
        ]
        metric_issue = issue or ("measurement unavailable" if len(values) != rounds else None)
        estimate = _sample_estimate(values, metric_issue, critical)
        estimates[metric] = {
            "mean": estimate.estimate.point,
            "ci_low": estimate.estimate.ci_low,
            "ci_high": estimate.estimate.ci_high,
            "values": values,
            "issue": metric_issue,
        }
    return {
        **condition,
        "state": state,
        "issue": issue,
        "sample_n": len(rows),
        "successful_n": sum(row["status"] == "success" for row in rows),
        "failed_n": sum(failures.values()),
        "metrics": estimates,
    }


def pilot_results(snapshot: dict[str, Any], name: str) -> dict[str, Any]:
    """Derive one view without changing the shared observation selection."""
    if name not in (*BUNDLE_NAMES, "composition") or snapshot["pilot_data_version"] != PILOT_DATA_VERSION:
        raise ValueError("unsupported pilot figure bundle")
    rounds = snapshot["rounds"]
    critical = None if rounds < 2 else float(stats.t.ppf(0.975, rounds - 1))
    conditions = {row["id"]: condition_estimates(row, rounds) for row in snapshot["conditions"]}
    comparisons = []
    scope = (
        "composition" if name == "composition" else "applications" if name.startswith("applications-") else "extensions"
    )
    for comparison in snapshot["comparisons"]:
        if comparison["scope"] != scope:
            continue
        baseline = conditions[comparison["baseline"]]
        candidate = conditions[comparison["candidate"]]
        if scope == "applications" and (baseline["treatment"] != "off" or candidate["treatment"] != "proof-extraction"):
            continue
        issue = "; ".join(dict.fromkeys(x for x in (baseline["issue"], candidate["issue"]) if x)) or None
        ratios = {}
        overheads = {}
        for metric in ("runtime", "memory"):
            b = _sample_estimate(baseline["metrics"][metric]["values"], baseline["metrics"][metric]["issue"], critical)
            c = _sample_estimate(
                candidate["metrics"][metric]["values"], candidate["metrics"][metric]["issue"], critical
            )
            # Fieller takes denominator first: speedup is reference / candidate.
            ratio = _ratio_estimate(c, b, critical)
            ratios[metric] = {
                "mean": ratio.estimate.point,
                "ci_low": ratio.estimate.ci_low,
                "ci_high": ratio.estimate.ci_high,
                "issue": ratio.issue,
            }
            overhead = _ratio_estimate(b, c, critical)
            overheads[metric] = {
                "mean": overhead.estimate.point,
                "ci_low": overhead.estimate.ci_low,
                "ci_high": overhead.estimate.ci_high,
                "issue": overhead.issue,
            }
        states = {baseline["state"], candidate["state"]}
        state = (
            "failed"
            if "failed" in states
            else "excluded"
            if "excluded" in states
            else "pending"
            if issue
            else "complete"
        )
        comparisons.append(
            {
                **comparison,
                "state": state,
                "issue": issue,
                "reference": baseline,
                "ours": candidate,
                "speedup": ratios,
                "overhead": overheads,
            }
        )
    points = []
    for row in comparisons:
        if row["state"] != "complete":
            continue
        b, c = row["reference"], row["ours"]
        x = b["metrics"]["runtime"]
        y = row["speedup"]["runtime"] if name.endswith("-speedup") else c["metrics"]["runtime"]
        if x["mean"] is None or y["mean"] is None or min(x["mean"], y["mean"]) <= 0:
            continue
        points.append(
            {
                "experiment": row["experiment"],
                "series": row["series"],
                "project": row["project"],
                "treatment": c["treatment"],
                "configuration": row["candidate_label"],
                "workload": row["label"],
                "logical_id": row["logical_id"],
                "x": x["mean"],
                "x_low": x["ci_low"],
                "x_high": x["ci_high"],
                "y": y["mean"],
                "y_low": y["ci_low"],
                "y_high": y["ci_high"],
                "interval_issue": "; ".join(
                    ([y["issue"]] if y["issue"] else [])
                    + [
                        f"{axis} CI crosses zero; clipped on log axis"
                        for axis, metric in (("x", x), ("y", y))
                        if metric["ci_low"] is not None and metric["ci_low"] <= 0
                    ]
                )
                or None,
                "reference_threads": b["threads"],
                "candidate_threads": c["threads"],
                "reference_n": b["sample_n"],
                "candidate_n": c["sample_n"],
            }
        )
    coverage = []
    for experiment in (
        snapshot["projects"].values()
        if scope == "applications"
        else [item for item in snapshot["experiments"] if item.get("scope", "extensions") == scope]
    ):
        identifier = experiment["id"]
        rows = [row for row in comparisons if row["project" if scope == "applications" else "experiment"] == identifier]
        counts = Counter(row["state"] for row in rows)
        coverage.append(
            {
                "id": identifier,
                "label": experiment["label"],
                "planned": len(rows),
                **{state: counts[state] for state in ("complete", "pending", "excluded", "failed")},
            }
        )
    selected_ids = {row[side] for row in comparisons for side in ("baseline", "candidate")}
    selected = [conditions[key] for key in sorted(selected_ids)]
    identity = hashlib.sha256(
        json.dumps(
            [{key: value for key, value in row.items() if key != "metrics"} for row in selected],
            sort_keys=True,
            separators=(",", ":"),
        ).encode()
    ).hexdigest()
    return {
        "pilot_data_version": PILOT_DATA_VERSION,
        "figure": name,
        "stage": "pilot",
        "rounds": rounds,
        "confidence": 0.95,
        "selection_sha256": identity,
        "statistics": "Arithmetic means with marginal Student-t 95% CIs; independent-sample Fieller-style speedup CIs.",
        "conditions": selected,
        "comparisons": comparisons,
        "points": points,
        "coverage": coverage,
        "provenance": snapshot["provenance"],
        "pilot_snapshot": snapshot,
    }


def pilot_tex(results: dict[str, Any]) -> tuple[str, str]:
    """Export full-precision per-workload numbers and a readable comparison table."""
    name = results["figure"]
    numbers: dict[str, Any] = {
        f"{name}/rounds": results["rounds"],
        f"{name}/planned": len(results["comparisons"]),
        f"{name}/complete": len(results["points"]),
    }
    for row in results["coverage"]:
        for field in ("planned", "complete", "pending", "excluded", "failed"):
            numbers[f"{name}/coverage/{row['id']}/{field}"] = row[field]
    table = [r"\begin{tabular}{llrr}", r"Experiment / workload & Status & Reference (s) & extlog (s) \\", r"\hline"]
    for row in results["comparisons"]:
        logical = row["logical_id"].removeprefix("sha256:")
        prefix = f"{name}/{row['experiment']}/{logical}"
        for role in ("reference", "ours"):
            condition = row[role]
            numbers[f"{prefix}/{role}/n"] = condition["sample_n"]
            for field in ("mean", "ci_low", "ci_high"):
                numbers[f"{prefix}/{role}/runtime/{field.replace('_', '-')}"] = condition["metrics"]["runtime"][field]
        for field in ("mean", "ci_low", "ci_high"):
            numbers[f"{prefix}/speedup/{field.replace('_', '-')}"] = row["speedup"]["runtime"][field]
        values = []
        for role in ("reference", "ours"):
            metric = row[role]["metrics"]["runtime"]
            values.append(
                "unavailable"
                if metric["mean"] is None
                else f"{metric['mean']:.4g}"
                + (f" [{metric['ci_low']:.4g}, {metric['ci_high']:.4g}]" if metric["ci_low"] is not None else "")
            )
        label = tex_escape(f"{row['series']} / {row['label']}")
        table.append(f"{label} & {tex_escape(row['state'])} & {values[0]} & {values[1]} " + r"\\")
    table.append(r"\end{tabular}")
    macros = [
        f"%% Pilot: {results['rounds']} requested observations per condition; no runtime cutoff.\n",
        r"\providecommand{\EgglogFigureNumber}[1]{\ifcsname egglogfigure@#1\endcsname"
        r"\csname egglogfigure@#1\endcsname\else\textnormal{unavailable}\fi}",
    ]
    for key, value in sorted(numbers.items()):
        content = (
            r"\textnormal{unavailable}"
            if value is None
            else f"{value:.12g}"
            if isinstance(value, float)
            else str(value)
        )
        macros.append(r"\expandafter\def\csname egglogfigure@" + key + r"\endcsname{" + content + "}")
    return "\n".join(macros) + "\n", "\n".join(table) + "\n"


def coverage_tables(snapshot: dict[str, Any]) -> dict[str, str]:
    """Summarize planned inputs and executed proof evidence, retaining unknowns."""
    result = pilot_results(snapshot, "extensions-runtime")
    headers = [
        r"\begin{tabular}{lrrrrrr}",
        r"Experiment & Planned & Complete & Pending & Failed & Excluded & Checked proofs \\",
        r"\hline",
    ]
    composition = [
        r"\begin{tabular}{llrrrr}",
        r"Complete Slotted case & Status & Proofs off (s) & Production (s) & Overhead [95\% CI] & Checked proofs \\",
        r"\hline",
    ]
    for row in result["coverage"]:
        comparisons = [c for c in result["comparisons"] if c["experiment"] == row["id"]]
        candidates = [c["ours"] for c in comparisons]
        produced = [
            c["validation"]["summary"]
            for c in candidates
            if c["validation"] is not None and c["validation"]["summary"] is not None
        ]
        verified = sum(p["verified_certificates"] for p in produced) if produced else None
        verified_text = "unavailable" if verified is None else str(verified)
        headers.append(
            f"{tex_escape(row['label'])} & {row['planned']} & {row['complete']} & {row['pending']} "
            f"& {row['failed']} & {row['excluded']} & {verified_text} " + r"\\"
        )
    for row in pilot_results(snapshot, "composition")["comparisons"]:
        values = []
        for metric in (
            row["reference"]["metrics"]["runtime"],
            row["ours"]["metrics"]["runtime"],
            row["overhead"]["runtime"],
        ):
            values.append(
                "unavailable"
                if metric["mean"] is None
                else f"{metric['mean']:.4g}"
                + (f" [{metric['ci_low']:.4g}, {metric['ci_high']:.4g}]" if metric["ci_low"] is not None else "")
            )
        evidence = row["ours"]["validation"]
        count = (
            evidence["summary"]["verified_certificates"]
            if evidence is not None and evidence["summary"] is not None
            else "unavailable"
        )
        composition.append(
            f"{tex_escape(row['label'])} & {tex_escape(row['state'])} & {' & '.join(values)} & {count} " + r"\\"
        )
    headers.append(r"\end{tabular}")
    composition.append(r"\end{tabular}")
    sources = [
        r"\begin{tabular}{llrlrrr}",
        r"Project & Acquisition & Replays & Input LOC median [range] & "
        r"Baseline (s) & Proof production (s) & Validated \\",
        r"\hline",
    ]
    conditions = [condition_estimates(c, snapshot["rounds"]) for c in snapshot["conditions"]]
    for project, info in snapshot["projects"].items():
        inputs = [f for f in snapshot["files"] if f["project"] == project]
        locs = [f["input_loc"] for f in inputs]
        times: dict[str, list[float]] = {}
        for treatment in ("off", "proof-extraction"):
            times[treatment] = [
                c["metrics"]["runtime"]["mean"]
                for c in conditions
                if c["project"] == project
                and c["treatment"] == treatment
                and c["metrics"]["runtime"]["mean"] is not None
            ]
        validated = sum(
            c["validation"] is not None and c["validation"]["status"] == "passed"
            for c in conditions
            if c["project"] == project and c["treatment"] == "proof-extraction"
        )
        description = "unavailable" if not locs else f"{statistics.median(locs):g} [{min(locs)}, {max(locs)}]"
        runtimes = []
        for treatment in ("off", "proof-extraction"):
            timing_values = times[treatment]
            runtimes.append(
                f"{statistics.median(timing_values):.4g} [{min(timing_values):.4g}, {max(timing_values):.4g}]; "
                f"{len(timing_values)}/{len(inputs)}"
                if timing_values
                else "unavailable"
            )
        project_link = r"\href{" + info["source"] + "}{" + tex_escape(info["label"]) + "}"
        sources.append(
            f"{project_link} & {tex_escape(info['capture'])} & {len(inputs)} & {description} "
            f"& {' & '.join(runtimes)} & {validated}/{len(inputs)} " + r"\\"
        )
    sources.append(r"\end{tabular}")
    return {
        "experiment-coverage.table.tex": "\n".join(headers) + "\n",
        "composition-coverage.table.tex": "\n".join(composition) + "\n",
        "corpus-sources.table.tex": "\n".join(sources) + "\n",
    }


def tex_escape(text: str) -> str:
    """Protect arbitrary benchmark labels in generated TeX table cells."""
    replacements = {
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
    }
    return re.sub(r"[\\&%$#_{}~^]", lambda match: replacements[match.group()], text)
