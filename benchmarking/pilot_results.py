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

from .engines import PROOF_ORACLES
from .pilot_ast import LEGACY_PASS_LABELS
from .reports.analysis import _ratio_estimate, _sample_estimate

PILOT_DATA_VERSION = 1
BUNDLE_NAMES = (
    "extensions-runtime",
    "extensions-speedup",
    "applications-proof-runtime",
    "applications-proof-speedup",
    "extensions-memory",
    "applications-proof-memory",
)


def condition_estimates(condition: dict[str, Any], rounds: int, metric_kind: str = "runtime") -> dict[str, Any]:
    """Qualify one endpoint using actual execution and separate proof evidence."""
    rows = condition["observations"]
    failures = Counter(row["status"] for row in rows if row["status"] != "success")
    validation = condition["validation"]
    issue = condition["exclusion"]["reason"] if condition["exclusion"] else None
    if issue is None and failures:
        issue = ", ".join(f"{count} {status}" for status, count in sorted(failures.items()))
    if issue is None and len(rows) != rounds:
        issue = f"{len(rows)}/{rounds} observations"
    if issue is None and validation is not None and validation["status"] != "passed":
        issue = validation["issue"] or "proof validation pending"
    critical = None if rounds < 2 else float(stats.t.ppf(0.975, rounds - 1))
    estimates = {}
    for field, metric, divisor in (("wall_sec", "runtime", 1), ("max_rss_bytes", "memory", 1048576)):
        values = [
            float(row[field]) / divisor
            for row in rows
            if row["status"] == "success" and row[field] is not None and math.isfinite(row[field]) and row[field] > 0
        ]
        metric_issue = issue or (f"{metric} measurement unavailable" if len(values) != rounds else None)
        estimate = _sample_estimate(values, metric_issue, critical)
        estimates[metric] = {
            "mean": estimate.estimate.point,
            "ci_low": estimate.estimate.ci_low,
            "ci_high": estimate.estimate.ci_high,
            "values": values,
            "issue": metric_issue,
        }
    issue = estimates[metric_kind]["issue"]
    if condition["exclusion"]:
        state = "excluded"
    elif failures or (validation is not None and validation["status"] == "failed"):
        state = "failed"
    elif issue is not None:
        state = "pending"
    else:
        state = "complete"
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
    metric_kind = "memory" if name.endswith("-memory") else "runtime"
    conditions = {row["id"]: condition_estimates(row, rounds, metric_kind) for row in snapshot["conditions"]}
    comparisons = []
    scope = (
        "composition" if name == "composition" else "applications" if name.startswith("applications-") else "extensions"
    )
    for comparison in snapshot["comparisons"]:
        if comparison["scope"] != scope:
            continue
        comparison = dict(comparison)
        for field in ("series", "candidate_label", "reference_label"):
            comparison[field] = re.sub(
                r"\bextlog_(?:dcp|scp|cp|c|d|s)\b",
                lambda match: LEGACY_PASS_LABELS[match.group()],
                comparison[field],
            )
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
        x = b["metrics"][metric_kind]
        y = row["speedup"][metric_kind] if name.endswith("-speedup") else c["metrics"][metric_kind]
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
            [row for row in snapshot["conditions"] if row["id"] in selected_ids],
            sort_keys=True,
            separators=(",", ":"),
        ).encode()
    ).hexdigest()
    return {
        "pilot_data_version": PILOT_DATA_VERSION,
        "figure": name,
        "metric": metric_kind,
        "units": "MiB" if metric_kind == "memory" else "s",
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
    metric_kind = results["metric"]
    numbers: dict[str, Any] = {
        f"{name}/rounds": results["rounds"],
        f"{name}/planned": len(results["comparisons"]),
        f"{name}/complete": len(results["points"]),
    }
    for row in results["coverage"]:
        for field in ("planned", "complete", "pending", "excluded", "failed"):
            numbers[f"{name}/coverage/{row['id']}/{field}"] = row[field]
    table = [
        r"\begin{tabular}{llrr}",
        f"Experiment / workload & Status & Reference ({results['units']}) & Candidate ({results['units']}) " + r"\\",
        r"\hline",
    ]
    for row in results["comparisons"]:
        logical = row["logical_id"].removeprefix("sha256:")
        prefix = f"{name}/{row['experiment']}/{logical}"
        for role in ("reference", "ours"):
            condition = row[role]
            numbers[f"{prefix}/{role}/n"] = condition["sample_n"]
            for field in ("mean", "ci_low", "ci_high"):
                numbers[f"{prefix}/{role}/{metric_kind}/{field.replace('_', '-')}"] = condition["metrics"][metric_kind][
                    field
                ]
        if metric_kind == "runtime":
            for field in ("mean", "ci_low", "ci_high"):
                numbers[f"{prefix}/speedup/{field.replace('_', '-')}"] = row["speedup"][metric_kind][field]
        values = []
        for role in ("reference", "ours"):
            metric = row[role]["metrics"][metric_kind]
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


def _coverage_evidence(conditions: list[dict[str, Any]]) -> dict[str, Any]:
    """Separate observed execution, checked-run counters, and comparison evidence."""
    proof_conditions = [c for c in conditions if c["treatment"] in PROOF_ORACLES]
    summaries = [
        c["validation"]["summary"]
        for c in proof_conditions
        if c["validation"] is not None and c["validation"]["summary"] is not None
    ]
    validation = Counter(
        c["validation"]["status"] if c["validation"] is not None else "unknown" for c in proof_conditions
    )
    return {
        "planned": len(conditions),
        "executed": sum(any(row["status"] == "success" for row in c["observations"]) for c in conditions),
        "proof_configs": len(proof_conditions),
        "validation": validation,
        "summary_n": len(summaries),
        "counters": {
            field: sum(summary[field] for summary in summaries) if summaries else None
            for field in ("check_requests", "extraction_requests", "produced_certificates", "verified_certificates")
        },
        "outputs": Counter(c.get("ordinary_output_parity", "not-compared") for c in conditions),
        "tables": Counter(c.get("table_correspondence", "not-checked") for c in conditions),
    }


def _coverage_detail_row(label: str, conditions: list[dict[str, Any]]) -> str:
    """Format counters with their known-input denominator and distinct validation states."""
    evidence = _coverage_evidence(conditions)
    values = [tex_escape(label)]
    if evidence["proof_configs"]:
        values.append(f"{evidence['summary_n']}/{evidence['planned']}")
        for field in ("check_requests", "extraction_requests", "produced_certificates", "verified_certificates"):
            value = evidence["counters"][field]
            values.append(str(value) if value is not None else "unknown")
        values.append(
            tex_escape(
                "; ".join(
                    f"{status} {evidence['validation'][status]}/{evidence['planned']}"
                    for status in ("passed", "failed", "pending", "unknown", "excluded")
                    if evidence["validation"][status]
                )
            )
        )
    else:
        values.extend(["N/A"] * 6)
    for field in ("outputs", "tables"):
        values.append(
            tex_escape(
                "; ".join(
                    f"{status.replace('-', ' ')} {count}/{evidence['planned']}"
                    for status, count in sorted(evidence[field].items())
                )
            )
        )
    return " & ".join(values) + r" \\"


def coverage_tables(snapshot: dict[str, Any]) -> dict[str, str]:
    """Keep main capability evidence compact and detailed eligibility/counters separate."""
    result = pilot_results(snapshot, "extensions-runtime")
    applications = pilot_results(snapshot, "applications-proof-runtime")
    groups = [
        (item["label"], [row for row in result["comparisons"] if row["experiment"] == item["id"]])
        for item in result["coverage"]
    ]
    groups.append(("Existing programs + proofs", applications["comparisons"]))
    headers = [
        r"\begin{tabular}{lrll}",
        r"Experiment & Inputs & Executed (ref; ours) & Checked (ref; ours) \\",
        r"\hline",
    ]
    timing = [
        r"\begin{tabular}{lrrrrr}",
        r"Experiment & Inputs & Eligible timing pairs & Pending & Failed & Excluded \\",
        r"\hline",
    ]
    detail_rows = []
    for label, comparisons in groups:
        execution, checked = [], []
        for role in ("reference", "ours"):
            conditions = [row[role] for row in comparisons]
            evidence = _coverage_evidence(conditions)
            execution.append(f"{evidence['executed']}/{len(comparisons)}")
            checked.append(
                f"{evidence['validation']['passed']}/{len(comparisons)}" if evidence["proof_configs"] else "N/A"
            )
            detail_rows.append(_coverage_detail_row(f"{label} / {role}", conditions))
        headers.append(
            f"{tex_escape(label)} & {len(comparisons)} & {'; '.join(execution)} & {'; '.join(checked)} " + r"\\"
        )
        counts = Counter(row["state"] for row in comparisons)
        timing.append(
            f"{tex_escape(label)} & {len(comparisons)} & "
            + " & ".join(str(counts[state]) for state in ("complete", "pending", "failed", "excluded"))
            + r" \\"
        )
    headers.append(r"\end{tabular}")
    timing.append(r"\end{tabular}")
    # Source/review statuses are never inferred from execution or proof success.
    unique_inputs = {c["logical_id"]: c for c in snapshot["conditions"]}
    parity = Counter(c.get("ordinary_output_parity", "not-compared") for c in unique_inputs.values())
    tables = Counter(c.get("table_correspondence", "not-checked") for c in unique_inputs.values())
    correspondence = (
        "Ordinary outputs: "
        + "; ".join(f"{status.replace('-', ' ')} ({count} inputs)" for status, count in sorted(parity.items()))
        + ". Table correspondence: "
        + "; ".join(f"{status.replace('-', ' ')} ({count} inputs)" for status, count in sorted(tables.items()))
        + "."
    )
    headers.append(
        r"\par\smallskip{\footnotesize Counts use the fixed planned denominator. "
        r"Executed means at least one successful timed run; checked means a successful "
        r"separate certificate-validation run. N/A denotes a proofs-off configuration. "
        "}"
    )
    counter_header = [
        r"\begin{tabular}{llrrrrlll}",
        r"Experiment / endpoint & Summaries K/N & Checks & Extracts & Produced & Verified & "
        r"Validation inputs & Ordinary outputs & Tables \\",
        r"\hline",
    ]
    counter_note = (
        r"\par\smallskip{\footnotesize Counters describe one separate checked launch per input, "
        r"not certificates from timed objects. K/N gives inputs with emitted summaries; "
        r"unknown summaries are not zero counts. Failed launches may retain completed-prefix counters. "
        r"Table differences are reviewed input metadata, not a fresh correspondence check. "
        + tex_escape(correspondence)
        + "}"
    )
    details = timing + [r"\par\medskip"] + counter_header + detail_rows + [r"\end{tabular}", counter_note]
    composition = [
        r"\begin{tabular}{@{}lcc@{}}",
        r"Case & Additional goals & \shortstack{Checked source\\proof} \\",
        r"\hline",
    ]
    composition_details = [
        r"\begin{tabular}{llrrr}",
        r"Complete Slotted case & Timing pair & Proofs off (s) & Production (s) & Overhead [95\% CI] \\",
        r"\hline",
    ]
    composition_counter_rows = []
    omitted_source_proofs = []
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
        kernel, separator, phase = row["label"].removesuffix("-44rules").rpartition("_")
        publication = {"batax": "BATAX", "mmm": "MMM", "mmm_sum": "ΣMMM", "mttkrp": "MTTKRP", "ttm": "TTM"}
        case_label = f"{publication.get(kernel, kernel)} / {phase}" if separator else row["label"]
        case_tex = tex_escape(case_label).replace("Σ", r"$\Sigma$")
        validation = row["ours"]["validation"]
        summary = validation["summary"] if validation is not None else None
        proof_marker = (
            r"\ding{51}"
            if validation is not None
            and validation["status"] == "passed"
            and summary is not None
            and summary["success"]
            and summary["check_requests"] > 0
            and 0 < summary["produced_certificates"] == summary["verified_certificates"]
            else "Excluded*"
            if validation is not None and validation["status"] == "excluded"
            else r"\textbf{TODO}"
        )
        if validation is not None and validation["status"] == "excluded":
            omitted_source_proofs.append(case_tex)
        # Current snapshots have no paired semantic observations of additional
        # goals; graph size, execution and proof counters cannot supply them.
        composition.append(f"{case_tex} & " + r"\textbf{TODO}" + f" & {proof_marker} " + r"\\")
        composition_details.append(
            f"{tex_escape(row['label'])} & {tex_escape(row['state'])} & {' & '.join(values)} " + r"\\"
        )
        composition_counter_rows.append(_coverage_detail_row(row["label"], [row["ours"]]))
    composition.extend(
        (
            r"\end{tabular}",
            r"\par\smallskip{\footnotesize Additional goals are established by complete matching "
            r"but not restricted matching after the same bounded search. "
            r"\ding{51} denotes a separate successful source-check launch with every produced certificate verified. "
            + (
                "* Source-proof verification omitted for: " + ", ".join(omitted_source_proofs) + ". "
                if omitted_source_proofs
                else ""
            )
            + "}",
        )
    )
    composition_details += [
        r"\end{tabular}",
        r"\par\medskip",
        *counter_header,
        *composition_counter_rows,
        r"\end{tabular}",
        counter_note,
    ]
    sources = [
        r"\begin{tabular}{@{}lp{0.27\linewidth}rrc@{}}",
        r"Project & Acquisition & Replays & \shortstack{Input LOC\\median [range]} & Validated \\",
        r"\hline",
    ]
    provenance_sources = [
        r"\begin{tabular}{@{}lp{0.32\linewidth}rr@{}}",
        r"Project & Acquisition & Replays & \shortstack{Input LOC\\median [range]} \\",
        r"\hline",
    ]
    source_runtime = [
        r"\begin{tabular}{@{}llrlr@{}}",
        r"Project & Configuration & Timed & \shortstack{Runtime (s)\\median [range]} & Checked \\",
        r"\hline",
    ]
    conditions = [condition_estimates(c, snapshot["rounds"]) for c in snapshot["conditions"]]
    checked_inputs = {
        (c["project"], c["logical_id"])
        for c in conditions
        if c["treatment"] == "proof-extraction"
        and c["validation"] is not None
        and c["validation"]["status"] == "passed"
        and c["validation"]["summary"] is not None
        and c["validation"]["summary"]["success"]
        and 0
        < c["validation"]["summary"]["produced_certificates"]
        == c["validation"]["summary"]["verified_certificates"]
    }
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
        description = "unavailable" if not locs else f"{statistics.median(locs):,g} [{min(locs):,}, {max(locs):,}]"
        project_link = r"\href{" + info["source"] + "}{" + tex_escape(info["label"]) + "}"
        # File-level passed-c-and-cp means every source check and extraction was
        # compared with ordinary egglog under both c and cp. Execution and checked
        # certificates alone do not establish this ordinary-output parity.
        validation_marker = (
            r"\ding{51}"
            if inputs
            and all(
                f["ordinary_output_parity"] == "passed-c-and-cp" and (project, f["logical_id"]) in checked_inputs
                for f in inputs
            )
            else r"\textbf{TODO}"
        )
        provenance_row = f"{project_link} & {tex_escape(info['capture'])} & {len(inputs)} & {description}"
        sources.append(provenance_row + f" & {validation_marker} " + r"\\")
        provenance_sources.append(provenance_row + r" \\")
        for treatment in ("off", "proof-extraction"):
            timing_values = times[treatment]
            runtime = (
                f"{statistics.median(timing_values):.4g} [{min(timing_values):.4g}, {max(timing_values):.4g}]"
                if timing_values
                else "unavailable"
            )
            label = "Ordinary egglog" if treatment == "off" else "Proof production"
            checked_coverage = "N/A" if treatment == "off" else f"{validated}/{len(inputs)}"
            source_runtime.append(
                f"{project_link} & {label} & {len(timing_values)}/{len(inputs)} & {runtime} & {checked_coverage} "
                + r"\\"
            )
    sources.append(r"\end{tabular}")
    provenance_sources.append(r"\end{tabular}")
    source_runtime.append(r"\end{tabular}")
    return {
        "experiment-coverage.table.tex": "\n".join(headers) + "\n",
        "composition-coverage.table.tex": "\n".join(composition) + "\n",
        "experiment-coverage-details.table.tex": "\n".join(details) + "\n",
        "composition-coverage-details.table.tex": "\n".join(composition_details) + "\n",
        "corpus-sources.table.tex": "\n".join(sources) + "\n",
        "corpus-provenance.table.tex": "\n".join(provenance_sources) + "\n",
        "corpus-runtime-details.table.tex": "\n".join(source_runtime) + "\n",
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
