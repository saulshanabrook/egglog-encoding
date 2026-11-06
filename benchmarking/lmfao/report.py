"""Execution comparison and separate preparation costs for the LMFAO case study."""

from __future__ import annotations

from typing import Any

from . import model


def preparation_costs(plans: dict[str, Any], builds: dict[str, Any], aliases: dict[str, str]) -> dict[str, Any]:
    result = {}
    for label in ["original", *plans]:
        executed = aliases.get(label, label)
        generation = builds[label]["generation_seconds"]
        compilation = builds[executed]["compilation_seconds"]
        result[label] = {
            "optimization_and_generation_seconds": generation,
            "compilation_seconds": compilation,
            "one_time_phase_sum_seconds": generation + compilation,
            "execution_label": executed,
        }
    return result


def comparison_markdown(report: dict[str, Any]) -> str:
    lines = [
        "| Variant / engine | Allowed roots | Shared producers | Computation median (s) | Runs |",
        "|---|---|---|---:|---:|",
    ]
    costs = [
        "| Variant / engine | Optimization + generation (s) | C++ compilation (s) |",
        "|---|---:|---:|",
    ]
    configurations = {
        "single-root": ("Sales only", "Enabled"),
        "roots": ("All six", "Disabled"),
        "shared": ("All six", "Enabled"),
    }
    controls = report.get("binding_controls", {})
    quality = ["| Variant / engine | Views | Aggregate columns | Structural cost |", "|---|---:|---:|---:|"]
    for label in ["original", *report["optimizer"], *controls]:
        if label == "original":
            name, roots, sharing = "Original LMFAO", "Original policy", "Original merging"
        elif label in controls:
            name, roots, sharing = f"shared / ordinary {controls[label]}", "All six", "Enabled"
        else:
            variant, _, engine = label.partition("-slotted")
            name = f"{variant} / {'native multipattern' if engine else 'egglog'}"
            roots, sharing = configurations[variant]
        if summary := report.get("plan_summaries", {}).get(label):
            quality.append(
                f"| {name} | {summary['views']} | {summary['aggregate_columns']} | "
                f"{summary.get('structural_cost', '—')} |"
            )
        if label not in report["accounted_pipeline"]:
            lines.append(f"| {name} | {roots} | {sharing} | unavailable | — |")
            costs.append(f"| {name} | — | — |")
            continue
        preparation = report["accounted_pipeline"][label]
        timing = report["execution"][preparation["execution_label"]]["computation_seconds"]
        lines.append(f"| {name} | {roots} | {sharing} | {timing['median_seconds']:.4f} | {timing['samples']} |")
        values = [preparation[key] for key in ("optimization_and_generation_seconds", "compilation_seconds")]
        costs.append(f"| {name} | " + " | ".join(f"{v:.4f}" for v in values) + " |")
    lines.extend(
        [
            "",
            "Table: Execution of the original 140-query Favorita covariance workload through the same corrected "
            "LMFAO C++ backend. Within each egraph engine, compare shared with single-root to isolate the benefit "
            "of root choice, and shared with roots to isolate shared-producer merging. Queries, data, cost model "
            "and backend are fixed across these ablations. All variants retain identical-subexpression reuse and "
            "backend multi-output optimization. Times are medians of warm executions, excluding "
            "optimization, code generation, compilation, data loading and sorting. This matches the paper's "
            "computation timing scope, but uses medians rather than its means; dataset size and CPU affinity "
            "are recorded in metadata.json. Only selected variants are shown. Unavailable plans are not timings; "
            "see pipeline.json for failure details. "
            "Identical plans reuse execution observations as recorded by execution_aliases.",
            "",
            "Preparation costs are separate observations, one per phase:",
            "",
            *costs,
            "",
            "Optimization + generation measures the LMFAO compiler process, including its frontend, "
            "the optimizer subprocess (translation, rewriting/export, decoding, extraction and serialization), "
            "and C++ generation. Independent correctness checks and separate optimizer-only samples/graph "
            "diagnostics are excluded for both. Whole-process execution, including loading and sorting, "
            "remains in pipeline.json.",
            "",
            "For N executions of a reused plan, the estimated cost is optimization/generation + "
            "compilation + N × execution. This is an amortization model, not a measured end-to-end runtime; "
            "state whether execution includes loading and sorting.",
            "",
            *quality,
            "",
            "Ordinary binding controls use the same shared-view rules, cost function, joint extractor and backend. "
            "Named retains each source binder as constructor data; canonical uses one name for these closed kernels. "
            "Their preparation includes translation/canonicalization and extraction. All selected plans pass "
            "the same output checks; plan.json and plan.txt retain the selected queries and roots.",
        ]
    )
    return "\n".join(lines) + "\n"


def plan_text(plan: dict[str, Any]) -> str:
    """Render selected view equations and query references in serialized ID order."""
    names = [a for a, _ in model.WORKLOAD.attributes]
    tables = list(model.WORKLOAD.relations)
    lines = []
    for i, view in enumerate(plan["views"]):
        keys = ", ".join(names[k] for k in view["keys"])
        columns = []
        for j, aggregate in enumerate(view["aggregates"]):
            factors = [
                name if power == 1 else f"{name}^{power}"
                for f in aggregate["functions"]
                for name, power in [model.WORKLOAD.functions[f]]
            ]
            factors += [f"V{v}.a{a}" for v, a in aggregate["incoming"]]
            inputs = [tables[view["origin"]], *(f"V{v}" for v, _ in aggregate["incoming"])]
            columns.append(f"  a{j} = SUM({' * '.join(factors) or '1'}) FROM {' NATURAL JOIN '.join(inputs)}")
        lines += [f"V{i}[{keys}] ({tables[view['origin']]} -> {tables[view['destination']]}):", *columns, ""]
    for i, output in enumerate(plan["outputs"]):
        query = model.WORKLOAD.queries[i]
        keys, weight = ", ".join(query.groups), " * ".join(query.factors) or "1"
        lines.append(f"q{i}[{keys}] = V{output['view']}.a{output['aggregate']}  # SUM({weight}) over the full join")
    return "\n".join(lines) + "\n"
