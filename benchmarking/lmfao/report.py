"""Execution comparison and separate preparation costs for the LMFAO case study."""

from __future__ import annotations

import json
from typing import Any

from scipy import stats

from benchmarking.reports.analysis import _ratio_estimate, _sample_estimate

from . import model


def preparation_costs(plans: dict[str, Any], builds: dict[str, Any], aliases: dict[str, str]) -> dict[str, Any]:
    result = {}
    for label in ["original", *(["paper"] if "paper" in builds else []), *plans]:
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


def interval(estimate: dict[str, Any], digits: int = 3) -> str:
    point, low, high = (estimate[k] for k in ("point", "ci_low", "ci_high"))
    if point is None:
        return "—"
    result = f"{point:.{digits}f}"
    return result if low is None else f"{result} [{low:.{digits}f}, {high:.{digits}f}]"


def execution_ratios(report: dict[str, Any]) -> dict[str, Any]:
    """Use the paper harness's independent Fieller intervals for time ratios."""
    samples = {label: item["computation_seconds"]["values"] for label, item in report["execution"].items()}
    result = {"original": {"point": 1.0, "ci_low": None, "ci_high": None}}
    for label, values in samples.items():
        if label == "original":
            continue
        n = min(len(values), len(samples["original"]))
        critical = float(stats.t.ppf(0.975, n - 1)) if n > 1 else None
        baseline = _sample_estimate(samples["original"], None, critical)
        candidate = _sample_estimate(values, None, critical)
        result[label] = _ratio_estimate(baseline, candidate, critical).estimate._asdict()
    return result


def comparison_rows(report: dict[str, Any]) -> list[list[str]]:
    rows = []
    names = {
        "original": "LMFAO configured roots",
        "paper": "LMFAO + paper root heuristic",
        "slotted": "Slotted egglog",
        "debruijn": "Ordinary egglog (de Bruijn)",
    }
    ratios = execution_ratios(report)
    for label, name in names.items():
        optimization = report["optimizer"].get(label, {})
        timing = optimization.get("process_seconds")
        runtime = interval(timing["mean"]) if timing else "—"
        memory = optimization.get("peak_rss_mib")
        rss = interval(memory["mean"], 1) if memory else "—"
        if label not in report["accounted_pipeline"]:
            failures = sorted({row["status"] for row in optimization.get("failures", [])})
            reason = (
                ", ".join(failures) or optimization.get("pipeline_issue") or optimization.get("issue") or "unavailable"
            )
            rows.append(
                [
                    f"{name} ({reason})",
                    runtime,
                    rss,
                    "—",
                    "—",
                    "—",
                    f"{optimization.get('completed_samples', 0)} completed, "
                    f"{len(optimization.get('failures', []))} failed",
                ]
            )
            continue
        preparation = report["accounted_pipeline"][label]
        executed = preparation["execution_label"]
        samples = report["execution"][executed]["computation_seconds"]["samples"]
        rows.append(
            [
                name,
                runtime,
                rss,
                f"{preparation['optimization_and_generation_seconds']:.3f}",
                f"{preparation['compilation_seconds']:.3f}",
                interval(ratios[executed]),
                f"{optimization.get('completed_samples', '—')} egraph / {samples} execution",
            ]
        )
    return rows


def comparison_caption(report: dict[str, Any]) -> str:
    limit = report["optimizer_memory_limit_bytes"]
    bound = f"{limit / 1024**3:g} GiB allocator/address-space cap" if limit is not None else "no memory cap"
    baseline = interval(report["execution"]["original"]["computation_seconds"]["mean"], 4)
    lines = [
        "Favorita covariance batch (140 queries) on the public 2M-Sales-row sample, using the same pinned frontend "
        "and corrected C++ backend. This replicates the workload, not the paper's full dataset (127M joined tuples). "
        "The paper-root control uses our implementation of section 3.3's coverage heuristic; configured roots "
        "are those shipped in the artifact.",
        "",
        f"Both egraph encodings use the same {report['rewrite_round_budget']}-round search and {bound}, "
        "with proofs off. "
        "Resource failures have no query-time ratio. Samples count completed egraph/query runs; "
        "collection stops after a resource failure.",
        "",
        "Rewrite time and peak RSS are process means with 95% Student-t intervals, excluding DAG extraction. "
        "Plan + generate includes a rewrite run, extraction and C++ generation; do not add it to Rewrite. "
        "Planning/generation and C++ compilation are single observations without intervals.",
        "",
        "Query time is mean warm computation time divided by the configured-roots LMFAO mean (lower is better), "
        f"with independent 95% Fieller intervals. The baseline is {baseline} seconds. "
        "Computation excludes loading, sorting and checking, as in the paper. "
        "Undefined and single-sample intervals are omitted. Identical plans reuse checked execution observations.",
    ]
    return "\n".join(lines) + "\n"


def comparison_markdown(report: dict[str, Any]) -> str:
    lines = [
        "| Method | Rewrite (s) | Peak RSS (MiB) | Plan + generate (s) | "
        "C++ compilation (s) | Query time / LMFAO | Samples |",
        "|---|---:|---:|---:|---:|---:|---|",
        *("| " + " | ".join(row) + " |" for row in comparison_rows(report)),
        "",
        comparison_caption(report),
    ]
    return "\n".join(lines)


def paper_results(report: dict[str, Any]) -> dict[str, str]:
    """Format the checked execution table for the shared paper publisher."""
    if not {"original", "paper", "slotted"} <= report["accounted_pipeline"].keys() or any(
        item.get("pipeline_issue") for item in report["optimizer"].values()
    ):
        raise ValueError("LMFAO execution comparison is incomplete; no paper table replaced")
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
        "—": r"\textemdash{}",
    }

    def tex(value: str) -> str:
        return "".join(escapes.get(c, c) for c in value)

    table = [
        "% GENERATED: ./bench.py figures lmfao; provenance in lmfao.results.json",
        r"\begingroup\scriptsize\setlength{\tabcolsep}{3pt}",
        r"\begin{tabular}{lrrrrrl}",
        r"Method & \shortstack{Rewrite\\(s)} & \shortstack{Peak RSS\\(MiB)} & "
        r"\shortstack{Plan +\\generate (s)} & \shortstack{C++ compile\\(s)} & "
        r"\shortstack{Query time /\\LMFAO} & \shortstack{Samples\\egraph / exec.} \\",
        r"\hline",
    ]
    for row in comparison_rows(report):
        cells = list(map(tex, row))
        for i in (1, 2, 5):
            cells[i] = r"\shortstack{" + cells[i].replace(" [", r"\\{}[") + "}"
        cells[0] = r"\shortstack[l]{" + tex(row[0]).replace(" (", r"\\(") + "}"
        cells[-1] = (
            r"\shortstack[l]{"
            + tex(row[-1]).replace(" egraph", "").replace(" execution", "").replace(", ", r"\\")
            + "}"
        )
        table.append(" & ".join(cells) + r" \\")
    table += [r"\end{tabular}", r"\endgroup", ""]
    return {
        "lmfao.table.tex": "\n".join(table),
        "lmfao.caption.tex": tex(" ".join(comparison_caption(report).split())) + "\n",
        "lmfao.md": comparison_markdown(report),
        "lmfao.results.json": json.dumps(report, indent=2, allow_nan=False) + "\n",
    }


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
