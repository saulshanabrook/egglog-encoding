#!/usr/bin/env python3
"""Prepare PR comparison plots from public benchmark grouped exports only.

The collector is ./bench.py. This utility never opens or writes report JSONL.
The repository's grouped codec, latest-N selector, exclusion policy, arithmetic
means, and independent Fieller intervals remain the statistical implementation.
"""

from __future__ import annotations

import argparse
from dataclasses import asdict, replace
import hashlib
import json
import math
import os
from pathlib import Path
import re
import shlex
import subprocess
import sys
import tempfile


def write_json(path, data):
    path.write_text(json.dumps(data, indent=2, ensure_ascii=False, allow_nan=False) + "\n")


def digest(path):
    return "sha256:" + hashlib.sha256(path.read_bytes()).hexdigest()


def git(root, *args):
    return subprocess.check_output(["git", "-C", str(root), *args], text=True).strip()


def validate_manifest(manifest, *, require_bound):
    root = manifest["renderer_root"]
    if git(root, "rev-parse", "HEAD") != manifest["renderer_git_sha"] or git(root, "status", "--porcelain"):
        raise ValueError("The fixed benchmark/analysis checkout changed")
    if require_bound:
        if manifest.get("binding_status") != "final":
            raise ValueError("Source revisions are not final; collection/rendering is not ready")
        for source in (manifest["native"], *manifest["stages"]):
            if not re.fullmatch(r"[0-9a-f]{40}", source["git_sha"] or ""):
                raise ValueError(f"Unbound source revision: {source['label']}")


def config_and_figures(manifest):
    from benchmarking.figures import load_config, resolve_figures

    root = Path(manifest["renderer_root"])
    config = load_config(root / "figures/catalog.json")
    figures = resolve_figures(config, ("slotted-runtime", "slotted-multipattern-runtime"), root)
    counts = {item.figure.name: len(item.files) for item in figures}
    if counts != {"slotted-runtime": 10, "slotted-multipattern-runtime": 8}:
        raise ValueError(f"Unexpected catalog workload counts: {counts}")
    return config, figures


def comparison_sources(manifest, index, figure):
    if figure.figure.name == "slotted-runtime":
        return manifest["native"], "slotted-ref-nested", "slotted-no-aliasing"
    if index == 0:
        return manifest["stages"][0], "slotted-no-aliasing", "slotted"
    return manifest["stages"][index - 1], "slotted", "slotted"


def commands(manifest, figures):
    root = Path(manifest["renderer_root"])
    protocol = manifest["protocol"]
    result = []
    for index, stage in enumerate(manifest["stages"]):
        for figure in figures:
            baseline_source, baseline, candidate = comparison_sources(manifest, index, figure)
            baseline_target = f"{baseline_source['label']}="
            if index == 0 and figure.figure.name == "slotted-runtime":
                baseline_target += baseline_source["source"]
            memory = (
                ["--no-memory-limit"] if protocol["memory_limit_bytes"] is None
                else ["--memory-limit-gib", str(protocol["memory_limit_bytes"] / 1024**3)]
            )
            command = [
                "taskset", "-c", str(protocol["cpu"]), "./bench.py",
                *(str(file.absolute_path) for file in figure.files),
                "--target", f"{stage['label']}={stage['source']}", "--treatment", candidate,
                "--compare-target", baseline_target, "--compare-treatment", baseline,
                "--rounds", str(protocol["rounds"]), "--timeout-sec", str(protocol["timeout_sec"]),
                *memory, "--report", manifest["report_path"], "--detail", "files", "--format", "markdown",
            ]
            result.append({"stage": stage["label"], "figure": figure.figure.name,
                           "cwd": str(root), "argv": command})
    return result


def endpoint(grouped, stage, treatment, protocol):
    from benchmarking.models import BenchmarkEndpoint, TargetRow

    groups = [group for group in grouped.data["groups"]
              if stage["label"] in group["labels"] and group["key"]["treatment"] == treatment]
    hashes = {group["key"]["binary_sha256"] for group in groups}
    if len(hashes) != 1:
        raise ValueError(f"{stage['label']} / {treatment}: expected one current binary, found {hashes}")
    sample = max((row for group in groups for row in group["samples"]), key=lambda row: row["row_index"])
    if sample["target_git_sha"] != stage["git_sha"] or sample["target_is_dirty"]:
        raise ValueError(f"{stage['label']}: grouped provenance does not identify the expected clean source commit")
    target = TargetRow(**{name: sample[f"target_{name}"] for name in
                          ("source", "path", "git_ref", "git_sha", "is_dirty", "label")})
    return BenchmarkEndpoint(target, next(iter(hashes)), treatment, protocol["memory_limit_bytes"])


def selected_condition(grouped, target, file, manifest):
    from benchmarking.engines import TREATMENT_SPECS
    from benchmarking.reports.store import select_observations

    protocol = manifest["protocol"]
    # Use the export's frozen exclusions, as ordinary offline report analysis does.
    file = replace(file, exclusions=grouped.exclusions_by_input.get(file.sha256, file.exclusions))
    selection = select_observations(grouped, target, file, protocol["rounds"], protocol["timeout_sec"])
    if selection.issue:
        raise ValueError(f"{target.target.label}/{target.treatment}/{file.display_path}: {selection.issue}")
    observations = [dict(row.record) for row in selection.rows]
    for row in observations:
        row.pop("timing_summary", None)
        if row["memory_limit_bytes"] != protocol["memory_limit_bytes"] or row["timeout_sec"] > protocol["timeout_sec"]:
            raise ValueError("Selected observations do not use the manifest's cap and permitted watchdogs")
        if row["target_git_sha"] != target.target.git_sha or row["target_is_dirty"]:
            raise ValueError("Selected observations do not use the expected clean source")
    physical = file.for_binary(TREATMENT_SPECS[target.treatment].binary_name)
    return {"endpoint": asdict(target), "logical_id": file.sha256, "file_path": file.display_path,
            "physical_file_sha256": physical.sha256, "selected_row_indices": [row.row_index for row in selection.rows],
            "exclusion": asdict(selection.exclusion) if selection.exclusion else None, "observations": observations}


def comparisons(grouped, baseline, candidate, files, protocol):
    from benchmarking.models import ComparisonSpec
    from benchmarking.reports.analysis import analyze_pair

    comparison = ComparisonSpec(baseline, candidate, files, protocol["rounds"], protocol["timeout_sec"])
    data = analyze_pair(grouped, comparison, "files")
    rows = []
    for item in data.files:
        estimate = item.ratio.estimate
        if estimate.point is None or not math.isfinite(estimate.point):
            raise ValueError(f"Cannot publish incomplete comparison: {files[item.file_order].display_path}: {item.ratio.issue}")
        rows.append({"file_path": files[item.file_order].display_path,
                     "logical_id": files[item.file_order].sha256, "metric": item.metric,
                     "baseline": item.baseline._asdict(), "candidate": item.candidate._asdict(),
                     "ratio": estimate.point, "ci_low": estimate.ci_low, "ci_high": estimate.ci_high,
                     "issue": item.ratio.issue, "result_class": item.ratio.result_class})
    return {"baseline": asdict(baseline), "candidate": asdict(candidate), "files": rows,
            "summary": [{"metric": row.metric, "kind": row.summary_kind,
                         "file_order": row.file_order, "estimate": row.ratio.estimate._asdict(),
                         "issue": row.ratio.issue} for row in data.summary]}


def workload_name(path):
    name = Path(path).stem.removesuffix("-44rules")
    kernel, phase = name.rsplit("_", 1)
    return {"batax": "BATAX", "mmm": "MMM", "mmm_sum": "ΣMMM", "mttkrp": "MTTKRP", "ttm": "TTM"}[kernel] + " · " + phase


def mmm_focus_rows(comparison):
    """Expose the four motivating nested workloads without new statistics."""
    by_name = {Path(row["file_path"]).stem: row for row in comparison["files"] if row["metric"] == "wall_sec"}
    result = []
    for name in ("mmm_sum_1st", "mmm_sum_2nd", "mmm_1st", "mmm_2nd"):
        row = by_name[name + "-44rules"]
        result.append({
            "workload": workload_name(row["file_path"]), "file_path": row["file_path"],
            "logical_id": row["logical_id"],
            "baseline_mean_ms": 1000 * row["baseline"]["point"],
            "candidate_mean_ms": 1000 * row["candidate"]["point"],
            "ratio": {"point": row["ratio"], "ci_low": row["ci_low"], "ci_high": row["ci_high"]},
            "issue": row["issue"], "result_class": row["result_class"],
        })
    return result


def mmm_focus_summary(cumulative_result):
    nested = next(suite for suite in cumulative_result["suites"] if suite["name"] == "slotted-runtime")
    rows = mmm_focus_rows(nested["comparison"])
    selected = {row["logical_id"] for row in rows}
    return {
        "schema_version": 1, "kind": "Nested ΣMMM/MMM baseline-to-final comparison",
        **{key: cumulative_result[key] for key in
           ("baseline", "candidate", "protocol", "confidence", "statistics", "manifest_sha256",
            "source_grouped", "analysis")},
        "treatment": "slotted-no-aliasing", "units": {"means": "milliseconds", "ratio": "candidate / baseline"},
        "rows": rows,
        "conditions": [condition for condition in nested["conditions"] if condition["logical_id"] in selected],
    }


def panel(values, order, title, axis_title, overlay):
    bounds = [1, *(row[key] for row in values for key in ("ratio", "ci_low", "ci_high") if row[key] is not None)]
    domain = [min(0, min(bounds)), max(bounds) * 1.08]
    x = {"type": "quantitative", "scale": {"type": "symlog", "constant": 0.1, "domain": domain, "nice": False},
         "axis": {"title": axis_title, "labelExpr": "format(datum.value,',~f') + '×'",
                  "values": [-64, -16, -4, -1, 0, .1, .25, .5, 1, 2, 4, 8, 16, 32, 64, 128, 256],
                  "labelOverlap": "greedy", "grid": True}}
    encoding = {"x": x, "y": {"field": "workload", "type": "nominal", "sort": order, "title": None,
                              "axis": {"labelLimit": 130, "minExtent": 100}}}
    if overlay:
        encoding.update({"yOffset": {"field": "series", "sort": ["Parent", "This PR"],
                                     "scale": {"domain": ["Parent", "This PR"]}},
                         "color": {"field": "series", "type": "nominal", "title": None,
                                   "scale": {"domain": ["Parent", "This PR"], "range": ["#999999", "#111111"]},
                                   "legend": {"orient": "top", "symbolType": "square"}}})
    else:
        lo, hi = min(bounds), max(bounds)
        padding = max(.03, (hi - lo) * .08)
        x["scale"] = {"type": "linear", "domain": [min(.95, lo - padding), max(1.05, hi + padding)], "nice": False}
        x["axis"].pop("values")
        x["axis"]["tickCount"] = 7
        encoding["color"] = {"value": "#111111"}
    return {"title": {"text": title, "anchor": "start"}, "width": 410, "height": len(order) * 32,
            "data": {"values": values}, "encoding": encoding,
            "layer": [
                {"mark": {"type": "rule", "color": "#89919b", "strokeDash": [4, 3]},
                 "encoding": {"x": {"datum": 1}, "y": {"value": 0},
                              "y2": {"value": len(order) * 32}, "yOffset": {"value": 0},
                              "color": {"value": "#89919b"}},
                 "transform": [{"aggregate": [{"op": "count", "as": "n"}]}]},
                {"mark": {"type": "rule", "strokeWidth": 1.2},
                 "encoding": {"x": {"field": "ci_low"}, "x2": {"field": "ci_high"}},
                 "transform": [{"filter": "isValid(datum.ci_low) && isValid(datum.ci_high)"}]},
                *[{"mark": {"type": "tick", "orient": "vertical", "size": 7, "thickness": 1.2},
                   "encoding": {"x": {"field": field}}, "transform": [{"filter": f"isValid(datum.{field})"}]}
                  for field in ("ci_low", "ci_high")],
                {"mark": {"type": "point", "filled": True, "shape": "square", "size": 30},
                 "encoding": {"x": {"field": "ratio"}, "tooltip": [{"field": key} for key in
                               ("workload", "series", "ratio", "ci_low", "ci_high", "issue")]}},
                {"mark": {"type": "text", "align": "left", "dx": 7, "fontSize": 9},
                 "encoding": {"x": {"field": "ratio"}, "text": {"field": "issue"}},
                 "transform": [{"filter": "isValid(datum.issue) && datum.issue !== ''"}]},
            ]}


def specification(result):
    nested = next(suite for suite in result["suites"] if suite["name"] == "slotted-runtime")
    multi = next(suite for suite in result["suites"] if suite["name"] == "slotted-multipattern-runtime")
    order = [workload_name(row["file_path"]) for row in sorted(
        (row for row in nested["child_native"]["files"] if row["metric"] == "wall_sec"), key=lambda row: row["ratio"])]
    native = [{**row, "workload": workload_name(row["file_path"]), "series": label}
              for label, pair in (("Parent", nested["parent_native"]), ("This PR", nested["child_native"]))
              for row in pair["files"] if row["metric"] == "wall_sec"]
    top = panel(native, order, "Nested SDQL · 10 workloads · native comparison",
                "extlog / native Slotted (lower is faster)", True)
    top["width"] = 795
    bottom = []
    for suite, title in ((nested, "Nested SDQL · incremental change"), (multi, "Multipattern SDQL · incremental change")):
        delta = [{**row, "workload": workload_name(row["file_path"]), "series": "This PR / parent"}
                 for row in suite["child_parent"]["files"] if row["metric"] == "wall_sec"]
        selected_order = order if suite is nested else [row["workload"] for row in sorted(delta, key=lambda row: row["ratio"])]
        item = panel(delta, selected_order, title, "This PR / parent (lower is faster)", False)
        item["width"] = 330
        bottom.append(item)
    protocol = result["protocol"]
    cap = "uncapped" if protocol["memory_limit_bytes"] is None else f"{protocol['memory_limit_bytes'] / 1024**3:g} GiB allocator cap"
    sampling = f"PR comparison pilot · {protocol['rounds']} observations per condition · CPU {protocol['cpu']} · {cap}"
    watchdog = protocol.get("watchdog_note", f"{protocol['timeout_sec']} s timeout per workload process.")
    return {"$schema": "https://vega.github.io/schema/vega-lite/v6.json",
            "background": "white",
            "title": {"text": result["title"], "anchor": "start", "fontSize": 19,
                      "subtitle": [sampling, watchdog,
                                   "Arithmetic-mean whole-process time; independent Fieller 95% intervals; lower ratios mean less runtime.",
                                   f"Parent {result['parent']['git_sha'][:12]} → this PR {result['stage']['git_sha'][:12]}; native {result['native']['git_sha'][:12]}.",
                                   "Multipattern: parent-to-child changes only; native multipattern omitted at user request.",
                                   "Multipattern follows the paper catalog: BATAX 2nd and MTTKRP 2nd omitted; no exclusion changes."],
                      "subtitleFontSize": 11, "subtitlePadding": 7},
            "vconcat": [top, {"hconcat": bottom, "spacing": 35}], "spacing": 38,
            "resolve": {"scale": {"color": "shared"}},
            "config": {"font": "Arial", "view": {"stroke": None},
                       "axis": {"labelFontSize": 11, "titleFontSize": 11, "titleFontWeight": "normal", "gridColor": "#e6e8eb"},
                       "title": {"fontSize": 13}, "legend": {"labelFontSize": 11}}}


def render(manifest, figures, args):
    from benchmarking.figures import VEGA_PACKAGES
    from benchmarking.reports.store import parse_grouped_report
    from scipy import stats

    grouped_path = Path(manifest["grouped_path"])
    grouped_bytes = grouped_path.read_bytes()
    grouped_sha256 = "sha256:" + hashlib.sha256(grouped_bytes).hexdigest()
    grouped = parse_grouped_report(grouped_bytes, str(grouped_path))
    output = Path(manifest["output_dir"])
    output.mkdir(parents=True, exist_ok=True)
    protocol = manifest["protocol"]
    if not args.no_images:
        actual_node = subprocess.check_output(
            ["taskset", "-c", str(manifest["renderer_cpu"]), "npx", "--yes",
             f"--package={manifest['node_package']}", "node", "--version"], text=True
        ).strip()
        if actual_node != manifest["node_version"]:
            raise ValueError(f"Unexpected Node runtime: {actual_node}")
    outputs = []
    with tempfile.TemporaryDirectory(prefix=".pr-comparison.", dir=output) as temporary:
        temporary = Path(temporary)
        for parent, stage in zip(manifest["stages"], manifest["stages"][1:]):
            if args.only and stage["label"] not in args.only:
                continue
            result = {"schema_version": 1, "kind": "PR comparison pilot", "title": stage["title"],
                      "protocol": protocol, "native": manifest["native"], "parent": parent, "stage": stage,
                      "confidence": 0.95,
                      "t_critical": None if protocol["rounds"] < 2 else float(stats.t.ppf(0.975, protocol["rounds"] - 1)),
                      "units": {"wall_sec": "seconds", "max_rss_bytes": "bytes"},
                      "manifest_sha256": args.manifest_sha256, "prebuild": manifest["prebuild"],
                      "concurrent_work": manifest["concurrent_work"],
                      "host_isolation": manifest["host_isolation"],
                      "scope": manifest["scope"],
                      "statistics": "Repository arithmetic means and independent Fieller 95% intervals; newest N observations selected by shared cache policy.",
                      "source_grouped": {"path": str(grouped_path), "sha256": grouped_sha256},
                      "renderer": {"git_sha": git(manifest["renderer_root"], "rev-parse", "HEAD"),
                                   "script_sha256": digest(Path(__file__)), "vega_packages": VEGA_PACKAGES,
                                   "node_package": manifest["node_package"], "node_version": manifest["node_version"],
                                   "cpu": manifest["renderer_cpu"]},
                      "exclusions": {identity: [asdict(rule) for rule in rules] for identity, rules in grouped.exclusions_by_input.items()},
                      "catalog": {"path": str(Path(manifest["renderer_root"]) / "figures/catalog.json"),
                                  "sha256": digest(Path(manifest["renderer_root"]) / "figures/catalog.json")},
                      "suites": []}
            for figure in figures:
                is_nested = figure.figure.name == "slotted-runtime"
                candidate_treatment = "slotted-no-aliasing" if is_nested else "slotted"
                before = endpoint(grouped, parent, candidate_treatment, protocol)
                after = endpoint(grouped, stage, candidate_treatment, protocol)
                selected_endpoints = (before, after)
                native = endpoint(grouped, manifest["native"], "slotted-ref-nested", protocol) if is_nested else None
                if native is not None:
                    selected_endpoints = (native, *selected_endpoints)
                conditions = [selected_condition(grouped, selected, file, manifest)
                              for selected in selected_endpoints for file in figure.files]
                suite = {"name": figure.figure.name, "conditions": conditions,
                         "child_parent": comparisons(grouped, before, after, figure.files, protocol)}
                if native is not None:
                    suite.update(parent_native=comparisons(grouped, native, before, figure.files, protocol),
                                 child_native=comparisons(grouped, native, after, figure.files, protocol))
                result["suites"].append(suite)
            name = stage["label"] + "-slotted-comparison"
            write_json(temporary / f"{name}.results.json", result)
            spec_path = temporary / f"{name}.bound.vl.json"
            write_json(spec_path, specification(result))
            if not args.no_images:
                for extension in ("svg", "pdf", "png"):
                    command = ["taskset", "-c", str(manifest["renderer_cpu"]),
                               "npx", "--yes", f"--package={manifest['node_package']}",
                               *(f"--package={package}" for package in VEGA_PACKAGES),
                               f"vl2{extension}", str(spec_path), str(temporary / f"{name}.{extension}")]
                    if extension == "png":
                        command += ["-s", "2"]
                    completed = subprocess.run(command, cwd=manifest["renderer_root"], capture_output=True, text=True, check=True)
                    if any(line.startswith(("ERROR", "WARN")) for line in completed.stderr.splitlines()):
                        raise ValueError(f"Vega diagnostics for {name}: {completed.stderr}")
                    if not (temporary / f"{name}.{extension}").stat().st_size:
                        raise ValueError(f"Empty rendered image: {name}.{extension}")
            print(f"Prepared {name}", file=sys.stderr)
        # Every requested condition and format must succeed before publication.
        for path in sorted(temporary.iterdir()):
            destination = output / path.name
            os.replace(path, destination)
            outputs.append(str(destination))
    print(json.dumps({"outputs": outputs}, indent=2))


def cumulative(manifest, figures, args):
    from benchmarking.reports.store import parse_grouped_report
    from scipy import stats

    grouped_path = Path(manifest["grouped_path"])
    grouped_bytes = grouped_path.read_bytes()
    grouped = parse_grouped_report(grouped_bytes, str(grouped_path))
    protocol = manifest["protocol"]
    parent, stage = manifest["stages"][0], manifest["stages"][-1]
    result = {
        "schema_version": 1, "kind": "Cumulative PR comparison pilot",
        "baseline": parent, "candidate": stage, "protocol": protocol,
        "confidence": 0.95,
        "t_critical": None if protocol["rounds"] < 2 else float(stats.t.ppf(0.975, protocol["rounds"] - 1)),
        "units": {"wall_sec": "seconds", "max_rss_bytes": "bytes"},
        "statistics": "Shared analyze_pair arithmetic means and independent Fieller 95% ratio intervals; percent intervals are monotone transforms of ratio intervals. Absolute changes are differences of mean point estimates, without an asserted absolute-change CI.",
        "manifest_sha256": args.manifest_sha256, "scope": manifest["scope"],
        "prebuild": manifest["prebuild"], "concurrent_work": manifest["concurrent_work"],
        "host_isolation": manifest["host_isolation"],
        "exclusions": {identity: [asdict(rule) for rule in rules] for identity, rules in grouped.exclusions_by_input.items()},
        "source_grouped": {"path": str(grouped_path), "sha256": "sha256:" + hashlib.sha256(grouped_bytes).hexdigest()},
        "analysis": {"git_sha": git(manifest["renderer_root"], "rev-parse", "HEAD"),
                     "script_sha256": digest(Path(__file__))},
        "suites": [],
    }
    for figure in figures:
        treatment = "slotted-no-aliasing" if figure.figure.name == "slotted-runtime" else "slotted"
        before = endpoint(grouped, parent, treatment, protocol)
        after = endpoint(grouped, stage, treatment, protocol)
        conditions = [selected_condition(grouped, target, file, manifest)
                      for target in (before, after) for file in figure.files]
        pair = comparisons(grouped, before, after, figure.files, protocol)
        for row in pair["files"]:
            row["absolute_change"] = row["candidate"]["point"] - row["baseline"]["point"]
            row["change_percent"] = 100 * (row["ratio"] - 1)
            row["change_percent_ci_low"] = None if row["ci_low"] is None else 100 * (row["ci_low"] - 1)
            row["change_percent_ci_high"] = None if row["ci_high"] is None else 100 * (row["ci_high"] - 1)
        walls = [row for row in pair["files"] if row["metric"] == "wall_sec"]
        summed = {label: math.fsum(row[label]["point"] for row in walls) for label in ("baseline", "candidate")}
        summed["absolute_change"] = summed["candidate"] - summed["baseline"]
        result["suites"].append({"name": figure.figure.name, "conditions": conditions,
                                "comparison": pair, "summed_mean_wall_sec": summed})
    output = args.manifest.parent
    destination = output / "cumulative-results.json"
    focus_destination = output / "mmm-focus-results.json"
    with tempfile.TemporaryDirectory(prefix=".cumulative.", dir=output) as temporary:
        prepared = Path(temporary) / destination.name
        write_json(prepared, result)
        prepared_focus = Path(temporary) / focus_destination.name
        write_json(prepared_focus, mmm_focus_summary(result))
        os.replace(prepared, destination)
        os.replace(prepared_focus, focus_destination)
    print(str(destination))
    print(str(focus_destination))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("plan", "render", "cumulative"))
    parser.add_argument("--manifest", type=Path, default=Path(__file__).with_name("manifest.json"))
    parser.add_argument("--only", action="append", help="Limit rendering or command planning to a stage label")
    parser.add_argument("--no-images", action="store_true")
    args = parser.parse_args()
    manifest_bytes = args.manifest.read_bytes()
    args.manifest_sha256 = "sha256:" + hashlib.sha256(manifest_bytes).hexdigest()
    manifest = json.loads(manifest_bytes)
    validate_manifest(manifest, require_bound=args.action != "plan")
    sys.path.insert(0, manifest["renderer_root"])
    _, figures = config_and_figures(manifest)
    if args.action == "render":
        render(manifest, figures, args)
    elif args.action == "cumulative":
        cumulative(manifest, figures, args)
    else:
        for command in commands(manifest, figures):
            if args.only and command["stage"] not in args.only:
                continue
            print(f"# {command['stage']} · {command['figure']} · cwd={command['cwd']}")
            print(shlex.join(command["argv"]))


if __name__ == "__main__":
    main()
