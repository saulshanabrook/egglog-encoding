#!/usr/bin/env python3
"""Export the recording-only CDF from a selected ten-round observation artifact.

This command only reads cached observations. Optional PDF rendering uses npm.
"""

import argparse
import collections
import copy
import gzip
import hashlib
import json
import math
import statistics
import subprocess
import tempfile
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--selected", type=Path, required=True)
parser.add_argument("--output-dir", type=Path, required=True)
parser.add_argument("--render", action="store_true", help="Render PDF with pinned Vega npm packages")
args = parser.parse_args()
root = args.output_dir
root.mkdir(parents=True, exist_ok=True)
source = args.selected
selected = json.loads(gzip.decompress(source.read_bytes()))
files = {row["logical_id"]: row for row in selected["files"]}
groups = collections.defaultdict(list)
for row in selected["OFF_observations"] + selected["recording_observations"]:
    assert row["binary_sha256"] == selected["binary_sha256"] and row["target_git_sha"] == selected["source_git_sha"]
    assert row["status"] == "success" and row["threads"] == row["requested_threads"] == selected["threads"]
    assert row["timeout_sec"] == selected["timeout_sec"] and row["memory_limit_bytes"] == selected["memory_limit_bytes"]
    groups[row["file_sha256"], row["treatment"]].append(row["wall_sec"])
assert selected["rounds"] == 10
assert selected["treatment"] == "proofs" and selected["baseline_treatment"] == "off"
assert len(files) == len(selected["files"])
assert len(groups) == 2 * len(files) and all(len(values) == 10 for values in groups.values())
points = []
critical = 2.2621571628540993  # Student t, 9 degrees of freedom, two-sided95%; ten observations per endpoint.
for sha, metadata in files.items():
    baseline = groups[sha, "off"]
    candidate = groups[sha, "proofs"]
    b = statistics.fmean(baseline)
    c = statistics.fmean(candidate)
    vb = statistics.variance(baseline) / 10
    vc = statistics.variance(candidate) / 10
    aa = b * b - critical * critical * vb
    bb = -2 * b * c
    cc = c * c - critical * critical * vc
    discriminant = bb * bb - 4 * aa * cc
    interval = (
        [(-bb - math.sqrt(discriminant)) / (2 * aa), (-bb + math.sqrt(discriminant)) / (2 * aa)]
        if aa > 0 and discriminant >= 0
        else None
    )
    points.append(
        {
            "logical_id": sha,
            "file_sha256": sha,
            "path": metadata["path"],
            "workload": metadata["label"],
            "project": metadata["project"],
            "treatment": "proofs",
            "baseline_treatment": "off",
            "reference_n": 10,
            "candidate_n": 10,
            "OFF_mean_seconds": b,
            "recording_mean_seconds": c,
            "y": c / b,
            "ratio_95ci": interval,
            "OFF_mean_95ci": [b - critical * math.sqrt(vb), b + critical * math.sqrt(vb)],
            "recording_mean_95ci": [c - critical * math.sqrt(vc), c + critical * math.sqrt(vc)],
        }
    )
ratios = sorted(point["y"] for point in points)
quantiles = {str(q): ratios[math.ceil(q * len(ratios)) - 1] for q in (0.5, 0.95)}
upper = math.ceil(max(ratios))
counts = collections.Counter(ratios)
cumulative = 0
ranks = {}
steps: list[dict[str, float]] = [{"ratio": 0, "fraction": 0}]
for ratio, count in sorted(counts.items()):
    cumulative += count
    ranks[ratio] = cumulative / len(points)
    steps.append({"ratio": ratio, "fraction": ranks[ratio]})
steps.append({"ratio": upper, "fraction": 1})
bounds = {str(q): math.ceil(quantiles[str(q)] * 100) / 100 for q in (0.5, 0.95)}
guides = [
    {"ratio": quantiles[str(q)], "fraction": q, "zero": 0, "label": f"{q:.0%} < {bounds[str(q)]:.2f}×"}
    for q in (0.5, 0.95)
]
spec = copy.deepcopy(selected["spec_template"])
spec.pop("title", None)
spec["layer"][0]["data"] = {"values": guides}
spec["layer"][1]["data"] = {"values": guides}
spec["layer"][2]["data"] = {"values": steps}
spec["layer"][3]["data"] = {
    "values": [
        {
            "ratio": point["y"],
            "fraction": ranks[point["y"]],
            "project": selected["project_labels"][point["project"]],
            "workload": point["workload"],
        }
        for point in points
    ]
}
spec["layer"][4]["data"] = {"values": guides}
for layer in spec["layer"]:
    x = layer["encoding"]["x"]
    x["title"] = "Proof overhead"
    x["scale"]["domain"] = [0, upper]
    x["axis"]["values"] = [1, 2, 4, 6, 8]
spec["usermeta"] = {
    "workloads": len(files),
    "treatment": "proofs",
    "baseline_treatment": "off",
    "native_args": ["--proofs"],
    "weight": "one per workload",
    "quantile_method": "inverse empirical CDF",
    "quantiles": quantiles,
    "conservative_display_upper_bounds": {".5": bounds["0.5"], ".95": bounds["0.95"]},
    "population_confidence_band": False,
    "proof_extraction": False,
    "proof_verification": False,
}
result = {
    "kind": "corpus-proof-recording-cdf-v1",
    "figure": "applications-corpus-proof-cdf",
    "metric": "whole-process runtime ratio",
    "stage": "proof recording only",
    "treatment": "proofs",
    "baseline_treatment": "off",
    "rounds": 10,
    "source_git_sha": selected["source_git_sha"],
    "binary_sha256": selected["binary_sha256"],
    "threads": selected["threads"],
    "timeout_sec": selected["timeout_sec"],
    "memory_limit_bytes": selected["memory_limit_bytes"],
    "statistics": (
        "Arithmetic means; inverse empirical CDF across equal-weight inputs. "
        "Per-input independent-sample Fieller-style 95% intervals retained, not population CIs."
    ),
    "quantiles": quantiles,
    "max_ratio": max(ratios),
    "points": points,
    "provenance": selected["provenance"],
    "selected_data_file": source.name,
    "selected_data_sha256": "sha256:" + hashlib.sha256(source.read_bytes()).hexdigest(),
    "exporter_file": Path(__file__).name,
    "exporter_sha256": "sha256:" + hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
}
for name, value in [
    ("applications-corpus-proof-cdf.results.json.gz", result),
    ("applications-corpus-proof-cdf.bound.vl.json.gz", spec),
]:
    (root / name).write_bytes(gzip.compress((json.dumps(value, ensure_ascii=False) + "\n").encode(), mtime=0))
(root / "applications-corpus-proof-cdf.table.tex").write_text(
    "\\begin{tabular}{lrrr}\n"
    + r"Mode & Programs & 50th percentile & 95th percentile \\"
    + "\n"
    + f"Proof recording only & {len(files)} & ${quantiles['0.5']:.5f}\\times$ & ${quantiles['0.95']:.5f}\\times$ "
    + r"\\"
    + "\n"
    + "\\end{tabular}\n"
)
(root / "applications-corpus-proof-cdf.numbers.tex").write_text(
    "\\providecommand{\\EgglogFigureNumber}[1]{\\ifcsname egglogfigure@#1\\endcsname"
    "\\csname egglogfigure@#1\\endcsname\\else\\textnormal{unavailable}\\fi}\n"
    + "".join(
        "\\expandafter\\def\\csname egglogfigure@applications-corpus-proof-cdf/"
        + key
        + "\\endcsname{"
        + str(value)
        + "}\n"
        for key, value in [
            ("workloads", len(files)),
            ("recording/median", quantiles["0.5"]),
            ("recording/p95", quantiles["0.95"]),
        ]
    )
)
if args.render:
    with tempfile.NamedTemporaryFile(mode="w", suffix=".vl.json") as temporary:
        json.dump(spec, temporary, ensure_ascii=False)
        temporary.flush()
        subprocess.run(
            [
                "npx",
                "--yes",
                "--package=vega@6.4.0",
                "--package=vega-lite@6.4.3",
                "--package=vega-cli@6.4.0",
                "--package=canvas@3.2.3",
                "vl2pdf",
                temporary.name,
                str(root / "applications-corpus-proof-cdf.pdf"),
            ],
            check=True,
        )
print(json.dumps({"inputs": len(points), "quantiles": quantiles, "max": max(ratios), "mode": "proofs"}))
