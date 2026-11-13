#!/usr/bin/env python3
"""Reproduce the congruence CDF from existing cached selected C/OFF results.

Run export_corpus_congruence_cdf.py --selected INPUT --output-dir OUTPUT [--render]
No collection, engine launches, tests or TeX builds.
"""

import argparse
import collections
import copy
import gzip
import hashlib
import json
import math
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
points = selected["points"]
assert len(points) == 486
ratios = sorted(point["y"] for point in points)
quantiles = {str(q): ratios[math.ceil(q * len(points)) - 1] for q in (0.5, 0.95)}
upper = 3.6
counts = collections.Counter(ratios)
cumulative = 0
ranks = {}
steps: list[dict[str, float]] = [{"ratio": 1, "fraction": 0}]
for ratio, count in sorted(counts.items()):
    cumulative += count
    ranks[ratio] = cumulative / len(points)
    steps.append({"ratio": ratio, "fraction": ranks[ratio]})
steps.append({"ratio": upper, "fraction": 1})
guides = [
    {
        "ratio": quantiles[str(q)],
        "fraction": q,
        "x_start": 1,
        "y_start": 0,
        "label": f"{q:.0%} < {math.ceil(quantiles[str(q)] * 100) / 100:.2f}×",
    }
    for q in (0.5, 0.95)
]
spec = copy.deepcopy(selected["spec_template"])
spec.pop("title", None)
spec.update(width=250, height=145)
spec["layer"][0]["data"] = {"values": guides}
spec["layer"][0]["encoding"]["x"]["field"] = "x_start"
spec["layer"][1]["data"] = {"values": guides}
spec["layer"][1]["encoding"]["y"]["field"] = "y_start"
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
spec["layer"][4]["mark"].update(
    align={"expr": "datum.fraction > 0.9 ? 'right' : 'left'"},
    dx={"expr": "datum.fraction > 0.9 ? -5 : 5"},
    baseline={"expr": "datum.fraction > 0.9 ? 'bottom' : 'top'"},
    dy={"expr": "datum.fraction > 0.9 ? -4 : 5"},
)
for layer in spec["layer"]:
    x = layer["encoding"]["x"]
    x["title"] = "Congruence overhead"
    x["scale"] = {"type": "linear", "domain": [1, upper], "nice": False}
    x["axis"]["values"] = [1, 1.5, 2, 2.5, 3, 3.5]
    layer["encoding"]["y"]["title"] = "Workloads"
spec["usermeta"] = {
    "workloads": 486,
    "rounds": 10,
    "candidate_treatment": "term",
    "baseline_treatment": "off",
    "weight": "one per workload",
    "quantile_method": "inverse empirical CDF",
    "quantiles": quantiles,
    "population_confidence_band": False,
    "mode_boundaries": selected["mode_boundaries"],
}
result = {
    "kind": "corpus-congruence-cdf-v1",
    "candidate_treatment": "term",
    "baseline_treatment": "off",
    "population": 486,
    "observations_per_endpoint": 10,
    "quantile_method": "inverse empirical CDF, rank ceil(q*486)",
    "quantiles": quantiles,
    "minimum": ratios[0],
    "maximum": ratios[-1],
    "statistics": (
        "Existing ratios of independent ten-observation arithmetic C/OFF means; equal workload weights. "
        "Per-input ratio intervals retained in points; no population confidence band or new measurements."
    ),
    "points": points,
    "conditions": selected["conditions"],
    "provenance": selected["provenance"],
    "mode_boundaries": selected["mode_boundaries"],
    "original_scatter_file": selected["source_file"],
    "original_scatter_sha256": selected["source_sha256"],
    "selected_payload": source.name,
    "selected_payload_sha256": "sha256:" + hashlib.sha256(source.read_bytes()).hexdigest(),
    "exporter": Path(__file__).name,
    "exporter_sha256": "sha256:" + hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
}
for name, value in [
    ("corpus-congruence-cdf.bound.vl.json.gz", spec),
    ("corpus-congruence-cdf.results.json.gz", result),
]:
    (root / name).write_bytes(gzip.compress((json.dumps(value, ensure_ascii=False) + "\n").encode(), mtime=0))
numbers = (
    "\\providecommand{\\EgglogFigureNumber}[1]{\\ifcsname egglogfigure@#1\\endcsname"
    "\\csname egglogfigure@#1\\endcsname\\else\\textnormal{unavailable}\\fi}\n"
)
for key, value in [
    ("inputs", 486),
    ("observations-per-endpoint", 10),
    ("p50", quantiles["0.5"]),
    ("p95", quantiles["0.95"]),
    ("minimum", ratios[0]),
    ("maximum", ratios[-1]),
]:
    numbers += (
        "\\expandafter\\def\\csname egglogfigure@corpus-congruence-cdf/" + key + "\\endcsname{" + str(value) + "}\n"
    )
(root / "corpus-congruence-cdf.numbers.tex").write_text(numbers)
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
                str(root / "corpus-congruence-cdf.pdf"),
            ],
            check=True,
        )
print(json.dumps({"quantiles": quantiles, "min": ratios[0], "max": ratios[-1], "inputs": len(points)}))
