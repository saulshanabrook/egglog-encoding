#!/usr/bin/env python3
"""Reproduce the appendix two-panel CDF from embedded audited observations only.

Run export_corpus_proof_stages_cdf.py --selected INPUT --output-dir OUTPUT [--render]
No engine launches or TeX builds. --render uses the pinned Vega CLI packages.
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
from typing import Any

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
for rows in (
    selected["OFF_observations"],
    selected["proof_extraction_observations"],
    selected["proof_checking_observations"],
):
    for row in rows:
        groups[row["file_sha256"], row["treatment"]].append(row["wall_sec"])
assert len(files) == 486 and len(groups) == 1458 and all(len(values) == 10 for values in groups.values())
means = {key: statistics.fmean(values) for key, values in groups.items()}


def panel(treatment: str, label: str, upper: float) -> tuple[dict[str, Any], dict[str, Any]]:
    """Bind the main figure's project-dot/step/quantile encoding to one audited mode."""
    points = [
        {
            "file_sha256": sha,
            "path": metadata["path"],
            "workload": metadata["label"],
            "project": metadata["project"],
            "OFF_mean_seconds": means[sha, "off"],
            "mode_mean_seconds": means[sha, treatment],
            "ratio": means[sha, treatment] / means[sha, "off"],
            "observations_per_endpoint": 10,
        }
        for sha, metadata in files.items()
    ]
    ratios = sorted(point["ratio"] for point in points)
    assert upper >= ratios[-1]
    quantiles = {str(q): ratios[math.ceil(q * len(points)) - 1] for q in (0.5, 0.95)}
    ranks = {}
    cumulative = 0
    steps: list[dict[str, float]] = [{"ratio": 1, "fraction": 0}]
    for ratio, count in sorted(collections.Counter(ratios).items()):
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
    spec.pop("config", None)
    spec.pop("usermeta", None)
    spec.pop("title", None)
    spec.update(
        width=205, height=135, title={"text": label, "fontSize": 10, "fontWeight": "normal", "anchor": "middle"}
    )
    spec["layer"][0]["data"] = {"values": guides}
    spec["layer"][0]["encoding"]["x"]["field"] = "x_start"
    spec["layer"][1]["data"] = {"values": guides}
    spec["layer"][1]["encoding"]["y"]["field"] = "y_start"
    spec["layer"][2]["data"] = {"values": steps}
    spec["layer"][3]["data"] = {
        "values": [
            {
                "ratio": point["ratio"],
                "fraction": ranks[point["ratio"]],
                "project": selected["project_labels"][point["project"]],
                "workload": point["workload"],
            }
            for point in points
        ]
    }
    spec["layer"][4]["data"] = {"values": guides}
    spec["layer"][4]["mark"].update(
        align={"expr": "datum.fraction > 0.9 ? 'right' : 'left'"}, dx={"expr": "datum.fraction > 0.9 ? -5 : 5"}
    )
    for layer in spec["layer"]:
        x = layer["encoding"]["x"]
        x["title"] = "Proof overhead"
        x["scale"] = {"type": "log", "domain": [1, upper], "nice": False}
        x["axis"]["values"] = [tick for tick in [1, 2, 5, 10, 20, 50, 100, 200] if tick <= upper]
        layer["encoding"]["y"]["title"] = "Workloads"
    return spec, {
        "treatment": treatment,
        "label": label,
        "workloads": len(points),
        "observations_per_endpoint": 10,
        "quantiles": quantiles,
        "maximum": ratios[-1],
        "points": points,
    }


left, extraction = panel("proof-extraction", "(a) Recording + extraction", 20)
right, checking = panel("proof-testing", "(b) Recording + extraction + checking", 250)
spec = {
    "$schema": "https://vega.github.io/schema/vega-lite/v6.json",
    "hconcat": [left, right],
    "spacing": 24,
    "resolve": {"scale": {"color": "shared", "x": "independent", "y": "shared"}, "legend": {"color": "shared"}},
    "config": copy.deepcopy(selected["spec_template"]["config"]),
    "usermeta": {
        "population": 486,
        "observations_per_endpoint": 10,
        "baseline_treatment": "off",
        "source_git_sha": selected["source_git_sha"],
        "binary_sha256": selected["binary_sha256"],
        "threads": 1,
        "quantile_method": "inverse empirical CDF",
        "population_confidence_band": False,
        "scale": (
            "Both horizontal axes are logarithmic; panel ranges differ to preserve central detail and the strict tail."
        ),
        "mode_boundaries": selected["mode_boundaries"],
    },
}
result = {
    "kind": "corpus-proof-stages-cdf-v1",
    "baseline_treatment": "off",
    "source_git_sha": selected["source_git_sha"],
    "binary_sha256": selected["binary_sha256"],
    "threads": 1,
    "timeout_sec": selected["timeout_sec"],
    "memory_limit_bytes": selected["memory_limit_bytes"],
    "population": 486,
    "observations_per_endpoint": 10,
    "panels": [extraction, checking],
    "statistics": (
        "Ratio of independent ten-run arithmetic endpoint means per input; equal input weights. "
        "Inverse empirical CDF ranks ceil(q*486); no paired trials, population intervals or new certificate totals."
    ),
    "mode_boundaries": selected["mode_boundaries"],
    "provenance": selected["provenance"],
    "selected_payload": source.name,
    "selected_payload_sha256": "sha256:" + hashlib.sha256(source.read_bytes()).hexdigest(),
    "exporter": Path(__file__).name,
    "exporter_sha256": "sha256:" + hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
}
for name, value in [
    ("corpus-proof-stages-cdf.bound.vl.json.gz", spec),
    ("corpus-proof-stages-cdf.results.json.gz", result),
]:
    (root / name).write_bytes(gzip.compress((json.dumps(value, ensure_ascii=False) + "\n").encode(), mtime=0))
numbers = (
    "\\providecommand{\\EgglogFigureNumber}[1]{\\ifcsname egglogfigure@#1\\endcsname"
    "\\csname egglogfigure@#1\\endcsname\\else\\textnormal{unavailable}\\fi}\n"
)
for key, value in [
    ("inputs", 486),
    ("observations-per-endpoint", 10),
    ("extraction/p50", extraction["quantiles"]["0.5"]),
    ("extraction/p95", extraction["quantiles"]["0.95"]),
    ("checking/p50", checking["quantiles"]["0.5"]),
    ("checking/p95", checking["quantiles"]["0.95"]),
    ("checking/max", checking["maximum"]),
]:
    numbers += (
        "\\expandafter\\def\\csname egglogfigure@corpus-proof-stages-cdf/" + key + "\\endcsname{" + str(value) + "}\n"
    )
(root / "corpus-proof-stages-cdf.numbers.tex").write_text(numbers)
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
                str(root / "corpus-proof-stages-cdf.pdf"),
            ],
            check=True,
        )
print(json.dumps({p["treatment"]: {"quantiles": p["quantiles"], "max": p["maximum"]} for p in result["panels"]}))
