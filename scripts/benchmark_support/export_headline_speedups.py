#!/usr/bin/env python3
"""Generate headline number macros from public selected paper figure results.

Speedups divide native means by serial means on each fixed workload suite.
No observations are collected, and four-worker results are never used here.
"""

import argparse
import gzip
import hashlib
import json
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--figures-dir", type=Path, required=True)
parser.add_argument("--output", type=Path, required=True)
args = parser.parse_args()
math_path = args.figures_dir / "math-checked-unsimplified.results.json.gz"
suites_path = args.figures_dir / "integrated-runtime-means.results.json.gz"
corpus_path = args.figures_dir / "corpus-congruence-cdf.selected.json.gz"
math_result = json.loads(gzip.decompress(math_path.read_bytes()))
suites = {row["experiment"]: row for row in json.loads(gzip.decompress(suites_path.read_bytes()))}
corpus = json.loads(gzip.decompress(corpus_path.read_bytes()))
assert math_result["native_treatment"] == "egg-proof-testing"
assert math_result["ours_treatment"] == "proof-testing-unsimplified"
math_means = math_result["means_seconds"]
values = {
    "headline/math-checked-speedup": f"{math_means['native'] / math_means['ours_one_worker']:.2f}",
    "headline/disequality-speedup": (
        f"{suites['disequality']['reference']['mean'] / suites['disequality']['ours']['mean']:.2f}"
    ),
    "headline/slotted-restricted-speedup": (
        f"{suites['slotted']['reference']['mean'] / suites['slotted']['ours']['mean']:.2f}"
    ),
    "headline/corpus-project-count": str(len(corpus["project_labels"])),
}
assert {point["project"] for point in corpus["points"]} == set(corpus["project_labels"])
tex = (
    r"\providecommand{\EgglogFigureNumber}[1]{\ifcsname egglogfigure@#1\endcsname"
    r"\csname egglogfigure@#1\endcsname\else\textnormal{unavailable}\fi}"
    "\n"
)
for path in (math_path, suites_path, corpus_path):
    tex += f"% Source: {path.name}; SHA-256: {hashlib.sha256(path.read_bytes()).hexdigest()}\n"
for key, value in values.items():
    tex += r"\expandafter\def\csname egglogfigure@" + key + r"\endcsname{" + value + "}\n"
args.output.parent.mkdir(parents=True, exist_ok=True)
args.output.write_text(tex)
print(json.dumps(values))
