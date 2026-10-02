"""Expand the checked-in source recipes into the intended paper population."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
FAMILIES = ("math-growth", "luminal", "eggcc", "hardboiled", "misaal", "churchroad", "dialegg")


def dialegg_configurations(recipe: dict[str, Any]) -> dict[str, dict[str, Any]]:
    """Expand each declared paper pass sequence and input into a source invocation."""
    return {
        **{
            f"dialegg-runtime-{name}-{label}": {
                "input": f"bench/{name}/{name}.mlir",
                "template": f"bench/{name}/{name}.egg",
                "passes": passes,
                "population": "paper-runtime",
            }
            for name in recipe["runtime_programs"]
            for label, passes in recipe["runtime_passes"].items()
        },
        **{
            f"dialegg-timer-{name}": {
                "input": f"test/{name}/{name}.mlir",
                "template": f"test/{name}/{name}.egg",
                "passes": ["--eq-sat"],
                "population": "paper-timer",
            }
            for name in recipe["timer_programs"]
        },
        **{
            f"dialegg-timer-nmm-{size}": {
                "input": f"test/nmm/{size}mm.mlir",
                "template": "test/nmm/nmm.egg",
                "passes": ["--eq-sat"],
                "population": "paper-timer",
            }
            for size in recipe["timer_nmm"]
        },
        **{
            f"dialegg-extra-nmm-{size}": {
                "input": f"bench/nmm/{size}mm.mlir",
                "template": "bench/nmm/nmm.egg",
                "passes": ["--eq-sat"],
                "population": "artifact-extra",
            }
            for size in recipe["artifact_extra_nmm"]
        },
    }


def expected_cases(sources: dict[str, Any] | None = None) -> list[dict[str, Any]]:
    """Derive stable source identities before generation, never from successes."""
    sources = sources or json.loads((ROOT / "benchmarks/sources.json").read_text())
    cases: list[dict[str, Any]] = []
    for family in FAMILIES:
        recipe = sources[family]
        if family == "math-growth":
            cases.append({"id": "math-growth-011", "family": family, "source": recipe["input"]})
        elif family == "luminal":
            cases.extend({"id": "luminal-" + Path(p).stem, "family": family, "source": p} for p in recipe["inputs"])
        elif family == "hardboiled":
            cases.extend(
                {
                    "id": row["id"],
                    "family": family,
                    "source": "benchmarks/hardboiled/" + row["file"],
                    "input_kind": recipe["input_kind"],
                }
                for row in recipe["inputs"]
            )
        elif family == "eggcc":
            for source in recipe["programs"]:
                fenwick = "fenwick" in source
                for config in recipe["configurations"]:
                    if config["scope"] == "fenwick" and not fenwick:
                        continue
                    if config["scope"] == "bril-polybench" and not any(
                        f"/{s}/" in source for s in ("bril", "polybench")
                    ):
                        continue
                    options = (
                        ["--with-context"] if fenwick and config["id"] == "statewalk" else config["native_options"]
                    )
                    cases.append(
                        {
                            "id": f"eggcc-{Path(source).stem}--{config['id']}",
                            "family": family,
                            "source": source,
                            "configuration": {"native_options": options},
                        }
                    )
        elif family == "misaal":
            for target, programs in recipe["programs"].items():
                for name in programs:
                    cases.append(
                        {
                            "id": f"misaal-{target}-{name}",
                            "family": family,
                            "source": f"benchmarks/{target}/halide/{name}",
                            "configuration": {"target": target},
                            "paper_aliases": [
                                r["paper"] for r in recipe["paper_rows"] if r["source_generator"] == name
                            ],
                        }
                    )
        elif family == "churchroad":
            cases.extend({"id": "churchroad-" + Path(p).stem, "family": family, "source": p} for p in recipe["inputs"])
            later = recipe["later_evaluation"]
            cases.extend(
                {
                    "id": "churchroad-later-" + Path(p).stem,
                    "family": family,
                    "source": p,
                    "source_set": "later_evaluation",
                    "configuration": {"top_module_name": Path(p).stem, "architecture": "xilinx-ultrascale-plus"},
                }
                for p in later["sources"]
            )
        else:
            cases.extend(
                {"id": key, "family": family, "source": config["input"], "configuration": {"passes": config["passes"]}}
                for key, config in dialegg_configurations(recipe).items()
            )
    for case in cases:
        case.setdefault("configuration", {})
    ids = [case["id"] for case in cases]
    if len(ids) != len(set(ids)):
        raise ValueError("source recipes have duplicate case identities")
    return cases


def select_cases(cases: list[dict[str, Any]], families: list[str], names: list[str]) -> list[dict[str, Any]]:
    """Select in recipe order; include all recorded artifact extras by default."""
    if set(families) - set(FAMILIES):
        raise ValueError("unknown reproduction family")
    selected = [case for case in cases if case["family"] in families]
    if set(names) - {case["id"] for case in selected}:
        raise ValueError("unknown case in selected families")
    return [case for case in selected if not names or case["id"] in names]
