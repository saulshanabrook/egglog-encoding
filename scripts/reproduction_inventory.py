"""Expand source programs into paper-associated native optimization requests."""

from __future__ import annotations

from collections.abc import Mapping, Sequence
from pathlib import Path
from typing import Any

from scripts.reproduction_published import INPUT_KIND, published_entries

FAMILIES = ("eggcc", "hardboiled", "misaal", "churchroad", "dialegg", "speq")


def expected_cases(catalog: Mapping[str, Any], population: Mapping[str, Any]) -> list[dict[str, Any]]:
    """Account for required parents and extras independently of capture success.

    Output requests refer back to the catalog's sources rather than importing
    historical capture/validation status. Runtime aliases remain aliases.
    """
    cases: list[dict[str, Any]] = []
    later = population["churchroad"]["later_evaluation"]
    later_ids = {f"churchroad-later-{Path(source).stem}" for source in later["sources"]}
    published = population.get("hardboiled", {})
    if published.get("input_kind") == INPUT_KIND:
        for entry in published_entries(published).values():
            cases.append(
                {
                    "id": entry["id"],
                    "family": "hardboiled",
                    "input_kind": INPUT_KIND,
                    "source": "benchmarks/hardboiled/" + entry["file"],
                    "configuration": {
                        "input_kind": INPUT_KIND,
                        "repository": published["repository"],
                        "revision": published["source_revision"],
                        "git_blob": entry["git_blob"],
                    },
                    "scope": "required",
                    "paper_aliases": [],
                }
            )
    for source in catalog["cases"]:
        family = source["family"]
        if family not in FAMILIES or family == "dialegg":
            continue
        if family == "hardboiled" and published.get("input_kind") == INPUT_KIND:
            continue
        if family == "churchroad" and source["id"] in later_ids:
            # Published extras still come from the separate evaluation roster.
            continue
        base = {
            "id": source["id"],
            "family": family,
            "catalog_id": source["id"],
            "source": source["source"],
            "configuration": source.get("configuration", {}),
            "scope": "required",
            "paper_aliases": [],
        }
        if family == "eggcc":
            for config in population[family]["configurations"]:
                fenwick = "fenwick" in source["source"]
                if config["scope"] == "fenwick" and not fenwick:
                    continue
                if config["scope"] == "bril-polybench" and not any(
                    f"/{group}/" in source["source"] for group in ("bril", "polybench")
                ):
                    continue
                options = config["native_options"]
                if fenwick and config["id"] == "statewalk":
                    options = ["--with-context"]
                cases.append(
                    {
                        **base,
                        "id": f"{source['id']}--{config['id']}",
                        "configuration": {"native_options": options, "passes": "complete-native-schedule"},
                    }
                )
            continue
        if family == "misaal":
            generator = Path(source["source"]).name
            aliases = [r["paper"] for r in population[family]["paper_rows"] if r["source_generator"] == generator]
            base.update(paper_aliases=aliases, scope="required" if aliases else "artifact-extra")
        elif family == "hardboiled" and source["id"] in population[family]["artifact_extras"]:
            base["scope"] = "artifact-extra"
        elif family == "churchroad" and source["id"] == population[family]["paper_example_alias"]:
            base["paper_aliases"] = ["WOSET 2024 section II: unsigned 16x32 to 32 multiply"]
        cases.append(base)
    dialegg = population["dialegg"]
    for name in dialegg["runtime_programs"]:
        for label, passes in dialegg["runtime_passes"].items():
            cases.append(
                {
                    "id": f"dialegg-runtime-{name}-{label}",
                    "family": "dialegg",
                    "catalog_id": f"dialegg-{name}",
                    "source": f"bench/{name}/{name}.mlir",
                    "configuration": {"passes": passes},
                    "scope": "required",
                    "paper_aliases": [f"Figure 3 {name} {label}"],
                }
            )
    for name in dialegg["runtime_programs"][:3]:
        cases.append(
            {
                "id": f"dialegg-timer-{name}",
                "family": "dialegg",
                "catalog_id": f"dialegg-{name}",
                "source": f"test/{name}/{name}.mlir",
                "configuration": {"passes": ["--eq-sat"]},
                "scope": "required",
                "paper_aliases": [f"Table 2 {name}"],
            }
        )
    for size in (*dialegg["timer_nmm"], *dialegg["artifact_extra_nmm"]):
        extra = size in dialegg["artifact_extra_nmm"]
        cases.append(
            {
                "id": f"dialegg-{'extra' if extra else 'timer'}-nmm-{size}",
                "family": "dialegg",
                "catalog_id": f"dialegg-{str(size) + 'mm' if size in (2, 3) else 'nmm-' + str(size)}",
                "source": f"{'bench' if extra else 'test'}/nmm/{size}mm.mlir",
                "configuration": {"passes": ["--eq-sat"]},
                "scope": "artifact-extra" if extra else "required",
                "paper_aliases": [] if extra else [f"Table 2 {size}MM"],
            }
        )
    for source in later["sources"]:
        cases.append(
            {
                "id": f"churchroad-later-{Path(source).stem}",
                "family": "churchroad",
                "source": source,
                "configuration": {
                    "repository": later["repository"],
                    "revision": later["revision"],
                    "top_module_name": Path(source).stem,
                    "architecture": "xilinx-ultrascale-plus",
                },
                "scope": "artifact-extra",
                "paper_aliases": [],
                "repository": later["repository"],
                "revision": later["revision"],
            }
        )
    ids = [case["id"] for case in cases]
    if len(ids) != len(set(ids)):
        raise ValueError("reproduction case IDs must be unique")
    return sorted(cases, key=lambda case: FAMILIES.index(case["family"]))


def select_cases(
    cases: Sequence[dict[str, Any]], families: Sequence[str], names: Sequence[str]
) -> list[dict[str, Any]]:
    """Keep catalog order; explicit case selectors may opt into inventoried extras."""
    if any(family not in FAMILIES for family in families):
        raise ValueError("unknown reproduction family")
    scoped = [case for case in cases if case["family"] in families]
    if names:
        missing = set(names) - {case["id"] for case in scoped}
        if missing:
            raise ValueError("unknown reproduction cases in requested families: " + ", ".join(sorted(missing)))
        return [case for case in scoped if case["id"] in names]
    return [case for case in scoped if case["scope"] == "required"]
