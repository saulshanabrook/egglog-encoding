"""Project published corpus metadata without collecting or regenerating inputs."""

from __future__ import annotations

import json
from collections.abc import Sequence
from pathlib import Path
from typing import NotRequired, TypedDict, cast

from benchmarking.models import FileSpec


class Alias(TypedDict):
    case: str
    order: int


class Input(TypedDict):
    file: str
    sha256: str
    facts_sha256: str
    aliases: list[Alias]
    facts: NotRequired[str | None]


class Case(TypedDict):
    id: str
    family: str
    status: str
    workloads: list[str]
    reason: str | None


class Corpus(TypedDict):
    cases: list[Case]
    workloads: list[Input]


class Validation(TypedDict):
    file_sha256: str
    fact_directory_sha256: str
    binary_sha256: str
    timeout_sec: int
    disequality_encoding: str
    kind: str
    policy: str
    status: str
    reason: str | None


class FigureWorkload(TypedDict):
    id: str
    label: str
    family: str
    file_sha256: str
    fact_directory_sha256: str
    unavailable_reason: str
    validation_failures: dict[str, str]
    aliases: list[Alias]


class FigureInventory(TypedDict):
    id: int
    timeout_sec: int
    workloads: list[FigureWorkload]
    unavailable_cases: list[Case]


def figure_inventory(root: Path, timeout_sec: int, selected: Sequence[FileSpec] | None = None) -> FigureInventory:
    """Project only metadata consumed by Vega; retain exact strict failures and blockers."""

    directory = (root / "benchmarks/corpus").resolve()
    published = (
        None if selected is None else [file for file in selected if file.absolute_path.is_relative_to(directory)]
    )
    if published == []:
        return {"id": 1, "timeout_sec": timeout_sec, "workloads": [], "unavailable_cases": []}
    # Figure selection has already hashed its files. Do not inspect unrelated
    # prepared inputs when a custom configuration selects a small subset.
    corpus = cast(Corpus, json.loads((directory / "manifest.json").read_text()))
    identities = None if published is None else {(file.sha256, file.fact_directory_sha256) for file in published}
    registered = {
        (directory / item["file"]).resolve(): (item["sha256"], item["facts_sha256"]) for item in corpus["workloads"]
    }
    if published is not None and any(
        registered.get(file.absolute_path) != (file.sha256, file.fact_directory_sha256) for file in published
    ):
        raise ValueError("selected published corpus input changed or is unregistered; review its manifest")
    cases = {case["id"]: case for case in corpus["cases"]}
    workloads: dict[tuple[str, str], FigureWorkload] = {}
    for source in corpus["workloads"]:
        if identities is not None and (source["sha256"], source["facts_sha256"]) not in identities:
            continue
        first = source["aliases"][0]
        case = cases[first["case"]]
        identity = (source["sha256"], source["facts_sha256"])
        workloads[identity] = {
            "id": "/".join(identity),
            "label": case["id"] + (f" / call {first['order'] + 1}" if len(case["workloads"]) > 1 else ""),
            "family": case["family"],
            "file_sha256": source["sha256"],
            "fact_directory_sha256": source["facts_sha256"],
            "unavailable_reason": "",
            "validation_failures": {},
            "aliases": source["aliases"],
        }
    outcomes = root / "benchmarks/corpus/.local/outcomes.json"
    if outcomes.is_file():
        for outcome in cast(list[Validation], json.loads(outcomes.read_text())):
            item = workloads.get((outcome["file_sha256"], outcome["fact_directory_sha256"]))
            if (
                item is None
                or outcome["kind"] != "validation"
                or outcome["policy"] != "proof-testing-v1"
                or outcome["timeout_sec"] != timeout_sec
            ):
                continue
            key = f"{outcome['binary_sha256']}/{timeout_sec}/{outcome['disequality_encoding']}"
            if outcome["status"] == "success":
                item["validation_failures"].pop(key, None)
            else:
                item["validation_failures"][key] = outcome["reason"] or "Strict proof validation failed"
    return {
        "id": 1,
        "timeout_sec": timeout_sec,
        "workloads": list(workloads.values()),
        "unavailable_cases": [case for case in corpus["cases"] if case["status"] in ("blocked", "pending")],
    }
