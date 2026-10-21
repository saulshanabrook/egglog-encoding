"""Collect checked-in paper inputs and project their figure metadata."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import tempfile
from collections.abc import Sequence
from pathlib import Path
from typing import NotRequired, TypedDict, cast

from benchmarking import benchmark
from benchmarking.engines import MATH_WORKLOAD_SHA256

ROOT = Path(__file__).resolve().parents[1]


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
    iteration: int | None
    file_sha256: str
    fact_directory_sha256: str
    unavailable_reason: str
    validation_failures: dict[str, str]


class FigureInventory(TypedDict):
    id: int
    timeout_sec: int
    workloads: list[FigureWorkload]


def load_corpus(root: Path) -> Corpus:
    """Require the portable manifest's unique identities to match its actual inputs."""

    directory = root / "benchmarks/corpus"
    corpus = cast(Corpus, json.loads((directory / "manifest.json").read_text()))
    identities: set[tuple[str, str]] = set()
    for item in corpus["workloads"]:
        path = (directory / item["file"]).resolve()
        if not path.is_relative_to(directory.resolve()):
            raise ValueError(f"corpus path leaves its directory: {item['file']}")
        actual = "sha256:" + hashlib.sha256(path.read_bytes()).hexdigest()
        if actual != item["sha256"]:
            raise ValueError(f"corpus input changed: {item['file']}; review its manifest before collection")
        # The published corpus has self-contained inputs, with no external facts.
        if item.get("facts") or item["facts_sha256"]:
            raise ValueError(f"paper collection requires self-contained facts: {item['file']}")
        identity = (actual, item["facts_sha256"])
        if identity in identities:
            raise ValueError(f"duplicate corpus identity: {item['file']}; retain aliases in the manifest")
        identities.add(identity)
    if not identities:
        raise ValueError("paper corpus contains no workloads")
    return corpus


def collect(root: Path, comparison: str, rounds: int, timeout_sec: int, report: Path) -> int:
    """Run the three ordinary comparisons serially, sharing all compatible off rows."""

    corpus = load_corpus(root)
    files = [str(root / "benchmarks/corpus" / item["file"]) for item in corpus["workloads"]]
    comparisons = (
        ("recording", files, "proofs", "off"),
        ("checked", files, "proof-testing", "off"),
        (
            "math",
            [
                str(root / "benchmarks/corpus" / item["file"])
                for item in corpus["workloads"]
                if item["sha256"] == MATH_WORKLOAD_SHA256
            ],
            "egg-proof-testing",
            "egg",
        ),
    )
    for name, selected, treatment, baseline in comparisons:
        if comparison not in ("all", name):
            continue
        if not selected:
            raise ValueError("the fixed Math11 input is missing from the paper corpus")
        result = benchmark.main(
            [
                *selected,
                "--target",
                f"figures={root}",
                "--treatment",
                treatment,
                "--compare-treatment",
                baseline,
                "--rounds",
                str(rounds),
                "--timeout-sec",
                str(timeout_sec),
                "--report",
                str(report),
            ]
        )
        if result:
            return result
    return 0


def figure_inventory(root: Path, timeout_sec: int) -> FigureInventory:
    """Project only metadata consumed by Vega; retain exact strict failures and blockers."""

    corpus = load_corpus(root)
    cases = {case["id"]: case for case in corpus["cases"]}
    workloads: dict[tuple[str, str], FigureWorkload] = {}
    for source in corpus["workloads"]:
        first = source["aliases"][0]
        case = cases[first["case"]]
        identity = (source["sha256"], source["facts_sha256"])
        workloads[identity] = {
            "id": "/".join(identity),
            "label": case["id"] + (f" / call {first['order'] + 1}" if len(case["workloads"]) > 1 else ""),
            "family": case["family"],
            "iteration": 11 if source["sha256"] == MATH_WORKLOAD_SHA256 else None,
            "file_sha256": source["sha256"],
            "fact_directory_sha256": source["facts_sha256"],
            "unavailable_reason": "",
            "validation_failures": {},
        }
    for case in corpus["cases"]:
        if case["status"] in ("blocked", "pending"):
            workloads[(case["id"], "")] = {
                "id": case["id"],
                "label": case["id"],
                "family": case["family"],
                "iteration": None,
                "file_sha256": "",
                "fact_directory_sha256": "",
                "unavailable_reason": case["reason"] or "Replay unavailable",
                "validation_failures": {},
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
    return {"id": 1, "timeout_sec": timeout_sec, "workloads": list(workloads.values())}


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("collect", "inventory"))
    parser.add_argument("--comparison", choices=("all", "recording", "checked", "math"), default="all")
    parser.add_argument("--rounds", type=int, default=5)
    parser.add_argument("--timeout-sec", type=int, default=300)
    parser.add_argument("--report", type=Path, default=ROOT / ".reports.jsonl")
    parser.add_argument("--output", type=Path, default=ROOT / "benchmarks/local/figure-inventory.json")
    args = parser.parse_args(argv)
    if args.rounds < 1 or args.timeout_sec < 1:
        parser.error("rounds and timeout must be positive")
    if args.command == "collect":
        return collect(ROOT, args.comparison, args.rounds, args.timeout_sec, args.report)
    encoded = json.dumps(figure_inventory(ROOT, args.timeout_sec), separators=(",", ":")).encode() + b"\n"
    if args.output.is_file() and args.output.read_bytes() == encoded:
        return 0
    args.output.parent.mkdir(parents=True, exist_ok=True)
    temporary: Path | None = None
    try:
        with tempfile.NamedTemporaryFile(dir=args.output.parent, delete=False) as handle:
            temporary = Path(handle.name)
            handle.write(encoded)
        os.replace(temporary, args.output)
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
