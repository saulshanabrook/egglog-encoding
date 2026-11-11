"""Read the pinned LMFAO frontend export; categorical features are grouping keys."""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any

FIXTURES = Path(__file__).resolve().parents[2] / "benchmarks/lmfao"
COMMIT = "df6a5f59d597e9d7dd5984f268700223553789d0"


@dataclass(frozen=True)
class Query:
    groups: tuple[str, ...] = ()
    factors: tuple[str, ...] = ()


class Workload:
    def __init__(self, document: dict[str, Any]) -> None:
        self.document = document
        self.attributes = [(a["name"], a["type"]) for a in document["attributes"]]
        names = [a for a, _ in self.attributes]
        relations = document["relations"]
        self.relations = {r["name"]: [names[int(a)] for a in r["attributes"]] for r in relations}
        self.edges = [
            (r["name"], relations[int(n)]["name"])
            for i, r in enumerate(relations)
            for n in r["neighbors"]
            if i < int(n)
        ]
        self.root = relations[int(document["root"])]["name"]
        self.functions = [(names[int(f["attributes"][0])], int(f["power"])) for f in document["functions"]]
        self.queries = [
            Query(
                tuple(names[int(a)] for a in q["keys"]),
                tuple(name for f in q["functions"] for name, power in [self.functions[int(f)]] for _ in range(power)),
            )
            for q in document["queries"]
        ]

    @classmethod
    def read(cls, path: Path) -> Workload:
        return cls(json.loads(path.read_text()))


WORKLOAD = Workload.read(FIXTURES / "workload.json")


def read_plan(path: Path) -> dict[str, Any]:
    """Normalize Boost property_tree's string scalars and empty arrays."""
    plan = json.loads(path.read_text())
    return {
        "views": [
            {
                "origin": int(v["origin"]),
                "destination": int(v["destination"]),
                "keys": list(map(int, v["keys"])),
                "aggregates": [
                    {
                        "functions": list(map(int, a["functions"])),
                        "incoming": [list(map(int, e)) for e in a["incoming"]],
                    }
                    for a in v["aggregates"]
                ],
            }
            for v in plan["views"]
        ],
        "outputs": [{k: int(v) for k, v in o.items()} for o in plan["outputs"]],
    }


def ident(name: str) -> str:
    return '"' + name.replace('"', '""') + '"'
