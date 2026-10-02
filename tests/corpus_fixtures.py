"""Build small prepared manifests with real content identities for runner tests."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from benchmarking.suites import MANIFEST_RELATIVE_PATH
from benchmarking.targets import sha256_file


def prepare_corpus(root: Path, *, contents: tuple[str, ...] = ("(check (= 1 1))\n",), family: str = "eggcc") -> Path:
    path = root / MANIFEST_RELATIVE_PATH
    path.parent.mkdir(parents=True, exist_ok=True)
    cases: list[dict[str, Any]] = []
    workloads: list[dict[str, Any]] = []
    for order, source in enumerate(contents):
        file = path.parent / "workloads" / f"case-{order}.egg"
        file.parent.mkdir(exist_ok=True)
        file.write_text(source)
        name = file.relative_to(path.parent).as_posix()
        cases.append(
            {
                "id": f"case-{order}",
                "family": family,
                "source": f"author/{order}",
                "status": "ready",
                "workloads": [name],
            }
        )
        workloads.append(
            {
                "file": name,
                "sha256": sha256_file(file),
                "facts_sha256": "",
                "aliases": [{"case": f"case-{order}", "order": 0}],
                "adaptations": [],
            }
        )
    path.write_text(
        json.dumps(
            {
                "sources": {family: {"repository": "author", "revision": "pinned"}},
                "cases": cases,
                "workloads": workloads,
                "outcomes": [],
            }
        )
    )
    return path
