"""Acquire exact HardBoiled sources and omit only statically unscheduled higher-order rules."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any

from scripts.hardboiled_replay import egglog_forms

ROOT = Path(__file__).resolve().parents[1]
INPUT_KIND = "author-published-egglog"
REPOSITORY = "https://github.com/yihozhang/egglog-benchmarks"
REVISION = "da432767a04c1803dc7edb5a9f653d90c0fbe623"


def published_entries(manifest: dict[str, Any] | None = None) -> dict[str, dict[str, Any]]:
    """Bind this source recipe to the selected revision and all 42 unique files."""
    if manifest is None:
        manifest = json.loads((ROOT / "benchmarks/sources.json").read_text())["hardboiled"]
    if (
        manifest.get("input_kind") != INPUT_KIND
        or manifest.get("repository") != REPOSITORY
        or manifest.get("revision") != REVISION
    ):
        raise ValueError("published HardBoiled source manifest differs from the selected recipe")
    entries = {row["id"]: row for row in manifest["inputs"]}
    names = (
        {f"conv1d_{size}.egg" for size in range(8, 257, 8)}
        | {f"{name}_{size}.egg" for name in ("conv2d", "downsample", "upsample") for size in (16, 32)}
        | {"matmul.egg", "denoise.egg", "rec_filter.egg", "resize.egg"}
    )
    if len(entries) != 42 or len(manifest["inputs"]) != 42 or {row["file"] for row in entries.values()} != names:
        raise ValueError("published HardBoiled manifest must retain exactly the 42 selected inputs")
    if any(row["id"] != "hardboiled-published-" + Path(row["file"]).stem for row in entries.values()):
        raise ValueError("published HardBoiled case names differ from their source files")
    return entries


def verify_input(entry: dict[str, Any], data: bytes) -> None:
    """Require exact Git/SHA bytes and the retained original extraction queries."""
    blob = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
    if (
        len(data) != entry["size_bytes"]
        or hashlib.sha256(data).hexdigest() != entry["sha256"]
        or blob != entry["git_blob"]
    ):
        raise ValueError(f"published input identity changed: {entry['file']}")
    forms = [tokens for _, _, tokens in egglog_forms(data.decode())]
    if any(tokens[1] in {"include", "input", "output", "prove", "prove-extract"} for tokens in forms):
        raise ValueError("published input must be a self-contained ordinary Egglog program")
    extracts = sum(tokens[1] == "extract" for tokens in forms)
    if not extracts or extracts != entry["extracts"]:
        raise ValueError("published input lost its original extraction queries")
