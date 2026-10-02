"""Acquire exact HardBoiled sources and omit only statically unscheduled higher-order rules."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any

from scripts.hardboiled_replay import egglog_forms, omit_unexecuted_higher_order_rules

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


def prepare_published(output: Path, engine: Path) -> dict[str, Any]:
    """Fetch each pinned raw file into a fresh destination without a native build."""
    from scripts.reproduction_prepare_misaal_racket import fetch_bytes

    output.mkdir()
    inputs = output / "inputs"
    inputs.mkdir()
    entries = published_entries()
    acquired = []
    for entry in entries.values():
        url = f"https://raw.githubusercontent.com/yihozhang/egglog-benchmarks/{REVISION}/benchmarks/hardboiled/{entry['file']}"
        data = fetch_bytes(url, entry["size_bytes"])
        verify_input(entry, data)
        (inputs / entry["file"]).write_bytes(data)
        acquired.append({**entry, "url": url})
    receipt = output / "published-inputs.json"
    receipt.write_text(
        json.dumps(
            {"input_kind": INPUT_KIND, "repository": REPOSITORY, "revision": REVISION, "inputs": acquired}, indent=2
        )
        + "\n"
    )
    settings = output / "settings.json"
    settings.write_text(
        json.dumps(
            {
                "hardboiled": {
                    "input_kind": INPUT_KIND,
                    "revision": REVISION,
                    "paths": {"inputs": str(inputs.resolve()), "egglog": str(engine.resolve())},
                    "identity_paths": [str(receipt.resolve())],
                }
            },
            indent=2,
        )
        + "\n"
    )
    return {"status": "success", "settings": str(settings), "input_kind": INPUT_KIND}


def capture_published(case: dict[str, Any], settings: dict[str, Any], output: Path) -> dict[str, Any]:
    """Retain exact published bytes separately from the guarded benchmark adaptation."""
    entry = published_entries()[case["id"]]
    if (
        case["family"] != "hardboiled"
        or case.get("input_kind") != INPUT_KIND
        or settings.get("input_kind") != INPUT_KIND
        or case["source"] != "benchmarks/hardboiled/" + entry["file"]
    ):
        raise ValueError("published input differs from the selected source case")
    data = (ROOT / settings["paths"]["inputs"] / entry["file"]).read_bytes()
    verify_input(entry, data)
    adapted = omit_unexecuted_higher_order_rules(data.decode()).encode()
    output.mkdir()
    source = output / "source" / entry["file"]
    source.parent.mkdir()
    source.write_bytes(data)
    replay = output / entry["file"]
    replay.write_bytes(adapted)
    return {
        "status": "ordinary-validation-pending",
        "family": "hardboiled",
        "case_id": case["id"],
        "input_kind": INPUT_KIND,
        "published_input": {"repository": REPOSITORY, "revision": REVISION, **entry},
        "published_source": str(source),
        "materialization": {"complete": True, "expected_sessions": 1, "materialized_sessions": 1},
        "sessions": [
            {
                "replay": str(replay),
                "replay_sha256": "sha256:" + hashlib.sha256(adapted).hexdigest(),
                "adaptations": ["omit-unexecuted-higher-order-rules"] if adapted != data else [],
                "output_contract": {"kind": INPUT_KIND, "extracts": entry["extracts"]},
            }
        ],
    }


def verify_published_capture(capture: dict[str, Any]) -> None:
    """Prevent a published-input label from admitting native prefixes or unpinned files."""
    entry = published_entries()[capture["case_id"]]
    if (
        capture.get("family") != "hardboiled"
        or capture.get("published_input") != {"repository": REPOSITORY, "revision": REVISION, **entry}
        or "source_completion" in capture
        or len(capture.get("sessions", [])) != 1
    ):
        raise ValueError("published acquisition provenance is incomplete or changed")
    session = capture["sessions"][0]
    if session.get("output_contract") != {"kind": INPUT_KIND, "extracts": entry["extracts"]}:
        raise ValueError("published extraction contract changed")
    data = Path(capture["published_source"]).read_bytes()
    verify_input(entry, data)
    adapted = omit_unexecuted_higher_order_rules(data.decode()).encode()
    if (
        session.get("adaptations") != (["omit-unexecuted-higher-order-rules"] if adapted != data else [])
        or session.get("replay_sha256") != "sha256:" + hashlib.sha256(adapted).hexdigest()
        or Path(session["replay"]).read_bytes() != adapted
    ):
        raise ValueError("published replay differs from the permitted unscheduled-rule adaptation")
