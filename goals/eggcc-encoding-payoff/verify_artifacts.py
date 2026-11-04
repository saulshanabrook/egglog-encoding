"""Verify published study files and lossless compression without running experiments."""

from __future__ import annotations

import gzip
import hashlib
import json
import re
from pathlib import Path
from urllib.parse import unquote

here = Path(__file__).resolve().parent
root = here.parents[1]
manifest = json.loads((here / "sharing-manifest.json").read_text())

for entry in manifest["files"]:
    path = (root / entry["path"]).resolve()
    if not path.is_relative_to(root):
        raise SystemExit(f"Artifact escapes the checkout: {entry['path']}")
    with path.open("rb") as stream:
        digest = hashlib.file_digest(stream, "sha256").hexdigest()
    if digest != entry["sha256"] or path.stat().st_size != entry["bytes"]:
        raise SystemExit(f"Published artifact differs: {entry['path']}")
    if entry["gzip"]:
        original = hashlib.sha256()
        size = 0
        with gzip.open(path, "rb") as stream:
            while chunk := stream.read(1024 * 1024):
                original.update(chunk)
                size += len(chunk)
        if original.hexdigest() != entry["source_sha256"] or size != entry["source_bytes"]:
            raise SystemExit(f"Decompressed artifact differs: {entry['path']}")

links_checked = 0
for name in ["README.md", "report.md", "reference.md", "reproduce.md"]:
    document = here / name
    text = re.sub(r"(?ms)^```.*?^```\s*$", "", document.read_text())
    for link in re.findall(r"\[[^\]]*\]\(([^\s)]+)(?:\s+[^)]*)?\)", text):
        target = unquote(link.strip("<>").split("#", 1)[0])
        if not target or re.match(r"^\w+://", target) or target.startswith("mailto:"):
            continue
        if not (document.parent / target).exists():
            raise SystemExit(f"Missing link in {name}: {target}")
        links_checked += 1

print(f"Verified {len(manifest['files'])} artifacts and {links_checked} entry-point links.")
