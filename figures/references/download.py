"""Restore or verify the public lecture PDFs pinned by manifest.json."""

from __future__ import annotations

import argparse
import hashlib
import json
import urllib.request
from pathlib import Path


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verify-only", action="store_true", help="check local files without network access")
    args = parser.parse_args()
    directory = Path(__file__).resolve().parent
    manifest = json.loads((directory / "manifest.json").read_text())
    total_bytes = 0
    for deck in manifest["decks"]:
        path = directory / deck["local_path"]
        if path.exists():
            data = path.read_bytes()
        elif args.verify_only:
            raise SystemExit(f"Missing {path}; rerun without --verify-only to download it")
        else:
            request = urllib.request.Request(
                deck["url"], headers={"User-Agent": "egglog-encoding-reference-archive/1.0"}
            )
            with urllib.request.urlopen(request, timeout=120) as response:
                data = response.read()
        if not data.startswith(b"%PDF-") or hashlib.sha256(data).hexdigest() != deck["sha256"]:
            raise SystemExit(f"PDF/hash mismatch for {deck['url']}; keep the pinned manifest and inspect the source")
        if not path.exists():
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
        total_bytes += len(data)
        print(f"Verified {deck['local_path']}")
    print(f"Verified {len(manifest['decks'])} decks ({total_bytes:,} bytes)")


if __name__ == "__main__":
    main()
