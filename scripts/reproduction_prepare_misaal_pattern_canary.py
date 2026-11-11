"""Create an immutable, cold-cache HVX blur3x3 deduplication canary request."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

from scripts.misaal_reproduction import verified_request
from scripts.reproduction_misaal_patterns import CONTRACT

ROOT = Path(__file__).resolve().parents[1]
CASE = "misaal-hexagon-blur3x3"


def prepare_pattern_canary(settings_path: Path, output: Path, *, root: Path = ROOT) -> dict[str, Any]:
    """Change only the request flag, retaining original bytes and identity bindings.

    This performs read-only prerequisite verification and writes new JSON files.
    It neither imports pattern populations nor executes a source/compiler job.
    """
    settings_path = settings_path.resolve()
    output = output.resolve()
    if output.exists():
        raise FileExistsError(f"Canary output must be a new directory: {output}")
    settings_bytes = settings_path.read_bytes()
    settings = json.loads(settings_bytes)["misaal"]
    request_path = (root / settings["paths"]["requests"] / f"{CASE}.json").resolve()
    request_bytes = request_path.read_bytes()
    request = verified_request(request_path)
    if (
        request["case_id"] != CASE
        or request["source"] != "benchmarks/hexagon/halide/blur3x3"
        or request["configuration"] != {"target": "hexagon"}
        or request["revision"] != "44ff893445d664cd87f52b08a138260ed2015ba8"
        or settings["revision"] != request["revision"]
        or request.get("pattern_cache_contract", {}).get("environment") != "MISAAL_PATTERN_CACHE_DIR"
        or "MISAAL_PATTERN_CACHE_DIR" in request["environment"]
        or "pattern_deduplication" in request
    ):
        raise ValueError("Expected the original unflagged, cold-cache HVX blur3x3 request")
    if request != json.loads(request_bytes) or settings_bytes != settings_path.read_bytes():
        raise ValueError("Original canary inputs changed during verification")
    if list((Path(request["checkout"]) / "lib/patterns").glob("*.pickle")):
        raise ValueError("Prepared checkout must retain the original empty-cache precondition")

    request["pattern_deduplication"] = CONTRACT
    request_text = json.dumps(request, indent=2) + "\n"
    output.mkdir(parents=True, exist_ok=False)
    requests = output / "requests"
    requests.mkdir()
    (output / "original-request.json").write_bytes(request_bytes)
    (output / "original-settings.json").write_bytes(settings_bytes)
    (requests / f"{CASE}.json").write_text(request_text)
    provenance = {
        "case_id": CASE,
        "request_change": {"pattern_deduplication": CONTRACT},
        "source_request": {"path": str(request_path), "sha256": hashlib.sha256(request_bytes).hexdigest()},
        "source_settings": {"path": str(settings_path), "sha256": hashlib.sha256(settings_bytes).hexdigest()},
        "request_sha256": hashlib.sha256(request_text.encode()).hexdigest(),
        "preparer_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "cache_behavior": "unchanged fresh empty per-parent cache; no cache copied or created",
        "native_execution": False,
    }
    provenance_path = output / "provenance.json"
    provenance_path.write_text(json.dumps(provenance, indent=2) + "\n")
    settings["paths"]["requests"] = str(requests)
    settings["identity_paths"] = [*settings.get("identity_paths", []), str(provenance_path)]
    settings_file = output / "settings.json"
    settings_file.write_text(json.dumps({"misaal": settings}, indent=2) + "\n")
    receipt = {
        "status": "request-prepared",
        "case_id": CASE,
        "settings": str(settings_file),
        "native_execution": False,
        "artifacts": {
            str(path.relative_to(output)): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in sorted(output.rglob("*.json"))
        },
        "command": [
            str(root / ".venv/bin/python"),
            "-m",
            "scripts.suite_reproduction",
            "--family",
            "misaal",
            "--case",
            CASE,
            "--stage",
            "all",
            "--settings",
            str(settings_file),
        ],
        "cwd": str(root),
    }
    (output / "request-preparation.json").write_text(json.dumps(receipt, indent=2) + "\n")
    return receipt


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--settings", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--root", type=Path, default=ROOT)
    args = parser.parse_args()
    print(json.dumps(prepare_pattern_canary(args.settings, args.output, root=args.root.resolve()), indent=2))


if __name__ == "__main__":
    main()
