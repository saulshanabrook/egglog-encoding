#!/usr/bin/env python3
"""Reconstruct isolated sources from verified archives; never builds or runs EggCC."""
import argparse
import hashlib
import json
from pathlib import Path
import tarfile

BASE = Path(__file__).resolve().parent
PARTS = BASE.parent / "parts32-integration"
HOST = Path("/private/tmp/eggcc-pack32-candidate")
ENGINE = Path("/private/tmp/encoding-pack32-candidate")
BASES = [
    (HOST, "eggcc-parts32-candidate.tar", "7a886debd758e78d0e859a05bbac75084e7da9c4f4bd0d73321dcf6f5ad25c2a"),
    (ENGINE, "encoding-parts32-candidate.tar", "bf28b65f200123f5738326a069dad26d9d7004dd72ef89f9f4becd74f11cd82f"),
]


def admit():
    assert not HOST.exists() and not ENGINE.exists(), "Fresh candidate roots required"
    identities = json.loads((PARTS / "final-source-identities.json").read_text())
    overlay_hashes = {r["archive_path"]: r["sha256"] for r in identities["files"] if "archive_path" in r}
    for _, name, expected in BASES:
        with (PARTS / name).open("rb") as stream:
            assert hashlib.file_digest(stream, "sha256").hexdigest() == expected, name
    with tarfile.open(PARTS / "final-source.tar") as archive:
        members = archive.getmembers()
        assert {m.name for m in members if m.isfile()} == set(overlay_hashes)
        for member in members:
            assert member.isfile(), member.name
            data = archive.extractfile(member).read()
            assert hashlib.sha256(data).hexdigest() == overlay_hashes[member.name], member.name
    for target, name, _ in BASES:
        target.mkdir()
        with tarfile.open(PARTS / name) as archive:
            archive.extractall(target, filter="data")
    with tarfile.open(PARTS / "final-source.tar") as archive:
        for member in archive.getmembers():
            prefix, relative = member.name.split("/", 1)
            target = {"eggcc": HOST, "encoding": ENGINE}[prefix] / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(archive.extractfile(member).read())
    for relative in ("Cargo.toml", "dag_in_context/Cargo.toml"):
        path = HOST / relative
        text = path.read_text()
        assert text.count("/private/tmp/encoding-parts32-candidate") == 1
        path.write_text(text.replace("/private/tmp/encoding-parts32-candidate", str(ENGINE)))
    manifest = {
        "status": "source reconstruction only; no build or compiler execution",
        "host_root": str(HOST), "encoding_root": str(ENGINE),
        "base_archives": [{"path": str(PARTS / name), "sha256": digest} for _, name, digest in BASES],
        "reviewed_overlay": {"path": str(PARTS / "final-source.tar"), "members": overlay_hashes},
        "base_revisions": {"eggcc": "a0bbec127f83249074a46af3fd6f6126c90fe0fb", "encoding": "392b6d6b48b5bc307a5b9c981c957fc0a09e23e5"},
    }
    output = BASE / "source-admission.json"
    assert not output.exists()
    output.write_text(json.dumps(manifest, indent=2) + "\n")
    print("Reconstructed isolated Pack32 sources; no build or compiler execution")


if __name__ == "__main__":
    argparse.ArgumentParser(description=__doc__).parse_args()
    admit()
