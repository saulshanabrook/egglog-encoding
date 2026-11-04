#!/usr/bin/env python3
"""Stage the durable P1 sidecar in its isolated host. No build or execution."""
import argparse
import hashlib
import json
from pathlib import Path

BASE = Path(__file__).resolve().parent
HOST = Path("/private/tmp/eggcc-pack32-candidate")


def stage():
    library = HOST / "dag_in_context/src/lib.rs"
    text = library.read_text()
    old_schema = '        concat!(\n            include_str!("schema.egg"),\n            "\\n(relation Parts32FalseIfEnabled ())\\n"\n        ),'
    assert text.count(old_schema) == 1
    text = text.replace(old_schema, '        include_str!("schema.egg"),')
    start = text.index('        &if std::env::var("EGGCC_SCOPED_MODE").as_deref() == Ok("if-consumer-off") {')
    end = text.index('        &rulesets(config),', start)
    text = text[:start] + '        include_str!("optimizations/non_weakly_linear.egg"),\n' + text[end:]
    assert "Parts32FalseIfEnabled" not in text
    library.write_text(text)
    sidecar = HOST / "dag_in_context/src/scoped_reasoning.rs"
    sidecar.write_bytes((BASE / "scoped_reasoning.rs").read_bytes())
    manifest = {"status": "staged only; no compiler/native execution", "files": []}
    for path in (library, sidecar, HOST / "Cargo.toml", HOST / "Cargo.lock", HOST / "dag_in_context/Cargo.toml", HOST / "dag_in_context/Cargo.lock"):
        manifest["files"].append({"path": str(path), "sha256": hashlib.sha256(path.read_bytes()).hexdigest()})
    output = BASE / "staged-source-identities.json"
    assert not output.exists()
    output.write_text(json.dumps(manifest, indent=2) + "\n")
    print("Staged Pack32 source; no build or compiler execution")


if __name__ == "__main__":
    argparse.ArgumentParser(description=__doc__).parse_args()
    stage()
