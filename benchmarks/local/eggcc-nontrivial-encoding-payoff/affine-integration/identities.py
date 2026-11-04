#!/usr/bin/env python3
"""Bind the evaluated affine candidate, upstream source, engine, and artifacts."""

from pathlib import Path
import difflib
import hashlib
import json
import platform
import tarfile

BASE = Path(__file__).resolve().parent
U0 = Path("/private/tmp/eggcc-nontrivial-encoding-payoff-u0")
CANDIDATE = Path("/private/tmp/eggcc-affine-candidate")
ENGINE = Path("/private/tmp/encoding-affine-candidate")
ENGINE_REFERENCE = Path("/private/tmp/encoding-parts32-candidate")
PARTS32_EVIDENCE = BASE.parent / "parts32-integration"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_files(root):
    return {
        path.relative_to(root): digest(path)
        for path in root.rglob("*")
        if path.is_file()
        and "target" not in path.parts
        and ".git" not in path.parts
        and not path.name.endswith(".snap.new")
    }


def archive_source_files(archive, root):
    """Compare portable source entries, excluding macOS AppleDouble tar metadata."""
    result = {}
    with tarfile.open(archive) as contents:
        for member in contents:
            if not member.isfile():
                continue
            parts = Path(member.name).parts
            if parts[0].startswith("._"):
                continue
            assert parts[0] == root.name
            relative = Path(*parts[1:])
            if relative == Path(".") or relative.name.startswith("._"):
                continue
            assert relative not in result, relative
            result[relative] = hashlib.sha256(contents.extractfile(member).read()).hexdigest()
    return result


def main():
    admission = json.loads((BASE.parent / "admission/source-files.json").read_text())
    admission_mismatches = [
        name
        for name, expected in admission.items()
        if not (U0 / name).is_file() or digest(U0 / name) != expected
    ]
    assert not admission_mismatches
    upstream = source_files(U0)
    candidate = source_files(CANDIDATE)
    changed = [
        str(path)
        for path in sorted(set(upstream) | set(candidate))
        if upstream.get(path) != candidate.get(path)
    ]
    assert changed == [
        "Cargo.lock",
        "Cargo.toml",
        "dag_in_context/Cargo.lock",
        "dag_in_context/Cargo.toml",
        "dag_in_context/src/lib.rs",
        "dag_in_context/src/scoped_reasoning.rs",
    ], changed

    engine = source_files(ENGINE)
    engine_mismatches = [
        str(path)
        for path, expected in engine.items()
        if not (ENGINE_REFERENCE / path).is_file()
        or digest(ENGINE_REFERENCE / path) != expected
    ]
    assert not engine_mismatches
    assert archive_source_files(BASE / "eggcc-affine-candidate-source.tar", CANDIDATE) == candidate
    assert archive_source_files(BASE / "encoding-affine-candidate-source.tar", ENGINE) == engine
    frozen_engine = json.loads((PARTS32_EVIDENCE / "final-source-identities.json").read_text())
    assert digest(Path(frozen_engine["source_archive"])) == frozen_engine[
        "source_archive_sha256"
    ]
    frozen_engine_files = [
        item for item in frozen_engine["files"]
        if item.get("archive_path", "").startswith("encoding/")
    ]
    assert all(
        digest(ENGINE / item["archive_path"].removeprefix("encoding/"))
        == item["sha256"]
        for item in frozen_engine_files
    )
    engine_full_check = PARTS32_EVIDENCE / "commands/engine-make-check-process-access/receipt.json"
    check_receipt = json.loads(engine_full_check.read_text())
    assert check_receipt["argv"] == ["make", "check"]
    assert check_receipt["exit_code"] == 0 and not check_receipt["timed_out"]

    old_lib = (U0 / "dag_in_context/src/lib.rs").read_text().splitlines(True)
    new_lib = (CANDIDATE / "dag_in_context/src/lib.rs").read_text().splitlines(True)
    new_sidecar = (CANDIDATE / "dag_in_context/src/scoped_reasoning.rs").read_text().splitlines(True)
    patch = "".join(
        difflib.unified_diff(
            old_lib,
            new_lib,
            fromfile="a/dag_in_context/src/lib.rs",
            tofile="b/dag_in_context/src/lib.rs",
        )
    )
    patch += "".join(
        difflib.unified_diff(
            [],
            new_sidecar,
            fromfile="/dev/null",
            tofile="b/dag_in_context/src/scoped_reasoning.rs",
        )
    )
    (BASE / "candidate-semantic.patch").write_text(patch)

    tracked = [
        BASE.parent / "admission/manifest.json",
        BASE.parent / "admission/source-files.json",
        BASE.parent / "admission/bin/eggcc",
        BASE.parent / "admission/bin/tiger",
        CANDIDATE / "Cargo.toml",
        CANDIDATE / "Cargo.lock",
        CANDIDATE / "dag_in_context/Cargo.toml",
        CANDIDATE / "dag_in_context/Cargo.lock",
        CANDIDATE / "dag_in_context/src/lib.rs",
        CANDIDATE / "dag_in_context/src/scoped_reasoning.rs",
        ENGINE / "Cargo.toml",
        ENGINE / "Cargo.lock",
        ENGINE / "egglog-experimental/src/injectivity.rs",
        ENGINE / "egglog-experimental/src/disequality.rs",
        BASE / "bin/eggcc",
        BASE / "bin/tiger",
        CANDIDATE / "runtime/rt.bc",
        CANDIDATE / "runtime/rt.o",
        BASE / "eggcc-affine-candidate-source.tar",
        BASE / "encoding-affine-candidate-source.tar",
        BASE / "candidate-semantic.patch",
        *sorted((BASE / "fixtures").glob("*.bril")),
        *sorted((BASE / "pending-snapshots").glob("*.snap.new")),
        BASE / "positive-oracle.json",
        BASE / "positive-results.json",
        BASE / "negative-results.json",
        BASE / "context-negative-results.json",
        BASE / "verification.json",
        BASE / "failure-ledger.json",
        BASE / "validation.json",
        BASE / "report.md",
        PARTS32_EVIDENCE / "final-source-identities.json",
        Path(frozen_engine["source_archive"]),
        engine_full_check,
        PARTS32_EVIDENCE / "eggcc-snapshot-comparison.json",
        PARTS32_EVIDENCE / "commands/eggcc-make-test/receipt.json",
        BASE / "run.py",
        BASE / "matrix.py",
        BASE / "verify.py",
        BASE / "inspect.py",
        BASE / "identities.py",
    ]
    result = {
        "u0_revision": "a0bbec127f83249074a46af3fd6f6126c90fe0fb",
        "encoding_e1_base": "392b6d6b48b5bc307a5b9c981c957fc0a09e23e5",
        "admitted_u0_files_checked": len(admission),
        "admitted_u0_mismatches": admission_mismatches,
        "candidate_source_files": len(candidate),
        "candidate_archive_files_checked": len(candidate),
        "candidate_differences_from_u0": changed,
        "semantic_source_changes": [
            "dag_in_context/src/lib.rs",
            "dag_in_context/src/scoped_reasoning.rs",
        ],
        "selected_engine_files_checked_against_parts32": len(engine),
        "selected_engine_changed_files_checked_against_frozen_parts32": len(frozen_engine_files),
        "reused_engine_full_check_receipt": str(engine_full_check),
        "engine_archive_files_checked": len(engine),
        "selected_engine_mismatches": engine_mismatches,
        "machine": platform.platform(),
        "timing_campaign": False,
        "files": [{"path": str(path), "sha256": digest(path)} for path in tracked],
    }
    (BASE / "identities.json").write_text(json.dumps(result, indent=2) + "\n")


if __name__ == "__main__":
    main()
