"""Preparation uses the pinned tree and rejects source, patch or binary drift."""

import json
import subprocess
from pathlib import Path

import pytest

from benchmarking.targets import sha256_file
from benchmarks.reproduction.lmfao import prepare


def git(path: Path, *args: str) -> str:
    return subprocess.check_output(["git", "-C", str(path), *args], text=True).strip()


@pytest.fixture
def pinned_source(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> tuple[Path, Path]:
    source = tmp_path / "upstream"
    source.mkdir()
    git(source, "init", "-q")
    git(source, "config", "user.name", "Fixture")
    git(source, "config", "user.email", "fixture@example.invalid")
    (source / "src/compiler").mkdir(parents=True)
    (source / "src/compiler/input.txt").write_text("original\n")
    git(source, "add", ".")
    git(source, "commit", "-qm", "pinned")
    monkeypatch.setattr(prepare, "COMMIT", git(source, "rev-parse", "HEAD"))
    (source / "src/compiler/input.txt").write_text("newer upstream\n")
    git(source, "commit", "-qam", "newer")
    (source / "src/compiler/input.txt").write_text("uncommitted source changes\n")
    adapter = tmp_path / "adapter"
    adapter.mkdir()
    for name, before, after in zip(prepare.PATCHES, ["original", "bridge"], ["bridge", "corrected"], strict=True):
        (adapter / name).write_text(
            "diff --git a/src/compiler/input.txt b/src/compiler/input.txt\n"
            "--- a/src/compiler/input.txt\n+++ b/src/compiler/input.txt\n"
            f"@@ -1 +1 @@\n-{before}\n+{after}\n"
        )
    for name in prepare.HEADERS:
        (adapter / name).write_text("// test adapter\n")
    monkeypatch.setattr(prepare, "ADAPTER", adapter)
    output = tmp_path / "prepared"
    output.mkdir()
    return source, output


def test_patches_apply_to_pin_and_preserve_source(pinned_source: tuple[Path, Path]) -> None:
    source, output = pinned_source
    checkout = prepare.patched_checkout(source, output)
    assert git(checkout, "rev-parse", "HEAD") == prepare.COMMIT
    assert (checkout / "src/compiler/input.txt").read_text() == "corrected\n"
    assert (source / "src/compiler/input.txt").read_text() == "uncommitted source changes\n"
    assert all((checkout / "src/compiler" / header).exists() for header in prepare.HEADERS)


def test_patch_drift_fails_before_build(pinned_source: tuple[Path, Path]) -> None:
    source, output = pinned_source
    patch = prepare.ADAPTER / prepare.PATCHES[0]
    patch.write_text(patch.read_text().replace("-original", "-wrong base"))
    with pytest.raises(subprocess.CalledProcessError):
        prepare.patched_checkout(source, output)
    assert (output / "source/src/compiler/input.txt").read_text() == "original\n"


@pytest.mark.parametrize("changed", ["commit", "adapter", "binary"])
def test_backend_provenance_rejects_drift(
    pinned_source: tuple[Path, Path],
    changed: str,
) -> None:
    _, output = pinned_source
    (output / "build").mkdir()
    binary = output / "build/multifaq"
    binary.write_bytes(b"prepared executable")
    manifest = {
        "lmfao_commit": prepare.COMMIT,
        "adapter_sha256": prepare.adapter_hashes(),
        "binary_sha256": sha256_file(binary),
    }
    path = output / "provenance.json"
    path.write_text(json.dumps(manifest))
    assert prepare.verify_backend(binary) == manifest
    if changed == "commit":
        manifest["lmfao_commit"] = "0" * 40
        path.write_text(json.dumps(manifest))
    elif changed == "adapter":
        (prepare.ADAPTER / prepare.HEADERS[0]).write_text("changed bridge")
    else:
        binary.write_bytes(b"other executable")
    with pytest.raises(ValueError, match="provenance differs"):
        prepare.verify_backend(binary)
