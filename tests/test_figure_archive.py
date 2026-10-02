"""Portable evidence retains exact inputs and rejects an inconsistent corpus."""

from __future__ import annotations

import hashlib
import json
import shutil
import subprocess
import zipfile
from pathlib import Path

import pytest

from benchmarking.archive import FIGURES, archive_figures
from benchmarking.reports.grouped import write_grouped_report
from benchmarking.reports.store import ReportStore

from .report_fixtures import ROOT, make_record


@pytest.fixture
def evidence(tmp_path: Path) -> tuple[Path, Path]:
    corpus = tmp_path / "benchmarks/local/corpus"
    corpus.mkdir(parents=True)
    workload = corpus / "input.egg"
    workload.write_text("(datatype Expr (Leaf))\n(let x (Leaf))\n(extract x)\n")
    digest = "sha256:" + hashlib.sha256(workload.read_bytes()).hexdigest()
    manifest = {
        "sources": {"eggcc": {"repository": "https://example.test/source", "revision": "pinned"}},
        "cases": [
            {"id": "case", "family": "eggcc", "source": "original", "status": "ready", "workloads": ["input.egg"]}
        ],
        "workloads": [
            {
                "file": "input.egg",
                "sha256": digest,
                "facts_sha256": "",
                "aliases": [{"case": "case", "order": 0}],
                "adaptations": [],
            }
        ],
        "outcomes": [],
    }
    (corpus / "manifest.json").write_text(json.dumps(manifest))
    (tmp_path / "benchmarks/sources.json").write_text(json.dumps(manifest["sources"]))
    (tmp_path / "benchmarks/local/figure-inventory.json").write_text('{"timeout_sec": 300}')
    for file in ("Makefile", "Cargo.lock"):
        shutil.copyfile(ROOT / file, tmp_path / file)
    figures = tmp_path / "figures/expanded"
    figures.mkdir(parents=True)
    for name in FIGURES:
        shutil.copyfile(ROOT / f"figures/expanded/{name}.vl.json", figures / f"{name}.vl.json")
        for extension in ("svg", "png"):
            (figures / f"{name}.{extension}").write_bytes(b"existing image")
    store = ReportStore(tmp_path / ".reports.jsonl")
    store.append(
        make_record(0, started_at="2026-10-02T00:00:00Z", target_label="figures", timeout_sec=300, file_sha256=digest)
    )
    store.append(
        make_record(
            1,
            started_at="2026-10-02T00:00:01Z",
            status="timed-out",
            treatment="proof-extraction",
            target_label="figures",
            timeout_sec=300,
            file_sha256=digest,
        )
    )
    write_grouped_report(store.grouped_report(), tmp_path / ".reports-grouped.json")
    subprocess.run(["git", "init", "-q"], cwd=tmp_path, check=True)
    subprocess.run(["git", "add", "Makefile"], cwd=tmp_path, check=True)
    subprocess.run(
        ["git", "-c", "user.name=Test", "-c", "user.email=test@example.test", "commit", "-qm", "fixture"],
        cwd=tmp_path,
        check=True,
    )
    return tmp_path, workload


def test_archive_preserves_exact_snapshot_paths_failures_and_hashes(evidence: tuple[Path, Path]) -> None:
    root, workload = evidence
    original = (root / ".reports-grouped.json").read_bytes()
    cache_time = (root / ".reports.jsonl").stat().st_mtime_ns
    destination = archive_figures(root, root / "evidence.zip")
    with zipfile.ZipFile(destination) as archive:
        assert archive.read(".reports-grouped.json") == original
        assert b"timed-out" in original
        assert archive.read("benchmarks/local/corpus/input.egg") == workload.read_bytes()
        stamp = json.loads(archive.read("provenance.json"))
        assert stamp["binary_sha256"] == ["sha256:bin"]
        assert "vega-lite@6.4.3" in stamp["render_packages"]
        for path, digest in stamp["files"].items():
            assert digest == "sha256:" + hashlib.sha256(archive.read(path)).hexdigest()
        assert "make -B figures/expanded/" in archive.read("README.md").decode()
        assert ".reports.jsonl" not in archive.namelist()
    assert (root / ".reports.jsonl").stat().st_mtime_ns == cache_time


@pytest.mark.parametrize("change", ["modify", "remove"])
def test_changed_corpus_does_not_replace_retained_archive(evidence: tuple[Path, Path], change: str) -> None:
    root, workload = evidence
    destination = root / "evidence.zip"
    destination.write_bytes(b"retained evidence")
    if change == "modify":
        workload.write_text("(check false)\n")
    else:
        workload.unlink()
    with pytest.raises(ValueError, match="changed or missing inputs"):
        archive_figures(root, destination)
    assert destination.read_bytes() == b"retained evidence"
