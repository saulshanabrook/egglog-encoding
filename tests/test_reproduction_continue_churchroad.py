"""Continuation protocol only: mocked child processes never compile or run native code."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import pytest

from benchmarking.pilot import PilotProcessResult
from benchmarking.targets import sha256_file
from scripts import reproduction_continue_churchroad as continuation


@pytest.fixture
def checkpoint(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> tuple:
    monkeypatch.setattr(continuation, "ROOT", tmp_path)
    previous = tmp_path / "benchmarks/local/reproduction/failed"
    output = previous.with_name("continued")
    source = previous / "sources/churchroad"
    old = "fn fixture() {\n        .arg(spec_filepath)\n}\n"
    files = {
        "scripts/reproduction_prepare_churchroad.py": "exact old preparer",
        "scripts/eggcc_churchroad_complete.py": "current capture implementation",
        "capture-before.py": "old capture implementation",
        "engine": "ordinary engine",
        "racket": "host prerequisite",
        "benchmarks/local/reproduction/failed/evidence/churchroad-native-capture.patch": "original patch",
        "benchmarks/local/reproduction/failed/sources/churchroad/src/lib.rs": old,
        "benchmarks/local/reproduction/failed/sources/churchroad/src/main.rs": "unchanged main",
        "benchmarks/local/reproduction/failed/sources/churchroad/Cargo.toml": "unchanged manifest",
        "benchmarks/local/reproduction/failed/sources/churchroad/Cargo.lock": "frozen dependencies",
        "benchmarks/local/reproduction/failed/sources/churchroad/yosys-plugin/churchroad.so": "plugin",
        (
            "benchmarks/local/reproduction/failed/sources/lakeroad/racket/generated/xilinx-ultrascale-plus-dsp48e2.rkt"
        ): "model",
        "benchmarks/local/reproduction/failed/prefix/bin/bitwuzla": "solver",
        "benchmarks/local/reproduction/failed/prefix/bin/yosys": "synthesizer",
        "benchmarks/local/reproduction/failed/prefix/bin/yosys-config": "configuration",
        "benchmarks/local/reproduction/failed/racket-user/package.rkt": "dependency",
    }
    for name, content in files.items():
        path = tmp_path / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content)
    target = previous / "build/cargo"
    saved = {
        "status": "failure",
        "reason": "error[E0382]: use of moved value: spec_filepath",
        "implementation_sha256": sha256_file(tmp_path / "scripts/reproduction_prepare_churchroad.py"),
        "capture_implementation_sha256": sha256_file(tmp_path / "capture-before.py"),
        "host_tools": {"racket": {"path": str(tmp_path / "racket"), "sha256": sha256_file(tmp_path / "racket")}},
        "racket_runtime_paths": [],
        "steps": [
            {"name": "verified-native-prerequisites", "status": "success"},
            {
                "name": "churchroad-build",
                "status": "failure",
                "cwd": str(source),
                "command": [
                    "env",
                    f"CARGO_TARGET_DIR={target}",
                    "MAKEFLAGS=-j1",
                    "cargo",
                    f"+{continuation.RUST_VERSION}",
                    "build",
                    "--locked",
                    "-j1",
                    "--bin",
                    "churchroad",
                ],
            },
        ],
    }
    receipt = previous / "preparation.json"
    receipt.write_text(json.dumps(saved))
    state: dict[str, Any] = {"saved": saved, "old": old}
    launches: list[dict] = []

    def patch(original: Path) -> dict[str, str]:
        assert (original / "src/lib.rs").read_text() == "original src/lib.rs"
        return {
            "src/lib.rs": old.replace(".arg(spec_filepath)", ".arg(&spec_filepath)") + state.get("extra_change", ""),
            "src/main.rs": "unchanged main",
            "Cargo.toml": "unchanged manifest",
        }

    def run(command: list[str], cwd: Path, prefix: Path, **options: Any) -> PilotProcessResult:
        name = prefix.name.split("-", 1)[1]
        retained = json.loads((output / "continuation.json").read_text())
        assert retained["steps"][-1]["status"] == "running"
        assert sha256_file(receipt) == retained["previous_receipt_sha256"]
        launches.append({"name": name, "command": command, "options": options})
        stdout, stderr = prefix.with_suffix(".stdout.log"), prefix.with_suffix(".stderr.log")
        stdout.write_text("")
        stderr.write_text("")
        if name == state.get("guard"):
            raise ValueError("memory guard refused to launch")
        if name == "source-revision":
            stdout.write_text(continuation.REVISIONS["churchroad"][1])
        elif name.startswith("source-"):
            stdout.write_text("original " + command[-1].removeprefix("HEAD:"))
        elif name == "churchroad-build":
            assert (output / "evidence/previous-lib.rs").read_text() == old
            assert retained["repair_sha256"] == sha256_file(output / "evidence/borrow-repair.patch")
            assert (source / "src/lib.rs").read_text() == patch(output / "evidence/original-source")["src/lib.rs"]
            binary = target / "debug/churchroad"
            binary.parent.mkdir(parents=True)
            binary.write_text("new native driver")
            if state.get("changed_product"):
                (previous / "prefix/bin/bitwuzla").write_text("unexpected mutation")
        return PilotProcessResult("success", 0, 0, 0, stdout, stderr, None)

    monkeypatch.setattr(continuation, "patched_churchroad_sources", patch)
    monkeypatch.setattr(continuation, "run_bounded_command", run)
    return previous, output, tmp_path / "engine", tmp_path / "capture-before.py", state, launches


def test_continuation_preserves_failed_evidence_and_only_rebuilds_driver(checkpoint: tuple) -> None:
    previous, output, engine, capture, state, launches = checkpoint
    before = (previous / "preparation.json").read_bytes()
    result = continuation.continue_churchroad(previous, output, engine, capture)
    assert result["status"] == "success", result["reason"]
    assert (previous / "preparation.json").read_bytes() == before
    assert (output / "evidence/previous-preparation.json").read_bytes() == before
    assert (output / "evidence/previous-lib.rs").read_text() == state["old"]
    assert result["device_execution"] is result["benchmark_execution"] is False
    names = [row["name"] for row in launches]
    assert names == [
        "source-revision",
        "source-lib.rs",
        "source-main.rs",
        "source-Cargo.toml",
        "churchroad-build",
        "churchroad-help",
        "linked-bitwuzla",
        "linked-yosys",
        "linked-churchroad",
        "linked-plugin",
        "linked-racket",
    ]
    for row in launches:
        assert row["options"]["require_guard"]
        assert row["options"]["disk_reserve_bytes"] == 10 * 1024**3
    settings = json.loads(Path(result["settings"]).read_text())["churchroad"]
    assert settings["paths"]["checkout"] == str(previous / "sources/churchroad")
    assert settings["paths"]["binary"] == str(output / "churchroad-capture")
    assert str(previous / "prefix") in settings["identity_paths"]
    assert str(output / "evidence") in settings["identity_paths"]


@pytest.mark.parametrize("bad_checkpoint", ["earlier-failure", "different-error", "parallel-build", "changed-preparer"])
def test_continuation_rejects_unreviewed_checkpoints_before_launch(checkpoint: tuple, bad_checkpoint: str) -> None:
    previous, output, engine, capture, state, launches = checkpoint
    saved = state["saved"]
    if bad_checkpoint == "earlier-failure":
        saved["steps"][0]["status"] = "failure"
    elif bad_checkpoint == "different-error":
        saved["reason"] = "some other failure"
    elif bad_checkpoint == "parallel-build":
        saved["steps"][-1]["command"].remove("-j1")
    else:
        saved["implementation_sha256"] = "different source"
    (previous / "preparation.json").write_text(json.dumps(saved))
    with pytest.raises(ValueError):
        continuation.continue_churchroad(previous, output, engine, capture)
    assert not launches and not output.exists()


def test_continuation_rejects_extra_source_changes_without_modifying_failed_source(checkpoint: tuple) -> None:
    previous, output, engine, capture, state, launches = checkpoint
    state["extra_change"] = "unreviewed change"
    result = continuation.continue_churchroad(previous, output, engine, capture)
    assert result["status"] == "blocked" and "more than the reviewed" in result["reason"]
    assert (previous / "sources/churchroad/src/lib.rs").read_text() == state["old"]
    assert not any(row["name"] == "churchroad-build" for row in launches)
    assert not (output / "settings.json").exists()


def test_continuation_resource_stop_does_not_start_next_child(checkpoint: tuple) -> None:
    previous, output, engine, capture, state, launches = checkpoint
    state["guard"] = "churchroad-build"
    result = continuation.continue_churchroad(previous, output, engine, capture)
    assert result["status"] == "resource-stopped"
    assert launches[-1]["name"] == "churchroad-build"
    assert (output / "evidence/previous-lib.rs").read_text() == state["old"]
    assert not (output / "settings.json").exists()


def test_changed_verified_prerequisite_blocks_settings(checkpoint: tuple) -> None:
    previous, output, engine, capture, state, _ = checkpoint
    state["changed_product"] = True
    result = continuation.continue_churchroad(previous, output, engine, capture)
    assert result["status"] == "blocked" and "output changed" in result["reason"]
    assert not (output / "settings.json").exists()
