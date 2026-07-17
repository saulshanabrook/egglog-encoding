"""Test Samply artifact decoding, symbolication, statistics, and rendering."""

from __future__ import annotations

import gzip
import io
import subprocess
from pathlib import Path
from typing import Any

import pytest
from rich.console import Console

from benchmarking import samply_analysis

from .profile_fixtures import make_cpu_profile_data, make_cpu_summary, write_profile


def test_read_profile_artifact_rejects_plain_json(tmp_path: Path) -> None:
    artifact = tmp_path / "profile.json.gz"
    write_profile(artifact, compressed=False)

    with pytest.raises(ValueError, match="not gzip-compressed"):
        samply_analysis.read_artifact(artifact)


def test_read_profile_artifact_rejects_malformed_json(tmp_path: Path) -> None:
    artifact = tmp_path / "profile.json.gz"
    with gzip.open(artifact, "wt", encoding="utf-8") as handle:
        handle.write("not-json")

    with pytest.raises(ValueError, match="could not parse profile artifact"):
        samply_analysis.read_artifact(artifact)


def test_read_profile_artifact_normalizes_os_errors(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    artifact = tmp_path / "profile.json.gz"
    artifact.write_bytes(b"\x1f\x8b")
    original_open = Path.open

    def denied_open(path: Path, *args: Any, **kwargs: Any) -> Any:
        if path == artifact:
            raise PermissionError("denied")
        return original_open(path, *args, **kwargs)

    monkeypatch.setattr(Path, "open", denied_open)

    with pytest.raises(ValueError, match="could not read profile artifact"):
        samply_analysis.read_artifact(artifact)


def test_profile_leaf_samples_have_named_fields(tmp_path: Path) -> None:
    binary = tmp_path / "egglog-experimental"
    profile = make_cpu_profile_data(binary)

    samples = tuple(samply_analysis._thread_leaf_samples(profile["threads"][0], 1e-6))

    assert samples[0].cpu_seconds == pytest.approx(0.1)
    assert samples[0].library_index == 0
    assert samples[0].function_name == "0x10"
    assert samples[0].relative_address == 0x10


def test_macos_profile_summary_uses_cpu_deltas_and_atos_offsets(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    binary = tmp_path / "egglog-experimental"
    binary.write_bytes(b"binary")
    profile = make_cpu_profile_data(binary)
    commands: list[list[str]] = []

    def fake_run(command: list[str], **kwargs: Any) -> subprocess.CompletedProcess[str]:
        commands.append(command)
        return subprocess.CompletedProcess(
            command,
            0,
            stdout="crate..Thing$LT$T$GT$::run::h1234 (in egglog-experimental) + 4\n",
            stderr="",
        )

    monkeypatch.setattr(samply_analysis.shutil, "which", lambda name: "/usr/bin/atos" if name == "atos" else None)
    monkeypatch.setattr(samply_analysis.subprocess, "run", fake_run)

    summary = samply_analysis.summarize(profile, binary)

    assert summary.observed_cpu_seconds == pytest.approx(0.6)
    assert summary.application_cpu_seconds == pytest.approx(0.1)
    assert summary.other_library_cpu_seconds == pytest.approx(0.2)
    assert summary.unattributed_cpu_seconds == pytest.approx(0.3)
    assert summary.symbolized_application_cpu_seconds == pytest.approx(0.1)
    assert len(summary.functions) == 1
    assert summary.functions[0].name == "crate::Thing<T>::run::h1234"
    assert summary.functions[0].cpu_seconds == pytest.approx(0.1)
    assert len(commands) == 1
    assert "-offset" in commands[0]
    assert "0x10" in commands[0]
    assert "0x100000010" not in commands[0]


def test_macos_profile_summary_is_partial_without_atos(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    binary = tmp_path / "egglog-experimental"
    binary.write_bytes(b"binary")
    monkeypatch.setattr(samply_analysis.shutil, "which", lambda name: None)
    monkeypatch.setattr(
        samply_analysis.subprocess,
        "run",
        lambda *args, **kwargs: pytest.fail("symbolizer should not run without atos"),
    )

    summary = samply_analysis.summarize(make_cpu_profile_data(binary), binary)

    assert summary.observed_cpu_seconds == pytest.approx(0.6)
    assert summary.application_cpu_seconds == pytest.approx(0.1)
    assert summary.symbolized_application_cpu_seconds == 0
    assert summary.functions == ()
    assert any("atos is unavailable" in warning for warning in summary.warnings)


def test_macos_rust_v0_symbols_use_llvm_cxxfilt(monkeypatch: pytest.MonkeyPatch) -> None:
    commands: list[tuple[list[str], str | None]] = []

    def fake_run(command: list[str], **kwargs: Any) -> subprocess.CompletedProcess[str]:
        commands.append((command, kwargs.get("input")))
        return subprocess.CompletedProcess(command, 0, stdout="__rustc::__rdl_alloc\n", stderr="")

    monkeypatch.setattr(
        samply_analysis.shutil,
        "which",
        lambda name: "/usr/bin/xcrun" if name == "xcrun" else None,
    )
    monkeypatch.setattr(samply_analysis.subprocess, "run", fake_run)

    symbols, warnings = samply_analysis.demangle_rust_v0_symbols({0x10: "_RNvExample"})

    assert symbols == {0x10: "__rustc::__rdl_alloc"}
    assert warnings == ()
    assert commands == [(["/usr/bin/xcrun", "llvm-cxxfilt"], "_RNvExample\n")]


def test_profile_load_command_quotes_paths_for_posix_and_windows(tmp_path: Path) -> None:
    artifact = tmp_path / "profiles with spaces" / "profile.json.gz"

    assert samply_analysis.load_command(artifact, os_name="posix") == f"samply load '{artifact.resolve()}'"
    assert samply_analysis.load_command(artifact, os_name="nt") == f'samply load "{artifact.resolve()}"'
    assert samply_analysis.load_command(Path(".profiles/profile.json.gz"), os_name="posix") == (
        "samply load .profiles/profile.json.gz"
    )


def test_profile_rich_and_markdown_render_same_summary(tmp_path: Path) -> None:
    artifact = tmp_path / "profiles with spaces" / "profile.json.gz"
    summary = make_cpu_summary()
    report = samply_analysis.ProfileReport(
        artifact=artifact,
        cache_status="hit",
        workload="dir\\name|file\nnext.egg",
        backend="main",
        treatment="proofs",
        top=1,
        cpu_summary=summary,
    )
    rich_output = io.StringIO()
    console = Console(file=rich_output, force_terminal=False, width=120)

    samply_analysis.render_rich(console, report)
    markdown = samply_analysis.render_markdown(report)

    for value in ("CPU Profile Summary", "Observed thread", "Application symbols", "first", "samply load"):
        assert value in rich_output.getvalue()
        assert value in markdown
    assert "second" not in rich_output.getvalue()
    assert "second" not in markdown
    assert "first&lt;T&gt;" in markdown
    assert "dir\\\\name\\|file<br>next.egg" in markdown
    assert "| Metric | CPU | Share |" in markdown
