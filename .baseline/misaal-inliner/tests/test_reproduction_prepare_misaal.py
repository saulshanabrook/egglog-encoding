"""Preparation safety and receipt contracts; these never build native tools."""

import json
from pathlib import Path

import pytest

from benchmarking.pilot import PilotProcessResult
from scripts import reproduction_prepare_misaal as preparation


def test_raw_hash_matches_capture_protocol(tmp_path: Path) -> None:
    source = tmp_path / "input"
    source.write_bytes(b"abc")
    assert preparation.sha256_file(source) == "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"


def test_guarded_failure_retains_request_and_stops(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    def fail(command: list[str], cwd: Path, prefix: Path, **kwargs: object) -> PilotProcessResult:
        assert command == ["a-compiler"]
        assert cwd == tmp_path
        assert kwargs == {
            "timeout_sec": 1800,
            "memory_limit_bytes": 5 * 1024**3,
            "allow_warning_pressure": True,
            "require_guard": True,
            "disk_reserve_bytes": 10 * 1024**3,
        }
        return PilotProcessResult("memory-limit", -9, 1.0, 6 * 1024**3, prefix, prefix, "over cap")

    monkeypatch.setattr(preparation, "run_bounded_command", fail)
    attempt = preparation.Preparation(tmp_path)
    with pytest.raises(RuntimeError, match="memory-limit"):
        attempt.step("build", ["a-compiler"], timeout=1800)
    assert (tmp_path / "steps/001-build.request.json").is_file()
    assert '"status": "memory-limit"' in (tmp_path / "steps/001-build.result.json").read_text()


def test_patch_requires_exact_context_and_owned_source(tmp_path: Path) -> None:
    attempt = preparation.Preparation(tmp_path)
    source = tmp_path / "sources/CMakeLists.txt"
    source.parent.mkdir()
    source.write_text("old\n")
    attempt.patch(source, [("old\n", "new\n")], "build-only")
    assert source.read_text() == "new\n"
    assert "-old\n+new\n" in (tmp_path / "patches/build-only.patch").read_text()
    with pytest.raises(ValueError, match="exactly one context"):
        attempt.patch(source, [("old\n", "invented\n")], "invalid")
    assert not (tmp_path / "patches/invalid.patch").exists()
    with pytest.raises(ValueError, match="outside"):
        attempt.patch(tmp_path / "outside", [("old", "new")], "outside")


def test_receipt_cannot_replace_previous_evidence(tmp_path: Path) -> None:
    receipt = tmp_path / "receipt.json"
    preparation.write_json(receipt, {"status": "failure"})
    with pytest.raises(FileExistsError):
        preparation.write_json(receipt, {"status": "success"})
    assert '"failure"' in receipt.read_text()


def test_wide_constant_repair_preserves_all_decimal_values(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    backend = tmp_path / "backend"
    backend.write_bytes(b"pinned backend")
    monkeypatch.setattr(preparation, "EGGLOG_SHA256", preparation.sha256_file(backend))
    (tmp_path / "identity.json").write_text(
        json.dumps(
            {
                "misaal_revision": preparation.MISAAL_REVISION,
                "hydride_revision": preparation.HYDRIDE_REVISION,
            }
        )
    )
    steps = tmp_path / "steps"
    steps.mkdir()
    stderr = steps / "018-legalizer-build.stderr.log"
    stderr.write_text("integer literal is too large to be represented in any integer type")
    (steps / "018-legalizer-build.result.json").write_text(
        json.dumps(
            {
                "status": "failure",
                "stderr_path": str(stderr),
            }
        )
    )
    source = (
        tmp_path
        / "sources/MISAAL/Hydride/codegen-generator/tools/low-level-codegen/InstSelectors/x86/x86LegalizerAllArgs.cpp"
    )
    source.parent.mkdir(parents=True)
    values = [2**width - 1 for width in (128, 256, 512)] * 4
    source.write_text("\n".join(f"isAMatch(CI, 3, {value})" for value in values) + "\nisAMatch(CI, 3, 12)\n")
    commands: list[list[str]] = []

    def step(self: preparation.Preparation, name: str, command: list[str]) -> str:
        commands.append(command)
        return ""

    monkeypatch.setattr(preparation.Preparation, "step", step)
    monkeypatch.setattr(preparation, "finish_native", lambda *_: tmp_path / "request.json")
    preparation.repair_wide_literals(tmp_path, backend)
    assert source.read_text().splitlines() == [
        *(f'isAMatch(CI, 3, int512_t("{value}"))' for value in values),
        "isAMatch(CI, 3, 12)",
    ]
    assert len(commands) == 1 and commands[0][-2:] == ["--parallel", "1"]
    assert (tmp_path / "patches/legalizer-exact-wide-constants.patch").is_file()


def test_cache_override_preserves_default_names(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    attempt = preparation.Preparation(tmp_path)
    modules = {"Halide": "halide", "x86": "x86", "ARM": "ARM", "HVX": "hvx"}
    for module, stem in modules.items():
        source = tmp_path / f"sources/MISAAL/lib/patterns/{module}.py"
        source.parent.mkdir(parents=True, exist_ok=True)
        source.write_text(
            'import os\nMISAAL_ROOT = "/source"\n'
            f'pickle_file_name = MISAAL_ROOT + "/lib/patterns/{stem}.pickle"\n'
            f'abstract_pickle_file_name = MISAAL_ROOT + "/lib/patterns/{stem}_abstract.pickle"\n'
        )
    preparation.patch_pattern_cache(attempt)
    for override in (None, "/attempt/pattern-cache"):
        if override is None:
            monkeypatch.delenv("MISAAL_PATTERN_CACHE_DIR", raising=False)
        else:
            monkeypatch.setenv("MISAAL_PATTERN_CACHE_DIR", override)
        for module, stem in modules.items():
            namespace: dict[str, object] = {}
            source = tmp_path / f"sources/MISAAL/lib/patterns/{module}.py"
            exec(compile(source.read_text(), str(source), "exec"), namespace)
            cache = override or "/source/lib/patterns"
            assert namespace["pickle_file_name"] == f"{cache}/{stem}.pickle"
            assert namespace["abstract_pickle_file_name"] == f"{cache}/{stem}_abstract.pickle"


def test_fresh_wide_constant_patch_rejects_changed_upstream(tmp_path: Path) -> None:
    attempt = preparation.Preparation(tmp_path)
    source = (
        tmp_path
        / "sources/MISAAL/Hydride/codegen-generator/tools/low-level-codegen/InstSelectors/x86/x86LegalizerAllArgs.cpp"
    )
    source.parent.mkdir(parents=True)
    value = 2**128 - 1
    original = f"isAMatch(CI, 3, {value})\n" * 11
    source.write_text(original)
    with pytest.raises(ValueError, match="expected the 12 observed oversized literals, found 11"):
        preparation.patch_wide_literals(attempt)
    assert source.read_text() == original
    assert not (tmp_path / "patches/legalizer-exact-wide-constants.patch").exists()
    source.write_text(original + f"isAMatch(CI, 3, {value})\n")
    preparation.patch_wide_literals(attempt)
    assert source.read_text() == f'isAMatch(CI, 3, int512_t("{value}"))\n' * 12
    assert not list((tmp_path / "steps").iterdir())
