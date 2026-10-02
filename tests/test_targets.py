"""Test target syntax, checkout materialization, build selection, and hashing."""

from __future__ import annotations

import io
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Any

import pytest
from rich.console import Console

from benchmarking import models, targets


def make_dirty_git_repo(path: Path) -> tuple[str, Path]:
    """Create the dirty checkout needed only by target materialization tests."""

    tracked = path / "tracked.txt"
    (path / ".gitignore").write_text("/.bench-worktrees/\n", encoding="utf-8")
    tracked.write_text("committed\n", encoding="utf-8")
    subprocess.run(["git", "init", "--quiet"], cwd=path, check=True)
    subprocess.run(["git", "add", ".gitignore", tracked.name], cwd=path, check=True)
    subprocess.run(
        [
            "git",
            "-c",
            "user.name=Benchmark Test",
            "-c",
            "user.email=benchmark@example.com",
            "commit",
            "--quiet",
            "-m",
            "initial",
        ],
        cwd=path,
        check=True,
    )
    sha = targets.git_sha(path)
    tracked.write_text("dirty\n", encoding="utf-8")
    return (sha, tracked)


def test_parse_target_variants() -> None:
    assert targets.parse_target(".") == models.TargetRequest(raw=".", source=".", label=None)
    assert targets.parse_target("main=@main") == models.TargetRequest(raw="main=@main", source="@main", label="main")
    assert targets.parse_target("prev-run=") == models.TargetRequest(raw="prev-run=", source="", label="prev-run")
    assert targets.parse_target("#33") == models.TargetRequest(raw="#33", source="#33", label="#33")
    assert targets.parse_target("candidate=#33") == models.TargetRequest(
        raw="candidate=#33", source="#33", label="candidate"
    )


@pytest.mark.parametrize("raw", ["#", "#0", "#abc", "candidate=#0"])
def test_parse_target_rejects_invalid_pr_targets(raw: str) -> None:
    with pytest.raises(ValueError, match="invalid PR target"):
        targets.parse_target(raw)


def test_materialize_pr_target_fetches_origin_pull_ref(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    calls: list[list[str]] = []

    def fake_run(
        args: list[str],
        *,
        cwd: Path,
        check: bool,
        stdout: Any | None = None,
        stderr: Any | None = None,
    ) -> None:
        calls.append(args)
        assert cwd == tmp_path
        assert check
        assert stdout is sys.stderr
        assert stderr is sys.stderr

    def fake_git_sha(cwd: Path, ref: str = "HEAD") -> str:
        assert cwd in {tmp_path, tmp_path / ".bench-worktrees" / "33"}
        if ref == "refs/remotes/origin/pr/33":
            return "abc123"
        if ref == "HEAD":
            return "abc123"
        raise AssertionError(f"unexpected ref: {ref}")

    monkeypatch.setattr(targets.subprocess, "run", fake_run)
    monkeypatch.setattr(targets, "git_sha", fake_git_sha)
    monkeypatch.setattr(targets, "find_clean_worktree_for_sha", lambda repo, sha: None)

    checkout_path, sha = targets.materialize_pr_target(tmp_path, "#33", "#33")

    assert checkout_path == tmp_path / ".bench-worktrees" / "33"
    assert sha == "abc123"
    assert calls == [
        ["git", "fetch", "origin", "+refs/pull/33/head:refs/remotes/origin/pr/33"],
        ["git", "worktree", "add", "--detach", str(tmp_path / ".bench-worktrees" / "33"), "abc123"],
    ]


@pytest.mark.parametrize("source", ["@HEAD", "#33"])
def test_explicit_git_sources_isolate_dirty_matching_worktree(
    source: str,
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    sha, _ = make_dirty_git_repo(tmp_path)

    if source == "#33":

        def fake_fetch_pr_ref(repo: Path, number: int) -> str:
            assert repo == tmp_path
            assert number == 33
            return "HEAD"

        monkeypatch.setattr(targets, "fetch_pr_ref", fake_fetch_pr_ref)

    row = targets.materialize_target_request(targets.parse_target(source), tmp_path, tmp_path)
    checkout = Path(row.path)

    assert checkout != tmp_path.resolve()
    assert row.git_sha == sha
    assert not row.is_dirty
    assert (checkout / "tracked.txt").read_text(encoding="utf-8") == "committed\n"


def test_find_clean_worktree_for_sha_skips_manually_deleted_worktree(tmp_path: Path) -> None:
    sha, _ = make_dirty_git_repo(tmp_path)
    deleted_worktree = tmp_path.parent / f"{tmp_path.name}-deleted-worktree"
    subprocess.run(
        ["git", "worktree", "add", "--detach", str(deleted_worktree), sha],
        cwd=tmp_path,
        check=True,
    )
    shutil.rmtree(deleted_worktree)

    assert targets.find_clean_worktree_for_sha(tmp_path, sha) is None


@pytest.mark.parametrize("use_absolute_path", [False, True])
def test_path_targets_retain_dirty_checkout(use_absolute_path: bool, tmp_path: Path) -> None:
    sha, tracked = make_dirty_git_repo(tmp_path)
    source = str(tmp_path) if use_absolute_path else "."

    row = targets.materialize_target_request(targets.parse_target(source), tmp_path, tmp_path)

    assert Path(row.path) == tmp_path.resolve()
    assert row.git_ref == "HEAD"
    assert row.git_sha == sha
    assert row.is_dirty
    assert tracked.read_text(encoding="utf-8") == "dirty\n"


def test_build_target_builds_release_binary(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    monkeypatch.delenv("CARGO_TARGET_DIR", raising=False)
    commands: list[list[str]] = []
    binary = tmp_path / "target" / "release" / "egglog-experimental"
    binary.parent.mkdir(parents=True)
    binary.write_text("binary", encoding="utf-8")
    label = "build [red]literal[/red] x[/blue]"
    row = models.TargetRow(".", str(tmp_path), "HEAD", "abc123", False, label)
    monkeypatch.setattr(targets.subprocess, "run", lambda command, **kwargs: commands.append(command))
    monkeypatch.setattr(targets, "sha256_file", lambda path: "sha256:bin")
    stream = io.StringIO()

    targets.build_target(row, Console(file=stream, color_system=None))

    assert commands == [["cargo", "build", "--release", "-p", "egglog-experimental"]]
    assert stream.getvalue().strip() == f"Building {label}"


@pytest.mark.parametrize("engines", [("egglog",), ("egg",), ("egglog", "egg"), ("egg", "egglog", "egg")])
@pytest.mark.parametrize("profile", ["release", "profiling"])
def test_single_and_mixed_targets_build_the_same_individual_package_commands(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
    engines: tuple[models.Engine, ...],
    profile: targets.BuildProfile,
) -> None:
    monkeypatch.delenv("CARGO_TARGET_DIR", raising=False)
    commands: list[list[str]] = []
    packages = {"egglog": "egglog-experimental", "egg": "egg-math-benchmark"}
    row = models.TargetRow(".", str(tmp_path), "HEAD", "abc123", False)

    def build(command: list[str], **kwargs: Any) -> None:
        assert kwargs["cwd"] == tmp_path
        commands.append(command)
        binary = tmp_path / "target" / profile / command[-1]
        binary.parent.mkdir(parents=True, exist_ok=True)
        binary.write_text(f"{command[-1]} with its individual package features\n")

    monkeypatch.setattr(targets.subprocess, "run", build)
    monkeypatch.setattr(targets, "git_dirty", lambda _path: False)

    resolved = targets.build_resolved_target(
        targets.parse_target("."), row, Console(file=io.StringIO()), profile, engines
    )

    unique_engines = tuple(dict.fromkeys(engines))
    profile_args = ["--release"] if profile == "release" else ["--profile", "profiling"]
    assert commands == [["cargo", "build", *profile_args, "-p", packages[engine]] for engine in unique_engines]
    assert tuple(binary.engine for binary in resolved.engine_binaries) == unique_engines
    for binary in resolved.engine_binaries:
        assert binary.path is not None
        assert binary.sha256 == targets.sha256_file(binary.path)
    assert {path.name for path in (tmp_path / "target" / profile).iterdir()} == {
        packages[engine] for engine in unique_engines
    }


def test_legacy_resolved_target_only_falls_back_to_egglog_binary() -> None:
    binary = Path("/tmp/egglog-experimental")
    target = models.ResolvedTarget(
        request=targets.parse_target("."),
        row=models.TargetRow(".", "/tmp", "HEAD", "abc123", False),
        binary_sha256="sha256:egglog",
        binary_path=binary,
    )

    assert target.binary_sha256_for("proofs") == "sha256:egglog"
    assert target.binary_path_for("proofs") == binary
    with pytest.raises(ValueError, match="has no egg binary"):
        target.binary_sha256_for("egg-proofs")
    with pytest.raises(ValueError, match="has no egg binary"):
        target.binary_path_for("egg-proofs")


@pytest.mark.parametrize("relative", [False, True])
def test_build_locates_binary_in_cargo_target_dir(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, relative: bool
) -> None:
    checkout = tmp_path / "checkout"
    checkout.mkdir()
    configured = "../shared-target" if relative else str(tmp_path / "shared-target")
    monkeypatch.setenv("CARGO_TARGET_DIR", configured)
    monkeypatch.delenv("EGGLOG_BENCH_MEMORY_GUARD", raising=False)
    produced = (checkout / configured / "release/egglog-experimental").resolve()
    produced.parent.mkdir(parents=True)
    produced.write_bytes(b"built in shared Cargo output")
    commands: list[list[str]] = []
    monkeypatch.setattr(targets.subprocess, "run", lambda command, **kwargs: commands.append(command))
    row = models.TargetRow(".", str(checkout), "HEAD", "abc123", False)
    path, digest = targets.build_target(row, Console(file=io.StringIO()))
    assert path.resolve() == produced and digest == targets.sha256_file(produced)
    assert commands == [["cargo", "build", "--release", "-p", "egglog-experimental"]]
