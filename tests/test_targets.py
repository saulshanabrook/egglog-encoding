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


def test_build_target_enables_requested_backend_features(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    commands: list[list[str]] = []
    binary = tmp_path / "target" / "release" / "egglog-experimental"
    binary.parent.mkdir(parents=True)
    binary.write_text("binary", encoding="utf-8")
    label = "build [red]literal[/red] x[/blue]"
    row = models.TargetRow(".", str(tmp_path), "HEAD", "abc123", False, label)
    monkeypatch.setattr(targets.subprocess, "run", lambda command, **kwargs: commands.append(command))
    monkeypatch.setattr(targets, "sha256_file", lambda path: "sha256:bin")
    stream = io.StringIO()

    targets.build_target(
        row,
        Console(file=stream, color_system=None),
        cargo_features=models.backend_cargo_features(("main", "dd")),
    )

    assert commands == [["cargo", "build", "--release", "-p", "egglog-experimental", "--features", "dd-backend"]]
    assert stream.getvalue().strip() == f"Building {label}"
