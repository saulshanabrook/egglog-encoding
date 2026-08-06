"""Stage historical Rust sources with the minimal current-Cargo compatibility patch."""

from __future__ import annotations

import argparse
import os
import shutil
import sys
import tempfile
from pathlib import Path

RUST_ARTIFACT_TOOLCHAIN = "1.91.0"
RUST_ARTIFACT_COMPATIBILITY = "qualify-ast-rule-bounded-driver-and-standalone-workspace-v1"

_RULE_REPLACEMENTS = (
    ("            Rule {", "            ast::Rule {", 1),
    (
        "fn parenthesize_globals(rule: Rule, globals: &HashSet<Symbol>) -> Rule {",
        "fn parenthesize_globals(rule: ast::Rule, globals: &HashSet<Symbol>) -> ast::Rule {",
        1,
    ),
    (
        "fn flatten_rule(rule_in: Rule, globals: &HashSet<Symbol>) -> NormRule {",
        "fn flatten_rule(rule_in: ast::Rule, globals: &HashSet<Symbol>) -> NormRule {",
        1,
    ),
)

_MATH_REPLACEMENTS = (
    (
        "    #[structopt(long)]\n    disable_eqlog: bool,\n",
        (
            "    #[structopt(long)]\n"
            "    disable_eqlog: bool,\n"
            "    #[structopt(long)]\n"
            "    disable_eqlog_naive: bool,\n"
            "    #[structopt(long)]\n"
            "    only_iter: Option<usize>,\n"
        ),
        1,
    ),
    (
        (
            "        if !opt.disable_eqlog {\n"
            "            let mut durations = vec![];\n"
            "            let mut size = 0;\n"
            "            for _ in 0..opt.repeat {\n"
            "                let eqlognaive_start_time"
        ),
        (
            "        if !opt.disable_eqlog && !opt.disable_eqlog_naive {\n"
            "            let mut durations = vec![];\n"
            "            let mut size = 0;\n"
            "            for _ in 0..opt.repeat {\n"
            "                let eqlognaive_start_time"
        ),
        1,
    ),
    (
        "        if !opt.disable_egg && !opt.disable_eqlog {",
        "        if !opt.disable_egg && !opt.disable_eqlog && !opt.disable_eqlog_naive {",
        1,
    ),
    (
        "        if opt.disable_egg && !opt.disable_eqlog {",
        "        if opt.disable_egg && !opt.disable_eqlog && !opt.disable_eqlog_naive {",
        1,
    ),
    (
        "    for i in 1..opt.iter_size + 1 {",
        (
            "    let start_iter = opt.only_iter.unwrap_or(1);\n"
            "    let end_iter = opt.only_iter.unwrap_or(opt.iter_size);\n"
            "    for i in start_iter..=end_iter {"
        ),
        1,
    ),
)


def stage_rust_artifact(artifact_root: Path, destination: Path, kind: str) -> None:
    """Copy the selected authenticated source bundle and patch its build boundary."""

    if kind not in {"math", "eqlog"}:
        raise ValueError(f"unknown historical Rust artifact kind: {kind}")
    source = artifact_root.resolve(strict=True)
    target = destination.expanduser().absolute()
    target.parent.mkdir(parents=True, exist_ok=True)
    stage = Path(tempfile.mkdtemp(prefix=f".{target.name}.staging-", dir=target.parent))
    try:
        shutil.copytree(source / "eqlog", stage / "eqlog")
        if kind == "math":
            shutil.copytree(source / "micro-benchmarks", stage / "micro-benchmarks")
        _patch_rule_resolution(stage / "eqlog/src/desugar.rs")
        if kind == "math":
            _apply_replacements(stage / "micro-benchmarks/src/main.rs", _MATH_REPLACEMENTS)
        top_manifest = stage / ("micro-benchmarks/Cargo.toml" if kind == "math" else "eqlog/Cargo.toml")
        make_manifest_standalone(top_manifest)
        replace_directory(stage, target)
    except BaseException:
        remove_tree(stage)
        raise


def make_manifest_standalone(path: Path) -> None:
    """Prevent a staged package from joining the repository's parent workspace."""

    source = path.read_text(encoding="utf-8")
    if "[workspace]" in source:
        return
    path.write_text(source.rstrip() + "\n\n[workspace]\n", encoding="utf-8")


def replace_directory(stage: Path, destination: Path) -> None:
    """Publish a complete staged directory while preserving the prior tree on failure."""

    backup: Path | None = None
    if os.path.lexists(destination):
        if destination.is_symlink() or not destination.is_dir():
            raise ValueError(f"stage destination is not a regular directory: {destination}")
        backup = Path(tempfile.mkdtemp(prefix=f".{destination.name}.old-", dir=destination.parent))
        backup.rmdir()
        destination.rename(backup)
    try:
        stage.rename(destination)
    except BaseException:
        if backup is not None:
            backup.rename(destination)
        raise
    if backup is not None:
        remove_tree(backup)


def remove_tree(path: Path) -> None:
    """Remove one adapter-owned staging path without following a symlink."""

    if not os.path.lexists(path):
        return
    if path.is_symlink() or not path.is_dir():
        path.unlink()
    else:
        shutil.rmtree(path)


def _patch_rule_resolution(path: Path) -> None:
    _apply_replacements(path, _RULE_REPLACEMENTS)


def _apply_replacements(path: Path, replacements: tuple[tuple[str, str, int], ...]) -> None:
    source = path.read_text(encoding="utf-8")
    for old, new, expected_count in replacements:
        actual_count = source.count(old)
        if actual_count != expected_count:
            raise ValueError(
                f"historical Eqlog compatibility source changed at {path}: "
                f"expected {expected_count} occurrence(s) of {old!r}, found {actual_count}"
            )
        source = source.replace(old, new)
    path.write_text(source, encoding="utf-8")


def _parse_args(argv: list[str] | None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--artifact-root", type=Path, required=True)
    parser.add_argument("--destination", type=Path, required=True)
    parser.add_argument("--kind", choices=("math", "eqlog"), required=True)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    """Stage one historical Rust source bundle for a recorded build hook."""

    args = _parse_args(argv)
    try:
        stage_rust_artifact(args.artifact_root, args.destination, args.kind)
        return 0
    except (OSError, ValueError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
