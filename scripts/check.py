#!/usr/bin/env python3
"""Run repository validation and paper builds; Make targets forward here."""

from __future__ import annotations

import argparse
import os
import re
import shlex
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PAPER_MODULES = (
    "EgglogSemantics.Spec.Syntax",
    "EgglogSemantics.Spec.Term",
    "EgglogSemantics.Spec.Database",
    "EgglogSemantics.Spec.Congruence",
    "EgglogSemantics.Spec.Eval",
    "EgglogSemantics.Spec.Match",
    "EgglogSemantics.Spec.Step",
    "EgglogSemantics.Spec.Divergence",
    "EgglogSemantics.Spec.Behavior",
    "EgglogSemantics.Spec.Order",
    "EgglogSemantics.Source.Domain",
    "EgglogSemantics.Source.WellFormed",
    "EgglogSemantics.Proofs.OrderFinite",
    "EgglogSemantics.Congruence.Correctness",
)


class Checks:
    def __init__(self, *, dry_run: bool = False) -> None:
        self.dry_run = dry_run
        self._done: set[str] = set()
        self._difftest_built = False
        self._rust_args = shlex.split(os.environ.get("RUST_TEST_ARGS", ""))
        self._lean_bin = self._path(os.environ.get("LEAN_BIN_DIR") or "~/.elan/bin")
        self._certificates = self._path(os.environ.get("LEAN_CERTIFICATES") or "/tmp/egglog-lean-certificates.json")

    @staticmethod
    def _path(value: str) -> Path:
        return (ROOT / Path(value).expanduser()).resolve()

    def __call__(self, target: str) -> None:
        if target not in self._done:
            getattr(self, target.replace("-", "_"))()
            self._done.add(target)

    def _group(self, *targets: str) -> None:
        for target in targets:
            self(target)

    def _run(self, *args: str, lean: bool = False, env: dict[str, str] | None = None) -> None:
        cwd = ROOT / "semantics" if lean else ROOT
        process_env = os.environ.copy()
        if lean:
            process_env["PATH"] = f"{self._lean_bin}{os.pathsep}{process_env.get('PATH', '')}"
        process_env.update(env or {})
        prefix = "semantics: " if lean else ""
        print(f"{prefix}{shlex.join(args)}", file=sys.stderr, flush=True)
        if not self.dry_run:
            subprocess.run(args, cwd=cwd, env=process_env, check=True)

    def _python(self, *args: str) -> None:
        self._run("uv", "run", "--locked", *args)

    def _lake(self, *args: str) -> None:
        self._run("lake", *args, lean=True)

    def _difftest(self, *args: str) -> None:
        if not self._difftest_built:
            self._lake("build", "difftest")
            self._difftest_built = True
        self._run(".lake/build/bin/difftest", *args, lean=True)

    def check(self) -> None:
        self._group("nits", "test")

    def nits(self) -> None:
        self._group("python-nits", "rust-nits")

    def test(self) -> None:
        self._group("python-test", "rust-test")
        self._run("cargo", "build", "-p", "egglog-experimental", "-p", "egraph-isomorphism", "--bins")
        self._run("cargo", "build", "--manifest-path", "slotted/xmulti/Cargo.toml")
        self._run("cargo", "test", "--manifest-path", "slotted/xmulti/Cargo.toml", "--", *self._rust_args)
        self._python("python", "slotted/checks/check-slotted.py")

    def python_check(self) -> None:
        self._group("python-nits", "python-test")

    def python_nits(self) -> None:
        self._group("python-lock", "python-format-check", "python-lint", "python-typecheck")

    def python_lock(self) -> None:
        self._run("uv", "lock", "--check")

    def python_format_check(self) -> None:
        self._python("ruff", "format", "--check", ".")

    def python_lint(self) -> None:
        self._python("ruff", "check", ".")

    def python_typecheck(self) -> None:
        self._python("mypy", ".")

    def python_test(self) -> None:
        self._python("pytest", "-q")

    def rust_check(self) -> None:
        self._group("rust-nits", "rust-test")

    def rust_nits(self) -> None:
        self._group("rust-format-check", "rust-clippy", "rust-doc-links")

    def rust_format_check(self) -> None:
        self._run("cargo", "fmt", "--all", "--", "--check")

    def rust_clippy(self) -> None:
        self._run("cargo", "clippy", "--workspace", "--all-targets", "--", "-D", "warnings")

    def rust_doc_links(self) -> None:
        self._run(
            "cargo", "doc", "--no-deps", "--document-private-items", "--workspace", env={"RUSTDOCFLAGS": "-D warnings"}
        )

    def rust_test(self) -> None:
        self._run("cargo", "test", "--workspace", "--", *self._rust_args)

    def proof_tests(self) -> None:
        self._run("cargo", "test", "--workspace", "--test", "files", "proofs/", "--", *self._rust_args)

    def lean_check(self) -> None:
        self._lake("build")
        print("Check Lean sources for proof holes", file=sys.stderr, flush=True)
        if not self.dry_run:
            holes = [
                f"{path.relative_to(ROOT)}:{line_no}: {line}"
                for path in sorted((ROOT / "semantics/EgglogSemantics").rglob("*.lean"))
                for line_no, line in enumerate(path.read_text().splitlines(), 1)
                if re.search(r"\bsorry\b", line) and "`sorry`" not in line
            ]
            if holes:
                raise RuntimeError("Lean proof holes:\n" + "\n".join(holes))
        self._group(
            "lean-congruence-test",
            "lean-provenance-test",
            "lean-resugar-test",
            "lean-egg-test",
            "lean-certificate-test",
        )

    def lean_congruence_test(self) -> None:
        self._difftest("congruence", "64")

    def lean_provenance_test(self) -> None:
        self._difftest("provenance", "64")

    def lean_resugar_test(self) -> None:
        self._difftest("resugar", "64")

    def lean_egg_test(self) -> None:
        self._difftest("egg", "64")

    def lean_update_egg_snapshots(self) -> None:
        self._difftest("egg", "64", "update")

    def lean_certificate_test(self) -> None:
        if not self.dry_run:
            self._certificates.parent.mkdir(parents=True, exist_ok=True)
        self._difftest("export-fixtures", str(self._certificates))
        self._run("cmp", str(self._certificates), "egglog/tests/lean-certificates.json")
        self._difftest("export-certificates", "64", str(self._certificates))
        self._run(
            "cargo",
            "test",
            "-p",
            "egglog",
            "--test",
            "lean_certificates",
            "--",
            *self._rust_args,
            env={"EGGLOG_LEAN_CERTIFICATES": str(self._certificates)},
        )

    def lean_update_fixtures(self) -> None:
        self._difftest("export-fixtures", "../egglog/tests/lean-certificates.json")

    def lean_difftest(self) -> None:
        self._run("./scripts/difftest.sh")

    def lean_compiled_difftest(self) -> None:
        self._run("./scripts/compiled-difftest.sh")

    def paper(self) -> None:
        self("paper-check")

    def paper_check(self) -> None:
        self("paper-extract")
        self._run(
            "latexmk",
            "-pdf",
            "-Werror",
            "-halt-on-error",
            "-interaction=nonstopmode",
            "-outdir=../paper/build",
            "../paper/semantics.tex",
            lean=True,
        )

    def paper_extract(self) -> None:
        self._lake("build", "EgglogPaper", *(f"{module}:blueprint" for module in PAPER_MODULES))
        self._lake(
            "env",
            ".lake/packages/LeanArchitect/.lake/build/bin/extract_blueprint",
            "index",
            "EgglogPaper",
            ",".join(PAPER_MODULES),
        )

    def update_snapshots(self) -> None:
        self._python("pytest", "-q", "--snapshot-update", "--snapshot-details")
        self._run(
            "cargo", "test", "-p", "egglog-experimental", "--test", "slotted_files", env={"INSTA_UPDATE": "always"}
        )

    def format(self) -> None:
        self._python("ruff", "format", ".")
        self._run("cargo", "fmt", "--all")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=__doc__,
        epilog="RUST_TEST_ARGS defaults to empty. LEAN_BIN_DIR and LEAN_CERTIFICATES accept repo-relative paths.",
    )
    targets = sorted(name.replace("_", "-") for name in vars(Checks) if not name.startswith("_"))
    parser.add_argument("targets", nargs="*", metavar="TARGET", help="default: check; choices: " + ", ".join(targets))
    parser.add_argument("--dry-run", action="store_true", help="show commands without executing them")
    args = parser.parse_args(argv)
    for target in args.targets:
        if target not in targets:
            parser.error(f"unknown target {target!r}")
    try:
        checks = Checks(dry_run=args.dry_run)
        for target in args.targets or ["check"]:
            checks(target)
    except subprocess.CalledProcessError as exc:
        return exc.returncode if exc.returncode >= 0 else 128 - exc.returncode
    except (OSError, RuntimeError, ValueError) as exc:
        print(f"check: {exc}", file=sys.stderr)
        return 1
    except KeyboardInterrupt:
        return 130
    return 0


if __name__ == "__main__":
    sys.exit(main())
