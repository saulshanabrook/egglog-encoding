#!/usr/bin/env python3
"""Generate the egglog-encoding nightly benchmark webpage.

Runs ``bench.py`` once per target and treatment into ``<output_dir>/index.jsonl``,
then re-renders that cache as the interactive page beside it. Both files are
replaced each run, so the cache never outlives the schema version that wrote it
and a failed run publishes no page.
"""

from __future__ import annotations

import argparse
import os
import shlex
import subprocess
import sys
from collections.abc import Sequence
from pathlib import Path

type Target = tuple[str, str]  # (label, source) for bench.py's label=source syntax
type Treatment = str

REPO_ROOT = Path(__file__).resolve().parents[1]
BENCH_SCRIPT = REPO_ROOT / "bench.py"
DEFAULT_OUTPUT_DIR = REPO_ROOT / "nightly" / "output"

# bench.py derives the page name from the cache name, so these two must match.
REPORT_NAME = "index.jsonl"
PAGE_NAME = "index.html"

# Checkouts to measure, each with a stable label so the dropdown shows which
# commit an endpoint belongs to. Endpoint identity is (binary, treatment), so a
# branch matching main byte-for-byte collapses to one endpoint per treatment;
# the two diverge once the code differs.
BRANCH: Target = ("branch", ".")
TARGETS: tuple[Target, ...] = (BRANCH, ("main", "@origin/main"))

# Treatments to measure.
TREATMENTS: tuple[Treatment, ...] = (
    "term",
    "proofs",
    "proof-extraction",
)

# Every endpoint is measured against ordinary mode on its own checkout, so the
# page opens on proof overhead of the branch.
BASELINE: Treatment = "off"
HEADLINE: Treatment = "proofs"

# The nightly host leaves rustup's shim directory off PATH, so cargo resolves to
# Ubuntu's, which predates rust-toolchain.toml's pin; only rustup honours that
# pin. Putting the shims first makes cargo fetch the pinned toolchain. `CARGO_HOME`
# follows the Makefile's CARGO_HOME_DIR, which is where it installs rustup.
CARGO_BIN_DIR = Path(os.environ.get("CARGO_HOME") or Path.home() / ".cargo") / "bin"


def _bench_env() -> dict[str, str]:
    """bench.py's environment: rustup's cargo first, and no browser launch."""

    # Prepend unconditionally: already being *somewhere* on PATH is not enough,
    # since a directory holding a distro cargo can precede it and still win.
    shims = str(CARGO_BIN_DIR)
    path = [entry for entry in os.environ.get("PATH", "").split(os.pathsep) if entry != shims]
    path.insert(0, shims)
    # Keep the headless nightly host from launching bench.py's best-effort browser.
    return {**os.environ, "PATH": os.pathsep.join(path), "BROWSER": "true"}


def _run(
    target: Target,
    treatment: Treatment,
    *,
    report_path: Path,
    open_report: bool,
    rounds: int | None,
) -> int:
    """Benchmark one endpoint against the baseline on the same checkout."""

    label, source = target
    command = [
        sys.executable,
        str(BENCH_SCRIPT),
        "--target",
        f"{label}={source}",
        "--treatment",
        treatment,
        "--compare-target",
        f"{label}={source}",
        "--compare-treatment",
        BASELINE,
        # This run's own cache, never the checkout-wide default one.
        "--report",
        str(report_path),
        # Per-file tables make a long run's progress legible.
        "--detail",
        "files",
        *(["--rounds", str(rounds)] if rounds is not None else []),
        *(["--open"] if open_report else []),
    ]
    print(f"nightly: {' '.join(shlex.quote(part) for part in command)}", file=sys.stderr)
    return subprocess.run(command, cwd=REPO_ROOT, env=_bench_env(), check=False).returncode


def _clear(output_dir: Path) -> None:
    """Drop what an earlier run published, leaving anything else in place."""

    output_dir.mkdir(parents=True, exist_ok=True)
    for name in (REPORT_NAME, PAGE_NAME):
        (output_dir / name).unlink(missing_ok=True)


def _positive_int(value: str) -> int:
    """Parse ``--rounds``, which bench.py also requires to be positive."""

    parsed = int(value)
    if parsed <= 0:
        raise argparse.ArgumentTypeError("must be positive")
    return parsed


def main(argv: Sequence[str] | None = None) -> int:
    """Measure into ``<output_dir>/index.jsonl`` and render ``index.html`` beside it."""

    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument(
        "output_dir",
        nargs="?",
        type=Path,
        default=DEFAULT_OUTPUT_DIR,
        help="directory to publish index.html and index.jsonl into",
    )
    parser.add_argument(
        "--rounds",
        type=_positive_int,
        help="rounds per endpoint/file, passed to bench.py",
    )
    args = parser.parse_args(list(argv) if argv is not None else None)
    output_dir = args.output_dir.expanduser().resolve()
    _clear(output_dir)
    report_path = output_dir / REPORT_NAME

    # Populate the dropdown with every endpoint. A combination that fails to
    # build or run drops one option instead of failing the whole nightly.
    for target in TARGETS:
        for treatment in TREATMENTS:
            if _run(target, treatment, report_path=report_path, open_report=False, rounds=args.rounds) != 0:
                print(f"nightly: skipped {target[0]} {treatment}", file=sys.stderr)

    # The whole cache is now populated, so this last run re-renders it as the
    # page. Its rows are already cached, so it only rebuilds the report.
    rendered = _run(BRANCH, HEADLINE, report_path=report_path, open_report=True, rounds=args.rounds) == 0
    if not rendered or not (output_dir / PAGE_NAME).is_file():
        print("nightly: benchmark did not produce a report", file=sys.stderr)
        return 1
    print(f"nightly: wrote report to {output_dir / PAGE_NAME}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
