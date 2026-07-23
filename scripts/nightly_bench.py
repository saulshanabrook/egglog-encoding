#!/usr/bin/env python3
"""Generate the egglog-encoding nightly benchmark webpage.

Runs the public benchmark entrypoint (``bench.py``) over a benchmark suite and
writes eval-live's single-file interactive HTML report to
``nightly/output/index.html``. The egraphs-good nightly service
(``nightly.cs.washington.edu``) checks out this repository, runs ``make
nightly``, and serves that directory, matching ``report=`` in the nightly
configuration.

The output directory defaults to ``<repo>/nightly/output`` and may be
overridden with a single positional argument. Environment variables tune the
run without editing this script:

- ``NIGHTLY_ROUNDS``: rows per endpoint/file (default: bench.py's default).
- ``NIGHTLY_TIMEOUT_SEC``: per-process timeout in seconds.
- ``NIGHTLY_FILES``: shell-split benchmark files; empty selects bench.py's
  representative suite.
- ``NIGHTLY_FACT_DIRECTORY``: fact directory for the explicit ``NIGHTLY_FILES``.
"""

from __future__ import annotations

import os
import shlex
import subprocess
import sys
from collections.abc import Sequence
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
BENCH_SCRIPT = REPO_ROOT / "bench.py"
DEFAULT_OUTPUT_DIR = REPO_ROOT / "nightly" / "output"


def _optional_int_env(name: str) -> int | None:
    """Return a positive integer environment override, or None when unset."""

    raw = os.environ.get(name)
    if raw is None or raw.strip() == "":
        return None
    value = int(raw)
    if value <= 0:
        raise ValueError(f"{name} must be a positive integer, got {value}")
    return value


def _bench_command(output_dir: Path) -> list[str]:
    """Build the bench.py invocation that writes the interactive report."""

    report_path = output_dir / "index.jsonl"
    command = [sys.executable, str(BENCH_SCRIPT)]
    command.extend(shlex.split(os.environ.get("NIGHTLY_FILES", "")))
    fact_directory = os.environ.get("NIGHTLY_FACT_DIRECTORY", "").strip()
    if fact_directory:
        command.extend(("--fact-directory", fact_directory))
    command.extend(("--report", str(report_path), "--open"))
    rounds = _optional_int_env("NIGHTLY_ROUNDS")
    if rounds is not None:
        command.extend(("--rounds", str(rounds)))
    timeout_sec = _optional_int_env("NIGHTLY_TIMEOUT_SEC")
    if timeout_sec is not None:
        command.extend(("--timeout-sec", str(timeout_sec)))
    return command


def main(argv: Sequence[str] | None = None) -> int:
    """Run the benchmark suite and write ``<output_dir>/index.html``."""

    args = tuple(sys.argv[1:] if argv is None else argv)
    if len(args) > 1:
        print(f"usage: {Path(__file__).name} [output_dir]", file=sys.stderr)
        return 2
    output_dir = Path(args[0]).expanduser().resolve() if args else DEFAULT_OUTPUT_DIR
    output_dir.mkdir(parents=True, exist_ok=True)

    # Start each nightly from a clean slate so the page reflects a fresh
    # measurement of the current checkout rather than reused cached rows.
    report_path = output_dir / "index.jsonl"
    page_path = output_dir / "index.html"
    report_path.unlink(missing_ok=True)
    page_path.unlink(missing_ok=True)

    command = _bench_command(output_dir)
    # Neutralize bench.py's best-effort browser launch on headless nightly hosts.
    env = {**os.environ, "BROWSER": "true"}
    print(f"nightly: {' '.join(shlex.quote(part) for part in command)}", file=sys.stderr)
    result = subprocess.run(command, cwd=REPO_ROOT, env=env, check=False)
    if result.returncode != 0:
        print(f"nightly: bench.py exited with status {result.returncode}", file=sys.stderr)
        return result.returncode
    if not page_path.is_file():
        print(f"nightly: expected report was not written: {page_path}", file=sys.stderr)
        return 1
    print(f"nightly: wrote report to {page_path}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
