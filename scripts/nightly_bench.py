#!/usr/bin/env python3
"""Generate the egglog-encoding nightly benchmark webpage.

Runs the public benchmark entrypoint (``bench.py``) once per available
backend/treatment endpoint, on the current checkout and on the latest ``main``,
accumulating every endpoint in one report cache. eval-live's interactive report
discovers its dropdown from every cached endpoint, so the page can compare any
two of them. Each endpoint is labelled by target (``branch`` / ``main``) and
commit hash, so it is clear which commit each side is.

The page opens on branch-vs-main proof mode (both commit hashes side by side);
when the two checkouts share a binary — identical code — that comparison is
degenerate, so it falls back to proof overhead (``proofs`` vs ``off``) on the
branch. The page is written to ``nightly/output/index.html`` with the raw cache
beside it as ``index.jsonl``.

The egraphs-good nightly service (``nightly.cs.washington.edu``) checks out this
repository, runs ``make nightly``, and serves that directory, matching
``report=`` in the nightly configuration.

The output directory defaults to ``<repo>/nightly/output`` and may be overridden
with a single positional argument.
"""

from __future__ import annotations

import os
import shlex
import subprocess
import sys
from collections.abc import Sequence
from pathlib import Path

type Target = tuple[str, str]  # (label, source) for bench.py's label=source syntax
type Endpoint = tuple[str, str]  # (backend, treatment)
type Selection = tuple[Target, Endpoint]

REPO_ROOT = Path(__file__).resolve().parents[1]
BENCH_SCRIPT = REPO_ROOT / "bench.py"
DEFAULT_OUTPUT_DIR = REPO_ROOT / "nightly" / "output"

# Checkouts whose endpoints populate the report, each with a stable label so the
# dropdown shows which commit an endpoint belongs to. Endpoint identity is
# (binary, backend, treatment), so a branch that matches main byte-for-byte
# collapses to one endpoint per config; the two diverge once the code differs.
BRANCH: Target = ("branch", ".")
MAIN: Target = ("main", "@origin/main")
TARGETS: tuple[Target, ...] = (BRANCH, MAIN)

# Every backend/treatment endpoint bench.py can run: the dd backend runs only
# term and proofs, and proof-extraction is main-only.
ENDPOINTS: tuple[Endpoint, ...] = (
    ("main", "off"),
    ("main", "term"),
    ("main", "proofs"),
    ("main", "proof-extraction"),
    ("dd", "term"),
    ("dd", "proofs"),
)

# Baseline every endpoint is measured against.
BASELINE: Endpoint = ("main", "off")

# The comparison the page opens on, best match first. Branch vs main at equal
# treatment shows both commit hashes at once; it is rejected when the two share
# a binary, so fall back to proof overhead on the branch.
HEADLINE_CANDIDATE: Selection = (BRANCH, ("main", "proofs"))
HEADLINE_BASELINES: tuple[Selection, ...] = (
    (MAIN, ("main", "proofs")),
    (BRANCH, BASELINE),
)


def _command(report_path: Path, candidate: Selection, baseline: Selection, *, open_report: bool) -> list[str]:
    """Build the bench.py comparison of candidate vs baseline."""

    (cand_label, cand_source), (cand_backend, cand_treatment) = candidate
    (base_label, base_source), (base_backend, base_treatment) = baseline
    command = [
        sys.executable,
        str(BENCH_SCRIPT),
        "--target",
        f"{cand_label}={cand_source}",
        "--backend",
        cand_backend,
        "--treatment",
        cand_treatment,
        "--compare-target",
        f"{base_label}={base_source}",
        "--compare-backend",
        base_backend,
        "--compare-treatment",
        base_treatment,
        "--report",
        str(report_path),
    ]
    if open_report:
        command.append("--open")
    return command


def _run(command: list[str], env: dict[str, str]) -> int:
    """Run one bench.py comparison, streaming its output, and return its status."""

    print(f"nightly: {' '.join(shlex.quote(part) for part in command)}", file=sys.stderr)
    return subprocess.run(command, cwd=REPO_ROOT, env=env, check=False).returncode


def main(argv: Sequence[str] | None = None) -> int:
    """Populate the endpoint cache and write ``<output_dir>/index.html``."""

    args = tuple(sys.argv[1:] if argv is None else argv)
    if len(args) > 1:
        print(f"usage: {Path(__file__).name} [output_dir]", file=sys.stderr)
        return 2
    output_dir = Path(args[0]).expanduser().resolve() if args else DEFAULT_OUTPUT_DIR
    output_dir.mkdir(parents=True, exist_ok=True)
    report_path = output_dir / "index.jsonl"
    page_path = output_dir / "index.html"

    # Start from fresh data, but leave any previous page in place: --open
    # overwrites index.html atomically only on success, so a failed run keeps
    # the last good page.
    report_path.unlink(missing_ok=True)

    # Neutralize bench.py's best-effort browser launch on headless nightly hosts.
    env = {**os.environ, "BROWSER": "true"}

    # Populate the cache with every endpoint. This is best effort: a combination
    # that fails to build or run just drops one dropdown option instead of
    # failing the whole nightly.
    for target in TARGETS:
        for endpoint in ENDPOINTS:
            if endpoint == BASELINE:
                continue  # cached as the compare side of every other endpoint
            status = _run(_command(report_path, (target, endpoint), (target, BASELINE), open_report=False), env)
            if status != 0:
                print(f"nightly: skipped {target[0]} {endpoint[0]}/{endpoint[1]} (exit {status})", file=sys.stderr)

    # Render the page, opening on the first headline comparison that succeeds.
    for baseline in HEADLINE_BASELINES:
        status = _run(_command(report_path, HEADLINE_CANDIDATE, baseline, open_report=True), env)
        if status == 0 and page_path.is_file():
            print(f"nightly: wrote report to {page_path}", file=sys.stderr)
            return 0
        (base_label, _source), (backend, treatment) = baseline
        print(f"nightly: headline vs {base_label} {backend}/{treatment} unavailable (exit {status})", file=sys.stderr)
    print("nightly: no headline comparison produced a report", file=sys.stderr)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
