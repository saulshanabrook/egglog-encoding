#!/usr/bin/env python3
"""Collect checked/off nightly comparisons and publish reports from their cache."""

from __future__ import annotations

import argparse
import html
import os
import subprocess
import sys
from collections.abc import Sequence
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from rich.console import Console

from benchmarking import collection, targets, workloads
from benchmarking.engines import Treatment
from benchmarking.models import BenchmarkEndpoint, ComparisonSpec, EndpointRequest, FileSpec, ResolvedTarget
from benchmarking.reports.grouped import grouped_report_path, write_grouped_report
from benchmarking.reports.interactive import write_interactive_report
from benchmarking.reports.presentation import build_report_catalog
from benchmarking.reports.render import render_markdown_report_document
from benchmarking.reports.store import GroupedReport, ReportStore

REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_OUTPUT_DIR = REPO_ROOT / "nightly/output"
REPORT_NAME = "index.jsonl"
PAGE_NAME = "index.html"
STATUS_NAME = "status.txt"
TARGETS = (("branch", "."), ("main", "@origin/main"))
TREATMENTS: tuple[Treatment, ...] = ("off", "proof-testing")
WORKLOADS = (
    "egglog-experimental/tests/math-microbenchmark-rational.egg",
    "egglog-experimental/tests/fixtures/eggcc-2mm-pass1.egg",
    "egglog/tests/hardboiled_conv1d_32.egg",
    "egglog/tests/luminal-llama.egg",
    "egglog/tests/papers/misaal-hvx-dot-product.egg",
    "egglog/tests/papers/churchroad-wide-multiply.egg",
    "egglog-experimental/tests/papers/dialegg-nmm40.egg",
)


def _positive_int(value: str) -> int:
    parsed = int(value)
    if parsed <= 0:
        raise argparse.ArgumentTypeError("must be positive")
    return parsed


def _render(
    args: argparse.Namespace,
    grouped: GroupedReport,
    resolved_targets: dict[str, ResolvedTarget],
    files: tuple[FileSpec, ...],
) -> None:
    """Render the collected snapshot without resolving targets or collecting rows."""
    target = resolved_targets["branch"]
    comparison = ComparisonSpec(
        BenchmarkEndpoint(target, "off"),
        BenchmarkEndpoint(target, "proof-testing"),
        files,
        args.rounds,
        args.timeout_sec,
    )
    available = {(row["binary_sha256"], row["treatment"], row["disequality_encoding"]) for row in grouped.records}
    if comparison.baseline.cache_identity in available and comparison.candidate.cache_identity in available:
        write_interactive_report(grouped, comparison, args.output_dir / PAGE_NAME)
    else:
        # The interactive runtime requires both endpoint choices. A partial job
        # still gets the ordinary report's explicit missing cells.
        text = render_markdown_report_document(build_report_catalog(grouped, comparison, "files"))
        temporary = args.output_dir / (PAGE_NAME + ".tmp")
        temporary.write_text(
            "<!doctype html><meta charset=utf-8><title>Partial nightly</title><pre>" + html.escape(text) + "</pre>\n"
        )
        temporary.replace(args.output_dir / PAGE_NAME)
    if "main" in resolved_targets:
        if target.binary_sha256 == resolved_targets["main"].binary_sha256:
            text = "Branch and main use the same executable; their checked observations are shared.\n"
        else:
            comparison = ComparisonSpec(
                BenchmarkEndpoint(resolved_targets["main"], "proof-testing"),
                BenchmarkEndpoint(target, "proof-testing"),
                files,
                args.rounds,
                args.timeout_sec,
            )
            text = render_markdown_report_document(build_report_catalog(grouped, comparison, "files")) + "\n"
        (args.output_dir / "branch-vs-main.md").write_text(text)


def main(argv: Sequence[str] | None = None) -> int:
    """Collect the four endpoints, then render completed and partial results."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output_dir", nargs="?", type=Path, default=DEFAULT_OUTPUT_DIR)
    parser.add_argument("--rounds", type=_positive_int, default=1)
    parser.add_argument("--timeout-sec", type=_positive_int, default=120)
    args = parser.parse_args(list(argv) if argv is not None else None)
    args.output_dir = args.output_dir.expanduser().resolve()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    for name in (REPORT_NAME, "index-grouped.json", PAGE_NAME, STATUS_NAME, "branch-vs-main.md"):
        (args.output_dir / name).unlink(missing_ok=True)
    status_path = args.output_dir / STATUS_NAME
    status_path.write_text("Nightly started; checked proofs versus off.\n")
    page_path = args.output_dir / PAGE_NAME
    page_path.write_text(
        "<!doctype html><meta charset=utf-8><title>Nightly status</title>"
        '<p>Nightly is incomplete. See <a href="status.txt">status.txt</a>'
        " and retained index.jsonl.</p>\n"
    )
    # The nightly host leaves rustup's shims off PATH; its distro cargo cannot
    # honor the repository's pinned toolchain.
    shims = str(Path(os.environ.get("CARGO_HOME") or Path.home() / ".cargo") / "bin")
    os.environ["PATH"] = os.pathsep.join(
        (shims, *(entry for entry in os.environ.get("PATH", "").split(os.pathsep) if entry != shims))
    )
    console = Console(stderr=True)
    report = args.output_dir / REPORT_NAME
    store = ReportStore(report)
    resolved_targets: dict[str, ResolvedTarget] = {}
    files: tuple[FileSpec, ...] = ()
    failed = False
    try:
        files = workloads.resolve_files(WORKLOADS, REPO_ROOT, None)
        # Preserve branch observations before an older main can reject setup.
        for label, source in TARGETS:
            if label == "main":
                targets.run_text(["git", "fetch", "origin", "+refs/heads/main:refs/remotes/origin/main"], REPO_ROOT)
            request = targets.parse_target(f"{label}={source}")
            requests = tuple(collection.BenchmarkRequest(EndpointRequest(request, mode), files) for mode in TREATMENTS)
            resolved = collection.resolve_requests(
                requests, store, args.rounds, args.timeout_sec, False, REPO_ROOT, REPO_ROOT, console
            )
            resolved_targets[label] = resolved[request]
            plans = collection.plan_collection(store, requests, resolved, args.rounds, args.timeout_sec, False)
            collection.collect(store, plans, requests, resolved, args.timeout_sec, console)
    except (OSError, ValueError, RuntimeError, subprocess.SubprocessError) as error:
        failed = True
        with status_path.open("a") as status:
            status.write(f"Partial nightly: {error}\n")
    try:
        grouped = store.grouped_report(
            {(label, "egglog"): target.binary_sha256_for("off") for label, target in resolved_targets.items()}
        )
        write_grouped_report(grouped, grouped_report_path(report))
        if resolved_targets:
            _render(args, grouped, resolved_targets, files)
    except (OSError, ValueError, RuntimeError, subprocess.SubprocessError) as error:
        failed = True
        with status_path.open("a") as status:
            status.write(f"Rendering stopped: {error}\n")
    print(f"nightly: wrote {page_path}", file=sys.stderr)
    return int(failed)


if __name__ == "__main__":
    raise SystemExit(main())
