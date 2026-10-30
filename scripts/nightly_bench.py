#!/usr/bin/env python3
"""Run the nightly within one budget, including bootstrap and partial rendering.

The supervisor needs only host Python 3.8+ and the standard library. Project
imports occur in uv's Python 3.12 worker after bounded tool bootstrap.
"""

from __future__ import annotations

import argparse
import json
import os
import shutil
import signal
import subprocess
import sys
import time
from collections.abc import Sequence
from contextlib import suppress
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_OUTPUT_DIR = REPO_ROOT / "nightly/output"
REPORT_NAME = "index.jsonl"
PAGE_NAME = "index.html"
STATE_NAME = "nightly-context.json"
STATUS_NAME = "status.txt"
DEFAULT_BUDGET_SEC = 7200
RENDER_RESERVE_SEC = 120
CLEANUP_RESERVE_SEC = 5
BOOTSTRAP_COMMAND = ("make", "nightly-uv", "nightly-rustup")
TARGETS = (("branch", "."), ("main", "@origin/main"))
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


def _bench_env() -> dict[str, str]:
    """Use rustup's cargo on the nightly host."""
    shims = str(Path(os.environ.get("CARGO_HOME") or Path.home() / ".cargo") / "bin")
    path = [entry for entry in os.environ.get("PATH", "").split(os.pathsep) if entry != shims]
    return {**os.environ, "PATH": os.pathsep.join((shims, *path))}


def _run_phase(command: Sequence[str], deadline: float, env: dict[str, str]) -> int:
    """Bound an owned phase group, including exceptional and interrupted exits."""
    remaining = deadline - time.monotonic()
    if remaining <= 0:
        raise subprocess.TimeoutExpired(list(command), 0)
    process = subprocess.Popen(command, cwd=REPO_ROOT, env=env, start_new_session=True)
    try:
        return process.wait(timeout=max(0, deadline - time.monotonic()))
    except subprocess.TimeoutExpired:
        # The owner deadline already expired before this hard phase bound.
        raise
    except BaseException:
        # Give the collection owner a bounded chance to reap commands in their
        # separate sessions when the job is cancelled before its deadline.
        with suppress(ProcessLookupError):
            os.killpg(process.pid, signal.SIGTERM)
        with suppress(subprocess.TimeoutExpired):
            process.wait(timeout=max(0, min(CLEANUP_RESERVE_SEC, deadline - time.monotonic())))
        raise
    finally:
        # Collection's separately-sessioned commands have their own earlier
        # deadline and cleanup; this final bound also covers uv and rendering.
        with suppress(ProcessLookupError):
            os.killpg(process.pid, signal.SIGKILL)
        process.wait()


def _worker_command(args: argparse.Namespace, phase: str, deadline: float) -> list[str]:
    """Enter the pinned project environment with the same absolute deadline."""
    uv = os.environ.get("NIGHTLY_UV") or shutil.which("uv") or str(REPO_ROOT / ".uv/0.11.30/uv")
    return [
        uv,
        "run",
        "--python",
        "3.12",
        "--locked",
        "python",
        str(Path(__file__).resolve()),
        str(args.output_dir),
        "--worker",
        phase,
        "--deadline",
        str(deadline),
        "--rounds",
        str(args.rounds),
        "--timeout-sec",
        str(args.timeout_sec),
    ]


def _collect(args: argparse.Namespace) -> int:
    """Collect the four endpoints; persist exact context even after a fatal stop."""
    from dataclasses import asdict

    from rich.console import Console

    from benchmarking.collection import (
        BenchmarkRequest,
        collect_rows,
        emit_collection_plan,
        plan_collection,
        preflight_collection,
        resolve_requests,
    )
    from benchmarking.engines import Treatment
    from benchmarking.models import EndpointRequest
    from benchmarking.processes import COLLECTION_DEADLINE
    from benchmarking.reports.grouped import grouped_report_path, write_grouped_report
    from benchmarking.reports.store import ReportStore
    from benchmarking.targets import parse_target, run_text
    from benchmarking.workloads import resolve_files

    console = Console(stderr=True)
    report = args.output_dir / REPORT_NAME
    store = ReportStore(report)
    files = resolve_files(WORKLOADS, REPO_ROOT, None)
    context: dict[str, Any] = {
        "targets": {},
        "files": [
            {"display_path": f.display_path, "absolute_path": str(f.absolute_path), "sha256": f.sha256} for f in files
        ],
        "rounds": args.rounds,
        "timeout_sec": args.timeout_sec,
    }
    token = COLLECTION_DEADLINE.set(args.deadline)
    treatments: tuple[Treatment, ...] = ("off", "proof-testing")
    failed = False
    try:
        # Finish branch observations before attempting an older main that may
        # reject the native limit. Setup/control failures halt all later work.
        for label, source in TARGETS:
            if label == "main":
                run_text(
                    ["git", "fetch", "origin", "+refs/heads/main:refs/remotes/origin/main"],
                    REPO_ROOT,
                    capture_output=False,
                )
            request = parse_target(f"{label}={source}")
            requests = tuple(BenchmarkRequest(EndpointRequest(request, treatment), files) for treatment in treatments)
            resolved_targets = resolve_requests(
                requests,
                store,
                args.rounds,
                args.timeout_sec,
                False,
                REPO_ROOT,
                REPO_ROOT,
                console,
            )
            target = resolved_targets[request]
            context["targets"][label] = {
                "request": asdict(target.request),
                "row": asdict(target.row),
                "binary_sha256": target.binary_sha256_for("off"),
            }
            (plan,) = plan_collection(
                store,
                requests,
                resolved_targets,
                args.rounds,
                args.timeout_sec,
                False,
            )
            preflight_collection(plan, args.timeout_sec)
            emit_collection_plan(console, plan)
            collect_rows(store, plan, args.timeout_sec, console)
    except (OSError, ValueError, RuntimeError, subprocess.SubprocessError) as error:
        failed = True
        with (args.output_dir / STATUS_NAME).open("a") as status:
            status.write(f"Partial nightly: {error}\n")
    finally:
        COLLECTION_DEADLINE.reset(token)
        write_grouped_report(store.grouped_report(), grouped_report_path(report))
        temporary = args.output_dir / (STATE_NAME + ".tmp")
        temporary.write_text(json.dumps(context, indent=2) + "\n")
        temporary.replace(args.output_dir / STATE_NAME)
    return int(failed)


def _render(args: argparse.Namespace) -> int:
    """Render the saved snapshot without resolving targets or collecting rows."""
    from benchmarking.models import (
        BenchmarkEndpoint,
        ComparisonSpec,
        FileSpec,
        ResolvedTarget,
        TargetRequest,
        TargetRow,
    )
    from benchmarking.reports.interactive import write_interactive_report
    from benchmarking.reports.presentation import build_report_catalog
    from benchmarking.reports.render import render_markdown_report_document
    from benchmarking.reports.store import ReportStore

    context = json.loads((args.output_dir / STATE_NAME).read_text())
    targets = {
        label: ResolvedTarget(
            request=TargetRequest(**saved["request"]),
            row=TargetRow(**saved["row"]),
            binary_sha256=saved["binary_sha256"],
            binary_path=None,
            primary_engine="egglog",
        )
        for label, saved in context["targets"].items()
    }
    if not targets:
        return 1
    files = tuple(FileSpec(row["display_path"], Path(row["absolute_path"]), row["sha256"]) for row in context["files"])
    grouped = ReportStore(args.output_dir / REPORT_NAME).grouped_report()
    target = targets["branch"]
    comparison = ComparisonSpec(
        BenchmarkEndpoint(target, "off"),
        BenchmarkEndpoint(target, "proof-testing"),
        files,
        context["rounds"],
        context["timeout_sec"],
    )
    available = {(row["binary_sha256"], row["treatment"], row["disequality_encoding"]) for row in grouped.records}
    if comparison.baseline.cache_identity in available and comparison.candidate.cache_identity in available:
        write_interactive_report(grouped, comparison, args.output_dir / PAGE_NAME)
    else:
        import html

        # The merged interactive runtime requires both endpoint choices. A
        # partial job still gets the ordinary report's explicit missing cells.
        text = render_markdown_report_document(build_report_catalog(grouped, comparison, "files"))
        temporary = args.output_dir / (PAGE_NAME + ".tmp")
        temporary.write_text(
            "<!doctype html><meta charset=utf-8><title>Partial nightly</title><pre>" + html.escape(text) + "</pre>\n"
        )
        temporary.replace(args.output_dir / PAGE_NAME)
    if "branch" in targets and "main" in targets:
        if targets["branch"].binary_sha256 == targets["main"].binary_sha256:
            text = "Branch and main use the same executable; their checked observations are shared.\n"
        else:
            comparison = ComparisonSpec(
                BenchmarkEndpoint(targets["main"], "proof-testing"),
                BenchmarkEndpoint(targets["branch"], "proof-testing"),
                files,
                context["rounds"],
                context["timeout_sec"],
            )
            text = render_markdown_report_document(build_report_catalog(grouped, comparison, "files")) + "\n"
        (args.output_dir / "branch-vs-main.md").write_text(text)
    return 0


def main(argv: Sequence[str] | None = None) -> int:
    """Supervise bootstrap, collection and cache-only rendering under one clock."""
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("output_dir", nargs="?", type=Path, default=DEFAULT_OUTPUT_DIR)
    parser.add_argument("--rounds", type=_positive_int, default=1)
    parser.add_argument("--timeout-sec", type=_positive_int, default=120)
    parser.add_argument("--budget-sec", type=_positive_int, default=DEFAULT_BUDGET_SEC)
    parser.add_argument("--worker", choices=("collect", "render"), help=argparse.SUPPRESS)
    parser.add_argument("--deadline", type=float, help=argparse.SUPPRESS)
    args = parser.parse_args(list(argv) if argv is not None else None)
    args.output_dir = args.output_dir.expanduser().resolve()
    if args.worker:
        if args.deadline is None:
            parser.error("worker requires the supervisor deadline")
        sys.path.insert(0, str(REPO_ROOT))
        return _collect(args) if args.worker == "collect" else _render(args)
    if sys.version_info < (3, 8):  # noqa: UP036 - supervisor runs outside the project's Python 3.12 environment
        parser.error("nightly supervisor requires host Python 3.8 or newer")
    if not RENDER_RESERVE_SEC + CLEANUP_RESERVE_SEC < args.budget_sec <= DEFAULT_BUDGET_SEC:
        parser.error(f"--budget-sec must exceed cleanup/render reserves and be at most {DEFAULT_BUDGET_SEC}")
    started = time.monotonic()
    deadline = started + args.budget_sec
    collection_deadline = deadline - RENDER_RESERVE_SEC - CLEANUP_RESERVE_SEC
    args.output_dir.mkdir(parents=True, exist_ok=True)
    for name in (REPORT_NAME, "index-grouped.json", PAGE_NAME, STATE_NAME, STATUS_NAME, "branch-vs-main.md"):
        (args.output_dir / name).unlink(missing_ok=True)
    (args.output_dir / STATUS_NAME).write_text("Nightly started; checked proofs versus off.\n")
    fallback = args.output_dir / PAGE_NAME
    fallback.write_text(
        "<!doctype html><meta charset=utf-8><title>Nightly status</title>"
        '<p>Nightly is incomplete. See <a href="status.txt">status.txt</a>'
        " and retained index.jsonl.</p>\n"
    )
    env = _bench_env()
    failed = False
    try:
        code = _run_phase(BOOTSTRAP_COMMAND, collection_deadline, env)
        if code:
            raise RuntimeError(f"tool bootstrap failed with status {code}")
        code = _run_phase(_worker_command(args, "collect", collection_deadline), deadline - RENDER_RESERVE_SEC, env)
        if code:
            raise RuntimeError(f"collection worker exited with status {code}")
    except (OSError, RuntimeError, subprocess.SubprocessError) as error:
        failed = True
        with (args.output_dir / STATUS_NAME).open("a") as status:
            status.write(f"Partial nightly: {error}\n")
    if (args.output_dir / STATE_NAME).is_file():
        try:
            code = _run_phase(_worker_command(args, "render", deadline), deadline, env)
            if code:
                raise RuntimeError(f"render worker exited with status {code}")
        except (OSError, RuntimeError, subprocess.SubprocessError) as error:
            failed = True
            with (args.output_dir / STATUS_NAME).open("a") as status:
                status.write(f"Rendering stopped: {error}\n")
    print(f"nightly: wrote {fallback}", file=sys.stderr)
    return int(failed)


if __name__ == "__main__":

    def interrupted(_signal: int, _frame: Any) -> None:
        raise KeyboardInterrupt

    signal.signal(signal.SIGTERM, interrupted)
    raise SystemExit(main())
