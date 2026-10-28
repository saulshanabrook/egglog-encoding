"""Build and time the two executables. Graph export and checking live in verify."""

import argparse
import multiprocessing
import os
import signal
import subprocess
import sys
import threading
import time
from dataclasses import dataclass, field
from pathlib import Path

from slotted.treatments import SIDES, TREATMENTS, description
from slotted.workloads import add_arguments, workload_label

ROOT = Path(__file__).resolve().parents[1]
SCRATCH = ROOT / "target" / "slotted"

#: Release builds of both sides: egglog, and the reference through `xmulti` without the
#: crate's `checks` feature, the way the paper's experiments ran it.
EGGLOG = ROOT / "target" / "release" / "egglog-experimental"
#: Maximum actual symmetries exported per reference class, including identity.
#: Wide classes with small groups remain cheap; exceeding this limit makes the
#: comparison inconclusive while preserving direct class/node counts.
GROUP_LIMIT = 100_000
XMULTI = ROOT / "slotted" / "xmulti" / "target" / "release" / "xmulti"
BUILDS = (
    ("cargo", "build", "--release", "-p", "egglog-experimental"),
    ("cargo", "build", "--release", "--no-default-features", "--manifest-path", "slotted/xmulti/Cargo.toml"),
)


@dataclass(eq=False)
class Row:
    study: str
    case: str
    side: str
    rounds: int
    rules: int | None = None
    goal: str = "?"
    saturated: str = "?"
    seconds: float | None = None
    classes: int | None = None
    nodes: int | None = None
    checks: str | None = None
    substitution: str | None = None
    unsupported: dict[str, str] = field(default_factory=dict)
    vs_ref: dict = field(default_factory=dict, repr=False)
    graph: object = field(default=None, repr=False)
    graph_issue: str | None = None

    def workload(self):
        return self.study, self.case, self.rounds, self.rules

    def verdict(self, reference):
        if reference is None:
            return "inconclusive: reference observation unavailable"
        comparison = self.vs_ref.get(reference.side)
        if comparison is None or comparison.encoding is not self or comparison.reference is not reference:
            return "inconclusive: selected observations have not been compared"
        return comparison.verdict

    def as_dict(self):
        return {
            **{key: value for key, value in vars(self).items() if key not in ("graph", "vs_ref")},
            "vs_ref": {side: comparison.verdict for side, comparison in self.vs_ref.items()},
        }


@dataclass(frozen=True)
class Config:
    egglog: Path = EGGLOG
    xmulti: Path = XMULTI
    group_limit: int = GROUP_LIMIT
    checker: Path = ROOT / "target/release/egraph-isomorphism"


def quiet_progress(row, phase):
    """Library callers collect observations without displaying CLI progress."""


class Progress:
    """One dot per sample; identify a phase only when it takes more than five seconds.

    Timer callbacks only print to stderr. Cancel and join before changing the display
    so a completed phase cannot report itself as still running.
    """

    delay = 5

    def __init__(self, parallel=False):
        self.timer = None
        self.workload = None
        self.line_open = False
        self.parallel = parallel

    def __enter__(self):
        return self

    def cancel(self):
        if self.timer is not None:
            self.timer.cancel()
            self.timer.join()
            self.timer = None

    def __exit__(self, *_):
        self.cancel()
        if self.line_open:
            print(file=sys.stderr, flush=True)

    def __call__(self, row, phase):
        self.cancel()
        if phase == "idle":
            return
        label = workload_label(row.study, row.case, row.rules)
        if self.parallel and phase == "done":
            print(".", end="", file=sys.stderr, flush=True)
            return
        if not self.parallel and row.workload() != self.workload:
            if self.line_open:
                print(file=sys.stderr)
            print(f"{label}: ", end="", file=sys.stderr, flush=True)
            self.workload, self.line_open = row.workload(), True
        if phase == "done":
            print("." if self.line_open else "  .", end="", file=sys.stderr, flush=True)
            self.line_open = True
            return

        def slow():
            if self.parallel:
                # Write a complete, short message at once so workers' text does not
                # interleave inside a message. Dots may arrive between messages.
                sys.stderr.write(f"\n  {label} / {row.side}: {phase} (Running ...)\n")
                sys.stderr.flush()
                return
            if self.line_open:
                print(file=sys.stderr)
            print(f"  {label} / {row.side}: {phase} (Running ...)", file=sys.stderr, flush=True)
            self.line_open = False

        self.timer = threading.Timer(self.delay, slow)
        self.timer.daemon = True
        self.timer.start()


def build(*, env=None):
    """Bring both binaries up to date, so a timing is of the code in the checkout.
    cargo's own output stays on stderr."""
    for cmd in BUILDS:
        subprocess.run(cmd, cwd=ROOT, stdout=sys.stderr, env=env, check=True)


def oracle_env(side, group_limit):
    """Use the selected substitution policy without reference debugging overhead."""
    return {
        **{
            key: value
            for key, value in os.environ.items()
            if key not in ("XMULTI_DEBUG", "XMULTI_DEBUG_RULE", "XMULTI_TRACE")
        },
        "XMULTI_GROUP_LIMIT": str(group_limit),
        "XMULTI_SUBST": TREATMENTS[side].substitution,
    }


def run_reference(spec, row, timeout, progress=quiet_progress, *, config=None):
    """Time the reference goal check with an explicit substitution policy."""
    config = config or Config()
    env = oracle_env(row.side, config.group_limit)
    row.substitution = env["XMULTI_SUBST"]
    progress(row, "goal")
    t0 = time.perf_counter()
    try:
        r = subprocess.run([str(config.xmulti)], input=spec, capture_output=True, text=True, timeout=timeout, env=env)
    except subprocess.TimeoutExpired:
        row.goal, row.seconds = "timeout", time.perf_counter() - t0
        row.graph_issue = "reference timed run exceeded timeout"
        return
    row.seconds = time.perf_counter() - t0
    lines = r.stdout.splitlines()
    if r.returncode != 0 and "REFERENCE_LIMIT:" not in r.stderr:
        row.goal = "error: " + ((r.stderr.strip().splitlines() or ["?"])[-1])[:80]
        row.graph_issue = row.goal
        return
    row.goal = next((ln.split()[1] for ln in lines if ln.startswith("GOAL ")), "?")
    row.saturated = next((ln.split()[1] for ln in lines if ln.startswith("SATURATED ")), "?")
    row.checks = next((ln.split("=", 1)[1] for ln in lines if ln.startswith("CONFIG checks=")), None)
    reported_subst = next((ln.split("=", 1)[1] for ln in lines if ln.startswith("CONFIG substitution=")), None)
    if reported_subst != row.substitution:
        row.goal = "error: reference substitution policy missing or unexpected; rebuild xmulti"
        row.graph_issue = row.goal
        return


def slotted_flags(row):
    return TREATMENTS[row.side].flags


def goal_result(result):
    if result.returncode == 0:
        return "yes"
    return "no" if "Check failed" in result.stderr else "error"


def run_egglog(program, name, row, timeout, progress=quiet_progress, *, config=None):
    """Time source transformation, execution, and the goal check in one process."""
    config = config or Config()
    SCRATCH.mkdir(parents=True, exist_ok=True)
    path = SCRATCH / f"eval-{name}-{os.getpid()}.egg"
    path.write_text(program)
    progress(row, "goal")
    t0 = time.perf_counter()
    try:
        r = subprocess.run(
            [str(config.egglog), *slotted_flags(row), str(path)],
            capture_output=True,
            text=True,
            cwd=ROOT,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired:
        row.goal, row.seconds = "timeout", time.perf_counter() - t0
        return
    finally:
        path.unlink(missing_ok=True)
    row.seconds = time.perf_counter() - t0
    row.goal = goal_result(r)


def run(workload, side, timeout, progress=quiet_progress, *, config=None):
    """Execute the same goal-checking program for benchmarking and testing."""
    row = Row(workload.study, workload.case, side, workload.rounds, workload.rules)
    row.unsupported = workload.unsupported
    if TREATMENTS[side].engine == "reference":
        run_reference(workload.reference(side), row, timeout, progress, config=config)
    else:
        run_egglog(workload.program, workload.case, row, timeout, progress, config=config)
    return row


def goal_errors(rows):
    return [
        f"{row.case} / {row.side}: goal not reached ({row.goal})"
        for row in rows
        if row.goal != "yes" and not (TREATMENTS[row.side].engine == "reference" and row.goal == "timeout")
    ]


def positive_int(value):
    value = int(value)
    if value < 1:
        raise argparse.ArgumentTypeError("must be positive")
    return value


def parser(title):
    result = argparse.ArgumentParser(
        description=title, epilog=description(), formatter_class=argparse.RawDescriptionHelpFormatter
    )
    add_arguments(result)
    result.add_argument("--timeout", type=positive_int, default=300, help="seconds per subprocess (default 300)")
    result.add_argument("-j", "--jobs", type=positive_int, default=1, help="concurrent workloads (default 1)")
    result.add_argument("--no-build", action="store_true", help="use existing release binaries")
    return result


def setup(args, workloads, sides=SIDES, *, config=None):
    config = config or Config()
    for workload in workloads:
        if not workload.supported_sides(sides):
            raise ValueError(f"{workload.case}: all selected treatments are unsupported: {workload.unsupported}")
    if not args.no_build:
        build()
    for tool in (config.egglog, config.xmulti):
        if not tool.exists():
            raise ValueError(f"missing {tool}; run without --no-build")
    print(f"egglog {config.egglog}\nxmulti {config.xmulti}", file=sys.stderr)
    print(f"Timeout: {args.timeout}s per process. One dot per completed treatment/sample.", file=sys.stderr)
    if args.jobs > 1:
        print(f"Parallel workloads: {args.jobs}; timings include resource contention.", file=sys.stderr)
    return config


def stop_worker(_signum, _frame):
    # Unwind subprocess.run and scratch-file finally blocks on pool termination.
    raise SystemExit(0)


def init_worker():
    signal.signal(signal.SIGINT, signal.SIG_IGN)


def parallel_workload(payload):
    worker, workload, options = payload
    # Idle workers use the default SIGTERM handler to avoid unwinding queue locks.
    previous = signal.signal(signal.SIGTERM, stop_worker)
    try:
        with Progress(parallel=True) as progress:
            return worker(workload, progress=progress, **options)
    finally:
        signal.signal(signal.SIGTERM, previous)


def run_workloads(workloads, worker, *, jobs=1, **options):
    """Keep input order in the results; workers own their scratch files and progress."""
    if jobs == 1:
        with Progress() as progress:
            return [worker(workload, progress=progress, **options) for workload in workloads]
    context = multiprocessing.get_context("spawn")
    with context.Pool(min(jobs, len(workloads)), initializer=init_worker) as pool:
        results = list(pool.imap(parallel_workload, ((worker, w, options) for w in workloads)))
        pool.close()
        pool.join()
    print(file=sys.stderr, flush=True)
    return results


def table(headers, rows):
    """Small, static Markdown tables; no dependency on the proof benchmark UI."""

    def line(values):
        cells = ("—" if v is None else str(v).replace("|", "\\|").replace("\n", " ") for v in values)
        return "| " + " | ".join(cells) + " |"

    return "\n".join([line(headers), line(["---"] * len(headers)), *(line(row) for row in rows)])
