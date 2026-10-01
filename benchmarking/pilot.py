"""Prepare suites with cached measured screening and separate strict-proof evidence."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
import signal
import subprocess
import sys
import time
from collections.abc import Callable, Mapping, Sequence
from contextlib import suppress
from dataclasses import asdict, dataclass
from datetime import UTC, datetime
from pathlib import Path
from typing import Any, Literal, cast

from rich.console import Console

from .admission import PILOT_RELATIVE_PATH as PILOT_RELATIVE_PATH
from .admission import PROOF_TREATMENTS, ProofTreatment, preparation_outcome
from .admission import PilotPolicy as PilotPolicy
from .admission import find_pilot_record as find_pilot_record
from .admission import load_pilot_records as load_pilot_records
from .admission import pilot_identity as pilot_identity
from .collection import build_collection_plan, collect_rows, preflight_collection
from .engines import Engine
from .memory_guard import GROUP_LIMIT_BYTES, MemoryGuard, group_rss_bytes
from .models import BenchmarkEndpoint, EngineBinary, FileSpec, ResolvedTarget, TargetRequest, TargetRow
from .reports.grouped import grouped_report_path, write_grouped_report
from .reports.store import CacheKey, ReportStore, parse_report_record
from .suites import SUITE_NAMES, SuiteSelection, build_coverage, render_coverage_markdown, resolve_suite
from .targets import build_target, git_dirty, git_sha, sha256_file, workload_command
from .workloads import require_workload_unchanged


@dataclass(frozen=True)
class PilotProcessResult:
    status: Literal["success", "failure", "timed-out", "memory-limit", "resource-stopped"]
    returncode: int | None
    wall_sec: float
    peak_rss_bytes: int
    stdout_path: Path
    stderr_path: Path
    message: str | None


def _kill_retained_root_group(pid: int) -> None:
    """Signal an unreaped root group; verify macOS's zombie-only EPERM case.

    The caller must retain this child with WNOWAIT until its final wait. Never
    waive EPERM by errno alone: both child exit and absence of live group members
    must be observed successfully while the root PID is still reserved.
    """
    try:
        os.killpg(pid, signal.SIGKILL)
    except ProcessLookupError:
        return
    except PermissionError as signal_error:
        if sys.platform != "darwin":
            raise
        exited = getattr(os, "waitid")(os.P_PID, pid, os.WEXITED | os.WNOHANG | os.WNOWAIT)  # noqa: B009
        if exited is None or exited.si_pid != pid:
            raise
        snapshot = subprocess.run(
            ["ps", "-axo", "pid=,pgid=,stat="], capture_output=True, text=True, check=True, timeout=1
        )
        seen = set()
        for line in snapshot.stdout.splitlines():
            columns = line.split()
            if len(columns) != 3:
                raise ValueError("Incomplete retained-root group membership snapshot") from signal_error
            member, group = map(int, columns[:2])
            if member in seen or member < 0 or group < 0:
                raise ValueError("Ambiguous retained-root group membership snapshot") from signal_error
            seen.add(member)
            if group == pid and not columns[2].startswith("Z"):
                raise


def run_bounded_command(
    command: Sequence[str],
    cwd: Path,
    output_prefix: Path,
    *,
    timeout_sec: float = 120,
    memory_limit_bytes: int = GROUP_LIMIT_BYTES,
    allow_warning_pressure: bool = False,
    require_guard: bool = False,
    disk_reserve_bytes: int = 0,
    sample_rss: Callable[[int], int] | None = None,
    cleanup_descendants: Callable[[], None] | None = None,
) -> PilotProcessResult:
    """Monitor an isolated process group's aggregate RSS and retain disk logs.

    RSS is sampled every 50 ms, so the threshold is a monitored guard rather
    than a kernel allocation limit. All surviving group members are killed
    when the parent exits, a limit is crossed, or the caller is interrupted.
    Explicit diagnostic callers may allow warning pressure; critical pressure,
    host reserve, and process-group limits still stop them. Timed collection
    does not use this override.
    """

    if timeout_sec <= 0 or memory_limit_bytes <= 0:
        raise ValueError("pilot process timeout and memory limit must be positive")
    if cleanup_descendants is not None and not all(
        hasattr(os, name) for name in ("waitid", "P_PID", "WEXITED", "WNOHANG", "WNOWAIT")
    ):
        raise ValueError("descendant cleanup requires non-consuming root exit observation (waitid/WNOWAIT)")
    guard = (
        MemoryGuard(allow_warning_pressure=allow_warning_pressure)
        if require_guard
        else MemoryGuard.from_environment(allow_warning_pressure=allow_warning_pressure)
    )
    if guard is not None and (reason := guard.check(0)):
        raise ValueError(f"resource guard refused to launch a workload: {reason}")
    if disk_reserve_bytes and shutil.disk_usage(cwd).free < disk_reserve_bytes:
        raise ValueError(f"disk guard refused to launch: fewer than {disk_reserve_bytes} bytes free")
    output_prefix.parent.mkdir(parents=True, exist_ok=True)
    stdout_path = Path(str(output_prefix) + ".stdout.log")
    stderr_path = Path(str(output_prefix) + ".stderr.log")
    start = time.monotonic()
    peak_rss = 0
    status: Literal["success", "failure", "timed-out", "memory-limit", "resource-stopped"] = "success"
    message: str | None = None
    env = os.environ.copy()
    env["RUST_LOG"] = "error"
    with stdout_path.open("wb") as stdout, stderr_path.open("wb") as stderr:
        process = subprocess.Popen(command, cwd=cwd, env=env, stdout=stdout, stderr=stderr, start_new_session=True)
        try:
            while True:
                if cleanup_descendants is None:
                    if process.poll() is not None:
                        break
                else:
                    # Keep the root PID unreaped through group cleanup. A poll()
                    # here would permit PID/PGID reuse during detached drain.
                    try:
                        # Typeshed omits this macOS API; availability is checked above.
                        exited = getattr(os, "waitid")(  # noqa: B009
                            os.P_PID, process.pid, os.WEXITED | os.WNOHANG | os.WNOWAIT
                        )
                    except Exception as error:
                        status = "resource-stopped"
                        message = f"root exit monitoring failed: {error}"
                        break
                    if exited is not None and exited.si_pid == process.pid:
                        break
                # Both macOS and Linux expose RSS in KiB through ps. Monitoring
                # the session's group includes descendants spawned by a driver.
                try:
                    rss = (sample_rss or group_rss_bytes)(process.pid)
                except Exception as error:
                    if sample_rss is None and (
                        guard is None or not isinstance(error, (OSError, ValueError, subprocess.SubprocessError))
                    ):
                        raise
                    status = "resource-stopped"
                    message = f"memory monitoring failed: {error}"
                    break
                peak_rss = max(peak_rss, rss)
                if disk_reserve_bytes:
                    try:
                        free_disk = shutil.disk_usage(cwd).free
                    except OSError as error:
                        status = "resource-stopped"
                        message = f"disk monitoring failed: {error}"
                        break
                    if free_disk < disk_reserve_bytes:
                        status = "resource-stopped"
                        message = f"free disk fell below the {disk_reserve_bytes}-byte reserve"
                        break
                if guard is not None and (reason := guard.check(rss)) is not None:
                    status = "resource-stopped"
                    message = reason
                    break
                if rss > memory_limit_bytes:
                    status = "memory-limit"
                    message = f"process-group RSS exceeded {memory_limit_bytes} bytes"
                    break
                if time.monotonic() - start >= timeout_sec:
                    status = "timed-out"
                    message = f"timed out after {timeout_sec:g} seconds"
                    break
                time.sleep(min(0.05, max(0, timeout_sec - (time.monotonic() - start))))
        finally:
            if cleanup_descendants is None:
                with suppress(ProcessLookupError):
                    os.killpg(process.pid, signal.SIGKILL)
                process.wait()
            else:
                cleanup_errors = []
                try:
                    try:
                        _kill_retained_root_group(process.pid)
                    except Exception as error:
                        cleanup_errors.append(f"initial root signal failed: {type(error).__name__}: {error}")
                    finally:
                        try:
                            cleanup_descendants()
                        except Exception as error:
                            cleanup_errors.append(f"descendant cleanup failed: {type(error).__name__}: {error}")
                finally:
                    try:
                        _kill_retained_root_group(process.pid)
                    except Exception as error:
                        cleanup_errors.append(f"final root signal failed: {type(error).__name__}: {error}")
                    finally:
                        process.wait()
                if cleanup_errors:
                    status = "resource-stopped"
                    previous = f"{message}; " if message else ""
                    message = previous + "; ".join(cleanup_errors)
    if status == "success" and process.returncode != 0:
        status = "failure"
        with stderr_path.open("rb") as log:
            log.seek(max(0, stderr_path.stat().st_size - 4000))
            message = log.read().decode("utf-8", errors="replace").strip()
        message = message or f"process exited with status {process.returncode}"
        if guard is not None and process.returncode == -signal.SIGKILL:
            status = "resource-stopped"
            message = f"resource guard halted pilot after unexpected SIGKILL (cause unknown): {message}"
    return PilotProcessResult(
        status, process.returncode, time.monotonic() - start, peak_rss, stdout_path, stderr_path, message
    )


def require_suite_admission(
    selection: SuiteSelection,
    targets: Sequence[ResolvedTarget],
    pilot_path: Path | None = None,
    *,
    store: ReportStore,
    timeout_sec: int = 120,
    rounds: int = 10,
    force_run: bool = False,
    treatment: ProofTreatment = "proof-extraction",
) -> tuple[tuple[FileSpec, ...], tuple[str, ...], tuple[tuple[FileSpec, str], ...]]:
    """Retain runnable cases and known failures without launching correctness tests."""

    records = load_pilot_records(pilot_path or selection.root / PILOT_RELATIVE_PATH)
    hashes_by_target: list[dict[str, str]] = []
    for target in targets:
        hashes: dict[str, str] = {binary.engine: binary.sha256 for binary in target.engine_binaries}
        if not hashes:
            hashes[target.primary_engine or "egglog"] = target.binary_sha256
        if any(case.family == "math-growth" for case in selection.cases):
            for engine, stem in (("egglog", "egglog-experimental"), ("egg", "egg-math-benchmark")):
                if engine not in hashes:
                    path = Path(target.row.path) / "target/release" / stem
                    if path.is_file():
                        hashes[engine] = sha256_file(path)
        hashes_by_target.append(hashes)
    files: list[FileSpec] = []
    issues: list[tuple[FileSpec, str]] = []
    diagnostics = [
        f"{case.id}: {selection.capture_errors.get(case.id, case.reason or case.status)}"
        for case in selection.cases
        if case.status != "captured" or case.id in selection.capture_errors
    ]
    for file in selection.files:
        family = selection.validation_families[(file.sha256, file.fact_directory_sha256)]
        outcomes = [
            preparation_outcome(
                file,
                family,
                hashes,
                selection.root,
                records,
                store.records,
                timeout_sec,
                rounds,
                treatment=treatment,
            )
            for hashes in hashes_by_target
        ]
        if not force_run and any(status == "normal-mode-blocked" for status, _ in outcomes):
            reason = "; ".join(str(r) for _, r in outcomes if r)
            diagnostics.append(f"{file.display_path}: normal-mode blocker: {reason}")
            issues.append((file, reason))
            continue
        files.append(file)
        reasons = tuple(
            dict.fromkeys(reason for status, reason in outcomes if status not in ("ready", "pending") and reason)
        )
        if blocker := selection.proof_blockers.get((file.sha256, file.fact_directory_sha256)):
            reasons = (*reasons, blocker)
        if reasons:
            issue = "; ".join(reasons)
            issues.append((file, issue))
            diagnostics.append(f"{file.display_path}: retained outcome: {issue}")
    return tuple(files), tuple(diagnostics), tuple(issues)


def pilot_workload(
    file: FileSpec,
    family: str,
    binaries: Mapping[str, Path],
    binary_hashes: Mapping[str, str],
    root: Path,
    evidence_directory: Path,
    policy: PilotPolicy,
    *,
    store: ReportStore,
    target: ResolvedTarget,
    previous: dict[str, Any] | None = None,
    refresh: bool = False,
    treatment: ProofTreatment = "proof-extraction",
) -> dict[str, Any]:
    """Screen through the ordinary collector, then retain separate proof logs."""

    identity = pilot_identity(file, family, binary_hashes, policy, root)
    record: dict[str, Any] = {
        "identity": identity,
        "file_path": file.display_path,
        "family": family,
        "started_at": datetime.now(UTC).isoformat(),
        "status": "admitted",
        "reason": None,
        "checks": [],
    }
    needed = ("egglog", "egg") if family == "math-growth" else ("egglog",)
    missing = [engine for engine in needed if engine not in binaries]
    if missing:
        record.update(status="blocked", reason=f"missing {' and '.join(missing)} binary; build it before the pilot")
        return record
    console = Console(stderr=True)
    for endpoint_treatment in ("off", treatment):
        endpoint = BenchmarkEndpoint(target, endpoint_treatment)
        plan = build_collection_plan(store, target, (endpoint,), (file,), 1, int(policy.timeout_sec), refresh, True)
        preflight_collection(plan, int(policy.timeout_sec))
        try:
            collect_rows(store, plan, int(policy.timeout_sec), console)
        except ValueError:
            latest = store.latest_records(CacheKey.for_endpoint(endpoint, file, int(policy.timeout_sec)), 1)
            if not latest or "resource guard" not in str(latest[-1].record["error_message"]):
                raise
            row = latest[-1].record
            record.update(
                status="resource-stopped", reason=f"{endpoint_treatment}: {row['error_message']}", operational_stop=True
            )
            return record
        row = store.latest_records(CacheKey.for_endpoint(endpoint, file, int(policy.timeout_sec)), 1)[-1].record
        if row["status"] != "success":
            record.update(status=row["status"], reason=f"{endpoint_treatment}: {row['error_message'] or row['status']}")
            return record
    if (
        previous is not None
        and not refresh
        and (
            previous["status"] == "admitted"
            or str(previous.get("reason", "")).startswith("proof-testing:")
            or any(check.get("treatment") == "proof-testing" for check in previous.get("checks", ()))
        )
    ):
        return previous
    result = run_bounded_command(
        workload_command(binaries["egglog"], file, "proof-testing"),
        root,
        evidence_directory / "proof-testing",
        timeout_sec=policy.timeout_sec,
        memory_limit_bytes=policy.memory_limit_bytes,
    )
    record["checks"].append({"treatment": "proof-testing", **asdict(result)})
    if result.status != "success":
        record.update(status=result.status, reason=f"proof-testing: {result.message}")
        if result.status == "resource-stopped":
            record["operational_stop"] = True
    if record["status"] == "admitted" and family == "math-growth":
        from .math_workloads import validate_math_workload

        validation = validate_math_workload(
            file.absolute_path,
            binaries["egg"],
            binaries["egglog"],
            evidence_directory / "math",
            runner=run_bounded_command,
            timeout_sec=policy.timeout_sec,
            memory_limit_bytes=policy.memory_limit_bytes,
        )
        record["math_validation"] = validation
        if validation["status"] != "success":
            record.update(
                status=validation["status"], reason=validation.get("reason", "Math boundary/parity gate failed")
            )
            if any(run["status"] == "resource-stopped" for run in validation.get("runs", [])):
                record["operational_stop"] = True
    require_workload_unchanged(file)
    if any(sha256_file(binaries[engine]) != binary_hashes[engine] for engine in needed):
        raise ValueError("pilot executable changed during validation; rerun with stable binaries")
    return record


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--suite", choices=SUITE_NAMES, action="append", required=True)
    parser.add_argument("--treatment", choices=PROOF_TREATMENTS, default="proof-extraction")
    parser.add_argument("--egglog-binary", type=Path)
    parser.add_argument("--egg-binary", type=Path)
    parser.add_argument(
        "--build", action="store_true", help="build required release executables with the resource guard"
    )
    parser.add_argument(
        "--evidence", type=Path, help="separate strict-proof evidence (default: benchmarks/local/pilot.jsonl)"
    )
    parser.add_argument(
        "--refresh", action="store_true", help="explicitly retry measured screening and strict validation"
    )
    parser.add_argument("--timeout-sec", type=int, default=120)
    parser.add_argument(
        "--allow-classified-failures",
        action="store_true",
        help="report classified workload failures without a failing exit status; safety stops and errors still fail",
    )
    parser.add_argument(
        "--coverage-only", action="store_true", help="report inventory and existing evidence without running"
    )
    parser.add_argument("--coverage-output", type=Path, help="write coverage JSON and sibling Markdown")
    parser.add_argument(
        "--report", type=Path, default=Path(".reports.jsonl"), help="shared benchmark cache (default: .reports.jsonl)"
    )
    args = parser.parse_args(argv)
    root = Path(__file__).resolve().parents[1]
    evidence_path = args.evidence or root / PILOT_RELATIVE_PATH
    previous_guard = os.environ.get("EGGLOG_BENCH_MEMORY_GUARD")
    os.environ["EGGLOG_BENCH_MEMORY_GUARD"] = "1"
    store: ReportStore | None = None
    result = 2
    try:
        if args.timeout_sec <= 0:
            raise ValueError("timeout must be positive")
        if str(args.report) == "-":
            raise ValueError("--report requires a file path")
        if evidence_path.resolve() == args.report.resolve():
            raise ValueError("pilot evidence must differ from the benchmark report")
        if args.coverage_output is not None:
            output_paths = (args.coverage_output.resolve(), args.coverage_output.with_suffix(".md").resolve())
            if {evidence_path.resolve(), args.report.resolve()}.intersection(output_paths):
                raise ValueError("coverage output must differ from the pilot evidence and benchmark report")
            if output_paths[0] == output_paths[1]:
                raise ValueError("coverage JSON and Markdown outputs must use different paths")
        selection = resolve_suite(args.suite, root, include_normal_only=bool(args.coverage_only))
        if not selection.files:
            args.coverage_only = True
        policy = PilotPolicy(timeout_sec=args.timeout_sec)
        records = load_pilot_records(evidence_path)
        store = None if args.coverage_only else ReportStore(args.report.resolve())
        target_row = None
        if not args.coverage_only:
            target_row = TargetRow(".", str(root), "HEAD", git_sha(root), git_dirty(root), "figures")
        if args.build and not args.coverage_only:
            assert target_row is not None
            if args.egglog_binary is None:
                build_target(target_row, Console(stderr=True))
            if "math-growth" in selection.validation_families.values() and args.egg_binary is None:
                build_target(target_row, Console(stderr=True), engine="egg")
        for explicit_binary in (args.egglog_binary, args.egg_binary):
            if explicit_binary is not None and not explicit_binary.is_file():
                raise FileNotFoundError(f"pilot binary does not exist: {explicit_binary}")
        binaries: dict[str, Path] = {
            engine: path.resolve()
            for engine, path in (
                ("egglog", args.egglog_binary or root / "target/release/egglog-experimental"),
                ("egg", args.egg_binary or root / "target/release/egg-math-benchmark"),
            )
            if path.is_file()
        }
        hashes = {engine: sha256_file(path) for engine, path in binaries.items()}
        measured = (
            store.records
            if store is not None
            else (
                tuple(parse_report_record(line) for line in args.report.read_bytes().splitlines())
                if args.report.exists()
                else ()
            )
        )
        failed = False
        stopped = False
        if not args.coverage_only:
            assert store is not None and target_row is not None
            if "egglog" not in binaries:
                raise FileNotFoundError("egglog release binary does not exist; build it or pass --build")
            target = ResolvedTarget(
                TargetRequest("figures=.", ".", "figures"),
                target_row,
                hashes["egglog"],
                binaries["egglog"],
                tuple(EngineBinary(cast(Engine, engine), hashes[engine], path) for engine, path in binaries.items()),
                "egglog",
            )
            evidence_path.parent.mkdir(parents=True, exist_ok=True)
            for index, file in enumerate(selection.files, 1):
                family = selection.validation_families[(file.sha256, file.fact_directory_sha256)]
                current = find_pilot_record(records, file, family, hashes, policy, root, treatment=args.treatment)
                status, reason = preparation_outcome(
                    file,
                    family,
                    hashes,
                    root,
                    records,
                    store.records,
                    args.timeout_sec,
                    treatment=args.treatment,
                    require_validation=True,
                )
                if not args.refresh and status != "pending":
                    failed |= status != "ready"
                    print(
                        f"{file.display_path}: {status} (reused)" + (f" — {reason}" if reason else ""), file=sys.stderr
                    )
                    continue
                key = hashlib.sha256(
                    json.dumps(pilot_identity(file, family, hashes, policy, root), sort_keys=True).encode()
                ).hexdigest()[:20]
                print(f"Preparing {index}/{len(selection.files)}: {file.display_path}", file=sys.stderr, flush=True)
                try:
                    record = pilot_workload(
                        file,
                        family,
                        binaries,
                        hashes,
                        root,
                        evidence_path.parent / "logs" / key / str(time.time_ns()),
                        policy,
                        store=store,
                        target=target,
                        previous=current,
                        refresh=args.refresh,
                        treatment=args.treatment,
                    )
                except ValueError as error:
                    if not str(error).startswith("resource guard refused to launch a workload:"):
                        raise
                    print(f"error: {error}; no further workloads will be launched", file=sys.stderr)
                    stopped = True
                    break
                if record is not current:
                    with evidence_path.open("a") as handle:
                        handle.write(json.dumps(record, default=str) + "\n")
                    records.append(record)
                if record.get("operational_stop"):
                    print(
                        f"error: resource guard stopped preparation: {record['reason']}; "
                        "evidence was retained; no further workloads will be launched",
                        file=sys.stderr,
                    )
                    stopped = True
                    break
                failed |= record["status"] != "admitted"
                print(
                    f"{file.display_path}: {record['status']}" + (f" — {record['reason']}" if record["reason"] else ""),
                    file=sys.stderr,
                    flush=True,
                )
            measured = store.records
        coverage = build_coverage(selection, evidence_path, hashes, measured, timeout_sec=args.timeout_sec)
        if args.coverage_output is not None:
            args.coverage_output.parent.mkdir(parents=True, exist_ok=True)
            args.coverage_output.write_text(json.dumps(coverage, indent=2) + "\n")
            args.coverage_output.with_suffix(".md").write_text(render_coverage_markdown(coverage))
        else:
            sys.stdout.write(render_coverage_markdown(coverage))
        result = 2 if stopped else 1 if failed and not args.allow_classified_failures else 0
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        print(f"error: {error}", file=sys.stderr)
        result = 2
    finally:
        if previous_guard is None:
            os.environ.pop("EGGLOG_BENCH_MEMORY_GUARD", None)
        else:
            os.environ["EGGLOG_BENCH_MEMORY_GUARD"] = previous_guard
        if store is not None:
            try:
                write_grouped_report(store.grouped_report(), grouped_report_path(store.path))
            except (OSError, ValueError) as error:
                print(f"error: could not refresh grouped report: {error}", file=sys.stderr)
                result = 2
    return result


if __name__ == "__main__":
    raise SystemExit(main())
