"""Run explicit strict proof checks and record outcomes outside the timing cache."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import sys
import tempfile
from collections.abc import Sequence
from pathlib import Path

from rich.console import Console

from .models import TargetRequest
from .processes import run_bounded_command
from .suites import SAFETY_POLICY, SUITE_NAMES, VALIDATION_POLICY, CorpusOutcome, resolve_suite
from .targets import build_target, sha256_file, target_row_for_request, workload_command
from .workloads import require_workload_unchanged


def record_outcome(path: Path, outcome: CorpusOutcome) -> None:
    """Atomically retain diagnostic history without touching measured observations."""

    original = path.read_bytes()
    manifest = json.loads(original)
    if not any(
        (workload["sha256"], workload.get("facts_sha256", ""))
        == (outcome["file_sha256"], outcome["fact_directory_sha256"])
        for workload in manifest["workloads"]
    ):
        raise ValueError("validated input is no longer in the prepared corpus")
    outcomes = manifest.setdefault("outcomes", [])
    if outcomes and outcomes[-1] == outcome:
        return
    outcomes.append(outcome)
    encoded = (json.dumps(manifest, indent=2) + "\n").encode()
    temporary: Path | None = None
    try:
        with tempfile.NamedTemporaryFile(dir=path.parent, prefix=".validation-", delete=False) as handle:
            temporary = Path(handle.name)
            handle.write(encoded)
        if path.read_bytes() != original:
            raise ValueError("corpus manifest changed during validation; retry after preparation completes")
        os.replace(temporary, path)
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--suite", choices=SUITE_NAMES, default="expanded")
    parser.add_argument("--binary", type=Path, help="existing egglog binary (default: build current release)")
    parser.add_argument("--timeout-sec", type=int, default=300)
    parser.add_argument("--disequality-encoding", choices=("nee", "ee"), default="nee")
    args = parser.parse_args(argv)
    console = Console(stderr=True)
    root = Path(__file__).resolve().parents[1]
    try:
        if args.timeout_sec <= 0:
            raise ValueError("timeout must be positive")
        selection = resolve_suite(args.suite, root)
        failed = bool(selection.capture_errors)
        for case in selection.cases:
            if reason := selection.capture_errors.get(case.id) or (
                (case.reason or case.status) if case.status in ("blocked", "pending") else None
            ):
                console.print(f"{case.id}: {reason}")
                failed = True
        if not selection.files:
            return int(failed)
        if args.binary:
            binary = args.binary.resolve()
            binary_hash = sha256_file(binary)
        else:
            binary, binary_hash = build_target(
                target_row_for_request(TargetRequest(".", ".", None), root, "HEAD"), console
            )
        for file in selection.files:
            safety = next(
                (
                    outcome
                    for outcome in reversed(selection.manifest.outcomes)
                    if outcome["kind"] == "safety"
                    and outcome["policy"] == SAFETY_POLICY
                    and (outcome["file_sha256"], outcome["fact_directory_sha256"])
                    == (file.sha256, file.fact_directory_sha256)
                ),
                None,
            )
            if safety is not None and safety["status"] != "success":
                console.print(f"{file.display_path}: safety-deferred; {safety['reason']}")
                failed = True
                continue
            require_workload_unchanged(file)
            if sha256_file(binary) != binary_hash:
                raise ValueError("validation executable changed; retry with a stable binary")
            outcome: CorpusOutcome = {
                "file_sha256": file.sha256,
                "fact_directory_sha256": file.fact_directory_sha256,
                "binary_sha256": binary_hash,
                "timeout_sec": args.timeout_sec,
                "disequality_encoding": args.disequality_encoding,
                "kind": "validation",
                "policy": VALIDATION_POLICY,
                "status": "success",
                "reason": None,
            }
            digest = hashlib.sha256(json.dumps(outcome, sort_keys=True).encode()).hexdigest()
            directory = selection.manifest.path.parent / "validation" / digest
            directory.mkdir(parents=True, exist_ok=True)
            run_directory = Path(tempfile.mkdtemp(dir=directory, prefix="run-"))
            prefix = run_directory / "proof-testing"
            outcome["evidence"] = run_directory.relative_to(selection.manifest.path.parent).as_posix()
            try:
                result = run_bounded_command(
                    workload_command(binary, file, "proof-testing", args.disequality_encoding),
                    root,
                    prefix,
                    timeout_sec=args.timeout_sec,
                    require_guard=True,
                )
            except ValueError as error:
                if not str(error).startswith("resource guard refused to launch"):
                    raise
                outcome.update({"kind": "safety", "policy": SAFETY_POLICY, "status": "deferred", "reason": str(error)})
                record_outcome(selection.manifest.path, outcome)
                console.print(f"{file.display_path}: {error}")
                return 1
            require_workload_unchanged(file)
            if sha256_file(binary) != binary_hash:
                raise ValueError("validation executable changed during execution; no outcome recorded")
            if result.status in ("memory-limit", "resource-stopped"):
                outcome.update(
                    {"kind": "safety", "policy": SAFETY_POLICY, "status": "deferred", "reason": result.message}
                )
            elif result.status != "success":
                outcome.update({"status": "failure", "reason": result.message or result.status})
            record_outcome(selection.manifest.path, outcome)
            console.print(
                f"{file.display_path}: {outcome['status']}" + (f"; {outcome['reason']}" if outcome["reason"] else "")
            )
            if outcome["kind"] == "safety":
                return 1
            failed |= outcome["status"] != "success"
        return int(failed)
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        print(str(error), file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
