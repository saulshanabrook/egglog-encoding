"""Run explicit strict proof checks without measurements or source acquisition."""

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

from .corpus import SAFETY_POLICY, VALIDATION_POLICY, CorpusOutcome, load_manifest, sha256_file
from .reproduction_process import run_bounded_command


def record_outcome(path: Path, outcome: CorpusOutcome) -> None:
    """Atomically retain local diagnostics without changing tracked corpus inputs."""

    original = path.read_bytes()
    manifest = json.loads(original)
    if not any(
        (workload["sha256"], workload.get("facts_sha256", ""))
        == (outcome["file_sha256"], outcome["fact_directory_sha256"])
        for workload in manifest["workloads"]
    ):
        raise ValueError("validated input is no longer in the prepared corpus")
    outcomes_path = path.parent / ".local/outcomes.json"
    outcomes_path.parent.mkdir(parents=True, exist_ok=True)
    previous = outcomes_path.read_bytes() if outcomes_path.is_file() else None
    outcomes = json.loads(previous) if previous is not None else []
    if outcomes and outcomes[-1] == outcome:
        return
    outcomes.append(outcome)
    encoded = (json.dumps(outcomes, indent=2) + "\n").encode()
    temporary: Path | None = None
    try:
        with tempfile.NamedTemporaryFile(dir=outcomes_path.parent, prefix=".validation-", delete=False) as handle:
            temporary = Path(handle.name)
            handle.write(encoded)
        if path.read_bytes() != original:
            raise ValueError("corpus manifest changed during validation; retry after preparation completes")
        current = outcomes_path.read_bytes() if outcomes_path.is_file() else None
        if current != previous:
            raise ValueError("corpus outcomes changed during validation; retry after the other validator completes")
        os.replace(temporary, outcomes_path)
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("files", nargs="*", help="manifest-relative inputs (default: every prepared input)")
    parser.add_argument("--binary", type=Path, help="existing controlled egglog executable")
    parser.add_argument("--timeout-sec", type=int, default=300)
    parser.add_argument("--disequality-encoding", choices=("nee", "ee"), default="nee")
    args = parser.parse_args(argv)
    root = Path(__file__).resolve().parents[2]
    try:
        if args.timeout_sec <= 0:
            raise ValueError("timeout must be positive")
        manifest = load_manifest(root)
        requested = set(args.files)
        by_name = {workload["file"]: workload for workload in manifest.workloads}
        if requested - by_name.keys():
            raise ValueError("validation inputs must name prepared manifest files")
        workloads = [workload for workload in manifest.workloads if not requested or workload["file"] in requested]
        if not workloads:
            print("no prepared inputs; run explicit source preparation first", file=sys.stderr)
            return 1
        binary = (args.binary or root / "target/release/egglog-experimental").resolve()
        binary_hash = sha256_file(binary)
        failed = False
        for workload in workloads:
            path = (manifest.path.parent / workload["file"]).resolve()
            if not path.is_relative_to(manifest.path.parent.resolve()):
                raise ValueError("prepared workload escapes the corpus directory")
            if workload.get("facts_sha256", "") or workload.get("facts"):
                raise ValueError("strict source validation requires standalone prepared inputs")
            expected = workload["sha256"]
            if sha256_file(path) != expected:
                raise ValueError("prepared workload changed before validation")
            if sha256_file(binary) != binary_hash:
                raise ValueError("validation executable changed before execution")
            outcome: CorpusOutcome = {
                "file_sha256": expected,
                "fact_directory_sha256": "",
                "binary_sha256": binary_hash,
                "timeout_sec": args.timeout_sec,
                "disequality_encoding": args.disequality_encoding,
                "kind": "validation",
                "policy": VALIDATION_POLICY,
                "status": "success",
                "reason": None,
            }
            digest = hashlib.sha256(json.dumps(outcome, sort_keys=True).encode()).hexdigest()
            directory = manifest.path.parent / ".local/validation" / digest
            directory.mkdir(parents=True, exist_ok=True)
            run_directory = Path(tempfile.mkdtemp(dir=directory, prefix="run-"))
            outcome["evidence"] = run_directory.relative_to(manifest.path.parent).as_posix()
            command = [str(binary), "--mode", "no-messages", "-j", "1", "--proof-testing"]
            if args.disequality_encoding != "nee":
                command.extend(("--disequality-encoding", args.disequality_encoding))
            command.append(str(path))
            result = run_bounded_command(
                command, root, run_directory / "proof-testing", timeout_sec=args.timeout_sec, native_limit=True
            )
            if sha256_file(path) != expected or sha256_file(binary) != binary_hash:
                raise ValueError("input or executable changed during execution; no outcome recorded")
            if result.status == "resource-stopped":
                outcome.update(
                    {"kind": "safety", "policy": SAFETY_POLICY, "status": "deferred", "reason": result.message}
                )
            elif result.status != "success":
                outcome.update({"status": "failure", "reason": result.message or result.status})
            record_outcome(manifest.path, outcome)
            print(
                f"{workload['file']}: {outcome['status']}" + (f"; {outcome['reason']}" if outcome["reason"] else ""),
                file=sys.stderr,
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
