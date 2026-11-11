"""Validate retained native output contracts using only standalone Egglog inputs."""

from __future__ import annotations

import json
from dataclasses import asdict
from pathlib import Path
from typing import Any

from benchmarking.targets import sha256_file
from scripts.dialegg_speq_complete import run_complete_command, validate_extract_output
from scripts.hardboiled_replay import egglog_forms


def validate_capture(
    capture: dict[str, Any], engine: Path, output: Path, *, timeout_sec: float = 300
) -> dict[str, Any]:
    """Keep parent completion, exact replay bytes and output agreement separate.

    Original best-extract contracts compare every returned term. For native
    custom extractors, query-only checks establish membership of their actual
    selections; ordinary extraction need not choose the same optimum.
    """
    output.mkdir(parents=True, exist_ok=False)
    result: dict[str, Any] = {
        "status": "blocked",
        "reason": None,
        "engine": str(engine.resolve()),
        "engine_sha256": sha256_file(engine),
        "workloads": [],
        "validations": [],
        "proof_validation": "not-run",
    }
    try:
        if capture.get("source_completion", {}).get("status") not in {"success", "complete"}:
            raise ValueError("the source parent did not complete; its prefixes are diagnostic only")
        sessions = capture.get("sessions") or capture.get("invocations")
        if sessions is None and capture.get("output_contract"):
            sessions = [
                {
                    "replay": capture["source_completion"]["output_path"],
                    "replay_sha256": capture["source_completion"]["output_sha256"],
                    "output_contract": capture["output_contract"],
                }
            ]
        if not sessions:
            raise ValueError("completed parent has no independently checkable output contracts")
        for index, session in enumerate(sessions):
            replay = Path(session.get("replay") or session["standalone"])
            expected_hash = session.get("replay_sha256") or session.get("standalone_sha256")
            if not expected_hash or sha256_file(replay).removeprefix("sha256:") != expected_hash.removeprefix(
                "sha256:"
            ):
                raise ValueError(f"replay identity changed: {replay}")
            source = replay.read_text()
            forms = [tokens for _, _, tokens in egglog_forms(source)]
            if any(tokens[1] in {"prove", "prove-extract", "include", "input"} for tokens in forms):
                raise ValueError("ordinary standalone validation requires self-contained commands and bundled facts")
            contract = session.get("output_contract")
            selections = session.get("selections")
            if selections is not None:
                if len(selections) != session["root_count"] or not selections:
                    raise ValueError("native selection/root correspondence is incomplete")
                for selected in selections:
                    expected_check = egglog_forms(selected["check"])[0][2]
                    if expected_check not in forms:
                        raise ValueError("replay omitted a native selected-output equality")
            elif not contract or contract["kind"] not in {
                "ordinary-best-extract",
                "query-only-native-output-equality",
            }:
                raise ValueError("unknown or absent native output contract")
            elif contract["kind"] == "query-only-native-output-equality":
                if not contract["roots"] or not any(tokens[1] == "check" for tokens in forms):
                    raise ValueError("native output query has no roots or checks")
            command = [str(engine.resolve()), "-j", "1", str(replay.resolve())]
            process = run_complete_command(command, output, output / f"replay-{index:04}", timeout_sec)
            row = {
                "replay": str(replay),
                "replay_sha256": sha256_file(replay),
                "command": command,
                **asdict(process),
                "stdout_path": str(process.stdout_path),
                "stderr_path": str(process.stderr_path),
            }
            result["validations"].append(row)
            if process.status != "success":
                result.update(status=process.status, reason=process.message or f"ordinary replay failed: {replay}")
                break
            outputs = validate_extract_output(source, process.stdout_path.read_text())
            if contract and contract["kind"] == "ordinary-best-extract" and outputs != contract["expected_terms"]:
                raise ValueError("ordinary extraction differs from the native output contract")
            if selections is not None and len(outputs) != len(selections):
                raise ValueError("ordinary output count differs from the recorded native roots")
            row["output_contract_passed"] = True
            # Zero-root setup sessions remain in the parent evidence, not the
            # measurement population. An unchanged extracted program is valid.
            if any(tokens[1] in {"extract", "check"} for tokens in forms):
                result["workloads"].append(str(replay))
        else:
            if not result["workloads"]:
                raise ValueError("completed source emitted helpers only, with no output workload")
            result["status"] = "success"
    except (OSError, ValueError, KeyError) as error:
        result.update(status="blocked", reason=str(error))
    finally:
        if result["status"] != "success":
            result["workloads"] = []
        (output / "validation.json").write_text(json.dumps(result, indent=2, default=str) + "\n")
    return result
