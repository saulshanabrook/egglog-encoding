"""Validate retained native output contracts using only standalone Egglog inputs."""

from __future__ import annotations

import hashlib
import json
from dataclasses import asdict
from pathlib import Path
from typing import Any

from benchmarking.targets import sha256_file
from scripts.dialegg_speq_complete import run_complete_command, validate_extract_output
from scripts.hardboiled_replay import egglog_forms


def native_check_contract(source: str, checks: list[tuple[int, str]], roots: list[dict[str, Any]]) -> dict[str, Any]:
    """Bind native equalities to exact commands and their preceding graph state.

    Callers supply the insertion positions while materializing the replay. Do
    not rediscover an equality by searching for a matching check somewhere else.
    """
    forms = [tokens for _, _, tokens in egglog_forms(source)]
    records = []
    previous = -1
    for position, check in checks:
        parsed = egglog_forms(check)
        if len(parsed) != 1 or parsed[0][2][1] != "check" or position <= previous:
            raise ValueError("native output checks must be single ordered check commands")
        tokens = parsed[0][2]
        if position >= len(forms) or forms[position] != tokens:
            raise ValueError("native output check is absent at its intended command boundary")
        records.append(
            {
                "command": position,
                "tokens": tokens,
                "prefix_sha256": hashlib.sha256(json.dumps(forms[:position]).encode()).hexdigest(),
            }
        )
        previous = position
    if not records or not roots:
        raise ValueError("native output contract requires all roots and checks")
    return {
        "kind": "query-only-native-output-equality",
        "roots": roots,
        "checks": records,
        "check_sha256": hashlib.sha256(json.dumps(records, sort_keys=True).encode()).hexdigest(),
        "claims_optimality": False,
    }


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
        if capture.get("status") not in {"reproduced", "ordinary-validation-pending", "ordinary-validation-failed"}:
            raise ValueError("capture is blocked or incomplete; native completion alone cannot admit its prefixes")
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
        materialization = capture.get("materialization", {})
        if (
            materialization.get("complete") is not True
            or materialization.get("expected_sessions") != len(sessions)
            or materialization.get("materialized_sessions") != len(sessions)
        ):
            raise ValueError("complete materialization of every native session is required")
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
                extracts = [index for index, tokens in enumerate(forms) if tokens[1] == "extract"]
                expected = native_check_contract(
                    source,
                    [(index + 1, selected["check"]) for index, selected in zip(extracts, selections, strict=True)],
                    selections,
                )
                if contract != expected:
                    raise ValueError("native selection contract changed or lost its extraction boundary")
            if not contract or contract["kind"] not in {
                "ordinary-best-extract",
                "query-only-native-output-equality",
            }:
                raise ValueError("unknown or absent native output contract")
            elif contract["kind"] == "query-only-native-output-equality":
                checks = contract.get("checks", [])
                expected = native_check_contract(
                    source,
                    [(check["command"], " ".join(check["tokens"])) for check in checks],
                    contract["roots"],
                )
                if contract != expected:
                    raise ValueError("native check hash, ordered checks, or preceding graph state changed")
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
