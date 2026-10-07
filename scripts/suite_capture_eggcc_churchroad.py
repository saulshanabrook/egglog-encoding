"""Capture complete Eggcc calls and Churchroad mapping phases from native events."""

from __future__ import annotations

import hashlib
import json
import re
import sys
from dataclasses import asdict
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from benchmarking.targets import sha256_file  # noqa: E402
from scripts.eggcc_churchroad_complete import (  # noqa: E402
    CaptureError,
    churchroad_mapping_session,
    eggcc_sessions,
    read_events,
)
from scripts.hardboiled_replay import egglog_forms  # noqa: E402
from scripts.paper_benchmarks.materialize import constructors  # noqa: E402
from scripts.reproduction_process import run_bounded_command  # noqa: E402
from scripts.reproduction_validation import (  # noqa: E402
    CHURCHROAD_PLACEHOLDERS,
    churchroad_circuit_contract,
    eggcc_root_contract,
)

PINS = {
    "eggcc": "16be0063133ef0b8ba21cd75ee377002dc3ecbed",
    "churchroad": "9f82ca23b273a5a500cc6a1ca60b30d3c33c5721",
}

EGGCC_HELPERS = {
    "TypeList-length",
    "ListExpr-length",
    "tuple-length",
    "Length-List<i64+IntInterval>",
    "Length-List<PtrPointees>",
    "succ",
}

EGGCC_EXPR_SET_TOKENS_SHA256 = "992434eb3686e88fcd37cbe063c331f02150714343e3421ed36b550d8aac4eb8"


def adapt_eggcc(source: str) -> str:
    """Apply the checked-in pass-one fixture's compatibility changes exactly.

    The unused ExprSet block must have no references outside its contiguous
    declaration block. Only the six deterministic length/successor functions
    may replace no-merge with merge-old. Keep every schedule command intact.
    """
    forms = egglog_forms(source)
    starts = [i for i, (_, _, tokens) in enumerate(forms) if tokens[1:3] == ["sort", "ExprSetPrim"]]
    ends = [i for i, (_, _, tokens) in enumerate(forms) if tokens[1:3] == ["datatype", "Pointees"]]
    if len(starts) != 1 or len(ends) != 1 or ends[0] - starts[0] != 10:
        raise ValueError("expected exactly the pinned ten-form ExprSet helper block before Pointees")
    start, end = starts[0], ends[0]
    block = [tokens for _, _, tokens in forms[start:end]]
    if hashlib.sha256(json.dumps(block, separators=(",", ":")).encode()).hexdigest() != EGGCC_EXPR_SET_TOKENS_SHA256:
        raise ValueError("ExprSet helper block differs from the pinned compiler")
    if any(
        token in {"ExprSet", "ExprSetPrim", "ES"} or token.startswith("ExprSet-")
        for _, _, tokens in forms[:start] + forms[end:]
        for token in tokens
    ):
        raise ValueError("ExprSet is referenced outside its unused helper block")
    source = source[: forms[start][0]] + source[forms[end][0] :]
    found = set(re.findall(r"^\(function (\S+) .*:no-merge\)$", source, re.MULTILINE))
    if found != EGGCC_HELPERS:
        raise ValueError(f"unexpected no-merge helper set: {sorted(found)}")
    source = source.replace(":no-merge", ":merge old")
    return (
        "; Complete native Eggcc optimization invocation; raw commands retained separately.\n"
        "; Compatibility: unused ExprSet helpers omitted; deterministic helpers use merge-old.\n"
        + source.rstrip()
        + "\n"
    )


def rename_churchroad_globals(
    source: str, query: str, rules: str, *, aliases: dict[str, str] | None = None
) -> tuple[str, str, dict[str, str]]:
    """Preserve paper-era global references at each command's declaration time.

    The native engine resolves bare names to previously declared globals, even
    inside later rules. Carry aliases between source parts, but leave earlier
    rule locals alone. Fresh base names avoid current global-shadowing errors.
    """
    tokens = re.compile(r';[^\n]*|"(?:\\.|[^"\\])*"|[()]|[^\s();"]+')
    bindings = dict(aliases or {})
    occupied = {token.lstrip("$") for token in tokens.findall(source + query + rules)}
    translated = []
    for program in (source, query):
        edits = []
        for start, end, form in egglog_forms(program):
            kind = form[1]
            atoms = [m for m in tokens.finditer(program, start, end) if not m[0].startswith(";")]
            if kind in {"push", "pop", "include"} or any(
                atoms[i - 1][0] == "(" and atom[0] == "let" for i, atom in enumerate(atoms[2:], 2)
            ):
                raise CaptureError("Churchroad nested binding/scope needs a reviewed global adaptation")
            name = form[2] if kind == "let" else None
            if name is not None:
                alias = f"$churchroad-global-{name}"
                if name in bindings:
                    raise CaptureError("Churchroad global rebinding needs a reviewed adaptation")
                if alias.lstrip("$") in occupied:
                    raise ValueError("Churchroad global alias prefix collides with an existing atom")
                edits.append((atoms[2].start(), atoms[2].end(), alias))
            # Declaration names, sort names, schedule names and rule attributes
            # are not expression variables. The pinned source has no global
            # references in declaration defaults/merges or schedule conditions.
            if kind in {"sort", "datatype", "function", "constructor", "relation", "ruleset", "run", "run-schedule"}:
                if bindings and any(option in form for option in (":default", ":merge", ":until")):
                    raise CaptureError("Churchroad declaration/schedule expression needs a reviewed global adaptation")
            else:
                depth = 0
                attributes = False
                for i, atom in enumerate(atoms):
                    if atom[0] == "(":
                        depth += 1
                    elif atom[0] == ")":
                        depth -= 1
                    elif depth == 1 and atom[0].startswith(":"):
                        attributes = True
                    elif (
                        not attributes
                        and not (kind == "let" and i == 2)
                        and atoms[i - 1][0] != "("
                        and atom[0] in bindings
                    ):
                        edits.append((atom.start(), atom.end(), bindings[atom[0]]))
            if name is not None:
                bindings[name] = alias
        for start, end, replacement in sorted(edits, reverse=True):
            program = program[:start] + replacement + program[end:]
        translated.append(program)
    return translated[0], translated[1], bindings


def materialize_sessions(record: dict[str, Any], sessions: list[dict[str, Any]], attempt: Path) -> None:
    """Adapt syntax while preserving native state and existing output-root values."""
    family = record["family"]
    record["materialization"] = {
        "expected_sessions": len(sessions),
        "materialized_sessions": 0,
        "complete": False,
    }
    for index, session in enumerate(sessions):
        raw = attempt / f"session-{index:03}-{session['kind']}.raw.egg"
        raw.write_text(session["program"])
        roots = session["roots"]
        if family == "eggcc":
            content = adapt_eggcc(session["replay_program"]) + "\n" + session["extracts"] + "\n"
            contract = eggcc_root_contract(content, roots)
        else:
            chunks = []
            aliases: dict[str, str] = {}
            for part in session["parts"]:
                program, _, aliases = rename_churchroad_globals(
                    constructors(part), "", session["program"], aliases=aliases
                )
                chunks.append(program)
            content = "\n".join(chunks)
            # These placeholders remain available to all source rules; only
            # ordinary output extraction excludes them from its representatives.
            for _, end, tokens in reversed(egglog_forms(content)):
                if tokens[1] == "constructor" and tokens[2] in CHURCHROAD_PLACEHOLDERS:
                    content = content[: end - 1] + " :unextractable" + content[end - 1 :]
            roots = [{**root, "replay_alias": aliases[root["name"]]} for root in roots]
            content += "\n" + "\n".join(f"(extract {root['replay_alias']})" for root in roots) + "\n"
            contract = churchroad_circuit_contract(content, roots)
        replay = attempt / f"session-{index:03}-{session['kind']}.egg"
        replay.write_text(content)
        record["sessions"].append(
            {
                **{
                    key: value
                    for key, value in session.items()
                    if key not in {"program", "replay_program", "extracts", "parts"}
                },
                "session": index,
                "raw": str(raw),
                "replay": str(replay),
                "raw_sha256": sha256_file(raw),
                "replay_sha256": sha256_file(replay),
                "roots": roots,
                "output_contract": contract,
            }
        )
        record["materialization"]["materialized_sessions"] = len(record["sessions"])
    record["materialization"]["complete"] = True
    record["status"] = "ordinary-validation-pending"


def materialize_complete_events(
    record: dict[str, Any], attempt: Path, *, max_evidence_bytes: int = 384 * 1024**2
) -> dict[str, Any]:
    """Admit completed independent calls; retain any later parent failure separately."""
    try:
        events = read_events(attempt / "native-events", max_bytes=max_evidence_bytes)
        sessions = eggcc_sessions(events) if record["family"] == "eggcc" else [churchroad_mapping_session(events)]
        record["parent_completed"] = events[-1]["kind"] == "parent-complete"
        record["source_completion"] = {
            "status": "complete",
            "parent_completed": record["parent_completed"],
            "scope": "complete Egglog calls",
            "outputs": [],
        }
        materialize_sessions(record, sessions, attempt)
    except (OSError, CaptureError, ValueError, KeyError) as error:
        record.update(status="blocked", reason=str(error))
    return record


def capture_complete(
    family: str,
    cases: list[dict[str, Any]],
    destination: Path,
    checkout: Path,
    binary: Path,
    engine: Path,
    *,
    timeout_sec: float = 300,
    validate_ordinary: bool = False,
) -> list[dict[str, Any]]:
    """Run source programs serially and materialize under the same resource guard."""
    from scripts.reproduction_validation import validate_capture

    records = []
    for case in cases:
        attempt = destination / case["id"]
        events = attempt / "native-events"
        events.mkdir(parents=True)
        source = checkout / case["source"]
        command = ["env", f"EGGLOG_REPRO_CAPTURE_DIR={events.resolve()}"]
        if family == "eggcc":
            command += [str(binary), str(source), "--run-mode", "optimize", *case.get("native_options", [])]
        else:
            command += [
                f"CARGO_MANIFEST_DIR={checkout}",
                str(binary),
                "--filepath",
                str(source),
                "--top-module-name",
                case.get("top_module_name", "mul"),
                "--architecture",
                case.get("architecture", "xilinx-ultrascale-plus"),
                "--out-filepath",
                str(attempt / "native-output.v"),
            ]
        process = run_bounded_command(
            command, checkout, attempt / "native", timeout_sec=timeout_sec, require_guard=True
        )
        record = {
            "id": case["id"],
            "family": family,
            "revision": PINS[family],
            "command": command,
            "process": asdict(process),
            "source_sha256": sha256_file(source),
            "binary_sha256": sha256_file(binary),
            "replay_engine_sha256": sha256_file(engine),
            "status": "blocked",
            "workloads": [],
            "sessions": [],
        }
        if process.status not in {"success", "failure", "timed-out"}:
            record.update(status=process.status, reason=process.message or process.status)
        else:
            request = attempt / "materialize.json"
            request.write_text(json.dumps(record, default=str) + "\n")
            materialization = run_bounded_command(
                [sys.executable, str(Path(__file__).resolve()), str(request)],
                ROOT,
                attempt / "materialize",
                timeout_sec=timeout_sec,
                require_guard=True,
            )
            result = attempt / "materialized.json"
            if materialization.status != "success" or not result.is_file():
                record.update(status=materialization.status, reason=materialization.message or "materialization failed")
            else:
                record = json.loads(result.read_text())
                if validate_ordinary:
                    checked = validate_capture(record, engine, attempt / "validation", timeout_sec=timeout_sec)
                    record.update(
                        status="reproduced" if checked["status"] == "success" else checked["status"],
                        workloads=checked["workloads"],
                        reason=checked.get("reason"),
                    )
        (attempt / "capture.json").write_text(json.dumps(record, indent=2, default=str) + "\n")
        records.append(record)
        if record["status"] in {"resource-stopped", "memory-limit", "cancelled", "interrupted"}:
            break
    return records


if __name__ == "__main__":
    request = Path(sys.argv[1])
    result = materialize_complete_events(json.loads(request.read_text()), request.parent)
    (request.parent / "materialized.json").write_text(json.dumps(result, indent=2, default=str) + "\n")
