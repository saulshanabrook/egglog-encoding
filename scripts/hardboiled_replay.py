"""Static HardBoiled modernization and historical query diagnostics; never runs an engine.

``adapt RAW OUTPUT`` writes the benchmark with every original extraction retained.
The ``freeze`` command is only a historical equality diagnostic, not a benchmark
preparation step. After a guarded ordinary
extraction run, ``freeze SOURCE STDOUT OBSERVATION DIRECTORY`` writes one query
and its initialization control. OBSERVATION must record success/returncode=0,
input_sha256, stdout_sha256 and engine_sha256. Controls remain a separate gate.
Consider roots in source order, advancing only after the preceding query was
established without the schedule; never select by measured runtime.
"""

from __future__ import annotations

import hashlib
import json
import re
from typing import Any

ORIGINAL_SCHEDULE = [
    "(",
    "run-schedule",
    "(",
    "repeat",
    "20",
    "(",
    "saturate",
    "(",
    "run",
    "typechecking",
    ")",
    ")",
    "(",
    "run",
    ")",
    "(",
    "run",
    "amx",
    ")",
    ")",
    ")",
]


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


def egglog_forms(source: str) -> list[tuple[int, int, list[str]]]:
    """Read balanced top-level forms, preserving strings, comments and offsets."""
    depth = 0
    start = 0
    end = 0
    tokens: list[str] = []
    result = []
    for match in re.finditer(r';[^\n]*|"(?:\\.|[^"\\])*"|[()]|[^\s();"]+', source):
        if source[end : match.start()].strip():
            raise ValueError("invalid or unterminated quoted token")
        end = match.end()
        token = match.group()
        if token.startswith(";"):
            continue
        if token == "(":
            if depth == 0:
                start = match.start()
                tokens = []
            depth += 1
        if depth <= 0:
            raise ValueError("non-expression output or unmatched closing parenthesis")
        tokens.append(token)
        if token == ")":
            depth -= 1
            if depth == 0:
                if len(tokens) < 3:
                    raise ValueError("empty top-level expression")
                result.append((start, end, tokens))
    if depth or source[end:].strip():
        raise ValueError("unclosed expression or quoted token")
    return result


def omit_unexecuted_keep_best(source: str) -> str:
    """Reject scheduled/dynamically referenced keep-best; omit its dead rule only."""
    parsed = egglog_forms(source)
    uses = [form for form in parsed if "keep-best" in form[2]]
    if not uses:
        return source
    scheduling = {"run", "run-schedule", "include", "unstable-combined-ruleset", "push", "pop"}
    schedules = [form for form in parsed if form[2][1] in scheduling]
    if len(schedules) != 1 or schedules[0][2] != ORIGINAL_SCHEDULE:
        raise ValueError("keep-best requires the closed original 20-iteration schedule")
    declarations = [form for form in uses if form[2] == ["(", "ruleset", "keep-best", ")"]]
    rules = [form for form in uses if form[2][:7] == ["(", "rule", "(", ")", "(", "(", "keep-best"]]
    if len(uses) != 2 or len(declarations) != 1 or len(rules) != 1:
        raise ValueError("keep-best is referenced beyond its unscheduled definition")
    start, end, tokens = rules[0]
    if tokens[-5:] != [")", ")", ":ruleset", "keep-best", ")"]:
        raise ValueError("keep-best action is not isolated in the unscheduled ruleset")
    return source[:start] + "; Unexecuted keep-best rule definition omitted: see static-audit.json.\n" + source[end:]


def omit_unexecuted_higher_order_rules(source: str) -> str:
    """Omit higher-order rules only under the closed, unscheduled canonicalize case."""
    parsed = egglog_forms(source)
    uses = [form for form in parsed if {"unstable-app", "unstable-fn"}.intersection(form[2])]
    if not uses:
        return source
    scheduling = {"run", "run-schedule", "include", "unstable-combined-ruleset", "push", "pop"}
    schedules = [form for form in parsed if form[2][1] in scheduling]
    if len(schedules) != 1 or schedules[0][2] != ORIGINAL_SCHEDULE:
        raise ValueError("higher-order omission requires the closed original 20-iteration schedule")
    if any(tokens[1] != "rule" or tokens[-3:] != [":ruleset", "canonicalize", ")"] for _, _, tokens in uses):
        raise ValueError("higher-order primitive is used outside unscheduled canonicalize rules")
    for start, end, _ in reversed(uses):
        source = source[:start] + "; Unexecuted higher-order canonicalize rule omitted.\n" + source[end:]
    return source


def freeze_extraction_query(source: str, stdout: str, root_index: int = 0) -> tuple[str, str, str]:
    """Replace terminal extracts by one frozen equality; never construct a target."""
    parsed = egglog_forms(source)
    schedules = [form for form in parsed if form[2][1] == "run-schedule"]
    if len(schedules) != 1 or schedules[0][2] != ORIGINAL_SCHEDULE:
        raise ValueError("query source does not preserve the original schedule")
    extractions = [form for form in parsed if form[2][1] == "extract"]
    if not extractions or any(len(form[2]) != 4 for form in extractions):
        raise ValueError("expected original named-root extractions")
    if parsed[-len(extractions) :] != extractions or extractions[0][0] < schedules[0][1]:
        raise ValueError("extractions must be terminal and follow the original schedule")
    outputs = egglog_forms(stdout)
    if len(outputs) != len(extractions):
        raise ValueError("ordinary output count differs from original extraction roots")
    prohibited = {"let", "rule", "rewrite", "birewrite", "check", "run", "run-schedule", "include", "extract"}
    for _, _, tokens in outputs:
        if tokens[1] in prohibited or any(token.startswith("$") for token in tokens):
            raise ValueError("ordinary output is not a closed extracted expression")
    if not 0 <= root_index < len(extractions):
        raise ValueError("root index is outside original extraction order")
    start, end, _ = outputs[root_index]
    query = f"(check (= {extractions[root_index][2][2]} {stdout[start:end]}))"
    replay = source
    for start, end, _ in reversed(extractions):
        replay = replay[:start] + replay[end:]
    replay = replay.rstrip() + "\n" + query + "\n"
    start, end, _ = schedules[0]
    negative = replay[:start] + "; Original schedule omitted for negative query control only.\n" + replay[end:]
    return replay, negative, query


def check_observed_selections(source: str, stdout: str) -> tuple[str, list[dict[str, str]]]:
    """Check every real sidecar selection where its original extraction occurred.

    These checks only query existing facts. They do not seed the selected terms,
    change the schedule, or claim optimality. Keep ordinary extraction requests
    too, so their root/variant contract remains visible in the standalone input.
    """
    extractions = [form for form in egglog_forms(source) if form[2][1] == "extract"]
    if not extractions or any(len(tokens) != 4 for _, _, tokens in extractions):
        raise ValueError("expected one named root per sidecar extraction")
    outputs = egglog_forms(stdout)
    if len(outputs) != len(extractions):
        raise ValueError("sidecar selection count differs from extraction roots")
    prohibited = {"let", "rule", "rewrite", "birewrite", "union", "set", "check", "run", "run-schedule", "include"}
    selections = []
    for (_, _, tokens), (start, end, output_tokens) in zip(extractions, outputs, strict=True):
        if output_tokens[1] in prohibited or any(token.startswith("$") for token in output_tokens):
            raise ValueError("sidecar selection must be a closed expression")
        root = tokens[2]
        if root in {"(", ")"} or root.startswith('"'):
            raise ValueError("sidecar extraction root must be a named value")
        selected = stdout[start:end]
        selections.append({"root": root, "selected": selected, "check": f"(check (= {root} {selected}))"})
    # Reverse insertion preserves every original command and push/pop boundary.
    for (_, end, _), selection in reversed(list(zip(extractions, selections, strict=True))):
        source = source[:end] + "\n" + selection["check"] + source[end:]
    return source, selections


def require_query_controls(positive: dict[str, Any], negative: dict[str, Any], negative_stderr: str) -> None:
    """Reject parser failures, crashes, resource stops and seeded query witnesses."""
    if (
        positive.get("halt")
        or negative.get("halt")
        or positive["status"] != "success"
        or positive["returncode"] != 0
        or negative["status"] != "failure"
        or negative["returncode"] != 1
        or re.search(r"(?m)^\s*Check failed:", negative_stderr) is None
    ):
        raise ValueError("positive execution and genuine unestablished-query control required")
