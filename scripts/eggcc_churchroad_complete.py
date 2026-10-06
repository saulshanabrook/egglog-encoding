"""Retain complete source computations and extract their original output roots.

Native Tiger still supplies later Eggcc passes. Replay uses ordinary Egglog
extraction, without claiming Tiger's selected program or effect linearity.
"""

from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path
from typing import Any, cast

from scripts.hardboiled_replay import egglog_forms

CHURCHROAD_MODULE_ENUM_SHA256 = "8c7f41ab787291fff683f36297436a5bbf74172c0d5675b495a2d7d543f3cf58"


class CaptureError(ValueError):
    """The native evidence does not identify a complete standalone computation."""


class CaptureResourceError(CaptureError):
    """Evidence exceeds the explicit in-process materialization budget."""


def read_events(directory: Path, *, max_bytes: int = 128 * 1024**2) -> list[dict[str, Any]]:
    """Reject incomplete writes and sequence gaps, independently of parent success."""
    paths = sorted(directory.glob("event-*.json"))
    total_bytes = sum(path.stat().st_size for path in paths)
    if max_bytes <= 0 or total_bytes > max_bytes:
        raise CaptureResourceError(f"native evidence is {total_bytes} bytes; materialization budget is {max_bytes}")
    events = []
    for index, path in enumerate(paths):
        try:
            event = json.loads(path.read_text())
        except (json.JSONDecodeError, UnicodeError) as error:
            raise CaptureError(f"incomplete native event {path.name}: {error}") from error
        if path.name != f"event-{index:06}.json" or event.get("sequence") != index:
            raise CaptureError(f"native event sequence is not contiguous at {path.name}")
        if event.get("version") != 1 or not isinstance(event.get("payload"), dict):
            raise CaptureError(f"unsupported native event contract in {path.name}")
        events.append(event)
    if not events:
        raise CaptureError("native execution did not retain any completed calls")
    return events


def _tree(tokens: list[str]) -> list[Any]:
    """Parse a tokenized closed command while preserving literal spellings."""
    stack: list[list[Any]] = [[]]
    for token in tokens:
        if token == "(":
            child: list[Any] = []
            stack[-1].append(child)
            stack.append(child)
        elif token == ")":
            stack.pop()
        else:
            stack[-1].append(token)
    return cast(list[Any], stack[0][0])


def eggcc_sessions(events: list[dict[str, Any]]) -> list[dict[str, Any]]:
    """Expose the author's existing Function values without rebuilding any term.

    The capture patch records each printer-returned root variable in a comment.
    These bindings are local to the once-run initializer, so store their values
    there and extract those handles after the untouched optimization schedule.
    A failed later pass does not discard a completed independent invocation.
    """
    sessions = []
    for event in events:
        if event["kind"] == "parent-complete":
            continue
        if event["kind"] != "optimization-complete":
            raise CaptureError(f"unexpected Eggcc capture boundary: {event['kind']}")
        payload = event["payload"]
        source, batch = payload["program"], payload["batch"]
        forms = egglog_forms(source)
        trees = [_tree(tokens) for _, _, tokens in forms]
        if any(token.startswith("reproduction_root_") for _, _, tokens in forms for token in tokens):
            raise CaptureError("source collides with an extraction root handle")
        initializers = [
            i
            for i, (start, end, _) in enumerate(forms)
            if "; Program nodes\n" in source[start:end] and "; Loop context unions\n" in source[start:end]
        ]
        if len(initializers) != 1:
            raise CaptureError("Eggcc source must identify exactly one initializer")
        index = initializers[0]
        initializer = trees[index]
        if len(initializer) != 5 or initializer[:2] != ["rule", []] or initializer[3] != ":ruleset":
            raise CaptureError("Eggcc initializer must be an empty-body rule")
        ruleset = initializer[4]
        uses = [i for i, (_, _, tokens) in enumerate(forms) if ruleset in tokens]
        if (
            index + 1 >= len(trees)
            or trees[index + 1] != ["run", ruleset, "1"]
            or len(uses) != 3
            or trees[uses[0]] != ["ruleset", ruleset]
            or uses[1:] != [index, index + 1]
        ):
            raise CaptureError("Eggcc initializer must run exactly once before its schedule")
        if not any(tree[0] == "run-schedule" for tree in trees[index + 2 :]):
            raise CaptureError("Eggcc source has no optimization schedule")
        start, end, _ = forms[index]
        init_text = source[start:end]
        markers = re.findall(r'^\s*; capture-root ("(?:\\.|[^"\\])*") (\S+)\s*$', init_text, re.MULTILINE)
        if not batch or len(batch) != len(set(batch)) or [json.loads(name) for name, _ in markers] != batch:
            raise CaptureError("Eggcc printer roots do not match the original function batch")
        roots = []
        for ordinal, (name, binding) in enumerate(markers):
            actions = [action for action in initializer[2] if action[:2] == ["let", binding]]
            if (
                len(actions) != 1
                or len(actions[0]) != 3
                or not isinstance(actions[0][2], list)
                or len(actions[0][2]) != 5
                or actions[0][2][:2] != ["Function", name]
            ):
                raise CaptureError("Eggcc printer root is not its original Function binding")
            roots.append({"name": json.loads(name), "binding": binding, "table": f"reproduction_root_{ordinal}"})
        tail = re.search(r"\)\s*:ruleset\s+" + re.escape(ruleset) + r"\s*\)$", init_text)
        if tail is None:
            raise CaptureError("Eggcc initializer action boundary changed")
        declarations = "".join(f"(function {root['table']} () Expr :merge old)\n" for root in roots)
        assignments = "".join(f"(set ({root['table']}) {root['binding']})\n" for root in roots)
        replay = (
            source[:start] + declarations + init_text[: tail.start()] + assignments + source[start + tail.start() :]
        )
        sessions.append(
            {
                "kind": "optimization",
                "pass": payload["pass"],
                "batch": batch,
                "program": source,
                "replay_program": replay,
                "extracts": "\n".join(f"(extract ({root['table']}))" for root in roots),
                "roots": roots,
                "events": [event["sequence"]],
            }
        )
    if not sessions:
        raise CaptureError("Eggcc has no completed optimization calls")
    return sessions


def churchroad_mapping_session(events: list[dict[str, Any]]) -> dict[str, Any]:
    """Preserve the entire persistent mapping computation, then extract its ports."""
    expected = [kind for _ in range(5) for kind in ("commands", "commands-result")] + ["mapping-complete"]
    if [event["kind"] for event in events] != expected:
        raise CaptureError("Churchroad lacks a complete ordered initialization and mapping phase")
    if any(event["payload"].get("success") is not True for event in events[1:-1:2]):
        raise CaptureError("Churchroad contains an unsuccessful native Egglog call")
    commands = events[:-1:2]
    if commands[-1]["payload"]["program"].strip() != "(run-schedule (saturate (seq typing transform mapping)))":
        raise CaptureError("Churchroad did not run the full original saturation schedule")
    omitted = commands[1]
    if (
        not (omitted["payload"].get("include_path") or "").endswith("/module_enumeration_rewrites.egg")
        or hashlib.sha256(omitted["payload"]["program"].encode()).hexdigest() != CHURCHROAD_MODULE_ENUM_SHA256
    ):
        raise CaptureError("Churchroad module-enumeration declarations changed")
    active = [event["payload"]["program"] for event in commands if event is not omitted]
    for program in active:
        forms = [tokens for _, _, tokens in egglog_forms(program)]
        if any("enumerate-modules" in tokens or tokens[1] in {"include", "reset", "push", "pop"} for tokens in forms):
            raise CaptureError("Churchroad active module enumeration or changed scope cannot be omitted")
    imported = [_tree(tokens) for _, _, tokens in egglog_forms(commands[2]["payload"]["program"])]
    names = events[-1]["payload"]["outputs"]
    ports = [form for form in imported if len(form) == 5 and form[0] == "IsPort" and form[3] == ["Output"]]
    if not names or len(names) != len(set(names)) or len(ports) != len(names):
        raise CaptureError("Churchroad output inventory does not match its original ports")
    roots = []
    for name in names:
        matches = [port for port in ports if port[2] == json.dumps(name)]
        if len(matches) != 1 or imported.count(["let", name, matches[0][4]]) != 1:
            raise CaptureError("Churchroad output lacks its original imported global alias")
        roots.append({"name": name, "module": json.loads(matches[0][1])})
    return {
        "kind": "circuit-extraction",
        "phase_boundary": "complete mapping saturation followed by ordinary output extraction before synthesis",
        "program": "\n".join(event["payload"]["program"] for event in commands),
        "parts": active,
        "roots": roots,
        "events": [event["sequence"] for event in events],
        "omitted_declarations": {
            "event": omitted["sequence"],
            "sha256": CHURCHROAD_MODULE_ENUM_SHA256,
            "reason": "closed native mapping schedule never references enumerate-modules",
        },
    }
