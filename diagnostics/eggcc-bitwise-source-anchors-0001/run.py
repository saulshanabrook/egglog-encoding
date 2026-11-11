"""Prepare a pinned Bitwise anchor diagnostic; native probes require --run-probes."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from collections import Counter, defaultdict
from collections.abc import Callable
from dataclasses import asdict
from pathlib import Path
from typing import Any

ENGINE_SHA256 = "7eb04703af3707fb60c1ebe8cef66a86f72de1dc55081c636b8ea38fe06229b2"
REPLAY_SHA256 = "ced29250ea65acb944aba02f05d92070c7aa0431017e85e26c3431ecf06f7768"
CAPTURE_SHA256 = "d9eb2fa090b404600bddfe68970e7a93c3457aa616b02114a9ecde839d1b2fbf"
INTENT_SHA256 = "1c7da56b5c7ac4a91dca39cc78585f18f5b17dafaeee7582351a7166a034bb74"
GRAPH_EVENT_SHA256 = "91563ff6f4179315e98ba6581abfbbc9aee8240e7864eb1dd6dc22ce3361c009"
PREFIX = "reproduction_2_"
ANCHORS = {
    "__tmp10": ("Assumption", "Assumption-136"),
    "__tmp98": ("Type", "Type-218"),
    "__tmp136": ("Type", "Type-255"),
    "__tmp196": ("Type", "Type-314"),
    "__tmp250": ("Type", "Type-366"),
    "__tmp306": ("Expr", "Expr-422"),
}


def parse_tree(tokens: list[str]) -> list[Any]:
    """Decode one already-tokenized form without evaluating any source action."""
    stack: list[list[Any]] = [[]]
    for token in tokens:
        if token == "(":
            stack.append([])
        elif token == ")":
            assert len(stack) > 1
            value = stack.pop()
            stack[-1].append(value)
        else:
            stack[-1].append(token)
    assert len(stack) == 1 and len(stack[0]) == 1 and isinstance(stack[0][0], list)
    return stack[0][0]


def prepare_variants(
    source: str, payload: dict[str, Any], capture_helpers: Any, parse_forms: Callable
) -> tuple[dict, dict]:
    """Bind only source-backed classes and preserve the complete selected-node query."""
    forms = parse_forms(source)
    checks = [(i, form) for i, form in enumerate(forms) if form[2][1] == "check"]
    assert [i for i, _ in checks] == list(range(998, 1004))
    initializer = forms[995]
    original_initializer = source[initializer[0] : initializer[1]]
    init_tree = parse_tree(initializer[2])
    assert init_tree[0:2] == ["rule", []] and init_tree[3:] == [":ruleset", "initialization"]
    assert source[forms[996][0] : forms[996][1]] == "(run initialization 1)"
    assert sum("initialization" in tokens and tokens[1] in {"run", "run-schedule"} for _, _, tokens in forms) == 1
    seed = original_initializer.split("; Program nodes\n", 1)[1].split("; Loop context unions\n", 1)[0]
    native_checks, native_roots = capture_helpers.eggcc_output_checks(
        payload["graph"], payload["program"], payload["batch"], seed
    )
    assert [tokens for _, _, tokens in parse_forms(native_checks)] == [form[2] for _, form in checks]
    assert native_roots[2]["name"] == "loop_subroutine" and native_roots[2]["selected_nodes"] == 226

    graph = payload["graph"]
    nodes = graph["nodes"]
    index: dict[tuple, set[str]] = defaultdict(set)
    for node in nodes.values():
        index[(node["op"], tuple(nodes[child]["eclass"] for child in node["children"]))].add(node["eclass"])
    bindings: dict[str, str] = {}
    binding_forms: dict[str, list[Any]] = {}

    def resolve(expression: Any) -> str:
        key: tuple[str, tuple[str, ...]]
        if isinstance(expression, str):
            if expression in bindings:
                return bindings[expression]
            key = (expression, ())
        else:
            assert isinstance(expression, list) and expression and isinstance(expression[0], str)
            key = (expression[0], tuple(resolve(child) for child in expression[1:]))
        choices = index.get(key, set())
        assert len(choices) == 1, f"native source lookup is absent or ambiguous: {key!r}"
        return next(iter(choices))

    for _, _, tokens in parse_forms(seed):
        form = parse_tree(tokens)
        if form[0] == "FunctionHasType":
            continue
        assert len(form) == 3 and form[0] == "let" and form[1] not in bindings
        bindings[form[1]] = resolve(form[2])
        binding_forms[form[1]] = form
    assert len(bindings) == 345
    reverse: dict[str, list[str]] = defaultdict(list)
    for name, class_id in bindings.items():
        reverse[class_id].append(name)
    anchor_names = {local: "reproduction_bitwise_anchor_" + local.removeprefix("__tmp") for local in ANCHORS}
    all_tokens = {token for _, _, tokens in forms for token in tokens}
    assert not set(anchor_names.values()) & all_tokens
    for local, (sort, class_id) in ANCHORS.items():
        assert bindings[local] == class_id, (local, bindings[local], class_id)
        assert reverse[class_id] == [local], f"anchor source identity is not unique: {local}"
        assert graph["class_data"][class_id]["type"] == sort
    assert binding_forms["__tmp306"][2][:2] == ["Function", '"loop_subroutine"']
    assert binding_forms["__tmp74"][2][:2] == ["Function", '"main"']
    assert bindings["__tmp74"] != bindings["__tmp306"]
    assert bindings["__tmp306"] == native_roots[2]["eclass"]
    dummy = [parse_tree(t) for _, _, t in forms if t[:3] == ["(", "let", "DUMMYCTX"]]
    assert dummy == [["let", "DUMMYCTX", ["InFunc", '"DUMMY"']]]
    assert resolve(dummy[0][2]) == "Assumption-48"
    assert graph["class_data"]["Assumption-48"]["let"] == "DUMMYCTX"

    selection = capture_helpers.tiger_selections(payload["program"])[2]
    query = capture_helpers.WitnessQuery(graph, PREFIX)
    erased_roots: set[str] = set()
    for node_id, _ in selection:
        node = nodes[node_id]
        kept = {"Arg": [], "Empty": [], "Const": [0]}.get(node["op"], list(range(len(node["children"]))))
        for position, child in enumerate(node["children"]):
            if position not in kept:
                erased_roots.add(child)
                query.original(child)
    assert len(query.originals) == 538 and len(erased_roots) == 6
    _, (start, end, _) = checks[2]
    check = source[start:end]
    opening = re.match(r"\(\s*check\b", check)
    assert opening is not None
    body = check[opening.end() : -1]
    facts = parse_forms(body)
    assert len(facts) == 1110
    selected = [(a, b, t) for a, b, t in facts if re.fullmatch(PREFIX + r"s\d+", t[2])]
    assert len(selected) == 226
    assert [t[2] for _, _, t in selected] == [PREFIX + f"s{i}" for i in range(226)]
    assert {token for _, _, tokens in selected for token in tokens if re.fullmatch(PREFIX + r"o\d+", token)} == {
        query.originals[node_id] for node_id in erased_roots
    }
    closure = [t for _, _, t in facts if re.fullmatch(PREFIX + r"o\d+", t[2])]
    assert closure == [parse_forms(fact)[0][2] for fact in query.facts]
    assert Counter(t[2].startswith(PREFIX + "seed") for _, _, t in facts) == {True: 346, False: 764}
    assert facts[-1][2] == ["(", "=", PREFIX + "seed306", PREFIX + "s225", ")"]
    identities = []
    identity_facts = []
    for node_id in sorted(erased_roots, key=lambda node_id: int(query.originals[node_id].split("_o")[1])):
        class_id = nodes[node_id]["eclass"]
        variable = query.originals[node_id]
        source_local: str | None
        if class_id == "Assumption-48":
            value = "DUMMYCTX"
            source_local = None
        else:
            assert len(reverse[class_id]) == 1
            source_local = reverse[class_id][0]
            assert source_local in anchor_names and source_local != "__tmp306"
            value = f"({anchor_names[source_local]})"
        identity_facts.append(f"(= {variable} {value})")
        identities.append(
            {"node": node_id, "class": class_id, "variable": variable, "source_local": source_local, "lookup": value}
        )
    assert {item["source_local"] for item in identities} == {
        None,
        "__tmp10",
        "__tmp98",
        "__tmp136",
        "__tmp196",
        "__tmp250",
    }
    root_fact = f"(= {PREFIX}seed306 ({anchor_names['__tmp306']}))"
    replacement_facts = [
        root_fact,
        *identity_facts,
        *(body[a:b] for a, b, _ in selected),
        body[facts[-1][0] : facts[-1][1]],
    ]
    assert len(replacement_facts) == 234
    replacement = "(check\n  " + "\n  ".join(replacement_facts) + "\n)"
    definitions = "".join(
        f"(function {anchor_names[local]} () {sort} :merge old)\n" for local, (sort, _) in ANCHORS.items()
    )
    assignments = "\n" + "".join(f"(set ({anchor_names[local]}) {local})\n" for local in ANCHORS)
    tail = re.search(r"\)\s*:ruleset initialization\s*\)$", original_initializer)
    assert tail is not None
    altered_initializer = original_initializer[: tail.start()] + assignments + original_initializer[tail.start() :]
    altered_tree = parse_tree(parse_forms(altered_initializer)[0][2])
    expected_sets = [["set", [anchor_names[local]], local] for local in ANCHORS]
    assert altered_tree[:2] == init_tree[:2] and altered_tree[3:] == init_tree[3:]
    assert altered_tree[2] == init_tree[2] + expected_sets
    assert altered_initializer.replace(assignments, "", 1) == original_initializer
    edits = [
        (start, end, replacement),
        (checks[0][1][0], checks[0][1][0], "(print-size)\n"),
        (initializer[0], initializer[1], definitions + altered_initializer),
    ]
    anchored = source
    for begin, finish, text in sorted(edits, reverse=True):
        anchored = anchored[:begin] + text + anchored[finish:]
    new_forms = parse_forms(anchored)
    normalized = []
    original_commands = [source[a:b] for a, b, _ in forms]
    for a, b, tokens in new_forms:
        command = anchored[a:b]
        if tokens[1] == "function" and tokens[2] in anchor_names.values():
            continue
        if tokens == ["(", "print-size", ")"]:
            continue
        if command == altered_initializer:
            command = original_initializer
        elif command == replacement:
            command = check
        normalized.append(command)
    assert normalized == original_commands, "an unapproved original command changed"
    assert len(new_forms) == len(forms) + 7
    assert [tokens for _, _, tokens in parse_forms(replacement[6:-1])] == [
        parse_forms(fact)[0][2] for fact in replacement_facts
    ]
    negative = anchored.replace(
        f"(set ({anchor_names['__tmp306']}) __tmp306)", f"(set ({anchor_names['__tmp306']}) __tmp74)", 1
    )
    assert negative != anchored
    assert (
        negative.replace(
            f"(set ({anchor_names['__tmp306']}) __tmp74)", f"(set ({anchor_names['__tmp306']}) __tmp306)", 1
        )
        == anchored
    )
    baseline = source[: checks[0][1][0]] + "(print-size)\n"
    assert parse_forms(baseline)[:-1] == forms[:998]
    return {"baseline-counts.egg": baseline, "anchored.egg": anchored, "negative-input.egg": negative}, {
        "meaning": "Source-backed identity replacement; not literal fact-token equivalence or corpus admission",
        "source_bindings_resolved": len(bindings),
        "source_binding_classes": bindings,
        "original_facts": len(facts),
        "anchored_facts": 234,
        "selected_facts_preserved_byte_for_byte": 226,
        "other_checks_preserved_byte_for_byte": 5,
        "original_actions_rules_and_schedules_preserved": True,
        "new_nonconstructor_tables": anchor_names,
        "new_assignments": expected_sets,
        "one_initialization_match_and_run": True,
        "erased_field_identities": identities,
        "input_class": bindings["__tmp306"],
        "input_source_local": "__tmp306",
        "negative_control_local": "__tmp74",
        "negative_control_class": bindings["__tmp74"],
        "selected_targets_inserted": False,
        "removed_auxiliary_closure_nodes": len(query.originals),
        "selected_fact_tokens_sha256": hashlib.sha256(json.dumps([t for _, _, t in selected]).encode()).hexdigest(),
        "admitted": False,
    }


def main() -> int:
    if not __debug__:
        raise RuntimeError("assertions are mandatory; do not use -O or PYTHONOPTIMIZE")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--run-probes", action="store_true", help="launch guarded native diagnostics after preparation")
    args = parser.parse_args()
    root, output = args.root.resolve(), args.output.resolve()
    durable = root / "benchmarks/local/reproduction/diagnostics"
    if not output.is_relative_to(durable.resolve()) or output.exists():
        raise ValueError("output must be fresh and below root/benchmarks/local/reproduction/diagnostics")
    sys.path.insert(0, str(root))
    from benchmarking.pilot import run_bounded_command
    from scripts import eggcc_churchroad_complete as capture_helpers
    from scripts.hardboiled_replay import egglog_forms
    from scripts.reproduction_process import exclusive_job

    previous = durable / "eggcc-bitwise-stage-boundary-0001/intent.json"
    previous_bytes = previous.read_bytes()
    assert hashlib.sha256(previous_bytes).hexdigest() == INTENT_SHA256
    receipt = Path(json.loads(previous_bytes)["capture"])
    receipt_bytes = receipt.read_bytes()
    assert hashlib.sha256(receipt_bytes).hexdigest() == CAPTURE_SHA256
    capture = json.loads(receipt_bytes)
    assert capture["parent_completed"] and capture["sessions"][2]["events"] == [5, 6, 9]
    replay = Path(capture["sessions"][2]["replay"])
    original = replay.read_bytes()
    assert hashlib.sha256(original).hexdigest() == REPLAY_SHA256
    event = replay.parent / "native-events/event-000006.json"
    event_bytes = event.read_bytes()
    assert hashlib.sha256(event_bytes).hexdigest() == GRAPH_EVENT_SHA256
    native = json.loads(event_bytes)
    assert native["sequence"] == 6 and native["kind"] == "tiger-result"
    variants, assertions = prepare_variants(original.decode(), native["payload"], capture_helpers, egglog_forms)
    engine = root / "target/release/egglog-experimental"
    files = {
        "engine": engine,
        "script": Path(__file__).resolve(),
        "parser": root / "scripts/hardboiled_replay.py",
        "capture_helper": root / "scripts/eggcc_churchroad_complete.py",
        "runner": root / "benchmarking/pilot.py",
        "guard": root / "benchmarking/memory_guard.py",
        "lock": root / "scripts/reproduction_process.py",
    }
    identities = {}
    for name, path in files.items():
        with path.open("rb") as stream:
            identities[name] = {"path": str(path), "sha256": hashlib.file_digest(stream, "sha256").hexdigest()}
    assert identities["engine"]["sha256"] == ENGINE_SHA256 == capture["replay_engine_sha256"].removeprefix("sha256:")
    output.mkdir(parents=True, exist_ok=False)
    for name, contents in variants.items():
        (output / name).write_text(contents)
    for name, contents in {
        "original.egg": original,
        "source-capture.json": receipt_bytes,
        "native-graph-event.json": event_bytes,
        "previous-diagnostic-intent.json": previous_bytes,
        "runner-source.py": Path(__file__).read_bytes(),
    }.items():
        (output / name).write_bytes(contents)
    intent = {
        "admitted": False,
        "run_probes_requested": args.run_probes,
        "assertions": assertions,
        "source_capture": str(receipt),
        "capture_sha256": CAPTURE_SHA256,
        "original_sha256": REPLAY_SHA256,
        "native_graph_sha256": GRAPH_EVENT_SHA256,
        "identities": identities,
        "variants": {name: hashlib.sha256(text.encode()).hexdigest() for name, text in variants.items()},
        "timeout_per_probe_sec": 60,
        "memory_limit_bytes": 5 * 1024**3,
        "disk_reserve_bytes": 10 * 1024**3,
        "require_guard": True,
        "allow_warning_pressure": True,
    }
    (output / "intent.json").write_text(json.dumps(intent, indent=2) + "\n")
    if not args.run_probes:
        print(json.dumps({"status": "prepared-only", "output": str(output), "admitted": False}))
        return 0
    outcomes = []
    baseline_counts = None
    names = set(assertions["new_nonconstructor_tables"].values())
    with exclusive_job(root / "benchmarks/local/reproduction/stages/.heavy-job.lock"):
        for filename in variants:
            command = ["/usr/bin/env", "RUST_LOG=egglog=info", str(engine), "-j", "1", str(output / filename)]
            prefix = output / filename.removesuffix(".egg")
            (Path(str(prefix) + ".command.json")).write_text(json.dumps(command, indent=2) + "\n")
            try:
                process = run_bounded_command(
                    command,
                    root,
                    prefix,
                    timeout_sec=60,
                    memory_limit_bytes=5 * 1024**3,
                    require_guard=True,
                    disk_reserve_bytes=10 * 1024**3,
                    allow_warning_pressure=True,
                )
            except (OSError, ValueError, RuntimeError) as error:
                outcomes.append({"variant": filename, "status": "launch-refused", "reason": str(error)})
                break
            (Path(str(prefix) + ".result.json")).write_text(json.dumps(asdict(process), indent=2, default=str) + "\n")
            counts = {}
            completed = 0
            failed_check = False
            with process.stderr_path.open() as stream:
                for line in stream:
                    if match := re.fullmatch(r"\[INFO \] Function (\S+) has size (\d+)\n?", line):
                        assert match[1] not in counts, "duplicate function-size receipt"
                        counts[match[1]] = int(match[2])
                    completed += line.startswith("[INFO ] Checked fact ")
                    failed_check |= "Check failed:" in line
            if filename == "baseline-counts.egg":
                passed = process.status == "success" and process.returncode == 0 and completed == 0 and bool(counts)
                baseline_counts = counts
            else:
                original_counts = {name: count for name, count in counts.items() if name not in names}
                counts_match = original_counts == baseline_counts and {
                    name: counts.get(name) for name in names
                } == dict.fromkeys(names, 1)
                passed = counts_match and (
                    (process.status == "success" and process.returncode == 0 and completed == 6 and not failed_check)
                    if filename == "anchored.egg"
                    else (process.status == "failure" and process.returncode == 1 and completed == 2 and failed_check)
                )
            outcomes.append(
                {
                    "variant": filename,
                    "process_status": process.status,
                    "completed_checks": completed,
                    "check_failure_observed": failed_check,
                    "visible_table_counts": counts,
                    "passed": passed,
                }
            )
            if not passed:
                break
    interpretation = {
        "status": "diagnostic-gates-passed"
        if len(outcomes) == 3 and all(o.get("passed") for o in outcomes)
        else "diagnostic-incomplete-or-failed",
        "outcomes": outcomes,
        "admitted": False,
        "limits": "Counts are a drift gate, not graph-equivalence proof; no corpus/proof/native-cost admission.",
    }
    (output / "interpretation.json").write_text(json.dumps(interpretation, indent=2) + "\n")
    print(json.dumps({"status": interpretation["status"], "output": str(output), "admitted": False}))
    return 0 if interpretation["status"] == "diagnostic-gates-passed" else 2


if __name__ == "__main__":
    raise SystemExit(main())
