"""Validate retained native output contracts using only standalone Egglog inputs."""

from __future__ import annotations

import hashlib
import json
import re
from dataclasses import asdict
from pathlib import Path
from typing import Any, cast

from benchmarking.targets import sha256_file
from scripts.dialegg_speq_complete import run_complete_command, validate_extract_output
from scripts.hardboiled_replay import egglog_forms, native_check_contract
from scripts.reproduction_published import INPUT_KIND, verify_published_capture

CHURCHROAD_PLACEHOLDERS = ("Wire", "PrimitiveInterfaceDSP", "PrimitiveInterfaceDSP3")


def churchroad_circuit_contract(source: str, roots: list[dict[str, Any]]) -> dict[str, Any]:
    """Bind ordinary circuit extracts to real output aliases and complete prior state.

    These are adapted extractions, with no native-selected expected term. Only
    extraction visibility changes: placeholders remain available to all rules.
    """
    forms = [tokens for _, _, tokens in egglog_forms(source)]
    if not roots or len({(root["module"], root["name"]) for root in roots}) != len(roots):
        raise ValueError("Churchroad circuit extraction requires distinct original output ports")
    ports = [form for form in forms if len(form) == 9 and form[1] == "IsPort" and form[4:7] == ["(", "Output", ")"]]
    if len(ports) != len(roots):
        raise ValueError("Churchroad circuit extraction must cover every original output port")
    marked = [tokens for tokens in forms if ":unextractable" in tokens]
    if sorted(tokens[2] for tokens in marked) != sorted(CHURCHROAD_PLACEHOLDERS) or any(
        tokens[1] != "constructor" or tokens[-2] != ":unextractable" for tokens in marked
    ):
        raise ValueError("Churchroad circuit extraction must exclude exactly the three placeholder constructors")
    extracts = [(index, tokens) for index, tokens in enumerate(forms) if tokens[1] == "extract"]
    if [index for index, _ in extracts] != list(range(len(forms) - len(roots), len(forms))):
        raise ValueError("Churchroad circuit extraction must end with one extract per original output")
    if any(tokens[1] in {"check", "prove", "prove-extract"} for tokens in forms):
        raise ValueError("Churchroad circuit extraction cannot add a chosen equality or executable proof")
    records = []
    for (position, tokens), root in zip(extracts, roots, strict=True):
        alias = root["replay_alias"]
        bindings = [form for form in forms if form[:3] == ["(", "let", alias]]
        if tokens != ["(", "extract", alias, ")"] or len(bindings) != 1 or len(bindings[0]) != 5:
            raise ValueError("Churchroad circuit extract lost its original output global")
        port = [
            "(",
            "IsPort",
            json.dumps(root["module"]),
            json.dumps(root["name"]),
            "(",
            "Output",
            ")",
            bindings[0][3],
            ")",
        ]
        if ports.count(port) != 1:
            raise ValueError("Churchroad circuit extract is not bound to its original output port")
        records.append(
            {
                "command": position,
                "tokens": tokens,
                "prefix_sha256": hashlib.sha256(json.dumps(forms[:position]).encode()).hexdigest(),
            }
        )
    return {
        "kind": "churchroad-circuit-extract",
        "roots": roots,
        "extracts": records,
        "excluded_constructors": list(CHURCHROAD_PLACEHOLDERS),
        "claims_native_selection": False,
        "claims_optimality": False,
    }


def _sexpr(tokens: list[str]) -> list[Any]:
    """Parse already-tokenized closed forms for typed constructor accounting."""
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


def static_extract_model(source: str, terms: list[list[str]]) -> dict[str, Any]:
    """Account only for closed, typed constructor trees with static additive costs.

    Containers, scoped declarations, dynamic costs and unknown primitive terms
    deliberately do not qualify. Counts are tree counts, including repeated
    children, and remain below both backends' integer-overflow boundaries.
    """
    forms = [tokens for _, _, tokens in egglog_forms(source)]
    unsupported = {"set-cost", "unstable-cost", "with-dynamic-cost", "push", "pop", ":unextractable"}
    if any(unsupported.intersection(tokens) for tokens in forms):
        raise ValueError("unsupported dynamic, scoped or unextractable cost model")
    trees = [_sexpr(tokens) for tokens in forms]
    eq_sorts = {tree[1] for tree in trees if tree[0] == "datatype" or (tree[0] == "sort" and len(tree) == 2)}
    constructors: dict[str, dict[str, Any]] = {}
    for tree in trees:
        declarations = []
        if tree[0] == "datatype":
            for variant in tree[2:]:
                if not isinstance(variant, list):
                    raise ValueError("unsupported datatype declaration")
                tail = variant.index(":cost") if ":cost" in variant else len(variant)
                declarations.append((variant[0], variant[1:tail], tree[1], variant[tail:]))
        elif tree[0] in {"constructor", "function"} and tree[3] in eq_sorts:
            # Historical functions with merge actions are not constructors.
            if tree[0] == "function" and ":merge" in tree:
                continue
            declarations.append((tree[1], tree[2], tree[3], tree[4:]))
        for name, inputs, output, options in declarations:
            if options and (len(options) != 2 or options[0] != ":cost"):
                raise ValueError("unsupported constructor cost options")
            cost = int(options[1]) if options else 1
            if cost < 0 or cost >= 2**63 or name in constructors or not all(isinstance(t, str) for t in inputs):
                raise ValueError("ambiguous or unsupported constructor cost declaration")
            constructors[name] = {"inputs": inputs, "output": output, "cost": cost}

    def term_cost(term: Any, expected_sort: str | None = None) -> int:
        if isinstance(term, str):
            valid = (
                (expected_sort == "String" and term.startswith('"') and term.endswith('"'))
                or (expected_sort == "i64" and re.fullmatch(r"-?\d+", term) and -(2**63) <= int(term) < 2**63)
                or (expected_sort == "f64" and re.fullmatch(r"-?(?:\d+\.\d*|\d*\.\d+)(?:[eE][+-]?\d+)?", term))
            )
            if not valid:
                raise ValueError("unsupported or ill-typed primitive in static output")
            return 1
        if not term or term[0] not in constructors:
            raise ValueError("output uses an unsupported constructor/container")
        schema = constructors[term[0]]
        if (expected_sort is not None and schema["output"] != expected_sort) or len(term) - 1 != len(schema["inputs"]):
            raise ValueError("ill-typed constructor output")
        cost = schema["cost"] + sum(term_cost(arg, sort) for arg, sort in zip(term[1:], schema["inputs"], strict=True))
        if cost >= 2**63:
            raise ValueError("static tree cost may overflow a historical backend")
        return int(cost)

    costs = [term_cost(_sexpr(tokens)) for tokens in terms]
    return {
        "semantics": "typed-static-additive-tree-v1",
        "primitive_cost": 1,
        "constructors": constructors,
        "costs": costs,
    }


def static_native_contract(source: str, terms: list[list[str]], native_costs: list[int]) -> dict[str, Any]:
    """Bind every unchanged best extract to its preceding native-membership query."""
    validate_extract_output(source, "\n".join(" ".join(term) for term in terms))
    model = static_extract_model(source, terms)
    if not terms or model["costs"] != native_costs:
        raise ValueError("native extractor cost logs disagree with the typed static model")
    forms = [tokens for _, _, tokens in egglog_forms(source)]
    extracts = [(i, tokens) for i, tokens in enumerate(forms) if tokens[1] == "extract"]
    roots = []
    checks = []
    for (position, tokens), term, cost in zip(extracts, terms, native_costs, strict=True):
        check = f"(check (= {tokens[2]} {' '.join(term)}))"
        checks.append((position - 1, check))
        roots.append({"extract_request": tokens, "native_term": term, "native_cost": cost})
    return {
        "kind": "ordinary-best-static-native",
        "expected_terms": terms,
        "native_costs": native_costs,
        "cost_model": model,
        "membership": native_check_contract(source, checks, roots),
    }


def materialize_static_native_contract(
    source: str, terms: list[list[str]], native_costs: list[int]
) -> tuple[str, dict[str, Any]]:
    """Insert queries only; leave every original command and extraction option intact."""
    validate_extract_output(source, "\n".join(" ".join(term) for term in terms))
    extracts = [form for form in egglog_forms(source) if form[2][1] == "extract"]
    for (start, _, tokens), term in reversed(list(zip(extracts, terms, strict=True))):
        source = source[:start] + f"(check (= {tokens[2]} {' '.join(term)}))\n" + source[start:]
    return source, static_native_contract(source, terms, native_costs)


def validate_static_native_output(source: str, contract: dict[str, Any], stdout: str, stderr: str) -> dict[str, Any]:
    """Require native membership plus both observed minimum costs, not pretty-print equivalence."""
    expected = static_native_contract(source, contract["expected_terms"], contract["native_costs"])
    if contract != expected:
        raise ValueError("static native output contract or extraction boundary changed")
    outputs = validate_extract_output(source, stdout)
    model = static_extract_model(source, outputs)
    logged = [int(cost) for cost in re.findall(r"Best cost for the extract root: (\d+)\b", stderr)]
    if model["costs"] != logged or logged != contract["native_costs"]:
        raise ValueError("replay extractor cost logs, typed tree costs and native minimum costs must agree")
    return {
        "native_costs": contract["native_costs"],
        "replay_costs": logged,
        "exact_terms": outputs == contract["expected_terms"],
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
        published = capture.get("input_kind") == INPUT_KIND
        if published:
            verify_published_capture(capture)
        elif capture.get("source_completion", {}).get("status") not in {"success", "complete"}:
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
                "ordinary-best-static-native",
                "query-only-native-output-equality",
                "churchroad-circuit-extract",
                *({INPUT_KIND} if published else set()),
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
            elif contract["kind"] == "churchroad-circuit-extract" and contract != churchroad_circuit_contract(
                source, contract["roots"]
            ):
                raise ValueError("Churchroad circuit extraction boundary or preceding graph state changed")
            if contract["kind"] == "ordinary-best-static-native":
                expected = static_native_contract(source, contract["expected_terms"], contract["native_costs"])
                if contract != expected:
                    raise ValueError("static native output contract or extraction boundary changed")
            command = [str(engine.resolve()), "-j", "1", str(replay.resolve())]
            if contract["kind"] == "ordinary-best-static-native":
                command = ["env", "RUST_LOG=egglog::extract=debug", *command]
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
            if contract["kind"] == "churchroad-circuit-extract":
                if any(
                    tokens[index - 1] == "(" and token in CHURCHROAD_PLACEHOLDERS
                    for tokens in outputs
                    for index, token in enumerate(tokens)
                ):
                    raise ValueError("Churchroad circuit extraction returned a placeholder instead of a circuit")
                row["extracted_circuits"] = [
                    {"root": root, "term": term} for root, term in zip(contract["roots"], outputs, strict=True)
                ]
            if contract and contract["kind"] == "ordinary-best-extract" and outputs != contract["expected_terms"]:
                raise ValueError("ordinary extraction differs from the native output contract")
            if contract["kind"] == "ordinary-best-static-native":
                row["cost_validation"] = validate_static_native_output(
                    source, contract, process.stdout_path.read_text(), process.stderr_path.read_text()
                )
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
