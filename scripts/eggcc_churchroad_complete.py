"""Native capture patches and fail-closed output witnesses for Eggcc/Churchroad.

The patches observe native execution without replacing its extractor or feedback.
Replays distinguish full native results from explicitly scoped completed phases;
adapted behavioral circuit extraction makes no native-selection claim.
"""

from __future__ import annotations

import difflib
import hashlib
import json
import math
import re
import struct
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any

from scripts.hardboiled_replay import egglog_forms


class CaptureError(ValueError):
    """Native evidence is incomplete or cannot yet be represented faithfully."""


class CaptureResourceError(CaptureError):
    """Evidence exceeds the explicit in-process materialization budget."""


RUST_CAPTURE = r"""
// Observation only: exclusive files preserve every boundary, including failures.
pub fn reproduction_capture(kind: &str, payload: serde_json::Value) {
    use std::io::Write;
    use std::sync::atomic::{AtomicUsize, Ordering};
    static SEQUENCE: AtomicUsize = AtomicUsize::new(0);
    if let Some(directory) = std::env::var_os("EGGLOG_REPRO_CAPTURE_DIR") {
        let sequence = SEQUENCE.fetch_add(1, Ordering::SeqCst);
        let path = std::path::Path::new(&directory).join(format!("event-{sequence:06}.json"));
        let mut file = std::fs::OpenOptions::new().write(true).create_new(true).open(path).unwrap();
        let event = serde_json::json!({"version": 1, "sequence": sequence,
            "kind": kind, "payload": payload});
        serde_json::to_writer(&mut file, &event).unwrap();
        file.write_all(b"\n").unwrap();
        file.sync_all().unwrap();
    }
}
"""

TIGER_SELECTION = r"""
    // Keep original node provenance before printing the lossy DumT/DumC form.
    if (std::getenv("EGGLOG_REPRO_CAPTURE_DIR")) {
        printf("; reproduction-selection-begin\n");
        for (size_t capture_i = 0; capture_i < e.size(); ++capture_i) {
            const ENode &capture_node = g.eclasses[e[capture_i].c].enodes[e[capture_i].n];
            printf("; reproduction-node ");
            for (unsigned char byte : capture_node.get_name()) printf("%02x", byte);
            for (auto child : e[capture_i].ch) printf(" %d", child);
            printf("\n");
        }
        printf("; reproduction-selection-end\n");
    }
"""

CHURCHROAD_MODULE_ENUM_SHA256 = "8c7f41ab787291fff683f36297436a5bbf74172c0d5675b495a2d7d543f3cf58"

CHURCHROAD_RUN = r"""
pub trait ReproductionRun {
    fn reproduction_run_program(&mut self, filename: Option<String>, source: &str)
        -> Result<Vec<String>, egglog::Error>;
}
impl ReproductionRun for egglog::EGraph {
    fn reproduction_run_program(&mut self, filename: Option<String>, source: &str)
        -> Result<Vec<String>, egglog::Error> {
        // All instrumented native callsites use None. Retain the actual included
        // bytes while executing the original include, with its original context.
        let included = source.trim().strip_prefix("(include ").and_then(|s| s.strip_suffix(')'));
        let (program, include_path) = if let Some(argument) = included {
            let path: String = serde_json::from_str(argument.trim()).unwrap();
            (std::fs::read_to_string(&path).unwrap(), Some(path))
        } else { (source.to_owned(), None) };
        reproduction_capture("commands", serde_json::json!({
            "program": program, "include_path": include_path, "original": source}));
        let result = self.parse_and_run_program(filename, source);
        reproduction_capture("commands-result", serde_json::json!({
            "success": result.is_ok(), "output": format!("{:?}", &result)}));
        result
    }
}
"""


def patched_eggcc_sources(checkout: Path) -> dict[str, str]:
    """Return pinned, guarded instrumentation; never mutate the source checkout.

    Exact boundaries deliberately fail when upstream code changes. That requires
    reviewing a new revision instead of reporting an uninstrumented run complete.
    """
    edits: dict[str, list[tuple[str, str]]] = {
        "dag_in_context/src/lib.rs": [
            ("pub type Result =", RUST_CAPTURE + "\npub type Result ="),
            (
                "            let mut egraph = new_single_threaded_egraph();\n"
                "            egraph.parse_and_run_program(None, &egglog_prog)?;",
                '            reproduction_capture("optimization-start", serde_json::json!({\n'
                '                "pass": i, "batch": &batch, "program": &egglog_prog,\n'
                '                "expected_passes": schedule_list.len(), "cutoff": cutoff}));\n'
                "            let mut egraph = new_single_threaded_egraph();\n"
                "            egraph.parse_and_run_program(None, &egglog_prog)?;",
            ),
            (
                "    // Tiger returns an egglog file containing just one program, run the egglog program",
                '    reproduction_capture("tiger-result", serde_json::json!({\n'
                '        "graph": egraph, "batch": batch, "program": &tiger_output,\n'
                '        "arguments": tiger_args.iter().map(|s| s.to_string_lossy().into_owned()).collect::<Vec<_>>()\n'
                "    }));\n"
                "    // Tiger returns an egglog file containing just one program, run the egglog program",
            ),
            (
                "        extract_program_with_egglog(original_prog, batch, &mut tiger_egraph).override_arg_types();",
                "        extract_program_with_egglog(original_prog, batch, &mut tiger_egraph).override_arg_types();\n"
                '    reproduction_capture("reconstruction-complete", serde_json::json!({"batch": batch}));',
            ),
            (
                "    for value_term in output_terms {",
                "    let mut reproduction_outputs = Vec::new();\n    for value_term in output_terms {",
            ),
            (
                "                if extracted.insert(func_name.clone(), expr.clone()).is_some() {",
                "                reproduction_outputs.push(serde_json::json!({\n"
                '                    "name": func_name, "program": print_with_intermediate_vars(&termdag, value_term)\n'
                "                }));\n"
                "                if extracted.insert(func_name.clone(), expr.clone()).is_some() {",
            ),
            (
                "    let mut res = original_prog.clone();",
                '    reproduction_capture("reconstruction-outputs", serde_json::json!({\n'
                '        "batch": batch, "outputs": reproduction_outputs}));\n'
                "    let mut res = original_prog.clone();",
            ),
            (
                "            iter_result.typecheck();",
                "            iter_result.typecheck();\n"
                '            reproduction_capture("optimization-complete", serde_json::json!({\n'
                '                "pass": i, "batch": &batch, "typechecked": true}));',
            ),
        ],
        "src/main.rs": [
            (
                "    let eggcc_duration = start_time.elapsed();",
                '    dag_in_context::reproduction_capture("parent-complete", serde_json::json!({\n'
                '        "result": &result, "outputs": &result.visualizations}));\n'
                "    let eggcc_duration = start_time.elapsed();",
            ),
        ],
        "dag_in_context/src/tiger/toegglog.cpp": [
            ("#include <cassert>", "#include <cassert>\n#include <cstdlib>"),
            (
                "void print_egg_extraction(const EGraph &g, const Extraction &e) {",
                "void print_egg_extraction(const EGraph &g, const Extraction &e) {" + TIGER_SELECTION,
            ),
        ],
    }
    patched = {}
    for relative, replacements in edits.items():
        source = (checkout / relative).read_text()
        for before, after in replacements:
            if source.count(before) != 1:
                raise CaptureError(f"Eggcc instrumentation boundary changed in {relative}: {before[:90]!r}")
            source = source.replace(before, after, 1)
        patched[relative] = source
    return patched


def patched_churchroad_sources(checkout: Path) -> dict[str, str]:
    """Observe the native persistent graph, synthesis feedback, and selections."""
    edits: dict[str, list[tuple[str, str]]] = {
        "src/main.rs": [
            (
                "use std::collections::HashMap;",
                "use churchroad::{ReproductionRun, reproduction_capture};\nuse std::collections::HashMap;",
            ),
            (
                "    let output_names_and_bws: Vec<_> = {",
                '    reproduction_capture("initial-roots", serde_json::json!({\n'
                '        "names": outputs.iter().map(|(_, name)| name).collect::<Vec<_>>() }));\n'
                "    let output_names_and_bws: Vec<_> = {",
            ),
            (
                "    let node_ids = find_primitive_interfaces_serialized(&serialized_egraph);",
                "    let node_ids = find_primitive_interfaces_serialized(&serialized_egraph);\n"
                '    reproduction_capture("mapping-snapshot", serde_json::json!({\n'
                '        "graph": &serialized_egraph,\n'
                '        "proposals": node_ids.iter().map(|n| n.to_string()).collect::<Vec<_>>() }));',
            ),
            (
                '        log::info!(\n            "Calling Lakeroad with spec:',
                '        reproduction_capture("selection", serde_json::json!({\n'
                '            "snapshot": "mapping", "kind": "spec", "input": sketch_template_node_id.to_string(),\n'
                '            "root": spec_node_id.to_string(),\n'
                '            "choices": spec_choices.iter().map(|(c,n)|\n'
                "                (c.to_string(), n.to_string())).collect::<Vec<_>>() }));\n"
                '        log::info!(\n            "Calling Lakeroad with spec:',
            ),
            (
                "    let verilog = to_verilog_egraph_serialize(",
                '    reproduction_capture("final-selection", serde_json::json!({\n'
                '        "graph": &serialized,\n'
                '        "choices": choices.iter().map(|(c,n)| (c.to_string(), n.to_string())).collect::<Vec<_>>(),\n'
                '        "roots": outputs.iter().cloned().map(|(value,name)| {\n'
                "            let class = egraph.value_to_class_id(&egraph.find(value));\n"
                '            serde_json::json!({"name": name, "class": class.to_string(),\n'
                '                "node": choices[&class].to_string()})\n'
                "        }).collect::<Vec<_>>() }));\n"
                "    let verilog = to_verilog_egraph_serialize(",
            ),
            (
                "    // STEP 7: Simulate.",
                '    reproduction_capture("parent-complete", serde_json::json!({"verilog": &verilog}));\n'
                "    // STEP 7: Simulate.",
            ),
        ],
        "src/lib.rs": [
            ("pub mod global_greedy_dag;", "pub mod global_greedy_dag;\n" + RUST_CAPTURE + CHURCHROAD_RUN),
            ("        .arg(spec_filepath)", "        .arg(&spec_filepath)"),
            (
                "    let output = command.output().unwrap();",
                '    reproduction_capture("synthesis-input", serde_json::json!({\n'
                '        "spec": std::fs::read_to_string(spec_filepath).unwrap(),\n'
                '        "command": format!("{:?}", &command), "architecture": architecture}));\n'
                "    let output = command.output().unwrap();\n"
                '    reproduction_capture("synthesis-output", serde_json::json!({\n'
                '        "success": output.status.success(), "code": output.status.code(),\n'
                '        "stdout": String::from_utf8_lossy(&output.stdout),\n'
                '        "stderr": String::from_utf8_lossy(&output.stderr)}));',
            ),
            (
                "    let choices = AnythingExtractor.extract(serialized_egraph, &[]);",
                "    let choices = AnythingExtractor.extract(serialized_egraph, &[]);\n"
                "    for root in serialized_egraph[sketch_template_node_id].children.iter()\n"
                "        .chain(std::iter::once(sketch_template_node_id)) {\n"
                '        reproduction_capture("selection", serde_json::json!({\n'
                '            "snapshot": "mapping", "kind": "port-binding",\n'
                '            "input": root.to_string(), "root": root.to_string(),\n'
                '            "choices": choices.iter().map(|(c,n)|\n'
                "                (c.to_string(), n.to_string())).collect::<Vec<_>>() }));\n"
                "    }",
            ),
            (
                '    let command_output = Command::new("yosys")',
                '    let mut reproduction_yosys = Command::new("yosys");\n    let command_output = reproduction_yosys',
            ),
            (
                "    if !command_output.status.success() {",
                '    reproduction_capture("yosys-output", serde_json::json!({\n'
                '        "command": format!("{:?}", &reproduction_yosys),\n'
                '        "source": std::fs::read_to_string(verilog_filepath).unwrap(),\n'
                '        "success": command_output.status.success(),\n'
                '        "stdout": String::from_utf8_lossy(&command_output.stdout),\n'
                '        "stderr": String::from_utf8_lossy(&command_output.stderr)}));\n'
                "    if !command_output.status.success() {",
            ),
        ],
    }
    patched = {}
    for relative, replacements in edits.items():
        source = (checkout / relative).read_text()
        # Only the original native callsites are rewritten, never our delegate.
        source = re.sub(r"\.parse_and_run_program\(\s*None,", ".reproduction_run_program(None,", source)
        for before, after in replacements:
            if source.count(before) != 1:
                raise CaptureError(f"Churchroad instrumentation boundary changed in {relative}: {before[:90]!r}")
            source = source.replace(before, after, 1)
        patched[relative] = source
    manifest = (checkout / "Cargo.toml").read_text()
    if "serde_json" not in manifest:
        manifest = manifest.replace("[dependencies]\n", '[dependencies]\nserde_json = "1.0"\n', 1)
    # This crate is built independently from the repository's workspace.
    if "[workspace]" not in manifest:
        manifest += "\n[workspace]\n"
    patched["Cargo.toml"] = manifest
    return patched


def write_native_patch(checkout: Path, patched: dict[str, str], destination: Path) -> None:
    """Retain a reproducible patch, with paths relative to the native checkout."""
    patch = "".join(
        "".join(
            difflib.unified_diff(
                (checkout / relative).read_text().splitlines(True),
                source.splitlines(True),
                fromfile=f"a/{relative}",
                tofile=f"b/{relative}",
            )
        )
        for relative, source in patched.items()
    )
    destination.write_text(patch)


def read_events(
    directory: Path, *, max_bytes: int = 128 * 1024**2, require_parent_complete: bool = True
) -> list[dict[str, Any]]:
    """Reject gaps, incomplete writes and unknown versions; require the selected boundary."""
    paths = sorted(directory.glob("event-*.json"))
    total_bytes = sum(path.stat().st_size for path in paths)
    if max_bytes <= 0 or total_bytes > max_bytes:
        raise CaptureResourceError(
            f"native evidence is {total_bytes} bytes; materialization budget is {max_bytes}; "
            "retain the capture and use a reviewed larger budget or streaming materialization"
        )
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
    if not events or (require_parent_complete and events[-1]["kind"] != "parent-complete"):
        raise CaptureError("native optimization did not retain a parent-complete event")
    return events


def tiger_selections(program: str) -> list[list[tuple[str, list[int]]]]:
    """Read Tiger's observed original-node choices, including shared children."""
    groups: list[list[tuple[str, list[int]]]] = []
    current: list[tuple[str, list[int]]] | None = None
    for line in program.splitlines():
        if line == "; reproduction-selection-begin":
            if current is not None:
                raise CaptureError("nested Tiger selection records")
            current = []
        elif line == "; reproduction-selection-end":
            if not current:
                raise CaptureError("empty or unmatched Tiger selection record")
            groups.append(current)
            current = None
        elif line.startswith("; reproduction-node "):
            if current is None:
                raise CaptureError("Tiger node outside a selection record")
            fields = line.removeprefix("; reproduction-node ").split()
            try:
                node = bytes.fromhex(fields[0]).decode()
                children = [int(child) for child in fields[1:]]
            except (ValueError, UnicodeError, IndexError) as error:
                raise CaptureError("invalid Tiger selection node encoding") from error
            if any(child < 0 or child >= len(current) for child in children):
                raise CaptureError("Tiger selection children must refer to earlier selected nodes")
            current.append((node, children))
    if current is not None or not groups:
        raise CaptureError("Tiger did not retain complete original-node selection provenance")
    return groups


class WitnessQuery:
    """A finite, query-only encoding of observed nodes and equality anchors.

    Node variables preserve sharing and can express cycles without constructing
    terms. Opaque primitive representations fail closed rather than being quoted
    or coerced into a different value. This is membership, not a cost/legality proof.
    """

    def __init__(self, graph: dict[str, Any], prefix: str) -> None:
        self.nodes = graph["nodes"]
        self.prefix = prefix
        self.facts: list[str] = []
        self.originals: dict[str, str] = {}

    def expression(self, node_id: str, children: list[str]) -> str:
        node = self.nodes[node_id]
        op = node["op"]
        literal = re.fullmatch(r'"(?:[^"\\]|\\.)*"|true|false|[+-]?(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][+-]?\d+)?', op)
        if literal and not children:
            return str(op)
        if node_id.startswith("primitive"):
            raise CaptureError(f"unrepresentable primitive at {node_id}: {op!r}")
        if not re.fullmatch(r"[^\s();\"]+", op) or op in {"DumT", "DumC"}:
            raise CaptureError(f"unrepresentable original operator at {node_id}: {op!r}")
        return f"({op}{(' ' + ' '.join(children)) if children else ''})"

    def original(self, node_id: str) -> str:
        """Constrain a raw original node closure iteratively, including cycles."""
        if node_id in self.originals:
            return self.originals[node_id]
        pending = [node_id]
        self.originals[node_id] = f"{self.prefix}o{len(self.originals)}"
        while pending:
            current = pending.pop()
            try:
                node = self.nodes[current]
            except KeyError as error:
                raise CaptureError(f"missing original graph node {current}") from error
            for child in node["children"]:
                if child not in self.originals:
                    self.originals[child] = f"{self.prefix}o{len(self.originals)}"
                    pending.append(child)
            expression = self.expression(current, [self.originals[child] for child in node["children"]])
            self.facts.append(f"(= {self.originals[current]} {expression})")
        return self.originals[node_id]

    def finish(self) -> str:
        return "(check\n  " + "\n  ".join(self.facts) + "\n)\n"


def eggcc_seed_query(program: str, prefix: str) -> tuple[list[str], dict[str, str]]:
    """Turn native shared initialization/output lets into relational query facts.

    This only accepts the printer's let bindings, with earlier bindings or literal
    operands. No source action is executed when the witness is checked.
    """
    tokens = re.findall(r';[^\n]*|"(?:[^"\\]|\\.)*"|[()]|[^\s();]+', program)
    stack: list[list[Any]] = [[]]
    for token in tokens:
        if token.startswith(";"):
            continue
        if token == "(":
            stack.append([])
        elif token == ")":
            if len(stack) < 2:
                raise CaptureError("unbalanced native seed expressions")
            value = stack.pop()
            stack[-1].append(value)
        else:
            stack[-1].append(token)
    if len(stack) != 1:
        raise CaptureError("incomplete native seed expressions")
    bindings: dict[str, str] = {}
    roots: dict[str, str] = {}
    facts = []

    def render(expression: Any, *, operator: bool = False) -> str:
        if isinstance(expression, list):
            if not expression:
                raise CaptureError("empty native seed expression")
            return (
                "("
                + render(expression[0], operator=True)
                + (" " + " ".join(render(arg) for arg in expression[1:]) if len(expression) > 1 else "")
                + ")"
            )
        if not isinstance(expression, str):
            raise CaptureError("invalid native seed atom")
        if operator:
            return expression
        if expression in bindings:
            return bindings[expression]
        if re.fullmatch(r'"(?:[^"\\]|\\.)*"|true|false|[+-]?(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][+-]?\d+)?', expression):
            return expression
        raise CaptureError(f"unbound or opaque native seed value: {expression!r}")

    for form in stack[0]:
        if not isinstance(form, list) or not form:
            raise CaptureError("invalid native seed form")
        if form[0] == "FunctionHasType":
            continue
        if len(form) != 3 or form[0] != "let" or not isinstance(form[1], str):
            raise CaptureError(f"unsupported action in native seed binding: {form[0]!r}")
        name = form[1]
        if name in bindings:
            raise CaptureError(f"duplicate native seed binding {name!r}")
        expression = render(form[2])
        variable = f"{prefix}seed{len(bindings)}"
        bindings[name] = variable
        facts.append(f"(= {variable} {expression})")
        if isinstance(form[2], list) and form[2][0] == "Function":
            function_name = json.loads(form[2][1])
            if function_name in roots:
                raise CaptureError(f"duplicate native seed Function {function_name!r}")
            roots[function_name] = variable
    return facts, roots


def _eggcc_tree(tokens: list[str]) -> list[Any]:
    """Parse one balanced tokenized form without interpreting atoms or literals."""
    stack: list[list[Any]] = [[]]
    for token in tokens:
        if token == "(":
            stack.append([])
        elif token == ")":
            value = stack.pop()
            stack[-1].append(value)
        else:
            stack[-1].append(token)
    return list(stack[0][0])


def _eggcc_text(tree: Any) -> str:
    """Render only the validated observation syntax, preserving literal tokens."""
    return tree if isinstance(tree, str) else "(" + " ".join(_eggcc_text(value) for value in tree) + ")"


def eggcc_source_anchors(graph: dict[str, Any], selection_program: str, source: str) -> tuple[str, dict[str, Any]]:
    """Observe uniquely grounded initializer values without adding target terms.

    Only constructor applications can ground an identity: a mutable custom-table
    lookup in the final graph need not equal its value during initialization.
    Unsupported source expressions retain the structural query path.
    """
    forms = egglog_forms(source)
    trees = [_eggcc_tree(tokens) for _, _, tokens in forms]
    plan: dict[str, Any] = {
        "status": "structural-fallback",
        "reason": None,
        "classes": {},
        "root_classes": {},
        "unresolved_source_bindings": {},
        "observation_tables": [],
        "f64_literal_matches": [],
        "derived_observations": [],
        "unresolved_erased_fields": {},
        "original_program_sha256": hashlib.sha256(source.encode()).hexdigest(),
        "replay_program_sha256": hashlib.sha256(source.encode()).hexdigest(),
        "native_graph_sha256": hashlib.sha256(json.dumps(graph, sort_keys=True).encode()).hexdigest(),
    }
    pending_forms = list(trees)
    while pending_forms:
        form = pending_forms.pop()
        if form and isinstance(form[0], str) and form[0] in {"push", "pop", "reset", "include", "fail", "keep-best"}:
            plan["reason"] = "source changes scope or reconstructs tables whose constructor lifetimes are not tracked"
            return source, plan
        pending_forms.extend(child for child in form if isinstance(child, list))
    initializers = [
        index
        for index, (start, end, _) in enumerate(forms)
        if "; Program nodes\n" in source[start:end] and "; Loop context unions\n" in source[start:end]
    ]
    if len(initializers) != 1:
        plan["reason"] = "source markers do not identify one initializer command"
        return source, plan
    index = initializers[0]
    init = trees[index]
    if len(init) != 5 or init[:2] != ["rule", []] or init[3] != ":ruleset" or not isinstance(init[4], str):
        plan["reason"] = "initializer is not one empty-body rule with an explicit ruleset"
        return source, plan
    ruleset = init[4]
    uses = [i for i, (_, _, tokens) in enumerate(forms) if ruleset in tokens]
    if (
        index + 1 >= len(trees)
        or trees[index + 1] != ["run", ruleset, "1"]
        or len(uses) != 3
        or trees[uses[0]] != ["ruleset", ruleset]
        or uses[1:] != [index, index + 1]
    ):
        plan["reason"] = "initializer ruleset must be declared once and run exactly once immediately after its rule"
        return source, plan
    start, end, _ = forms[index]
    initializer = source[start:end]
    tail = re.search(r"\)\s*:ruleset\s+" + re.escape(ruleset) + r"\s*\)$", initializer)
    if tail is None:
        plan["reason"] = "initializer action boundary is not representable without reprinting source"
        return source, plan
    seed = initializer.split("; Program nodes\n", 1)[1].split("; Loop context unions\n", 1)[0]
    seed_names = [tokens[2] for _, _, tokens in egglog_forms(seed) if tokens[:2] == ["(", "let"]]
    seed_actions = [action for action in init[2] if action[0] == "let" and action[1] in seed_names]
    if [action[1] for action in seed_actions] != seed_names or len(set(seed_names)) != len(seed_names):
        raise CaptureError("initializer source bindings are duplicated or do not match its marked program nodes")
    local_counts = Counter(action[1] for action in init[2] if action[0] == "let")
    if any(local_counts[name] != 1 for name in seed_names):
        raise CaptureError("initializer reassigns a retained source local")

    signatures: dict[str, tuple[list[str], str]] = {}
    eq_sorts = set()
    for form in trees[:index]:
        if form[0] == "datatype":
            eq_sorts.add(form[1])
            for variant in form[2:]:
                arguments = variant[1:]
                stop = next((i for i, value in enumerate(arguments) if str(value).startswith(":")), len(arguments))
                signatures[variant[0]] = (arguments[:stop], form[1])
        elif form[0] == "constructor":
            signatures[form[1]] = (form[2], form[3])
        elif form[0] == "sort" and len(form) == 2:
            eq_sorts.add(form[1])
    declared_tables = set(signatures) | {form[1] for form in trees if form[0] in {"function", "relation"}}
    known_commands = {
        "sort",
        "datatype",
        "constructor",
        "function",
        "relation",
        "let",
        "set",
        "union",
        "delete",
        "subsume",
        "ruleset",
        "unstable-combined-ruleset",
        "rule",
        "rewrite",
        "birewrite",
        "run",
        "run-schedule",
        "check",
        "extract",
        "print-size",
        "print-function",
        "print-stats",
    }
    if any(form[0] not in known_commands | declared_tables for form in trees):
        plan["reason"] = "source has an unsupported top-level command or macro; retain structural identities"
        return source, plan
    declared_rulesets = {form[1] for form in trees if form[0] in {"ruleset", "unstable-combined-ruleset"}}
    scheduled_rulesets = {""}
    for (_, _, tokens), form in zip(forms, trees, strict=True):
        if form[0] in {"run", "run-schedule"}:
            scheduled_rulesets.update(declared_rulesets.intersection(tokens))
    combined = {form[1]: set(form[2:]) for form in trees if form[0] == "unstable-combined-ruleset"}
    while True:
        expanded = scheduled_rulesets | set().union(*(combined.get(name, set()) for name in scheduled_rulesets))
        if expanded == scheduled_rulesets:
            break
        scheduled_rulesets = expanded
    deleted_constructors = set()
    for form in trees:
        if form[0] in {"rule", "rewrite", "birewrite"}:
            rule_ruleset = form[form.index(":ruleset") + 1] if ":ruleset" in form else ""
            if rule_ruleset not in scheduled_rulesets:
                continue
        pending_actions = [form]
        while pending_actions:
            action = pending_actions.pop()
            if (
                action
                and action[0] == "delete"
                and len(action) == 2
                and isinstance(action[1], list)
                and action[1]
                and action[1][0] in signatures
            ):
                deleted_constructors.add(action[1][0])
            pending_actions.extend(child for child in action if isinstance(child, list))
    plan["constructor_lifetime"] = {
        "scheduled_rulesets": sorted(scheduled_rulesets),
        "deleted_constructor_heads": sorted(deleted_constructors),
        "subsumed_rows_retain_identity": True,
    }
    nodes = graph["nodes"]
    class_data = graph.get("class_data", {})
    rows: dict[tuple[str, tuple[str, ...]], set[str]] = defaultdict(set)
    for node in nodes.values():
        try:
            children = tuple(nodes[child]["eclass"] for child in node["children"])
        except KeyError as error:
            raise CaptureError(f"native graph has a missing constructor child: {error}") from error
        rows[(node["op"], children)].add(node["eclass"])
    values: dict[str, str] = {}
    candidates: dict[str, dict[str, str]] = {}
    # The graph serializer may print 0.00001 as 1e-5. Compare typed finite
    # binary64 identities, never decimal tolerances or untyped numeric values.
    finite_f64: dict[bytes, dict[str, set[str]]] = defaultdict(lambda: defaultdict(set))
    for node in nodes.values():
        if node["children"] or class_data.get(node["eclass"], {}).get("type") != "f64":
            continue
        try:
            value = float(node["op"])
        except ValueError:
            continue
        if math.isfinite(value):
            finite_f64[struct.pack(">d", value)][node["eclass"]].add(node["op"])

    def resolve(expression: Any, expected_sort: str | None = None) -> str:
        if isinstance(expression, str) and expression in values:
            result = values[expression]
        else:
            if isinstance(expression, list):
                if not expression or expression[0] not in signatures:
                    raise LookupError("source call is not a declared constructor")
                if expression[0] in deleted_constructors:
                    raise LookupError(f"constructor {expression[0]} can be deleted by a reached source action")
                inputs, output_sort = signatures[expression[0]]
                if len(inputs) != len(expression) - 1 or expected_sort not in {None, output_sort}:
                    raise CaptureError("native source constructor has inconsistent arity or sort")
                expected_sort = output_sort
                key = (
                    expression[0],
                    tuple(resolve(child, sort) for child, sort in zip(expression[1:], inputs, strict=True)),
                )
                choices = rows.get(key, set())
                if len(choices) > 1:
                    raise CaptureError(f"ambiguous native constructor identity for source call {expression[0]}")
            elif isinstance(expression, str) and expected_sort == "f64":
                try:
                    value = float(expression)
                except ValueError as error:
                    raise LookupError("source f64 literal is unsupported") from error
                if not math.isfinite(value):
                    raise LookupError("nonfinite source f64 literal retains structural matching")
                bits = struct.pack(">d", value)
                choices = set(finite_f64.get(bits, {}))
                if len(choices) != 1:
                    raise LookupError("source f64 bits have no unique retained native class")
                match = {
                    "source": expression,
                    "native": sorted(finite_f64[bits][next(iter(choices))]),
                    "bits": bits.hex(),
                    "sort": "f64",
                    "class": next(iter(choices)),
                }
                if match not in plan["f64_literal_matches"]:
                    plan["f64_literal_matches"].append(match)
            elif isinstance(expression, str) and re.fullmatch(
                r'"(?:[^"\\]|\\.)*"|true|false|[+-]?(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][+-]?\d+)?', expression
            ):
                choices = {
                    value
                    for value in rows.get((expression, ()), set())
                    if expected_sort is None or class_data.get(value, {}).get("type") == expected_sort
                }
            else:
                raise LookupError("source operand has no grounded earlier binding")
            if len(choices) != 1:
                raise LookupError("source value has no unique retained constructor row")
            result = next(iter(choices))
        actual_sort = class_data.get(result, {}).get("type")
        if actual_sort is None:
            raise LookupError("native graph omits the value's sort metadata")
        if expected_sort is not None and actual_sort != expected_sort:
            raise CaptureError("native constructor row has conflicting output sort metadata")
        return result

    for form in trees[:index]:
        if form[0] != "let" or len(form) != 3:
            continue
        try:
            class_id = resolve(form[2])
        except LookupError:
            continue
        values[form[1]] = class_id
        if class_data[class_id].get("let") == form[1] and class_data[class_id]["type"] in eq_sorts:
            candidates[class_id] = {
                "kind": "global",
                "binding": form[1],
                "sort": class_data[class_id]["type"],
                "lookup": form[1],
            }
    for ordinal, action in enumerate(seed_actions):
        name = action[1]
        try:
            class_id = resolve(action[2])
        except LookupError as error:
            values.pop(name, None)
            plan["unresolved_source_bindings"][name] = str(error)
            continue
        values[name] = class_id
        if isinstance(action[2], list) and action[2][0] == "Function":
            plan["root_classes"][json.loads(action[2][1])] = class_id
        sort = class_data[class_id]["type"]
        if sort in eq_sorts and class_id not in candidates:
            table = f"reproduction_anchor_{ordinal}"
            candidates[class_id] = {
                "kind": "initializer",
                "binding": name,
                "sort": sort,
                "table": table,
                "lookup": f"({table})",
            }
    needed = set()
    pending: list[str] = []
    for selection in tiger_selections(selection_program):
        root = nodes[selection[-1][0]]
        try:
            name = json.loads(nodes[root["children"][0]]["op"])
        except (KeyError, IndexError, ValueError) as error:
            raise CaptureError("native selection root has no identifiable Function name") from error
        if plan["root_classes"].get(name) == root["eclass"] and root["eclass"] in candidates:
            needed.add(root["eclass"])
        for node_id, _ in selection:
            node = nodes[node_id]
            kept = {"Arg": [], "Empty": [], "Const": [0]}.get(node["op"], list(range(len(node["children"]))))
            pending.extend(child for i, child in enumerate(node["children"]) if i not in kept)
    # Tiger can erase a Type value created by a native rule after initialization.
    # Only this one-level TupleT(TypeList) case is supported: its child must
    # already have a source handle, and the final native row must be unique.
    # The replay observes that row after the source schedule; it never builds it.
    for node_id in sorted(set(pending)):
        node = nodes[node_id]
        class_id = node["eclass"]
        if class_id in candidates or node["op"] != "TupleT":
            continue
        reason = None
        if signatures.get("TupleT") != (["TypeList"], "Type") or len(node["children"]) != 1:
            reason = "erased TupleT has an unsupported constructor signature"
        elif class_data.get(class_id, {}).get("type") != "Type":
            reason = "erased TupleT has inconsistent native sort"
        else:
            child_class = nodes[node["children"][0]]["eclass"]
            handle = candidates.get(child_class)
            if handle is None or handle["sort"] != "TypeList":
                reason = "erased TupleT child has no grounded TypeList source handle"
            elif rows.get(("TupleT", (child_class,))) != {class_id}:
                reason = "erased TupleT has ambiguous native constructor identity"
            else:
                table = f"reproduction_derived_type_{len(plan['derived_observations'])}"
                derived = {
                    "kind": "existing-row",
                    "node": node_id,
                    "native_class": class_id,
                    "sort": "Type",
                    "table": table,
                    "lookup": f"({table})",
                    "child_class": child_class,
                    "child_lookup": handle["lookup"],
                }
                candidates[class_id] = derived
                needed.add(child_class)
                plan["derived_observations"].append(derived)
        if reason is not None:
            plan["unresolved_erased_fields"][node_id] = reason
    visited = set()
    while pending:
        node_id = pending.pop()
        if node_id in visited:
            continue
        visited.add(node_id)
        node = nodes[node_id]
        if node["eclass"] in candidates:
            needed.add(node["eclass"])
        else:
            pending.extend(node["children"])
    plan["classes"] = {class_id: entry for class_id, entry in candidates.items() if class_id in needed}
    plan["observation_tables"] = [entry for entry in plan["classes"].values() if entry["kind"] == "initializer"]
    all_tokens = {token for _, _, tokens in forms for token in tokens}
    if any(entry["table"] in all_tokens for entry in plan["observation_tables"]):
        raise CaptureError("source collides with a reproduction source-anchor table")
    declarations = "".join(
        f"(function {entry['table']} () {entry['sort']} :merge old)\n" for entry in plan["observation_tables"]
    )
    assignments = "".join(f"(set ({entry['table']}) {entry['binding']})\n" for entry in plan["observation_tables"])
    replay = source[:start] + declarations + initializer[: tail.start()] + assignments + source[start + tail.start() :]
    if not needed:
        plan["reason"] = "no required identity has a grounded source handle; all constraints remain structural"
    else:
        plan["status"] = "source-anchored"
    plan["replay_program_sha256"] = hashlib.sha256(replay.encode()).hexdigest()
    return replay, plan


def eggcc_output_checks(
    graph: dict[str, Any],
    program: str,
    batch: list[str],
    seed_program: str,
    *,
    source_anchors: dict[str, Any] | None = None,
) -> tuple[str, list[dict[str, Any]]]:
    """Bind every native selection to its unambiguous named application root.

    Tiger erases Arg/Empty type and context and Const's type/context. Recover only
    those fields from the selected original node. Every retained child must match
    the corresponding original eclass. A new erasure/transformation is a blocker.
    """
    nodes = graph["nodes"]
    queries = []
    roots = []
    seen = set()
    # Tiger's find_function_roots emits one request per Function enode, even
    # when multiple enodes belong to the same eclass. Keep every actual choice
    # and query; equal application names do not imply duplicate requests.
    requested_classes = Counter(node["eclass"] for node in nodes.values() if node["op"] == "Function")
    selected_classes: Counter[str] = Counter()
    for group_index, selection in enumerate(tiger_selections(program)):
        prefix = f"reproduction_{group_index}_"
        query = WitnessQuery(graph, prefix)
        seed_facts, seed_roots = eggcc_seed_query(seed_program, prefix)
        if set(seed_roots) != set(batch):
            raise CaptureError("native initialization does not name exactly the selected Function batch")
        query.facts.extend(seed_facts)
        original_requests: set[str] = set()
        selected_facts = []
        for index, (node_id, child_indices) in enumerate(selection):
            if node_id not in nodes:
                raise CaptureError(f"Tiger selected node absent from its input graph: {node_id}")
            node = nodes[node_id]
            original_children = node["children"]
            op = node["op"]
            kept = {"Arg": [], "Empty": [], "Const": [0]}.get(op, list(range(len(original_children))))
            expected_arity = {"Arg": 2, "Empty": 2, "Const": 3}.get(op, len(original_children))
            if len(original_children) != expected_arity or len(kept) != len(child_indices):
                raise CaptureError(f"unsupported Tiger child projection for {op} at {node_id}")
            substitutions = {}
            for position, child_index in zip(kept, child_indices, strict=True):
                selected_child = selection[child_index][0]
                if nodes[selected_child]["eclass"] != nodes[original_children[position]]["eclass"]:
                    raise CaptureError(f"Tiger child provenance disagrees with original eclass at {node_id}")
                substitutions[position] = f"{prefix}s{child_index}"
            original_requests.update(
                child for position, child in enumerate(original_children) if position not in substitutions
            )
            children = [
                substitutions[position] if position in substitutions else query.original(child)
                for position, child in enumerate(original_children)
            ]
            fact = f"(= {prefix}s{index} {query.expression(node_id, children)})"
            query.facts.append(fact)
            selected_facts.append(fact)
        root_id = selection[-1][0]
        root = nodes[root_id]
        if root["op"] != "Function" or len(root["children"]) != 4:
            raise CaptureError("Tiger selection does not end at a Function application root")
        try:
            name = json.loads(nodes[root["children"][0]]["op"])
        except (ValueError, KeyError) as error:
            raise CaptureError("Function root lacks its original string name") from error
        if not isinstance(name, str) or name not in batch:
            raise CaptureError(f"unexpected native Function root: {name!r}")
        # A Function name is the native application's lookup key. Ambiguous names
        # cannot silently anchor a different root that happens to pass this query.
        classes = {
            value["eclass"]
            for value in nodes.values()
            if value["op"] == "Function"
            and value["children"]
            and nodes[value["children"][0]]["op"] == json.dumps(name, ensure_ascii=False)
        }
        if classes != {root["eclass"]}:
            raise CaptureError(f"ambiguous original Function identity for {name!r}")
        witness = None
        if source_anchors is not None:
            handles = source_anchors["classes"]
            input_handle = (
                handles.get(root["eclass"]) if source_anchors["root_classes"].get(name) == root["eclass"] else None
            )
            if input_handle is not None:
                query.facts[: len(seed_facts)] = [f"(= {seed_roots[name]} {input_handle['lookup']})"]
            reachable = set()
            pending = list(original_requests)
            while pending:
                node_id = pending.pop()
                if node_id in reachable:
                    continue
                reachable.add(node_id)
                if nodes[node_id]["eclass"] not in handles:
                    pending.extend(nodes[node_id]["children"])
            # Preserve the original variable allocation and every selected fact.
            # Only the auxiliary original-node closure is replaced/pruned.
            original_facts = {
                (
                    f"(= {variable} "
                    f"{query.expression(node_id, [query.originals[c] for c in nodes[node_id]['children']])})"
                ): node_id
                for node_id, variable in query.originals.items()
            }
            replaced = []
            for fact in query.facts:
                original_node = original_facts.get(fact)
                if original_node is None:
                    replaced.append(fact)
                elif original_node in reachable:
                    handle = handles.get(nodes[original_node]["eclass"])
                    replaced.append(f"(= {query.originals[original_node]} {handle['lookup']})" if handle else fact)
            query.facts = replaced
            witness = {
                "input": {
                    "mode": "source-handle" if input_handle else "structural",
                    "native_class": root["eclass"],
                    "handle": input_handle,
                    "fallback_reason": None
                    if input_handle
                    else "named source root has no grounded handle in this native class",
                },
                "erased_fields": [
                    {
                        "node": node_id,
                        "native_class": nodes[node_id]["eclass"],
                        "handle": handles.get(nodes[node_id]["eclass"]),
                        "fallback_reason": None
                        if nodes[node_id]["eclass"] in handles
                        else "no grounded source handle; retain structural closure",
                    }
                    for node_id in sorted(original_requests)
                ],
                "original_closure_nodes": len(query.originals),
                "retained_original_nodes": len(reachable),
                "selected_facts_sha256": hashlib.sha256("\n".join(selected_facts).encode()).hexdigest(),
            }
        query.facts.append(f"(= {seed_roots[name]} {prefix}s{len(selection) - 1})")
        queries.append(query.finish())
        roots.append(
            {
                "selection": group_index,
                "name": name,
                "node": root_id,
                "eclass": root["eclass"],
                "selected_nodes": len(selection),
            }
        )
        if witness is not None:
            roots[-1]["witness"] = witness | {"query_fact_count": len(query.facts)}
        selected_classes[root["eclass"]] += 1
        seen.add(name)
    if seen != set(batch) or len(batch) != len(set(batch)):
        raise CaptureError(f"native Function roots do not cover the whole batch: {batch!r} vs {sorted(seen)!r}")
    if selected_classes != requested_classes:
        raise CaptureError(
            "native Function selections do not preserve Tiger's input root request multiplicity: "
            f"{dict(requested_classes)!r} vs {dict(selected_classes)!r}"
        )
    return "\n".join(queries), roots


def _eggcc_constructor_signatures(source: str) -> dict[str, tuple[list[str], str]]:
    """Read declared constructor arities and sorts without evaluating source."""
    signatures: dict[str, tuple[list[str], str]] = {}
    for _, _, tokens in egglog_forms(source):
        tree = _eggcc_tree(tokens)
        constructor_declarations = []
        if tree[0] == "datatype":
            for variant in tree[2:]:
                stop = next((i for i, value in enumerate(variant[1:]) if str(value).startswith(":")), len(variant) - 1)
                constructor_declarations.append((variant[0], variant[1 : stop + 1], tree[1]))
        elif tree[0] == "constructor":
            constructor_declarations.append((tree[1], tree[2], tree[3]))
        for name, arguments, sort in constructor_declarations:
            if name in signatures or not all(isinstance(value, str) for value in [*arguments, sort]):
                raise CaptureError("duplicate or opaque constructor signature in lookup source")
            signatures[name] = (arguments, sort)
    return signatures


def _eggcc_dag_observers(
    requests: list[dict[str, Any]], prefix: str
) -> tuple[str, dict[str, str], dict[str, int], list[str]]:
    """Read one grounded constructor/alias per rule into observation tables.

    The callers validate typing, topology, and complete root closure. Source
    expressions occur only in rule bodies; heads write already-bound values.
    Every key observes one grounded constructor or alias, so its value is unique
    modulo equality. Merge-old retains that value without requiring the
    proof-unsupported eq-sort no-merge conflict check.
    """
    sorts = {entry["sort"] for request in requests for entry in request["entries"] if not entry["literal"]}
    tables = {sort: prefix + f"value_{i}" for i, sort in enumerate(sorted(sorts))}
    counts: Counter[str] = Counter()
    depths = set()
    request_programs = []
    for request, data in enumerate(requests):
        entries, bindings = data["entries"], data["bindings"]
        variables = {entry["fact"][1]: index for index, entry in enumerate(entries)}
        rules = []
        for index, entry in enumerate(entries):
            if entry["literal"]:
                continue
            fact = entry["fact"]
            arguments = fact[2][1:] if isinstance(fact[2], list) else [fact[2]]
            body = []
            for variable in dict.fromkeys(arguments):
                if variable in bindings:
                    body.append(bindings[variable])
                elif variable in variables:
                    child_index = variables[variable]
                    child = entries[child_index]
                    body.append(
                        child["fact"]
                        if child["literal"]
                        else ["=", variable, [tables[child["sort"]], str(request), str(child_index)]]
                    )
            body.append(fact)
            rule = [
                "rule",
                body,
                [["set", [tables[entry["sort"]], str(request), str(index)], fact[1]]],
                ":ruleset",
                prefix + f"depth_{entry['depth']}",
            ]
            rule.append(":internal-include-subsumed")
            rule.extend([":name", json.dumps(prefix + f"rule_{request}_{index}")])
            rules.append(_eggcc_text(rule))
            counts[tables[entry["sort"]]] += 1
            depths.add(entry["depth"])
        request_programs.append("\n".join(rules))
    declarations = [f"(function {name} (i64 i64) {sort} :merge old)" for sort, name in tables.items()]
    declarations.extend(f"(ruleset {prefix}depth_{depth})" for depth in sorted(depths))
    runs = [f"(run {prefix}depth_{depth} 1)" for depth in sorted(depths)]
    return "\n" + "\n".join(declarations + request_programs + runs) + "\n", tables, dict(counts), request_programs


def _eggcc_literal_sort(token: str) -> str | None:
    """Classify a preserved native literal token, without changing its spelling."""
    if re.fullmatch(r'"(?:[^"\\]|\\.)*"', token):
        try:
            json.loads(token)
        except ValueError as error:
            raise CaptureError("reconstruction has an invalid quoted literal") from error
        return "String"
    if token in {"true", "false"}:
        return "bool"
    if re.fullmatch(r"[+-]?\d+", token):
        return "i64"
    if re.fullmatch(r"[+-]?(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][+-]?\d+)?", token):
        return "f64"
    return None


def eggcc_reconstruction_lookups(
    source: str, checks: str, roots: list[dict[str, Any]]
) -> tuple[str, str, dict[str, Any]]:
    """Decompose complete, grounded native reconstruction checks without inserting terms.

    Unlike Tiger selections these outputs already retain every constructor
    field. Only their exact topological let-derived equalities are accepted.
    Missing rows cannot create observations; no unsupported query is weakened.
    """
    prefix = "reconstruction_lookup_"
    forms = egglog_forms(source)
    if any(token.startswith((prefix, "reconstruction_seed")) for _, _, tokens in forms for token in tokens):
        raise CaptureError("source collides with a reconstruction observer or query variable")
    signatures = _eggcc_constructor_signatures(source)
    eq_sorts = {
        tree[1]
        for _, _, tokens in forms
        if (tree := _eggcc_tree(tokens))[0] == "datatype" or tree[0] == "sort" and len(tree) == 2
    }
    if not signatures or any(sort not in eq_sorts for _, sort in signatures.values()):
        raise CaptureError("reconstruction requires declared equality-sort constructors")
    queries = egglog_forms(checks)
    if not queries or len(queries) != len(roots):
        raise CaptureError("reconstruction lookup must retain every native output check")
    requests: list[dict[str, Any]] = []
    metadata: list[dict[str, Any]] = []
    for request, ((start, end, tokens), root) in enumerate(zip(queries, roots, strict=True)):
        query = _eggcc_tree(tokens)
        if query[0] != "check" or len(query) < 2 or root.get("output", request) != request:
            raise CaptureError("reconstruction query or native output ordering changed")
        entries: list[dict[str, Any]] = []
        variables: dict[str, int] = {}
        function_entries = []
        for index, fact in enumerate(query[1:]):
            if (
                not isinstance(fact, list)
                or len(fact) != 3
                or fact[0] != "="
                or fact[1] != f"reconstruction_seed{index}"
            ):
                raise CaptureError("reconstruction requires exact ordered native binding equalities")
            rhs = fact[2]
            dependencies = []
            literal = False
            if isinstance(rhs, str):
                if rhs in variables:
                    dependencies.append(variables[rhs])
                    sort = entries[variables[rhs]]["sort"]
                elif (sort := _eggcc_literal_sort(rhs)) is not None:
                    literal = True
                else:
                    raise CaptureError("reconstruction alias is not an earlier native binding")
            elif isinstance(rhs, list) and rhs and isinstance(rhs[0], str) and rhs[0] in signatures:
                arguments, sort = signatures[rhs[0]]
                if len(arguments) != len(rhs) - 1:
                    raise CaptureError("reconstruction constructor arity differs from source")
                for argument, expected in zip(rhs[1:], arguments, strict=True):
                    if not isinstance(argument, str):
                        raise CaptureError("reconstruction constructors must retain flat native bindings")
                    if argument in variables:
                        child = variables[argument]
                        actual = entries[child]["sort"]
                        dependencies.append(child)
                    else:
                        actual = _eggcc_literal_sort(argument)
                        if actual is None:
                            raise CaptureError("reconstruction has an opaque literal or ungrounded child")
                    if actual != expected:
                        raise CaptureError("reconstruction child sort differs from its declared constructor")
                if rhs[0] == "Function":
                    if len(rhs) != 5 or _eggcc_literal_sort(rhs[1]) != "String" or json.loads(rhs[1]) != root["name"]:
                        raise CaptureError("reconstruction Function differs from its named native output")
                    function_entries.append(index)
            else:
                raise CaptureError("reconstruction contains an unknown constructor or expression")
            entries.append(
                {
                    "fact": fact,
                    "sort": sort,
                    "dependencies": dependencies,
                    "literal": literal,
                    "depth": -1
                    if literal
                    else 1 + max((entries[child]["depth"] for child in dependencies), default=-1),
                }
            )
            variables[fact[1]] = index
        if len(function_entries) != 1:
            raise CaptureError("reconstruction must constrain exactly one named Function per output")
        root_index = len(entries) - 1
        function_index = root_index
        while isinstance(entries[function_index]["fact"][2], str) and not entries[function_index]["literal"]:
            function_index = entries[function_index]["dependencies"][0]
        if function_index != function_entries[0]:
            raise CaptureError("reconstruction terminal binding does not name its Function")
        reachable = set()
        pending = [root_index]
        while pending:
            index = pending.pop()
            if index not in reachable:
                reachable.add(index)
                pending.extend(entries[index]["dependencies"])
        if reachable != set(range(len(entries))):
            raise CaptureError("reconstruction lookup cannot discard disconnected native facts")
        requests.append({"entries": entries, "bindings": {}})
        metadata.append(
            {
                "request": request,
                "name": root["name"],
                "query_fact_count": len(entries),
                "constructor_facts": sum(isinstance(entry["fact"][2], list) for entry in entries),
                "max_depth": entries[root_index]["depth"],
                "original_query_sha256": hashlib.sha256(checks[start:end].encode()).hexdigest(),
            }
        )
    # check_facts includes subsumed rows; keep the same snapshot visibility.
    suffix, tables, counts, programs = _eggcc_dag_observers(requests, prefix)
    terminal = []
    for request, (data, item, program) in enumerate(zip(requests, metadata, programs, strict=True)):
        index = len(data["entries"]) - 1
        last = data["entries"][index]
        observer = [tables[last["sort"]], str(request), str(index)]
        check = _eggcc_text(["check", ["=", last["fact"][1], observer]])
        terminal.append(check)
        item.update(
            root_observer={"table": observer[0], "key": [request, index], "sort": last["sort"]},
            root_check_sha256=hashlib.sha256(check.encode()).hexdigest(),
            lookup_rules_sha256=hashlib.sha256(program.encode()).hexdigest(),
        )
    translated = "\n".join(terminal) + "\n"
    return (
        suffix,
        translated,
        {
            "status": "existing-row-dag",
            "source_prefix_sha256": hashlib.sha256(source.encode()).hexdigest(),
            "original_checks_sha256": hashlib.sha256(checks.encode()).hexdigest(),
            "lookup_program_sha256": hashlib.sha256(suffix.encode()).hexdigest(),
            "root_checks_sha256": hashlib.sha256(translated.encode()).hexdigest(),
            "tables": tables,
            "expected_rows": counts,
            "requests": metadata,
            "proof_compatibility": {
                "status": "unvalidated",
                "ordinary_only": False,
                "reason": "grounded constructor observers use merge-old; strict proof validation remains required",
            },
        },
    )


def eggcc_dag_lookups(
    source: str,
    graph: dict[str, Any],
    selection_program: str,
    checks: str,
    roots: list[dict[str, Any]],
    anchors: dict[str, Any],
) -> tuple[str, str, dict[str, Any]]:
    """Decompose exact selected DAG queries into existing-constructor lookups.

    Constructor functional dependencies and grounded source handles make each
    observed value unique modulo equality, permitting merge-old observers.
    Each depth runs once after its dependencies; every selected entry must reach
    its root. Missing grounding keeps the entire original query, never a subset.
    Proof compatibility does not establish strict proof validity for a replay.
    """
    prefix = "reproduction_lookup_"
    plan: dict[str, Any] = {
        "status": "structural-fallback",
        "reason": None,
        "source_prefix_sha256": hashlib.sha256(source.encode()).hexdigest(),
        "original_checks_sha256": hashlib.sha256(checks.encode()).hexdigest(),
        "proof_compatibility": {
            "status": "unvalidated",
            "ordinary_only": False,
            "reason": "grounded constructor observers use merge-old; strict proof validation remains required",
        },
        "requests": [],
    }
    forms = egglog_forms(source)
    if any(token.startswith(prefix) for _, _, tokens in forms for token in tokens):
        raise CaptureError("source collides with a reproduction lookup name")
    derived = anchors.get("derived_observations", [])
    derived_commands = []
    if derived:
        ruleset = "reproduction_derived_types"
        child_variable, value_variable = "reproduction_derived_child", "reproduction_derived_value"
        all_tokens = {token for _, _, tokens in forms for token in tokens}
        reserved = {ruleset, child_variable, value_variable, *(entry["table"] for entry in derived)}
        if reserved & all_tokens:
            raise CaptureError("source collides with a derived source-anchor observer")
        derived_commands.append(f"(ruleset {ruleset})")
        for entry in derived:
            node = graph["nodes"][entry["node"]]
            children = node["children"]
            handles = anchors["classes"]
            if (
                node["op"] != "TupleT"
                or len(children) != 1
                or node["eclass"] != entry["native_class"]
                or graph["nodes"][children[0]]["eclass"] != entry["child_class"]
                or handles[entry["child_class"]]["lookup"] != entry["child_lookup"]
                or handles[entry["child_class"]]["sort"] != "TypeList"
                or handles[entry["native_class"]] != entry
            ):
                raise CaptureError("derived TupleT observation differs from its grounded native identity")
            derived_commands.extend(
                [
                    f"(function {entry['table']} () Type :merge old)",
                    f"(rule ((= {child_variable} {entry['child_lookup']}) "
                    f"(= {value_variable} (TupleT {child_variable}))) "
                    f"((set ({entry['table']}) {value_variable})) :ruleset {ruleset} :internal-include-subsumed)",
                ]
            )
        derived_commands.append(f"(run {ruleset} 1)")
    derived_program = "\n".join(derived_commands) + "\n" if derived_commands else ""
    plan["derived_observations"] = derived
    plan["derived_expected_rows"] = {entry["table"]: 1 for entry in derived}
    plan["derived_program_sha256"] = hashlib.sha256(derived_program.encode()).hexdigest()
    selections = tiger_selections(selection_program)
    check_forms = egglog_forms(checks)
    if len(selections) != len(roots) or len(check_forms) != len(roots):
        raise CaptureError("lookup translation must retain every selected root request and check")
    for selection in selections:
        reachable = set()
        pending = [len(selection) - 1]
        while pending:
            index = pending.pop()
            if index not in reachable:
                reachable.add(index)
                pending.extend(selection[index][1])
        if reachable != set(range(len(selection))):
            raise CaptureError("disconnected selected entries cannot be discarded by lookup translation")
    classes = graph.get("class_data", {})
    if any("type" not in classes.get(node["eclass"], {}) for node in graph["nodes"].values()) or any(
        root.get("witness", {}).get("input", {}).get("mode") != "source-handle"
        or any(field["handle"] is None for field in root.get("witness", {}).get("erased_fields", []))
        for root in roots
    ):
        plan["reason"] = (
            "native sorts or source input/erased-field grounding is missing; retain every structural constraint"
        )
        return derived_program, checks, plan
    signatures = _eggcc_constructor_signatures(source)
    nodes = graph["nodes"]
    rows: dict[tuple[str, tuple[str, ...]], str] = {}
    for node in nodes.values():
        if node["op"] not in signatures:
            continue
        inputs, output = signatures[node["op"]]
        try:
            child_classes = tuple(nodes[child]["eclass"] for child in node["children"])
            sorts = [classes[class_id]["type"] for class_id in child_classes]
            output_sort = classes[node["eclass"]]["type"]
        except KeyError as error:
            raise CaptureError("lookup constructor row has missing typed graph metadata") from error
        if sorts != inputs or output_sort != output:
            raise CaptureError("lookup constructor row has inconsistent arity or sort")
        key = (node["op"], child_classes)
        if key in rows and rows[key] != node["eclass"]:
            raise CaptureError("ambiguous native constructor FD in lookup graph")
        rows[key] = node["eclass"]
    handles = {}
    for class_id, handle in anchors["classes"].items():
        if class_id not in classes or classes[class_id]["type"] != handle["sort"]:
            raise CaptureError("source handle has inconsistent native sort")
        lookup = handle["lookup"]
        if lookup in handles:
            raise CaptureError("source lookup aliases conflicting native identities")
        handles[lookup] = (class_id, handle["sort"])
    # Literal entries have no table and remain exact body equalities wherever
    # referenced. Constructor entries retain their request/index even if the
    # same native node or class occurs at another selected index.
    requests: list[dict[str, Any]] = []
    literal = re.compile(r'"(?:[^"\\]|\\.)*"|true|false|[+-]?(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][+-]?\d+)?')
    for request, ((start, end, tokens), selection, root) in enumerate(zip(check_forms, selections, roots, strict=True)):
        variable_prefix = f"reproduction_{request}_"
        query = _eggcc_tree(tokens)
        last_variable = f"{variable_prefix}s{len(selection) - 1}"
        final = query[-1]
        if (
            query[0] != "check"
            or not isinstance(final, list)
            or len(final) != 3
            or final[0] != "="
            or final[2] != last_variable
            or not isinstance(final[1], str)
            or not re.fullmatch(variable_prefix + r"seed\d+", final[1])
        ):
            raise CaptureError("lookup translation found an unknown root equality")
        selected = {}
        bindings = {}
        for fact in query[1:-1]:
            if not isinstance(fact, list) or len(fact) != 3 or fact[0] != "=" or not isinstance(fact[1], str):
                raise CaptureError("lookup translation found an unknown query constraint")
            if match := re.fullmatch(variable_prefix + r"s(\d+)", fact[1]):
                index = int(match[1])
                if fact[1] != f"{variable_prefix}s{index}":
                    raise CaptureError("lookup selected variable has a noncanonical index")
                if index in selected:
                    raise CaptureError("duplicate selected constraint in lookup query")
                selected[index] = fact
            else:
                if fact[1] in bindings or _eggcc_text(fact[2]) not in handles:
                    raise CaptureError("lookup query has an unknown or missing source anchor")
                bindings[fact[1]] = fact
        if set(selected) != set(range(len(selection))) or final[1] not in bindings:
            raise CaptureError("lookup query does not constrain every selected index and input")
        input_fact = bindings[final[1]]
        input_lookup = _eggcc_text(input_fact[2])
        if root["witness"]["input"]["handle"]["lookup"] != input_lookup or handles[input_lookup][0] != root["eclass"]:
            raise CaptureError("lookup query input differs from its original source identity")
        entries = []
        used_bindings = {final[1]}
        for index, (node_id, children) in enumerate(selection):
            if node_id not in nodes:
                raise CaptureError("lookup selection names a missing native graph node")
            node = nodes[node_id]
            sort = classes[node["eclass"]]["type"]
            fact = selected[index]
            if isinstance(fact[2], str):
                if node["children"] or children or not literal.fullmatch(node["op"]) or fact[2] != node["op"]:
                    raise CaptureError("lookup literal differs from the exact selected value")
                entries.append({"fact": fact, "sort": sort, "depth": -1, "literal": True})
                continue
            if not isinstance(fact[2], list) or not fact[2] or node["op"] not in signatures:
                raise CaptureError("lookup selected operator is not a declared constructor")
            inputs, output = signatures[node["op"]]
            expected_arity = {"Arg": 2, "Empty": 2, "Const": 3}.get(node["op"], len(inputs))
            if sort != output or fact[2][0] != node["op"] or len(fact[2]) != len(inputs) + 1:
                raise CaptureError("lookup selected constructor has inconsistent fields or sort")
            kept = {"Arg": [], "Empty": [], "Const": [0]}.get(node["op"], list(range(len(inputs))))
            if len(inputs) != expected_arity or len(kept) != len(children):
                raise CaptureError("lookup selected constructor has an unknown field projection")
            substitutions = dict(zip(kept, children, strict=True))
            dependencies = []
            for position, (argument, original_child, expected_sort) in enumerate(
                zip(fact[2][1:], node["children"], inputs, strict=True)
            ):
                if position in substitutions:
                    child = substitutions[position]
                    if (
                        argument != f"{variable_prefix}s{child}"
                        or entries[child]["sort"] != expected_sort
                        or nodes[selection[child][0]]["eclass"] != nodes[original_child]["eclass"]
                    ):
                        raise CaptureError("lookup selected edge differs from its typed native provenance")
                    dependencies.append(entries[child]["depth"])
                else:
                    if not isinstance(argument, str) or argument not in bindings:
                        raise CaptureError("lookup erased field has no grounded source anchor")
                    identity = handles[_eggcc_text(bindings[argument][2])]
                    if identity != (nodes[original_child]["eclass"], expected_sort):
                        raise CaptureError("lookup erased field differs from its typed source identity")
                    used_bindings.add(argument)
            entries.append({"fact": fact, "sort": sort, "depth": 1 + max(dependencies, default=-1), "literal": False})
        if used_bindings != set(bindings):
            raise CaptureError("lookup translation would discard an original-field constraint")
        if selection[-1][0] != root["node"] or entries[-1]["literal"]:
            raise CaptureError("lookup selected root differs from the native request")
        requests.append({"entries": entries, "bindings": bindings, "input": input_fact, "final": final})
        plan["requests"].append(
            {
                "request": request,
                "selected_nodes": len(selection),
                "selected_facts_sha256": hashlib.sha256(
                    "\n".join(_eggcc_text(selected[i]) for i in range(len(selection))).encode()
                ).hexdigest(),
                "original_query_sha256": hashlib.sha256(checks[start:end].encode()).hexdigest(),
            }
        )
    observer_program, tables, counts, request_programs = _eggcc_dag_observers(requests, prefix)
    root_checks = []
    for request, (data, request_program) in enumerate(zip(requests, request_programs, strict=True)):
        entries = data["entries"]
        last = entries[-1]
        root_check = _eggcc_text(
            [
                "check",
                data["input"],
                ["=", last["fact"][1], [tables[last["sort"]], str(request), str(len(entries) - 1)]],
                data["final"],
            ]
        )
        root_checks.append(root_check)
        plan["requests"][request].update(
            root_check_sha256=hashlib.sha256(root_check.encode()).hexdigest(),
            lookup_rules_sha256=hashlib.sha256(request_program.encode()).hexdigest(),
            root_observer={"table": tables[last["sort"]], "key": [request, len(entries) - 1], "sort": last["sort"]},
        )
    suffix = derived_program + observer_program
    translated = "\n".join(root_checks) + "\n"
    plan.update(
        status="existing-row-dag",
        tables=tables,
        expected_rows=dict(counts),
        lookup_program_sha256=hashlib.sha256(suffix.encode()).hexdigest(),
        root_checks_sha256=hashlib.sha256(translated.encode()).hexdigest(),
    )
    return suffix, translated, plan


def eggcc_sessions(events: list[dict[str, Any]]) -> list[dict[str, Any]]:
    """Pair completed native passes and their fresh reconstruction graphs.

    The full parent event is mandatory, even when an earlier pass succeeded.
    Unrecognized reached stages fail closed and remain available in raw evidence.
    """
    if not events or events[-1]["kind"] != "parent-complete":
        raise CaptureError("Eggcc parent optimization did not complete")
    if not events[-1]["payload"].get("outputs") or any(
        not output.get("result") for output in events[-1]["payload"]["outputs"]
    ):
        raise CaptureError("Eggcc did not retain its actual final optimized program output")
    sessions = []
    body = events[:-1]
    if not body or len(body) % 5:
        raise CaptureError("incomplete Eggcc optimization/reconstruction event sequence")
    for offset in range(0, len(body), 5):
        start, tiger, outputs, reconstructed, end = body[offset : offset + 5]
        if [event["kind"] for event in (start, tiger, outputs, reconstructed, end)] != [
            "optimization-start",
            "tiger-result",
            "reconstruction-outputs",
            "reconstruction-complete",
            "optimization-complete",
        ]:
            raise CaptureError("unexpected Eggcc native boundary or missing host-feedback completion")
        original = start["payload"]
        result = tiger["payload"]
        batch = original["batch"]
        if original.get("cutoff") != original.get("expected_passes"):
            raise CaptureError("Eggcc native run stopped before its complete optimization schedule")
        if any(event["payload"].get("batch") != batch for event in (tiger, outputs, reconstructed, end)):
            raise CaptureError("Eggcc function batch changed across one native pass")
        if original["pass"] != end["payload"].get("pass") or end["payload"].get("typechecked") is not True:
            raise CaptureError("Eggcc pass did not retain successful native typechecking")
        source = original["program"]
        if source.count("; Program nodes\n") != 1 or source.count("; Loop context unions\n") != 1:
            raise CaptureError("Eggcc initialization boundaries changed")
        seed_program = source.split("; Program nodes\n", 1)[1].split("; Loop context unions\n", 1)[0]
        replay_program, source_anchors = eggcc_source_anchors(result["graph"], result["program"], source)
        checks, roots = eggcc_output_checks(
            result["graph"], result["program"], batch, seed_program, source_anchors=source_anchors
        )
        lookup_program, checks, selection_lookups = eggcc_dag_lookups(
            replay_program, result["graph"], result["program"], checks, roots, source_anchors
        )
        if selection_lookups["status"] == "existing-row-dag":
            for root, request in zip(roots, selection_lookups["requests"], strict=True):
                witness = root["witness"]
                witness.update(
                    selection_lookup=request,
                    structural_query_fact_count=witness["query_fact_count"],
                    query_fact_count=3,
                )
        reconstructed_checks = []
        reconstructed_roots = []
        output_names = []
        for output_index, output in enumerate(outputs["payload"]["outputs"]):
            facts, output_roots = eggcc_seed_query(output["program"], "reconstruction_")
            if list(output_roots) != [output["name"]]:
                raise CaptureError("reconstruction output does not match its native Function name")
            output_names.append(output["name"])
            reconstructed_checks.append("(check\n  " + "\n  ".join(facts) + "\n)\n")
            reconstructed_roots.append(
                {
                    "name": output["name"],
                    "output": output_index,
                    "event": outputs["sequence"],
                    "program_sha256": hashlib.sha256(output["program"].encode()).hexdigest(),
                }
            )
        if sorted(output_names) != sorted(batch):
            raise CaptureError("native reconstruction did not return every requested Function")
        sessions.append(
            {
                "kind": "optimization",
                "pass": original["pass"],
                "batch": batch,
                "program": original["program"],
                "replay_program": replay_program,
                "source_anchors": source_anchors,
                "lookup_program": lookup_program,
                "selection_lookups": selection_lookups,
                "checks": checks,
                "roots": roots,
                "events": [start["sequence"], tiger["sequence"], end["sequence"]],
            }
        )
        reconstruction_program, reconstruction_checks, reconstruction_lookups = eggcc_reconstruction_lookups(
            result["program"], "\n".join(reconstructed_checks), reconstructed_roots
        )
        # Native reconstruction is a separate, source-seeded graph. Its ordinary
        # output requests name every Function and remain separate from membership
        # checks against the preceding optimized graph.
        sessions.append(
            {
                "kind": "reconstruction",
                "pass": original["pass"],
                "batch": batch,
                "program": result["program"],
                "lookup_program": reconstruction_program,
                "checks": reconstruction_checks,
                "reconstruction_lookups": reconstruction_lookups,
                "roots": reconstructed_roots,
                "events": [tiger["sequence"], outputs["sequence"], reconstructed["sequence"]],
            }
        )
    starts = [event["payload"] for event in body if event["kind"] == "optimization-start"]
    expected = starts[0].get("expected_passes")
    if (
        not isinstance(expected, int)
        or expected < 1
        or any(start.get("expected_passes") != expected for start in starts)
    ):
        raise CaptureError("Eggcc did not retain a consistent full schedule length")
    if sorted({start["pass"] for start in starts}) != list(range(expected)):
        raise CaptureError("Eggcc completed only a prefix of its native optimization passes")
    return sessions


def churchroad_selection_check(
    graph: dict[str, Any],
    choices: dict[str, str],
    root: str,
    *,
    input_node: str | None = None,
    port: str | None = None,
    prefix: str = "churchroad_reproduction_",
) -> str:
    """Check an observed Churchroad selection, preserving its exact root choice.

    Native node_to_string uses the supplied root node and follows `choices` only
    for children. Port roots additionally bind the original IsPort output row;
    intermediate specs/port bindings bind their actual input node instead.
    """
    query = WitnessQuery(graph, prefix)
    nodes = graph["nodes"]
    selected = {root: f"{prefix}s0"}
    pending = [root]
    while pending:
        node_id = pending.pop()
        node = nodes[node_id]
        children = []
        for child in node["children"]:
            eclass = nodes[child]["eclass"]
            chosen = choices.get(eclass)
            if chosen is None or chosen not in nodes or nodes[chosen]["eclass"] != eclass:
                raise CaptureError(f"Churchroad selection lacks a valid chosen node for {eclass}")
            if chosen not in selected:
                selected[chosen] = f"{prefix}s{len(selected)}"
                pending.append(chosen)
            children.append(selected[chosen])
        query.facts.append(f"(= {selected[node_id]} {query.expression(node_id, children)})")
    if input_node is not None:
        if nodes[input_node]["eclass"] != nodes[root]["eclass"]:
            raise CaptureError("Churchroad input and selected result have different original eclasses")
        original = query.original(input_node)
        query.facts.append(f"(= {original} {selected[root]})")
    elif port is not None:
        ports = [
            value
            for value in nodes.values()
            if value["op"] == "IsPort"
            and len(value["children"]) == 4
            and nodes[value["children"][1]]["op"] == json.dumps(port, ensure_ascii=False)
            and nodes[value["children"][2]]["op"] == "Output"
            and nodes[value["children"][3]]["eclass"] == nodes[root]["eclass"]
        ]
        if len(ports) != 1:
            raise CaptureError(f"Churchroad output port {port!r} lacks an unambiguous original IsPort row")
        module, name, _, _ = ports[0]["children"]
        query.facts.append(
            f"(IsPort {query.expression(module, [])} {query.expression(name, [])} (Output) {selected[root]})"
        )
    else:
        raise CaptureError("Churchroad selected result has no input/output-port anchor")
    return query.finish()


def churchroad_mapping_session(events: list[dict[str, Any]], *, circuit_outputs: bool = False) -> dict[str, Any]:
    """Recover complete saturation and its actual spec selections before synthesis.

    Keep all preceding calls in the same graph. The terminal checks observe both
    the proposed mapping and its chosen equal spec; they insert no graph facts.
    Circuit mode instead extracts the original output ports after an empty
    proposal phase; it does not claim to recover a native-selected circuit.
    """
    mappings = [event for event in events if event["kind"] == "mapping-snapshot"]
    if len(mappings) != 1:
        raise CaptureError("Churchroad phase lacks one completed mapping snapshot")
    mapping = mappings[0]
    prefix = [event for event in events if event["sequence"] <= mapping["sequence"]]
    if [event["kind"] for event in prefix] != [
        "commands",
        "commands-result",
        "commands",
        "commands-result",
        "yosys-output",
        "commands",
        "commands-result",
        "initial-roots",
        "commands",
        "commands-result",
        "commands",
        "commands-result",
        "mapping-snapshot",
    ]:
        raise CaptureError("Churchroad phase lacks the complete ordered initialization and mapping calls")
    commands = [event for event in prefix if event["kind"] == "commands"]
    if any(event["payload"].get("success") is not True for event in prefix if event["kind"] == "commands-result"):
        raise CaptureError("Churchroad phase contains an unsuccessful native Egglog call")
    if commands[-1]["payload"]["program"].strip() != "(run-schedule (saturate (seq typing transform mapping)))":
        raise CaptureError("Churchroad phase did not run the full original saturation schedule")
    yosys = prefix[4]["payload"]
    if not yosys.get("success") or yosys["stdout"] != commands[2]["payload"]["program"]:
        raise CaptureError("Churchroad phase did not import its successful native Yosys output")
    if not prefix[7]["payload"].get("names"):
        raise CaptureError("Churchroad phase has no original output ports")
    omitted = commands[1]
    if (
        not (omitted["payload"].get("include_path") or "").endswith("/module_enumeration_rewrites.egg")
        or hashlib.sha256(omitted["payload"]["program"].encode()).hexdigest() != CHURCHROAD_MODULE_ENUM_SHA256
    ):
        raise CaptureError("Churchroad phase module-enumeration declarations changed")
    active = [event for event in commands if event is not omitted]
    if any("enumerate-modules" in event["payload"]["program"] for event in active):
        raise CaptureError("active Churchroad module enumeration cannot be omitted")
    if any("(include " in event["payload"]["program"] for event in active):
        raise CaptureError("Churchroad phase contains an uncaptured nested include")
    proposals = mapping["payload"]["proposals"]
    if circuit_outputs:
        if proposals:
            raise CaptureError("behavioral circuit recovery is scoped to empty mapping proposals")
        names = prefix[7]["payload"]["names"]
        nodes = mapping["payload"]["graph"]["nodes"]
        ports = [
            node
            for node in nodes.values()
            if node["op"] == "IsPort" and len(node["children"]) == 4 and nodes[node["children"][2]]["op"] == "Output"
        ]
        if len(names) != len(set(names)) or len(ports) != len(names):
            raise CaptureError("Churchroad circuit outputs do not match the original output-port inventory")
        imported = [tokens for _, _, tokens in egglog_forms(commands[2]["payload"]["program"])]
        roots = []
        for name in names:
            matched = [port for port in ports if nodes[port["children"][1]]["op"] == json.dumps(name)]
            if len(matched) != 1:
                raise CaptureError("Churchroad circuit output port is missing or ambiguous")
            module, port_name, _, node = matched[0]["children"]
            source_ports = [
                form
                for form in imported
                if len(form) == 9
                and form[:7] == ["(", "IsPort", nodes[module]["op"], nodes[port_name]["op"], "(", "Output", ")"]
            ]
            if len(source_ports) != 1 or ["(", "let", name, source_ports[0][-2], ")"] not in imported:
                raise CaptureError("Churchroad circuit output lacks its original imported global alias")
            roots.append(
                {"name": name, "module": json.loads(nodes[module]["op"]), "node": node, "class": nodes[node]["eclass"]}
            )
        return {
            "kind": "circuit-extraction",
            "phase_boundary": "complete mapping saturation followed by adapted behavioral output extraction",
            "mapping_snapshot_event": mapping["sequence"],
            "parts": [
                *({"program": event["payload"]["program"], "checks": ""} for event in active),
                {"program": "\n".join(f"(extract {root['name']})" for root in roots), "checks": ""},
            ],
            "roots": roots,
            "program": "\n".join(event["payload"]["program"] for event in commands),
            "checks": "",
            "events": [event["sequence"] for event in prefix],
            "omitted_declarations": {
                "event": omitted["sequence"],
                "sha256": CHURCHROAD_MODULE_ENUM_SHA256,
                "reason": "closed native mapping schedule never references enumerate-modules",
            },
        }
    if not proposals or len(proposals) != len(set(proposals)):
        raise CaptureError("Churchroad phase requires nonempty distinct observed mapping outputs")
    # The native driver selects specs immediately before its first synthesis.
    # Do not recover a set whose remaining selections depend on later host work.
    following = [event for event in events if event["sequence"] > mapping["sequence"]]
    selections = []
    for event in following:
        if event["kind"] != "selection":
            break
        payload = event["payload"]
        if payload.get("snapshot") != "mapping" or payload.get("kind") != "spec":
            raise CaptureError("Churchroad phase selection is not a pre-synthesis mapping spec")
        selections.append(event)
    if [event["payload"]["input"] for event in selections] != proposals:
        raise CaptureError("Churchroad phase lacks a pre-synthesis spec selection for every proposal")
    graph = mapping["payload"]["graph"]
    checks, roots = [], []
    for index, event in enumerate(selections):
        payload = event["payload"]
        if graph["nodes"][payload["input"]]["op"] not in {"PrimitiveInterfaceDSP", "PrimitiveInterfaceDSP3"}:
            raise CaptureError("Churchroad phase observed an unsupported mapping proposal")
        checks.append(
            churchroad_selection_check(
                graph,
                dict(payload["choices"]),
                payload["root"],
                input_node=payload["input"],
                prefix=f"churchroad_reproduction_{index}_",
            )
        )
        roots.append(
            {
                "kind": "spec",
                "input": payload["input"],
                "node": payload["root"],
                "class": graph["nodes"][payload["root"]]["eclass"],
                "selection_event": event["sequence"],
            }
        )
    return {
        "kind": "mapping-phase",
        "phase_boundary": "complete mapping saturation and observed spec selection before Lakeroad",
        "mapping_snapshot_event": mapping["sequence"],
        "parts": [
            *({"program": event["payload"]["program"], "checks": ""} for event in active),
            {"program": "", "checks": "\n".join(checks)},
        ],
        "roots": roots,
        "program": "\n".join(event["payload"]["program"] for event in commands),
        "checks": "\n".join(checks),
        "events": [event["sequence"] for event in [*prefix, *selections]],
        "omitted_declarations": {
            "event": omitted["sequence"],
            "sha256": CHURCHROAD_MODULE_ENUM_SHA256,
            "reason": "closed native mapping schedule never references enumerate-modules",
        },
    }


def churchroad_sessions(events: list[dict[str, Any]]) -> list[dict[str, Any]]:
    """Assemble the one native persistent graph, with checks at its snapshots."""
    if not events or events[-1]["kind"] != "parent-complete" or not events[-1]["payload"].get("verilog"):
        raise CaptureError("Churchroad did not finish emitting its final Verilog")
    by_kind: dict[str, list[dict[str, Any]]] = {}
    for event in events:
        by_kind.setdefault(event["kind"], []).append(event)
    allowed = {
        "commands",
        "commands-result",
        "initial-roots",
        "mapping-snapshot",
        "selection",
        "synthesis-input",
        "synthesis-output",
        "yosys-output",
        "final-selection",
        "parent-complete",
    }
    if set(by_kind) - allowed:
        raise CaptureError(f"unaccounted Churchroad native events: {sorted(set(by_kind) - allowed)}")
    if any(len(by_kind.get(kind, [])) != 1 for kind in ("initial-roots", "mapping-snapshot", "final-selection")):
        raise CaptureError("Churchroad did not retain exactly one initial, mapping, and final root snapshot")
    mapping = by_kind["mapping-snapshot"][0]
    final = by_kind["final-selection"][0]
    selections = by_kind.get("selection", [])
    proposals = mapping["payload"]["proposals"]
    specs = [event for event in selections if event["payload"]["kind"] == "spec"]
    if [event["payload"]["input"] for event in specs] != proposals:
        raise CaptureError("Churchroad did not capture one actual spec for every native mapping proposal")
    expected_selections = []
    for proposal in proposals:
        node = mapping["payload"]["graph"]["nodes"][proposal]
        if node["op"] not in {"PrimitiveInterfaceDSP", "PrimitiveInterfaceDSP3"}:
            raise CaptureError("Churchroad reached an unsupported native proposal kind")
        expected_selections.append(("spec", proposal))
        expected_selections.extend(("port-binding", child) for child in [*node["children"], proposal])
    if [(event["payload"]["kind"], event["payload"]["input"]) for event in selections] != expected_selections:
        raise CaptureError("Churchroad did not capture all actual spec and port-binding selections")
    for kind in ("synthesis-input", "synthesis-output"):
        if len(by_kind.get(kind, [])) != len(proposals):
            raise CaptureError("Churchroad did not retain all synthesis input/output pairs")
    if any(not event["payload"].get("success") for event in by_kind.get("synthesis-output", [])):
        raise CaptureError("Churchroad retained an unsuccessful synthesis call")
    commands = by_kind.get("commands", [])
    if len(commands) != 5 + len(proposals):
        raise CaptureError("Churchroad command count differs from the pinned initialization/mapping/synthesis flow")
    if any(command["sequence"] > mapping["sequence"] for command in commands[:5]) or any(
        not mapping["sequence"] < command["sequence"] < final["sequence"] for command in commands[5:]
    ):
        raise CaptureError("Churchroad initialization/synthesis commands cross their native snapshot boundaries")
    # Pair the engine delegate receipts in event order. A captured call alone is
    # not evidence that its original program was executed successfully.
    pending_command = None
    for event in events:
        if event["kind"] == "commands":
            if pending_command is not None:
                raise CaptureError("Churchroad command lacks its native engine completion")
            pending_command = event
        elif event["kind"] == "commands-result":
            if pending_command is None or not event["payload"].get("success"):
                raise CaptureError("Churchroad native engine call failed or has no matching input")
            pending_command = None
    if pending_command is not None:
        raise CaptureError("Churchroad final engine call did not complete")
    yosys = by_kind.get("yosys-output", [])
    if len(yosys) != 1 + len(proposals):
        raise CaptureError("Churchroad did not retain every Yosys frontend/synthesis translation")
    for event in yosys:
        following = next((command for command in commands if command["sequence"] > event["sequence"]), None)
        if (
            not event["payload"].get("success")
            or following is None
            or following["payload"]["program"] != event["payload"]["stdout"]
        ):
            raise CaptureError("Churchroad translated host output was not fed to the next native engine call")
    omitted = [
        event
        for event in commands
        if (event["payload"].get("include_path") or "").endswith("/module_enumeration_rewrites.egg")
    ]
    if (
        len(omitted) != 1
        or hashlib.sha256(omitted[0]["payload"]["program"].encode()).hexdigest() != CHURCHROAD_MODULE_ENUM_SHA256
    ):
        raise CaptureError("Churchroad module-enumeration declarations changed; review their active-operation boundary")
    active_commands = [event for event in commands if event is not omitted[0]]
    if any("enumerate-modules" in event["payload"]["program"] for event in active_commands):
        raise CaptureError(
            "active Churchroad enumerate-modules requires unsupported debruijnify; declarations cannot be dropped"
        )
    mapping_checks = []
    for index, event in enumerate(selections):
        payload = event["payload"]
        if payload.get("snapshot") != "mapping" or event["sequence"] < mapping["sequence"]:
            raise CaptureError("Churchroad selection has an unknown source snapshot")
        mapping_checks.append(
            churchroad_selection_check(
                mapping["payload"]["graph"],
                dict(payload["choices"]),
                payload["root"],
                input_node=payload["input"],
                prefix=f"churchroad_reproduction_{index}_",
            )
        )
    payload = final["payload"]
    roots = payload["roots"]
    names = by_kind["initial-roots"][0]["payload"]["names"]
    if not roots or [root["name"] for root in roots] != names:
        raise CaptureError("Churchroad final extraction lost or reordered original output-port aliases")
    final_checks = []
    for index, root in enumerate(roots):
        if payload["graph"]["nodes"][root["node"]]["eclass"] != root["class"]:
            raise CaptureError("Churchroad output-root class and selected node disagree")
        final_checks.append(
            churchroad_selection_check(
                payload["graph"],
                dict(payload["choices"]),
                root["node"],
                port=root["name"],
                prefix=f"churchroad_reproduction_final_{index}_",
            )
        )
    # All spec and binding extractions use the pre-loop mapping snapshot, even
    # when the host performs them later. Check them before any synthesis update.
    parts = []
    inserted = False
    for event in active_commands:
        if not inserted and event["sequence"] > mapping["sequence"]:
            parts.append({"program": "", "checks": "\n".join(mapping_checks)})
            inserted = True
        program = event["payload"]["program"]
        if "(include " in program:
            raise CaptureError("Churchroad replay contains an uncaptured nested include")
        parts.append({"program": program, "checks": ""})
    if not inserted:
        parts.append({"program": "", "checks": "\n".join(mapping_checks)})
    parts.append({"program": "", "checks": "\n".join(final_checks)})
    return [
        {
            "kind": "persistent",
            "parts": parts,
            "roots": roots,
            "program": "\n".join(event["payload"]["program"] for event in commands),
            "checks": "\n".join(mapping_checks + final_checks),
            "events": [event["sequence"] for event in events],
            "omitted_declarations": {
                "event": omitted[0]["sequence"],
                "sha256": CHURCHROAD_MODULE_ENUM_SHA256,
                "reason": "closed native schedule never references enumerate-modules",
            },
        }
    ]
