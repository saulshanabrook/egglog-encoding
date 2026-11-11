"""Native capture patches and fail-closed output witnesses for Eggcc/Churchroad.

The patches observe native execution. They never replace its extractor or its
feedback. A replay is admitted separately, after the recorded parent completes
and the ordinary engine checks the observed results against existing rows.
"""

from __future__ import annotations

import difflib
import hashlib
import json
import re
from collections import Counter
from pathlib import Path
from typing import Any


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


def read_events(directory: Path, *, max_bytes: int = 128 * 1024**2) -> list[dict[str, Any]]:
    """Reject gaps, incomplete writes, unknown versions, and absent completion."""
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
    if not events or events[-1]["kind"] != "parent-complete":
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


def eggcc_output_checks(
    graph: dict[str, Any], program: str, batch: list[str], seed_program: str
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
            children = [
                substitutions[position] if position in substitutions else query.original(child)
                for position, child in enumerate(original_children)
            ]
            query.facts.append(f"(= {prefix}s{index} {query.expression(node_id, children)})")
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
        checks, roots = eggcc_output_checks(result["graph"], result["program"], batch, seed_program)
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
                "checks": checks,
                "roots": roots,
                "events": [start["sequence"], tiger["sequence"], end["sequence"]],
            }
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
                "checks": "\n".join(reconstructed_checks),
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
