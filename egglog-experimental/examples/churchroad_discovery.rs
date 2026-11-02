//! Bounded Churchroad discovery over a frozen circuit, driven by churchroad-eval.py.
use egglog::{
    EGraph, SerializeConfig, add_primitive,
    sort::{MapContainer, VecContainer},
};
use egglog_experimental::slotted::{self, Compiler};
use serde_json::{Value, json};
use std::{collections::HashMap, fs, io::Write, path::Path, time::Instant};

fn record(directory: &Path, phase: &str, start: Instant) {
    let mut file = fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(directory.join("phases.jsonl"))
        .unwrap();
    writeln!(
        file,
        "{}",
        json!({"phase": phase, "seconds": start.elapsed().as_secs_f64()})
    )
    .unwrap();
}

fn main() {
    let request: Value =
        serde_json::from_str(&fs::read_to_string(std::env::args().nth(1).unwrap()).unwrap())
            .unwrap();
    let directory = Path::new(request["directory"].as_str().unwrap());
    let slots = request["slotted"].as_bool().unwrap();
    let start = Instant::now();
    let mut compiler = Compiler::default();
    let mut graph = if slots {
        slotted::new_egraph()
    } else {
        EGraph::default()
    };
    record(directory, "engine_setup", start);
    let start = Instant::now();
    let declarations = request["declarations"].as_str().unwrap();
    let declarations = if slots {
        compiler.compile(None, declarations).unwrap()
    } else {
        declarations.to_string()
    };
    let maintenance = if slots {
        compiler.compile(None, "(run 0)").unwrap()
    } else {
        String::new()
    };
    record(directory, "source_lowering", start);
    fs::write(directory.join("lowered.egg"), &declarations).unwrap();
    let start = Instant::now();
    graph.parse_and_run_program(None, &declarations).unwrap();
    if !slots {
        let arc = graph.get_sort_by_name("IVec").unwrap().clone();
        // The circuit is frozen: these integers name canonical source e-classes.
        // This favors the vector control by avoiding native egraph.find calls.
        add_primitive!(&mut graph, "debruijnify" = |xs: @VecContainer (arc)| -> @VecContainer (arc) {{
            let mut names = HashMap::new();
            let data = xs.data.iter().map(|v| {
                let next = names.len() as i64;
                let index = *names.entry(*v).or_insert(next);
                state.base_values().get::<i64>(index)
            }).collect();
            VecContainer { data, do_rebuild: false }
        }});
    } else {
        graph
            .parse_and_run_program(None, "(sort IVec (Vec i64))")
            .unwrap();
        let arc = graph.get_sort_by_name("IVec").unwrap().clone();
        let renaming = graph.get_sort_by_name("Renaming").unwrap().clone();
        // Transport a template's occurrence slots through an existing edge.
        // No source-expression canonicalization or fresh numbering happens here.
        add_primitive!(&mut graph, "interface-rename" = |xs: @VecContainer (arc), map: @MapContainer (renaming)| -> @VecContainer (arc) {{
            VecContainer { data: xs.data.iter().map(|x| map.data[x]).collect(), do_rebuild: false }
        }});
    }
    record(directory, "declarations", start);
    for name in ["input", "rules"] {
        let start = Instant::now();
        graph
            .parse_and_run_program(None, request[name].as_str().unwrap())
            .unwrap();
        record(directory, name, start);
    }
    for _ in 0..request["rounds"].as_u64().unwrap() {
        let start = Instant::now();
        graph
            .parse_and_run_program(None, "(run enumerate 1)")
            .unwrap();
        record(directory, "enumeration", start);
        if slots && request["eager_maintenance"].as_bool().unwrap_or(false) {
            let start = Instant::now();
            graph.parse_and_run_program(None, &maintenance).unwrap();
            record(directory, "slot_maintenance", start);
        }
        if slots {
            let start = Instant::now();
            graph
                .parse_and_run_program(None, "(run-schedule (saturate (run interfaces)))")
                .unwrap();
            record(directory, "interfaces", start);
        }
    }
    // Canonical construction above maintains the invariants incrementally:
    // ordered templates never union, shrink, or acquire symmetries. The logical
    // exporter independently validates those invariants. The eager treatment
    // runs generic maintenance as a correctness/performance control.
    let start = Instant::now();
    let mut candidates = Vec::new();
    graph.function_entries("Candidate", |row| {
        let root = graph.value_to_base::<i64>(row.inputs[0]);
        if slots {
            let map = graph.value_to_container::<egglog::sort::MapContainer>(row.inputs[2]).unwrap();
            let bindings: Vec<_> = map.data.iter().map(|(k, v)| (graph.value_to_base::<i64>(*k), graph.value_to_base::<i64>(*v))).collect();
            candidates.push(json!({"root": root, "class": format!("M-{:?}", row.inputs[1]), "bindings": bindings}));
        } else {
            let args = graph.value_to_container::<VecContainer>(row.inputs[2]).unwrap();
            let args: Vec<_> = args.data.iter().map(|v| graph.value_to_base::<i64>(*v)).collect();
            candidates.push(json!({"root": root, "class": graph.value_to_class_id(graph.get_sort_by_name("Module").unwrap(), row.inputs[1]), "arguments": args}));
        }
    }).unwrap();
    let document = if slots {
        serde_json::to_value(slotted::export::export(&graph).unwrap()).unwrap()
    } else {
        let exported = graph.serialize(SerializeConfig::default());
        assert!(exported.is_complete());
        serde_json::to_value(exported.egraph).unwrap()
    };
    record(directory, "graph_export", start);
    fs::write(
        directory.join("graph.json"),
        serde_json::to_vec(&document).unwrap(),
    )
    .unwrap();
    fs::write(
        directory.join("candidates.json"),
        serde_json::to_vec(&candidates).unwrap(),
    )
    .unwrap();
    fs::write(
        directory.join("run-report.json"),
        serde_json::to_vec(graph.get_overall_run_report()).unwrap(),
    )
    .unwrap();
}
