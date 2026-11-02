// Built in the pinned Churchroad checkout. Its enumeration rules are unchanged.
use egglog::{EGraph, SerializeConfig};
use serde_json::{json, Value};
use std::{fs, io::Write, path::Path, time::Instant};

fn record(directory: &Path, phase: &str, start: Instant) {
    let mut file = fs::OpenOptions::new().create(true).append(true)
        .open(directory.join("phases.jsonl")).unwrap();
    writeln!(file, "{}", json!({"phase": phase, "seconds": start.elapsed().as_secs_f64()})).unwrap();
}

fn main() {
    let request: Value = serde_json::from_str(&fs::read_to_string(std::env::args().nth(1).unwrap()).unwrap()).unwrap();
    let directory = Path::new(request["directory"].as_str().unwrap());
    let start = Instant::now();
    let mut graph = EGraph::default();
    churchroad::import_churchroad(&mut graph);
    record(directory, "declarations", start);
    let start = Instant::now();
    graph.parse_and_run_program(None, request["input"].as_str().unwrap()).unwrap();
    record(directory, "input", start);
    for _ in 0..request["rounds"].as_u64().unwrap() {
        let start = Instant::now();
        graph.parse_and_run_program(None, "(run enumerate-modules 1)").unwrap();
        record(directory, "enumeration", start);
    }
    let start = Instant::now();
    let document = graph.serialize(SerializeConfig::default());
    record(directory, "graph_export", start);
    fs::write(directory.join("graph.json"), serde_json::to_vec(&document).unwrap()).unwrap();
}
