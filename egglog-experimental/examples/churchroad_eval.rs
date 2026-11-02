//! Phase timer for the independent Python Churchroad evaluation driver.
use egglog::{EGraph, SerializeConfig};
use egglog_experimental::slotted::{self, Compiler};
use serde_json::{Value, json};
use std::{fs, io::Write, path::Path, time::Instant};

fn record(directory: &Path, name: &str, start: Instant) {
    let mut file = fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(directory.join("phases.jsonl"))
        .unwrap();
    writeln!(
        file,
        "{}",
        json!({"phase": name, "seconds": start.elapsed().as_secs_f64()})
    )
    .unwrap();
}

fn snapshot(graph: &EGraph, slots: bool) -> Value {
    if slots {
        serde_json::to_value(slotted::export::export(graph).unwrap()).unwrap()
    } else {
        let result = graph.serialize(SerializeConfig::default());
        assert!(result.is_complete(), "incomplete graph export");
        serde_json::to_value(result.egraph).unwrap()
    }
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
    for name in ["declarations", "input", "rules"] {
        let mut source = request[name].as_str().unwrap().to_string();
        if slots {
            let start = Instant::now();
            source = compiler.compile(None, &source).unwrap();
            record(directory, "source_lowering", start);
        }
        let start = Instant::now();
        graph.parse_and_run_program(None, &source).unwrap();
        record(directory, name, start);
    }
    if let Some(schedule) = request["schedule"].as_str() {
        assert!(!slots);
        let start = Instant::now();
        graph.parse_and_run_program(None, schedule).unwrap();
        record(directory, "eqsat", start);
    } else {
        let start = Instant::now();
        let schedule = if slots {
            compiler.compile(None, "(run 1)").unwrap()
        } else {
            "(run 1)".to_string()
        };
        record(directory, "source_lowering", start);
        let start = Instant::now();
        let mut previous = snapshot(&graph, slots);
        record(directory, "convergence_export", start);
        let limit = request["max_iterations"].as_u64().unwrap();
        let mut converged = false;
        for iteration in 1..=limit {
            let start = Instant::now();
            graph.parse_and_run_program(None, &schedule).unwrap();
            record(directory, "eqsat", start);
            let start = Instant::now();
            let next = snapshot(&graph, slots);
            converged = previous == next;
            record(directory, "convergence_export", start);
            previous = next;
            if converged {
                fs::write(
                    directory.join("convergence.json"),
                    json!({"iterations":iteration,"stable":true}).to_string(),
                )
                .unwrap();
                break;
            }
        }
        assert!(
            converged,
            "mapping did not converge within the iteration budget"
        );
    }
    let start = Instant::now();
    let document = snapshot(&graph, slots);
    record(directory, "graph_export", start);
    fs::write(
        directory.join("graph.json"),
        serde_json::to_vec(&document).unwrap(),
    )
    .unwrap();
}
