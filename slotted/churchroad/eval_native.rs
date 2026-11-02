// Built by churchroad-eval.py in the pinned Churchroad checkout.
// All mapping, synthesis, and extraction functions come from that checkout.
use churchroad::*;
use egglog::{EGraph, SerializeConfig};
use serde_json::{json, Value};
use std::collections::HashMap;
use std::fs;
use std::io::Write;
use std::path::Path;
use std::time::Instant;

fn measured<T>(directory: &Path, name: &str, f: impl FnOnce() -> T) -> T {
    let start = Instant::now();
    let result = f();
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
    result
}

fn main() {
    let request: Value =
        serde_json::from_str(&fs::read_to_string(std::env::args().nth(1).unwrap()).unwrap())
            .unwrap();
    let directory = Path::new(request["directory"].as_str().unwrap());
    let mut graph = EGraph::default();
    measured(directory, "engine_setup", || import_churchroad(&mut graph));
    if let Some(verilog) = request["verilog"].as_str() {
        let commands = measured(directory, "frontend", || {
            commands_from_verilog_file(
                Path::new(verilog),
                request["top"].as_str().unwrap(),
                true,
                true,
                HashMap::new(),
            )
        });
        fs::write(directory.join("frontend.egg"), &commands).unwrap();
        measured(directory, "import", || {
            graph.parse_and_run_program(None, &commands).unwrap()
        });
    } else {
        measured(directory, "import", || {
            graph
                .parse_and_run_program(None, request["input"].as_str().unwrap())
                .unwrap()
        });
    }
    let outputs = measured(directory, "ports", || {
        let serialized = graph.serialize(SerializeConfig::default());
        get_inputs_and_outputs_serialized(&serialized)
            .1
            .into_iter()
            .map(|(name, id)| (name, graph.class_id_to_value(&id)))
            .collect::<Vec<_>>()
    });
    if let Some(rules) = request["rules"].as_str() {
        measured(directory, "rules", || {
            graph.parse_and_run_program(None, rules).unwrap()
        });
        measured(directory, "eqsat", || {
            graph
                .parse_and_run_program(
                    None,
                    "(run-schedule (saturate (seq typing transform mapping)))",
                )
                .unwrap()
        });
    }
    let serialized = measured(directory, "graph_export", || {
        graph.serialize(SerializeConfig::default())
    });
    fs::write(
        directory.join("graph.json"),
        serde_json::to_vec(&serialized).unwrap(),
    )
    .unwrap();
    let proposals = measured(directory, "proposals", || {
        find_primitive_interfaces_serialized(&serialized)
    });
    fs::write(
        directory.join("proposals.json"),
        serde_json::to_vec(&proposals).unwrap(),
    )
    .unwrap();
    if !request["synthesis"].as_bool().unwrap_or(false) {
        return;
    }
    for (i, proposal) in proposals.iter().enumerate() {
        let (choices, spec) = measured(directory, "spec_extraction", || {
            find_spec_for_primitive_interface_including_nodes(
                &serialized[proposal].eclass,
                &serialized,
                serialized[proposal].children.iter().cloned().collect(),
            )
        });
        let commands = measured(directory, "synthesis_bridge", || {
            call_lakeroad_on_primitive_interface_and_spec(
                &serialized,
                &choices,
                &spec,
                proposal,
                "xilinx-ultrascale-plus",
            )
        });
        fs::write(directory.join(format!("synthesis-{i}.egg")), &commands).unwrap();
        measured(directory, "reinsertion", || {
            graph.parse_and_run_program(None, &commands).unwrap()
        });
    }
    let final_graph = measured(directory, "final_snapshot", || {
        graph.serialize(SerializeConfig::default())
    });
    let choices = measured(directory, "extraction", || {
        global_greedy_dag::GlobalGreedyDagExtractor {
            structural_only: true,
        }
        .extract(&final_graph, &[])
    });
    let output_map = outputs
        .into_iter()
        .map(|(name, value)| (graph.value_to_class_id(&graph.find(value)), name))
        .collect();
    let verilog = measured(directory, "codegen", || {
        to_verilog_egraph_serialize(
            &final_graph,
            &choices,
            "clk",
            HashMap::new(),
            Some(output_map),
        )
    });
    fs::write(directory.join("mapped.v"), verilog).unwrap();
    fs::write(
        directory.join("final-graph.json"),
        serde_json::to_vec(&final_graph).unwrap(),
    )
    .unwrap();
}
