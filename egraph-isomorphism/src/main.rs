use std::{fs::File, io, process::ExitCode};

use egraph_isomorphism::{
    AnnotatedEGraph, Graph, Limits, Outcome, Witness, find_isomorphism, verify,
};
use serde::Deserialize;
use serde_json::{Value, json};

#[derive(Deserialize)]
#[serde(untagged)]
enum Request {
    Compare(Box<Comparison>),
    Validate { graph: Box<AnnotatedEGraph> },
}

#[derive(Deserialize)]
struct Comparison {
    left: AnnotatedEGraph,
    right: AnnotatedEGraph,
    #[serde(default)]
    limits: Limits,
    #[serde(default)]
    witness: Option<Witness>,
}

fn request() -> Result<Request, Box<dyn std::error::Error>> {
    let mut args = std::env::args().skip(1);
    let Some(left) = args.next() else {
        return Ok(serde_json::from_reader(io::stdin().lock())?);
    };
    let right = args.next().ok_or("expected LEFT.json RIGHT.json")?;
    let mut limits = Limits::default();
    let mut witness = None;
    while let Some(arg) = args.next() {
        let value = args.next().ok_or("missing option value")?;
        match arg.as_str() {
            "--search-limit" => limits.search = value.parse()?,
            "--node-limit" => limits.node_variants = value.parse()?,
            "--witness" => witness = Some(serde_json::from_reader(File::open(value)?)?),
            _ => return Err(format!("unknown option: {arg}").into()),
        }
    }
    Ok(Request::Compare(Box::new(Comparison {
        left: serde_json::from_reader(File::open(left)?)?,
        right: serde_json::from_reader(File::open(right)?)?,
        limits,
        witness,
    })))
}

fn run() -> Result<(Value, u8), Box<dyn std::error::Error>> {
    let request = match request()? {
        Request::Compare(request) => *request,
        Request::Validate { graph } => {
            let (classes, nodes) = Graph::try_from(graph.as_ref())?.counts();
            return Ok((
                json!({"status":"valid", "classes":classes, "nodes":nodes}),
                0,
            ));
        }
    };
    let left = Graph::try_from(&request.left).map_err(|e| format!("left graph: {e}"))?;
    let right = Graph::try_from(&request.right).map_err(|e| format!("right graph: {e}"))?;
    if let Some(witness) = request.witness {
        return Ok(match verify(&left, &right, &witness) {
            Ok(()) => (json!({"status": "verified"}), 0),
            Err(e) => (
                json!({"status": "invalid_witness", "reason": e.to_string()}),
                4,
            ),
        });
    }
    let outcome = find_isomorphism(&left, &right, request.limits)?;
    let code = match outcome {
        Outcome::Isomorphic { .. } => 0,
        Outcome::Different { .. } => 1,
        Outcome::Inconclusive { .. } => 3,
    };
    Ok((serde_json::to_value(outcome)?, code))
}

fn main() -> ExitCode {
    if std::env::args()
        .nth(1)
        .is_some_and(|a| a == "--help" || a == "-h")
    {
        println!(
            "egraph-isomorphism LEFT.json RIGHT.json [--search-limit N] [--node-limit N] [--witness FILE]\n\nWith no arguments, reads {{left, right, limits?, witness?}} JSON from stdin,\nor {{graph}} to validate a document and report its class/node counts.\nPrints a JSON verdict and witness. Exit codes: 0 equal/verified/valid, 1 different,\n2 invalid input, 3 inconclusive, 4 invalid witness. --witness reads the witness\nobject from an earlier isomorphic result. Inputs use egraph-serialize with\noptional slotted annotations; exports must be complete."
        );
        return ExitCode::SUCCESS;
    }
    let (result, code) =
        run().unwrap_or_else(|e| (json!({"status": "invalid", "reason": e.to_string()}), 2));
    if serde_json::to_writer(io::stdout().lock(), &result).is_err() {
        return ExitCode::from(2);
    }
    ExitCode::from(code)
}
