use std::io::Write;
use std::process::{Command, Stdio};

use serde_json::{Value, json};

fn request(value: Value) -> (i32, Value) {
    let mut child = Command::new(env!("CARGO_BIN_EXE_egraph-isomorphism"))
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    child
        .stdin
        .take()
        .unwrap()
        .write_all(serde_json::to_string(&value).unwrap().as_bytes())
        .unwrap();
    let output = child.wait_with_output().unwrap();
    assert!(
        output.stderr.is_empty(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    (
        output.status.code().unwrap(),
        serde_json::from_slice(&output.stdout).unwrap(),
    )
}

#[test]
fn json_protocol_distinguishes_all_verdicts_and_verifies_saved_witnesses() {
    let graph = json!({"nodes":{"node":{"op":"constant","eclass":"class"}}});
    let (code, valid) = request(json!({"graph":graph}));
    assert_eq!(code, 0);
    assert_eq!(valid, json!({"status":"valid", "classes":1, "nodes":1}));
    let (code, invalid) =
        request(json!({"graph":{"nodes":{"n":{"op":"x","eclass":"c","children":["absent"]}}}}));
    assert_eq!(code, 2);
    assert_eq!(invalid["status"], "invalid");
    let comparison = json!({"left":graph, "right":graph});
    let (code, equal) = request(comparison.clone());
    assert_eq!(code, 0);
    assert_eq!(equal["status"], "isomorphic");
    let mut check = comparison.clone();
    check["witness"] = equal["witness"].clone();
    let (code, verified) = request(check.clone());
    assert_eq!(code, 0);
    assert_eq!(verified["status"], "verified");
    check["witness"]["classes"]["class"]["target"] = json!("absent");
    let (code, invalid) = request(check);
    assert_eq!(code, 4);
    assert_eq!(invalid["status"], "invalid_witness");
    let mut other = comparison.clone();
    other["right"]["nodes"]["node"]["op"] = json!("different");
    let (code, different) = request(other);
    assert_eq!(code, 1);
    assert_eq!(different["status"], "different");
    let mut limited = comparison.clone();
    limited["limits"] = json!({"search":0});
    let (code, limit) = request(limited);
    assert_eq!(code, 3);
    assert_eq!(limit["status"], "inconclusive");
    let mut broken = comparison;
    broken["left"]["nodes"]["node"]["children"] = json!(["missing"]);
    let (code, invalid) = request(broken);
    assert_eq!(code, 2);
    assert_eq!(invalid["status"], "invalid");
}
