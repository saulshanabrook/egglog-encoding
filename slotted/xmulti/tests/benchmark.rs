//! Exercise the frozen input, native limit, goal, and same-process report boundary.

#![cfg(not(feature = "checks"))]

use std::process::Command;

#[test]
fn frozen_benchmark_preserves_substitution_and_reports_the_same_execution() {
    let directory = std::env::temp_dir().join(format!("xmulti-benchmark-{}", std::process::id()));
    std::fs::create_dir_all(&directory).unwrap();
    let input = directory.join("test.ref");
    let summary = directory.join("timing.json");
    let spec = "rounds 0\nterm (null)\ngoal (null)\n";
    std::fs::write(
        &input,
        serde_json::json!({"multi": spec, "nested": spec}).to_string(),
    )
    .unwrap();
    for matcher in ["multi", "nested"] {
        for substitution in ["snapshot", "syntactic"] {
            let result = Command::new(env!("CARGO_BIN_EXE_xmulti"))
                .args([
                    "--matcher",
                    matcher,
                    "--substitution",
                    substitution,
                    "--timing-summary",
                ])
                .arg(&summary)
                .arg(&input)
                .output()
                .unwrap();
            assert!(
                result.status.success(),
                "{}",
                String::from_utf8_lossy(&result.stderr)
            );
            let output = String::from_utf8(result.stdout).unwrap();
            assert!(output.contains("CONFIG checks=off"));
            assert!(output.contains(&format!("CONFIG substitution={substitution}")));
            assert!(output.contains("GOAL yes"));
            assert!(!output.contains("GRAPH "));
            let report: serde_json::Value =
                serde_json::from_slice(&std::fs::read(&summary).unwrap()).unwrap();
            assert_eq!(
                report["schema_version"],
                egglog_reports::TimingSummary::SCHEMA_VERSION
            );
            assert!(report["frontend_parse_ns"].as_u64().unwrap() > 0);
            assert!(report["commands_check_ns"].as_u64().unwrap() > 0);
            assert_eq!(report["rulesets"], serde_json::json!([]));
        }
    }
    std::fs::remove_file(&summary).unwrap();
    std::fs::write(
        &input,
        serde_json::json!({
            "multi": "rounds 0\nterm (null)\ngoal (f (null) (null))\n",
            "nested": null,
            "unsupported_reason": "requires multipatterns"
        })
        .to_string(),
    )
    .unwrap();
    let failed = Command::new(env!("CARGO_BIN_EXE_xmulti"))
        .args([
            "--matcher",
            "multi",
            "--substitution",
            "snapshot",
            "--timing-summary",
        ])
        .arg(&summary)
        .arg(&input)
        .output()
        .unwrap();
    assert_eq!(failed.status.code(), Some(1));
    assert!(String::from_utf8(failed.stdout)
        .unwrap()
        .contains("GOAL no"));
    assert!(!summary.exists());
    let unsupported = Command::new(env!("CARGO_BIN_EXE_xmulti"))
        .args(["--matcher", "nested", "--substitution", "syntactic"])
        .arg(&input)
        .output()
        .unwrap();
    assert_eq!(unsupported.status.code(), Some(2));
    assert!(String::from_utf8(unsupported.stderr)
        .unwrap()
        .contains("requires multipatterns"));
    let limited = Command::new(env!("CARGO_BIN_EXE_xmulti"))
        .args(["--memory-limit-bytes=0", "--help"])
        .output()
        .unwrap();
    assert_eq!(limited.status.code(), Some(87));
    std::fs::remove_dir_all(directory).unwrap();
}
