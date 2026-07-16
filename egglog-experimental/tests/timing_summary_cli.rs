#![cfg(feature = "dd-backend")]

use std::path::PathBuf;
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT_TEMP_DIRECTORY: AtomicU64 = AtomicU64::new(0);

fn temporary_directory() -> PathBuf {
    let directory = std::env::temp_dir().join(format!(
        "egglog-experimental-dd-timing-summary-{}-{}",
        std::process::id(),
        NEXT_TEMP_DIRECTORY.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir(&directory).unwrap();
    directory
}

#[test]
fn dd_timing_summary_v1_splits_search_and_apply_for_every_named_ruleset() {
    let directory = temporary_directory();
    let program_path = directory.join("program.egg");
    let summary_path = directory.join("summary.json");
    let mut program = String::from(
        r#"
        (ruleset zeta)
        (ruleset alpha)
        (relation seed (i64))
        (relation middle (i64))
        (relation result (i64))
        (rule ((seed x)) ((middle x)) :ruleset zeta)
        (rule ((middle x)) ((result x)) :ruleset alpha)
        "#,
    );
    for value in 0..512 {
        program.push_str(&format!("(seed {value})\n"));
    }
    program.push_str("(run zeta 1)\n(run alpha 1)\n");
    std::fs::write(&program_path, program).unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_egglog-experimental"))
        .arg("--backend")
        .arg("dd")
        .arg("--timing-summary")
        .arg(&summary_path)
        .arg(&program_path)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "egglog-experimental DD failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );

    let bytes = std::fs::read(&summary_path).unwrap();
    assert_eq!(bytes.last(), Some(&b'\n'));
    assert!(!bytes[..bytes.len() - 1].contains(&b'\n'));

    let summary: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
    let summary_object = summary.as_object().unwrap();
    assert_eq!(summary_object.len(), 2);
    assert!(summary_object.contains_key("schema_version"));
    assert!(summary_object.contains_key("rulesets"));
    assert_eq!(summary["schema_version"], 1);

    let rulesets = summary["rulesets"].as_array().unwrap();
    let names = rulesets
        .iter()
        .map(|ruleset| ruleset["name"].as_str().unwrap())
        .collect::<Vec<_>>();
    assert!(names.windows(2).all(|pair| pair[0] < pair[1]));
    for ruleset in rulesets {
        let ruleset_object = ruleset.as_object().unwrap();
        assert_eq!(ruleset_object.len(), 5);
        for field in ["name", "search_ns", "apply_ns", "merge_ns", "rebuild_ns"] {
            assert!(ruleset_object.contains_key(field));
        }
        assert!(ruleset["name"].is_string());
        for field in ["search_ns", "apply_ns", "merge_ns", "rebuild_ns"] {
            assert!(ruleset[field].is_u64());
        }
        assert_eq!(ruleset["rebuild_ns"], 0);
    }

    for name in ["alpha", "zeta"] {
        let timed = rulesets
            .iter()
            .find(|ruleset| ruleset["name"] == name)
            .unwrap_or_else(|| panic!("missing timing for named ruleset {name}"));
        assert!(timed["search_ns"].as_u64().unwrap() > 0);
        assert!(timed["apply_ns"].as_u64().unwrap() > 0);
        assert!(timed["merge_ns"].as_u64().unwrap() > 0);
    }

    std::fs::remove_dir_all(directory).unwrap();
}
