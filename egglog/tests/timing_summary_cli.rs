use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT_TEMP_DIRECTORY: AtomicU64 = AtomicU64::new(0);

fn temporary_directory(label: &str) -> PathBuf {
    let directory = std::env::temp_dir().join(format!(
        "egglog-timing-summary-{label}-{}-{}",
        std::process::id(),
        NEXT_TEMP_DIRECTORY.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir(&directory).unwrap();
    directory
}

fn run_egglog(arguments: &[&Path]) -> Output {
    let mut command = Command::new(env!("CARGO_BIN_EXE_egglog"));
    for argument in arguments {
        command.arg(argument);
    }
    command.output().unwrap()
}

fn assert_duration(value: &serde_json::Value) {
    let duration = value.as_object().unwrap();
    assert_eq!(duration.len(), 2);
    assert!(duration["secs"].is_u64());
    assert!(duration["nanos"].is_u64());
}

fn ruleset<'a>(summary: &'a serde_json::Value, name: &str) -> &'a serde_json::Value {
    summary["rulesets"]
        .as_array()
        .unwrap()
        .iter()
        .find(|ruleset| ruleset["name"] == name)
        .unwrap_or_else(|| panic!("missing ruleset {name:?}"))
}

#[test]
fn checks_have_the_same_command_timing_path_with_and_without_term_encoding() {
    let program = r#"
        (relation item (i64))
        (item 1)
        (check (item 1))
    "#;

    for (label, treatment_flags) in [("off", &[][..]), ("term", &["--term-encoding"][..])] {
        let directory = temporary_directory(label);
        let program_path = directory.join("program.egg");
        let summary_path = directory.join("summary.json");
        std::fs::write(&program_path, program).unwrap();
        let mut arguments = treatment_flags.iter().map(Path::new).collect::<Vec<_>>();
        arguments.extend([
            Path::new("--timing-summary"),
            summary_path.as_path(),
            program_path.as_path(),
        ]);

        let output = run_egglog(&arguments);
        assert!(
            output.status.success(),
            "egglog failed in {label} mode: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        let summary: serde_json::Value =
            serde_json::from_slice(&std::fs::read(&summary_path).unwrap()).unwrap();

        assert!(summary["commands_check_ns"].as_u64().unwrap() > 0);
        assert!(
            !summary["rulesets"]
                .as_array()
                .unwrap()
                .iter()
                .any(|ruleset| {
                    ruleset["name"]
                        .as_str()
                        .is_some_and(|name| name.contains("check_facts_ruleset"))
                })
        );

        std::fs::remove_dir_all(directory).unwrap();
    }
}

#[test]
fn encoded_equality_rulesets_are_tagged_by_role_not_mixed_with_program_rules() {
    let directory = temporary_directory("equality-role");
    let program_path = directory.join("program.egg");
    let summary_path = directory.join("summary.json");
    std::fs::write(
        &program_path,
        r#"
            (datatype Math (Num i64))
            (let one (Num 1))
            (let two (Num 2))
            (union one two)
            (run 1)
        "#,
    )
    .unwrap();

    let output = run_egglog(&[
        Path::new("--term-encoding"),
        Path::new("--timing-summary"),
        &summary_path,
        &program_path,
    ]);
    assert!(
        output.status.success(),
        "term-encoded egglog failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let summary: serde_json::Value =
        serde_json::from_slice(&std::fs::read(&summary_path).unwrap()).unwrap();
    let maintenance_names = summary["rulesets"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|ruleset| ruleset["role"] == "equality")
        .map(|ruleset| ruleset["name"].as_str().unwrap().to_owned())
        .collect::<std::collections::BTreeSet<_>>();

    assert!(!maintenance_names.is_empty());
    assert!(
        !summary["rulesets"]
            .as_array()
            .unwrap()
            .iter()
            .any(|ruleset| {
                ruleset["role"] == "program"
                    && maintenance_names.contains(ruleset["name"].as_str().unwrap())
            })
    );

    std::fs::remove_dir_all(directory).unwrap();
}

#[test]
fn timing_summary_is_compact_and_works_with_every_report_level() {
    let program = r#"
        (ruleset zeta)
        (ruleset alpha)
        (relation seed (i64))
        (relation middle (i64))
        (rule ((seed x)) ((middle x)) :ruleset zeta)
        (rule ((middle x)) ((seed x)) :ruleset alpha)
        (seed 1)
        (run zeta 1)
        (run alpha 1)
    "#;

    for report_level in ["time-only", "with-plan", "stage-info"] {
        let directory = temporary_directory(report_level);
        let program_path = directory.join("program.egg");
        let summary_path = directory.join("summary.json");
        let report_path = directory.join("report.json");
        std::fs::write(&program_path, program).unwrap();

        let output = run_egglog(&[
            Path::new("--report-level"),
            Path::new(report_level),
            Path::new("--save-report"),
            &report_path,
            Path::new("--timing-summary"),
            &summary_path,
            &program_path,
        ]);
        assert!(
            output.status.success(),
            "egglog failed at report level {report_level}: {}",
            String::from_utf8_lossy(&output.stderr)
        );

        let bytes = std::fs::read(&summary_path).unwrap();
        assert_eq!(bytes.last(), Some(&b'\n'));
        assert!(!bytes[..bytes.len() - 1].contains(&b'\n'));

        let summary: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
        assert_eq!(summary.as_object().unwrap().len(), 10);
        assert_eq!(summary["schema_version"], 4);
        assert_eq!(summary["commands_check_ns"], 0);
        for field in [
            "frontend_parse_ns",
            "frontend_other_ns",
            "frontend_install_ns",
            "typecheck_ns",
            "commands_actions_ns",
            "commands_other_ns",
        ] {
            assert!(
                summary[field].as_u64().unwrap() > 0,
                "expected nonzero {field}"
            );
        }
        let rulesets = summary["rulesets"].as_array().unwrap();
        assert_eq!(rulesets.len(), 2);
        assert_eq!(rulesets[0]["name"], "alpha");
        assert_eq!(rulesets[1]["name"], "zeta");
        for ruleset_name in ["alpha", "zeta"] {
            let timing = ruleset(&summary, ruleset_name);
            assert_eq!(timing["role"], "program");
            for phase in [
                "assembly_ns",
                "search_ns",
                "apply_ns",
                "execution_ns",
                "merge_ns",
            ] {
                assert!(timing[phase].is_u64());
            }
        }
        assert!(summary["native_rebuild_ns"].is_u64());
        let report: serde_json::Value =
            serde_json::from_slice(&std::fs::read(&report_path).unwrap()).unwrap();
        for iteration in report["iterations"].as_array().unwrap() {
            assert!(iteration["name"].is_string());
            assert_eq!(iteration["role"], "program");
            let split = iteration["report"]["rule_set_report"]["pre_merge"]["Split"]
                .as_object()
                .unwrap();
            assert_eq!(split.len(), 3);
            assert_duration(&split["search"]);
            assert_duration(&split["apply"]);
            assert_duration(&split["unattributed"]);
        }

        std::fs::remove_dir_all(directory).unwrap();
    }
}

#[test]
fn parallel_saved_report_uses_combined_pre_merge_shape() {
    let directory = temporary_directory("combined-report");
    let program_path = directory.join("program.egg");
    let report_path = directory.join("report.json");
    let mut program = String::from(
        r#"
        (relation seeds (i64))
        (relation results (i64))
        (rule ((seeds x)) ((results x)))
        "#,
    );
    for value in 0..10_001 {
        program.push_str(&format!("(seeds {value})\n"));
    }
    program.push_str("(run 1)\n");
    std::fs::write(&program_path, program).unwrap();

    let output = run_egglog(&[
        Path::new("--threads"),
        Path::new("2"),
        Path::new("--save-report"),
        &report_path,
        &program_path,
    ]);
    assert!(
        output.status.success(),
        "parallel egglog failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );

    let report: serde_json::Value =
        serde_json::from_slice(&std::fs::read(&report_path).unwrap()).unwrap();
    let iterations = report["iterations"].as_array().unwrap();
    assert!(!iterations.is_empty());
    for iteration in iterations {
        let combined = iteration["report"]["rule_set_report"]["pre_merge"]["Combined"]
            .as_object()
            .unwrap();
        assert_eq!(combined.len(), 1);
        assert_duration(&combined["elapsed"]);
    }

    std::fs::remove_dir_all(directory).unwrap();
}

#[test]
fn failed_program_does_not_write_timing_summary() {
    let directory = temporary_directory("failure");
    let program_path = directory.join("program.egg");
    let summary_path = directory.join("summary.json");
    std::fs::write(&program_path, "(check (= 1 2))").unwrap();

    let output = run_egglog(&[Path::new("--timing-summary"), &summary_path, &program_path]);

    assert!(!output.status.success());
    assert!(!summary_path.exists());

    let previous_contents = b"summary from an earlier successful run\n";
    std::fs::write(&summary_path, previous_contents).unwrap();
    let output = run_egglog(&[Path::new("--timing-summary"), &summary_path, &program_path]);

    assert!(!output.status.success());
    assert_eq!(std::fs::read(&summary_path).unwrap(), previous_contents);
    std::fs::remove_dir_all(directory).unwrap();
}

#[test]
fn stdin_program_writes_timing_summary() {
    let directory = temporary_directory("stdin");
    let summary_path = directory.join("summary.json");
    let mut child = Command::new(env!("CARGO_BIN_EXE_egglog"))
        .arg("--timing-summary")
        .arg(&summary_path)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    child.stdin.take().unwrap().write_all(b"(run 1)\n").unwrap();

    let output = child.wait_with_output().unwrap();

    assert!(
        output.status.success(),
        "egglog failed for stdin input: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let bytes = std::fs::read(&summary_path).unwrap();
    assert_eq!(bytes.last(), Some(&b'\n'));
    let summary: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
    assert_eq!(summary["schema_version"], 4);
    assert!(summary["rulesets"].is_array());
    std::fs::remove_dir_all(directory).unwrap();
}

#[test]
fn timing_summary_has_no_environment_variable_interface() {
    let directory = temporary_directory("environment");
    let program_path = directory.join("program.egg");
    let summary_path = directory.join("summary.json");
    std::fs::write(&program_path, "(run 1)").unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_egglog"))
        .env("EGGLOG_TIMING_SUMMARY", &summary_path)
        .arg(&program_path)
        .output()
        .unwrap();

    assert!(output.status.success());
    assert!(!summary_path.exists());
    std::fs::remove_dir_all(directory).unwrap();
}

#[test]
fn timing_summary_rejects_parallel_execution() {
    let directory = temporary_directory("parallel");
    let program_path = directory.join("program.egg");
    let summary_path = directory.join("summary.json");
    std::fs::write(&program_path, "(run 1)").unwrap();

    let output = run_egglog(&[
        Path::new("--threads"),
        Path::new("2"),
        Path::new("--timing-summary"),
        &summary_path,
        &program_path,
    ]);

    assert!(!output.status.success());
    assert!(
        String::from_utf8_lossy(&output.stderr)
            .contains("--timing-summary requires --threads 1 for accurate phase timing")
    );
    assert!(!summary_path.exists());
    std::fs::remove_dir_all(directory).unwrap();
}
