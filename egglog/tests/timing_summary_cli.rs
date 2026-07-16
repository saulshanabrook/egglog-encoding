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
        assert_eq!(summary.as_object().unwrap().len(), 2);
        assert_eq!(summary["schema_version"], 2);
        let rulesets = summary["rulesets"].as_array().unwrap();
        assert_eq!(
            rulesets
                .iter()
                .map(|ruleset| ruleset["name"].as_str().unwrap())
                .collect::<Vec<_>>(),
            ["alpha", "zeta"]
        );
        for ruleset in rulesets {
            assert_eq!(ruleset.as_object().unwrap().len(), 6);
            assert!(ruleset["search_ns"].is_u64());
            assert!(ruleset["apply_ns"].is_u64());
            assert!(ruleset["unattributed_ns"].is_u64());
            assert!(ruleset["merge_ns"].is_u64());
            assert!(ruleset["rebuild_ns"].is_u64());
        }
        assert!(
            serde_json::from_slice::<serde_json::Value>(&std::fs::read(&report_path).unwrap())
                .is_ok()
        );

        std::fs::remove_dir_all(directory).unwrap();
    }
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
    assert_eq!(summary["schema_version"], 2);
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
