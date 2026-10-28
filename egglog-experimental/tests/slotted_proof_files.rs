use egglog::CommandOutput;
use egglog_experimental::slotted::{Compiler, Options, ProofMode, new_egraph_with_proofs};
use libtest_mimic::Trial;
use std::path::Path;

fn main() {
    let args = libtest_mimic::Arguments::from_args();
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap();
    // Includes resolve from the invocation directory, as in the CLI.
    std::env::set_current_dir(root).unwrap();
    let mut tests = Vec::new();
    for pattern in [
        "egglog-experimental/tests/slotted/**/*.egg",
        "egglog-experimental/benches/slotted/**/*.egg",
    ] {
        for path in glob::glob(pattern).unwrap() {
            let path = path.unwrap();
            let source = std::fs::read_to_string(&path).unwrap();
            let mut compiler = Compiler::new(Options {
                no_aliasing: path.starts_with("egglog-experimental/tests/slotted/nested"),
                proof_mode: ProofMode::Prove,
            });
            let encoded = compiler.compile(Some(path.display().to_string()), &source);
            // Keep unsupported fixtures visible; all other compilation errors fail.
            let unsupported = encoded.as_ref().is_err_and(|error| {
                error
                    .to_string()
                    .contains("uses subst, which has no proof translation")
            });
            let name = path
                .strip_prefix("egglog-experimental")
                .unwrap()
                .display()
                .to_string();
            tests.push(
                Trial::test(name, move || {
                    let encoded = encoded?;
                    let expected = encoded.matches("(prove-slotted ").count();
                    let outputs = new_egraph_with_proofs().parse_and_run_program(None, &encoded)?;
                    let proofs = outputs
                        .iter()
                        .filter(|output| matches!(output, CommandOutput::UserDefined(_)))
                        .count();
                    assert_eq!(proofs, expected, "every claim must produce a checked proof");
                    Ok(())
                })
                .with_ignored_flag(unsupported),
            );
        }
    }
    assert!(!tests.is_empty(), "no slotted fixtures found");
    libtest_mimic::run(&args, tests).exit();
}
