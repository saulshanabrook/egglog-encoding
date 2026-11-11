use egglog::{CommandOutput, Error};
use egglog_experimental::slotted::{
    Compiler, Options, ProofMode, new_egraph, new_egraph_with_proofs,
};
use libtest_mimic::Trial;
use std::path::Path;

#[path = "support/proof_coverage.rs"]
mod coverage;

/// Recover positive probe equalities from the ordinary execution, then require
/// an independently checked source proof for each probe, including reflexivity.
fn probe_claims(source: &str, probes: &[String], no_aliasing: bool) -> Result<String, Error> {
    let mut compiler = Compiler::new(Options {
        no_aliasing,
        ..Default::default()
    });
    let mut graph = new_egraph();
    compiler.compile_program(None, source)?.run(&mut graph)?;
    let mut representatives: Vec<&str> = Vec::new();
    let mut claims = String::new();
    for probe in probes {
        let mut representative = probe.as_str();
        for &other in &representatives {
            let query = format!("(check (renaming-= {other} {probe}))");
            match compiler.compile_program(None, &query)?.run(&mut graph) {
                Ok(_) => {
                    representative = other;
                    break;
                }
                Err(Error::CheckError(..)) => {}
                Err(error) => return Err(error),
            }
        }
        if representative == probe {
            representatives.push(probe);
        }
        claims.push_str(&format!("(check (renaming-= {representative} {probe}))\n"));
    }
    Ok(claims)
}

#[derive(serde::Deserialize)]
struct Probes {
    probes: Vec<String>,
}

#[derive(serde::Deserialize)]
struct Ignore {
    file: String,
    treatments: Vec<String>,
    reason: String,
}

fn main() {
    let args = libtest_mimic::Arguments::from_args();
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap();
    // Includes resolve from the invocation directory, as in the CLI.
    std::env::set_current_dir(root).unwrap();
    let ignores: Vec<Ignore> =
        serde_json::from_str(include_str!("../../benchmarks/ignore.json")).unwrap();
    let mut tests = Vec::new();
    for pattern in [
        "egglog-experimental/tests/slotted/**/*.egg",
        "egglog-experimental/benches/slotted/**/*.egg",
        "benchmarks/slotted/inputs/**/*.egg",
        "benchmarks/slotted/correctness/**/*.egg",
    ] {
        for path in glob::glob(pattern).unwrap() {
            let path = path.unwrap();
            let ignored = ignores.iter().find(|rule| {
                rule.treatments.iter().any(|t| t == "slotted-proof-testing")
                    && glob::Pattern::new(&format!("benchmarks/{}", rule.file))
                        .unwrap()
                        .matches_path(&path)
            });
            if let Some(rule) = ignored {
                eprintln!("Deferred source proof {}: {}", path.display(), rule.reason);
            }
            let source = std::fs::read_to_string(&path).unwrap();
            let no_aliasing = path.starts_with("egglog-experimental/tests/slotted/nested")
                || path.starts_with("benchmarks/slotted/correctness/nested");
            let mut compiler = Compiler::new(Options {
                no_aliasing,
                proof_mode: ProofMode::Prove,
            });
            let encoded = compiler.compile_program(Some(path.display().to_string()), &source);
            let name = path
                .strip_prefix("egglog-experimental")
                .unwrap_or(&path)
                .display()
                .to_string();
            let test = Trial::test(format!("proofs/slotted/{name}"), move || {
                // Match the CLI's stack allowance for the larger frozen proof DAGs.
                stacker::grow(8 * 1024 * 1024, || {
                    let encoded = encoded?;
                    let mut expected =
                        coverage::expected_proofs(&source).map_err(|e| e.to_string())?;
                    let mut graph = new_egraph_with_proofs();
                    let mut outputs = encoded.run(&mut graph)?;
                    if path.starts_with("benchmarks/slotted/correctness") {
                        let probes: Probes = serde_json::from_str(&std::fs::read_to_string(
                            path.with_extension("ref"),
                        )?)?;
                        let claims = probe_claims(&source, &probes.probes, no_aliasing)?;
                        expected += probes.probes.len();
                        outputs.extend(compiler.compile_program(None, &claims)?.run(&mut graph)?);
                    }
                    let proofs = outputs
                        .iter()
                        .filter(|output| matches!(output, CommandOutput::UserDefined(_)))
                        .count();
                    assert_eq!(proofs, expected, "every claim must produce a checked proof");
                    Ok(())
                })
            });
            tests.push(test.with_ignored_flag(ignored.is_some()));
        }
    }
    assert!(!tests.is_empty(), "no slotted fixtures found");
    libtest_mimic::run(&args, tests).exit();
}
