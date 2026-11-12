//! Whole-program S-expression sizes for independently compiled configurations.
//!
//! This helper resolves one input/configuration per process. It never evaluates
//! user commands, schedules, checks, extracts, or proofs. Compiler initialization
//! and the metadata/push/pop handling required by `resolve_program` still occur.
//! Every emitted command, including fixed and schema-dependent support, counts.
//!
//! `cp`/`dcp` use the public proof-testing configuration to obtain the same
//! check/extract instrumentation as the CLI's `--proof-extraction --mode desugar`.
//! That CLI's private verification switch only affects execution, which is absent
//! here. `scp` preserves the established Slotted `ProofMode::Prove` profile before
//! resolving its serialized commands through the combined core instrumentation.
//! These are configuration endpoints, not consecutive C and P intermediates.

use egglog::ast::{Sexp, parse_sexps};
use egglog_experimental::slotted::{Compiler, Options, ProofMode};
use serde::Serialize;
use std::ffi::OsString;
use std::path::PathBuf;

#[global_allocator]
static ALLOCATOR: benchmark_memory::LimitedAllocator = benchmark_memory::LimitedAllocator;

type CompileResult<T> = Result<T, (&'static str, String)>;

struct Arguments {
    profile: String,
    complete_slotted: bool,
    file: PathBuf,
}

#[derive(Serialize)]
struct Record {
    version: u8,
    status: &'static str,
    file: PathBuf,
    profile: String,
    no_aliasing: Option<bool>,
    count_convention: &'static str,
    source_normalization: &'static str,
    source_ast_nodes: Option<usize>,
    normalized_source_ast_nodes: Option<usize>,
    include_files: Vec<PathBuf>,
    output_ast_nodes: Option<usize>,
    error: Option<String>,
    error_stage: Option<&'static str>,
}

fn arguments(args: impl IntoIterator<Item = OsString>) -> Result<Arguments, String> {
    let mut args = args.into_iter().skip(1);
    let mut profile = None;
    let mut complete_slotted = false;
    let mut file = None;
    let mut positional = false;
    while let Some(arg) = args.next() {
        match arg.to_str() {
            Some("--") if !positional => positional = true,
            Some("--profile") if !positional => {
                if profile.is_some() {
                    return Err("--profile may only be specified once".into());
                }
                let value = args
                    .next()
                    .and_then(|arg| arg.into_string().ok())
                    .ok_or("--profile requires off, c, cp, d, dcp, s, or scp")?;
                if !matches!(
                    value.as_str(),
                    "off" | "c" | "cp" | "d" | "dcp" | "s" | "scp"
                ) {
                    return Err(format!("unknown profile {value}"));
                }
                profile = Some(value);
            }
            Some("--complete-slotted") if !positional => {
                if complete_slotted {
                    return Err("--complete-slotted may only be specified once".into());
                }
                complete_slotted = true;
            }
            Some(option) if !positional && option.starts_with('-') => {
                return Err(format!("unknown option {option}"));
            }
            _ => {
                if file.replace(PathBuf::from(arg)).is_some() {
                    return Err("exactly one input file is required".into());
                }
            }
        }
    }
    let profile = profile.ok_or("--profile is required")?;
    if complete_slotted && !matches!(profile.as_str(), "s" | "scp") {
        return Err("--complete-slotted requires profile s or scp".into());
    }
    Ok(Arguments {
        profile,
        complete_slotted,
        file: file.ok_or("an input file is required")?,
    })
}

fn nodes(source: &str) -> Result<usize, egglog::ast::ParseError> {
    let forms = parse_sexps(None, source)?;
    let mut pending: Vec<_> = forms.iter().collect();
    let mut count = 0;
    while let Some(form) = pending.pop() {
        count += 1;
        if let Sexp::List(items, _) = form {
            pending.extend(items);
        }
    }
    Ok(count)
}

/// Frozen benchmark sources already contain their entire library and facts.
/// Reject external commands before resolution: proof/term instrumentation reads
/// input data into fiat actions even in desugar mode.
fn validate_source(source: &str) -> CompileResult<()> {
    let forms = parse_sexps(None, source).map_err(|error| ("source-parse", error.to_string()))?;
    let mut pending: Vec<_> = forms.iter().collect();
    while let Some(form) = pending.pop() {
        if let Sexp::List(items, _) = form {
            if let Some(Sexp::Atom(head, _)) = items.first()
                && matches!(head.as_ref(), "input" | "include")
            {
                return Err((
                    "external-input",
                    format!("{head} commands require a self-contained, already inlined source"),
                ));
            }
            pending.extend(items);
        }
    }
    Ok(())
}

fn compile(profile: &str, no_aliasing: bool, filename: &str, source: &str) -> CompileResult<usize> {
    let filename = Some(filename.to_owned());
    if profile == "s" {
        let program = Compiler::new(Options {
            no_aliasing,
            proof_mode: ProofMode::Disabled,
        })
        .compile(filename, source)
        .map_err(|error| ("source-slotted", error.to_string()))?;
        return nodes(&program).map_err(|error| ("output-parse", error.to_string()));
    }
    let commands = if profile == "scp" {
        let program = Compiler::new(Options {
            no_aliasing,
            proof_mode: ProofMode::Prove,
        })
        .compile_program(filename.clone(), source)
        .map_err(|error| ("source-slotted-proofs", error.to_string()))?;
        egglog_experimental::slotted::new_egraph_with_proofs()
            .resolve_program(filename, &program.to_string())
            .map_err(|error| ("core-proof-congruence", error.to_string()))?
    } else {
        // The ordinary compiler control uses core schedules consistently with
        // the encoded configurations. Timed runtime `off` uses extended schedules.
        let graph = egglog_experimental::new_experimental_egraph_for_proofs();
        let mut graph = match profile {
            "c" => graph.with_term_encoding_enabled(),
            "cp" | "dcp" => graph.with_proofs_enabled().with_proof_testing(),
            "off" | "d" => graph,
            _ => unreachable!("arguments validate the profile"),
        };
        graph
            .resolve_program(filename, source)
            .map_err(|error| ("core-resolution", error.to_string()))?
    };
    // Avoid joining an entire large generated program or writing it to stdout.
    commands.into_iter().try_fold(0, |count, command| {
        nodes(&command.to_string())
            .map(|nodes| count + nodes)
            .map_err(|error| ("output-parse", error.to_string()))
    })
}

fn collect(args: Arguments) -> Record {
    let mut record = Record {
        version: 1,
        status: "error",
        file: args.file,
        no_aliasing: matches!(args.profile.as_str(), "s" | "scp").then_some(!args.complete_slotted),
        profile: args.profile,
        count_convention: "sexp-list-atom-literal-v1",
        source_normalization: "self-contained-source-v1",
        source_ast_nodes: None,
        normalized_source_ast_nodes: None,
        include_files: Vec::new(),
        output_ast_nodes: None,
        error: None,
        error_stage: None,
    };
    let result = (|| {
        let source = std::fs::read_to_string(&record.file)
            .map_err(|error| ("source-read", error.to_string()))?;
        record.source_ast_nodes =
            Some(nodes(&source).map_err(|error| ("source-parse", error.to_string()))?);
        validate_source(&source)?;
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            compile(
                &record.profile,
                !args.complete_slotted,
                &record.file.to_string_lossy(),
                &source,
            )
        }))
        .unwrap_or_else(|panic| {
            let message = panic
                .downcast_ref::<String>()
                .cloned()
                .or_else(|| {
                    panic
                        .downcast_ref::<&str>()
                        .map(|message| (*message).into())
                })
                .unwrap_or_else(|| "compiler panicked without a string payload".into());
            Err(("compiler-panic", message))
        })
    })();
    match result {
        Ok(count) => {
            record.status = "ok";
            record.output_ast_nodes = Some(count);
        }
        Err((stage, error)) => {
            record.error_stage = Some(stage);
            record.error = Some(error);
        }
    }
    record
}

fn main() {
    let args = benchmark_memory::configure(std::env::args_os());
    match arguments(args) {
        Ok(args) => println!("{}", serde_json::to_string(&collect(args)).unwrap()),
        Err(error) => {
            println!(
                "{}",
                serde_json::json!({"version": 1, "status": "error", "error_stage": "arguments", "error": error})
            );
            std::process::exit(2);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn core_profiles_do_not_execute_user_commands_or_read_external_facts() {
        let source = r#"
            (datatype T (A) (B))
            (let value (A))
            (run 1)
            (extract value)
            (check (= value (B)))
            (panic "user program must never execute")
        "#;
        for profile in ["off", "c", "cp", "d", "dcp"] {
            assert!(compile(profile, true, "compile-only.egg", source).unwrap() > 0);
        }
        let result = validate_source("(fail (input nonexistent \"must-not-read.facts\"))");
        assert_eq!(result.unwrap_err().0, "external-input");
    }

    #[test]
    fn slotted_profiles_compile_a_false_ground_claim_without_evaluating_it() {
        let source = r#"
            (datatype U (V Var) (F U))
            (let value (F (V $a)))
            (rewrite (F x) x)
            (run 1)
            (check (= value (V $b)))
        "#;
        for no_aliasing in [true, false] {
            for profile in ["s", "scp"] {
                assert!(compile(profile, no_aliasing, "compile-only.egg", source).unwrap() > 0);
            }
        }
    }

    #[test]
    fn external_command_validation_uses_forms_instead_of_text_matching() {
        for source in [
            "(include \"must-not-read.egg\")",
            "(fail (include \"must-not-read.egg\"))",
            "(input nonexistent \"must-not-read.facts\")",
        ] {
            assert_eq!(validate_source(source).unwrap_err().0, "external-input");
        }
        validate_source("; (include \"comment.egg\")\n(panic \"(input string)\")").unwrap();
    }
}
