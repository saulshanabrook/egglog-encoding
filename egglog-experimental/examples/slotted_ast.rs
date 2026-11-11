//! Compile-only sizes of the SDQL source and its composed encodings.
use egglog::ast::{Sexp, parse_sexps};
use egglog_experimental::slotted::{CompileError, Compiler, Options, ProofMode};
use std::path::Path;

fn nodes(source: &str) -> Result<usize, Box<dyn std::error::Error>> {
    fn count(form: &Sexp<'_>) -> usize {
        match form {
            Sexp::List(items, _) => 1 + items.iter().map(count).sum::<usize>(),
            _ => 1,
        }
    }
    Ok(parse_sexps(None, source)?.iter().map(count).sum())
}

#[derive(Debug, thiserror::Error)]
enum ProofCompilationError {
    #[error(transparent)]
    Source(#[from] CompileError),
    #[error(transparent)]
    Core(#[from] egglog::Error),
}

/// Follow the source proof profile before composing with the core encoding.
fn proof_program(filename: Option<String>, source: &str) -> Result<String, ProofCompilationError> {
    let compiled = Compiler::new(Options {
        no_aliasing: true,
        proof_mode: ProofMode::Prove,
    })
    .compile_program(filename.clone(), source)?;
    let mut graph = egglog_experimental::slotted::new_egraph_with_proofs();
    Ok(graph
        .resolve_program(filename, &compiled.to_string())?
        .into_iter()
        .map(|command| command.to_string())
        .collect::<Vec<_>>()
        .join("\n"))
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    for filename in std::env::args().skip(1) {
        let source = std::fs::read_to_string(&filename)?;
        let lowered = Compiler::new(Options {
            no_aliasing: true,
            proof_mode: ProofMode::Disabled,
        })
        .compile(Some(filename.clone()), &source)?;
        let proof = proof_program(Some(filename.clone()), &source);
        let (proof_nodes, proof_program, unsupported, unsupported_type, unsupported_stage) =
            match proof {
                Ok(program) => (Some(nodes(&program)?), Some(program), None, None, None),
                Err(error) => {
                    let stage = match &error {
                        ProofCompilationError::Source(_) => "source-slotted-proofs",
                        ProofCompilationError::Core(_) => "core-proof-congruence",
                    };
                    (
                        None,
                        None,
                        Some(error.to_string()),
                        Some(format!("{error:?}")),
                        Some(stage),
                    )
                }
            };
        let proof_compatible = Compiler::new(Options {
            no_aliasing: true,
            proof_mode: ProofMode::Check,
        })
        .compile(Some(filename.clone()), &source)?;
        let mut congruence =
            egglog_experimental::slotted::new_egraph().with_term_encoding_enabled();
        let congruence = congruence.resolve_program(Some(filename.clone()), &proof_compatible);
        let congruence_error = congruence.as_ref().err().map(ToString::to_string);
        let congruence_program = congruence.ok().map(|commands| {
            commands
                .into_iter()
                .map(|command| command.to_string())
                .collect::<Vec<_>>()
                .join("\n")
        });
        let congruence_nodes = congruence_program.as_deref().map(nodes).transpose()?;
        println!(
            "{}",
            serde_json::json!({
                "file": filename,
                "compiler_binary": std::env::current_exe()?,
                "programs": {"source": source, "slotted": lowered, "proof_compatible_slotted": proof_compatible, "proof_congruence": proof_program, "congruence": congruence_program},
                "benchmark": Path::new(&filename).file_stem().unwrap().to_str().unwrap(),
                "source_ast_nodes": nodes(&source)?,
                "slotted_ast_nodes": nodes(&lowered)?,
                "proof_congruence_ast_nodes": proof_nodes,
                "proof_congruence_error": unsupported,
                "proof_congruence_error_debug": unsupported_type,
                "proof_congruence_error_stage": unsupported_stage,
                "congruence_ast_nodes": congruence_nodes,
                "congruence_error": congruence_error,
                "proof_compatible_slotted_ast_nodes": nodes(&proof_compatible)?,
            })
        );
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn supported_source_profile_lowers_through_core_proofs() {
        let source = r#"
            (datatype U (V Var) (F U))
            (let input (F (V $a)))
            (rewrite (F x) x :name "unwrap")
            (run 1)
            (check (= input (V $a)))
        "#;
        let lowered = proof_program(None, source).unwrap();
        let ordinary = Compiler::new(Options {
            no_aliasing: true,
            proof_mode: ProofMode::Disabled,
        })
        .compile(None, source)
        .unwrap();
        assert!(nodes(&lowered).unwrap() > nodes(&ordinary).unwrap());
        assert!(nodes(&ordinary).unwrap() > nodes(source).unwrap());
    }

    #[test]
    fn source_substitution_lowers_through_core_proofs() {
        let source = r#"
            (datatype U (V Var) (Lam Var U :binder 0) (Let U Var U :binder 1))
            (let input (Let (V $y) $x (Lam $y (V $x))))
            (rewrite (Let value $x body) (subst body $x value) :name "beta")
            (run 1)
            (check (= input (Lam $z (V $y))))
        "#;
        let lowered = proof_program(None, source).unwrap();
        assert!(nodes(&lowered).unwrap() > nodes(source).unwrap());
        assert!(lowered.contains("slotted-substitute"));
        assert!(lowered.contains("slotted-prove"));
    }

    #[test]
    fn counts_forms_and_tokens_without_counting_comments_or_string_contents() {
        assert_eq!(
            nodes("; ignored (words)\n(rule () ((f \"a (b)\")))").unwrap(),
            7
        );
    }
}
