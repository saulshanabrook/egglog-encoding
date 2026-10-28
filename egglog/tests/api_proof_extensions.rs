use egglog::{CommandOutput, EGraph, Error, UserDefinedCommand, ast::Expr};
use std::sync::Arc;

struct ProveFromExtension(bool);

impl UserDefinedCommand for ProveFromExtension {
    fn supports_term_encoding(&self) -> bool {
        self.0
    }

    fn update(&self, graph: &mut EGraph, _: &[Expr]) -> Result<Vec<CommandOutput>, Error> {
        graph.parse_and_run_program(None, "(prove (= (A) (B)))")
    }
}

#[test]
fn proof_commands_require_explicit_extension_support() -> Result<(), Error> {
    for enabled in [false, true] {
        let mut graph = EGraph::default();
        graph.add_command(
            "extension-proof".into(),
            Arc::new(ProveFromExtension(enabled)),
        )?;
        let mut graph = graph.with_proofs_enabled();
        graph.parse_and_run_program(None, "(datatype U (A) (B)) (A) (rewrite (A) (B)) (run 1)")?;
        let result = graph.parse_and_run_program(None, "(extension-proof)");
        if enabled {
            assert_eq!(
                result?
                    .iter()
                    .filter(|output| matches!(output, CommandOutput::ProveExists { .. }))
                    .count(),
                1
            );
        } else {
            assert!(matches!(result, Err(Error::UnsupportedProofCommand { .. })));
        }
    }
    Ok(())
}

#[test]
fn printed_strings_round_trip_through_proof_instrumentation() -> Result<(), Error> {
    let mut graph = EGraph::new_with_proofs();
    let outputs = graph.parse_and_run_program(
        None,
        r#"
        (datatype U (Text String))
        (Text "a\"b\\c")
        (prove (= (Text "a\"b\\c") (Text "a\"b\\c")))
    "#,
    )?;
    assert_eq!(
        outputs
            .iter()
            .filter(|output| matches!(output, CommandOutput::ProveExists { .. }))
            .count(),
        1
    );
    Ok(())
}
