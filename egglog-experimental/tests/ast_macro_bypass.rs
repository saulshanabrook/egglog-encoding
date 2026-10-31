use egglog::ast::Command;
use egglog::util::SymbolGen;
use egglog::{CommandMacro, Error, TypeInfo};
use egglog_experimental::{DisequalityEncoding, new_experimental_egraph_with_options};
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

struct IdentityCounter(Arc<AtomicUsize>);

impl CommandMacro for IdentityCounter {
    fn preserves_closed_constructor_action(&self, _: Option<&str>) -> bool {
        true
    }

    fn transform(
        &self,
        command: Command,
        _: &mut SymbolGen,
        _: &TypeInfo,
    ) -> Result<Vec<Command>, Error> {
        self.0.fetch_add(1, Ordering::SeqCst);
        Ok(vec![command])
    }
}

#[test]
fn registered_experimental_macros_skip_closed_ast_actions() {
    // Match the CLI's native off/NEE factory, including every real macro.
    let mut graph = new_experimental_egraph_with_options(true, DisequalityEncoding::Nee);
    let calls = Arc::new(AtomicUsize::new(0));
    graph
        .command_macros_mut()
        .register(Arc::new(IdentityCounter(calls.clone())));
    graph
        .parse_and_run_program(None, "(datatype T (A) (B) (F T))")
        .unwrap();
    calls.store(0, Ordering::SeqCst);

    graph
        .parse_and_run_program(None, "(F (A)) (union (A) (B)) (F (B))")
        .unwrap();
    assert_eq!(calls.load(Ordering::SeqCst), 0);
    assert_eq!(graph.get_size("F"), 1);
    // Check commands deliberately use normal macro dispatch after the zero-call
    // assertion; they verify the union and congruence rather than fresh IDs.
    graph
        .parse_and_run_program(None, "(check (= (A) (B))) (check (= (F (A)) (F (B))))")
        .unwrap();
}
