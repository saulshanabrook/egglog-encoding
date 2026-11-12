//! Shared match queues preserve rule identity, schema, and compiler scopes.
use egglog_experimental::slotted::{Compiler, Options, new_egraph};

fn run(compiler: &mut Compiler, graph: &mut egglog::EGraph, source: &str) -> String {
    let encoded = compiler.compile(None, source).unwrap();
    graph.parse_and_run_program(None, &encoded).unwrap();
    encoded
}

fn queue_count(encoded: &str) -> usize {
    encoded.matches("(relation _slotted_match_queue_").count()
}

#[test]
fn identical_schemas_keep_each_rules_matches_separate() {
    for no_aliasing in [false, true] {
        let mut compiler = Compiler::new(Options {
            no_aliasing,
            ..Default::default()
        });
        let mut graph = new_egraph();
        let encoded = run(
            &mut compiler,
            &mut graph,
            r#"
(datatype E (V Var) (F E) (G E) (FromF E) (FromG E))
(rewrite (F x) (FromF x))
(rewrite (G y) (FromG y))
(let f (F (V $a)))
(let g (G (V $b)))
(run 1)
(check (= f (FromF (V $a))))
(check (= g (FromG (V $b))))
(fail (check (= f (FromG (V $a)))))
(fail (check (= g (FromF (V $b)))))
"#,
        );
        assert_eq!(queue_count(&encoded), 1);
        assert_eq!(graph.get_size("_slotted_match_queue_0"), 0);
    }
}

#[test]
fn payload_and_carrier_sorts_distinguish_queues() {
    let encoded = run(
        &mut Compiler::default(),
        &mut new_egraph(),
        r#"
(datatype E (V Var) (N i64) (Number i64) (Name String) (Text String))
(datatype T (VT Var) (F T) (G T))
(rewrite (N n) (Number n))
(rewrite (Name s) (Text s))
(rewrite (F x) (G x))
(let number (N 42))
(let text (Name "payload"))
(let other (F (VT $a)))
(run 1)
(check (= number (Number 42)))
(check (= text (Text "payload")))
(check (= other (G (VT $a))))
"#,
    );
    assert_eq!(queue_count(&encoded), 3);
}

#[test]
fn queues_survive_incremental_inputs_and_restore_with_scopes() {
    let mut compiler = Compiler::default();
    let mut graph = new_egraph();
    run(
        &mut compiler,
        &mut graph,
        r#"
(datatype E (V Var) (F E) (G E) (H E) (N i64) (Number i64) (Name String) (Text String))
(rewrite (F x) (G x))
"#,
    );
    let scoped = run(
        &mut compiler,
        &mut graph,
        r#"
(push)
(rewrite (G x) (H x))
(rewrite (N n) (Number n))
(let local (F (V $a)))
(run 2)
(check (= local (H (V $a))))
(pop)
"#,
    );
    assert_eq!(queue_count(&scoped), 1, "the carrier-only queue is reused");
    let later = run(
        &mut compiler,
        &mut graph,
        r#"
(rewrite (Name s) (Text s))
(let later (F (V $b)))
(let text (Name "after pop"))
(run 2)
(check (= later (G (V $b))))
(check (= text (Text "after pop")))
(fail (check (= later (H (V $b)))))
"#,
    );
    assert_eq!(queue_count(&later), 1, "the popped schema is declared anew");
}
