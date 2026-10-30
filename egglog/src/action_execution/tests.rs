use super::*;

#[test]
fn execution_scope_commits_pending_prefix_on_success_and_error() {
    for fails in [false, true] {
        let mut graph = EGraph::default();
        graph
            .parse_and_run_program(None, "(datatype T (A) (F T))")
            .unwrap();
        let command = graph.parse_program(None, "(F (A))").unwrap().remove(0);
        let commands = graph.resolve_command(command).unwrap().desugared;
        let result = ActionExecutor::run(&mut graph, |execution| {
            for command in commands {
                execution.command(command)?;
            }
            assert_eq!(execution.graph.get_size("F"), 0);
            if fails {
                Err(Error::BackendError("expected scope error".into()))
            } else {
                Ok(())
            }
        });
        assert_eq!(result.is_err(), fails);
        assert_eq!(graph.get_size("F"), 1);
    }
}

type BatchEvent = (usize, Vec<Rc<egglog_bridge::TableAction>>);
type OrderLog = Arc<std::sync::Mutex<Vec<&'static str>>>;

std::thread_local! {
    pub(super) static BATCH_EVENTS: std::cell::RefCell<Option<Vec<BatchEvent>>> = const { std::cell::RefCell::new(None) };
    pub(super) static ORDER_LOG: std::cell::RefCell<Option<OrderLog>> = const { std::cell::RefCell::new(None) };
}

thread_local! {
    pub(super) static GROUND_ACTIONS_EXECUTED: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[test]
fn resolved_dispatch_uses_native_actions_and_falls_back_for_primitives() {
    let mut graph = EGraph::default();
    graph
        .parse_and_run_program(None, "(datatype T (A) (B) (F T) (Num i64))")
        .unwrap();
    for (source, native_actions) in [
        ("(F (A))", 1),
        ("(union (A) (B))", 1),
        ("(Num (+ 1 2))", 0),
        ("(begin (F (B)))", 0),
        ("(begin (let local (A)) (F local))", 0),
    ] {
        let before = GROUND_ACTIONS_EXECUTED.get();
        for command in graph.parse_program(None, source).unwrap() {
            let resolved = graph.resolve_command(command).unwrap();
            assert_eq!(resolved.desugared.len(), 1, "{source}");
            for command in resolved.desugared {
                graph.run_command(command).unwrap();
            }
        }
        assert_eq!(
            GROUND_ACTIONS_EXECUTED.get() - before,
            native_actions,
            "{source}"
        );
    }
    assert_eq!(graph.get_size("F"), 1);
    assert_eq!(graph.get_size("Num"), 1);
    graph
        .parse_and_run_program(
            None,
            "(check (= (A) (B))) (check (= (Num 3) (Num (+ 1 2))))",
        )
        .unwrap();
}

#[test]
fn resolved_dispatch_preserves_proof_and_term_execution() {
    for (mut graph, proofs) in [
        (EGraph::new_with_term_encoding(), false),
        (EGraph::new_with_proofs().with_proof_testing(), true),
    ] {
        assert!(graph.proof_state.original_typechecking.is_some());
        assert_eq!(graph.are_proofs_enabled(), proofs);
        let before = GROUND_ACTIONS_EXECUTED.get();
        graph
            .parse_and_run_program(
                None,
                "(datatype T (A) (B) (F T))
                 (F (A)) (union (A) (B))
                 (check (= (F (A)) (F (B))))",
            )
            .unwrap();
        assert_eq!(GROUND_ACTIONS_EXECUTED.get(), before);
    }
}

// Compare prepared actions with the existing resolved-command compiler.
fn run_ground_action_oracle(
    graph: &mut EGraph,
    source: &str,
    direct: bool,
) -> Result<Vec<String>, Error> {
    if direct {
        return graph
            .parse_and_run_program(None, source)
            .map(|outputs| outputs.iter().map(ToString::to_string).collect());
    }
    let mut outputs = Vec::new();
    for command in graph.parse_program(None, source)? {
        for command in graph.resolve_command(command)?.desugared {
            // Bypass resolved dispatch so the oracle always uses the compiler.
            let result = match command {
                ResolvedNCommand::CoreAction(action) => {
                    graph.eval_actions(&ResolvedActions::new(vec![action]))?;
                    Vec::new()
                }
                ResolvedNCommand::CoreActions(actions) => {
                    graph.eval_actions(&actions)?;
                    Vec::new()
                }
                command => graph.run_command(command)?,
            };
            outputs.extend(result.iter().map(ToString::to_string));
        }
    }
    Ok(outputs)
}

fn assert_action_graphs_equal(left: &EGraph, right: &EGraph) {
    assert_eq!(
        left.functions.keys().collect::<Vec<_>>(),
        right.functions.keys().collect::<Vec<_>>()
    );
    for (name, function) in &left.functions {
        let mut left_rows = Vec::new();
        left.backend.for_each(function.backend_id, |row| {
            left_rows.push((row.vals.to_vec(), row.subsumed))
        });
        let mut right_rows = Vec::new();
        right
            .backend
            .for_each(right.functions[name].backend_id, |row| {
                right_rows.push((row.vals.to_vec(), row.subsumed))
            });
        left_rows.sort();
        right_rows.sort();
        assert_eq!(left_rows, right_rows, "{name}");
    }
}

#[test]
fn ground_actions_match_compiled_execution() {
    for threads in [1, 4] {
        let mut direct = EGraph::default();
        let mut compiled = EGraph::default();
        for graph in [&mut direct, &mut compiled] {
            graph.backend.set_num_threads(threads);
            graph
                .parse_and_run_program(
                    None,
                    "(datatype T (A) (B) (N1) (N2) (Pair T T) (Num i64))
                     (relation seen (T))
                     (function missing (T) T :no-merge)
                     (function tuple-result (T) (T T) :merge (values old0 old1))
                     (index Occ missing (any 0 1))
                     (let $global (A))",
                )
                .unwrap();
        }
        for (source, succeeds, native_actions) in [
            ("(Pair (N1) (Pair (N1) (N2)))", true, 1),
            ("(Pair (Pair (N1) (N2)) (Pair (N1) (N2)))", true, 1),
            ("(seen (Pair (A) (A)))", true, 1),
            ("(union (A) (A))", true, 1),
            ("(Pair (B) (B))", true, 1),
            ("(union (A) (B))", true, 1),
            ("(union (A) (B))", true, 1),
            ("(union (Pair (N1) (N2)) (Pair (N2) (N1)))", true, 1),
            ("(check (= (Pair (N1) (N2)) (Pair (N2) (N1))))", true, 0),
            ("(check (= (Pair (A) (A)) (Pair (B) (B))))", true, 0),
            ("(push)", true, 0),
            ("(constructor Temporary () T) (Temporary)", true, 1),
            ("(pop)", true, 0),
            ("(Temporary)", false, 0),
            ("(Num (+ 1 2))", true, 0),
            ("(Pair $global (N1))", true, 0),
            ("(begin (Pair (N2) (N2)))", true, 0),
            ("(begin (let local (N2)) (Pair local local))", true, 0),
            ("(fail (missing (Pair (N2) (B))))", true, 0),
            ("(missing (Pair (N2) (A)))", false, 0),
            ("(set (missing (N1)) (N2))", true, 0),
            ("(delete (missing (N1)))", true, 0),
            ("(tuple-result (A))", false, 0),
            ("(Occ (A) (A) (B))", false, 0),
            ("(Pair (A) unbound)", false, 0),
            ("(Pair (A))", false, 0),
        ] {
            let before_direct = GROUND_ACTIONS_EXECUTED.get();
            let actual = run_ground_action_oracle(&mut direct, source, true);
            assert_eq!(
                GROUND_ACTIONS_EXECUTED.get() - before_direct,
                native_actions,
                "{source}",
            );
            let before_oracle = GROUND_ACTIONS_EXECUTED.get();
            let expected = run_ground_action_oracle(&mut compiled, source, false);
            assert_eq!(GROUND_ACTIONS_EXECUTED.get(), before_oracle, "{source}");
            assert_eq!(actual.is_ok(), succeeds, "{source}: {actual:?}");
            assert_eq!(expected.is_ok(), succeeds, "{source}: {expected:?}");
            if let (Ok(actual), Ok(expected)) = (actual, expected) {
                assert_eq!(actual, expected, "{source}");
            }
            assert_action_graphs_equal(&direct, &compiled);
        }
    }
}

#[test]
fn ground_actions_check_eligibility_before_mutation() {
    for mode in 0..3 {
        let mut graph = match mode {
            0 => EGraph::default(),
            1 => EGraph::new_with_term_encoding(),
            _ => EGraph::new_with_proofs(),
        };
        graph
            .parse_and_run_program(
                None,
                "(datatype T (A) (N1) (N2) (Pair T T) (Num i64))
                     (let $global (A))",
            )
            .unwrap();
        if mode == 0 {
            graph
                .parse_and_run_program(
                    None,
                    "(function custom (T) T :no-merge)
                     (index Occ custom (any 0 1))",
                )
                .unwrap();
        }
        for (source, admitted) in [
            ("(Pair (N1) (N2))", true),
            ("(Pair (N1) (missing))", false),
            ("(union (N1) (+ 1 2))", false),
            ("(union (A) (Pair (A) (A)))", true),
            ("(Num 1)", false),
            ("(+ 1 2)", false),
            ("(custom (A))", false),
            ("(Pair $global (A))", false),
            ("(set (custom (A)) (N1))", false),
            ("(delete (custom (A)))", false),
            ("(begin (A))", false),
        ] {
            if mode != 0 && !admitted {
                continue;
            }
            let before = graph.clone();
            let commands = graph.parse_program(None, source).unwrap();
            let accepted = commands.into_iter().any(|command| {
                graph.resolve_command(command).is_ok_and(|commands| {
                    commands.desugared.iter().any(|command| match command {
                        ResolvedNCommand::CoreAction(action) => graph
                            .prepare_resolved_ground_action(
                                action,
                                &mut GroundActionCache::default(),
                            )
                            .is_some(),
                        _ => false,
                    })
                })
            });
            assert_eq!(accepted, admitted && mode == 0, "mode {mode}: {source}");
            assert_action_graphs_equal(&graph, &before);
            assert!(!graph.backend.flush_updates());
        }
    }
}

#[test]
fn ground_actions_keep_numeric_constructor_names_distinct() {
    let source = "(datatype T (A) (A1))
                      (begin (A) (A) (A) (A) (A))
                      (union (A) (A1))
                      (check (= (A) (A1)))";
    for direct in [true, false] {
        run_ground_action_oracle(&mut EGraph::default(), source, direct).unwrap();
    }
}

#[test]
fn insertion_batches_ignore_unrelated_globals_and_containers() {
    let mut graph = EGraph::default();
    graph
        .parse_and_run_program(
            None,
            "(datatype T (A) (B) (F T))
            (sort Unused (Vec T)) (let $unrelated 7)",
        )
        .unwrap();
    let actions = graph.parse_program(None, "(F (A)) (F (B))").unwrap();
    assert!(actions.iter().all(|command| {
        match command {
            Command::Action(action) => graph
                .type_info
                .typecheck_closed_constructor_action(action)
                .is_some(),
            _ => false,
        }
    }));
    graph
        .parse_and_run_program(None, "(F (A)) (F (B))")
        .unwrap();
    assert_eq!(graph.get_size("F"), 2);
    graph
        .parse_and_run_program(
            None,
            "(check (= $unrelated 7))
            (check (= (F (A)) (F (A))))",
        )
        .unwrap();
}

#[test]
fn populated_containers_keep_insertion_admission_and_rebuild_after_union() {
    for threads in [1, 4] {
        for direct in [false, true] {
            let mut graph = EGraph::default();
            graph.backend.set_num_threads(threads);
            graph
                .parse_and_run_program(
                    None,
                    "(datatype T (A) (B) (F T))
                     (sort TVec (Vec T))
                     (function observed (TVec) i64 :no-merge)
                     (let $left (vec-of (A)))
                     (let $right (vec-of (B)))
                     (set (observed $left) 7)",
                )
                .unwrap();
            let commands = graph
                .parse_program(None, "(F (A)) (F (B)) (union (A) (B))")
                .unwrap();
            assert!(commands.iter().all(|command| {
                match command {
                    Command::Action(action) => graph
                        .type_info
                        .typecheck_closed_constructor_action(action)
                        .is_some(),
                    _ => false,
                }
            }));
            assert_eq!(graph.get_size("F"), 0);
            run_ground_action_oracle(
                &mut graph,
                "(F (A)) (F (B)) (union (A) (B))
                 (check (= $left $right))
                 (check (= (observed $right) 7))",
                direct,
            )
            .unwrap();
            assert_eq!(graph.get_size("F"), 1);
        }
    }
}

#[test]
fn pending_insertions_commit_before_fail_child_reads() {
    use std::sync::atomic::{AtomicUsize, Ordering};

    #[derive(Clone)]
    struct ReadSize(Arc<AtomicUsize>);
    impl Primitive for ReadSize {
        fn name(&self) -> &str {
            "read-f-size"
        }
        fn get_type_constraints(&self, span: &Span) -> Box<dyn TypeConstraint> {
            SimpleTypeConstraint::new(self.name(), vec![I64Sort.to_arcsort()], span.clone())
                .into_box()
        }
    }
    impl ReadPrim for ReadSize {
        fn apply<'a, 'db>(&self, state: ReadState<'a, 'db>, _: &[Value]) -> Option<Value> {
            let size = state.table_size("F")?;
            self.0.store(size, Ordering::SeqCst);
            Some(state.base_values().get(size as i64))
        }
    }
    let observed = Arc::new(AtomicUsize::new(usize::MAX));
    let mut graph = EGraph::default();
    graph.add_read_primitive(ReadSize(observed.clone()), None);
    graph
        .parse_and_run_program(
            None,
            "(datatype T (A) (F T)) (function out () i64 :no-merge)",
        )
        .unwrap();
    let error = graph
        .parse_and_run_program(None, "(F (A)) (fail (set (out) (read-f-size)))")
        .unwrap_err();
    assert!(matches!(error, Error::ExpectFail(..)));
    assert_eq!(observed.load(Ordering::SeqCst), 1);
    assert_eq!(graph.get_size("F"), 1);
    assert_eq!(graph.get_size("out"), 0);
}

#[test]
fn batches_flush_for_keyed_reads_globals_and_deletes() {
    let source = "(datatype T (A) (B) (F T))
            (function f () i64 :no-merge)
            (function g () i64 :no-merge)
            (function out () i64 :no-merge)
            (function value (T) i64 :no-merge)
            (F (A)) (set (f) 1) (set (g) (f)) (check (= (g) 1))
            (delete (f)) (fail (check (= (f) 1)))
            (let $a (A)) (F $a)
            (set (value (A)) 7) (union (A) (B))
            (set (out) (value (B))) (check (= (out) 7))";
    for direct in [false, true] {
        run_ground_action_oracle(&mut EGraph::default(), source, direct).unwrap();
    }
}

#[test]
fn union_preserves_a_failing_merge_boundary() {
    let mut graph = EGraph::default();
    graph
        .parse_and_run_program(
            None,
            "(datatype T (A) (B) (C))
            (function value (T) i64 :no-merge)
            (set (value (A)) 0) (set (value (B)) 1)",
        )
        .unwrap();
    assert!(
        graph
            .parse_and_run_program(None, "(union (A) (B)) (C)")
            .is_err()
    );
    assert_eq!(graph.get_size("C"), 0);
}

#[test]
fn constructor_rows_remain_subsumed_after_union() {
    for direct in [false, true] {
        let mut graph = EGraph::default();
        run_ground_action_oracle(
            &mut graph,
            "(datatype T (A) (B) (F T))
                (F (A)) (subsume (F (A))) (union (A) (B)) (F (B))",
            direct,
        )
        .unwrap();
        let mut rows = Vec::new();
        graph
            .backend
            .for_each(graph.functions["F"].backend_id, |row| {
                rows.push(row.subsumed)
            });
        assert_eq!(rows, vec![true]);
    }
}

#[test]
fn completed_constructor_prefix_survives_macro_errors() {
    struct RejectCheck;
    impl CommandMacro for RejectCheck {
        fn transform(
            &self,
            command: Command,
            _: &mut SymbolGen,
            _: &TypeInfo,
        ) -> Result<Vec<Command>, Error> {
            if matches!(command, Command::Check(..)) {
                Err(Error::BackendError("expected macro error".into()))
            } else {
                Ok(vec![command])
            }
        }
    }
    let mut graph = EGraph::default();
    graph
        .parse_and_run_program(None, "(datatype T (A) (F T))")
        .unwrap();
    graph.command_macros.register(Arc::new(RejectCheck));
    assert!(
        graph
            .parse_and_run_program(None, "(F (A)) (check (= (A) (A)))")
            .is_err()
    );
    assert_eq!(graph.get_size("F"), 1);
}

#[test]
fn read_primitives_observe_completed_insertions() {
    #[derive(Clone)]
    struct ReadSize;
    impl Primitive for ReadSize {
        fn name(&self) -> &str {
            "read-f-size"
        }
        fn get_type_constraints(&self, span: &Span) -> Box<dyn TypeConstraint> {
            SimpleTypeConstraint::new(self.name(), vec![I64Sort.to_arcsort()], span.clone())
                .into_box()
        }
    }
    impl ReadPrim for ReadSize {
        fn apply<'a, 'db>(&self, state: ReadState<'a, 'db>, _: &[Value]) -> Option<Value> {
            Some(
                state
                    .base_values()
                    .get(state.table_size("F").unwrap() as i64),
            )
        }
    }
    let mut graph = EGraph::default();
    graph.add_read_primitive(ReadSize, None);
    graph
        .parse_and_run_program(
            None,
            "(datatype T (A) (B) (F T))
        (function result () i64 :no-merge)
        (F (A)) (F (B)) (set (result) (read-f-size))
        (check (= (result) 2))",
        )
        .unwrap();
}

#[test]
fn parser_and_command_macros_run_before_preparation() {
    struct RewriteA;
    impl CommandMacro for RewriteA {
        fn transform(
            &self,
            command: Command,
            _: &mut SymbolGen,
            _: &TypeInfo,
        ) -> Result<Vec<Command>, Error> {
            Ok(vec![match command {
                Command::Action(Action::Expr(span, Expr::Call(_, ref head, _))) if head == "A" => {
                    Command::Action(Action::Expr(
                        span.clone(),
                        Expr::Call(span, "B".into(), vec![]),
                    ))
                }
                command => command,
            }])
        }
    }
    let mut graph = EGraph::default();
    graph
        .parse_and_run_program(None, "(datatype T (A) (B) (F T))")
        .unwrap();
    graph.command_macros.register(Arc::new(RewriteA));
    graph
        .parser
        .add_expr_macro(Arc::new(SimpleMacro::new("Alias", |_, span, _| {
            Ok(Expr::Call(span, "B".into(), vec![]))
        })));
    graph
        .parse_and_run_program(None, "(A) (F (Alias))")
        .unwrap();
    assert_eq!(graph.get_size("A"), 0);
    assert_eq!(graph.get_size("B"), 1);
    assert_eq!(graph.get_size("F"), 1);
}

#[test]
fn declared_calls_with_primitive_alternatives_keep_ambiguity() {
    #[derive(Clone)]
    struct AlsoA(ArcSort);
    impl Primitive for AlsoA {
        fn name(&self) -> &str {
            "A"
        }
        fn get_type_constraints(&self, span: &Span) -> Box<dyn TypeConstraint> {
            SimpleTypeConstraint::new(self.name(), vec![self.0.clone()], span.clone()).into_box()
        }
    }
    impl PurePrim for AlsoA {
        fn apply(&self, _: PureState<'_, '_>, _: &[Value]) -> Option<Value> {
            unreachable!("ambiguous calls cannot execute")
        }
    }
    let mut graph = EGraph::default();
    graph
        .parse_and_run_program(None, "(datatype T (A))")
        .unwrap();
    let sort = graph.type_info.get_sort_by_name("T").unwrap().clone();
    graph.add_pure_primitive(AlsoA(sort), None);
    assert!(graph.parse_and_run_program(None, "(A)").is_err());
    assert_eq!(graph.get_size("A"), 0);
}

#[test]
fn ground_action_cache_keeps_call_validation_and_command_scope() {
    let mut initial = EGraph::default();
    initial
        .parse_and_run_program(None, "(datatype T (A) (F T)) (datatype U (B))")
        .unwrap();
    for source in ["(F (A)) (F (A) (A))", "(F (A)) (F (B))"] {
        let mut graph = initial.clone();
        assert!(graph.parse_and_run_program(None, source).is_err());
        assert_eq!(graph.get_size("F"), 1);
        assert_eq!(graph.get_size("B"), 0);
    }

    let mut graph = initial;
    assert!(
        graph
            .parse_and_run_program(
                None,
                "(push) (constructor Temporary () T) (Temporary) (pop) (Temporary)",
            )
            .is_err()
    );
    assert!(!graph.functions.contains_key("Temporary"));
    graph
        .parse_and_run_program(
            None,
            "
        (push)
        (constructor Reused () T)
        (Reused)
        (pop)
        (constructor Padding () T)
        (constructor Reused () T)
        (Reused)
        (check (= (Reused) (Reused)))
    ",
        )
        .unwrap();
    assert_eq!(graph.get_size("Padding"), 0);
    assert_eq!(graph.get_size("Reused"), 1);
}

#[test]
fn cached_calls_preserve_parser_macro_registration() {
    let mut graph = EGraph::default();
    graph
        .parse_and_run_program(None, "(datatype T (A) (B) (F T))")
        .unwrap();
    graph
        .parser
        .add_command_macro(Arc::new(SimpleMacro::new("replace-a", |_, _, parser| {
            parser.add_expr_macro(Arc::new(SimpleMacro::new("A", |_, span, _| {
                Ok(Expr::Call(span, "B".into(), vec![]))
            })));
            Ok(vec![])
        })));
    graph
        .parse_and_run_program(None, "(F (A)) (replace-a) (F (A))")
        .unwrap();
    assert_eq!(graph.get_size("A"), 1);
    assert_eq!(graph.get_size("B"), 1);
    assert_eq!(graph.get_size("F"), 2);
}

#[test]
fn argument_buffers_reset_between_wide_and_narrow_calls() {
    let mut graph = EGraph::default();
    graph
        .parse_and_run_program(
            None,
            "(datatype T (A) (B) (F T) (Wide T T T T T))
        (Wide (A) (A) (A) (A) (A)) (F (A))
        (Wide (B) (B) (B) (B) (B))",
        )
        .unwrap();
    assert_eq!(graph.get_size("Wide"), 2);
    assert_eq!(graph.get_size("F"), 1);
}

#[test]
fn insertion_batches_keep_metadata_across_flushes_and_unions() {
    for threads in [1, 4] {
        let mut graph = EGraph::default();
        graph.backend.set_num_threads(threads);
        graph
            .parse_and_run_program(None, "(datatype T (A) (B) (F T))")
            .unwrap();
        BATCH_EVENTS.with(|events| *events.borrow_mut() = Some(Vec::new()));
        let mut source = "(F (A))\n".repeat(257);
        source.push_str("(union (A) (B))\n(F (B))");
        let program = graph.parse_program(None, &source).unwrap();
        let result = graph.run_program(program);
        let events = BATCH_EVENTS.with(|events| events.borrow_mut().take().unwrap());
        result.unwrap();
        assert_eq!(graph.get_size("F"), 1);
        assert_eq!(
            events.iter().map(|(count, _)| *count).collect::<Vec<_>>(),
            [256, 1, 1, 1]
        );
        assert!(events.iter().all(|(_, tables)| tables.len() == 2));
        // First-action lookups are [A,F], [A,F], [A,B], then [B,F].
        assert!(Rc::ptr_eq(&events[0].1[0], &events[1].1[0]));
        assert!(Rc::ptr_eq(&events[0].1[0], &events[2].1[0]));
        assert!(Rc::ptr_eq(&events[2].1[1], &events[3].1[0]));
        assert!(Rc::ptr_eq(&events[0].1[1], &events[1].1[1]));
        assert!(Rc::ptr_eq(&events[0].1[1], &events[3].1[1]));
        graph
            .parse_and_run_program(None, "(check (= (F (A)) (F (B))))")
            .unwrap();
    }
}

#[test]
fn opaque_constraint_and_read_observe_the_committed_prefix() {
    use std::sync::Mutex;
    use std::sync::atomic::{AtomicUsize, Ordering};

    #[derive(Clone)]
    struct ObservePrefix {
        order: Arc<Mutex<Vec<&'static str>>>,
        observed: Arc<AtomicUsize>,
    }
    impl Primitive for ObservePrefix {
        fn name(&self) -> &str {
            "observe-f-prefix"
        }
        fn get_type_constraints(&self, span: &Span) -> Box<dyn TypeConstraint> {
            self.order.lock().unwrap().push("constraints");
            SimpleTypeConstraint::new(self.name(), vec![I64Sort.to_arcsort()], span.clone())
                .into_box()
        }
    }
    impl ReadPrim for ObservePrefix {
        fn apply<'a, 'db>(&self, state: ReadState<'a, 'db>, _: &[Value]) -> Option<Value> {
            let size = state.table_size("F")?;
            self.observed.store(size, Ordering::SeqCst);
            self.order.lock().unwrap().push("read");
            Some(state.base_values().get(size as i64))
        }
    }
    let order = Arc::new(Mutex::new(Vec::new()));
    let observed = Arc::new(AtomicUsize::new(usize::MAX));
    let mut graph = EGraph::default();
    graph.add_read_primitive(
        ObservePrefix {
            order: order.clone(),
            observed: observed.clone(),
        },
        None,
    );
    graph
        .parse_and_run_program(None, "(datatype T (A) (F T))")
        .unwrap();
    order.lock().unwrap().clear();
    ORDER_LOG.with(|slot| *slot.borrow_mut() = Some(order.clone()));
    let result = graph.parse_and_run_program(None, "(F (A)) (observe-f-prefix)");
    ORDER_LOG.with(|slot| slot.borrow_mut().take());
    result.unwrap();
    assert_eq!(observed.load(Ordering::SeqCst), 1);
    assert_eq!(graph.get_size("F"), 1);
    let order = order.lock().unwrap();
    let commit = order.iter().position(|event| *event == "commit").unwrap();
    let constraints = order
        .iter()
        .position(|event| *event == "constraints")
        .unwrap();
    let read = order.iter().position(|event| *event == "read").unwrap();
    assert!(commit < constraints && constraints < read, "{order:?}");
}
