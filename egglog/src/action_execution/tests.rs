use super::*;

type BatchEvent = (usize, Option<Rc<egglog_bridge::TableAction>>);
type OrderLog = Arc<std::sync::Mutex<Vec<&'static str>>>;

std::thread_local! {
    pub(super) static BATCH_EVENTS: std::cell::RefCell<Vec<BatchEvent>> = const { std::cell::RefCell::new(Vec::new()) };
    pub(super) static ORDER_LOG: std::cell::RefCell<Option<OrderLog>> = const { std::cell::RefCell::new(None) };
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
            // Keep the compiled reference independent of late recognition.
            let result = match command {
                ResolvedNCommand::CoreAction(action) => {
                    graph.eval_actions(ActionBatch::CompiledOracle(&ResolvedActions::new(
                        vec![action],
                    )))?;
                    Vec::new()
                }
                ResolvedNCommand::CoreActions(actions) => {
                    graph.eval_actions(ActionBatch::CompiledOracle(&actions))?;
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
fn runtime_view_actions_match_compiled_execution() {
    for source in ["(View (A))", "(union (View (A)) (A))"] {
        let mut direct = EGraph::default();
        let mut compiled = EGraph::default();
        for graph in [&mut direct, &mut compiled] {
            graph
                .parse_and_run_program(
                    None,
                    "(datatype T (A) (B))
                     (function View (T) T :no-merge :internal-role constructor-view)
                     (set (View (A)) (B))",
                )
                .unwrap();
            let view = &graph.functions["View"];
            assert!(view.is_view());
            assert_eq!(view.func_type().role, FunctionRole::ConstructorView);
        }
        assert_eq!(
            run_ground_action_oracle(&mut direct, source, true).unwrap(),
            run_ground_action_oracle(&mut compiled, source, false).unwrap(),
        );
        assert_action_graphs_equal(&direct, &compiled);
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
        for (source, succeeds) in [
            ("(Pair (N1) (Pair (N1) (N2)))", true),
            ("(seen (Pair (A) (A)))", true),
            ("(union (A) (A))", true),
            ("(Pair (B) (B))", true),
            ("(union (A) (B))", true),
            ("(union (A) (B))", true),
            ("(check (= (Pair (A) (A)) (Pair (B) (B))))", true),
            ("(push)", true),
            ("(constructor Temporary () T) (Temporary)", true),
            ("(pop)", true),
            ("(Temporary)", false),
            ("(Num (+ 1 2))", true),
            ("(Pair $global (N1))", true),
            ("(begin (Pair (N2) (N2)))", true),
            ("(begin (let local (N2)) (Pair local local))", true),
            ("(missing (Pair (N2) (A)))", false),
            ("(set (missing (N1)) (N2))", true),
            ("(delete (missing (N1)))", true),
            ("(tuple-result (A))", false),
            ("(Occ (A) (A) (B))", false),
            ("(Pair (A) unbound)", false),
            ("(Pair (A))", false),
        ] {
            let actual = run_ground_action_oracle(&mut direct, source, true);
            let expected = run_ground_action_oracle(&mut compiled, source, false);
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
fn resolved_constructor_actions_prepare_for_direct_execution() {
    let mut graph = EGraph::default();
    graph
        .parse_and_run_program(None, "(datatype T (A) (F T))")
        .unwrap();
    let command = graph.parse_program(None, "(F (A))").unwrap().pop().unwrap();
    let commands = graph.resolve_command(command).unwrap().desugared;
    assert_eq!(commands.len(), 1);
    let ResolvedNCommand::CoreAction(action) = commands.into_iter().next().unwrap() else {
        panic!("expected one resolved action");
    };
    let actions = ResolvedActions::new(vec![action]);
    let mut calls = GroundActionCache::default();
    assert!(
        graph
            .prepare_resolved_ground_actions(&actions, &mut calls)
            .is_some()
    );
    assert_eq!(graph.get_size("F"), 0);
    graph
        .eval_actions(ActionBatch::Resolved(&actions, &mut calls))
        .unwrap();
    assert_eq!(graph.get_size("F"), 1);
}

#[test]
fn resolved_batches_coalesce_and_keep_metadata_across_flushes_and_unions() {
    for threads in [1, 4] {
        let mut graph = EGraph::default();
        graph.backend.set_num_threads(threads);
        graph
            .parse_and_run_program(None, "(datatype T (A) (B) (F T))")
            .unwrap();
        BATCH_EVENTS.with(|events| events.borrow_mut().clear());
        let mut source = "(F (A))\n".repeat(257);
        source.push_str("(union (A) (B))\n(F (A))");
        graph.parse_and_run_program(None, &source).unwrap();
        let events = BATCH_EVENTS.with(|events| std::mem::take(&mut *events.borrow_mut()));
        assert_eq!(
            events.iter().map(|(count, _)| *count).collect::<Vec<_>>(),
            [256, 1, 1, 1]
        );
        let first = events[0].1.as_ref().unwrap();
        assert!(
            events
                .iter()
                .all(|(_, table)| Rc::ptr_eq(first, table.as_ref().unwrap())),
            "the A handle must stay interned across bounded flushes and the union"
        );
        assert_eq!(graph.get_size("F"), 1);
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
            let accepted = commands.iter().any(|command| match command {
                Command::Action(action) => graph
                    .prepare_ground_action(
                        typechecking::ClosedAction::from_action(action),
                        &mut GroundActionCache::default(),
                        |_| true,
                    )
                    .is_some(),
                _ => false,
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
                .prepare_ground_action(
                    typechecking::ClosedAction::from_action(action),
                    &mut GroundActionCache::default(),
                    |_| true,
                )
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
            let mut calls = GroundActionCache::default();
            assert!(commands.iter().all(|command| {
                match command {
                    Command::Action(action) => graph
                        .prepare_ground_action(
                            typechecking::ClosedAction::from_action(action),
                            &mut calls,
                            |_| true,
                        )
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
fn repeated_nullary_calls_refresh_after_flushes_and_unions() {
    let source = format!(
        "(datatype T (A) (B) (F T))
(A)
{}
(union (A) (B))
{}
(check (= (F (A)) (F (B))))",
        "(F (B))\n".repeat(260),
        "(F (B))\n".repeat(260),
    );
    let mut graph = EGraph::default();
    let mut compiled = EGraph::default();
    run_ground_action_oracle(&mut graph, &source, true).unwrap();
    run_ground_action_oracle(&mut compiled, &source, false).unwrap();
    assert_eq!(graph.get_size("F"), 1);
    assert_action_graphs_equal(&graph, &compiled);
}

#[test]
fn nullary_caching_keeps_subsumed_constructor_rows() {
    let mut graph = EGraph::default();
    graph
        .parse_and_run_program(
            None,
            "(datatype T (A) (Pair T T))
        (A) (subsume (A)) (Pair (A) (A)) (Pair (A) (A))",
        )
        .unwrap();
    let mut rows = Vec::new();
    graph
        .backend
        .for_each(graph.functions["A"].backend_id, |row| {
            rows.push(row.subsumed)
        });
    assert_eq!(rows, vec![true]);
    assert_eq!(graph.get_size("Pair"), 1);
}
