use egglog::ast::{Command, Expr};
use egglog::util::SymbolGen;
use egglog::*;
use std::{
    panic::{AssertUnwindSafe, catch_unwind},
    sync::{Arc, Mutex},
};

struct RecordFunctionInputArity {
    name: String,
    seen: Arc<Mutex<Vec<usize>>>,
}

struct CountCommandMacroCalls(Arc<Mutex<usize>>);

struct BindThenFail;

impl UserDefinedCommand for BindThenFail {
    fn update(&self, egraph: &mut EGraph, _args: &[Expr]) -> Result<Vec<CommandOutput>, Error> {
        egraph.parse_and_run_program(None, "(relation Leaked ())")?;
        Err(Error::BackendError("expected".to_owned()))
    }
}

impl CommandMacro for CountCommandMacroCalls {
    fn transform(
        &self,
        command: Command,
        _symbol_gen: &mut SymbolGen,
        _type_info: &TypeInfo,
    ) -> Result<Vec<Command>, Error> {
        *self.0.lock().unwrap() += 1;
        Ok(vec![command])
    }
}

#[test]
fn fail_body_is_not_passed_through_command_macros_twice() {
    let calls = Arc::new(Mutex::new(0));
    let mut egraph = EGraph::default();
    egraph
        .command_macros_mut()
        .register(Arc::new(CountCommandMacroCalls(calls.clone())));

    egraph
        .parse_and_run_program(None, "(fail (check (= 1 2)))")
        .unwrap();

    assert_eq!(*calls.lock().unwrap(), 1);
}

impl CommandMacro for RecordFunctionInputArity {
    fn transform(
        &self,
        command: Command,
        _symbol_gen: &mut SymbolGen,
        type_info: &TypeInfo,
    ) -> Result<Vec<Command>, Error> {
        if let Some(func) = type_info.get_func_type(&self.name) {
            self.seen.lock().unwrap().push(func.input.len());
        }
        Ok(vec![command])
    }
}

#[test]
fn proof_mode_command_macros_see_original_function_arities() {
    let seen = Arc::new(Mutex::new(vec![]));
    let mut egraph = EGraph::new_with_proofs();
    egraph
        .command_macros_mut()
        .register(Arc::new(RecordFunctionInputArity {
            name: "score".to_string(),
            seen: seen.clone(),
        }));

    egraph
        .parse_and_run_program(
            None,
            r#"
            (datatype Math (Num i64))
            (function score (Math) i64 :merge old)
            (let x (Num 1))
            "#,
        )
        .unwrap();

    assert_eq!(*seen.lock().unwrap(), vec![1]);
}

#[test]
fn term_and_proof_modes_lower_input_rows_as_fiat_actions() {
    let directory = std::env::temp_dir().join(format!("egglog_proof_input_{}", std::process::id()));
    std::fs::create_dir_all(&directory).unwrap();
    std::fs::write(directory.join("edges.tsv"), "a\tb\nb\tc\n").unwrap();
    std::fs::write(directory.join("scores.tsv"), "a\t7\n").unwrap();
    std::fs::write(directory.join("seen.tsv"), "a\n").unwrap();

    for mut egraph in [
        EGraph::new_with_term_encoding(),
        EGraph::new_with_proofs().with_proof_testing(),
    ] {
        egraph.fact_directory = Some(directory.clone());
        egraph
            .parse_and_run_program(
                None,
                r#"
                (relation Edge (String String))
                (function score (String) i64 :no-merge)
                (function seen (String) Unit :no-merge)
                (input Edge "edges.tsv")
                (input score "scores.tsv")
                (input seen "seen.tsv")
                (check (Edge "a" "b"))
                (check (= (score "a") 7))
                (check (= (seen "a") ()))
                "#,
            )
            .unwrap();
    }

    std::fs::remove_dir_all(directory).ok();
}

#[test]
fn term_and_proof_modes_reject_eq_sort_no_merge_functions() {
    // Eq-sort-output `:no-merge` is not modeled by the encoding (its conflict check
    // needs union-find leaders); such a program is unsupported and runs plain only.
    // Primitive/Unit-output `:no-merge` is supported (see the input test above).
    for mut egraph in [
        EGraph::new_with_term_encoding(),
        EGraph::new_with_proofs().with_proof_testing(),
    ] {
        let error = egraph
            .parse_and_run_program(None, "(sort Foo) (function bar () Foo :no-merge)")
            .unwrap_err();
        assert!(matches!(error, Error::UnsupportedProofCommand { .. }));
        assert!(error.to_string().contains("`:no-merge`"));
    }
}

#[test]
fn proof_mode_rejects_fail_wrapped_input() {
    let error = EGraph::new_with_proofs()
        .parse_and_run_program(
            None,
            r#"
            (relation Edge (String String))
            (fail (input Edge "edges.tsv"))
            "#,
        )
        .unwrap_err();

    assert!(matches!(error, Error::UnsupportedProofCommand { .. }));
    assert!(
        error
            .to_string()
            .contains("`fail` wrapping an `input` command")
    );
}

#[test]
fn proof_mode_allows_fail_wrapping_set() {
    // A `(fail (set …))` is accepted by proof encoding (it used to be rejected as a
    // non-atomic wrapped command). The set succeeds, so `fail` reports that its
    // wrapped command did not fail.
    let error = EGraph::new_with_proofs()
        .parse_and_run_program(
            None,
            r#"
            (function score () i64 :merge old)
            (fail (set (score) 1))
            "#,
        )
        .unwrap_err();

    assert!(matches!(error, Error::ExpectFail(..)));
}

#[test]
fn proof_mode_allows_fail_wrapping_multi_operation_encoding() {
    // A wrapped command that encodes to several commands is now accepted;
    // declaring the function succeeds, so `fail` reports it did not fail.
    let error = EGraph::new_with_proofs()
        .parse_and_run_program(None, "(fail (function score () i64 :merge old))")
        .unwrap_err();

    assert!(matches!(error, Error::ExpectFail(..)));
}

#[test]
fn proof_mode_fail_catches_failure_among_wrapped_commands() {
    // `fail` runs the wrapped commands in order and succeeds at the first failure:
    // the set succeeds and the mismatched check fails, so the `fail` passes.
    EGraph::new_with_proofs()
        .parse_and_run_program(
            None,
            r#"
            (function score () i64 :merge old)
            (fail (set (score) 1) (check (= (score) 2)))
            "#,
        )
        .unwrap();
}

#[test]
fn proof_testing_uses_only_actions_before_the_nested_proof() {
    let error = EGraph::new_with_proofs()
        .with_proof_testing()
        .parse_and_run_program(
            None,
            r#"
            (datatype Math (A) (B))
            (fail
              (union (A) (B))
              (check (= (A) (B))))
            "#,
        )
        .unwrap_err();

    assert!(matches!(error, Error::ExpectFail(..)));
}

#[test]
fn proof_testing_ignores_rules_after_an_expected_failure() {
    EGraph::new_with_proofs()
        .with_proof_testing()
        .parse_and_run_program(
            None,
            r#"
            (datatype Math (A) (B))
            (relation Seed ())
            (Seed)
            (fail
              (check (= (A) (B)))
              (rule ((Seed)) ((union (A) (B))) :name "same"))
            (rule ((Seed)) ((union (A) (B))) :name "same")
            (run 1)
            (check (= (A) (B)))
            "#,
        )
        .unwrap();
}

#[test]
fn proof_testing_keeps_actions_before_an_expected_failure() {
    EGraph::new_with_proofs()
        .with_proof_testing()
        .parse_and_run_program(
            None,
            r#"
            (datatype Math (A) (B) (C))
            (fail
              (union (A) (B))
              (check (= (A) (C))))
            (check (= (A) (B)))
            "#,
        )
        .unwrap();
}

#[test]
fn proof_testing_keeps_begin_actions_before_an_expected_failure() {
    EGraph::new_with_proofs()
        .with_proof_testing()
        .parse_and_run_program(
            None,
            r#"
            (datatype Math (A) (B) (C))
            (fail
              (begin (union (A) (B)))
              (check (= (A) (C))))
            (check (= (A) (B)))
            "#,
        )
        .unwrap();
}

#[test]
fn failed_primitive_actions_do_not_enter_proof_history() {
    EGraph::new_with_proofs()
        .with_proof_testing()
        .parse_and_run_program(
            None,
            r#"
            (fail (log 0.0))
            (check (= 1.0 1.0))
            "#,
        )
        .unwrap();
}

#[test]
fn encoded_fail_supports_global_let_forms() {
    let programs = [
        r#"
        (datatype Math (A) (B))
        (fail
          (let $x (A))
          (check (= (A) (B))))
        (check (= $x (A)))
        "#,
        r#"
        (datatype Math (A) (B))
        (fail
          (let $x (begin (let y (A)) (A)))
          (check (= (A) (B))))
        (check (= $x (A)))
        "#,
    ];

    for program in programs {
        for mut egraph in [
            EGraph::default(),
            EGraph::new_with_term_encoding(),
            EGraph::new_with_proofs(),
            EGraph::new_with_proofs().with_proof_testing(),
        ] {
            egraph.parse_and_run_program(None, program).unwrap();
        }
    }
}

#[test]
fn fail_does_not_swallow_internal_proof_marker_errors() {
    let error = EGraph::default()
        .parse_and_run_program(None, r#"(fail (@record-proof-command "nested:0"))"#)
        .unwrap_err();

    assert!(matches!(error, Error::ProofCommandMarker(_)));
}

#[test]
fn failed_encoded_action_blocks_are_atomic() {
    let program = r#"
        (function score () i64 :merge old)
        (fail (begin (set (score) 1) (panic "expected")))
        (fail (check (= (score) 1)))
    "#;

    for mut egraph in [
        EGraph::default(),
        EGraph::new_with_term_encoding(),
        EGraph::new_with_proofs(),
        EGraph::new_with_proofs().with_proof_testing(),
    ] {
        let result = catch_unwind(AssertUnwindSafe(|| {
            egraph.parse_and_run_program(None, program)
        }));
        result
            .expect("a failed action block must not panic proof testing")
            .expect("the failed action block must leave no function value");
    }
}

#[test]
fn failed_schedule_rolls_back_the_entire_source_command() {
    let program = r#"
        (datatype Math (A) (B))
        (relation Seed ())
        (ruleset r)
        (Seed)
        (rule ((Seed)) ((union (A) (B))) :ruleset r :name "u")
        (fail (run-schedule (seq (run r) (run missing))))
        (fail (check (= (A) (B))))
    "#;

    for mut egraph in [
        EGraph::default(),
        EGraph::new_with_term_encoding(),
        EGraph::new_with_proofs(),
        EGraph::new_with_proofs().with_proof_testing(),
    ] {
        egraph.parse_and_run_program(None, program).unwrap();
    }
}

#[test]
fn failed_pop_rolls_back_the_entire_source_command() {
    let program = r#"
        (datatype Math (A))
        (push)
        (fail (pop 2))
        (pop)
    "#;

    for mut egraph in [
        EGraph::default(),
        EGraph::new_with_term_encoding(),
        EGraph::new_with_proofs(),
        EGraph::new_with_proofs().with_proof_testing(),
    ] {
        egraph.parse_and_run_program(None, program).unwrap();
    }
}

#[test]
fn nested_fail_rolls_back_its_failing_child() {
    let program = r#"
        (datatype Math (A) (B))
        (fail (fail (union (A) (B))))
        (fail (check (= (A) (B))))
    "#;

    for mut egraph in [
        EGraph::default(),
        EGraph::new_with_term_encoding(),
        EGraph::new_with_proofs(),
        EGraph::new_with_proofs().with_proof_testing(),
    ] {
        egraph.parse_and_run_program(None, program).unwrap();
    }
}

#[test]
fn desugared_fail_children_preserve_the_source_command_rollback_boundary() {
    let programs = [
        r#"
        (datatype Math (A) (B))
        (relation Seed ())
        (ruleset r)
        (Seed)
        (rule ((Seed)) ((union (A) (B))) :ruleset r :name "u")
        (fail (run-schedule (seq (run r) (run missing))))
        (fail (check (= (A) (B))))
        "#,
        r#"
        (datatype Math (A) (B))
        (fail (fail (union (A) (B))))
        (fail (check (= (A) (B))))
        "#,
    ];

    for program in programs {
        let desugared = EGraph::default()
            .resolve_program(None, program)
            .unwrap()
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join("\n");
        let mut replay = EGraph::default();
        replay.ensure_no_reserved_symbols(false);
        replay.parse_and_run_program(None, &desugared).unwrap();
    }
}

#[test]
fn failed_user_defined_commands_roll_back_and_are_not_statically_desugared() {
    let mut live = EGraph::default();
    live.add_command("bind-then-fail".to_owned(), Arc::new(BindThenFail))
        .unwrap();
    live.parse_and_run_program(None, "(fail (bind-then-fail))")
        .unwrap();
    assert!(live.get_function("Leaked").is_none());
    live.parse_and_run_program(None, "(relation Leaked ())")
        .unwrap();

    let mut encoder = EGraph::default();
    encoder
        .add_command("bind-then-fail".to_owned(), Arc::new(BindThenFail))
        .unwrap();
    let error = encoder
        .resolve_program(None, "(fail (bind-then-fail))")
        .unwrap_err();
    assert!(matches!(error, Error::DesugarError(..)));
    assert!(
        error
            .to_string()
            .contains("cannot statically desugar a `fail` body that may change compiler state")
    );
}

#[test]
fn failed_top_level_action_block_rolls_back_before_the_next_api_call() {
    for mut egraph in [
        EGraph::default(),
        EGraph::new_with_term_encoding(),
        EGraph::new_with_proofs(),
        EGraph::new_with_proofs().with_proof_testing(),
    ] {
        egraph
            .parse_and_run_program(None, "(function score () i64 :merge old)")
            .unwrap();
        assert!(
            egraph
                .parse_and_run_program(None, r#"(begin (set (score) 1) (panic "expected"))"#,)
                .is_err()
        );
        let check = catch_unwind(AssertUnwindSafe(|| {
            egraph.parse_and_run_program(None, "(fail (check (= (score) 1)))")
        }));
        check
            .expect("the next API call must not panic")
            .expect("the failed action block must leave no function value");
    }
}

#[test]
fn failed_global_let_blocks_leave_no_declaration() {
    let program = r#"
        (datatype Math (A))
        (fail (let $x (begin (panic "expected") (A))))
        (let $x (A))
        (check (= $x (A)))
    "#;

    for mut egraph in [
        EGraph::default(),
        EGraph::new_with_term_encoding(),
        EGraph::new_with_proofs(),
        EGraph::new_with_proofs().with_proof_testing(),
    ] {
        egraph.parse_and_run_program(None, program).unwrap();
    }
}

#[test]
fn desugaring_rejects_fail_bodies_that_change_static_scope() {
    let programs = [
        r#"
        (datatype Math (A))
        (fail (let $x (begin (panic "expected") (A))))
        (let $x (A))
        "#,
        r#"
        (datatype Math (A) (B))
        (fail (let $x (A)) (check (= (A) (B))))
        (let $y $x)
        "#,
        r#"
        (datatype Math (A) (B))
        (fail (push) (check (= (A) (B))) (pop))
        "#,
    ];

    for program in programs {
        for mut encoder in [
            EGraph::default(),
            EGraph::new_with_term_encoding(),
            EGraph::new_with_proofs(),
            EGraph::new_with_proofs().with_proof_testing(),
        ] {
            let error = encoder.resolve_program(None, program).unwrap_err();
            assert!(matches!(error, Error::DesugarError(..)));
            assert!(error.to_string().contains(
                "cannot statically desugar a `fail` body that may change compiler state"
            ));
        }
    }
}

#[test]
fn failed_global_let_block_rolls_back_before_the_next_api_call() {
    for mut egraph in [
        EGraph::default(),
        EGraph::new_with_term_encoding(),
        EGraph::new_with_proofs(),
        EGraph::new_with_proofs().with_proof_testing(),
    ] {
        egraph
            .parse_and_run_program(None, "(datatype Math (A))")
            .unwrap();
        assert!(
            egraph
                .parse_and_run_program(None, r#"(let $x (begin (panic "expected") (A)))"#,)
                .is_err()
        );
        egraph
            .parse_and_run_program(None, "(let $x (A)) (check (= $x (A)))")
            .unwrap();
    }
}

#[test]
fn proof_mode_recovers_after_a_command_error() {
    let mut egraph = EGraph::new_with_proofs().with_proof_testing();
    egraph
        .parse_and_run_program(None, "(datatype Math (A) (B) (C)) (union (A) (B))")
        .unwrap();
    assert!(
        egraph
            .parse_and_run_program(None, "(check (= (A) (C)))")
            .is_err()
    );
    egraph
        .parse_and_run_program(None, "(check (= (A) (B)))")
        .unwrap();
}

#[test]
fn proof_mode_eval_expr_recovers_after_an_error() {
    let mut parser = egglog::ast::Parser::default();
    let failing_primitive = parser.get_expr_from_string(None, "(log 0.0)").unwrap();

    for mut egraph in [
        EGraph::new_with_term_encoding(),
        EGraph::new_with_proofs(),
        EGraph::new_with_proofs().with_proof_testing(),
    ] {
        assert!(egraph.eval_expr(&failing_primitive).is_err());
        egraph
            .parse_and_run_program(None, "(relation Recovered ())")
            .unwrap();
    }

    let failing_constructor = parser.get_expr_from_string(None, "(A)").unwrap();
    for mut egraph in [
        EGraph::new_with_term_encoding(),
        EGraph::new_with_proofs(),
        EGraph::new_with_proofs().with_proof_testing(),
    ] {
        egraph
            .parse_and_run_program(None, "(datatype Math (A))")
            .unwrap();
        assert!(egraph.eval_expr(&failing_constructor).is_err());
        egraph.parse_and_run_program(None, "(A)").unwrap();
    }
}

/// A set element is reshaped (`(Id (N 1))` → `(N 1)`) and then collapses into
/// another element (`(N 1)` = `(N 3)`), in a set whose value-order element
/// list disagrees with its term form's AST order. Guards against container
/// rebuild proofs identifying changed elements by position instead of by term.
#[test]
fn unordered_container_reshaped_element_collapse_proof() {
    let program = "
(datatype Math (N i64) (Id Math))
(sort MSet (Set Math))
(relation Holds (MSet))
(relation Go ())
(Go)
(rewrite (Id x) x)
(rule ((Go)) ((Holds (set-of (Id (N 1)) (Id (N 2)) (N 3)))))
(rule ((Go)) ((union (N 1) (N 3))))
(run 8)
(check (Holds (set-of (N 1) (N 2))))
";
    EGraph::new_with_proofs()
        .with_proof_testing()
        .parse_and_run_program(None, program)
        .unwrap();
}
