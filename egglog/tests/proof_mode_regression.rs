use egglog::ast::{Command, Expr};
use egglog::util::SymbolGen;
use egglog::*;
use std::sync::{Arc, Mutex};

struct RecordFunctionInputArity {
    name: String,
    seen: Arc<Mutex<Vec<usize>>>,
}

struct DefineSort;

impl UserDefinedCommand for DefineSort {
    fn update(&self, egraph: &mut EGraph, _args: &[Expr]) -> Result<Vec<CommandOutput>, Error> {
        egraph.parse_and_run_program(None, "(sort Leaked)")
    }
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
fn fail_rejects_definitions_user_commands_and_scope_commands() {
    let rejected = [
        "(fail (sort S))",
        "(fail (datatype D (D0)))",
        "(fail (datatype* (Ds (Ds0))))",
        "(fail (constructor C () S))",
        "(fail (relation R (i64)))",
        "(fail (function f () i64 :no-merge))",
        "(fail (index I f (any 0)))",
        "(fail (ruleset rs))",
        "(fail (unstable-combined-ruleset both left right))",
        "(fail (rule () ((panic \"unused\"))))",
        "(fail (rewrite 1 2))",
        "(fail (birewrite 1 2))",
        "(fail (let value 1))",
        "(fail (let value (begin (+ 1 1))))",
        "(fail (push))",
        "(fail (pop))",
        "(fail (fail (sort Nested)))",
        "(fail (define-sort) (panic \"stop\"))",
    ];
    let mut egraph = EGraph::default();
    egraph
        .add_command("define-sort".to_owned(), Arc::new(DefineSort))
        .unwrap();
    for source in rejected {
        let error = egraph.parse_and_run_program(None, source).unwrap_err();
        assert!(
            matches!(&error, Error::DesugarError(..)),
            "{source}: {error:?}"
        );
    }
}

#[test]
fn fail_rejects_proof_commands_in_all_modes() {
    for mut egraph in [
        EGraph::default(),
        EGraph::new_with_term_encoding(),
        EGraph::new_with_proofs(),
    ] {
        for source in ["(fail (prove (= 1 1)))", "(fail (prove-exists Missing))"] {
            let error = egraph.parse_and_run_program(None, source).unwrap_err();
            assert!(
                matches!(&error, Error::DesugarError(..)),
                "{source}: {error:?}"
            );
        }
    }
}

#[test]
fn proof_mode_fail_rolls_back_action_effects() {
    for source in [
        r#"
        (function score () i64 :merge old)
        (fail (set (score) 1) (panic "stop"))
        (fail (check (= (score) 1)))
        "#,
        r#"
        (datatype N (A) (B))
        (let a (A))
        (let b (B))
        (fail (union a b) (panic "stop"))
        (fail (check (= a b)))
        "#,
        r#"
        (datatype N (A))
        (fail (A) (panic "stop"))
        (fail (check (A)))
        "#,
    ] {
        EGraph::new_with_proofs()
            .parse_and_run_program(None, source)
            .unwrap_or_else(|error| panic!("{source}: {error:?}"));
    }
}

#[test]
fn proof_mode_fail_catches_input_errors() {
    EGraph::new_with_proofs()
        .parse_and_run_program(
            None,
            r#"
            (relation R (i64))
            (fail (input R "missing.tsv"))
            "#,
        )
        .unwrap();
}

#[test]
fn proof_mode_fail_rolls_back_input_rows() {
    let directory =
        std::env::temp_dir().join(format!("egglog_proof_fail_input_{}", std::process::id()));
    std::fs::create_dir_all(&directory).unwrap();
    std::fs::write(directory.join("rows.tsv"), "1\n").unwrap();

    let mut egraph = EGraph::new_with_proofs();
    egraph.fact_directory = Some(directory.clone());
    egraph
        .parse_and_run_program(
            None,
            r#"
            (relation R (i64))
            (fail (input R "rows.tsv") (panic "stop"))
            (fail (check (R 1)))
            "#,
        )
        .unwrap();

    std::fs::remove_dir_all(directory).ok();
}

#[test]
fn proof_mode_fail_does_not_offset_later_fiats() {
    EGraph::new_with_proofs()
        .parse_and_run_program(
            None,
            r#"
            (datatype N (A) (B))
            (fail (check (= (A) (B))) (union (A) (B)))
            (union (A) (B))
            (prove (= (A) (B)))
            "#,
        )
        .unwrap();
}

#[test]
fn fail_with_term_building_extract_has_the_same_behavior_in_all_modes() {
    for mut egraph in [
        EGraph::default(),
        EGraph::new_with_term_encoding(),
        EGraph::new_with_proofs(),
    ] {
        egraph
            .parse_and_run_program(None, "(datatype N (A))")
            .unwrap();
        let error = egraph
            .parse_and_run_program(None, "(fail (extract (A)))")
            .unwrap_err();
        assert!(matches!(error, Error::ExpectFail(_)));
        egraph
            .parse_and_run_program(None, "(fail (check (A)))")
            .unwrap();
    }
}

#[test]
fn proof_mode_rejects_output_at_top_level_and_inside_fail() {
    for source in ["(output \"term.txt\" 1)", "(fail (output \"term.txt\" 1))"] {
        let error = EGraph::new_with_proofs()
            .parse_and_run_program(None, source)
            .unwrap_err();
        assert!(matches!(error, Error::UnsupportedProofCommand { .. }));
        assert!(error.to_string().contains("`output`"));
    }
}

#[test]
fn fail_rolls_back_successful_mutations_in_all_modes() {
    for mut egraph in [
        EGraph::default(),
        EGraph::new_with_term_encoding(),
        EGraph::new_with_proofs(),
    ] {
        egraph
            .parse_and_run_program(
                None,
                r#"
            (function score () i64 :merge old)
            (fail (set (score) 1) (check (= (score) 2)))
            (fail (check (= (score) 1)))
            "#,
            )
            .unwrap();
    }
}

#[test]
fn fail_rolls_back_when_every_wrapped_command_succeeds() {
    for mut egraph in [
        EGraph::default(),
        EGraph::new_with_term_encoding(),
        EGraph::new_with_proofs(),
    ] {
        let error = egraph
            .parse_and_run_program(None, "(relation R (i64)) (fail (R 1))")
            .unwrap_err();
        assert!(matches!(error, Error::ExpectFail(_)));
        egraph
            .parse_and_run_program(None, "(fail (check (R 1)))")
            .unwrap();
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
