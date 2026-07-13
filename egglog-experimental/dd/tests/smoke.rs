use std::panic::{catch_unwind, AssertUnwindSafe};
use std::sync::Arc;

use egglog::ast::Span;
use egglog::constraint::{SimpleTypeConstraint, TypeConstraint};
use egglog::scheduler::{Matches, Scheduler};
use egglog::sort::I64Sort;
use egglog::{prelude::*, EGraph, Primitive, PrimitiveValidator, Value, WritePrim, WriteState};

#[derive(Clone)]
struct ChooseAllScheduler;

impl Scheduler for ChooseAllScheduler {
    fn filter_matches(&mut self, _rule: &str, _ruleset: &str, matches: &mut Matches) -> bool {
        matches.choose_all();
        true
    }
}

#[derive(Clone)]
struct RegistryWrite;

impl Primitive for RegistryWrite {
    fn name(&self) -> &str {
        "registry-write"
    }

    fn get_type_constraints(&self, span: &Span) -> Box<dyn TypeConstraint> {
        SimpleTypeConstraint::new(
            self.name(),
            vec![I64Sort.to_arcsort(), I64Sort.to_arcsort()],
            span.clone(),
        )
        .into_box()
    }
}

impl WritePrim for RegistryWrite {
    fn apply<'a, 'db>(&self, _state: WriteState<'a, 'db>, args: &[Value]) -> Option<Value> {
        Some(args[0])
    }
}

#[test]
fn dd_runs_basic_egg() {
    let backend = Box::new(egglog_experimental_dd::EGraph::new());
    let mut eg = EGraph::with_backend(backend).with_term_encoding();
    eg.parse_and_run_program(
        None,
        "(datatype Math (Num i64) (Add Math Math))\n(Add (Num 1) (Num 2))\n(run 1)\n(print-size Add)",
    )
    .unwrap();
}

#[test]
fn dd_runs_proof_mode_pair_container_side_condition() {
    let backend = Box::new(egglog_experimental_dd::EGraph::new());
    let mut eg = egglog_experimental::new_experimental_egraph_with_backend_and_proofs(backend);
    eg.parse_and_run_program(
        None,
        r#"
        (datatype Expr (A))
        (sort Cost (Pair Expr i64))
        (relation Seed (Expr))
        (relation Seen ())

        (Seed (A))

        (rule ((Seed e)
               (= c (pair e 1)))
              ((Seen))
              :name "pair-side-condition")

        (run 1)
        (prove (Seen))
        "#,
    )
    .unwrap();
}

#[test]
fn dd_proof_mode_resolves_constructor_view_conflicts() {
    let backend = Box::new(egglog_experimental_dd::EGraph::new());
    let mut eg = egglog_experimental::new_experimental_egraph_with_backend_and_proofs(backend);
    eg.parse_and_run_program(
        None,
        r#"
        (datatype Expr (A) (B) (F Expr))
        (let a (A))
        (let b (B))
        (let fa (F a))
        (let fb (F b))
        (union a b)
        (run 5)
        (prove (= fa fb))
        "#,
    )
    .unwrap();
}

/// DD has no native union-find, so it must be paired with term encoding.
/// Without it, the frontend refuses to run rather than silently drop `union`s.
#[test]
fn dd_without_term_encoding_errors() {
    let backend = Box::new(egglog_experimental_dd::EGraph::new());
    let mut eg = EGraph::with_backend(backend); // no `.with_term_encoding()`
    let err = eg
        .parse_and_run_program(None, "(datatype Math (Num i64))\n(run 1)")
        .unwrap_err();
    assert!(
        err.to_string().contains("term encoding"),
        "expected a term-encoding-required error, got: {err}"
    );
}

#[test]
fn dd_custom_scheduler_returns_a_backend_capability_error() {
    let backend = Box::new(egglog_experimental_dd::EGraph::new());
    let mut eg = EGraph::with_backend(backend).with_term_encoding();
    eg.parse_and_run_program(
        None,
        r#"
        (ruleset scheduled)
        (relation Input (i64))
        (relation Output (i64))
        (rule ((Input x)) ((Output x)) :ruleset scheduled)
        "#,
    )
    .unwrap();
    let scheduler = eg.add_scheduler(Box::new(ChooseAllScheduler));

    let error = eg
        .step_rules_with_scheduler(scheduler, "scheduled")
        .expect_err("DD cannot instantiate custom-scheduler matches through the bridge");

    assert!(
        error.to_string().contains("reference bridge backend"),
        "unexpected scheduler capability error: {error}"
    );
}

#[test]
fn registry_primitive_returns_run_rules_error_without_unwinding() {
    let backend = Box::new(egglog_experimental_dd::EGraph::new());
    let mut eg = EGraph::with_backend(backend).with_term_encoding();
    let validator: PrimitiveValidator = Arc::new(|_, args| args.first().copied());
    eg.add_write_primitive(RegistryWrite, Some(validator));

    let outcome = catch_unwind(AssertUnwindSafe(|| {
        eg.parse_and_run_program(
            None,
            r#"
            (relation Input (i64))
            (relation Output (i64))
            (Input 1)
            (rule ((Input x))
                  ((let y (registry-write x))
                   (Output y)))
            (run 1)
            "#,
        )
    }));
    let error = outcome
        .expect("registry-backed primitive failure must not unwind")
        .unwrap_err();
    assert!(
        error
            .to_string()
            .contains("requires a backend action registry"),
        "unexpected registry capability error: {error}"
    );
}

#[test]
fn dd_frontend_push_pop_rebuilds_cloned_join_state() {
    let backend = Box::new(egglog_experimental_dd::EGraph::new());
    let mut eg = EGraph::with_backend(backend).with_term_encoding();

    eg.parse_and_run_program(
        None,
        r#"
        (relation Input (i64))
        (relation Output (i64))
        (rule ((Input x)) ((Output x)))

        (Input 1)
        (run 1)
        (check (Output 1))

        (push)
        (Input 2)
        (run 1)
        (check (Output 2))
        (pop)

        (check (Output 1))
        (fail (check (Output 2)))
        (Input 3)
        (run 1)
        (check (Output 3))
        "#,
    )
    .expect("DD push/pop must restore state and rebuild the transient join");
}

#[test]
fn backend_generic_reads_work_without_an_action_registry() {
    let backend = Box::new(egglog_experimental_dd::EGraph::new());
    let mut eg = EGraph::with_backend(backend).with_term_encoding();
    eg.parse_and_run_program(
        None,
        r#"
        (relation R (i64))
        (R 3)
        "#,
    )
    .unwrap();

    let mut relation_entry = None;
    eg.constructor_enodes("R", |enode| {
        relation_entry = Some(eg.value_to_base::<i64>(enode.children[0]));
    })
    .unwrap();
    assert_eq!(relation_entry, Some(3));
    assert!(eg.function_entries("R", |_| {}).is_err());

    let mut called = false;
    let error = eg
        .update(|_| {
            called = true;
            Ok(())
        })
        .unwrap_err();
    assert!(!called);
    assert!(error
        .to_string()
        .contains("EGraph::update requires a backend action registry"));
}
