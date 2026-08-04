// Confirms that a real rewrite rule fires through the Differential Dataflow
// join: without the body producing a match and the head applying it (then
// congruence closing), the final `(check ...)` would fail.
use std::sync::Arc;

use egglog::EGraph;
use egglog_ast::core::{
    GenericAtom, GenericAtomTerm, GenericCoreAction, GenericCoreActions, GenericCoreRule, Query,
};
use egglog_ast::span::{RustSpan, Span};
use egglog_backend_trait::{
    Backend, ColumnTy, DefaultVal, FunctionConfig, MergeFn, ReadMode, RuleActionCall, RuleBodyCall,
    RuleSetRun, RuleSpec, RuleValue, RuleVar,
};

fn dd_egraph() -> EGraph {
    EGraph::with_backend(Box::new(egglog_experimental_dd::EGraph::new())).with_term_encoding()
}

#[test]
fn commutativity_fires_through_dd_join() {
    let mut eg = dd_egraph();
    eg.parse_and_run_program(
        None,
        r#"
        (datatype Math (Num i64) (Add Math Math))
        (rewrite (Add a b) (Add b a))
        (let t (Add (Num 1) (Num 2)))
        (run 3)
        ; only holds if (Add a b) matched on the DD join, the head built
        ; (Add b a), and congruence unified the two:
        (check (= (Add (Num 1) (Num 2)) (Add (Num 2) (Num 1))))
        "#,
    )
    .expect("commutativity rewrite should fire and unify via the DD join");
}

#[test]
fn multi_atom_join_associativity() {
    // A two-atom body join ((Add a b) matched against the rewrite LHS decomposed
    // into view atoms) exercising a wider DD join than a single atom.
    let mut eg = dd_egraph();
    eg.parse_and_run_program(
        None,
        r#"
        (datatype Math (Num i64) (Add Math Math) (Mul Math Math))
        (rewrite (Mul a (Add b c)) (Add (Mul a b) (Mul a c)))
        (let e (Mul (Num 2) (Add (Num 3) (Num 4))))
        (run 3)
        (check (= (Mul (Num 2) (Add (Num 3) (Num 4)))
                  (Add (Mul (Num 2) (Num 3)) (Mul (Num 2) (Num 4)))))
        "#,
    )
    .expect("distributivity rewrite should fire via the multi-atom DD join");
}

#[test]
fn index_only_body_joins_instead_of_firing_once() {
    // A body whose only atom is an index atom is still atom-bearing: it must be
    // joined, not treated as `(rule () …)` and fired once from an empty
    // environment (which leaves the head's variables unbound). Built against the
    // backend SPI directly because the frontend only emits index atoms under the
    // term encoding, where it always pairs them with an ordinary table atom.
    fn sp() -> Span {
        Span::Rust(Arc::new(RustSpan {
            file: file!(),
            line: line!(),
            column: column!(),
        }))
    }
    fn var(id: u32, name: &str) -> RuleVar {
        RuleVar {
            id,
            name: name.into(),
            ty: ColumnTy::Id,
        }
    }
    fn term(v: &RuleVar) -> GenericAtomTerm<RuleVar, RuleValue> {
        GenericAtomTerm::Var(sp(), v.clone())
    }
    fn table(name: &str) -> FunctionConfig {
        FunctionConfig {
            schema: vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Id],
            n_vals: 1,
            n_identity_vals: None,
            default: DefaultVal::Fail,
            merge: MergeFn::Old,
            name: name.into(),
            can_subsume: false,
        }
    }

    let mut eg = egglog_experimental_dd::EGraph::new();
    let edge = eg.add_table(table("edge"));
    let touched = eg.add_table(table("touched"));
    let a = eg.fresh_id();
    let b = eg.fresh_id();
    eg.add_values(vec![(edge, vec![a, b, a])]);
    eg.flush_updates();

    // `(EdgeOcc x p q x)`: the rows of `edge` reached through a value occurring
    // in any of its three columns, where that value is also the row's output.
    let (x, p, q, unit) = (var(0, "x"), var(1, "p"), var(2, "q"), var(3, "unit"));
    let mut body = Query::default();
    body.atoms.push(GenericAtom {
        span: sp(),
        head: RuleBodyCall::IndexTable {
            id: edge,
            any_of: vec![0, 1, 2],
            read: ReadMode::Live,
        },
        args: vec![term(&x), term(&p), term(&q), term(&x), term(&unit)],
    });
    let rule = RuleSpec {
        name: "index-only".into(),
        seminaive: true,
        no_decomp: false,
        core: GenericCoreRule {
            span: sp(),
            body,
            head: GenericCoreActions::new(vec![GenericCoreAction::Set(
                sp(),
                RuleActionCall::Table {
                    id: touched,
                    name: "touched".into(),
                },
                vec![term(&p), term(&q)],
                vec![term(&x)],
            )]),
        },
    };

    let id = eg.add_rule(rule).expect("index-only body is a valid rule");
    eg.run_rules(RuleSetRun {
        name: Some("index-only"),
        rules: &[id],
    })
    .expect("index-only body should join, binding the head's variables");
    eg.flush_updates();

    let mut rows = Vec::new();
    eg.for_each_while_dyn(touched, &mut |row| {
        rows.push(row.vals.to_vec());
        true
    });
    assert_eq!(rows, vec![vec![a, b, a]]);
}
