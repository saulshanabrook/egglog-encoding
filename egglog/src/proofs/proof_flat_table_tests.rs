use std::fmt::Write as _;

use crate::{EGraph, ast::FunctionSubtype};

const PRELUDE: &str = r#"
    (datatype Math (Num i64) (Add Math Math))

    (rule ((= e (Add a b)))
          ((union e (Add b a)))
          :name "commute")

    (Add (Num 1) (Num 2))
    (run 1)
"#;

fn is_proof_node(egraph: &EGraph, function: &crate::Function) -> bool {
    function.decl.internal_term_node
        && function
            .schema
            .input
            .last()
            .is_some_and(|sort| sort.name() == egraph.proof_state.proof_names.proof_datatype)
}

fn flat_row_count(egraph: &EGraph) -> usize {
    egraph
        .functions
        .values()
        .filter(|function| egraph.backend.table_is_flat(function.backend_id))
        .map(|function| egraph.backend.table_size(function.backend_id))
        .sum()
}

fn egraph_and_proof_node_decl() -> (EGraph, crate::ast::ResolvedFunctionDecl) {
    let mut egraph = EGraph::new_with_proofs();
    egraph.parse_and_run_program(None, PRELUDE).unwrap();
    let decl = egraph
        .functions
        .values()
        .find(|function| is_proof_node(&egraph, function))
        .expect("expected a generated proof-node relation")
        .decl
        .clone();
    (egraph, decl)
}

#[test]
fn only_proof_node_relations_use_flat_storage() {
    let mut egraph = EGraph::new_with_proofs();
    egraph.parse_and_run_program(None, PRELUDE).unwrap();

    let mut flat_proof_nodes = 0;
    let mut keyed_term_nodes = 0;
    for function in egraph.functions.values() {
        let is_flat = egraph.backend.table_is_flat(function.backend_id);
        if is_proof_node(&egraph, function) {
            assert!(is_flat, "{}", function.name());
            assert_eq!(
                function.decl.subtype,
                FunctionSubtype::Custom,
                "{}",
                function.name()
            );
            assert_eq!(function.schema.outputs.len(), 1, "{}", function.name());
            assert_eq!(
                function.schema.outputs[0].name(),
                "Unit",
                "{}",
                function.name()
            );
            assert!(function.decl.merge.is_none(), "{}", function.name());
            assert!(
                function.decl.term_constructor.is_none(),
                "{}",
                function.name()
            );
            assert!(
                function
                    .schema
                    .input
                    .last()
                    .is_some_and(|sort| sort.is_eq_sort()),
                "{}",
                function.name()
            );
            assert!(!function.can_subsume, "{}", function.name());
            flat_proof_nodes += 1;
        } else {
            assert!(!is_flat, "{}", function.name());
            if function.decl.internal_term_node {
                keyed_term_nodes += 1;
            }
        }
    }

    assert!(
        flat_proof_nodes > 0,
        "expected generated proof-node relations"
    );
    assert!(
        keyed_term_nodes > 0,
        "term-node relations should remain on keyed storage"
    );
}

#[test]
#[should_panic(expected = "must be a custom function")]
fn proof_node_storage_rejects_constructor_semantics() {
    let (mut egraph, mut decl) = egraph_and_proof_node_decl();
    decl.name = "invalid-proof-constructor".into();
    decl.subtype = FunctionSubtype::Constructor;
    egraph.declare_function(&decl).unwrap();
}

#[test]
#[should_panic(expected = "cannot declare merge behavior")]
fn proof_node_storage_rejects_merge_semantics() {
    let (mut egraph, mut decl) = egraph_and_proof_node_decl();
    let output_sort = egraph
        .type_info
        .get_sort_by_name(&decl.schema.outputs[0])
        .unwrap()
        .clone();
    decl.name = "invalid-proof-merge".into();
    decl.merge = Some(crate::ast::ResolvedMerge::result_only(
        crate::ast::GenericExpr::Var(
            crate::span!(),
            crate::ast::ResolvedVar {
                name: "old".into(),
                sort: output_sort,
                is_global_ref: false,
            },
        ),
    ));
    egraph.declare_function(&decl).unwrap();
}

#[test]
#[should_panic(expected = "cannot be an FD view")]
fn proof_node_storage_rejects_view_semantics() {
    let (mut egraph, mut decl) = egraph_and_proof_node_decl();
    decl.name = "invalid-proof-view".into();
    decl.term_constructor = Some("unused-constructor".into());
    egraph.declare_function(&decl).unwrap();
}

#[test]
#[should_panic(expected = "must have exactly one Unit output")]
fn proof_node_storage_rejects_non_unit_outputs() {
    let (mut egraph, mut decl) = egraph_and_proof_node_decl();
    decl.name = "invalid-proof-output".into();
    decl.schema.outputs = vec![egraph.proof_state.proof_names.proof_datatype.clone()];
    egraph.declare_function(&decl).unwrap();
}

#[test]
fn proof_node_rows_follow_egraph_push_and_pop() {
    let mut egraph = EGraph::new_with_proofs().with_num_threads(4);
    egraph.parse_and_run_program(None, PRELUDE).unwrap();
    let before_push = flat_row_count(&egraph);
    assert!(before_push > 0);

    egraph.push();
    egraph
        .parse_and_run_program(
            None,
            r#"
            (union (Add (Num 3) (Num 4)) (Add (Num 4) (Num 3)))
            "#,
        )
        .unwrap();
    assert!(flat_row_count(&egraph) > before_push);

    egraph.pop().unwrap();
    assert_eq!(flat_row_count(&egraph), before_push);

    egraph
        .parse_and_run_program(
            None,
            r#"
            (union (Add (Num 5) (Num 6)) (Add (Num 6) (Num 5)))
            (prove (= (Add (Num 5) (Num 6)) (Add (Num 6) (Num 5))))
            "#,
        )
        .unwrap();
    assert!(flat_row_count(&egraph) > before_push);
}

#[test]
fn parallel_rule_matches_append_proof_nodes_without_loss() {
    const SEEDS: usize = 4096;
    let mut source = String::from(
        r#"
        (datatype Math (Num i64) (Add Math Math))
        (relation Seed (i64))

        (rule ((Seed i))
              ((union (Add (Num i) (Num 0)) (Add (Num 0) (Num i))))
              :name "commute-seed")
        "#,
    );
    for seed in 1..=SEEDS {
        writeln!(source, "(Seed {seed})").unwrap();
    }
    source.push_str(
        r#"
        (run 1)
        (prove (= (Add (Num 4096) (Num 0)) (Add (Num 0) (Num 4096))))
        "#,
    );

    let mut egraph = EGraph::new_with_proofs().with_num_threads(4);
    egraph.parse_and_run_program(None, &source).unwrap();
    assert!(
        flat_row_count(&egraph) > SEEDS,
        "parallel proof production should append records for every matched seed"
    );
}
