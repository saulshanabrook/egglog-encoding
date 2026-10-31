//! Rigid names and carrier-specific variable constructors.
use egglog_experimental::slotted::{
    Compiler, Options, ProofMode, new_egraph, new_egraph_with_proofs,
};

#[test]
fn variable_equalities_do_not_cross_carriers() {
    let source = r#"
        (datatype A (VA Var) (Lam Var A :binder 0))
        (datatype B (VB Var))
        (let a $a)
        (let b $b)
        (let left (VB a))
        (let right (VB b))
        (union (VA a) (VA b))
        (check (= (VA a) (VA b)))
        (check (!= left right))
        (fail (check (= left right)))
        (let identity (Lam $bound (VA $bound)))
        (check (= identity (Lam $renamed (VA $renamed))))
    "#;
    check(source);
}

fn check(source: &str) {
    for proof_mode in [ProofMode::Disabled, ProofMode::Prove] {
        let encoded = Compiler::new(Options {
            proof_mode,
            ..Options::default()
        })
        .compile(None, source)
        .unwrap();
        let mut graph = if proof_mode == ProofMode::Prove {
            new_egraph_with_proofs()
        } else {
            new_egraph()
        };
        graph.parse_and_run_program(None, &encoded).unwrap();
        if proof_mode == ProofMode::Disabled {
            egglog_experimental::slotted::export::export(&graph).unwrap();
        }
    }
}

#[test]
fn bare_names_cannot_be_used_as_carrier_equalities() {
    for command in [
        "(union $a $b)",
        "(rewrite $a $b)",
        "(rewrite (V $a) $b)",
        "(union (V $a) $b)",
        "(check (= (V $a) $b))",
    ] {
        let source = format!("(datatype Math (V Var)) {command}");
        assert!(
            Compiler::default().compile(None, &source).is_err(),
            "{command}"
        );
    }
}

#[test]
fn builtin_var_sort_name_is_reserved() {
    let error = Compiler::default()
        .compile(None, "(datatype Math (Var Var))")
        .unwrap_err();
    assert!(error.to_string().contains("reserved"));
}

#[test]
fn a_concrete_global_binder_keeps_its_name() {
    check(
        r#"
        (datatype Math (V Var) (Wrap Math) (Lam Var Math :binder 0))
        (let binder $a)
        (let input (Wrap (V binder)))
        (rewrite (Wrap e) (Lam binder e))
        (run 1)
        (check (= input (Lam $bound (V $bound))))
    "#,
    );
}
