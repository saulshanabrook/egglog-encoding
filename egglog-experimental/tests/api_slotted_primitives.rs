use egglog::{EGraph, Error};

#[test]
fn runtime_registration_is_isolated_from_ordinary_egglog() -> Result<(), Error> {
    let mut ordinary = EGraph::default();
    ordinary.parse_and_run_program(None, "(sort Frame) (sort Binding) (sort Names)")?;
    assert!(
        ordinary
            .parse_and_run_program(None, "(let f (frame))")
            .is_err()
    );
    let mut eg = egglog_experimental::slotted::new_egraph();
    eg.parse_and_run_program(
        None,
        r#"
(let $shape (node-shape (vec-of (map-of 0 5)) (vec-of (set-of (map-of 0 0)))))
(check (= (vec-get $shape 0) (map-of 0 0)))
(check (= (vec-get $shape 1) (map-of 0 5)))
(check (= (set-length (symmetries-of $shape 2)) 0))
; Ordinary container declarations do not register duplicate slotted overloads.
(sort MoreGroups (Vec Group))
(check (= (set-length (symmetries-of $shape 2)) 0))
"#,
    )?;
    Ok(())
}

#[test]
fn renaming_primitives() -> Result<(), Error> {
    egglog_experimental::slotted::new_egraph()
        .parse_and_run_program(None, include_str!("fixtures/slotted-primitives.egg"))?;
    Ok(())
}

#[test]
fn class_slot_bindings_reject_non_identity_maps() -> Result<(), Error> {
    let mut eg = egglog_experimental::slotted::new_egraph();
    eg.parse_and_run_program(
        None,
        r#"
(fail (root "p" (map-of 0 1)))
(check (= (root "p" (map-of 0 0)) (root "p" (map-of 0 0))))
"#,
    )?;
    Ok(())
}

#[test]
fn coset_reps_are_a_vector_sorted_by_content() -> Result<(), Error> {
    let mut eg = egglog_experimental::slotted::new_egraph();
    eg.parse_and_run_program(
        None,
        r#"
; S3 on {0, 1, 2}: pinning slot 0 leaves one representative per preimage of 0
(let $grp (group-close (set-of (map-of 0 1 1 0 2 2) (map-of 0 1 1 2 2 0))))
(check (= (set-length $grp) 6))
(let $reps (group-coset-reps $grp (map-of 0 0)))
(check (= (vec-length $reps) 3))
(check (= (vec-get $reps 0) (map-of 0 0 1 1 2 2)))
(check (= (vec-get $reps 1) (map-of 0 1 1 0 2 2)))
(check (= (vec-get $reps 2) (map-of 0 1 1 2 2 0)))
"#,
    )?;
    Ok(())
}
