use egglog::{EGraph, Error};

#[test]
fn shape_primitives_do_not_depend_on_sort_declaration_order() -> Result<(), Error> {
    let declarations = [
        "(sort Renamings (Vec Renaming)) (sort Group (Set Renaming)) (sort Groups (Vec Group))",
        "(sort Group (Set Renaming)) (sort Renamings (Vec Renaming)) (sort Groups (Vec Group))",
        "(sort Group (Set Renaming)) (sort Groups (Vec Group)) (sort Renamings (Vec Renaming))",
    ];
    for declarations in declarations {
        let mut eg = EGraph::default();
        eg.parse_and_run_program(
            None,
            &format!(
                r#"
(sort Renaming (Map i64 i64))
{declarations}
(let $shape (node-shape (vec-of (map-of 0 5)) (vec-of (set-of (map-of 0 0)))))
(check (= (vec-get $shape 0) (map-of 0 0)))
(check (= (vec-get $shape 1) (map-of 0 5)))
(check (= (set-length (symmetries-of $shape 2)) 0))
; Another vector over the same group must not duplicate symmetries-of.
(sort MoreGroups (Vec Group))
(check (= (set-length (symmetries-of $shape 2)) 0))
"#
            ),
        )?;
    }
    Ok(())
}

#[test]
fn class_slot_bindings_reject_non_identity_maps() -> Result<(), Error> {
    let mut eg = EGraph::default();
    eg.parse_and_run_program(
        None,
        r#"
(sort Renaming (Map i64 i64))
(fail (let $bad (root "p" (map-of 0 1))))
(check (= (root "p" (map-of 0 0)) (root "p" (map-of 0 0))))
"#,
    )?;
    Ok(())
}
