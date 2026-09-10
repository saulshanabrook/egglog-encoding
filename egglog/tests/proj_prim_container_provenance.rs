use egglog::sort::VecContainer;
use egglog::{EGraph, add_primitive_with_validator};

#[test]
fn proj_prim_uses_the_typed_container_argument() {
    let mut egraph = EGraph::new_with_proofs();
    egraph
        .parse_and_run_program(
            None,
            r#"
            (datatype N (Z) (S N))
            (sort MN (Map N N))
            (relation Has (MN))
            (relation Seen (N))
            (let $key (S (Z)))
            (Has (map-insert (map-empty) $key (Z)))

            ; `$key` is a non-container argument that also contains the result.
            (rule ((Has m)
                   (= z (map-get m $key)))
                  ((Seen z))
                  :name "map-get-with-decoy")

            (run 1)
            (prove (Seen (Z)))
            "#,
        )
        .unwrap();
}

#[test]
fn proj_prim_builds_projection_chain_through_nested_containers() {
    let mut egraph = EGraph::new_with_proofs();
    egraph
        .parse_and_run_program(
            None,
            "(datatype N (Z)) (sort Ns (Vec N)) (sort Nss (Vec Ns))",
        )
        .unwrap();

    let outer_sort = egraph.get_sort_by_name("Nss").unwrap().clone();
    let element_sort = egraph.get_sort_by_name("N").unwrap().clone();
    add_primitive_with_validator!(
        &mut egraph,
        "deep-first" = |xss: @VecContainer (outer_sort)| -?> # (element_sort) {{
            let xs = state
                .container_values()
                .get_val::<VecContainer>(*xss.data.first()?)?;
            xs.data.first().copied()
        }},
        |dag: &mut TermDag, args: &[TermId]| {
            let Term::App(_, outer) = dag.get(*args.first()?) else {
                return None;
            };
            let Term::App(_, inner) = dag.get(*outer.first()?) else {
                return None;
            };
            inner.first().copied()
        }
    );

    egraph
        .parse_and_run_program(
            None,
            r#"
            (relation Has (Nss))
            (relation Seen (N))
            (Has (vec-of (vec-of (Z))))

            (rule ((Has xss)
                   (= z (deep-first xss)))
                  ((Seen z))
                  :name "deep-first")

            (run 1)
            (prove (Seen (Z)))
            "#,
        )
        .unwrap();
}
