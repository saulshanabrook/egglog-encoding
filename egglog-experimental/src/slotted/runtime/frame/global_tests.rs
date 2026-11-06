use super::{Binding, Frame, Reading, Renaming};

fn literal(name: &str, slot: i64) -> Binding {
    Binding::Lit {
        name: name.into(),
        edge: Renaming::from([(0, slot)]),
        carried: true,
    }
}

fn root(name: &str, slots: &[i64]) -> Binding {
    Binding::Root {
        var: name.into(),
        free_vars: slots.iter().copied().collect(),
        reading: Reading::Identity,
    }
}

#[test]
fn global_aliases_share_their_concrete_coordinate() {
    let frame = Frame::globals("globals", &[literal("first", 17), literal("alias", 17)])
        .unwrap()
        .anchored("globals")
        .unwrap();
    assert_eq!(frame.ren("first"), Some(Renaming::from([(0, 17)])));
    assert_eq!(frame.ren("alias"), frame.ren("first"));
    assert!(frame.ren("missing").is_none());
}

#[test]
fn concrete_slots_can_match_pattern_slot_literals() {
    let globals = Frame::globals("globals", &[literal("fixed", 17)]).unwrap();
    let pattern = Frame::atom("pattern", &[root("term", &[0]), literal("$pattern", 0)]).unwrap();
    let joined = globals.join(&pattern).unwrap();
    let refinements = joined.refinements();
    assert!(
        refinements
            .iter()
            .any(|frame| frame.ren("fixed") == frame.ren("$pattern"))
    );
    assert!(
        refinements
            .iter()
            .any(|frame| frame.ren("fixed") != frame.ren("$pattern"))
    );

    let pinned = Frame::atom(
        "pattern",
        &[
            root("term", &[0]),
            literal("fixed", 0),
            literal("$pattern", 0),
        ],
    )
    .unwrap();
    let pinned = globals.join(&pinned).unwrap().anchored("globals").unwrap();
    assert_eq!(pinned.ren("$pattern"), Some(Renaming::from([(0, 17)])));
}

#[test]
fn different_global_coordinates_stay_apart() {
    let globals = Frame::globals("globals", &[literal("left", 17), literal("right", 19)]).unwrap();
    assert!(
        globals
            .refinements()
            .iter()
            .all(|frame| frame.ren("left") != frame.ren("right"))
    );
    let identified = Frame::atom(
        "pattern",
        &[root("term", &[0]), literal("left", 0), literal("right", 0)],
    )
    .unwrap();
    assert!(globals.join(&identified).is_none());

    // Query-local slot literals still obey their own distinct-name contract.
    assert!(
        Frame::atom(
            "pattern",
            &[root("term", &[0]), literal("$x", 0), literal("$y", 0)]
        )
        .is_none()
    );
}

#[test]
fn unicode_global_labels_work_in_frames_and_source_queries() {
    let frame = Frame::globals("globals", &[literal("λ", 23), literal("变量", 23)])
        .unwrap()
        .anchored("globals")
        .unwrap();
    assert_eq!(frame.ren("λ"), Some(Renaming::from([(0, 23)])));
    assert_eq!(frame.ren("变量"), frame.ren("λ"));

    let source = r#"
(datatype U (V Var) (F U))
(let λ $a)
(let 变量 λ)
(let value (F (V λ)))
(check (= value (F (V 变量))))
(check (= value (F (V $pattern))))
"#;
    let program = crate::slotted::Compiler::default()
        .compile(None, source)
        .unwrap();
    crate::slotted::new_egraph()
        .parse_and_run_program(None, &program)
        .unwrap();
}
