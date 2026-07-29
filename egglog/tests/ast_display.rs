use egglog::{EGraph, ast::Command};

#[test]
fn datatype_variant_unextractable_round_trips_through_display() {
    let mut egraph = EGraph::default();
    let commands = egraph
        .parse_program(None, "(datatype Math (Hidden i64 :unextractable))")
        .unwrap();
    let rendered = commands
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>()
        .join("\n");
    let reparsed = egraph.parse_program(None, &rendered).unwrap();

    let Command::Datatype { variants, .. } = &reparsed[0] else {
        panic!("display changed the datatype command kind");
    };
    assert!(
        variants[0].unextractable,
        "display dropped :unextractable from a datatype variant"
    );
}
