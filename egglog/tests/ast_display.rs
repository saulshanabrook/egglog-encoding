use egglog::{EGraph, ast::Command, ast::Literal};

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

#[test]
fn string_literal_display_round_trips_every_unescaped_control() {
    let value = "quote\" slash\\ newline\n tab\t cr\r nul\0 snowman ☃";
    let program = format!("(let $text {})", Literal::String(value.into()));
    let mut egraph = EGraph::default();
    let commands = egraph.parse_program(None, &program).unwrap();
    let rendered = commands[0].to_string();
    let reparsed = egraph.parse_program(None, &rendered).unwrap();

    assert_eq!(reparsed[0].to_string(), rendered);
}
