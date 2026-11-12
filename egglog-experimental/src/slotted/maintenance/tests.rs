use super::*;
use crate::slotted::syntax;
use egglog::ast::{Command, Parser};
use std::collections::BTreeSet;

fn check_declarations(generated: &Generated) {
    let emitted: BTreeSet<_> = syntax::parse(None, &generated.source)
        .unwrap()
        .into_iter()
        .filter_map(|(form, _)| {
            let (head, args) = form.call().unwrap();
            matches!(
                head,
                "sort" | "constructor" | "function" | "relation" | "ruleset"
            )
            .then(|| args[0].atom().unwrap().to_owned())
        })
        .collect();
    let recorded: BTreeSet<_> = generated.declarations.iter().cloned().collect();
    assert_eq!(recorded.len(), generated.declarations.len());
    assert_eq!(recorded, emitted);
}

#[test]
fn generated_declaration_metadata_covers_both_encodings() {
    check_declarations(&shared());
    let symbols = Symbols::new("Carrier", 3);
    for proofs in [false, true] {
        check_declarations(&carrier(&symbols, proofs));
        for columns in [
            vec![],
            vec![Column::Payload("String".into())],
            vec![Column::Var],
            vec![Column::Child, Column::Payload("i64".into()), Column::Child],
            vec![Column::Child, Column::Binder, Column::Binder, Column::Child],
        ] {
            let generated = constructor(
                &Constructor {
                    name: "_Node".into(),
                    sort: symbols.sort.clone(),
                    columns,
                },
                &symbols,
                proofs,
            );
            check_declarations(&generated);
            // Check the actual egglog AST: every rule still has its machinery
            // phase and namespaced variables, including dynamic binder names.
            for command in Parser::default()
                .get_program_from_string(None, &generated.source)
                .unwrap()
            {
                if let Command::Rule { rule } = command {
                    assert!(rule.ruleset.starts_with("slotted"), "{}", rule.name);
                    let mut check = |_: &_, name: &String| {
                        assert!(name.starts_with('_'), "{}: {name}", rule.name);
                    };
                    for fact in &rule.body {
                        fact.visit_vars(&mut check);
                    }
                    rule.head.visit_vars(&mut check);
                }
            }
        }
    }
}
