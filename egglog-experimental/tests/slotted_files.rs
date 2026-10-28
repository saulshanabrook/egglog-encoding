//! Run every slotted fixture; snapshot a small cross-section of the lowering.
use egglog::ast::{Literal, Sexp, parse_sexps};
use egglog_experimental::slotted::{Compiler, Options, new_egraph};
use libtest_mimic::Trial;
use std::{collections::BTreeSet, path::Path};

const SNAPSHOTS: &[&str] = &[
    "datatype.egg",
    "multiple-sorts.egg",
    "named-slots.egg",
    "nested/binder-safe-matching.egg",
    "query-predicates.egg",
];

fn rule_names(source: &str) -> BTreeSet<String> {
    parse_sexps(None, source)
        .unwrap()
        .into_iter()
        .filter_map(|form| {
            let Sexp::List(args, _) = form else {
                return None;
            };
            let Some(Sexp::Atom(head, _)) = args.first() else {
                return None;
            };
            if head != "rewrite" && head != "rule" {
                return None;
            }
            args.windows(2).find_map(|pair| match pair {
                [Sexp::Atom(key, _), Sexp::Literal(Literal::String(name), _)] if key == ":name" => {
                    Some(name.clone())
                }
                [Sexp::Atom(key, _), _] if key == ":name" => panic!("rule names must be quoted"),
                _ => None,
            })
        })
        .collect()
}

fn main() {
    let args = libtest_mimic::Arguments::from_args();
    let crate_root = Path::new(env!("CARGO_MANIFEST_DIR"));
    // Includes resolve from the invocation directory, as in the CLI.
    std::env::set_current_dir(crate_root.parent().unwrap()).unwrap();
    let mut tests = Vec::new();
    let mut named_rules = 0;
    for pattern in [
        "egglog-experimental/tests/slotted/**/*.egg",
        "egglog-experimental/benches/slotted/**/*.egg",
    ] {
        for path in glob::glob(pattern).unwrap() {
            let path = path.unwrap();
            let source = std::fs::read_to_string(&path).unwrap();
            let names = rule_names(&source);
            named_rules += names.len();
            let name = path
                .strip_prefix("egglog-experimental")
                .unwrap()
                .to_str()
                .unwrap()
                .to_owned();
            tests.push(Trial::test(name, move || {
                let mut compiler = Compiler::new(Options {
                    no_aliasing: path.starts_with("egglog-experimental/tests/slotted/nested"),
                    ..Default::default()
                });
                let encoded = compiler.compile(Some(path.display().to_string()), &source)?;
                let emitted_names = rule_names(&encoded);
                assert!(
                    names.is_subset(&emitted_names),
                    "lost source rule names: {:?}",
                    names.difference(&emitted_names).collect::<Vec<_>>()
                );
                new_egraph().parse_and_run_program(Some(path.display().to_string()), &encoded)?;
                if let Ok(local) = path.strip_prefix("egglog-experimental/tests/slotted")
                    && SNAPSHOTS.iter().any(|name| local == Path::new(name))
                {
                    let snapshot = local
                        .to_str()
                        .unwrap()
                        .trim_end_matches(".egg")
                        .replace('/', "__");
                    let mut settings = insta::Settings::clone_current();
                    settings.set_snapshot_path(crate_root.join("tests/slotted/snapshots"));
                    settings.set_prepend_module_to_snapshot(false);
                    settings.set_input_file(&path);
                    settings.bind(|| insta::assert_snapshot!(snapshot, encoded));
                }
                Ok(())
            }));
        }
    }
    assert!(tests.len() >= 46, "missing slotted fixtures");
    assert!(named_rules >= 50, "missing named-rule coverage");

    let guide = include_str!("../src/slotted/LANGUAGE.md");
    let examples = guide
        .split("```slotted\n")
        .skip(1)
        .map(|block| block.split("```").next().unwrap())
        .collect::<Vec<_>>();
    assert!(!examples.is_empty(), "no public language examples");
    for predicate in [
        "=",
        "!=",
        "renaming-=",
        "renaming-!=",
        "free",
        "not-free",
        "free-names-are",
    ] {
        assert!(
            examples
                .iter()
                .any(|s| s.contains(&format!("({predicate} "))),
            "no example of {predicate}"
        );
    }
    for (i, source) in examples.into_iter().enumerate() {
        tests.push(Trial::test(format!("language-doc/{i}"), move || {
            let encoded = Compiler::default().compile(None, source)?;
            new_egraph().parse_and_run_program(None, &encoded)?;
            Ok(())
        }));
    }
    libtest_mimic::run(&args, tests).exit();
}
