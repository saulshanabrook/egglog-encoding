//! A missing join must break the intended source assertion, not merely fail to compile.
use egglog::{
    Error,
    ast::{Command, Sexp, parse_sexps},
};
use egglog_experimental::slotted::{Compiler, new_egraph};

#[test]
fn multipattern_assertions_detect_missing_joins() {
    let mutations: &[(&str, &str, &str, &[&str])] = &[
        (
            "beta premise unjoined from the function",
            ":when ((= f (Lam $v body)))\n         :name \"beta-guarded\"",
            ":when ((= zz (Lam $v body)))\n         :name \"beta-guarded\"",
            &["stuck"],
        ),
        (
            "load-after-store no longer joins on the address",
            ":when ((= m (Store m0 p v)))",
            ":when ((= m (Store m0 pp v)))",
            &["other"],
        ),
        (
            "double-product no longer joins the two factor pairs",
            "(= r (Mul a b))",
            "(= r (Mul aa bb))",
            &["no"],
        ),
        (
            "double-product's top pattern unjoined from the match",
            "(= e (Add l r))",
            "(= ee (Add l r))",
            &["no", "no2"],
        ),
        (
            "two-literals-two-slots spelled with one literal, so the two bound slots are one name",
            "(= g (Lam $y body)))\n         :name \"two-literals-two-slots\"",
            "(= g (Lam $x body)))\n         :name \"two-literals-two-slots\"",
            &["two-names"],
        ),
        (
            "same-body no longer shares the body",
            "(= g (Lam $w body))",
            "(= g (Lam $w body2))",
            &["q"],
        ),
        (
            "eta's shape premise unjoined from the function",
            "(= f (Lam $w g))",
            "(= zz (Lam $w g))",
            &["notlam"],
        ),
        (
            "eta's slot side condition dropped",
            "(not-free $v f)\n                ",
            "",
            &["held"],
        ),
        (
            "cross-product loses its third disconnected pattern",
            "\n                (= r (Store s1 s2 s3))",
            "",
            &["root2"],
        ),
        (
            "cross-slots stops asking the Add's children to be one slot",
            "(= r (Add $u $u))",
            "(= r (Add $u $u2))",
            &["root3", "root4"],
        ),
        (
            "abstract-constant takes its argument from the OTHER lambda",
            "(App (Lam $n (Lam $x (Add $x $n))) a)",
            "(App (Lam $n (Lam $x (Add $x $n))) b)",
            &["f2"],
        ),
        (
            "the payload join stops asking for one number",
            "(= y (Num i))",
            "(= y (Num j))",
            &["mixed"],
        ),
        (
            "abstract-constant stops asking the two constants to differ",
            "(= other (Lam $y (Add $y b)))\n                (!= a b))",
            "(= other (Lam $y (Add $y b))))",
            &["lone"],
        ),
    ];
    let source = include_str!("slotted/multipattern.egg");
    for &(name, old, new, expected) in mutations {
        let source = replace_code(source, old, new);
        let source = source.replace(
            "egglog-experimental/",
            &format!("{}/", env!("CARGO_MANIFEST_DIR")),
        );
        let claims = parse_sexps(None, &source)
            .unwrap()
            .into_iter()
            .filter_map(claim_name)
            .collect::<Vec<_>>();
        let encoded = Compiler::default().compile(None, &source).unwrap();
        let mut graph = new_egraph();
        let commands = graph.parse_program(None, &encoded).unwrap();
        let mut claim = 0;
        let mut broken = None;
        for command in commands {
            let is_check = matches!(command, Command::Check(..) | Command::Fail(..));
            match graph.run_program(vec![command]) {
                Ok(_) => {}
                Err(Error::CheckError(..) | Error::ExpectFail(..)) if is_check => {
                    broken = Some(claims[claim].as_str());
                    break;
                }
                Err(e) => panic!("{name}: failed for the wrong reason: {e}"),
            }
            if is_check {
                claim += 1;
            }
        }
        assert!(
            broken.is_some_and(|got| expected.contains(&got)),
            "{name}: broke {broken:?}, expected {expected:?}"
        );
    }
}

fn claim_name(form: Sexp) -> Option<String> {
    let Sexp::List(mut xs, _) = form else {
        return None;
    };
    let Sexp::Atom(head, _) = &xs[0] else {
        return None;
    };
    match head.as_str() {
        "fail" => claim_name(xs.remove(1)),
        "check" => {
            let Sexp::List(fact, _) = xs.remove(1) else {
                panic!("invalid check")
            };
            fact.into_iter().skip(1).find_map(|x| match x {
                Sexp::Atom(s, _) if !s.starts_with('$') => Some(s),
                _ => None,
            })
        }
        _ => None,
    }
}

/// Comments quote the same rules; only executable occurrences are mutations.
fn replace_code(source: &str, old: &str, new: &str) -> String {
    let mut masked = source.as_bytes().to_vec();
    let mut comment = false;
    for byte in &mut masked {
        if *byte == b'\n' {
            comment = false;
        }
        if *byte == b';' {
            comment = true;
        }
        if comment {
            *byte = 0;
        }
    }
    let masked = String::from_utf8(masked).unwrap();
    let matches = masked
        .match_indices(old)
        .map(|(i, _)| i)
        .collect::<Vec<_>>();
    assert!(!matches.is_empty(), "stale mutation: {old}");
    let mut result = source.to_owned();
    for i in matches.into_iter().rev() {
        result.replace_range(i..i + old.len(), new);
    }
    result
}
