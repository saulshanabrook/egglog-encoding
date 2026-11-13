pub(super) use crate::surface::{Form, convert, parse, quote};

/// Machinery variables use a separate namespace from source declarations.
pub(super) fn machinery(source: &str) -> String {
    fn prefix(f: &mut Form, operator: bool) {
        match f {
            Form::Atom(s)
                if !operator && !s.starts_with(['"', ':']) && s.parse::<i64>().is_err() =>
            {
                *s = format!("_{s}")
            }
            Form::List(xs) => {
                let mut keyword = false;
                for (i, x) in xs.iter_mut().enumerate() {
                    let next = matches!(x,Form::Atom(s) if [":ruleset",":name",":when",":subsume"].contains(&s.as_str()));
                    prefix(x, i == 0 || keyword);
                    keyword = next;
                }
            }
            _ => {}
        }
    }
    parse(None, source)
        .expect("generated machinery syntax")
        .into_iter()
        .map(|(mut f, _)| {
            if let Form::List(xs) = &mut f
                && xs.first() == Some(&Form::Atom("rule".into()))
            {
                if !xs.contains(&Form::Atom(":ruleset".into())) {
                    xs.extend([Form::Atom(":ruleset".into()), Form::Atom("slotted".into())]);
                }
                prefix(&mut f, false);
            }
            f.render()
        })
        .collect::<Vec<_>>()
        .join("\n")
}
