use egglog::ast::{ParseError, Sexp, Span, parse_sexps};

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum Form {
    Atom(String),
    List(Vec<Form>),
}

impl Form {
    pub fn atom(&self) -> Result<&str, String> {
        match self {
            Self::Atom(s) => Ok(s),
            _ => Err("expected an atom".into()),
        }
    }
    pub fn list(&self) -> Result<&[Form], String> {
        match self {
            Self::List(xs) => Ok(xs),
            _ => Err("expected a list".into()),
        }
    }
    pub fn symbol(&self) -> Result<&str, String> {
        let s = self.atom()?;
        if s.starts_with('"') || s.parse::<f64>().is_ok() || matches!(s, "true" | "false") {
            return Err(format!("expected an identifier, got {s}"));
        }
        Ok(s)
    }
    pub fn call(&self) -> Result<(&str, &[Form]), String> {
        let (head, args) = self.list()?.split_first().ok_or("expected a call")?;
        Ok((head.symbol()?, args))
    }
    pub fn render(&self) -> String {
        match self {
            Self::Atom(s) => s.clone(),
            Self::List(xs) => format!(
                "({})",
                xs.iter().map(Self::render).collect::<Vec<_>>().join(" ")
            ),
        }
    }
}

fn convert(s: Sexp) -> Form {
    match s {
        Sexp::Atom(a, _) => Form::Atom(a),
        Sexp::Literal(egglog::ast::Literal::String(s), _) => Form::Atom(quote(&s)),
        Sexp::Literal(l, _) => Form::Atom(l.to_string()),
        Sexp::List(xs, _) => Form::List(xs.into_iter().map(convert).collect()),
    }
}

pub(super) fn parse(
    filename: Option<String>,
    source: &str,
) -> Result<Vec<(Form, Span)>, ParseError> {
    Ok(parse_sexps(filename, source)?
        .into_iter()
        .map(|s| {
            let span = s.span();
            (convert(s), span)
        })
        .collect())
}

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

pub(super) fn quote(s: &str) -> String {
    egglog::ast::Literal::String(s.into()).to_string()
}
