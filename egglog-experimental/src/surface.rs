use egglog::ast::{Expr, Fact, ParseError, Sexp, Span, parse_sexps};

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Form {
    Atom(String),
    List(Vec<Form>),
}

impl Form {
    pub fn from_expr(expr: &Expr) -> Self {
        match expr {
            Expr::Var(_, name) => Self::Atom(name.clone()),
            Expr::Lit(_, lit) => Self::Atom(lit.to_string()),
            Expr::Call(_, head, args) => Self::List(
                std::iter::once(Self::Atom(head.clone()))
                    .chain(args.iter().map(Self::from_expr))
                    .collect(),
            ),
        }
    }

    pub fn from_fact(fact: &Fact) -> Self {
        match fact {
            Fact::Eq(_, lhs, rhs) => Self::List(vec![
                Self::Atom("=".into()),
                Self::from_expr(lhs),
                Self::from_expr(rhs),
            ]),
            Fact::Fact(expr) => Self::from_expr(expr),
        }
    }

    pub fn expr(&self) -> Result<Expr, String> {
        source_expr(&self.sexp().map_err(|e| e.to_string())?).map_err(|e| e.to_string())
    }

    pub fn fact(&self) -> Result<Fact, String> {
        match self.call() {
            Ok(("=", [lhs, rhs])) => Ok(Fact::Eq(egglog::span!(), lhs.expr()?, rhs.expr()?)),
            Ok(("=", _)) => Err("an equality needs two operands".into()),
            _ => Ok(Fact::Fact(self.expr()?)),
        }
    }

    pub fn sexp(&self) -> Result<Sexp<'_>, ParseError> {
        match self {
            Self::Atom(atom) => Ok(parse_sexps(None, atom)?.remove(0)),
            Self::List(items) => Ok(Sexp::List(
                items.iter().map(Self::sexp).collect::<Result<_, _>>()?,
                egglog::span!(),
            )),
        }
    }
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

// Surface identifiers are preserved verbatim, including `_` and class variables
// that share a spelling with an egglog command.
pub(crate) fn source_expr(source: &Sexp<'_>) -> Result<Expr, ParseError> {
    match source {
        Sexp::Atom(name, span) => Ok(Expr::Var(span.clone(), name.to_string())),
        Sexp::Literal(literal, span) => Ok(Expr::Lit(span.clone(), literal.clone())),
        Sexp::List(items, span) => {
            let Some((Sexp::Atom(head, _), args)) = items.split_first() else {
                return Err(ParseError(
                    span.clone(),
                    "expected a source expression".into(),
                ));
            };
            Ok(Expr::Call(
                span.clone(),
                head.to_string(),
                args.iter().map(source_expr).collect::<Result<_, _>>()?,
            ))
        }
    }
}

pub(crate) fn convert(s: &Sexp<'_>) -> Form {
    match s {
        Sexp::Atom(a, _) => Form::Atom(a.to_string()),
        Sexp::Literal(egglog::ast::Literal::String(s), _) => Form::Atom(quote(s)),
        Sexp::Literal(l, _) => Form::Atom(l.to_string()),
        Sexp::List(xs, _) => Form::List(xs.iter().map(convert).collect()),
    }
}

pub(crate) fn parse(
    filename: Option<String>,
    source: &str,
) -> Result<Vec<(Form, Span)>, ParseError> {
    Ok(parse_sexps(filename, source)?
        .into_iter()
        .map(|s| {
            let span = s.span();
            (convert(&s), span)
        })
        .collect())
}

pub(crate) fn quote(s: &str) -> String {
    egglog::ast::Literal::String(s.into()).to_string()
}

use std::collections::BTreeSet;

pub(crate) fn read(
    filename: Option<String>,
    source: &str,
    active: &mut BTreeSet<std::path::PathBuf>,
) -> Result<Vec<(Form, Span)>, ParseError> {
    expand_includes(parse(filename, source)?, active)
}

pub(crate) fn expand_includes(
    forms: Vec<(Form, Span)>,
    active: &mut BTreeSet<std::path::PathBuf>,
) -> Result<Vec<(Form, Span)>, ParseError> {
    let mut out = Vec::new();
    for (form, span) in forms {
        if let Ok(("include", [arg])) = form.call() {
            let file = unquote(arg.atom().map_err(|e| ParseError(span.clone(), e))?)
                .map_err(|e| ParseError(span.clone(), e))?;
            let path = std::fs::canonicalize(&file)
                .map_err(|e| ParseError(span.clone(), format!("include {file}: {e}")))?;
            if !active.insert(path.clone()) {
                return Err(ParseError(span, format!("recursive include {file}")));
            }
            let text = std::fs::read_to_string(&path)
                .map_err(|e| ParseError(span.clone(), format!("include {file}: {e}")))?;
            out.extend(read(Some(file), &text, active)?);
            active.remove(&path);
        } else {
            out.push((form, span));
        }
    }
    Ok(out)
}

pub(crate) fn declarations(
    f: &Form,
    sorts: &mut Vec<String>,
    ctors: &mut Vec<Form>,
) -> Result<(), String> {
    let (head, args) = f.call()?;
    match head {
        "sort" if args.len() == 1 => sorts.push(args[0].symbol()?.into()),
        "constructor" => ctors.push(f.clone()),
        "datatype" => {
            let (name, variants) = args.split_first().ok_or("datatype needs a sort name")?;
            sorts.push(name.symbol()?.into());
            for v in variants {
                let (ctor, cols) = v.call()?;
                let split = cols
                    .iter()
                    .position(|f| matches!(f,Form::Atom(s) if s.starts_with(':')))
                    .unwrap_or(cols.len());
                let mut parts = vec![
                    Form::Atom("constructor".into()),
                    Form::Atom(ctor.into()),
                    Form::List(cols[..split].to_vec()),
                    name.clone(),
                ];
                parts.extend_from_slice(&cols[split..]);
                ctors.push(Form::List(parts));
            }
        }
        "datatype*" => {
            for f in args {
                let mut parts = vec![Form::Atom("datatype".into())];
                parts.extend_from_slice(f.list()?);
                declarations(&Form::List(parts), sorts, ctors)?;
            }
        }
        _ => {}
    }
    Ok(())
}

pub(crate) fn unquote(s: &str) -> Result<String, String> {
    if !s.starts_with('"') {
        return Ok(s.into());
    }
    let expr = egglog::ast::Parser::default()
        .get_expr_from_string(None, s)
        .map_err(|e| e.to_string())?;
    if let egglog::ast::Expr::Lit(_, egglog::ast::Literal::String(s)) = expr {
        Ok(s)
    } else {
        Err("expected a string".into())
    }
}
