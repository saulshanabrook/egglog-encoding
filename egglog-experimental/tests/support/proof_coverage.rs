use egglog::ast::{Literal, Sexp, parse_sexps};
use std::collections::BTreeSet;

type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;

#[derive(Clone, Default)]
struct Scope {
    constructors: BTreeSet<String>,
}

fn call<'a, 'src>(form: &'a Sexp<'src>) -> Option<(&'a str, &'a [Sexp<'src>])> {
    let Sexp::List(items, _) = form else {
        return None;
    };
    let (Sexp::Atom(head, _), args) = items.split_first()? else {
        return None;
    };
    Some((head, args))
}

fn read(source: &str) -> Result<String> {
    let mut forms = String::new();
    for form in parse_sexps(None, source)? {
        if let Some(("include", [Sexp::Literal(Literal::String(path), _)])) = call(&form) {
            forms.push_str(&read(&std::fs::read_to_string(path)?)?);
        } else {
            forms.push_str(form.span().string());
            forms.push('\n');
        }
    }
    Ok(forms)
}

impl Scope {
    fn datatype(&mut self, variants: &[Sexp]) {
        for variant in variants {
            if let Some((name, _)) = call(variant) {
                self.constructors.insert(name.into());
            }
        }
    }

    fn declare(&mut self, form: &Sexp) {
        match call(form) {
            Some(("constructor", [Sexp::Atom(name, _), ..])) => {
                self.constructors.insert(name.to_string());
            }
            Some(("datatype", [_, variants @ ..])) => self.datatype(variants),
            Some(("datatype*", datatypes)) => {
                let datatypes = match datatypes {
                    [Sexp::List(nested, _)] if call(&datatypes[0]).is_none() => nested.as_slice(),
                    other => other,
                };
                for datatype in datatypes {
                    if let Some((_, variants)) = call(datatype) {
                        self.datatype(variants);
                    }
                }
            }
            _ => {}
        }
    }
}

/// Count supported positive claims from source, independently of proof emission.
pub fn expected_proofs(source: &str) -> Result<usize> {
    let source = read(source)?;
    let forms = parse_sexps(None, &source)?;
    let mut scope = Scope::default();
    let mut scopes = Vec::new();
    let mut region_start = 0;
    let mut count = 0;
    for (i, form) in forms.iter().enumerate() {
        if i == region_start {
            // Source declarations are hoisted within regions delimited by push/pop.
            for declaration in forms[i..]
                .iter()
                .take_while(|form| !matches!(call(form), Some(("push" | "pop", _))))
            {
                scope.declare(declaration);
            }
        }
        match call(form) {
            Some(("push", [])) => {
                scopes.push(scope.clone());
                region_start = i + 1;
            }
            Some(("pop", [])) => {
                scope = scopes.pop().ok_or("pop without push")?;
                region_start = i + 1;
            }
            Some(("extract", [_])) => count += 1,
            Some(("check", facts)) if !facts.is_empty() => {
                if facts.iter().all(|fact| match call(fact) {
                    Some(("=" | "renaming-=", [_, _])) => true,
                    Some(("known-disequal", [_, _]) | ("contradiction", [])) => true,
                    Some(("__internal-holds", [_, Sexp::Atom(ctor, _)])) => {
                        scope.constructors.contains(ctor.as_ref())
                    }
                    Some((head, _)) => scope.constructors.contains(head),
                    _ => false,
                }) {
                    count += 1;
                }
            }
            _ => {}
        }
    }
    Ok(count)
}
