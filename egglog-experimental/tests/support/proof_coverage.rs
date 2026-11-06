use egglog::ast::{Literal, Sexp, parse_sexps};
use std::collections::{BTreeMap, BTreeSet};

type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;

#[derive(Clone, Default)]
struct Scope {
    globals: BTreeSet<String>,
    // A payload argument must be a literal, even when its name denotes a global elsewhere.
    constructors: BTreeMap<String, Vec<bool>>,
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
    fn constructor(&mut self, name: &str, inputs: &[Sexp]) {
        let columns = inputs.iter().take_while(|input| !matches!(input, Sexp::Atom(name, _) if name.starts_with(':')))
            .map(|input| matches!(input, Sexp::Atom(sort, _) if matches!(sort.as_ref(), "i64" | "String"))).collect();
        self.constructors.insert(name.into(), columns);
    }

    fn datatype(&mut self, variants: &[Sexp]) {
        for variant in variants {
            if let Some((name, inputs)) = call(variant) {
                self.constructor(name, inputs);
            }
        }
    }

    fn declare(&mut self, form: &Sexp) {
        match call(form) {
            Some(("constructor", [Sexp::Atom(name, _), Sexp::List(inputs, _), ..])) => {
                self.constructor(name, inputs)
            }
            Some(("datatype", [_, variants @ ..])) => self.datatype(variants),
            Some(("datatype*", [Sexp::List(datatypes, _)])) => {
                for datatype in datatypes {
                    if let Some((_, variants)) = call(datatype) {
                        self.datatype(variants);
                    }
                }
            }
            _ => {}
        }
    }

    fn ground(&self, expr: &Sexp) -> bool {
        match expr {
            Sexp::Atom(name, _) => name.starts_with('$') || self.globals.contains(name.as_ref()),
            Sexp::Literal(..) => true,
            Sexp::List(..) => {
                let Some((head, args)) = call(expr) else {
                    return false;
                };
                let columns = self
                    .constructors
                    .get(head)
                    .expect("compiled source declares its constructors");
                args.iter().zip(columns).all(|(arg, payload)| {
                    if *payload {
                        matches!(arg, Sexp::Literal(..))
                    } else {
                        self.ground(arg)
                    }
                })
            }
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
            Some(("let", [Sexp::Atom(name, _), _])) => {
                scope.globals.insert(name.to_string());
            }
            Some(("push", [])) => {
                scopes.push(scope.clone());
                region_start = i + 1;
            }
            Some(("pop", [])) => {
                scope = scopes.pop().ok_or("pop without push")?;
                region_start = i + 1;
            }
            Some(("check", [fact])) => {
                match call(fact) {
                    Some(("=" | "renaming-=", [lhs, rhs]))
                        if scope.ground(lhs) && scope.ground(rhs) =>
                    {
                        count += 1
                    }
                    // Internal existence sugar yields an equality for nullary constructors.
                    Some(("__internal-holds", [term, Sexp::Atom(ctor, _)]))
                        if scope
                            .constructors
                            .get(ctor.as_ref())
                            .is_some_and(Vec::is_empty)
                            && scope.ground(term) =>
                    {
                        count += 1
                    }
                    _ => {}
                }
            }
            _ => {}
        }
    }
    Ok(count)
}
