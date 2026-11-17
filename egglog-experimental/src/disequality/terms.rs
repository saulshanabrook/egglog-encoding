//! Represent disequality evidence with constructors and guarded rewrites.
use super::Encoding;
use egglog::{
    CommandMacro, Error, TypeInfo,
    ast::{Action, Command, Expr, ParseError, Rewrite, Schema},
    util::SymbolGen,
};

pub(super) struct Terms(pub(super) Encoding);

impl Terms {
    fn evidence(&self, name: &str) -> bool {
        name == self.0.contradiction || name.starts_with(&format!("{}-", self.0.ne_prefix))
    }

    fn witness(&self, expr: &Expr) -> Expr {
        let Expr::Call(span, name, _) = expr else {
            unreachable!("evidence call")
        };
        Expr::Call(span.clone(), format!("{name}-witness"), vec![])
    }
}

impl CommandMacro for Terms {
    fn transform(
        &self,
        command: Command,
        _: &mut SymbolGen,
        types: &TypeInfo,
    ) -> Result<Vec<Command>, Error> {
        Ok(match command {
            Command::Relation { span, name, inputs } if self.evidence(&name) => {
                let sort = if let Some(sort) = inputs.first() {
                    sort.clone()
                } else {
                    let mut sorts = types.get_arcsorts_by(|s| types.is_sort_unionable(s));
                    sorts.sort_by_key(|s| s.name().to_owned());
                    sorts
                        .first()
                        .ok_or_else(|| {
                            ParseError(span.clone(), "evidence requires an equality sort".into())
                        })?
                        .name()
                        .to_owned()
                };
                let witness = format!("{name}-witness");
                let constructor = |name, input| Command::Constructor {
                    span: span.clone(),
                    name,
                    schema: Schema::new(input, sort.clone()),
                    cost: None,
                    unextractable: false,
                    hidden: false,
                    role: Default::default(),
                };
                vec![
                    constructor(witness.clone(), vec![]),
                    constructor(name, inputs),
                    Command::Action(Action::Let(
                        span.clone(),
                        format!("{witness}-root"),
                        Expr::Call(span, witness, vec![]),
                    )),
                ]
            }
            Command::Rule { rule } if rule.ruleset == self.0.ruleset => {
                let [action] = rule.head.0.as_slice() else {
                    unreachable!("one extension action")
                };
                let (lhs, rhs) = match action {
                    Action::Union(_, a, b) => (a.clone(), b.clone()),
                    Action::Expr(_, term) => (self.witness(term), term.clone()),
                    _ => unreachable!("extension rules union terms or insert evidence"),
                };
                vec![Command::Rewrite(
                    rule.ruleset,
                    Rewrite {
                        span: rule.span,
                        name: rule.name,
                        lhs,
                        rhs,
                        conditions: rule.body,
                    },
                    false,
                )]
            }
            Command::Action(Action::Expr(span, term)) if matches!(&term, Expr::Call(_, name, _) if self.evidence(name)) =>
            {
                vec![Command::Action(Action::Union(
                    span,
                    self.witness(&term),
                    term,
                ))]
            }
            command => vec![command],
        })
    }
}
