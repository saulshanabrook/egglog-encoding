//! Existential checks over the same candidate queries and refinements as rewrites.
use egglog::{
    CommandOutput, Context, Core, EGraph, Error, UserDefinedCommand,
    ast::{Command, Expr, Fact, Facts, Literal},
    sort::VecContainer,
};

use super::{
    query::Query,
    syntax::{Form, quote},
};

pub(super) fn emit(query: &Query, source: &Form, expected: bool) -> String {
    let split = query.split.expect("a checked pattern has a matching frame");
    let mut bindings = vec![format!("({} Frames)", query.refined)];
    for (name, class) in &query.classes {
        bindings.push(format!("({class} {})", query.sorts[name]));
    }
    format!(
        "(slotted-check {expected} {} (bindings {}) {} {} {} {})",
        quote(&source.render()),
        bindings.join(" "),
        quote(&format!("(check {})", query.body[..split].join(" "))),
        quote(&query.frame),
        quote(&query.refined),
        quote(&format!(
            "(check {})",
            query.body[query.filter_start..].join(" ")
        )),
    )
}

pub(super) struct CheckCommand;

fn string(expr: &Expr) -> Result<&str, Error> {
    match expr {
        Expr::Lit(_, Literal::String(s)) => Ok(s),
        _ => Err(Error::BackendError(
            "slotted-check expects compiler-generated arguments".into(),
        )),
    }
}

fn facts(graph: &mut EGraph, source: &str) -> Result<Vec<Fact>, Error> {
    match graph.parse_program(None, source)?.pop() {
        Some(Command::Check(_, facts)) => Ok(facts),
        _ => Err(Error::BackendError(
            "slotted-check expects a check expression".into(),
        )),
    }
}

impl UserDefinedCommand for CheckCommand {
    fn update(&self, graph: &mut EGraph, args: &[Expr]) -> Result<Vec<CommandOutput>, Error> {
        let [
            Expr::Lit(_, Literal::Bool(expected)),
            source,
            Expr::Call(_, _, bindings),
            candidates,
            frame,
            refinements,
            filters,
        ] = args
        else {
            return Err(Error::BackendError(
                "slotted-check expects compiler-generated arguments".into(),
            ));
        };
        let frame = string(frame)?;
        let refinements = string(refinements)?;
        let mut vars = Vec::new();
        for binding in bindings {
            let Expr::Call(_, name, sorts) = binding else {
                return Err(Error::BackendError("invalid slotted-check binding".into()));
            };
            let [Expr::Var(_, sort)] = sorts.as_slice() else {
                return Err(Error::BackendError(
                    "invalid slotted-check binding sort".into(),
                ));
            };
            let sort = graph
                .type_info()
                .get_sort_by_name(sort)
                .ok_or_else(|| Error::BackendError(format!("unknown query sort {sort}")))?
                .clone();
            vars.push((name.as_str(), sort));
        }
        let mut locals = vars
            .iter()
            .map(|(name, sort)| ((*name).to_owned(), egglog::span!(), sort.clone()))
            .collect::<Vec<_>>();
        locals.push((
            frame.into(),
            egglog::span!(),
            graph.type_info().get_sort_by_name("Frame").unwrap().clone(),
        ));
        let unit = graph.type_info().get_sort_by_name("Unit").unwrap().clone();
        let filters = facts(graph, string(filters)?)?
            .into_iter()
            .map(|fact| {
                let expr = match fact {
                    Fact::Eq(span, a, b) => Expr::Call(
                        span.clone(),
                        "guard".into(),
                        vec![Expr::Call(span, "bool=".into(), vec![a, b])],
                    ),
                    Fact::Fact(expr) => expr,
                };
                graph
                    .typecheck_expr_with_bindings_and_output(
                        &expr,
                        &locals,
                        unit.clone(),
                        Context::Read,
                    )
                    .map_err(Error::from)
            })
            .collect::<Result<Vec<_>, _>>()?;
        let candidate_facts = facts(graph, string(candidates)?)?;
        let candidates = graph.query(&vars, Facts(candidate_facts))?;
        for candidate in candidates {
            let frames = graph
                .value_to_container::<VecContainer>(candidate[refinements])
                .expect("Frames container");
            let mut values = candidate
                .iter()
                .map(|(name, value)| (name.as_str(), *value))
                .collect::<Vec<_>>();
            for &value in &frames.data {
                values.push((frame, value));
                let matched = graph.read(|mut state| {
                    filters
                        .iter()
                        .all(|expr| state.eval_resolved_expr(expr, &values).is_some())
                });
                if matched {
                    return if *expected {
                        Ok(vec![])
                    } else {
                        Err(Error::ExpectFail(source.span()))
                    };
                }
                values.pop();
            }
        }
        if !expected {
            return Ok(vec![]);
        }
        Err(Error::CheckError(
            facts(graph, string(source)?)?,
            source.span(),
        ))
    }
}
