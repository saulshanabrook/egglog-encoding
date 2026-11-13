//! Separate injectivity generates cancellation and upward disequality rules.
//!
//! `(separately-injective F)` promises injectivity in each coordinate with all
//! other inputs fixed. Only existing ordinary constructors can be marked. The
//! generated joins include subsumed rows and create no constructor applications.

use std::{collections::BTreeMap, sync::Arc};

use egglog::{
    CommandMacro, EGraph, Error, TypeError, TypeInfo,
    ast::{
        Action, Actions, Command, Expr, Fact, FunctionRole, FunctionSubtype, Macro, ParseError,
        Parser, Rule, RuleEvalMode, Sexp, Span,
    },
    util::{FreshGen, SymbolGen},
};

use crate::disequality::Encoding;

pub(crate) fn add_injectivity_support(egraph: &mut EGraph, encoding: Encoding) {
    egraph
        .parser
        .add_command_macro(Arc::new(SeparatelyInjective));
    egraph
        .command_macros_mut()
        .register(Arc::new(LowerInjectivity(encoding)));
}

struct SeparatelyInjective;

impl Macro<Vec<Command>> for SeparatelyInjective {
    fn name(&self) -> &str {
        "separately-injective"
    }

    fn parse(
        &self,
        args: &[Sexp],
        span: Span,
        _parser: &mut Parser,
    ) -> Result<Vec<Command>, ParseError> {
        let [name] = args else {
            return Err(ParseError(
                span,
                "usage: (separately-injective <constructor>)".into(),
            ));
        };
        Ok(vec![Command::UserDefined(
            span.clone(),
            self.name().into(),
            vec![Expr::Var(
                name.span(),
                name.expect_atom("constructor name")?,
            )],
        )])
    }
}

struct LowerInjectivity(Encoding);

impl CommandMacro for LowerInjectivity {
    fn preserves_closed_constructor_action(&self, _expression_head: Option<&str>) -> bool {
        true
    }

    fn transform(
        &self,
        command: Command,
        symbols: &mut SymbolGen,
        types: &TypeInfo,
    ) -> Result<Vec<Command>, Error> {
        let Command::UserDefined(ref span, ref head, ref args) = command else {
            return Ok(vec![command]);
        };
        if head != "separately-injective" {
            return Ok(vec![command]);
        }
        let span = span.clone();
        let [Expr::Var(_, name)] = args.as_slice() else {
            return Err(
                ParseError(span, "usage: (separately-injective <constructor>)".into()).into(),
            );
        };
        let function = types
            .source_types()
            .get_func_type(name)
            .ok_or_else(|| ParseError(span.clone(), format!("unknown constructor `{name}`")))?;
        if function.subtype != FunctionSubtype::Constructor
            || function.role != FunctionRole::Ordinary
        {
            return Err(ParseError(
                span,
                format!("separately-injective requires an ordinary constructor, got `{name}`"),
            )
            .into());
        }
        if !types.is_sort_unionable(function.output()) {
            return Err(TypeError::NonUnionableSort(function.output().clone(), span).into());
        }
        for (index, sort) in function.input.iter().enumerate() {
            if sort.is_container_sort() {
                return Err(ParseError(span, format!("separately-injective constructor `{name}` does not support container argument {index}")).into());
            }
            if sort.is_eq_sort() && !types.is_sort_unionable(sort) {
                return Err(TypeError::NonUnionableSort(sort.clone(), span).into());
            }
        }
        if function.input.is_empty() {
            return Ok(vec![]);
        }
        let mut sorts = BTreeMap::from([(function.output().name().into(), span.clone())]);
        for sort in &function.input {
            if types.is_sort_unionable(sort) {
                sorts.insert(sort.name().into(), span.clone());
            }
        }
        let mut commands = self.0.support_commands(sorts, None, symbols, types);
        let inputs: Vec<_> = function
            .input
            .iter()
            .map(|_| Expr::Var(span.clone(), symbols.fresh("injectivity-input")))
            .collect();
        let other = Expr::Var(span.clone(), symbols.fresh("injectivity-other"));
        let left = Expr::Var(span.clone(), symbols.fresh("injectivity-left"));
        let right = Expr::Var(span.clone(), symbols.fresh("injectivity-right"));
        for (index, sort) in function.input.iter().enumerate() {
            let mut matching = inputs.clone();
            matching[index] = other.clone();
            let left_call = Expr::Call(span.clone(), name.clone(), inputs.clone());
            let right_call = Expr::Call(span.clone(), name.clone(), matching);
            let unequal = Fact::Fact(Expr::Call(
                span.clone(),
                if types.is_sort_unionable(sort) {
                    format!("{}-{}", self.0.ne_prefix, sort.name())
                } else {
                    "!=".into()
                },
                vec![inputs[index].clone(), other.clone()],
            ));
            let mut heads = Vec::new();
            if types.is_sort_unionable(sort) {
                let cancel = vec![
                    Fact::Eq(span.clone(), left.clone(), left_call.clone()),
                    Fact::Eq(span.clone(), left.clone(), right_call.clone()),
                ];
                heads.push((
                    cancel,
                    Action::Union(span.clone(), inputs[index].clone(), other.clone()),
                ));
            }
            let upward = vec![
                Fact::Eq(span.clone(), left.clone(), left_call),
                Fact::Eq(span.clone(), right.clone(), right_call),
                unequal,
            ];
            heads.push((
                upward,
                Action::Expr(
                    span.clone(),
                    Expr::Call(
                        span.clone(),
                        format!("{}-{}", self.0.ne_prefix, function.output().name()),
                        vec![left.clone(), right.clone()],
                    ),
                ),
            ));
            for (body, action) in heads {
                commands.push(Command::Rule {
                    rule: Rule {
                        span: span.clone(),
                        name: symbols.fresh(&format!("injectivity-{name}")),
                        ruleset: self.0.ruleset.clone(),
                        body,
                        head: Actions::singleton(action),
                        eval_mode: RuleEvalMode::Seminaive,
                        no_decomp: false,
                        include_subsumed: true,
                    },
                });
            }
        }
        Ok(commands)
    }
}
