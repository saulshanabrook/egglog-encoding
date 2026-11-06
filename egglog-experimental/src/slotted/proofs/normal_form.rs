//! Prepare source rule premises for ordinary proof checking.

use super::HashMap;
use super::context::pattern_term;
use super::terms::instantiate;
use egglog::ast::{
    ResolvedExpr, ResolvedExprExt, ResolvedFact, ResolvedNCommand, ResolvedRule, ResolvedVar,
};
use egglog::util::{FreshGen, INTERNAL_SYMBOL_PREFIX, IndexMap, SymbolGen};
use egglog::{ResolvedCall, TermDag, TermId};
use std::collections::{BTreeMap, BTreeSet};

/// Rule bodies prepared for source premises and ordinary proof checking.
#[derive(Clone, Debug)]
pub(in crate::slotted) struct NormalRule {
    pub body: Vec<ResolvedFact>,
    pub commands: [ResolvedNCommand; 1],
    pub renaming_args: BTreeMap<usize, Vec<ResolvedVar>>,
    auxiliary: Vec<(String, ResolvedExpr)>,
}

impl NormalRule {
    pub fn new(rule: &ResolvedRule) -> Self {
        let mut names = BTreeSet::new();
        rule.clone().visit_exprs(&mut |expr| {
            names.extend(expr.vars().map(|v| v.name));
            expr
        });
        let mut prefix = format!("{INTERNAL_SYMBOL_PREFIX}slotted-proof-");
        while names.iter().any(|name| name.starts_with(&prefix)) {
            prefix.push('-');
        }
        let mut symbols = SymbolGen::new(prefix);
        let mut auxiliary = Vec::new();
        let mut body = Vec::new();
        for fact in &rule.body {
            if matches!(fact, ResolvedFact::Fact(ResolvedExpr::Call(_, ResolvedCall::Primitive(head), _)) if head.name() == "renaming-=")
            {
                body.push(fact.clone());
                continue;
            }
            let start = body.len();
            let fact = egglog::proof::proof_form_fact(fact.clone(), &mut body, &mut symbols);
            for binding in &body[start..] {
                let ResolvedFact::Eq(_, expr, ResolvedExpr::Var(_, var)) = binding else {
                    unreachable!("normalizing slotted guards only lifts constructor operands")
                };
                auxiliary.push((var.name.clone(), expr.clone()));
            }
            body.push(fact);
        }
        let mut expanded = Vec::new();
        let mut renaming_args = BTreeMap::new();
        for (i, fact) in body.iter().enumerate() {
            if let ResolvedFact::Fact(ResolvedExpr::Call(span, ResolvedCall::Primitive(head), args)) =
                fact
                && head.name() == "renaming-="
            {
                let variables: Vec<_> = args
                    .iter()
                    .map(|arg| ResolvedVar {
                        name: symbols.fresh("argument"),
                        sort: arg.output_type().clone(),
                        is_global_ref: false,
                    })
                    .collect();
                let arguments: Vec<_> = args
                    .iter()
                    .zip(&variables)
                    .map(|(arg, var)| {
                        let representative = ResolvedExpr::Var(arg.span(), var.clone());
                        expanded.push(ResolvedFact::Eq(
                            arg.span(),
                            arg.clone(),
                            representative.clone(),
                        ));
                        representative
                    })
                    .collect();
                expanded.push(ResolvedFact::Fact(ResolvedExpr::Call(
                    span.clone(),
                    ResolvedCall::Primitive(head.clone()),
                    arguments,
                )));
                renaming_args.insert(i, variables);
            } else {
                expanded.push(fact.clone());
            }
        }
        let commands = [ResolvedNCommand::NormRule {
            rule: ResolvedRule {
                body: expanded,
                ..rule.clone()
            },
        }];
        Self {
            body,
            commands,
            renaming_args,
            auxiliary,
        }
    }

    pub fn bindings(
        &self,
        dag: &mut TermDag,
        bindings: &HashMap<String, TermId>,
    ) -> Result<IndexMap<String, TermId>, String> {
        let mut bindings = bindings.clone();
        let mut auxiliary = IndexMap::default();
        for (name, expr) in &self.auxiliary {
            let pattern = pattern_term(dag, expr);
            let term = instantiate(dag, pattern, &bindings)?;
            auxiliary.insert(name.clone(), term);
            bindings.insert(name.clone(), term);
        }
        Ok(auxiliary)
    }
}
