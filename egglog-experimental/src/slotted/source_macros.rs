//! Run ordinary command macros against source types before slot encoding.
//! Parsing, constructor layouts, and scopes belong to the existing frontend;
//! macros receive egglog's TypeInfo and need no knowledge of slot encoding.
use super::{
    frontend::{declarations, source_constructor, source_rewrite, source_ruleset},
    model::{Column, Language},
    proofs::{context::ProofContext, guards, substitution},
    syntax::{self, Form},
    var_sort::VarSort,
};
use egglog::{
    CommandMacroRegistry, Context, EGraph,
    ast::{Action, Command, Expr, Literal, ParseError, Span},
    util::{FreshGen, SymbolGen},
};
use std::{collections::BTreeMap, sync::Arc};

const SLOT: &str = "_slotted_source_slot";

#[derive(Clone)]
pub(super) struct SourceMacros {
    graph: EGraph,
    macros: CommandMacroRegistry,
    symbols: SymbolGen,
}

impl SourceMacros {
    pub(super) fn new(mut graph: EGraph) -> Self {
        let macros = std::mem::take(graph.command_macros_mut());
        graph.parser.ensure_no_reserved_symbols = false;
        egglog::prelude::add_base_sort(&mut graph, VarSort, egglog::span!()).unwrap();
        guards::register(&mut graph, &Arc::new(ProofContext::default()));
        substitution::register(&mut graph, &Arc::new(ProofContext::default()));
        graph
            .parse_and_run_program(None, &format!("(function {SLOT} (String) Var :no-merge)"))
            .unwrap();
        let symbols = graph.parser.symbol_gen.clone();
        Self {
            graph,
            macros,
            symbols,
        }
    }

    pub(super) fn lower(
        &mut self,
        forms: &[(Form, Span)],
        previous: &Language,
    ) -> Result<Vec<(Form, Span)>, ParseError> {
        let span = forms
            .first()
            .map(|(_, s)| s.clone())
            .unwrap_or_else(|| egglog::span!());
        self.lower_inner(forms, previous)
            .map_err(|e| ParseError(span, e))
    }

    fn lower_inner(
        &mut self,
        forms: &[(Form, Span)],
        previous: &Language,
    ) -> Result<Vec<(Form, Span)>, String> {
        let mut graph = self.graph.clone();
        let mut lang = previous.clone();
        let mut sorts = Vec::new();
        let mut constructors = Vec::new();
        for (form, _) in forms {
            declarations(form, &mut sorts, &mut constructors)?;
        }
        let all_sorts: Vec<_> = previous
            .carriers
            .iter()
            .map(|s| s.sort.clone())
            .chain(sorts)
            .collect();
        for form in constructors {
            let op = source_constructor(
                &form,
                all_sorts.iter().map(String::as_str),
                lang.constructors.values(),
            )?;
            lang.constructors.insert(op.name.clone(), op);
        }
        for sort in all_sorts {
            graph
                .parse_and_run_program(None, &format!("(sort {sort})"))
                .map_err(|e| e.to_string())?;
        }
        for op in lang.constructors.values() {
            graph
                .parse_and_run_program(
                    None,
                    &format!(
                        "(constructor {} ({}) {})",
                        op.name,
                        op.input_sorts().collect::<Vec<_>>().join(" "),
                        op.sort
                    ),
                )
                .map_err(|e| e.to_string())?;
        }
        let mut globals = BTreeMap::new();
        for (name, term) in &previous.globals {
            let sort = previous.sort_of(term).ok_or("global has no source sort")?;
            bind(&mut graph, &mut globals, &mut self.symbols, name, sort)?;
        }
        let mut out = Vec::new();
        for (form, span) in forms {
            if matches!(
                form.call(),
                Ok(("sort" | "constructor" | "datatype" | "datatype*", _))
            ) {
                out.push((form.clone(), span.clone()));
                continue;
            }
            for command in parse(&mut graph, form)? {
                let command = command.visit_exprs(&mut |expr| capture(expr, &lang, &globals));
                let original = render(&command);
                let commands = self
                    .macros
                    .apply(command, &mut self.symbols, graph.type_info())
                    .map_err(|e| e.to_string())?;
                for command in commands {
                    let unchanged = render(&command) == original;
                    let before = out.len();
                    self.emit(command, span, &mut graph, &mut globals, &mut out)?;
                    if unchanged {
                        out.truncate(before);
                        out.push((form.clone(), span.clone()));
                    }
                }
            }
        }
        // Ask macros to flush pending invariants, without adding a user round.
        let flush = graph
            .parser
            .get_program_from_string(None, "(run 0)")
            .map_err(|e| e.to_string())?
            .remove(0);
        let commands = self
            .macros
            .apply(flush.clone(), &mut self.symbols, graph.type_info())
            .map_err(|e| e.to_string())?;
        if commands.len() != 1 || render(&commands[0]) != render(&flush) {
            for command in commands {
                self.emit(
                    command,
                    &egglog::span!(),
                    &mut graph,
                    &mut globals,
                    &mut out,
                )?;
            }
        }
        Ok(out)
    }

    fn emit(
        &mut self,
        command: Command,
        span: &Span,
        graph: &mut EGraph,
        globals: &mut BTreeMap<String, String>,
        out: &mut Vec<(Form, Span)>,
    ) -> Result<(), String> {
        match &command {
            Command::Constructor { .. }
            | Command::Sort { .. }
            | Command::Relation { .. }
            | Command::Function { .. } => {
                graph
                    .run_program(vec![command.clone()])
                    .map_err(|e| e.to_string())?;
            }
            Command::Action(Action::Let(_, name, value)) => {
                let sort = graph
                    .type_info()
                    .infer_expr_sort(&mut self.symbols, value, &[], Context::Full)
                    .map_err(|e| e.to_string())?;
                bind(graph, globals, &mut self.symbols, name, sort.name())?;
            }
            _ => {}
        }
        let command = command.visit_exprs(&mut |expr| restore(expr, globals));
        out.extend(
            syntax::parse(None, &render(&command))
                .map_err(|e| e.to_string())?
                .into_iter()
                .map(|(f, _)| (f, span.clone())),
        );
        Ok(())
    }
}

// Typechecking uses abstract globals. The graph never executes source actions,
// and payload locals remain distinct from captured term globals with the same name.
fn bind(
    graph: &mut EGraph,
    globals: &mut BTreeMap<String, String>,
    symbols: &mut SymbolGen,
    name: &str,
    sort: &str,
) -> Result<(), String> {
    let alias = format!("${}", symbols.fresh("source-global"));
    let value = symbols.fresh("source-value");
    graph
        .resolve_program(
            None,
            &format!("(function {value} () {sort} :no-merge) (let {alias} ({value}))"),
        )
        .map_err(|e| e.to_string())?;
    globals.insert(name.into(), alias);
    Ok(())
}

fn capture(expr: Expr, lang: &Language, globals: &BTreeMap<String, String>) -> Expr {
    match expr {
        Expr::Var(span, name) if name.starts_with('$') => Expr::Call(
            span.clone(),
            SLOT.into(),
            vec![Expr::Lit(span, Literal::String(name))],
        ),
        Expr::Var(span, name) if globals.contains_key(&name) => {
            Expr::Var(span, globals[&name].clone())
        }
        Expr::Call(span, head, args) => {
            let args = args
                .into_iter()
                .enumerate()
                .map(|(i, arg)| {
                    if lang
                        .constructors
                        .get(&head)
                        .is_some_and(|op| matches!(op.columns.get(i), Some(Column::Payload(_))))
                    {
                        restore(arg, globals)
                    } else {
                        arg
                    }
                })
                .collect();
            Expr::Call(span, head, args)
        }
        expr => expr,
    }
}

fn restore(expr: Expr, globals: &BTreeMap<String, String>) -> Expr {
    match expr {
        Expr::Call(span, head, args) if head == SLOT => {
            let [Expr::Lit(_, Literal::String(slot))] = args.as_slice() else {
                unreachable!("source slot")
            };
            Expr::Var(span, slot.clone())
        }
        Expr::Var(span, name) => Expr::Var(
            span,
            globals
                .iter()
                .find(|(_, alias)| **alias == name)
                .map(|(name, _)| name.clone())
                .unwrap_or(name),
        ),
        expr => expr,
    }
}

// Command's display form omits rewrite names. Preserve this source metadata
// both when comparing macro output and when handing it to the next pass.
fn render(command: &Command) -> String {
    let mut text = command.to_string();
    if let Command::Rewrite(_, rewrite, _) = command
        && !rewrite.name.is_empty()
    {
        text.pop();
        text.push_str(&format!(" :name {})", syntax::quote(&rewrite.name)));
    }
    text
}

fn parse(graph: &mut EGraph, form: &Form) -> Result<Vec<Command>, String> {
    let span = egglog::span!();
    let (head, args) = form.call()?;
    Ok(match (head, args) {
        ("let", [name, value]) => vec![Command::Action(Action::Let(
            span,
            name.symbol()?.into(),
            value.expr()?,
        ))],
        ("union", [a, b]) => vec![Command::Action(Action::Union(span, a.expr()?, b.expr()?))],
        ("check", facts) => vec![Command::Check(
            span,
            facts.iter().map(Form::fact).collect::<Result<_, _>>()?,
        )],
        ("fail", [command]) => vec![Command::Fail(span, parse(graph, command)?)],
        ("rewrite", _) => {
            let ruleset = source_ruleset(args)?;
            vec![Command::Rewrite(ruleset, source_rewrite(args)?, false)]
        }
        _ => graph
            .parser
            .parse_command(&form.sexp().map_err(|e| e.to_string())?)
            .map_err(|e| e.to_string())?,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn expanded_source_is_an_ordinary_program() {
        let source = "(datatype E (A) (B) (F E)) (separately-injective F)
            (disequal (A) (B)) (let a (F (A))) (let b (F (B)))
            (check (known-disequal a b)) (fail (check (contradiction)))";
        let mut macros = SourceMacros::new(crate::disequality_source_macros());
        let expanded = macros
            .lower(&syntax::parse(None, source).unwrap(), &Language::default())
            .unwrap();
        let text = expanded
            .iter()
            .map(|(f, _)| f.render())
            .collect::<Vec<_>>()
            .join("\n");
        for syntax in [
            "separately-injective",
            "known-disequal",
            "(disequal ",
            "(contradiction)",
            "(relation ",
            "(rule ",
            "slotted",
        ] {
            assert!(!text.contains(syntax), "{syntax}: {text}");
        }
        EGraph::default()
            .parse_and_run_program(None, &text)
            .unwrap();
        super::super::Compiler::new(super::super::Options {
            proof_mode: super::super::ProofMode::Prove,
            ..Default::default()
        })
        .compile_program(None, &text)
        .unwrap()
        .run(&mut super::super::new_egraph_with_proofs())
        .unwrap();
    }
}
