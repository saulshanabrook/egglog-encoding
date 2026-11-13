//! Lower injectivity/disequality before slot encoding, using source constructors
//! and guarded rewrites. Only private evidence terms are equated with the witness;
//! no evidence insertion unions an object-language expression with that witness.
use super::{
    frontend::{declarations, source_constructor},
    maintenance,
    model::{Column, Language},
    syntax::{self, Form},
};
use crate::{disequality::Encoding, injectivity::LowerInjectivity};
use egglog::{
    CommandMacro, EGraph,
    ast::{Action, Command, Expr, ParseError, Span},
    util::SymbolGen,
};
use std::collections::{BTreeMap, BTreeSet};

const PREFIX: &str = "_slotted_disequality_";
pub(super) const MATCH: &str = "_slotted_disequality_match";
pub(super) const APPLY: &str = "_slotted_disequality_apply";
const WITNESS: &str = "_slotted_disequality_witness";
const CONTRADICTION: &str = "_slotted_disequality_contradiction";
const NE: &str = "_slotted_disequality_ne";

#[derive(Clone)]
pub(super) struct SourcePass {
    sort: Option<String>,
    symbols: SymbolGen,
}

impl Default for SourcePass {
    fn default() -> Self {
        Self {
            sort: None,
            symbols: SymbolGen::new(PREFIX.into()),
        }
    }
}

fn parse(text: &str) -> Result<Form, String> {
    Ok(syntax::parse(None, text)
        .map_err(|e| e.to_string())?
        .remove(0)
        .0)
}

impl SourcePass {
    pub(super) fn is_rule(&self, name: &str) -> bool {
        // Proof mode may suffix a name reused after pop. The reserved prefix
        // still identifies the supporting rule after that disambiguation.
        name.starts_with(PREFIX)
    }

    pub(super) fn schedule(&self, steps: usize, has_rules: bool) -> String {
        if self.sort.is_none() {
            return maintenance::schedule(steps, has_rules);
        }
        let machinery = maintenance::MACHINERY;
        let close = format!(
            "(saturate (seq {machinery} (run {MATCH}) (saturate (run slotted-refine)) (run {APPLY})))"
        );
        let user = if steps > 0 && has_rules {
            format!(
                "(repeat {steps} (seq (run) (saturate (run slotted-refine)) (run slotted-apply) {close}))"
            )
        } else {
            String::new()
        };
        format!("(run-schedule {close} {user})")
    }

    fn encoding() -> Encoding {
        let mut encoding = Encoding::default();
        encoding.ruleset = MATCH.into();
        encoding.contradiction = CONTRADICTION.into();
        encoding.ne_prefix = NE.into();
        encoding
    }

    fn support(&mut self, sort: &str, graph: &mut EGraph) -> Result<Vec<Form>, String> {
        if let Some(active) = &self.sort {
            if active != sort {
                return Err(
                    "slotted disequality currently requires one carrier sort per scope".into(),
                );
            }
            return Ok(vec![]);
        }
        let commands = Self::encoding().support_commands(
            BTreeMap::from([(sort.into(), egglog::span!())]),
            None,
            &mut self.symbols,
            graph.type_info(),
        );
        // Install ordinary signatures solely for the shared injectivity pass.
        graph
            .run_program(commands.clone())
            .map_err(|e| e.to_string())?;
        self.sort = Some(sort.into());
        let mut result = syntax::parse(
            None,
            &format!(
                "(ruleset {MATCH}) (ruleset {APPLY})
             (constructor {WITNESS} () {sort})
             (constructor {CONTRADICTION} () {sort})
             (constructor {NE}-{sort} ({sort} {sort}) {sort})
             (let {PREFIX}root ({WITNESS}))"
            ),
        )
        .map_err(|e| e.to_string())?
        .into_iter()
        .map(|(f, _)| f)
        .collect::<Vec<_>>();
        result.extend(self.rules(commands)?);
        Ok(result)
    }

    fn rules(&mut self, commands: Vec<Command>) -> Result<Vec<Form>, String> {
        let mut result = Vec::new();
        for command in commands {
            let Command::Rule { rule } = command else {
                continue;
            };
            let [action] = rule.head.0.as_slice() else {
                unreachable!("one extension action")
            };
            let (lhs, rhs) = match action {
                Action::Union(_, a, b) => (a.clone(), b.clone()),
                Action::Expr(_, term) => (
                    Expr::Call(egglog::span!(), WITNESS.into(), vec![]),
                    term.clone(),
                ),
                _ => unreachable!("injectivity/disequality only unions or inserts evidence"),
            };
            result.push(parse(&format!(
                "(rewrite {lhs} {rhs} :when ({}) :name {})",
                rule.body
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(" "),
                syntax::quote(&rule.name),
            ))?);
        }
        Ok(result)
    }

    pub(super) fn lower(
        &mut self,
        forms: &[(Form, Span)],
        previous: &Language,
    ) -> Result<Vec<(Form, Span)>, ParseError> {
        if forms.is_empty() {
            return Ok(vec![]);
        }
        let span = forms[0].1.clone();
        self.lower_inner(forms, previous)
            .map_err(|e| ParseError(span, e))
    }

    fn lower_inner(
        &mut self,
        forms: &[(Form, Span)],
        previous: &Language,
    ) -> Result<Vec<(Form, Span)>, String> {
        fn reserved(form: &Form) -> bool {
            match form {
                Form::Atom(s) => s.trim_start_matches('"').starts_with(PREFIX),
                Form::List(parts) => parts.iter().any(reserved),
            }
        }
        if forms.iter().any(|(f, _)| reserved(f)) {
            return Err(format!(
                "names beginning {PREFIX} are reserved by the disequality pass"
            ));
        }
        fn uses_extension(f: &Form) -> bool {
            matches!(
                f.call(),
                Ok((
                    "separately-injective" | "disequal" | "known-disequal" | "contradiction",
                    _
                ))
            ) || matches!(f, Form::List(parts) if parts.iter().any(uses_extension))
        }
        if !forms.iter().any(|(f, _)| uses_extension(f)) {
            return Ok(forms.to_vec());
        }
        let mut lang = previous.clone();
        let mut sorts = previous
            .carriers
            .iter()
            .map(|s| s.sort.clone())
            .collect::<BTreeSet<_>>();
        let mut new_sorts = Vec::new();
        let mut constructors = Vec::new();
        for (form, _) in forms {
            declarations(form, &mut new_sorts, &mut constructors)?;
        }
        sorts.extend(new_sorts);
        for form in constructors {
            let op = source_constructor(
                &form,
                sorts.iter().map(String::as_str),
                lang.constructors.values(),
            )?;
            lang.constructors.insert(op.name.clone(), op);
        }
        let mut graph = EGraph::default();
        let mut declarations = "(sort Var)".to_owned();
        for sort in &sorts {
            declarations.push_str(&format!("(sort {sort})"));
        }
        for op in lang
            .constructors
            .values()
            .filter(|op| !op.name.starts_with(PREFIX))
        {
            declarations.push_str(&format!(
                "(constructor {} ({}) {})",
                op.name,
                op.input_sorts().collect::<Vec<_>>().join(" "),
                op.sort
            ));
        }
        if let Some(sort) = &self.sort {
            declarations.push_str(&format!(
                "(relation {CONTRADICTION} ()) (relation {NE}-{sort} ({sort} {sort}))"
            ));
        }
        graph
            .parse_and_run_program(None, &declarations)
            .map_err(|e| e.to_string())?;
        let mut globals = previous
            .globals
            .iter()
            .filter_map(|(name, term)| {
                previous
                    .sort_of(term)
                    .map(|sort| (name.clone(), sort.to_owned()))
            })
            .collect::<BTreeMap<_, _>>();
        let mut out = Vec::new();
        for (form, span) in forms {
            let mut context = globals.clone();
            let (head, args) = form.call()?;
            if head == "separately-injective" {
                let [name] = args else {
                    return Err("separately-injective expects one constructor".into());
                };
                let name = name.symbol()?;
                let op = lang
                    .constructors
                    .get(name)
                    .ok_or_else(|| format!("unknown constructor {name}"))?;
                if op.columns.iter().any(|c| !matches!(c, Column::Child)) {
                    return Err("slotted separately-injective currently requires only term children (no binders, Var, or payloads)".into());
                }
                out.extend(
                    self.support(&op.sort, &mut graph)?
                        .into_iter()
                        .map(|f| (f, span.clone())),
                );
                let command = Command::UserDefined(
                    span.clone(),
                    head.into(),
                    vec![Expr::Var(span.clone(), name.into())],
                );
                let commands = LowerInjectivity(Self::encoding())
                    .transform(command, &mut self.symbols, graph.type_info())
                    .map_err(|e| e.to_string())?;
                out.extend(self.rules(commands)?.into_iter().map(|f| (f, span.clone())));
                continue;
            }
            if uses_extension(form) {
                infer(form, None, &lang, &mut context)?;
            }
            let mut support = Vec::new();
            let lowered = self.command(form, &lang, &context, &mut graph, &mut support)?;
            out.extend(support.into_iter().map(|f| (f, span.clone())));
            if let ("let", [name, term]) = (head, args)
                && let Some(sort) = infer(term, None, &lang, &mut context)?
            {
                globals.insert(name.symbol()?.into(), sort);
            }
            out.push((lowered, span.clone()));
        }
        // Declarations and the inert witness may precede observations in this
        // region; injectivity rewrites must stay at their declaration point.
        // This lets an earlier check close an empty evidence ruleset without
        // seeing any promises or assertions that occur after that check.
        let (mut declarations, commands): (Vec<_>, Vec<_>) = out.into_iter().partition(|(form, _)| {
            matches!(form.call(), Ok(("ruleset" | "constructor" | "let", [Form::Atom(name), ..])) if name.starts_with(PREFIX))
        });
        declarations.extend(commands);
        Ok(declarations)
    }

    fn command(
        &mut self,
        form: &Form,
        lang: &Language,
        context: &BTreeMap<String, String>,
        graph: &mut EGraph,
        support: &mut Vec<Form>,
    ) -> Result<Form, String> {
        let (head, args) = form.call()?;
        match (head, args) {
            ("disequal", [a, b]) => {
                let fact = self.fact(
                    &parse(&format!("(known-disequal {} {})", a.render(), b.render()))?,
                    lang,
                    context,
                    graph,
                    support,
                )?;
                Ok(parse(&format!("(union ({WITNESS}) {})", fact.render()))?)
            }
            ("disequal", _) => Err("disequal expects two terms".into()),
            ("known-disequal" | "contradiction", _) => {
                Err("known-disequal and contradiction are root query patterns only".into())
            }
            ("check", facts) => Ok(Form::List(
                std::iter::once(Form::Atom(head.into()))
                    .chain(
                        facts
                            .iter()
                            .map(|f| self.fact(f, lang, context, graph, support))
                            .collect::<Result<Vec<_>, _>>()?,
                    )
                    .collect(),
            )),
            ("fail", [command]) => Ok(Form::List(vec![
                Form::Atom(head.into()),
                self.command(command, lang, context, graph, support)?,
            ])),
            ("rewrite", _) => {
                let mut parts = form.list()?.to_vec();
                for i in 1..parts.len() {
                    if parts[i - 1] == Form::Atom(":when".into()) {
                        parts[i] = Form::List(
                            parts[i]
                                .list()?
                                .iter()
                                .map(|f| self.fact(f, lang, context, graph, support))
                                .collect::<Result<_, _>>()?,
                        );
                    }
                }
                Ok(Form::List(parts))
            }
            _ => Ok(form.clone()),
        }
    }

    fn fact(
        &mut self,
        form: &Form,
        lang: &Language,
        context: &BTreeMap<String, String>,
        graph: &mut EGraph,
        support: &mut Vec<Form>,
    ) -> Result<Form, String> {
        match form.call()? {
            ("known-disequal", [a, b]) => {
                let mut context = context.clone();
                let a_sort = infer(a, None, lang, &mut context)?;
                let b_sort = infer(b, a_sort.as_deref(), lang, &mut context)?;
                let sort = a_sort.or(b_sort).or_else(|| self.sort.clone()).ok_or(
                    "cannot infer disequality operand sort; include a constructor pattern",
                )?;
                if !lang.constructors.values().any(|op| op.sort == sort) {
                    return Err("disequality requires an equality sort".into());
                }
                infer(a, Some(&sort), lang, &mut context)?;
                support.extend(self.support(&sort, graph)?);
                parse(&format!("({NE}-{sort} {} {})", a.render(), b.render()))
            }
            ("contradiction", []) => {
                let sort = self
                    .sort
                    .clone()
                    .or_else(|| {
                        let sorts = lang
                            .constructors
                            .values()
                            .map(|op| op.sort.clone())
                            .collect::<BTreeSet<_>>();
                        (sorts.len() == 1).then(|| sorts.into_iter().next().unwrap())
                    })
                    .ok_or("contradiction requires a single disequality carrier")?;
                support.extend(self.support(&sort, graph)?);
                parse(&format!("({CONTRADICTION})"))
            }
            ("known-disequal" | "contradiction", _) => {
                Err("invalid disequality query arity".into())
            }
            _ => Ok(form.clone()),
        }
    }
}

fn infer(
    form: &Form,
    expected: Option<&str>,
    lang: &Language,
    vars: &mut BTreeMap<String, String>,
) -> Result<Option<String>, String> {
    let sort = match form {
        Form::Atom(name) => {
            if name.starts_with('"') {
                Some("String".into())
            } else if name.parse::<i64>().is_ok() {
                Some("i64".into())
            } else if name.starts_with('$') {
                Some("Var".into())
            } else {
                if let Some(sort) = expected {
                    if vars.get(name).is_some_and(|old| old != sort) {
                        return Err(format!("incompatible sorts for {name}"));
                    }
                    vars.insert(name.clone(), sort.into());
                }
                vars.get(name).cloned()
            }
        }
        Form::List(parts) => {
            if let Ok((head, args)) = form.call()
                && let Some(op) = lang.constructors.get(head)
            {
                for (arg, sort) in args.iter().zip(op.input_sorts()) {
                    infer(arg, Some(sort), lang, vars)?;
                }
                Some(op.sort.clone())
            } else {
                for part in parts {
                    infer(part, None, lang, vars)?;
                }
                None
            }
        }
    };
    if let (Some(expected), Some(actual)) = (expected, &sort)
        && actual != expected
    {
        return Err(format!(
            "disequality operand has sort {actual}, expected {expected}"
        ));
    }
    Ok(sort)
}
