//! Constructor/rewrite presentation of the shared injectivity/disequality rules.
//! This pass only reads ordinary constructor signatures. Later extensions' syntax
//! (for example binder annotations) is carried through without interpretation.
use crate::{
    disequality::Encoding,
    injectivity::LowerInjectivity,
    surface::{self, Form},
};
use egglog::{
    CommandMacro, EGraph,
    ast::{Action, Command, Expr, ParseError, Span},
    util::SymbolGen,
};
use std::collections::{BTreeMap, BTreeSet};

const PREFIX: &str = "_disequality_";
const RULESET: &str = "_disequality_rules";
const WITNESS: &str = "_disequality_witness";
const CONTRADICTION: &str = "_disequality_contradiction";
const NE: &str = "_disequality_ne";

#[derive(Clone)]
struct Signature {
    input: Vec<String>,
    output: String,
}

#[derive(Clone, Default)]
struct State {
    sorts: BTreeSet<String>,
    constructors: BTreeMap<String, Signature>,
    globals: BTreeMap<String, String>,
    supported: BTreeSet<String>,
    contradiction_sort: Option<String>,
    pending: bool,
}

/// Lower injectivity and positive disequality into constructors, guarded rewrites,
/// and ordinary schedules, independently of the subsequent encoding or runtime.
/// Declarations and globals persist across inputs and follow push/pop scopes.
#[derive(Clone)]
pub struct Compiler {
    state: State,
    scopes: Vec<State>,
    symbols: SymbolGen,
}

impl Default for Compiler {
    fn default() -> Self {
        Self {
            state: State::default(),
            scopes: Vec::new(),
            symbols: SymbolGen::new(PREFIX.into()),
        }
    }
}

fn parse(text: &str) -> Result<Form, String> {
    Ok(surface::parse(None, text)
        .map_err(|e| e.to_string())?
        .remove(0)
        .0)
}

impl Compiler {
    /// Compile an input without advancing state on failure. Includes resolve from
    /// the working directory. The result has no injectivity/disequality syntax.
    pub fn compile(
        &mut self,
        filename: Option<String>,
        source: &str,
    ) -> Result<String, ParseError> {
        let forms = surface::read(filename, source, &mut BTreeSet::new())?;
        let mut next = self.clone();
        let mut out = Vec::new();
        let mut start = 0;
        for (i, (form, span)) in forms.iter().enumerate() {
            if let Ok((head @ ("push" | "pop"), args)) = form.call() {
                out.extend(next.region(&forms[start..i])?);
                if !args.is_empty() {
                    return Err(ParseError(
                        span.clone(),
                        format!("{head} takes no arguments"),
                    ));
                }
                if head == "push" {
                    next.scopes.push(next.state.clone());
                } else {
                    next.state = next.scopes.pop().ok_or_else(|| {
                        ParseError(span.clone(), "pop without a corresponding push".into())
                    })?;
                }
                out.push(form.clone());
                start = i + 1;
            }
        }
        out.extend(next.region(&forms[start..])?);
        *self = next;
        Ok(out.iter().map(Form::render).collect::<Vec<_>>().join("\n"))
    }

    fn encoding() -> Encoding {
        Encoding {
            ruleset: RULESET.into(),
            contradiction: CONTRADICTION.into(),
            ne_prefix: NE.into(),
            ..Default::default()
        }
    }

    fn support(&mut self, sort: &str, graph: &mut EGraph) -> Result<Vec<Form>, String> {
        if self.state.supported.contains(sort) {
            return Ok(vec![]);
        }
        let commands = Self::encoding().support_commands(
            BTreeMap::from([(sort.into(), egglog::span!())]),
            None,
            &mut self.symbols,
            graph.type_info(),
        );
        graph
            .run_program(commands.clone())
            .map_err(|e| e.to_string())?;
        let mut text = String::new();
        if self.state.contradiction_sort.is_none() {
            self.state.contradiction_sort = Some(sort.into());
            text.push_str(&format!(
                "(ruleset {RULESET}) (constructor {CONTRADICTION} () {sort})"
            ));
        }
        self.state.supported.insert(sort.into());
        text.push_str(&format!(
            "(constructor {WITNESS}-{sort} () {sort})
            (constructor {NE}-{sort} ({sort} {sort}) {sort})
            (let {PREFIX}root-{sort} ({WITNESS}-{sort}))"
        ));
        let mut out = surface::parse(None, &text)
            .map_err(|e| e.to_string())?
            .into_iter()
            .map(|(f, _)| f)
            .collect::<Vec<_>>();
        out.extend(self.rules(commands)?);
        self.state.pending = true;
        Ok(out)
    }

    fn rules(&self, commands: Vec<Command>) -> Result<Vec<Form>, String> {
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
                Action::Expr(_, term @ Expr::Call(_, name, _)) => {
                    let sort = if name == CONTRADICTION {
                        self.state.contradiction_sort.as_deref().unwrap()
                    } else {
                        name.strip_prefix(&format!("{NE}-"))
                            .expect("evidence constructor")
                    };
                    (
                        Expr::Call(egglog::span!(), format!("{WITNESS}-{sort}"), vec![]),
                        term.clone(),
                    )
                }
                _ => unreachable!("extension rules union terms or insert evidence"),
            };
            result.push(parse(&format!(
                "(rewrite {lhs} {rhs} :when ({}) :ruleset {RULESET} :name {})",
                rule.body
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(" "),
                surface::quote(&rule.name)
            ))?);
        }
        Ok(result)
    }

    fn region(&mut self, forms: &[(Form, Span)]) -> Result<Vec<Form>, ParseError> {
        let span = forms
            .first()
            .map(|(_, s)| s.clone())
            .unwrap_or_else(|| egglog::span!());
        self.region_inner(forms).map_err(|e| ParseError(span, e))
    }

    fn region_inner(&mut self, forms: &[(Form, Span)]) -> Result<Vec<Form>, String> {
        fn reserved(form: &Form) -> bool {
            match form {
                Form::Atom(s) => s.starts_with(PREFIX),
                Form::List(parts) => parts.iter().any(reserved) || parts.windows(2).any(|pair|
                    matches!(pair, [Form::Atom(key), Form::Atom(name)] if key == ":name" && name.trim_start_matches('"').starts_with(PREFIX))),
            }
        }
        if forms.iter().any(|(f, _)| reserved(f)) {
            return Err(format!(
                "names beginning {PREFIX} are reserved by the disequality pass"
            ));
        }
        let mut sorts = Vec::new();
        let mut constructors = Vec::new();
        for (f, _) in forms {
            surface::declarations(f, &mut sorts, &mut constructors)?;
        }
        self.state.sorts.extend(sorts.iter().cloned());
        for form in &constructors {
            let (_, args) = form.call()?;
            let [name, inputs, output, ..] = args else {
                return Err("constructor expects a name, inputs, and output sort".into());
            };
            self.state.constructors.insert(
                name.symbol()?.into(),
                Signature {
                    input: inputs
                        .list()?
                        .iter()
                        .map(|f| f.symbol().map(String::from))
                        .collect::<Result<_, _>>()?,
                    output: output.symbol()?.into(),
                },
            );
        }
        if self.state.supported.is_empty() && !forms.iter().any(|(f, _)| uses_extension(f)) {
            for (form, _) in forms {
                if let Ok(("let", [name, term])) = form.call() {
                    let mut vars = self.state.globals.clone();
                    if let Some(sort) = infer(term, None, &self.state, &mut vars)? {
                        self.state.globals.insert(name.symbol()?.into(), sort);
                    }
                }
            }
            return Ok(forms.iter().map(|(f, _)| f.clone()).collect());
        }
        // Only signatures matter to the shared rule generator. Unknown input
        // sorts belong to a later extension; preserve those declarations without
        // assigning them semantics here.
        let mut graph = EGraph::default();
        let mut types = sorts_text(&self.state.sorts);
        for (name, signature) in &self.state.constructors {
            if signature.input.iter().all(|s| {
                self.state.sorts.contains(s) || graph.type_info().get_sort_by_name(s).is_some()
            }) {
                types.push_str(&format!(
                    "(constructor {name} ({}) {})",
                    signature.input.join(" "),
                    signature.output
                ));
            }
        }
        graph
            .parse_and_run_program(None, &types)
            .map_err(|e| e.to_string())?;
        if !self.state.supported.is_empty() {
            let commands = Self::encoding().support_commands(
                self.state
                    .supported
                    .iter()
                    .map(|s| (s.clone(), egglog::span!()))
                    .collect(),
                None,
                &mut self.symbols,
                graph.type_info(),
            );
            graph.run_program(commands).map_err(|e| e.to_string())?;
        }
        let mut out = Vec::new();
        for (form, span) in forms {
            let (head, args) = form.call()?;
            let mut context = self.state.globals.clone();
            if uses_extension(form) {
                infer(form, None, &self.state, &mut context)?;
            }
            if head == "separately-injective" {
                let [name] = args else {
                    return Err("separately-injective expects one constructor".into());
                };
                let name = name.symbol()?;
                let signature = self
                    .state
                    .constructors
                    .get(name)
                    .ok_or_else(|| format!("unknown constructor {name}"))?
                    .clone();
                if graph.type_info().get_func_type(name).is_none() {
                    return Err(format!(
                        "separately-injective {name}: input sort is not declared"
                    ));
                }
                for sort in std::iter::once(&signature.output)
                    .chain(&signature.input)
                    .filter(|s| self.state.sorts.contains(*s))
                    .cloned()
                    .collect::<Vec<_>>()
                {
                    out.extend(self.support(&sort, &mut graph)?);
                }
                let commands = LowerInjectivity(Self::encoding())
                    .transform(
                        Command::UserDefined(
                            span.clone(),
                            head.into(),
                            vec![Expr::Var(span.clone(), name.into())],
                        ),
                        &mut self.symbols,
                        graph.type_info(),
                    )
                    .map_err(|e| e.to_string())?;
                out.extend(self.rules(commands)?);
                self.state.pending = true;
                continue;
            }
            let mut support = Vec::new();
            let lowered = self.command(form, &context, &mut graph, &mut support)?;
            out.extend(support);
            if let ("let", [name, term]) = (head, args)
                && let Some(sort) = infer(term, None, &self.state, &mut context)?
            {
                self.state.globals.insert(name.symbol()?.into(), sort);
            }
            match head {
                "run" | "run-schedule" if !self.state.supported.is_empty() => {
                    self.close(&mut out)?;
                    let schedule = if head == "run" {
                        let (ruleset, count) = match args {
                            [count] => ("", count),
                            [name, count] => (name.symbol()?, count),
                            _ => {
                                return Err(
                                    "run expects an optional ruleset and a round count".into()
                                );
                            }
                        };
                        let count = count
                            .atom()?
                            .parse::<usize>()
                            .map_err(|_| "run expects a nonnegative round count")?;
                        parse(&format!("(repeat {count} (run {ruleset}))"))?
                    } else {
                        Form::List(
                            std::iter::once(Form::Atom("seq".into()))
                                .chain(args.iter().cloned())
                                .collect(),
                        )
                    };
                    out.push(parse(&format!(
                        "(run-schedule {})",
                        instrument(&schedule)?.render()
                    ))?);
                    self.state.pending = false;
                }
                "sort" | "constructor" | "datatype" | "datatype*" | "ruleset" => out.push(lowered),
                "let" | "union" | "disequal" | "rewrite" => {
                    out.push(lowered);
                    self.state.pending = true;
                }
                _ => {
                    self.close(&mut out)?;
                    out.push(lowered);
                }
            }
        }
        self.close(&mut out)?;
        // Declarations are inert and may be hoisted within a scope. Keep rules
        // and assertions in source order so later promises cannot justify an
        // earlier observation.
        if out.iter().any(|f| matches!(f.call(), Ok(("constructor", [Form::Atom(name), ..])) if name.starts_with(PREFIX))) {
            let mut declarations = sorts.iter().map(|s| parse(&format!("(sort {s})"))).collect::<Result<Vec<_>, _>>()?;
            declarations.extend(constructors);
            out.retain(|f| !matches!(f.call(), Ok(("sort" | "datatype" | "datatype*", _))) && !matches!(f.call(), Ok(("constructor", [Form::Atom(name), ..])) if !name.starts_with(PREFIX)));
            let (private, commands): (Vec<_>, Vec<_>) = out.into_iter().partition(|f| matches!(f.call(), Ok(("ruleset" | "constructor" | "let", [Form::Atom(name), ..])) if name.starts_with(PREFIX)));
            declarations.extend(private);
            declarations.extend(commands);
            out = declarations;
        }
        Ok(out)
    }

    fn close(&mut self, out: &mut Vec<Form>) -> Result<(), String> {
        if self.state.pending && !self.state.supported.is_empty() {
            out.push(parse(&format!(
                "(run-schedule (saturate (run {RULESET})))"
            ))?);
            self.state.pending = false;
        }
        Ok(())
    }

    fn command(
        &mut self,
        form: &Form,
        context: &BTreeMap<String, String>,
        graph: &mut EGraph,
        support: &mut Vec<Form>,
    ) -> Result<Form, String> {
        let (head, args) = form.call()?;
        match (head, args) {
            ("disequal", [a, b]) => {
                let fact = self.fact(
                    &parse(&format!("(known-disequal {} {})", a.render(), b.render()))?,
                    context,
                    graph,
                    support,
                )?;
                let (name, _) = fact.call()?;
                let sort = name.strip_prefix(&format!("{NE}-")).unwrap();
                parse(&format!("(union ({WITNESS}-{sort}) {})", fact.render()))
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
                            .map(|f| self.fact(f, context, graph, support))
                            .collect::<Result<Vec<_>, _>>()?,
                    )
                    .collect(),
            )),
            ("fail", [command]) => Ok(Form::List(vec![
                Form::Atom(head.into()),
                self.command(command, context, graph, support)?,
            ])),
            ("rewrite", _) => {
                let mut parts = form.list()?.to_vec();
                for i in 1..parts.len() {
                    if parts[i - 1] == Form::Atom(":when".into()) {
                        parts[i] = Form::List(
                            parts[i]
                                .list()?
                                .iter()
                                .map(|f| self.fact(f, context, graph, support))
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
        context: &BTreeMap<String, String>,
        graph: &mut EGraph,
        support: &mut Vec<Form>,
    ) -> Result<Form, String> {
        match form.call()? {
            ("known-disequal", [a, b]) => {
                let mut context = context.clone();
                let a_sort = infer(a, None, &self.state, &mut context)?;
                let b_sort = infer(b, a_sort.as_deref(), &self.state, &mut context)?;
                let sort = a_sort.or(b_sort).ok_or(
                    "cannot infer disequality operand sort; include a constructor pattern",
                )?;
                if !self.state.sorts.contains(&sort) {
                    return Err("disequality requires an equality sort".into());
                }
                infer(a, Some(&sort), &self.state, &mut context)?;
                support.extend(self.support(&sort, graph)?);
                parse(&format!("({NE}-{sort} {} {})", a.render(), b.render()))
            }
            ("contradiction", []) => {
                let sort = self
                    .state
                    .contradiction_sort
                    .clone()
                    .or_else(|| {
                        (self.state.sorts.len() == 1)
                            .then(|| self.state.sorts.first().unwrap().clone())
                    })
                    .ok_or("contradiction requires a disequality carrier")?;
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

fn sorts_text(sorts: &BTreeSet<String>) -> String {
    sorts.iter().map(|s| format!("(sort {s})")).collect()
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

fn infer(
    form: &Form,
    expected: Option<&str>,
    state: &State,
    vars: &mut BTreeMap<String, String>,
) -> Result<Option<String>, String> {
    let sort = match form {
        Form::Atom(name) => {
            if name.starts_with('"') {
                Some("String".into())
            } else if name.parse::<i64>().is_ok() {
                Some("i64".into())
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
                && let Some(signature) = state.constructors.get(head)
            {
                for (arg, sort) in args.iter().zip(&signature.input) {
                    // Only equality-term variables participate here. Primitive
                    // payload variables can have a separate scope in later passes.
                    if state.sorts.contains(sort) {
                        infer(arg, Some(sort), state, vars)?;
                    }
                }
                Some(signature.output.clone())
            } else {
                for part in parts {
                    infer(part, None, state, vars)?;
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

fn instrument(schedule: &Form) -> Result<Form, String> {
    let (head, args) = schedule.call()?;
    match head {
        "run" => Ok(parse(&format!(
            "(seq {} (saturate (run {RULESET})))",
            schedule.render()
        ))?),
        "seq" | "saturate" | "repeat" => {
            let mut parts = vec![Form::Atom(head.into())];
            let children = if head == "repeat" {
                let (count, children) = args
                    .split_first()
                    .ok_or("repeat expects a count and a schedule")?;
                parts.push(count.clone());
                children
            } else {
                args
            };
            parts.extend(
                children
                    .iter()
                    .map(instrument)
                    .collect::<Result<Vec<_>, _>>()?,
            );
            Ok(Form::List(parts))
        }
        _ => Err(format!("unsupported schedule {head}")),
    }
}
