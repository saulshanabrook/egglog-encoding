//! An explicit slotted-source to ordinary-egglog pass. Evaluation stays in egglog.
use super::compiled::{CompiledProgram, ExtractRequest, ExtractRequests, ProofRequests};
use super::errors::CompileError;
use super::proofs::pipeline::{EncodingNames, ProofRequest, SlottedClaim};
use super::proofs::resolve::Reader;
use super::{
    flatten, maintenance,
    model::*,
    query, rewrite,
    syntax::{self, Form},
};
use egglog::ast::{ParseError, ResolvedNCommand, ResolvedRule, Rewrite as SourceRewrite, Span};
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
/// Whether to emit native checks or translate proofs of slotted claims.
pub enum ProofMode {
    #[default]
    /// Use the ordinary encoding without proof instrumentation.
    Disabled,
    /// Run the proof-compatible encoding with ordinary checks.
    Check,
    /// Translate and verify supported equality checks; run ordinary checks for others.
    Prove,
    /// Materialize and simplify source proofs without verifying their derivations.
    Extract,
}

#[derive(Clone, Copy, Debug, Default)]
/// Control source-level slotted matching semantics.
pub struct Options {
    /// Match the reference nested matcher's restriction on non-pattern aliasing.
    pub no_aliasing: bool,
    /// Select proof instrumentation and claim handling.
    pub proof_mode: ProofMode,
}

#[derive(Default)]
struct Pattern {
    names: flatten::PatternNames,
    atoms: Vec<flatten::Atom>,
    conditions: query::Conditions,
    values: Vec<(String, Term, Option<String>)>,
    patterns: usize,
    proof_names: query::ProofNames,
}

impl Pattern {
    fn new(forms: &[Form]) -> Self {
        fn reserve(form: &Form, names: &mut flatten::PatternNames) {
            match form {
                Form::Atom(name) => names.reserve(name),
                Form::List(forms) => {
                    for form in forms {
                        reserve(form, names);
                    }
                }
            }
        }
        let mut pattern = Self::default();
        for form in forms {
            reserve(form, &mut pattern.names);
        }
        pattern.conditions.global_frame = pattern.names.fresh("_concrete");
        pattern
    }
}

#[derive(Clone, Default)]
struct ProofCompiler {
    source: Reader,
    names: EncodingNames,
    flattened: BTreeMap<String, ResolvedRule>,
}

#[derive(Clone)]
struct State {
    lang: Language,
    disequality: super::disequality::SourcePass,
    proofs: Option<ProofCompiler>,
    initialized: bool,
    dirty: bool,
    rules: usize,
    extracts: usize,
    reserved: BTreeSet<String>,
    declared: BTreeSet<String>,
    substitutions: Vec<rewrite::SubstitutionRequest>,
}

impl Default for State {
    fn default() -> Self {
        Self {
            lang: Language::default(),
            disequality: super::disequality::SourcePass::default(),
            proofs: None,
            initialized: false,
            dirty: false,
            rules: 0,
            extracts: 0,
            reserved: [
                "Var",
                "Names",
                "Binding",
                "Frame",
                "Renaming",
                "Frames",
                "Group",
                "Groups",
                "Renamings",
            ]
            .into_iter()
            .map(String::from)
            .collect(),
            declared: BTreeSet::new(),
            substitutions: Vec::new(),
        }
    }
}

/// Compiler state for successive input files or complete REPL commands.
/// Tracks declarations, globals, rewrites, and push/pop scopes.
#[derive(Clone, Default)]
pub struct Compiler {
    options: Options,
    parser: Option<egglog::ast::Parser>,
    state: State,
    scopes: Vec<State>,
    next_rule: usize,
    used_rule_names: BTreeSet<String>,
    next_check: usize,
    next_proof: usize,
    proof_requests: ProofRequests,
    extract_requests: ExtractRequests,
    substitution_phases: BTreeMap<usize, Arc<super::proofs::runtime_substitution::Phase>>,
}

impl Compiler {
    /// Create a compiler with an empty source environment.
    pub fn new(options: Options) -> Self {
        Self {
            options,
            state: State {
                proofs: matches!(options.proof_mode, ProofMode::Prove | ProofMode::Extract)
                    .then(ProofCompiler::default),
                ..Default::default()
            },
            ..Default::default()
        }
    }

    /// Use an existing slotted e-graph's parsing vocabulary when compiling.
    /// This avoids initializing a second graph solely to parse generated code.
    /// The graph must have the runtime and commands required by `options` registered.
    pub fn for_egraph(options: Options, graph: &egglog::EGraph) -> Self {
        Self {
            parser: Some(graph.parser.clone()),
            ..Self::new(options)
        }
    }

    /// Compile to lowered egglog text. Includes resolve from the working directory.
    /// Proof replay requires the original source; use [`Self::compile_program`] to
    /// retain it for execution. A failed compilation leaves this compiler unchanged.
    pub fn compile(
        &mut self,
        filename: Option<String>,
        source: &str,
    ) -> Result<String, CompileError> {
        let mut next = self.clone();
        let (text, _) = next.compile_inner(filename, source)?;
        next.extract_requests.clear();
        next.substitution_phases.clear();
        *self = next;
        Ok(text)
    }

    /// Compile commands and retain the original resolved programs for proof checking.
    /// Includes resolve from the working directory. A failure leaves this compiler unchanged.
    pub fn compile_program(
        &mut self,
        filename: Option<String>,
        source: &str,
    ) -> Result<CompiledProgram, CompileError> {
        let mut next = self.clone();
        let (text, proofs) = next.compile_inner(filename.clone(), source)?;
        let mut parser = self.parser.clone().unwrap_or_else(|| {
            let mut graph = super::new_egraph();
            super::proofs::pipeline::register(&mut graph);
            graph.parser
        });
        let commands = parser
            .get_program_from_string(filename, &text)
            .map_err(|error| ParseError(egglog::span!(), error.to_string()))?;
        *self = next;
        let extractions = std::mem::take(&mut self.extract_requests);
        let substitutions = std::mem::take(&mut self.substitution_phases);
        Ok(CompiledProgram {
            commands,
            proofs,
            extractions,
            substitutions,
        })
    }

    fn compile_inner(
        &mut self,
        filename: Option<String>,
        source: &str,
    ) -> Result<(String, ProofRequests), CompileError> {
        let forms = read(filename, source, &mut BTreeSet::new())?;
        let result = self.program(&forms)?;
        let proofs = std::mem::take(&mut self.proof_requests);
        Ok((result, proofs))
    }

    fn program(&mut self, forms: &[(Form, Span)]) -> Result<String, ParseError> {
        // Hoist declarations only within a scope, never across push/pop. This
        // also lets successive files and REPL inputs extend an existing language.
        let mut out = Vec::new();
        let mut start = 0;
        for (i, (form, span)) in forms.iter().enumerate() {
            if matches!(form.call(), Ok(("push" | "pop", _))) {
                out.push(self.region(&forms[start..i])?);
                out.push(
                    self.command(form)
                        .map_err(|e| ParseError(span.clone(), e))?,
                );
                start = i + 1;
            }
        }
        out.push(self.region(&forms[start..])?);
        Ok(out.join("\n"))
    }

    fn region(&mut self, forms: &[(Form, Span)]) -> Result<String, ParseError> {
        let forms = self.state.disequality.lower(forms, &self.state.lang)?;
        let forms = forms.as_slice();
        let mut sorts = Vec::new();
        let mut ctors = Vec::new();
        for (f, span) in forms {
            declarations(f, &mut sorts, &mut ctors).map_err(|e| ParseError(span.clone(), e))?;
        }
        self.state.dirty |= !sorts.is_empty() || !ctors.is_empty();
        let fallback = forms
            .first()
            .map(|(_, s)| s.clone())
            .unwrap_or_else(|| egglog::span!());
        let mut out = Vec::new();
        let mut declared = sorts.iter().cloned().collect::<BTreeSet<_>>();
        for form in ctors.iter().chain(forms.iter().map(|(f, _)| f)) {
            if let Some(name) = declaration_name(form) {
                declared.insert(name.to_owned());
            }
        }
        if !sorts.is_empty() && !self.state.initialized {
            self.emit(&mut out, maintenance::shared(), None);
            self.state.initialized = true;
        }
        for sort in sorts {
            if sort == "Var" {
                return Err(ParseError(
                    fallback.clone(),
                    "Var is a built-in rigid sort".into(),
                ));
            }
            if self.state.lang.carriers.iter().any(|s| s.sort == sort) {
                return Err(ParseError(
                    fallback.clone(),
                    format!("equality sort {sort:?} is declared more than once"),
                ));
            }
            let s = Symbols::new(&sort, self.state.lang.carriers.len());
            self.emit(
                &mut out,
                maintenance::carrier(&s, self.options.proof_mode != ProofMode::Disabled),
                Some(&sort),
            );
            self.state.lang.carriers.push(s);
        }
        for f in ctors {
            let op = self
                .constructor(&f)
                .map_err(|e| ParseError(fallback.clone(), e))?;
            self.emit(
                &mut out,
                maintenance::constructor(
                    &op,
                    self.state.lang.symbols(&op.sort),
                    self.options.proof_mode != ProofMode::Disabled,
                ),
                Some(&op.name),
            );
            self.state.lang.constructors.insert(op.name.clone(), op);
        }
        self.state.declared.extend(declared);
        if let Some(name) = self
            .state
            .declared
            .intersection(&self.state.reserved)
            .next()
        {
            return Err(ParseError(
                fallback,
                format!("declaration {name:?} is reserved by the slotted encoding"),
            ));
        }
        if let Some(proofs) = &mut self.state.proofs {
            proofs
                .source
                .declare(forms)
                .map_err(|e| ParseError(fallback.clone(), e.to_string()))?;
        }
        for (f, span) in forms {
            let head = f.call().map_err(|e| ParseError(span.clone(), e))?.0;
            if !matches!(
                head,
                "sort"
                    | "constructor"
                    | "datatype"
                    | "datatype*"
                    | "let"
                    | "union"
                    | "rewrite"
                    | "run"
                    | "extract"
                    | "ruleset"
            ) {
                self.maintain(&mut out);
            }
            let command = self.command(f).map_err(|e| ParseError(span.clone(), e))?;
            if matches!(head, "let" | "union")
                && let Some(proofs) = &mut self.state.proofs
            {
                proofs
                    .source
                    .command(f, span)
                    .map_err(|e| ParseError(span.clone(), e.to_string()))?;
            }
            match head {
                "run" | "extract" => self.state.dirty = false,
                "let" | "union" if !command.is_empty() => self.state.dirty = true,
                "sort" | "constructor" | "datatype" | "datatype*" | "rewrite" | "let" | "check"
                | "fail" | "print-size" | "print-function" | "slotted-export" => {}
                _ => self.state.dirty = self.state.initialized,
            }
            out.push(command);
        }
        self.maintain(&mut out);
        Ok(out
            .into_iter()
            .filter(|s| !s.is_empty())
            .collect::<Vec<_>>()
            .join("\n"))
    }

    /// Batch insertions, but finish invariant maintenance before an observation
    /// or returning a compiled input to the caller.
    fn maintain(&mut self, out: &mut Vec<String>) {
        if self.state.dirty {
            out.push(self.schedule(0));
            self.state.dirty = false;
        }
    }

    fn schedule(&self, steps: usize) -> String {
        self.state.disequality.schedule(steps, self.state.rules > 0)
    }

    fn emit(&mut self, out: &mut Vec<String>, source: String, source_name: Option<&str>) {
        // Reserve the declarations actually emitted, except the source's own
        // sort or constructor. This also catches collisions across input files.
        for (form, _) in syntax::parse(None, &source).expect("generated declarations") {
            if let Some(name) = declaration_name(&form)
                && Some(name) != source_name
            {
                self.state.reserved.insert(name.to_owned());
            }
        }
        out.push(source);
    }

    fn constructor(&self, f: &Form) -> Result<Constructor, String> {
        source_constructor(
            f,
            self.state.lang.carriers.iter().map(|s| s.sort.as_str()),
            self.state.lang.constructors.values(),
        )
    }

    fn command(&mut self, f: &Form) -> Result<String, String> {
        let (head, args) = f.call()?;
        match head {
            "constructor" | "datatype" | "datatype*" => Ok(String::new()),
            "sort" if args.len() == 1 => Ok(String::new()),
            "let" => {
                if args.len() != 2 {
                    return Err("let expects a name and term".into());
                }
                let name = args[0].atom()?;
                if self.state.lang.globals.contains_key(name) {
                    return Err(format!("global {name:?} is already bound"));
                }
                if name.starts_with('$') {
                    return Err(
                        "a slotted global name must not start with $; $ introduces a slot".into(),
                    );
                }
                let t = self.term(&args[1], true, None)?;
                let bare_slot = matches!(t, Term::Slot(_))
                    || matches!(&t, Term::Global(n) if self.state.lang.global_slot(n).is_some());
                let encoded = if bare_slot {
                    String::new()
                } else {
                    format!("(let ${name} {})", self.state.lang.encode(&t))
                };
                self.state.lang.globals.insert(name.into(), t);
                Ok(encoded)
            }
            "union" => {
                if args.len() != 2 {
                    return Err("union expects two terms".into());
                }
                let (sort, terms) = self.common(args)?;
                if sort == "Var" {
                    return Err(
                        "Var names are rigid and cannot be unioned; use the variable constructor"
                            .into(),
                    );
                }
                Ok(format!(
                    "(union {} {})",
                    self.state.lang.encode(&terms[0]),
                    self.state.lang.encode(&terms[1])
                ))
            }
            "rewrite" => self.rewrite(args),
            "run" => {
                if self.state.lang.carriers.is_empty() {
                    return Err("no equality sort is declared".into());
                }
                if args.len() != 1 {
                    return Err("slotted run expects a nonnegative round count".into());
                }
                let n = args[0]
                    .atom()?
                    .parse::<usize>()
                    .map_err(|_| "run expects a nonnegative round count")?;
                if n > 0 && !self.state.substitutions.is_empty() {
                    let id = self.next_proof;
                    self.next_proof += 1;
                    self.substitution_phases.insert(
                        id,
                        Arc::new(super::proofs::runtime_substitution::Phase {
                            substitutions: self.state.substitutions.clone(),
                        }),
                    );
                    let mut commands = vec![self.schedule(0)];
                    for _ in 0..n {
                        commands
                            .push("(run-schedule (run) (saturate (run slotted-refine)))".into());
                        commands.push(format!("(slotted-substitute {id})"));
                        commands.push(self.schedule(0));
                    }
                    return Ok(commands.join("\n"));
                }
                Ok(self.schedule(n))
            }
            "push" => {
                if !args.is_empty() {
                    return Err("slotted push takes no arguments".into());
                }
                self.scopes.push(self.state.clone());
                Ok(f.render())
            }
            "pop" => {
                if !args.is_empty() {
                    return Err("slotted pop takes no arguments".into());
                }
                self.state = self
                    .scopes
                    .pop()
                    .ok_or("pop without a corresponding push")?;
                Ok(f.render())
            }
            "check" | "fail" => self.check(f, false),
            "extract" => {
                if args.len() != 1 {
                    return Err("slotted extract expects one term".into());
                }
                let t = self.term(&args[0], true, None)?;
                let sort = self.sort_of(&t)?;
                if sort == "Var" {
                    return Err(
                        "extract expects a term in an equality sort; use the variable constructor"
                            .into(),
                    );
                }
                self.state.extracts += 1;
                let i = self.state.extracts;
                let names = self
                    .state
                    .lang
                    .slot_names
                    .entries()
                    .map(|(name, id)| format!("(slot {id} {})", syntax::quote(name)))
                    .collect::<Vec<_>>()
                    .join(" ");
                let command = if matches!(
                    self.options.proof_mode,
                    ProofMode::Prove | ProofMode::Extract
                ) {
                    let id = self.next_proof;
                    self.next_proof += 1;
                    self.state
                        .proofs
                        .as_mut()
                        .unwrap()
                        .source
                        .command(f, &egglog::span!())
                        .map_err(|e| e.to_string())?;
                    let mut compiler = self.clone();
                    // The runtime certifies this extraction with one internal
                    // check. Reserve its rule name before compiling later input.
                    self.next_check += 1;
                    compiler.proof_requests.clear();
                    compiler.extract_requests.clear();
                    compiler.substitution_phases.clear();
                    self.extract_requests.insert(
                        id,
                        Arc::new(ExtractRequest {
                            compiler,
                            input: args[0].render(),
                        }),
                    );
                    format!("slotted-prove-extract {id}")
                } else {
                    "slotted-extract".into()
                };
                Ok(format!(
                    "(let $$slotted_extract{i} {})\n{}\n({command} $$slotted_extract{i} {} {names})",
                    self.state.lang.encode(&t),
                    self.schedule(0),
                    self.state.lang.edge(&t),
                ))
            }
            "rule" | "birewrite" => Err(format!(
                "{head} is not supported by the slotted frontend; use rewrite"
            )),
            "run-schedule" | "run-report" => Err(format!(
                "{head} cannot bypass slotted maintenance; use (run N)"
            )),
            _ => Ok(f.render()),
        }
    }

    fn sort_of(&self, t: &Term) -> Result<String, String> {
        self.state
            .lang
            .sort_of(t)
            .map(str::to_owned)
            .ok_or_else(|| "cannot determine the term's sort".into())
    }

    fn common(&mut self, forms: &[Form]) -> Result<(String, Vec<Term>), String> {
        let terms = forms
            .iter()
            .map(|f| self.term(f, true, None))
            .collect::<Result<Vec<_>, _>>()?;
        let sort = terms
            .iter()
            .find_map(|t| self.state.lang.sort_of(t))
            .map(str::to_owned)
            .map(Ok)
            .unwrap_or_else(|| self.sort_of(terms.first().ok_or("missing term")?))?;
        if terms
            .iter()
            .any(|t| self.state.lang.sort_of(t).is_some_and(|s| s != sort))
        {
            return Err("cannot compare terms of different equality sorts".into());
        }
        Ok((sort, terms))
    }

    fn term(&mut self, f: &Form, ground: bool, expected: Option<&str>) -> Result<Term, String> {
        let term = match f {
            Form::Atom(s) if s.starts_with('$') => {
                if ground {
                    Term::Slot(self.state.lang.slot_names.intern(s)?)
                } else {
                    Term::Slot(s.clone())
                }
            }
            Form::Atom(s) if self.state.lang.constructors.contains_key(s) => {
                return Err(format!("constructor {s} needs parentheses: ({s})"));
            }
            Form::Atom(s) if self.state.lang.globals.contains_key(s) => Term::Global(s.clone()),
            Form::Atom(s) if !ground => Term::Variable(s.clone()),
            Form::Atom(s) => return Err(format!("global {s:?} is not bound")),
            Form::List(_) => {
                let (head, args) = f.call()?;
                if head == "subst" {
                    if ground || args.len() != 3 {
                        return Err(
                            "subst expects three arguments on a rewrite right-hand side".into()
                        );
                    }
                    return Ok(Term::Subst(Box::new([
                        self.term(&args[0], false, expected)?,
                        self.term(&args[1], false, Some("Var"))?,
                        self.term(&args[2], false, expected)?,
                    ])));
                }
                let op = self
                    .state
                    .lang
                    .constructors
                    .get(head)
                    .cloned()
                    .ok_or_else(|| format!("unknown constructor {head:?}"))?;
                if args.len() != op.columns.len() {
                    return Err(format!(
                        "{head} takes {} arguments, given {}",
                        op.columns.len(),
                        args.len()
                    ));
                }
                let mut terms = Vec::new();
                for (col, a) in op.columns.iter().zip(args) {
                    terms.push(match col {
                        Column::Payload(sort) => {
                            let text = a
                                .atom()
                                .map_err(|_| "computed payloads are not supported")?;
                            if text.starts_with('"') || text.parse::<i64>().is_ok() {
                                if (sort == "String") != text.starts_with('"') {
                                    return Err(format!(
                                        "{head}: payload does not have sort {sort}"
                                    ));
                                }
                                Term::Payload(text.into())
                            } else if ground {
                                return Err("ground payloads must be literals".into());
                            } else {
                                Term::PayloadVariable(text.into())
                            }
                        }
                        Column::Child => self.term(a, ground, Some(&op.sort))?,
                        Column::Var | Column::Binder => {
                            let t = self.term(a, ground, Some("Var"))?;
                            match &t {
                                Term::Slot(_) => t,
                                Term::Global(n) if self.state.lang.global_slot(n).is_some() => {
                                    if ground {
                                        Term::Slot(self.state.lang.global_slot(n).unwrap().into())
                                    } else {
                                        t
                                    }
                                }
                                _ => {
                                    return Err(format!(
                                        "{head}'s Var column takes a slot literal or a global name"
                                    ));
                                }
                            }
                        }
                    });
                }
                Term::Node(head.into(), terms)
            }
        };
        if let (Some(want), Some(actual)) = (expected, self.state.lang.sort_of(&term))
            && want != actual
        {
            return Err(format!("term has sort {actual}, expected {want}"));
        }
        let mut term = term;
        if ground {
            self.state.lang.refresh_shadowed(&mut term);
            let mut slots = BTreeSet::new();
            term.slot_literals(&mut slots);
            for slot in slots {
                self.state.lang.slot_names.intern(&slot)?;
            }
        }
        Ok(term)
    }

    fn global_terms(&self, p: &mut Pattern, term: &mut Term, sort: Option<&str>) {
        match term {
            Term::Global(n) if self.state.lang.global_slot(n).is_some() => {
                let slot = self.state.lang.global_slot(n).unwrap();
                p.conditions
                    .concrete_slots
                    .insert(n.clone(), self.state.lang.slot_names.id(slot));
                *term = Term::Slot(n.clone());
            }
            Term::Global(_) => {
                let root = p.names.fresh("_global");
                p.values
                    .push((root.clone(), term.clone(), sort.map(str::to_owned)));
                *term = Term::Variable(root);
            }
            Term::Node(op, args) => {
                let constructor = &self.state.lang.constructors[op];
                for (arg, sort) in args.iter_mut().zip(constructor.input_sorts()) {
                    self.global_terms(p, arg, Some(sort));
                }
            }
            Term::Subst(args) => {
                for arg in args.iter_mut() {
                    self.global_terms(p, arg, sort);
                }
            }
            _ => {}
        }
    }

    fn pattern_at(&self, p: &mut Pattern, root: String, mut term: Term) -> Result<(), String> {
        match &term {
            Term::Node(_, _) => {
                self.global_terms(p, &mut term, None);
                let tmp = if p.patterns == 0 {
                    "_t".into()
                } else {
                    format!("_w{}_", p.patterns)
                };
                let atoms = flatten::flatten(&self.state.lang, &term, &root, &tmp, &mut p.names)?;
                p.proof_names.patterns.push(flatten::pattern_names(&atoms));
                p.atoms.extend(atoms);
                p.patterns += 1;
            }
            Term::Slot(_) => {
                return Err("a term pattern needs a variable constructor around its slot".into());
            }
            Term::Global(_) => {
                let sort = self.state.lang.sort_of(&term).map(str::to_owned);
                if sort.as_deref() == Some("Var") {
                    return Err(
                        "a term pattern needs a variable constructor around its slot".into(),
                    );
                }
                p.values.push((root, term, sort));
            }
            _ => return Err("expected a constructor pattern or term global".into()),
        }
        Ok(())
    }

    fn pattern_value(&self, p: &mut Pattern, term: Term) -> Result<String, String> {
        if let Term::Variable(name) = term {
            return Ok(name);
        }
        let root = p.names.fresh("_p");
        self.pattern_at(p, root.clone(), term)?;
        Ok(root)
    }

    fn pattern_slot(&self, p: &mut Pattern, form: &Form) -> Result<String, String> {
        let name = form.atom()?;
        if name.starts_with('$') {
            return Ok(name.into());
        }
        if self.state.lang.globals.contains_key(name)
            && let Some(slot) = self.state.lang.global_slot(name)
        {
            p.conditions
                .concrete_slots
                .insert(name.into(), self.state.lang.slot_names.id(slot));
            return Ok(name.into());
        }
        Err(format!(
            "expected a pattern slot or a global bound to a slot, got {name:?}"
        ))
    }

    /// Facts in checks and rewrite guards share names, bindings, and predicates.
    fn pattern_fact(&mut self, p: &mut Pattern, fact: &Form) -> Result<(), String> {
        let (kind, args) = fact.call()?;
        if let Some(comparison) = query::Comparison::parse(kind) {
            if args.len() != 2 {
                return Err(format!("{kind} requires two terms"));
            }
            if kind == "="
                && let Form::Atom(name) = &args[0]
                && !name.starts_with('$')
                && !self.state.lang.globals.contains_key(name)
                && matches!(&args[1], Form::List(_))
            {
                let term = self.term(&args[1], false, None)?;
                return self.pattern_at(p, name.clone(), term);
            }
            let a = self.term(&args[0], false, None)?;
            let b = self.term(&args[1], false, None)?;
            if kind == "=" {
                match (&a, &b) {
                    (Term::Variable(v), other) | (other, Term::Variable(v))
                        if !matches!(other, Term::Variable(_)) =>
                    {
                        return self.pattern_at(p, v.clone(), other.clone());
                    }
                    _ => {}
                }
            }
            let a = self.pattern_value(p, a)?;
            let b = self.pattern_value(p, b)?;
            p.conditions.comparisons.push((comparison, a, b));
        } else {
            match kind {
                "free" | "not-free" => {
                    if args.len() < 2 {
                        return Err(format!("{kind} expects a slot and at least one term"));
                    }
                    let slot = self.pattern_slot(p, &args[0])?;
                    let mut terms = Vec::new();
                    for form in &args[1..] {
                        let term = self.term(form, false, None)?;
                        terms.push(self.pattern_value(p, term)?);
                    }
                    p.conditions.free.push((kind == "free", slot, terms));
                }
                "free-names-are" => {
                    let form = args.first().ok_or("free-names-are expects a term")?;
                    let term = self.term(form, false, None)?;
                    let root = self.pattern_value(p, term)?;
                    let slots = args[1..]
                        .iter()
                        .map(|f| self.pattern_slot(p, f))
                        .collect::<Result<_, _>>()?;
                    p.conditions.free_names.push((root, slots));
                }
                _ if self.state.lang.constructors.contains_key(kind) => {
                    let term = self.term(fact, false, None)?;
                    self.pattern_value(p, term)?;
                }
                _ => return Err(format!("unsupported slotted query predicate {kind}")),
            }
        }
        Ok(())
    }

    fn finish_pattern(&self, p: &mut Pattern) -> Result<(), String> {
        let mut sorts = p
            .atoms
            .iter()
            .map(|a| self.state.lang.constructors[&a.op].sort.clone())
            .collect::<BTreeSet<_>>();
        for (_, term, expected) in &p.values {
            if let Some(sort) = expected
                .as_deref()
                .or_else(|| self.state.lang.sort_of(term))
            {
                sorts.insert(sort.to_owned());
            }
        }
        if sorts.len() > 1 {
            return Err(
                "cross-sort multipatterns cannot compare terms of different equality sorts".into(),
            );
        }
        let sort = sorts
            .into_iter()
            .next()
            .or_else(|| {
                (self.state.lang.carriers.len() == 1)
                    .then(|| self.state.lang.carriers[0].sort.clone())
            })
            .ok_or("query has no equality-sort context; include a constructor pattern")?;
        p.conditions.values = p
            .values
            .drain(..)
            .map(|(root, term, _)| (root, term, sort.clone()))
            .collect();
        if !p.atoms.is_empty() {
            p.atoms = query::connected(std::mem::take(&mut p.atoms));
        }
        Ok(())
    }

    fn rewrite(&mut self, args: &[Form]) -> Result<String, String> {
        let mut source = source_rewrite(args)?;
        self.state.dirty |= self.state.disequality.is_rule(&source.name);
        name_rewrite(
            &mut source,
            self.next_rule,
            (self.options.proof_mode != ProofMode::Disabled).then_some(&mut self.used_rule_names),
        );
        let (encoded, flattened) = self.lower_rewrite(&source)?;
        if let Some(proofs) = &mut self.state.proofs {
            proofs
                .source
                .add_rewrite(&source)
                .map_err(|e| e.to_string())?;
            let resolved = proofs
                .source
                .resolve_rewrite(&flattened.rule)
                .map_err(|e| e.to_string())?;
            proofs.flattened.insert(source.name.clone(), resolved);
            proofs.names.insert(source.name.clone(), flattened.names);
        }
        self.next_rule += 1;
        Ok(encoded)
    }

    pub(super) fn lower_rewrite(
        &mut self,
        source: &SourceRewrite,
    ) -> Result<(String, flatten::Rewrite), String> {
        let lhs_form = Form::from_expr(&source.lhs);
        let rhs_form = Form::from_expr(&source.rhs);
        let facts: Vec<_> = source.conditions.iter().map(Form::from_fact).collect();
        let mut forms = vec![lhs_form.clone(), rhs_form.clone()];
        forms.extend(facts.clone());
        let lhs = self.term(&lhs_form, false, None)?;
        let mut rhs = self.term(&rhs_form, false, None)?;
        let mut p = Pattern::new(&forms);
        let root = self.pattern_value(&mut p, lhs.clone())?;
        if !matches!(lhs, Term::Node(_, _)) {
            p.proof_names.patterns.insert(0, vec![]);
        }
        for fact in &facts {
            self.pattern_fact(&mut p, fact)?;
        }
        if self.options.no_aliasing && p.patterns > 1 {
            return Err("no-aliasing mode requires a single nested pattern".into());
        }
        if p.atoms.is_empty() && p.values.is_empty() {
            return Err("a rewrite needs a constructor pattern on the left or in :when".into());
        }
        if !p.values.iter().any(|(v, _, _)| v == &root)
            && !p.atoms.iter().any(|a| {
                a.root == root
                    || a.kids
                        .iter()
                        .any(|k| matches!(k, Term::Variable(v) if *v == root))
            })
        {
            return Err(format!("rewrite root {root:?} is not bound by a pattern"));
        }
        self.global_terms(&mut p, &mut rhs, None);
        // Proof reconstruction follows the source traversal. Matching may reorder
        // these atoms for joins, but the flattened source rule keeps their order.
        let source_atoms = p.atoms.clone();
        self.finish_pattern(&mut p)?;
        let mut flattened = flatten::rewrite(
            &self.state.lang,
            &root,
            &lhs,
            &rhs,
            &source_atoms,
            &p.conditions,
            p.proof_names,
        );
        let (mut encoded, names, substitution) = rewrite::compile(
            &self.state.lang,
            rewrite::Rewrite {
                root: &root,
                atoms: &p.atoms,
                rhs: &rhs,
                conditions: p.conditions,
                name: Some(&source.name),
                ordinal: self.state.rules,
                nested: self.options.no_aliasing,
                proofs: matches!(
                    self.options.proof_mode,
                    ProofMode::Prove | ProofMode::Extract
                ),
                maintenance: self.state.disequality.is_rule(&source.name),
            },
            flattened.names,
        )?;
        if let Some(substitution) = substitution {
            if self.state.substitutions.is_empty() {
                encoded.insert_str(0, "(ruleset slotted-subst-apply)\n");
            }
            self.state.substitutions.push(substitution);
        }
        self.state.rules += 1;
        flattened.names = names;
        flattened.rule.name = source.name.clone();
        Ok((encoded, flattened))
    }

    fn proof_claim(&mut self, facts: &[Form]) -> Result<Option<String>, String> {
        if facts.is_empty()
            || facts.iter().any(|fact| {
                !matches!(fact.call(), Ok(("=" | "renaming-=", terms)) if terms.len() == 2)
                    && !fact
                        .call()
                        .is_ok_and(|(head, _)| self.state.lang.constructors.contains_key(head))
            })
        {
            return Ok(None);
        }
        let mut p = Pattern::new(facts);
        let mut claims = Vec::new();
        for fact in facts {
            let (head, arguments) = fact.call()?;
            let existence;
            let (kind, terms) = if self.state.lang.constructors.contains_key(head) {
                existence = [fact.clone(), fact.clone()];
                ("=", existence.as_slice())
            } else {
                (head, arguments)
            };
            let mut roots = Vec::new();
            let mut patterns = Vec::new();
            for term in terms {
                let term = self.term(term, false, None)?;
                let mut slots = BTreeSet::new();
                term.slot_literals(&mut slots);
                for slot in slots {
                    self.state.lang.slot_names.intern(&slot)?;
                }
                let is_node = matches!(term, Term::Node(_, _));
                roots.push(self.pattern_value(&mut p, term)?);
                patterns.push(if is_node {
                    p.proof_names.patterns.last().unwrap().clone()
                } else {
                    vec![]
                });
            }
            p.conditions.comparisons.push((
                query::Comparison::parse(kind).unwrap(),
                roots[0].clone(),
                roots[1].clone(),
            ));
            claims.push(SlottedClaim {
                kind: kind.into(),
                lhs: terms[0].expr()?,
                rhs: terms[1].expr()?,
                lhs_root: roots[0].clone(),
                rhs_root: roots[1].clone(),
                slot_names: BTreeMap::new(),
                names: query::ProofNames {
                    patterns,
                    ..Default::default()
                },
            });
        }
        self.finish_pattern(&mut p)?;
        let q = self.compile_check(&p)?;
        for claim in &mut claims {
            claim.names.classes = q.classes.iter().cloned().collect();
            claim.names.readings = q.readings.clone();
            claim.names.atoms = q.atoms.clone();
            claim.names.frame = q.frame.clone();
            claim.slot_names = self
                .state
                .lang
                .slot_names
                .entries()
                .map(|(name, id)| (name.to_owned(), id))
                .collect();
        }
        let id = self.next_proof;
        self.next_proof += 1;
        self.proof_requests
            .insert(id, Arc::new(self.proof_environment(claims)?));
        let proof = format!("(slotted-prove {id} {})", q.body.join(" "));
        Ok(Some(self.refine_check(&q, &proof)?))
    }

    fn proof_environment(&self, claims: Vec<SlottedClaim>) -> Result<ProofRequest, String> {
        let proofs = self.state.proofs.as_ref().expect("proof compilation state");
        let source = proofs.source.snapshot().map_err(|e| e.to_string())?;
        let mut flattened = source.clone();
        for command in &mut flattened.commands {
            if let ResolvedNCommand::NormRule { rule } = command {
                *rule = proofs.flattened[&rule.name].clone();
            }
        }
        Ok(ProofRequest {
            source,
            flattened,
            names: proofs.names.clone(),
            claims,
            verify: self.options.proof_mode == ProofMode::Prove,
        })
    }

    fn compile_check(&self, p: &Pattern) -> Result<query::Query, String> {
        let anchor = p.atoms.first().map(|a| a.root.as_str()).or_else(|| {
            p.conditions
                .values
                .first()
                .map(|(root, _, _)| root.as_str())
        });
        query::compile(
            &self.state.lang,
            &p.atoms,
            &p.conditions,
            "_check_",
            true,
            anchor,
            self.options.no_aliasing,
        )
    }

    fn refine_check(&mut self, q: &query::Query, check: &str) -> Result<String, String> {
        let split = q.split.ok_or("check has no matching frame")?;
        let ordinal = self.next_check;
        self.next_check += 1;
        Ok(format!(
            "(push)\n(ruleset $$slotted_check)\n(rule ({}) ((Idx {} 0)) :ruleset $$slotted_check :name \"slotted/check/{ordinal}\")\n(run-schedule (run $$slotted_check))\n(run-schedule (saturate (run slotted-refine)))\n{check}\n(pop)",
            q.body[..split].join(" "),
            q.length
        ))
    }

    fn check(&mut self, f: &Form, negated: bool) -> Result<String, String> {
        let (head, args) = f.call()?;
        if head == "fail" {
            if args.len() != 1 || args[0].call()?.0 != "check" {
                return Err("slotted fail takes a check".into());
            }
            return self.check(&args[0], !negated);
        }
        if !negated
            && matches!(
                self.options.proof_mode,
                ProofMode::Prove | ProofMode::Extract
            )
            && let Some(proof) = self.proof_claim(args)?
        {
            return Ok(proof);
        }
        if args.is_empty() {
            return Ok(if negated { "(fail (check))" } else { "(check)" }.into());
        }
        if let [fact] = args
            && let (kind @ ("__internal-holds" | "__internal-not-holds"), values) = fact.call()?
        {
            if values.len() != 2 {
                return Err("holds expects a term and constructor name".into());
            }
            let ctor = values[1].atom()?;
            let op = self
                .state
                .lang
                .constructors
                .get(ctor)
                .ok_or("unknown constructor in holds")?
                .clone();
            let term = self.term(&values[0], false, None)?;
            if self.state.lang.sort_of(&term).is_some_and(|s| s != op.sort) {
                return Err("holds compares different carrier sorts".into());
            }
            let mut names = Pattern::new(args).names;
            let mut pattern = vec![Form::Atom(ctor.into())];
            for column in op.columns {
                let stem = if matches!(column, Column::Var | Column::Binder) {
                    "$_bound"
                } else {
                    "_child"
                };
                pattern.push(Form::Atom(names.fresh(stem)));
            }
            let check = Form::List(vec![
                Form::Atom("check".into()),
                Form::List(vec![
                    Form::Atom("=".into()),
                    values[0].clone(),
                    Form::List(pattern),
                ]),
            ]);
            return self.check(&check, negated != (kind == "__internal-not-holds"));
        }
        let mut p = Pattern::new(args);
        for fact in args {
            self.pattern_fact(&mut p, fact)?;
        }
        self.finish_pattern(&mut p)?;
        let q = self.compile_check(&p)?;
        if self.options.proof_mode != ProofMode::Disabled {
            let check = call("check", q.body.iter().cloned());
            let check = if negated {
                format!("(fail {check})")
            } else {
                check
            };
            return self.refine_check(&q, &check);
        }
        Ok(super::check::emit(&q, f, !negated))
    }
}

pub(super) fn source_constructor<'a>(
    f: &Form,
    carriers: impl Iterator<Item = &'a str>,
    constructors: impl Iterator<Item = &'a Constructor>,
) -> Result<Constructor, String> {
    let carriers = carriers.collect::<BTreeSet<_>>();
    let constructors = constructors.collect::<Vec<_>>();
    let (_, args) = f.call()?;
    if args.len() < 3 {
        return Err("constructor expects a name, input sorts, and output sort".into());
    }
    let name = args[0].symbol()?.to_owned();
    if name.starts_with('$') {
        return Err("constructor names cannot start with $".into());
    }
    let sort = args[2].symbol()?.to_owned();
    if constructors.iter().any(|op| op.name == name) {
        return Err(format!("constructor {name:?} is declared more than once"));
    }
    if !carriers.contains(sort.as_str()) {
        return Err(format!(
            "constructor {name}: output sort {sort} is not a declared equality sort"
        ));
    }
    let cols = args[1]
        .list()?
        .iter()
        .map(Form::atom)
        .collect::<Result<Vec<_>, _>>()?;
    let child_count = cols
        .iter()
        .filter(|s| **s == "Var" || carriers.contains(**s))
        .count();
    let mut binders = BTreeSet::new();
    let mut in_binder = false;
    for f in &args[3..] {
        let t = f.atom()?;
        if t == ":binder" {
            in_binder = true;
        } else if t.starts_with(':') {
            return Err(format!("constructor {name}: option {t} is not supported"));
        } else {
            if !in_binder {
                return Err(format!("constructor {name}: expected :binder"));
            }
            let i = t
                .parse::<usize>()
                .map_err(|_| format!("constructor {name}: invalid binder position {t}"))?;
            if !binders.insert(i) {
                return Err(format!("constructor {name}: duplicate binder position"));
            }
        }
    }
    if let (Some(&lo), Some(&hi)) = (binders.first(), binders.last()) {
        if hi >= child_count.saturating_sub(1) {
            return Err(format!(
                "constructor {name}: binder positions must cover a following child"
            ));
        }
        if binders.len() != hi - lo + 1 {
            return Err(format!(
                "constructor {name}: binder positions must be contiguous"
            ));
        }
    }
    let variable = cols == ["Var"] && binders.is_empty();
    if variable
        && let Some(previous) = constructors
            .iter()
            .find(|op| op.sort == sort && op.columns == [Column::Var])
    {
        return Err(format!(
            "equality sort {sort:?} already has variable constructor {}",
            previous.name
        ));
    }
    let mut child = 0;
    let mut columns = Vec::new();
    for col in cols {
        if col == "Var" {
            columns.push(if binders.contains(&child) {
                    Column::Binder
                } else if variable {
                    Column::Var
                } else {
                    return Err(format!("constructor {name}: Var arguments must be binders or the unary variable constructor"));
                });
            child += 1;
        } else if carriers.contains(col) {
            if col != sort {
                return Err(format!(
                    "constructor {name}: cross-sort slotted children are not supported"
                ));
            }
            if binders.contains(&child) {
                return Err(format!(
                    "constructor {name}: binder columns must have sort Var"
                ));
            }
            columns.push(Column::Child);
            child += 1;
        } else if ["i64", "String"].contains(&col) {
            columns.push(Column::Payload(col.into()));
        } else {
            return Err(format!(
                "constructor {name}: unsupported payload sort {col}"
            ));
        }
    }
    Ok(Constructor {
        name,
        sort,
        columns,
    })
}

pub(super) fn name_rewrite(
    source: &mut SourceRewrite,
    ordinal: usize,
    used: Option<&mut BTreeSet<String>>,
) {
    let name = if source.name.is_empty() {
        format!("_slotted_match_{ordinal}")
    } else {
        source.name.clone()
    };
    source.name = name.clone();
    if let Some(used) = used {
        let mut suffix = ordinal;
        while !used.insert(source.name.clone()) {
            source.name = format!("{name}#{suffix}");
            suffix += 1;
        }
    }
}

pub(super) fn source_rewrite(args: &[Form]) -> Result<SourceRewrite, String> {
    if args.len() < 2 {
        return Err("rewrite needs a left- and right-hand side".into());
    }
    let mut source = SourceRewrite {
        span: egglog::span!(),
        lhs: args[0].expr()?,
        rhs: args[1].expr()?,
        conditions: vec![],
        name: String::new(),
    };
    let mut when_seen = false;
    let mut i = 2;
    while i < args.len() {
        let key = args[i].atom()?;
        i += 1;
        let start = i;
        while i < args.len() && !matches!(&args[i], Form::Atom(s) if s.starts_with(':')) {
            i += 1;
        }
        let values = &args[start..i];
        match key {
            ":ruleset" => return Err("named rulesets are not supported by the slotted schedule; omit :ruleset and use (run N)".into()),
            ":name" => {
                let [value] = values else { return Err(":name expects one argument".into()) };
                source.name = unquote(value.atom()?)?;
            }
            ":when" => {
                if when_seen { return Err("several :when clauses; use one list of facts".into()); }
                when_seen = true;
                let [value] = values else { return Err(":when takes one list of facts".into()) };
                let facts = value.list()?;
                if facts.iter().any(|fact| !matches!(fact, Form::List(_))) {
                    return Err(":when takes a list of facts".into());
                }
                source.conditions = facts.iter().map(Form::fact).collect::<Result<_, _>>()?;
            }
            _ => return Err(format!("unsupported rewrite option {key}")),
        }
    }
    Ok(source)
}

fn read(
    filename: Option<String>,
    source: &str,
    active: &mut BTreeSet<std::path::PathBuf>,
) -> Result<Vec<(Form, Span)>, ParseError> {
    expand_includes(syntax::parse(filename, source)?, active)
}

pub(super) fn expand_includes(
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

pub(super) fn declarations(
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
fn declaration_name(form: &Form) -> Option<&str> {
    let (head, args) = form.call().ok()?;
    matches!(
        head,
        "sort" | "constructor" | "function" | "relation" | "ruleset"
    )
    .then(|| args.first()?.atom().ok())
    .flatten()
}

fn unquote(s: &str) -> Result<String, String> {
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
