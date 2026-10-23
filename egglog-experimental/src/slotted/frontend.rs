//! An explicit slotted-source to ordinary-egglog pass. Evaluation stays in egglog.
use super::{
    maintenance,
    model::*,
    query, rewrite,
    syntax::{self, Form},
};
use egglog::ast::{ParseError, Span};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Copy, Debug, Default)]
/// Control source-level slotted matching semantics.
pub struct Options {
    /// Match the reference nested matcher's restriction on non-pattern aliasing.
    pub no_aliasing: bool,
}

struct Claim {
    facts: Vec<String>,
    invocations: Vec<(String, String)>,
}

#[derive(Clone)]
struct State {
    lang: Language,
    initialized: bool,
    rules: usize,
    extracts: usize,
    reserved: BTreeSet<String>,
    declared: BTreeSet<String>,
}

impl Default for State {
    fn default() -> Self {
        Self {
            lang: Language::default(),
            initialized: false,
            rules: 0,
            extracts: 0,
            reserved: [
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
        }
    }
}

/// Compiler state for successive input files or complete REPL commands.
/// Tracks declarations, globals, rewrites, and push/pop scopes.
#[derive(Clone, Default)]
pub struct Compiler {
    options: Options,
    state: State,
    scopes: Vec<State>,
}

impl Compiler {
    /// Create a compiler with an empty source environment.
    pub fn new(options: Options) -> Self {
        Self {
            options,
            ..Default::default()
        }
    }

    /// Compile a program without evaluating it. Includes resolve from the process
    /// working directory.
    /// A failed compilation leaves this compiler unchanged.
    pub fn compile(
        &mut self,
        filename: Option<String>,
        source: &str,
    ) -> Result<String, ParseError> {
        let mut next = self.clone();
        let forms = read(filename, source, &mut BTreeSet::new())?;
        let result = next.program(&forms)?;
        *self = next;
        Ok(result)
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
        let mut sorts = Vec::new();
        let mut ctors = Vec::new();
        for (f, span) in forms {
            declarations(f, &mut sorts, &mut ctors).map_err(|e| ParseError(span.clone(), e))?;
        }
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
            if self.state.lang.carriers.iter().any(|s| s.sort == sort) {
                return Err(ParseError(
                    fallback.clone(),
                    format!("equality sort {sort:?} is declared more than once"),
                ));
            }
            let s = Symbols::new(&sort, self.state.lang.carriers.len());
            self.emit(&mut out, maintenance::carrier(&s), Some(&sort));
            self.state.lang.carriers.push(s);
        }
        for f in ctors {
            let op = self
                .constructor(&f)
                .map_err(|e| ParseError(fallback.clone(), e))?;
            self.emit(
                &mut out,
                maintenance::constructor(&op, self.state.lang.symbols(&op.sort)),
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
        for (f, span) in forms {
            out.push(self.command(f).map_err(|e| ParseError(span.clone(), e))?);
        }
        Ok(out
            .into_iter()
            .filter(|s| !s.is_empty())
            .collect::<Vec<_>>()
            .join("\n"))
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
        let (_, args) = f.call()?;
        if args.len() < 3 {
            return Err("constructor expects a name, input sorts, and output sort".into());
        }
        let name = args[0].symbol()?.to_owned();
        if name.starts_with('$') {
            return Err("constructor names cannot start with $".into());
        }
        let sort = args[2].symbol()?.to_owned();
        if self.state.lang.constructors.contains_key(&name) {
            return Err(format!("constructor {name:?} is declared more than once"));
        }
        let carriers = self
            .state
            .lang
            .carriers
            .iter()
            .map(|s| s.sort.as_str())
            .collect::<BTreeSet<_>>();
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
        let child_count = cols.iter().filter(|s| carriers.contains(**s)).count();
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
        let mut child = 0;
        let mut columns = Vec::new();
        for col in cols {
            if carriers.contains(col) {
                if col != sort {
                    return Err(format!(
                        "constructor {name}: cross-sort slotted children are not supported"
                    ));
                }
                columns.push(if binders.contains(&child) {
                    Column::Binder
                } else {
                    Column::Child
                });
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
                if matches!(t, Term::Slot(_)) {
                    return Err(
                        "a global cannot currently store the invocation of a bare slot".into(),
                    );
                }
                let sort = self.sort_of(&t)?;
                let encoded = self.state.lang.encode_top(&t, &sort);
                self.state.lang.globals.insert(name.into(), t);
                Ok(format!("(let ${name} {encoded})"))
            }
            "union" => {
                if args.len() != 2 {
                    return Err("union expects two terms".into());
                }
                let (sort, terms) = self.common(args)?;
                Ok(format!(
                    "(union {} {})",
                    self.state.lang.encode_top(&terms[0], &sort),
                    self.state.lang.encode_top(&terms[1], &sort)
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
                Ok(maintenance::schedule(n, self.state.rules > 0))
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
            "check" | "fail" => self.check(f),
            "extract" => {
                let t = self.term(args.first().ok_or("extract expects a term")?, true, None)?;
                let sort = self.sort_of(&t)?;
                self.state.extracts += 1;
                let i = self.state.extracts;
                let sy = self.state.lang.symbols(&sort);
                Ok(format!(
                    "(function _leader{i} () {sort} :merge (ordering-min old new))\n(ruleset _extract{i})\n(rule (({} {} _m _l)) ((set (_leader{i}) _l)) :ruleset _extract{i})\n(run-schedule (saturate (run _extract{i})))\n(extract (_leader{i}))",
                    sy.renames,
                    self.state.lang.encode_top(&t, &sort)
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
            .or_else(|| {
                (self.state.lang.carriers.len() == 1)
                    .then(|| self.state.lang.carriers[0].sort.clone())
            })
            .ok_or_else(|| {
                "bare slot has no equality-sort context; put it under a constructor".into()
            })
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
            Form::Atom(s) if self.state.lang.globals.contains_key(s) => {
                if ground {
                    Term::Global(s.clone())
                } else {
                    self.expand(&self.state.lang.globals[s])
                }
            }
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
                        self.term(&args[1], false, expected)?,
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
                        Column::Binder => {
                            let t = self.term(a, ground, Some(&op.sort))?;
                            if !matches!(t, Term::Slot(_)) {
                                return Err(format!("{head}'s binder column takes a slot literal"));
                            }
                            t
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

    fn expand(&self, t: &Term) -> Term {
        match t {
            Term::Global(n) => self.expand(&self.state.lang.globals[n]),
            Term::Node(n, args) => {
                Term::Node(n.clone(), args.iter().map(|a| self.expand(a)).collect())
            }
            _ => t.clone(),
        }
    }

    fn rewrite(&mut self, args: &[Form]) -> Result<String, String> {
        if args.len() < 2 {
            return Err("rewrite needs a left- and right-hand side".into());
        }
        let lhs = self.term(&args[0], false, None)?;
        let rhs = self.term(&args[1], false, None)?;
        // Reserve the entire source rule before allocating roots, including
        // names introduced only in :when or used on the right-hand side.
        fn reserve(form: &Form, names: &mut query::PatternNames) {
            match form {
                Form::Atom(name) => names.reserve(name),
                Form::List(forms) => {
                    for form in forms {
                        reserve(form, names);
                    }
                }
            }
        }
        let mut names = query::PatternNames::default();
        for form in args {
            reserve(form, &mut names);
        }
        // A named root can be bound by the multipattern. This also permits a
        // rewrite of a child matched inside another atom of a multipattern.
        let (root, mut atoms) = if let Term::Variable(v) = &lhs {
            (v.clone(), Vec::new())
        } else {
            let root = names.fresh("_p");
            let atoms = query::flatten(&self.state.lang, &lhs, &root, "_t", &mut names)?;
            (root, atoms)
        };
        let mut conditions = query::Conditions::default();
        let mut name = None;
        let mut side = 0;
        let mut when_seen = false;
        let mut i = 2;
        while i < args.len() {
            let key = args[i].atom()?;
            i += 1;
            let start = i;
            while i < args.len() && !matches!(&args[i],Form::Atom(s) if s.starts_with(':')) {
                i += 1;
            }
            let values = &args[start..i];
            match key {
                ":ruleset" => {
                    return Err("named rulesets are not supported by the slotted schedule; omit :ruleset and use (run N)".into());
                }
                ":name" => {
                    if values.len() != 1 {
                        return Err(format!("{key} expects one argument"));
                    }
                    name = Some(unquote(values[0].atom()?)?);
                }
                ":when" => {
                    if when_seen {
                        return Err("several :when clauses; use one list of facts".into());
                    }
                    when_seen = true;
                    if values.len() != 1 {
                        return Err(":when takes one list of facts".into());
                    }
                    let facts = values[0].list()?;
                    if facts.iter().any(|f| !matches!(f, Form::List(_))) {
                        return Err(":when takes a list of facts".into());
                    }
                    for fact in facts {
                        let (kind, rest) = fact.call()?;
                        let mut extra = Vec::new();
                        match (kind, query::Comparison::parse(kind)) {
                            (_, Some(comparison))
                                if rest.len() == 2 && matches!(rest[1], Form::Atom(_)) =>
                            {
                                conditions.comparisons.push((
                                    comparison,
                                    rest[0].atom()?.to_owned(),
                                    rest[1].atom()?.to_owned(),
                                ));
                            }
                            ("=", _) if rest.len() == 2 => {
                                extra.push((rest[0].atom()?.to_owned(), rest[1].clone()))
                            }
                            ("free" | "not-free", _) if rest.len() >= 2 => {
                                let slot = rest[0].atom()?.to_owned();
                                let mut pvars = Vec::new();
                                for f in &rest[1..] {
                                    match f {
                                        Form::Atom(v) => pvars.push(v.clone()),
                                        _ => {
                                            let v = names.fresh(&format!("_cond{side}"));
                                            side += 1;
                                            pvars.push(v.clone());
                                            extra.push((v, f.clone()));
                                        }
                                    }
                                }
                                conditions.free.push((kind == "free", slot, pvars));
                            }
                            ("free-names-are", _) if !rest.is_empty() => {
                                let v = match &rest[0] {
                                    Form::Atom(v) => v.clone(),
                                    f => {
                                        let v = names.fresh(&format!("_cond{side}"));
                                        side += 1;
                                        extra.push((v.clone(), f.clone()));
                                        v
                                    }
                                };
                                let slots = rest[1..]
                                    .iter()
                                    .map(|s| s.atom().map(str::to_owned))
                                    .collect::<Result<Vec<_>, _>>()?;
                                conditions.free_names.push((v, slots));
                            }
                            (kind, _) if self.state.lang.constructors.contains_key(kind) => {
                                let v = names.fresh(&format!("_fact{side}"));
                                side += 1;
                                extra.push((v, fact.clone()));
                            }
                            _ => return Err(format!("unsupported slotted side condition {kind}")),
                        }
                        for (v, f) in extra {
                            if self.options.no_aliasing {
                                return Err(
                                    "no-aliasing mode requires a single nested pattern".into()
                                );
                            }
                            let t = self.term(&f, false, None)?;
                            atoms.extend(query::flatten(
                                &self.state.lang,
                                &t,
                                &v,
                                &format!("_w{side}_"),
                                &mut names,
                            )?);
                            side += 1;
                        }
                    }
                }
                _ => return Err(format!("unsupported rewrite option {key}")),
            }
        }
        let first = atoms
            .first()
            .ok_or("a rewrite needs a constructor pattern on the left or in :when")?;
        if !atoms.iter().any(|a| {
            a.root == root
                || a.kids
                    .iter()
                    .any(|k| matches!(k, Term::Variable(v) if *v == root))
        }) {
            return Err(format!("rewrite root {root:?} is not bound by a pattern"));
        }
        let sort = &self.state.lang.constructors[&first.op].sort;
        if atoms
            .iter()
            .any(|a| self.state.lang.constructors[&a.op].sort != *sort)
        {
            return Err("cross-sort multipatterns are not supported".into());
        }
        let atoms = query::connected(atoms);
        let result = rewrite::compile(
            &self.state.lang,
            rewrite::Rewrite {
                root: &root,
                atoms: &atoms,
                rhs: &rhs,
                conditions,
                name: name.as_deref(),
                ordinal: self.state.rules,
                nested: self.options.no_aliasing,
            },
        )?;
        self.state.rules += 1;
        Ok(result)
    }

    fn matches(&self, terms: &[Term], sort: &str) -> Result<Claim, String> {
        let lang = &self.state.lang;
        let sy = lang.symbols(sort);
        let mut facts = Vec::new();
        let mut matched = Vec::new();
        for (i, t) in terms.iter().enumerate() {
            if let Term::Slot(s) = t {
                let c = format!("({} 0)", sy.var);
                matched.push((
                    c.clone(),
                    format!(
                        "(compose (map-of 0 {}) ({} {c}))",
                        lang.slot_names.id(s),
                        sy.free_vars
                    ),
                ));
                continue;
            }
            let mut pattern = self.expand(t);
            let mut used = BTreeSet::new();
            pattern.slot_literals(&mut used);
            rename_binders(lang, &mut pattern, &BTreeMap::new(), &mut used, &mut 0);
            let root = format!("_c{i}");
            let atoms = query::flatten(
                lang,
                &pattern,
                &root,
                &format!("_c{i}t"),
                &mut query::PatternNames::default(),
            )?;
            let atoms = query::connected(atoms);
            let q = query::compile(
                lang,
                &atoms,
                &query::Conditions::default(),
                &format!("_c{i}"),
                false,
                None,
                false,
            )?;
            let c = q.class(&root)?;
            let mut free = lang
                .slots(t)
                .into_iter()
                .map(|s| (lang.slot_names.id(&s), s))
                .collect::<Vec<_>>();
            free.sort();
            let mut pairs = Vec::new();
            for (id, s) in free {
                pairs.push(
                    q.slots
                        .get(&s)
                        .ok_or_else(|| format!("claim lost free slot {s}"))?
                        .clone(),
                );
                pairs.push(id.to_string());
            }
            let frame = if pairs.is_empty() {
                "(map-empty)".into()
            } else {
                call("map-of", pairs)
            };
            matched.push((c, format!("(compose {frame} {})", q.maps[&root])));
            facts.extend(q.body);
        }
        Ok(Claim {
            facts,
            invocations: matched,
        })
    }

    fn check(&mut self, f: &Form) -> Result<String, String> {
        let (head, mut args) = f.call()?;
        let negated = head == "fail";
        let mut command = f;
        if negated {
            if args.len() != 1 {
                return Err("fail takes one check".into());
            }
            command = &args[0];
            let (h, a) = command.call()?;
            if h != "check" {
                return Err("slotted fail takes a check".into());
            }
            args = a;
        }
        if args.len() != 1 {
            return Ok(f.render());
        }
        let (kind, terms) = args[0].call()?;
        let (mut facts, negative) = match (kind, query::Comparison::parse(kind)) {
            (_, Some(comparison)) => {
                if terms.len() != 2 {
                    return Err("equality requires two terms".into());
                }
                let (sort, ts) = self.common(terms)?;
                let Claim {
                    mut facts,
                    invocations: matched,
                } = self.matches(&ts, &sort)?;
                let (a, b) = (&matched[0], &matched[1]);
                // Negate existence of an equal invocation, not individual
                // matches: another representative may still prove equality.
                let positive = query::Comparison {
                    negated: false,
                    ..comparison
                };
                facts.extend(positive.classes(&a.0, &b.0));
                facts.extend(positive.invocations(
                    &self.state.lang.symbols(&sort).group,
                    (&a.0, &a.1),
                    (&b.0, &b.1),
                ));
                (facts, comparison.negated)
            }
            ("free" | "not-free", _) => {
                if terms.len() < 2 {
                    return Err(format!("{kind} expects a slot and at least one term"));
                }
                let name = self.state.lang.slot_names.intern(terms[0].atom()?)?;
                let slot = self.state.lang.slot_names.id(&name).to_string();
                let (sort, ts) = self.common(&terms[1..])?;
                let Claim {
                    mut facts,
                    invocations,
                } = self.matches(&ts, &sort)?;
                let maps = invocations.into_iter().map(|(_, m)| m).collect::<Vec<_>>();
                facts.push(query::free_condition(true, &slot, &maps));
                (facts, kind == "not-free")
            }
            ("free-names-are" | "__internal-holds" | "__internal-not-holds", _) => {
                let t = self.term(terms.first().ok_or("claim requires a term")?, true, None)?;
                let sort = self.sort_of(&t)?;
                let Claim {
                    mut facts,
                    invocations: matched,
                } = self.matches(&[t], &sort)?;
                let (c, m) = &matched[0];
                if kind == "free-names-are" {
                    let mut slots = Vec::new();
                    for s in &terms[1..] {
                        let name = self.state.lang.slot_names.intern(s.atom()?)?;
                        let s = self.state.lang.slot_names.id(&name).to_string();
                        slots.push(s);
                    }
                    facts.push(query::free_names_condition(m, &slots));
                } else {
                    if terms.len() != 2 {
                        return Err("holds expects a term and constructor name".into());
                    }
                    let name = terms[1].atom()?;
                    let op = self
                        .state
                        .lang
                        .constructors
                        .get(name)
                        .ok_or_else(|| format!("unknown constructor {name}"))?;
                    if op.sort != sort {
                        return Err("holds compares different carrier sorts".into());
                    }
                    let n = op
                        .columns
                        .iter()
                        .map(|c| {
                            if matches!(c, Column::Payload(_)) {
                                1
                            } else {
                                2
                            }
                        })
                        .sum();
                    let row = call(name, (0..n).map(|i| format!("_hc{i}")));
                    let table = &self.state.lang.symbols(&sort).renames;
                    facts.extend([
                        format!("({table} {c} _hm1 _hl)"),
                        format!("({table} _hn _hm2 _hl)"),
                        format!("(= _hn {row})"),
                    ]);
                }
                (facts, kind == "__internal-not-holds")
            }
            _ => {
                return Ok(if negated {
                    format!("(fail {})", command.render())
                } else {
                    command.render()
                });
            }
        };
        let check = call("check", facts.drain(..));
        Ok(if negative != negated {
            format!("(fail {check})")
        } else {
            check
        })
    }
}

fn rename_binders(
    lang: &Language,
    t: &mut Term,
    outer: &BTreeMap<String, String>,
    used: &mut BTreeSet<String>,
    counter: &mut usize,
) {
    match t {
        Term::Slot(s) => {
            if let Some(n) = outer.get(s) {
                *s = n.clone();
            }
        }
        Term::Node(n, args) => {
            let op = &lang.constructors[n];
            let mut inner = outer.clone();
            for (col, arg) in op.columns.iter().zip(args.iter_mut()) {
                if *col == Column::Binder
                    && let Term::Slot(s) = arg
                {
                    let fresh = loop {
                        *counter += 1;
                        let n = format!("$_b{counter}");
                        if used.insert(n.clone()) {
                            break n;
                        }
                    };
                    inner.insert(s.clone(), fresh.clone());
                    *s = fresh;
                }
            }
            let mut child = 0;
            for (col, arg) in op.columns.iter().zip(args) {
                match col {
                    Column::Child => {
                        rename_binders(
                            lang,
                            arg,
                            if Some(child) == op.covered() {
                                &inner
                            } else {
                                outer
                            },
                            used,
                            counter,
                        );
                        child += 1;
                    }
                    Column::Binder => child += 1,
                    _ => {}
                }
            }
        }
        _ => {}
    }
}

fn read(
    filename: Option<String>,
    source: &str,
    active: &mut BTreeSet<std::path::PathBuf>,
) -> Result<Vec<(Form, Span)>, ParseError> {
    let mut out = Vec::new();
    for (form, span) in syntax::parse(filename, source)? {
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

fn declarations(f: &Form, sorts: &mut Vec<String>, ctors: &mut Vec<Form>) -> Result<(), String> {
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
