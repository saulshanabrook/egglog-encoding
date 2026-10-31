//! Native source rules, declaration scopes, and binding semantics for proof checking.

use super::format::{Claim, ClaimKind};
use super::guards::{GUARDS, GuardSignature};
use super::terms::{FreshSlots, Renaming, slot_of};
use super::{HashMap, HashSet};
use crate::slotted::var_sort::VarSort;
use egglog::ast::{
    Expr, Fact, FunctionDecl, GenericAction, GenericActions, ResolvedExpr, ResolvedFact,
    ResolvedRule, Rule, Schema,
};
use egglog::prelude::BaseSort;
use egglog::sort::{EqSort, UnitSort};
use egglog::util::{FreshGen, INTERNAL_SYMBOL_PREFIX, IndexMap, SymbolGen};
use egglog::{EGraph, ResolvedCall, Term, TermDag, TermId};
use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::fmt::{self, Display, Formatter};

pub use crate::slotted::model::{Column as ColumnKind, Constructor};

/// The resolved endpoints of a top-level `(union a b)`.
#[derive(Clone, Debug)]
pub struct Union {
    /// The union's left source term.
    pub lhs: TermId,
    /// The union's right source term.
    pub rhs: TermId,
}

/// A native source rule with its declaration-scoped global bindings.
#[derive(Clone, Debug)]
pub struct SourceRule {
    /// The original rewrite desugared to a typed rule.
    pub rule: ResolvedRule,
    /// Captured globals keyed by their resolved identities.
    pub globals: IndexMap<String, TermId>,
}

pub(super) trait SourceFact {
    fn terms(&self) -> Vec<&ResolvedExpr>;
    fn binding(&self) -> Option<(&String, &ResolvedExpr)>;
}

impl SourceFact for ResolvedFact {
    fn terms(&self) -> Vec<&ResolvedExpr> {
        match self {
            Self::Eq(_, a, b) => vec![a, b],
            Self::Fact(ResolvedExpr::Call(_, ResolvedCall::Primitive(_), args)) => {
                args.iter().collect()
            }
            Self::Fact(expr) => vec![expr],
        }
    }

    fn binding(&self) -> Option<(&String, &ResolvedExpr)> {
        match self {
            Self::Eq(_, ResolvedExpr::Var(_, var), rhs) => Some((&var.name, rhs)),
            _ => None,
        }
    }
}

pub(super) fn pattern_term(dag: &mut TermDag, expr: &ResolvedExpr) -> TermId {
    dag.expr_to_term(&expr.clone().make_unresolved())
}

#[derive(Clone, Debug, Default)]
/// Source declarations and axioms used by the independent proof checker.
pub struct SlottedProgram {
    /// Ground source slot spellings and their identities in the encoding.
    pub slot_names: BTreeMap<String, i64>,
    /// Carrier sorts visible at this point in the source program.
    pub sorts: BTreeSet<String>,
    /// Constructor signatures indexed by source name.
    pub constructors: HashMap<String, Constructor>,
    /// Source rewrites indexed by their proof names.
    pub rewrites: HashMap<String, SourceRule>,
    /// Globals, with their terms resolved: a global's term never mentions a global.
    pub lets: IndexMap<String, TermId>,
    /// Equalities explicitly asserted by source unions.
    pub unions: Vec<Union>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
/// A malformed or unsupported source form.
pub struct SourceError(pub String);

impl Display for SourceError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

impl Error for SourceError {}

/// The carrier sort of a program that has only one, as the convenience
/// constructors below assume.
pub const SINGLE_SORT: &str = "U";

impl SourceRule {
    pub(super) fn endpoints(&self) -> (&ResolvedExpr, &ResolvedExpr) {
        let [GenericAction::Union(_, lhs, rhs)] = self.rule.head.0.as_slice() else {
            unreachable!("source rewrites have one union action")
        };
        (lhs, rhs)
    }

    pub(super) fn conditions(&self) -> &[ResolvedFact] {
        &self.rule.body[1..]
    }

    pub(super) fn patterns(&self) -> impl Iterator<Item = &ResolvedExpr> {
        let (lhs, rhs) = self.endpoints();
        [lhs, rhs]
            .into_iter()
            .chain(self.conditions().iter().flat_map(SourceFact::terms))
    }

    /// Instantiate a source pattern, resolving globals to their fixed terms.
    pub fn instantiate(
        &self,
        dag: &mut TermDag,
        term: TermId,
        substitution: &HashMap<String, TermId>,
    ) -> Result<TermId, String> {
        let mut bindings = substitution.clone();
        bindings.extend(
            self.globals
                .iter()
                .map(|(name, &term)| (name.clone(), term)),
        );
        super::terms::instantiate(dag, term, &bindings)
    }

    /// Variables of a source pattern; global references are not variables.
    pub fn pattern_vars(&self, dag: &TermDag, term: TermId) -> Vec<String> {
        super::terms::pattern_vars(dag, term)
            .into_iter()
            .filter(|v| !self.globals.contains_key(v))
            .collect()
    }
}

impl SlottedProgram {
    /// Declare a constructor in the single-sort convenience program.
    pub fn add_constructor(&mut self, name: &str, columns: Vec<ColumnKind>) {
        self.add_sorted_constructor(name, SINGLE_SORT, columns);
    }

    /// A source constructor's column roles and carrier sort.
    pub fn add_sorted_constructor(&mut self, name: &str, sort: &str, columns: Vec<ColumnKind>) {
        self.sorts.insert(sort.to_owned());
        self.constructors.insert(
            name.to_owned(),
            Constructor {
                name: name.to_owned(),
                sort: sort.to_owned(),
                columns,
            },
        );
    }

    /// A ground term's sort, determined by its constructor or rigid value.
    pub fn sort_of(&self, dag: &TermDag, term: TermId) -> Option<String> {
        match dag.get(term) {
            Term::App(head, _) => self.constructors.get(head).map(|c| c.sort.clone()),
            Term::Var(_) if slot_of(dag, term).is_some() => Some("Var".into()),
            Term::Lit(egglog::ast::Literal::Int(_)) => Some("i64".into()),
            Term::Lit(egglog::ast::Literal::String(_)) => Some("String".into()),
            _ => None,
        }
    }

    /// Parse a global's term and resolve earlier globals.
    pub fn add_let(
        &mut self,
        dag: &mut TermDag,
        name: &str,
        text: &str,
    ) -> Result<(), SourceError> {
        self.add_let_expr(dag, name, &parse_expr(text)?)
    }

    pub(super) fn add_let_expr(
        &mut self,
        dag: &mut TermDag,
        name: &str,
        expr: &Expr,
    ) -> Result<(), SourceError> {
        let term = self.ground_term(dag, expr)?;
        self.lets.insert(name.to_string(), term);
        Ok(())
    }

    /// Record a source union after resolving globals.
    pub fn add_union(
        &mut self,
        dag: &mut TermDag,
        lhs: &str,
        rhs: &str,
    ) -> Result<(), SourceError> {
        self.add_union_expr(dag, &parse_expr(lhs)?, &parse_expr(rhs)?)
    }

    pub(super) fn add_union_expr(
        &mut self,
        dag: &mut TermDag,
        lhs: &Expr,
        rhs: &Expr,
    ) -> Result<(), SourceError> {
        let lhs = self.ground_term(dag, lhs)?;
        let rhs = self.ground_term(dag, rhs)?;
        self.unions.push(Union { lhs, rhs });
        Ok(())
    }

    /// A claim's two terms, read against the program's globals.
    pub fn claim(
        &self,
        dag: &mut TermDag,
        kind: &str,
        lhs: &str,
        rhs: &str,
    ) -> Result<Claim, SourceError> {
        self.claim_expr(dag, kind, &parse_expr(lhs)?, &parse_expr(rhs)?)
    }

    pub(super) fn claim_expr(
        &self,
        dag: &mut TermDag,
        kind: &str,
        lhs: &Expr,
        rhs: &Expr,
    ) -> Result<Claim, SourceError> {
        let kind = match kind {
            "=" => ClaimKind::Eq,
            "renaming-=" => ClaimKind::RenamingEq,
            other => return Err(SourceError(format!("unsupported claim kind {other}"))),
        };
        let lhs = self.ground_term(dag, lhs)?;
        let rhs = self.ground_term(dag, rhs)?;
        Ok(Claim { kind, lhs, rhs })
    }

    /// Parse and record a rewrite under the `:name` in its source text.
    pub fn add_rewrite(&mut self, dag: &mut TermDag, text: &str) -> Result<String, SourceError> {
        self.add_named_rewrite(dag, None, text)
    }

    /// Record a rewrite under `name` when supplied, requiring any source `:name`
    /// to agree; otherwise require a name in the source text.
    pub fn add_named_rewrite(
        &mut self,
        dag: &mut TermDag,
        name: Option<&str>,
        text: &str,
    ) -> Result<String, SourceError> {
        let forms =
            crate::slotted::syntax::parse(None, text).map_err(|e| SourceError(e.to_string()))?;
        let [(form, _)] = forms.as_slice() else {
            return Err(SourceError("expected one source rewrite".into()));
        };
        let ("rewrite", args) = form.call().map_err(SourceError)? else {
            return Err(SourceError("expected a source rewrite".into()));
        };
        let source = crate::slotted::frontend::source_rewrite(args).map_err(SourceError)?;
        if let Some(name) = name
            && !source.name.is_empty()
            && name != source.name
        {
            return Err(SourceError(format!(
                "rewrite name {:?} disagrees with {name:?}",
                source.name
            )));
        }
        let mut source = source.clone();
        if source.name.is_empty() {
            source.name = name
                .ok_or_else(|| SourceError("a rewrite needs a :name".into()))?
                .to_owned();
        }
        self.add_rewrite_ast(dag, &source)
    }

    pub(super) fn add_rewrite_ast(
        &mut self,
        dag: &mut TermDag,
        source: &egglog::ast::Rewrite,
    ) -> Result<String, SourceError> {
        let name = source.name.clone();
        let rule = self.resolve_rewrite(dag, source)?;
        self.rewrites.insert(name.clone(), rule);
        Ok(name)
    }

    fn resolve_rewrite(
        &self,
        dag: &TermDag,
        source: &egglog::ast::Rewrite,
    ) -> Result<SourceRule, SourceError> {
        let err = |e: &dyn Display| SourceError(e.to_string());
        let mut graph = EGraph::default();
        egglog::prelude::add_base_sort(&mut graph, VarSort, source.span.clone())
            .map_err(|e| err(&e))?;
        let source_terms: Vec<_> = std::iter::once(&source.lhs)
            .chain(std::iter::once(&source.rhs))
            .chain(source.conditions.iter().flat_map(|fact| match fact {
                Fact::Eq(_, a, b) => vec![a, b],
                Fact::Fact(Expr::Call(_, head, args)) if is_guard(head) => args.iter().collect(),
                Fact::Fact(expr) => vec![expr],
            }))
            .collect();
        let source_names: BTreeSet<_> = source_terms
            .iter()
            .flat_map(|expr| expr.vars())
            .chain(self.lets.keys().cloned())
            .collect();
        let mut prefix = format!("{INTERNAL_SYMBOL_PREFIX}slotted-resolve-");
        while source_names.iter().any(|name| name.starts_with(&prefix)) {
            prefix.push('-');
        }
        let mut symbols = SymbolGen::new(prefix);
        let carriers = &self.sorts;
        for name in carriers {
            graph
                .add_sort(EqSort { name: name.clone() }, source.span.clone())
                .map_err(|e| err(&e))?;
        }
        for op in self.constructors.values() {
            let decl = FunctionDecl::constructor(
                source.span.clone(),
                op.name.clone(),
                Schema {
                    input: op.input_sorts().map(str::to_owned).collect(),
                    outputs: vec![op.sort.clone()],
                },
                None,
                false,
                false,
            );
            graph
                .type_info()
                .typecheck_function(&mut symbols, &decl)
                .map_err(|e| err(&e))?;
        }
        for (name, _) in GUARDS {
            if name != "!=" {
                graph.add_pure_primitive(GuardSignature(name), None);
            }
        }

        // Captured carrier globals and local payload variables have distinct scopes.
        let mut payload_vars = BTreeSet::new();
        for expr in &source_terms {
            expr.fold(&mut |expr, _: Vec<()>| {
                if let Expr::Call(_, head, args) = expr
                    && let Some(op) = self.constructors.get(head)
                {
                    for (arg, column) in args.iter().zip(&op.columns) {
                        if matches!(column, ColumnKind::Payload(_)) {
                            payload_vars.extend(arg.vars());
                        }
                    }
                }
            });
        }
        let aliases: BTreeMap<_, _> = self
            .lets
            .keys()
            .map(|name| {
                let alias = if payload_vars.contains(name) {
                    symbols.fresh(format!("captured-{name}").as_str())
                } else {
                    name.clone()
                };
                (name.clone(), alias)
            })
            .collect();
        let globals: IndexMap<_, _> = self
            .lets
            .iter()
            .map(|(name, &term)| (aliases[name].clone(), term))
            .collect();
        fn capture(
            program: &SlottedProgram,
            expr: &Expr,
            payload: bool,
            aliases: &BTreeMap<String, String>,
        ) -> Expr {
            match expr {
                Expr::Var(span, name) if !payload && aliases.contains_key(name) => {
                    Expr::Var(span.clone(), aliases[name].clone())
                }
                Expr::Call(span, head, args) => Expr::Call(
                    span.clone(),
                    head.clone(),
                    args.iter()
                        .enumerate()
                        .map(|(i, arg)| {
                            let payload = program.constructors.get(head).is_some_and(|op| {
                                matches!(op.columns.get(i), Some(ColumnKind::Payload(_)))
                            });
                            capture(program, arg, payload, aliases)
                        })
                        .collect(),
                ),
                _ => expr.clone(),
            }
        }
        let lhs = capture(self, &source.lhs, false, &aliases);
        let rhs = capture(self, &source.rhs, false, &aliases);
        let mut body = vec![Fact::Fact(lhs.clone())];
        body.extend(source.conditions.iter().map(|fact| {
            match fact {
                Fact::Eq(span, a, b) => Fact::Eq(
                    span.clone(),
                    capture(self, a, false, &aliases),
                    capture(self, b, false, &aliases),
                ),
                Fact::Fact(Expr::Call(span, head, args)) if is_guard(head) => {
                    Fact::Fact(Expr::Call(
                        span.clone(),
                        head.clone(),
                        args.iter()
                            .map(|arg| capture(self, arg, false, &aliases))
                            .collect(),
                    ))
                }
                Fact::Fact(expr) => Fact::Fact(capture(self, expr, false, &aliases)),
            }
        }));
        let mut rule = Rule {
            span: source.span.clone(),
            head: GenericActions(vec![GenericAction::Union(source.span.clone(), lhs, rhs)]),
            body,
            name: source.name.clone(),
            ruleset: String::new(),
            eval_mode: Default::default(),
            no_decomp: false,
            include_subsumed: false,
        };
        // Slot literals have the rigid Var sort. Captured globals retain the
        // sort of their source term; constructor signatures infer all other locals.
        let var_ty = VarSort.to_arcsort();
        let mut bindings: IndexMap<_, _> = source_terms
            .iter()
            .flat_map(|expr| expr.vars())
            .filter(|name| name.starts_with('$') && !payload_vars.contains(name))
            .map(|name| (name, (source.span.clone(), var_ty.clone())))
            .collect();
        for (name, &term) in &globals {
            let sort = self
                .sort_of(dag, term)
                .ok_or_else(|| SourceError(format!("unknown sort for global {name}")))?;
            let ty = graph
                .get_sort_by_name(&sort)
                .ok_or_else(|| SourceError(format!("unknown sort {sort}")))?
                .clone();
            bindings.insert(name.clone(), (source.span.clone(), ty));
        }
        let expression_sort = |expr: &Expr| match expr {
            Expr::Call(_, head, _) => self.constructors.get(head).map(|c| c.sort.clone()),
            Expr::Var(_, name) if name.starts_with('$') => Some("Var".into()),
            Expr::Var(_, name) => globals.get(name).and_then(|&t| self.sort_of(dag, t)),
            Expr::Lit(_, lit) => Some(egglog::sort::literal_sort(lit).name().to_owned()),
        };
        // Infer plain facts in their source context: guards return Unit, while
        // constructor patterns return the carrier. Remove these type constraints
        // after resolution; the checker sees the original facts.
        let plain_facts: Vec<_> = rule
            .body
            .iter_mut()
            .enumerate()
            .map(|(i, fact)| {
                let Fact::Fact(expr) = fact else { return false };
                let guard = i > 0 && matches!(expr, Expr::Call(_, head, _) if is_guard(head));
                let name = symbols.fresh("source-fact");
                let sort = if guard {
                    Some(UnitSort.to_arcsort())
                } else {
                    expression_sort(expr).map(|sort| {
                        graph
                            .get_sort_by_name(&sort)
                            .expect("source sort is registered")
                            .clone()
                    })
                };
                if let Some(sort) = sort {
                    bindings.insert(name.clone(), (expr.span(), sort));
                }
                *fact = Fact::Eq(expr.span(), Expr::Var(expr.span(), name), expr.clone());
                true
            })
            .collect();
        let bindings = bindings
            .iter()
            .map(|(name, value)| (name.as_str(), value.clone()))
            .collect();
        let mut rule = graph
            .type_info()
            .typecheck_rule_with_bindings(&mut symbols, &rule, false, &bindings)
            .map_err(|e| err(&e))?;
        for (fact, plain) in rule.body.iter_mut().zip(plain_facts) {
            if plain {
                let ResolvedFact::Eq(_, _, expr) = fact else {
                    unreachable!("resolved fact retains its syntax")
                };
                *fact = ResolvedFact::Fact(expr.clone());
            }
        }
        for fact in &rule.body {
            if let ResolvedFact::Fact(ResolvedExpr::Call(_, ResolvedCall::Primitive(head), args)) =
                fact
            {
                let head = head.name();
                if !is_guard(head) {
                    return Err(SourceError(format!("unsupported source guard {head}")));
                }
                let valid = match head {
                    "!=" | "renaming-=" | "renaming-!=" => args.len() == 2,
                    "free" | "not-free" => args.len() >= 2,
                    "free-names-are" => !args.is_empty(),
                    _ => true,
                };
                if !valid {
                    return Err(SourceError(format!("wrong arity for {head}")));
                }
            }
        }
        Ok(SourceRule { rule, globals })
    }

    /// Resolve a ground source expression against its globals and slot names.
    pub(super) fn ground_term(
        &self,
        dag: &mut TermDag,
        expr: &Expr,
    ) -> Result<TermId, SourceError> {
        match expr {
            Expr::Var(_, name) if name.starts_with('$') => {
                let number = name[1..].parse::<i64>().ok();
                let canonical = number.map_or_else(|| name.clone(), |n| format!("${n}"));
                let slot = self
                    .slot_names
                    .get(name)
                    .or_else(|| self.slot_names.get(&canonical))
                    .copied()
                    .or(number)
                    .ok_or_else(|| SourceError(format!("unknown slot {name}")))?;
                Ok(super::terms::slot_term(dag, slot))
            }
            Expr::Var(_, name) => self
                .lets
                .get(name)
                .copied()
                .ok_or_else(|| SourceError(format!("unknown global {name}"))),
            Expr::Lit(_, lit) => Ok(dag.lit(lit.clone())),
            Expr::Call(_, head, args) => {
                let args = args
                    .iter()
                    .map(|a| self.ground_term(dag, a))
                    .collect::<Result<_, _>>()?;
                Ok(dag.app(head.clone(), args))
            }
        }
    }

    /// The free slots of a ground term, by the constructors' binder columns.
    pub fn free_slots(&self, dag: &TermDag, term: TermId) -> BTreeSet<i64> {
        let mut out = BTreeSet::new();
        self.free_slots_into(dag, term, &mut out);
        out
    }

    /// Compare well-formed source terms up to scoped bound names.
    /// Free slots, constructor heads, and payloads must match exactly.
    pub fn alpha_eq(&self, dag: &mut TermDag, lhs: TermId, rhs: TermId) -> bool {
        if lhs == rhs {
            return true;
        }
        let (lhs, rhs) = self.canonical_binders(dag, lhs, rhs);
        lhs == rhs
    }

    fn canonical_binders(&self, dag: &mut TermDag, lhs: TermId, rhs: TermId) -> (TermId, TermId) {
        let slots: BTreeSet<_> = super::terms::all_slots(dag, lhs)
            .into_iter()
            .chain(super::terms::all_slots(dag, rhs))
            .collect();
        let canonical = |dag: &mut TermDag, term| {
            let mut fresh = FreshSlots::new(slots.iter().copied());
            self.refresh_binders_from(dag, term, &mut |_| fresh.fresh())
        };
        (canonical(dag, lhs), canonical(dag, rhs))
    }

    pub(super) fn renaming_between(
        &self,
        dag: &mut TermDag,
        lhs: TermId,
        rhs: TermId,
    ) -> Option<Renaming> {
        let free = self.free_slots(dag, lhs);
        let (lhs, rhs) = self.canonical_binders(dag, lhs, rhs);
        let renaming = super::terms::term_renaming(dag, &[(lhs, rhs)])?;
        Renaming::completing(free.into_iter().map(|slot| (slot, renaming.apply(slot))))
    }

    /// Compare terms up to scoped bound names and a bijection of free slots.
    pub(super) fn eq_modulo_renaming(&self, dag: &mut TermDag, lhs: TermId, rhs: TermId) -> bool {
        self.renaming_between(dag, lhs, rhs).is_some()
    }

    fn free_slots_into(&self, dag: &TermDag, term: TermId, out: &mut BTreeSet<i64>) {
        match dag.get(term) {
            Term::Lit(_) => {}
            Term::Var(_) => {
                if let Some(slot) = slot_of(dag, term) {
                    out.insert(slot);
                }
            }
            Term::App(head, children) => {
                let Some(ctor) = self.constructors.get(head) else {
                    for &c in children {
                        self.free_slots_into(dag, c, out);
                    }
                    return;
                };
                let mut bound: Vec<i64> = vec![];
                for (col, &child) in ctor.columns.iter().zip(children) {
                    match col {
                        ColumnKind::Payload(_) => {}
                        ColumnKind::Var => self.free_slots_into(dag, child, out),
                        ColumnKind::Binder => {
                            if let Some(slot) = slot_of(dag, child) {
                                bound.push(slot);
                            }
                        }
                        ColumnKind::Child => {
                            let mut inner = BTreeSet::new();
                            self.free_slots_into(dag, child, &mut inner);
                            for b in bound.drain(..) {
                                inner.remove(&b);
                            }
                            out.extend(inner);
                        }
                    }
                }
            }
        }
    }

    /// Give each binder a name distinct from other binders and free slots,
    /// preserving names that are already distinct.
    pub fn refresh_binders(&self, dag: &mut TermDag, term: TermId) -> TermId {
        let mut slots = FreshSlots::new(
            super::terms::all_slots(dag, term)
                .into_iter()
                .chain(self.slot_names.values().copied()),
        );
        let free = self.free_slots(dag, term);
        let mut binders = HashMap::<i64, usize>::default();
        let mut pending = vec![term];
        while let Some(t) = pending.pop() {
            if let Term::App(head, children) = dag.get(t) {
                if let Some(ctor) = self.constructors.get(head) {
                    for (col, &child) in ctor.columns.iter().zip(children) {
                        if *col == ColumnKind::Binder
                            && let Some(slot) = slot_of(dag, child)
                        {
                            *binders.entry(slot).or_default() += 1;
                        }
                    }
                }
                pending.extend(children.iter().copied());
            }
        }
        self.refresh_binders_from(dag, term, &mut |slot| {
            if binders[&slot] == 1 && !free.contains(&slot) {
                slot
            } else {
                slots.fresh()
            }
        })
    }

    fn refresh_binders_from(
        &self,
        dag: &mut TermDag,
        term: TermId,
        fresh: &mut impl FnMut(i64) -> i64,
    ) -> TermId {
        let Term::App(head, children) = dag.get(term).clone() else {
            return term;
        };
        let columns = self.constructors.get(&head).map(|c| c.columns.clone());
        let mut children: Vec<TermId> = children
            .into_iter()
            .map(|c| self.refresh_binders_from(dag, c, fresh))
            .collect();
        if let Some(columns) = columns {
            let mut pending: Vec<(usize, i64, i64)> = vec![];
            for (j, col) in columns.iter().enumerate() {
                match col {
                    ColumnKind::Binder => {
                        if let Some(slot) = slot_of(dag, children[j]) {
                            let f = fresh(slot);
                            pending.push((j, slot, f));
                        }
                    }
                    ColumnKind::Child => {
                        // the innermost binder first: a name bound twice is the
                        // inner one's in the body
                        for (bj, slot, f) in pending.drain(..).rev() {
                            let sigma =
                                super::terms::Renaming::new([(slot, f), (f, slot)]).unwrap();
                            children[j] = super::terms::rename(dag, &sigma, children[j]);
                            children[bj] = super::terms::slot_term(dag, f);
                        }
                    }
                    ColumnKind::Var | ColumnKind::Payload(_) => {}
                }
            }
        }
        dag.app(head, children)
    }

    /// Did the program build this term: a slot, a literal, or a subterm of a
    /// `let` or `union`?
    pub fn is_built(&self, dag: &TermDag, term: TermId) -> bool {
        match dag.get(term) {
            Term::Lit(_) => true,
            Term::Var(_) => slot_of(dag, term).is_some(),
            Term::App(..) => {
                let roots = self
                    .lets
                    .values()
                    .copied()
                    .chain(self.unions.iter().flat_map(|u| [u.lhs, u.rhs]));
                let mut seen = HashSet::default();
                let mut stack: Vec<TermId> = roots.collect();
                while let Some(t) = stack.pop() {
                    if t == term {
                        return true;
                    }
                    if !seen.insert(t) {
                        continue;
                    }
                    if let Term::App(_, children) = dag.get(t) {
                        stack.extend(children.iter().copied());
                    }
                }
                false
            }
        }
    }

    /// Every term the program built: the subterms of its `let`s and `union`s.
    pub fn built_terms(&self, dag: &TermDag) -> Vec<TermId> {
        let mut seen = HashSet::default();
        let mut out = vec![];
        let mut stack: Vec<TermId> = self
            .lets
            .values()
            .copied()
            .chain(self.unions.iter().flat_map(|u| [u.lhs, u.rhs]))
            .collect();
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            if let Term::App(_, children) = dag.get(t) {
                out.push(t);
                stack.extend(children.iter().copied());
            }
        }
        out
    }

    /// Whether either orientation of an equality was asserted by a source union.
    pub fn is_union(&self, lhs: TermId, rhs: TermId) -> bool {
        self.unions
            .iter()
            .any(|u| (u.lhs, u.rhs) == (lhs, rhs) || (u.lhs, u.rhs) == (rhs, lhs))
    }
}

fn is_guard(name: &str) -> bool {
    GUARDS.iter().any(|(guard, _)| *guard == name)
}

fn parse_expr(text: &str) -> Result<Expr, SourceError> {
    let forms =
        crate::slotted::syntax::parse(None, text).map_err(|e| SourceError(e.to_string()))?;
    let [(form, _)] = forms.as_slice() else {
        return Err(SourceError("expected one source expression".into()));
    };
    form.expr().map_err(SourceError)
}

#[cfg(test)]
#[path = "source_tests.rs"]
mod tests;
