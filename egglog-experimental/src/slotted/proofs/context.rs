//! Native source rules, declaration scopes, and binding semantics for proof checking.

use super::bindings::GlobalNames;
#[cfg(test)]
use super::format::{Claim, ClaimKind};
use super::terms::{FreshSlots, Renaming, slot_of};
use super::{HashMap, HashSet};
use egglog::ast::{Expr, GenericAction, Literal, ResolvedExpr, ResolvedFact, ResolvedRule};
use egglog::util::IndexMap;
use egglog::{ResolvedCall, Term, TermDag, TermId};
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
    pub(in crate::slotted) normal: super::normal_form::NormalRule,
}

pub(in crate::slotted) trait SourceFact {
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
            Self::Eq(_, ResolvedExpr::Var(_, var), rhs) if var.sort.is_eq_sort() => {
                Some((&var.name, rhs))
            }
            _ => None,
        }
    }
}

pub(in crate::slotted) fn pattern_term(dag: &mut TermDag, expr: &ResolvedExpr) -> TermId {
    dag.expr_to_term(&expr.clone().make_unresolved())
}

#[derive(Clone, Debug, Default)]
/// Source declarations and axioms materialized in a proof's term arena.
pub struct ProofContext {
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

impl SourceRule {
    pub(super) fn capture(rule: ResolvedRule, globals: &IndexMap<String, TermId>) -> Self {
        let mut variables = Vec::new();
        let rule = rule.visit_exprs(&mut |expr| {
            if let ResolvedExpr::Var(_, var) = &expr {
                variables.push(var.clone());
            }
            expr
        });
        let locals = variables
            .iter()
            .filter(|v| !v.is_global_ref)
            .map(|v| v.name.clone())
            .collect();
        let names = GlobalNames::new(
            globals.keys(),
            &locals,
            variables.iter().map(|v| v.name.clone()),
        );
        let aliases = names.aliases;
        let rule = rule.visit_exprs(&mut |expr| match expr {
            ResolvedExpr::Var(span, mut var) if var.is_global_ref => {
                var.name = aliases[&var.name].clone();
                var.is_global_ref = false;
                ResolvedExpr::Var(span, var)
            }
            other => other,
        });
        let globals = globals
            .iter()
            .map(|(name, &term)| (aliases[name].clone(), term))
            .collect();
        let normal = super::normal_form::NormalRule::new(&rule);
        Self {
            rule,
            globals,
            normal,
        }
    }

    pub(in crate::slotted) fn endpoints(&self) -> (&ResolvedExpr, &ResolvedExpr) {
        let [GenericAction::Union(_, lhs, rhs)] = self.rule.head.0.as_slice() else {
            unreachable!("source rewrites have one union action")
        };
        (lhs, rhs)
    }

    pub(in crate::slotted) fn conditions(&self) -> &[ResolvedFact] {
        &self.rule.body[1..]
    }

    pub(in crate::slotted) fn patterns(&self) -> impl Iterator<Item = &ResolvedExpr> {
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
        let term = super::terms::instantiate(dag, term, &bindings)?;
        let (_, rhs) = self.endpoints();
        if let ResolvedExpr::Call(_, ResolvedCall::Primitive(primitive), _) = rhs
            && let Term::App(head, args) = dag.get(term).clone()
            && head == primitive.name()
        {
            primitive
                .validator()
                .and_then(|validate| validate(dag, &args))
                .ok_or_else(|| format!("could not validate source operation {head}"))
        } else {
            Ok(term)
        }
    }

    /// Variables of a source pattern; global references are not variables.
    pub fn pattern_vars(&self, dag: &TermDag, term: TermId) -> Vec<String> {
        super::terms::pattern_vars(dag, term)
            .into_iter()
            .filter(|v| !self.globals.contains_key(v))
            .collect()
    }
}

impl ProofContext {
    #[cfg(test)]
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

    /// Resolve a ground source expression against its globals and slot names.
    pub(super) fn ground_term(
        &self,
        dag: &mut TermDag,
        expr: &Expr,
    ) -> Result<TermId, SourceError> {
        match expr {
            Expr::Var(_, name) => self.ground_name(dag, name),
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

    /// Resolve globals and slot names while retaining local query variables.
    pub(super) fn query_pattern(
        &self,
        dag: &mut TermDag,
        expr: &Expr,
    ) -> Result<TermId, SourceError> {
        match expr {
            Expr::Var(_, name) if !name.starts_with('$') && !self.lets.contains_key(name) => {
                Ok(dag.var(name.clone()))
            }
            Expr::Call(_, head, args) => {
                let args = args
                    .iter()
                    .enumerate()
                    .map(|(i, arg)| {
                        if matches!(self.constructors[head].columns[i], ColumnKind::Payload(_))
                            && let Expr::Var(_, name) = arg
                        {
                            Ok(dag.var(name.clone()))
                        } else {
                            self.query_pattern(dag, arg)
                        }
                    })
                    .collect::<Result<_, _>>()?;
                Ok(dag.app(head.clone(), args))
            }
            _ => self.ground_term(dag, expr),
        }
    }

    pub(super) fn query_variables(&self, expr: &Expr) -> BTreeSet<String> {
        match expr {
            Expr::Var(_, name) if !name.starts_with('$') && !self.lets.contains_key(name) => {
                [name.clone()].into()
            }
            Expr::Call(_, head, args) => args
                .iter()
                .enumerate()
                .flat_map(|(i, arg)| {
                    if matches!(self.constructors[head].columns[i], ColumnKind::Payload(_)) {
                        arg.vars().collect()
                    } else {
                        self.query_variables(arg)
                    }
                })
                .collect(),
            _ => BTreeSet::new(),
        }
    }

    pub(super) fn query_instance(
        &self,
        dag: &mut TermDag,
        expr: &Expr,
        witnesses: &HashMap<String, TermId>,
    ) -> Result<TermId, SourceError> {
        match expr {
            Expr::Var(_, name) if !name.starts_with('$') && !self.lets.contains_key(name) => {
                witnesses
                    .get(name)
                    .copied()
                    .ok_or_else(|| SourceError(format!("missing query witness {name}")))
            }
            Expr::Call(_, head, args) => {
                let args = args
                    .iter()
                    .enumerate()
                    .map(|(i, arg)| {
                        if matches!(self.constructors[head].columns[i], ColumnKind::Payload(_))
                            && let Expr::Var(_, name) = arg
                        {
                            witnesses.get(name).copied().ok_or_else(|| {
                                SourceError(format!("missing payload witness {name}"))
                            })
                        } else {
                            self.query_instance(dag, arg, witnesses)
                        }
                    })
                    .collect::<Result<_, _>>()?;
                Ok(dag.app(head.clone(), args))
            }
            _ => self.ground_term(dag, expr),
        }
    }

    pub(super) fn ground_name(&self, dag: &mut TermDag, name: &str) -> Result<TermId, SourceError> {
        if let Some(suffix) = name.strip_prefix('$') {
            let number = suffix.parse::<i64>().ok();
            let canonical = number.map_or_else(|| name.to_owned(), |n| format!("${n}"));
            let slot = self
                .slot_names
                .get(name)
                .or_else(|| self.slot_names.get(&canonical))
                .copied()
                .or(number)
                .ok_or_else(|| SourceError(format!("unknown slot {name}")))?;
            Ok(super::terms::slot_term(dag, slot))
        } else {
            self.lets
                .get(name)
                .copied()
                .ok_or_else(|| SourceError(format!("unknown global {name}")))
        }
    }

    /// The free slots of a ground term, by the constructors' binder columns.
    pub fn free_slots(&self, dag: &TermDag, term: TermId) -> BTreeSet<i64> {
        self.free_slots_memo(dag, term, &mut HashMap::default())
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

    pub(super) fn canonical_binders(
        &self,
        dag: &mut TermDag,
        lhs: TermId,
        rhs: TermId,
    ) -> (TermId, TermId) {
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

    pub(in crate::slotted) fn renaming_between(
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
    pub(in crate::slotted) fn eq_modulo_renaming(
        &self,
        dag: &mut TermDag,
        lhs: TermId,
        rhs: TermId,
    ) -> bool {
        self.renaming_between(dag, lhs, rhs).is_some()
    }

    fn free_slots_memo(
        &self,
        dag: &TermDag,
        term: TermId,
        memo: &mut HashMap<TermId, BTreeSet<i64>>,
    ) -> BTreeSet<i64> {
        if let Some(slots) = memo.get(&term) {
            return slots.clone();
        }
        let mut out = BTreeSet::new();
        match dag.get(term) {
            Term::Lit(_) => {}
            Term::Var(_) => {
                if let Some(slot) = slot_of(dag, term) {
                    out.insert(slot);
                }
            }
            Term::App(head, children) => {
                if let Some(ctor) = self.constructors.get(head) {
                    let mut bound: Vec<i64> = vec![];
                    for (col, &child) in ctor.columns.iter().zip(children) {
                        match col {
                            ColumnKind::Payload(_) => {}
                            ColumnKind::Var => out.extend(self.free_slots_memo(dag, child, memo)),
                            ColumnKind::Binder => {
                                if let Some(slot) = slot_of(dag, child) {
                                    bound.push(slot);
                                }
                            }
                            ColumnKind::Child => {
                                let mut inner = self.free_slots_memo(dag, child, memo);
                                for b in bound.drain(..) {
                                    inner.remove(&b);
                                }
                                out.extend(inner);
                            }
                        }
                    }
                } else {
                    for &c in children {
                        out.extend(self.free_slots_memo(dag, c, memo));
                    }
                }
            }
        }
        memo.insert(term, out.clone());
        out
    }

    /// Give each binder a name distinct from other binders and free slots,
    /// preserving names that are already distinct.
    pub fn refresh_binders(&self, dag: &mut TermDag, term: TermId) -> TermId {
        self.refresh_binders_avoiding(dag, term, &BTreeSet::new())
    }

    pub(super) fn refresh_binders_avoiding(
        &self,
        dag: &mut TermDag,
        term: TermId,
        avoid: &BTreeSet<i64>,
    ) -> TermId {
        let mut slots = FreshSlots::new(
            super::terms::all_slots(dag, term)
                .into_iter()
                .chain(self.slot_names.values().copied())
                .chain(avoid.iter().copied()),
        );
        let mut free = self.free_slots(dag, term);
        free.extend(avoid);
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

    /// Whether either orientation of an equality was asserted by a source union.
    pub fn is_union(&self, lhs: TermId, rhs: TermId) -> bool {
        self.unions
            .iter()
            .any(|u| (u.lhs, u.rhs) == (lhs, rhs) || (u.lhs, u.rhs) == (rhs, lhs))
    }
}

/// Check a ground term against source constructor signatures and return its sort.
pub(super) fn check_term_sort(
    program: &ProofContext,
    dag: &TermDag,
    term: TermId,
    expected: Option<&str>,
) -> Result<String, String> {
    let actual = match dag.get(term) {
        Term::Lit(Literal::Int(_)) => "i64",
        Term::Lit(Literal::String(_)) => "String",
        Term::Lit(_) => return Err("unsupported payload literal".into()),
        Term::Var(_) if slot_of(dag, term).is_some() => "Var",
        Term::Var(v) => return Err(format!("uninstantiated variable {v}")),
        Term::App(head, children) => {
            let ctor = program
                .constructors
                .get(head)
                .ok_or_else(|| format!("unknown constructor {head}"))?;
            if children.len() != ctor.columns.len() {
                return Err(format!("wrong arity for {head}"));
            }
            for (&child, sort) in children.iter().zip(ctor.input_sorts()) {
                check_term_sort(program, dag, child, Some(sort))?;
            }
            ctor.sort.as_str()
        }
    };
    if let Some(expected) = expected
        && actual != expected
    {
        return Err(format!(
            "{} has sort {actual}, expected {expected}",
            dag.to_string(term)
        ));
    }
    Ok(actual.to_owned())
}

#[cfg(test)]
#[path = "tests/context.rs"]
mod tests;
