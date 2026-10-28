//! Source declarations, rewrites, and claims used by the slotted proof checker.

use super::terms::{FreshSlots, is_pattern_var, slot_of};
use super::{HashMap, HashSet};
use egglog::ast::Literal;
use egglog::util::IndexMap;
use egglog::{Term, TermDag, TermId};
use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::fmt::{self, Display, Formatter};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
/// How a surface constructor column participates in binding and renaming.
pub enum ColumnKind {
    /// A slotted child.
    Child,
    /// A column whose slot the node binds over the next child column.
    Binder,
    /// A payload: an `i64`, a `String`, …
    Payload,
}

#[derive(Clone, Debug)]
/// A source constructor's surface layout and sort signature.
pub struct Constructor {
    /// The constructor's source name.
    pub name: String,
    /// The role of each surface argument, in order.
    pub columns: Vec<ColumnKind>,
    /// The sort of each column: a carrier sort for a child or binder column, the
    /// payload's sort otherwise.
    pub sorts: Vec<String>,
    /// The carrier sort the constructor builds.
    pub output: String,
}

/// A top-level `(union a b)`, with the carrier sort the compiler gave it: two bare
/// slots carry no sort of their own.
#[derive(Clone, Debug)]
pub struct Union {
    /// The union's left source term.
    pub lhs: TermId,
    /// The union's right source term.
    pub rhs: TermId,
    /// The carrier sort containing both terms.
    pub sort: String,
}

/// A rewrite's right-hand side: a term to build, or one of its variables.
#[derive(Clone, Debug)]
pub enum Rhs {
    /// A constructor pattern instantiated by the rule application.
    Term(TermId),
    /// A variable whose matched term is reused directly.
    Var(String),
}

#[derive(Clone, Debug)]
/// A fact written in a rewrite's `:when` clause.
pub enum Condition {
    /// A constructor pattern that must exist.
    Fact(TermId),
    /// An equality between two source terms.
    Eq {
        /// Left source expression.
        lhs: TermId,
        /// Right source expression.
        rhs: TermId,
    },
    /// Two source terms that must differ.
    Neq {
        /// Left source expression.
        lhs: TermId,
        /// Right source expression.
        rhs: TermId,
    },
    /// An equality allowing a permutation of the right term's slots.
    RenamingEq {
        /// Left source expression.
        lhs: TermId,
        /// Right source expression.
        rhs: TermId,
    },
    /// Two source terms that differ under every slot permutation.
    RenamingNeq {
        /// Left source expression.
        lhs: TermId,
        /// Right source expression.
        rhs: TermId,
    },
    /// The slot occurs freely in at least one of the terms.
    Free {
        /// Source expression naming the tested slot.
        slot: TermId,
        /// Terms whose combined free slots are tested.
        terms: Vec<TermId>,
    },
    /// The slot occurs freely in none of the terms.
    NotFree {
        /// Source expression naming the tested slot.
        slot: TermId,
        /// Terms whose combined free slots are tested.
        terms: Vec<TermId>,
    },
    /// The term has exactly these free slots.
    FreeNames {
        /// Source expression whose free slots are tested.
        term: TermId,
        /// Source expressions naming the required slots.
        slots: Vec<TermId>,
    },
}

#[derive(Clone, Copy, Debug)]
pub(super) enum Requirement {
    Exists(TermId),
    Equal(TermId, TermId),
    RenamingEqual(TermId, TermId),
}

impl Condition {
    /// The source expressions in this fact, in written order.
    pub fn terms(&self) -> Vec<TermId> {
        match self {
            Self::Fact(t) => vec![*t],
            Self::Eq { lhs, rhs }
            | Self::Neq { lhs, rhs }
            | Self::RenamingEq { lhs, rhs }
            | Self::RenamingNeq { lhs, rhs } => vec![*lhs, *rhs],
            Self::Free { slot, terms } | Self::NotFree { slot, terms } => std::iter::once(*slot)
                .chain(terms.iter().copied())
                .collect(),
            Self::FreeNames { term, slots } => std::iter::once(*term)
                .chain(slots.iter().copied())
                .collect(),
        }
    }

    pub(super) fn requirements(&self) -> Vec<Requirement> {
        match self {
            Self::Eq { lhs, rhs } => vec![Requirement::Equal(*lhs, *rhs)],
            Self::RenamingEq { lhs, rhs } => vec![Requirement::RenamingEqual(*lhs, *rhs)],
            Self::Fact(term) | Self::FreeNames { term, .. } => vec![Requirement::Exists(*term)],
            Self::Free { terms, .. } | Self::NotFree { terms, .. } => {
                terms.iter().copied().map(Requirement::Exists).collect()
            }
            Self::Neq { lhs, rhs } | Self::RenamingNeq { lhs, rhs } => {
                vec![Requirement::Exists(*lhs), Requirement::Exists(*rhs)]
            }
        }
    }

    pub(super) fn binding<'a>(&self, dag: &'a TermDag) -> Option<(&'a String, TermId)> {
        let Self::Eq { lhs, rhs } = self else {
            return None;
        };
        let Term::Var(var) = dag.get(*lhs) else {
            return None;
        };
        Some((var, *rhs))
    }
}

#[derive(Clone, Debug)]
/// A named source rewrite with its matching premises.
pub struct Rewrite {
    /// Globals in scope when the rewrite was declared.
    pub globals: IndexMap<String, TermId>,
    /// The name used by proof rule applications.
    pub name: String,
    /// The root pattern matched by the rewrite.
    pub lhs: TermId,
    /// The term or variable produced by the rewrite.
    pub rhs: Rhs,
    /// The original `:when` facts, in source order.
    pub conditions: Vec<Condition>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
/// Whether a claim fixes free slots or permits a renaming between its sides.
pub enum ClaimKind {
    /// `(= a b)`: the same invocation.
    Eq,
    /// `(renaming-= a b)`: the same class under some renaming.
    RenamingEq,
}

/// A `prove-slotted`'s claim over source terms.
#[derive(Clone, Debug)]
pub struct Claim {
    /// The requested notion of equality.
    pub kind: ClaimKind,
    /// The carrier sort the two terms belong to.
    pub sort: String,
    /// The claim's left source term.
    pub lhs: TermId,
    /// The claim's right source term.
    pub rhs: TermId,
}

#[derive(Clone, Debug, Default)]
/// Source declarations and axioms used by the independent proof checker.
pub struct SlottedProgram {
    /// Ground source slot spellings and their identities in the encoding.
    pub slot_names: BTreeMap<String, i64>,
    /// Constructor signatures indexed by source name.
    pub constructors: HashMap<String, Constructor>,
    /// Source rewrites indexed by their proof names.
    pub rewrites: HashMap<String, Rewrite>,
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

impl Rewrite {
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
    /// A constructor of a program with the single carrier sort [`SINGLE_SORT`]; a
    /// payload column gets the sort `payload`.
    pub fn add_constructor(&mut self, name: &str, columns: Vec<ColumnKind>) {
        let columns = columns
            .into_iter()
            .map(|c| {
                let sort = match c {
                    ColumnKind::Child | ColumnKind::Binder => SINGLE_SORT,
                    ColumnKind::Payload => "payload",
                };
                (c, sort.to_string())
            })
            .collect();
        self.add_sorted_constructor(name, SINGLE_SORT, columns);
    }

    /// A constructor building `output`, each column with its kind and sort.
    pub fn add_sorted_constructor(
        &mut self,
        name: &str,
        output: &str,
        columns: Vec<(ColumnKind, String)>,
    ) {
        let (columns, sorts) = columns.into_iter().unzip();
        self.constructors.insert(
            name.to_string(),
            Constructor {
                name: name.to_string(),
                columns,
                sorts,
                output: output.to_string(),
            },
        );
    }

    /// The carrier sort a term names by its head constructor. A bare slot or a
    /// literal names none.
    pub fn sort_of(&self, dag: &TermDag, term: TermId) -> Option<String> {
        match dag.get(term) {
            Term::App(head, _) => self.constructors.get(head).map(|c| c.output.clone()),
            _ => None,
        }
    }

    /// Parse a global's term, resolve earlier globals, and refresh its binders.
    pub fn add_let(
        &mut self,
        dag: &mut TermDag,
        name: &str,
        text: &str,
    ) -> Result<(), SourceError> {
        let term = self.ground_term(dag, &parse_sexp(text)?)?;
        // kept with its binders named apart (see `refresh_binders`), so a term
        // spelled with other bound names differs from it by a bijection of slots
        let term = self.refresh_binders(dag, term);
        self.lets.insert(name.to_string(), term);
        Ok(())
    }

    /// A repeated union's first string carries a ` #n` suffix to keep the row
    /// distinct; it is not part of the term.
    fn strip_union_suffix(text: &str) -> &str {
        match text.rsplit_once(" #") {
            Some((head, n)) if n.parse::<u64>().is_ok() => head,
            _ => text,
        }
    }

    /// Record a source union after resolving globals and refreshing binders.
    pub fn add_union(
        &mut self,
        dag: &mut TermDag,
        lhs: &str,
        rhs: &str,
        sort: &str,
    ) -> Result<(), SourceError> {
        let lhs = self.ground_term(dag, &parse_sexp(Self::strip_union_suffix(lhs))?)?;
        let lhs = self.refresh_binders(dag, lhs);
        let rhs = self.ground_term(dag, &parse_sexp(rhs)?)?;
        let rhs = self.refresh_binders(dag, rhs);
        self.unions.push(Union {
            lhs,
            rhs,
            sort: sort.to_string(),
        });
        Ok(())
    }

    /// A claim's two terms, read against the program's globals.
    pub fn claim(
        &self,
        dag: &mut TermDag,
        kind: &str,
        sort: &str,
        lhs: &str,
        rhs: &str,
    ) -> Result<Claim, SourceError> {
        let kind = match kind {
            "=" => ClaimKind::Eq,
            "renaming-=" => ClaimKind::RenamingEq,
            other => return Err(SourceError(format!("unsupported claim kind {other}"))),
        };
        let lhs = self.ground_term(dag, &parse_sexp(lhs)?)?;
        let rhs = self.ground_term(dag, &parse_sexp(rhs)?)?;
        Ok(Claim {
            kind,
            sort: sort.to_string(),
            lhs,
            rhs,
        })
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
        let form = parse_sexp(text)?;
        let Sexp::List(items) = &form else {
            return Err(SourceError(format!("not a rewrite: {text}")));
        };
        let [head, lhs, rhs, options @ ..] = items.as_slice() else {
            return Err(SourceError(format!("not a rewrite: {text}")));
        };
        if head.atom() != Some("rewrite") {
            return Err(SourceError(format!("not a rewrite: {text}")));
        }
        let lhs = Self::pattern_term(dag, lhs)?;
        if !matches!(dag.get(lhs), Term::App(..)) && !is_class_var(dag, lhs) {
            return Err(SourceError(
                "a rewrite's left side must be a call or a pattern variable".into(),
            ));
        }
        let rhs = match rhs {
            Sexp::Atom(name) if !name.starts_with('$') && !is_number(name) => {
                // a bare name that is a global means that global
                match self.lets.get(name) {
                    Some(_) => Rhs::Term(dag.var(name.to_string())),
                    None => Rhs::Var(name.to_string()),
                }
            }
            Sexp::List(items) if items.first().and_then(Sexp::atom) == Some("subst") => {
                return Err(SourceError(
                    "subst right-hand sides are not supported in proofs".into(),
                ));
            }
            other => Rhs::Term(Self::pattern_term(dag, other)?),
        };
        let mut name = name.map(str::to_string);
        let mut conditions = vec![];
        let mut i = 0;
        while i < options.len() {
            match options[i].atom() {
                Some(":name") => {
                    name = Some(
                        options
                            .get(i + 1)
                            .and_then(|s| s.string_or_atom())
                            .ok_or_else(|| SourceError(":name needs a value".into()))?
                            .to_string(),
                    );
                    i += 2;
                }
                Some(":when") => {
                    let Some(Sexp::List(facts)) = options.get(i + 1) else {
                        return Err(SourceError(":when needs a list of facts".into()));
                    };
                    for fact in facts {
                        conditions.push(self.condition(dag, fact)?);
                    }
                    i += 2;
                }
                Some(other) => {
                    return Err(SourceError(format!("unsupported rewrite option {other}")));
                }
                None => return Err(SourceError("malformed rewrite options".into())),
            }
        }
        if let Term::Var(root) = dag.get(lhs)
            && !self.lets.contains_key(root)
            && !conditions.iter().any(|condition| {
                condition
                    .terms()
                    .iter()
                    .any(|&term| super::terms::pattern_vars(dag, term).contains(root))
            })
        {
            return Err(SourceError(format!(
                "rewrite root {root:?} is not bound by a pattern"
            )));
        }
        let name = name.ok_or_else(|| SourceError("a rewrite needs a :name".into()))?;
        self.rewrites.insert(
            name.clone(),
            Rewrite {
                name: name.clone(),
                lhs,
                rhs,
                conditions,
                globals: self.lets.clone(),
            },
        );
        Ok(name)
    }

    fn condition(&self, dag: &mut TermDag, fact: &Sexp) -> Result<Condition, SourceError> {
        let Sexp::List(items) = fact else {
            return Err(SourceError(format!("malformed :when fact {fact}")));
        };
        match items.as_slice() {
            [h, slot, terms @ ..] if matches!(h.atom(), Some("free" | "not-free")) => {
                if terms.is_empty() {
                    return Err(SourceError("free/not-free needs at least one term".into()));
                }
                let slot = Self::pattern_term(dag, slot)?;
                let terms = terms
                    .iter()
                    .map(|t| Self::pattern_term(dag, t))
                    .collect::<Result<_, _>>()?;
                Ok(if h.atom() == Some("free") {
                    Condition::Free { slot, terms }
                } else {
                    Condition::NotFree { slot, terms }
                })
            }
            [h, term, slots @ ..] if h.atom() == Some("free-names-are") => {
                let term = Self::pattern_term(dag, term)?;
                let slots = slots
                    .iter()
                    .map(|s| Self::pattern_term(dag, s))
                    .collect::<Result<_, _>>()?;
                Ok(Condition::FreeNames { term, slots })
            }
            [h, lhs, rhs]
                if matches!(h.atom(), Some("=" | "!=" | "renaming-=" | "renaming-!=")) =>
            {
                let lhs = Self::pattern_term(dag, lhs)?;
                let rhs = Self::pattern_term(dag, rhs)?;
                Ok(match h.atom().unwrap() {
                    "=" => Condition::Eq { lhs, rhs },
                    "!=" => Condition::Neq { lhs, rhs },
                    "renaming-=" => Condition::RenamingEq { lhs, rhs },
                    "renaming-!=" => Condition::RenamingNeq { lhs, rhs },
                    _ => unreachable!(),
                })
            }
            [head, ..]
                if head
                    .atom()
                    .is_some_and(|h| self.constructors.contains_key(h)) =>
            {
                Ok(Condition::Fact(Self::pattern_term(dag, fact)?))
            }
            _ => Err(SourceError(format!("unsupported :when fact {fact}"))),
        }
    }

    /// A rewrite's pattern: atoms are variables (slot literals keep their `$`),
    /// lists are constructor applications.
    fn pattern_term(dag: &mut TermDag, s: &Sexp) -> Result<TermId, SourceError> {
        match s {
            Sexp::Atom(a) => atom_term(dag, a, |dag, name| Ok(dag.var(name.to_string()))),
            Sexp::Str(text) => Ok(dag.lit(Literal::String(text.clone()))),
            Sexp::List(items) => {
                let (head, args) = items
                    .split_first()
                    .ok_or_else(|| SourceError("empty application".into()))?;
                let head = head
                    .atom()
                    .ok_or_else(|| SourceError("application head must be a symbol".into()))?;
                let args = args
                    .iter()
                    .map(|a| Self::pattern_term(dag, a))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(dag.app(head.to_string(), args))
            }
        }
    }

    /// A term written at the top level: bare symbols are globals.
    fn ground_term(&self, dag: &mut TermDag, s: &Sexp) -> Result<TermId, SourceError> {
        match s {
            Sexp::Atom(a) if a.starts_with('$') => {
                let number = a[1..].parse::<i64>().ok();
                let name = number.map_or_else(|| a.clone(), |n| format!("${n}"));
                let slot = self
                    .slot_names
                    .get(a)
                    .or_else(|| self.slot_names.get(&name))
                    .copied()
                    .or(number)
                    .ok_or_else(|| SourceError(format!("unknown slot {name}")))?;
                Ok(super::terms::slot_term(dag, slot))
            }
            Sexp::Atom(a) => atom_term(dag, a, |_, name| {
                self.lets
                    .get(name)
                    .copied()
                    .ok_or_else(|| SourceError(format!("unknown global {name}")))
            }),
            Sexp::Str(text) => Ok(dag.lit(Literal::String(text.clone()))),
            Sexp::List(items) => {
                let (head, args) = items
                    .split_first()
                    .ok_or_else(|| SourceError("empty application".into()))?;
                let head = head
                    .atom()
                    .ok_or_else(|| SourceError("application head must be a symbol".into()))?;
                let args = args
                    .iter()
                    .map(|a| self.ground_term(dag, a))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(dag.app(head.to_string(), args))
            }
        }
    }

    /// The free slots of a ground term, by the constructors' binder columns.
    pub fn free_slots(&self, dag: &TermDag, term: TermId) -> BTreeSet<i64> {
        let mut out = BTreeSet::new();
        self.free_slots_into(dag, term, &mut out);
        out
    }

    /// Compare source-condition endpoints, allowing only scoped bound names to
    /// differ. Free slots, constructor heads and payloads must match exactly.
    pub(super) fn alpha_eq(&self, dag: &mut TermDag, lhs: TermId, rhs: TermId) -> bool {
        if lhs == rhs {
            return true;
        }
        let slots: BTreeSet<_> = super::terms::all_slots(dag, lhs)
            .into_iter()
            .chain(super::terms::all_slots(dag, rhs))
            .collect();
        // Reuse the source reader's scope-aware refresh, giving both terms the
        // same fresh binder names. No free name is changed by this operation.
        let canonical = |dag: &mut TermDag, term| {
            let mut fresh = FreshSlots::new(slots.iter().copied());
            self.refresh_binders_from(dag, term, &mut |_| fresh.fresh())
        };
        canonical(dag, lhs) == canonical(dag, rhs)
    }

    /// Compare terms up to scoped bound names and a bijection of free slots.
    pub(super) fn eq_modulo_renaming(&self, dag: &mut TermDag, lhs: TermId, rhs: TermId) -> bool {
        let lhs = self.refresh_binders(dag, lhs);
        let rhs = self.refresh_binders(dag, rhs);
        super::terms::term_renaming(dag, &[(lhs, rhs)]).is_some()
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
                        ColumnKind::Payload => {}
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
                    ColumnKind::Payload => {}
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
        self.union_sort(lhs, rhs).is_some()
    }

    /// The sort of the source union between the two terms, in either direction.
    pub fn union_sort(&self, lhs: TermId, rhs: TermId) -> Option<&str> {
        self.unions
            .iter()
            .find(|u| (u.lhs, u.rhs) == (lhs, rhs) || (u.lhs, u.rhs) == (rhs, lhs))
            .map(|u| u.sort.as_str())
    }
}

fn is_number(a: &str) -> bool {
    a.parse::<i64>().is_ok() || a.parse::<f64>().is_ok() && a.contains('.')
}

/// A symbol as a term: a number, a boolean, a slot, or whatever `var` makes of a
/// name.
fn atom_term(
    dag: &mut TermDag,
    a: &str,
    var: impl FnOnce(&mut TermDag, &str) -> Result<TermId, SourceError>,
) -> Result<TermId, SourceError> {
    if let Ok(n) = a.parse::<i64>() {
        return Ok(dag.lit(Literal::Int(n)));
    }
    if a == "true" || a == "false" {
        return Ok(dag.lit(Literal::Bool(a == "true")));
    }
    if a.starts_with('$') {
        return Ok(dag.var(a.to_string()));
    }
    if a.contains('.')
        && let Ok(f) = a.parse::<f64>()
    {
        return Ok(dag.lit(Literal::Float(f.into())));
    }
    var(dag, a)
}

/// A parsed s-expression.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Sexp {
    /// An unquoted symbol or numeric literal.
    Atom(String),
    /// The decoded contents of a quoted string.
    Str(String),
    /// A parenthesized sequence of forms.
    List(Vec<Sexp>),
}

impl Sexp {
    /// The spelling of an unquoted atom, if this form is one.
    pub fn atom(&self) -> Option<&str> {
        match self {
            Sexp::Atom(a) => Some(a),
            _ => None,
        }
    }

    fn string_or_atom(&self) -> Option<&str> {
        match self {
            Sexp::Atom(a) | Sexp::Str(a) => Some(a),
            Sexp::List(_) => None,
        }
    }
}

impl Display for Sexp {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Sexp::Atom(a) => f.write_str(a),
            Sexp::Str(s) => write!(f, "{s:?}"),
            Sexp::List(items) => {
                write!(f, "(")?;
                for (i, item) in items.iter().enumerate() {
                    if i > 0 {
                        write!(f, " ")?;
                    }
                    write!(f, "{item}")?;
                }
                write!(f, ")")
            }
        }
    }
}

/// Parse one s-expression; comments (`;` to end of line) are skipped.
pub fn parse_sexp(text: &str) -> Result<Sexp, SourceError> {
    let chars: Vec<char> = text.chars().collect();
    let mut pos = 0;
    let out = parse_at(&chars, &mut pos)?;
    skip_space(&chars, &mut pos);
    if pos != chars.len() {
        return Err(SourceError(format!(
            "trailing text after s-expression in {text}"
        )));
    }
    Ok(out)
}

fn skip_space(chars: &[char], pos: &mut usize) {
    while *pos < chars.len() {
        if chars[*pos].is_whitespace() {
            *pos += 1;
        } else if chars[*pos] == ';' {
            while *pos < chars.len() && chars[*pos] != '\n' {
                *pos += 1;
            }
        } else {
            break;
        }
    }
}

fn parse_at(chars: &[char], pos: &mut usize) -> Result<Sexp, SourceError> {
    skip_space(chars, pos);
    let Some(&c) = chars.get(*pos) else {
        return Err(SourceError("unexpected end of s-expression".into()));
    };
    match c {
        '(' => {
            *pos += 1;
            let mut items = vec![];
            loop {
                skip_space(chars, pos);
                match chars.get(*pos) {
                    Some(')') => {
                        *pos += 1;
                        return Ok(Sexp::List(items));
                    }
                    Some(_) => items.push(parse_at(chars, pos)?),
                    None => return Err(SourceError("unclosed parenthesis".into())),
                }
            }
        }
        ')' => Err(SourceError("unexpected )".into())),
        '"' => {
            *pos += 1;
            let mut s = String::new();
            loop {
                match chars.get(*pos) {
                    Some('"') => {
                        *pos += 1;
                        return Ok(Sexp::Str(s));
                    }
                    Some('\\') => {
                        *pos += 1;
                        match chars.get(*pos) {
                            Some('n') => s.push('\n'),
                            Some('t') => s.push('\t'),
                            Some(&other) => s.push(other),
                            None => return Err(SourceError("unterminated string".into())),
                        }
                        *pos += 1;
                    }
                    Some(&other) => {
                        s.push(other);
                        *pos += 1;
                    }
                    None => return Err(SourceError("unterminated string".into())),
                }
            }
        }
        _ => {
            let start = *pos;
            while *pos < chars.len()
                && !chars[*pos].is_whitespace()
                && !matches!(chars[*pos], '(' | ')' | '"' | ';')
            {
                *pos += 1;
            }
            Ok(Sexp::Atom(chars[start..*pos].iter().collect()))
        }
    }
}

/// Is this a variable of a pattern (not a slot literal)?
pub fn is_class_var(dag: &TermDag, term: TermId) -> bool {
    is_pattern_var(dag, term) && !matches!(dag.get(term), Term::Var(name) if name.starts_with('$'))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_rewrites_lets_unions_and_claims() {
        let mut dag = TermDag::default();
        let mut program = SlottedProgram::default();
        program.add_constructor("Mul", vec![ColumnKind::Child, ColumnKind::Child]);
        program.add_constructor("Null", vec![]);
        program.add_constructor("Lam", vec![ColumnKind::Binder, ColumnKind::Child]);
        program.add_let(&mut dag, "m7", "(Mul $7 (Null))").unwrap();
        program.add_let(&mut dag, "zero", "(Null)").unwrap();
        program.add_union(&mut dag, "m7", "zero", "U").unwrap();
        let claim = program
            .claim(&mut dag, "=", "U", "(Mul $9 (Null))", "zero")
            .unwrap();
        let name = program
            .add_rewrite(
                &mut dag,
                r#"(rewrite (Lam $x (App f $x)) f :name "eta" :when ((not-free $x f)))"#,
            )
            .unwrap();
        assert_eq!(name, "eta");
        let eta = &program.rewrites["eta"];
        assert_eq!(dag.to_string(eta.lhs), "(Lam $x (App f $x))");
        assert!(matches!(&eta.rhs, Rhs::Var(v) if v == "f"));
        assert!(
            matches!(&eta.conditions[0], Condition::NotFree { slot, terms } if dag.to_string(*slot) == "$x" && terms.iter().map(|t| dag.to_string(*t)).collect::<Vec<_>>() == ["f"])
        );
        // a condition names as many variables as it likes
        program
            .add_rewrite(
                &mut dag,
                r#"(rewrite (App (Lam $z x) y) (App x y) :name "two" :when ((not-free $z x y)))"#,
            )
            .unwrap();
        assert!(
            matches!(&program.rewrites["two"].conditions[0], Condition::NotFree { terms, .. } if terms.iter().map(|t| dag.to_string(*t)).collect::<Vec<_>>() == ["x", "y"])
        );
        let Union { lhs: a, rhs: b, .. } = program.unions[0].clone();
        assert_eq!(program.unions[0].sort, "U");
        assert_eq!(dag.to_string(a), "(Mul $7 (Null))");
        assert_eq!(dag.to_string(b), "(Null)");
        assert!(program.is_union(b, a));
        assert!(program.is_built(&dag, a));
        assert_eq!(claim.kind, ClaimKind::Eq);
        assert_eq!(dag.to_string(claim.lhs), "(Mul $9 (Null))");
    }

    #[test]
    fn free_slots_respect_binders() {
        let mut dag = TermDag::default();
        let mut program = SlottedProgram::default();
        program.add_constructor("Lam", vec![ColumnKind::Binder, ColumnKind::Child]);
        program.add_constructor("App", vec![ColumnKind::Child, ColumnKind::Child]);
        program.add_constructor(
            "Let",
            vec![ColumnKind::Child, ColumnKind::Binder, ColumnKind::Child],
        );
        program
            .add_let(&mut dag, "k", "(Lam $0 (App $0 $3))")
            .unwrap();
        assert_eq!(
            program.free_slots(&dag, program.lets["k"]),
            BTreeSet::from([3])
        );
        program.add_let(&mut dag, "l", "(Let $1 $1 $1)").unwrap();
        // the value's occurrence is free, the body's is bound
        assert_eq!(
            program.free_slots(&dag, program.lets["l"]),
            BTreeSet::from([1])
        );
    }

    #[test]
    fn alpha_matching_preserves_free_names_and_binding_scope() {
        let mut dag = TermDag::default();
        let mut program = SlottedProgram::default();
        program.add_constructor("Lam", vec![ColumnKind::Binder, ColumnKind::Child]);
        program.add_constructor("Pair", vec![ColumnKind::Child, ColumnKind::Child]);
        program.add_constructor(
            "Let",
            vec![ColumnKind::Binder, ColumnKind::Child, ColumnKind::Child],
        );
        for (a, b, equal) in [
            ("(Lam $0 (Pair $0 $3))", "(Lam $1 (Pair $1 $3))", true),
            ("(Lam $0 (Pair $0 $3))", "(Lam $1 (Pair $1 $4))", false),
            ("(Lam $0 $1)", "(Lam $1 $1)", false),
            ("(Lam $0 $0)", "(Lam $1 $0)", false),
            ("(Lam $0 (Lam $0 $0))", "(Lam $1 (Lam $2 $2))", true),
            ("(Lam $0 (Lam $1 $0))", "(Lam $2 (Lam $2 $2))", false),
            ("(Let $0 $0 $0)", "(Let $1 $1 $0)", true),
            ("(Let $0 $0 $0)", "(Let $1 $1 $1)", false),
            ("(Pair (Lam $0 $0) $0)", "(Pair (Lam $1 $1) $0)", true),
        ] {
            let terms = program.claim(&mut dag, "=", "U", a, b).unwrap();
            assert_eq!(
                program.alpha_eq(&mut dag, terms.lhs, terms.rhs),
                equal,
                "{a} versus {b}"
            );
            assert_eq!(
                program.alpha_eq(&mut dag, terms.rhs, terms.lhs),
                equal,
                "{b} versus {a}"
            );
        }
    }

    #[test]
    fn renaming_comparison_preserves_aliasing_payloads_and_binding() {
        let mut dag = TermDag::default();
        let mut program = SlottedProgram::default();
        program.add_constructor("Pair", vec![ColumnKind::Child; 2]);
        program.add_constructor("Lam", vec![ColumnKind::Binder, ColumnKind::Child]);
        program.add_constructor("Num", vec![ColumnKind::Payload]);
        for (a, b, equal) in [
            ("(Pair $0 $1)", "(Pair $1 $0)", true),
            ("(Pair $0 $0)", "(Pair $1 $2)", false),
            ("(Lam $0 $0)", "(Lam $1 $2)", false),
            ("(Lam $0 (Pair $0 $1))", "(Lam $2 (Pair $2 $3))", true),
            ("(Pair (Lam $0 $0) $0)", "(Pair (Lam $1 $1) $2)", true),
            ("(Lam $0 (Lam $0 $0))", "(Lam $1 (Lam $2 $2))", true),
            ("(Lam $0 (Lam $0 $0))", "(Lam $1 (Lam $2 $1))", false),
            ("(Num 1)", "(Num 2)", false),
        ] {
            let lhs = program
                .ground_term(&mut dag, &parse_sexp(a).unwrap())
                .unwrap();
            let rhs = program
                .ground_term(&mut dag, &parse_sexp(b).unwrap())
                .unwrap();
            assert_eq!(
                program.eq_modulo_renaming(&mut dag, lhs, rhs),
                equal,
                "{a} vs {b}"
            );
        }
    }

    #[test]
    fn subst_is_refused() {
        let mut dag = TermDag::default();
        let mut program = SlottedProgram::default();
        let err = program
            .add_rewrite(
                &mut dag,
                r#"(rewrite (Let t $x b) (subst b $x t) :name "beta")"#,
            )
            .unwrap_err();
        assert!(err.0.contains("subst"));
    }
}
