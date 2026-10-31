//! Source terms and typed constructor layouts, independent of query emission.
use super::slots::Slots;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Debug)]
pub(super) struct Symbols {
    pub sort: String,
    pub index: usize,
    pub var: String,
    pub renames: String,
    pub equated: String,
    pub free_vars: String,
    pub subst_pending: String,
    pub shape_equal: String,
    pub invocation: String,
    pub group: String,
    pub coset_reps: String,
    pub big_reading: String,
    pub reading: String,
}

impl Symbols {
    pub fn new(sort: &str, i: usize, var: &str) -> Self {
        Self {
            sort: sort.into(),
            index: i,
            var: var.into(),
            renames: format!("RenamesToLeader_{i}"),
            equated: format!("Equated_{i}"),
            free_vars: format!("FreeVars_{i}"),
            subst_pending: format!("SubstPending_{i}"),
            shape_equal: format!("ShapeEqual_{i}"),
            invocation: format!("Invocation_{i}"),
            group: format!("EclassGroup_{i}"),
            coset_reps: format!("CosetReps_{i}"),
            big_reading: format!("BigReading_{i}"),
            reading: format!("Reading_{i}"),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
/// A source constructor argument's role in binding and renaming.
pub enum Column {
    /// A child in the constructor's carrier sort.
    Child,
    /// A rigid slot name in the carrier's variable constructor.
    Var,
    /// A slot binding the following child column.
    Binder,
    /// A literal or variable of the named payload sort.
    Payload(String),
}

#[derive(Clone, Debug)]
/// A source constructor's carrier sort and argument roles.
pub struct Constructor {
    /// The constructor name.
    pub name: String,
    /// The result sort, also used by child columns.
    pub sort: String,
    /// Argument roles in source order.
    pub columns: Vec<Column>,
}

impl Constructor {
    /// The sort of an argument, or `None` for an out-of-range index.
    pub fn column_sort(&self, index: usize) -> Option<&str> {
        self.columns.get(index).map(|column| match column {
            Column::Payload(sort) => sort.as_str(),
            Column::Var | Column::Binder => "Var",
            Column::Child => self.sort.as_str(),
        })
    }

    /// Argument sorts in source order.
    pub fn input_sorts(&self) -> impl Iterator<Item = &str> {
        (0..self.columns.len()).map(|i| self.column_sort(i).unwrap())
    }

    pub(super) fn children(&self) -> Vec<&Column> {
        self.columns
            .iter()
            .filter(|c| !matches!(c, Column::Payload(_)))
            .collect()
    }
    pub(super) fn binders(&self) -> Vec<usize> {
        self.children()
            .iter()
            .enumerate()
            .filter_map(|(i, c)| (**c == Column::Binder).then_some(i))
            .collect()
    }
    pub(super) fn covered(&self) -> Option<usize> {
        self.binders().last().map(|i| i + 1)
    }
    pub(super) fn types(&self) -> String {
        self.columns
            .iter()
            .map(|c| match c {
                Column::Payload(s) => s.clone(),
                Column::Var | Column::Binder => "Renaming".into(),
                Column::Child => format!("Renaming {}", self.sort),
            })
            .collect::<Vec<_>>()
            .join(" ")
    }
    pub(super) fn node(
        &self,
        head: &str,
        edges: &[String],
        kids: &[String],
        pays: &[String],
    ) -> String {
        let (mut k, mut p) = (0, 0);
        let mut args = Vec::new();
        for col in &self.columns {
            if matches!(col, Column::Payload(_)) {
                args.push(pays[p].clone());
                p += 1;
            } else {
                args.push(edges[k].clone());
                if *col == Column::Child {
                    args.push(kids[k].clone());
                }
                k += 1;
            }
        }
        call(head, args)
    }
    pub(super) fn split<'a>(&self, args: &'a [Term]) -> (Vec<&'a Term>, Vec<&'a Term>) {
        let mut kids = Vec::new();
        let mut pays = Vec::new();
        for (c, t) in self.columns.iter().zip(args) {
            if matches!(c, Column::Payload(_)) {
                pays.push(t)
            } else {
                kids.push(t)
            }
        }
        (kids, pays)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum Term {
    Slot(String),
    Variable(String),
    Global(String),
    Payload(String),
    PayloadVariable(String),
    Node(String, Vec<Term>),
    Subst(Box<[Term; 3]>),
}

#[derive(Clone, Default)]
pub(super) struct Language {
    pub carriers: Vec<Symbols>,
    pub constructors: BTreeMap<String, Constructor>,
    pub globals: BTreeMap<String, Term>,
    pub slot_names: Slots,
}

impl Language {
    pub fn global_slot(&self, name: &str) -> Option<&str> {
        match &self.globals[name] {
            Term::Slot(slot) => Some(slot),
            Term::Global(other) => self.global_slot(other),
            _ => None,
        }
    }
    pub fn symbols(&self, sort: &str) -> &Symbols {
        self.carriers
            .iter()
            .find(|s| s.sort == sort)
            .expect("validated carrier")
    }
    pub fn sort_of(&self, t: &Term) -> Option<&str> {
        match t {
            Term::Slot(_) => Some("Var"),
            Term::Node(n, _) => Some(&self.constructors[n].sort),
            Term::Global(n) => self.sort_of(&self.globals[n]),
            _ => None,
        }
    }
    pub fn slots(&self, t: &Term) -> BTreeSet<String> {
        match t {
            Term::Slot(s) => BTreeSet::from([s.clone()]),
            Term::Global(n) => self.slots(&self.globals[n]),
            Term::Node(n, args) => {
                let op = &self.constructors[n];
                let (kids, _) = op.split(args);
                let bound: BTreeSet<_> = op
                    .binders()
                    .iter()
                    .flat_map(|&i| self.slots(kids[i]))
                    .collect();
                kids.iter()
                    .enumerate()
                    .filter(|(i, _)| !op.binders().contains(i))
                    .flat_map(|(i, k)| {
                        let mut slots = self.slots(k);
                        if Some(i) == op.covered() {
                            slots.retain(|s| !bound.contains(s));
                        }
                        slots
                    })
                    .collect()
            }
            _ => BTreeSet::new(),
        }
    }
    pub fn encode(&self, t: &Term) -> String {
        match t {
            Term::Slot(_) => self.edge(t),
            Term::Global(n) if self.global_slot(n).is_some() => self.edge(t),
            Term::Global(n) => format!("${n}"),
            Term::Node(n, args) => {
                let op = &self.constructors[n];
                let (kids, pays) = op.split(args);
                let edges = kids.iter().map(|k| self.edge(k)).collect::<Vec<_>>();
                let children = kids.iter().map(|k| self.encode(k)).collect::<Vec<_>>();
                let pays = pays
                    .iter()
                    .map(|p| match p {
                        Term::Payload(p) => p.clone(),
                        _ => unreachable!("ground payload"),
                    })
                    .collect::<Vec<_>>();
                op.node(n, &edges, &children, &pays)
            }
            _ => unreachable!("ground term"),
        }
    }
    pub fn edge(&self, t: &Term) -> String {
        if let Term::Global(n) = t {
            return self.edge(&self.globals[n]);
        }
        if let Term::Slot(s) = t {
            return format!("(map-of 0 {})", self.slot_names.id(s));
        }
        let mut slots = self
            .slots(t)
            .into_iter()
            .map(|s| self.slot_names.id(&s))
            .collect::<Vec<_>>();
        slots.sort();
        if slots.is_empty() {
            "(map-empty)".into()
        } else {
            call(
                "map-of",
                slots
                    .into_iter()
                    .flat_map(|s| [s.to_string(), s.to_string()]),
            )
        }
    }
    /// Nested binder columns with the same spelling shadow outer columns.
    pub fn refresh_shadowed(&self, t: &mut Term) {
        let mut used = BTreeSet::new();
        t.slot_literals(&mut used);
        self.refresh(t, &mut used);
    }
    fn refresh(&self, t: &mut Term, used: &mut BTreeSet<String>) {
        if let Term::Node(n, args) = t {
            let op = &self.constructors[n];
            for (col, t) in op.columns.iter().zip(args.iter_mut()) {
                if *col == Column::Child {
                    self.refresh(t, used);
                }
            }
            let mut seen = BTreeSet::new();
            for (col, t) in op.columns.iter().zip(args).rev() {
                if *col == Column::Binder
                    && let Term::Slot(s) = t
                    && !seen.insert(s.clone())
                {
                    let mut i = 0;
                    while used.contains(&format!("${i}")) {
                        i += 1;
                    }
                    *s = format!("${i}");
                    used.insert(s.clone());
                }
            }
        }
    }
}

impl Term {
    pub fn slot_literals(&self, out: &mut BTreeSet<String>) {
        match self {
            Self::Slot(s) => {
                out.insert(s.clone());
            }
            Self::Node(_, args) => {
                for t in args {
                    t.slot_literals(out)
                }
            }
            Self::Subst(args) => {
                for t in args.iter() {
                    t.slot_literals(out)
                }
            }
            _ => {}
        }
    }
    pub fn has_payload_variable(&self) -> bool {
        match self {
            Self::PayloadVariable(_) => true,
            Self::Node(_, args) => args.iter().any(Self::has_payload_variable),
            _ => false,
        }
    }
    pub fn uses_subst(&self) -> bool {
        match self {
            Self::Subst(_) => true,
            Self::Node(_, args) => args.iter().any(Self::uses_subst),
            _ => false,
        }
    }
}

pub(super) fn call(head: &str, args: impl IntoIterator<Item = String>) -> String {
    let args = args.into_iter().collect::<Vec<_>>();
    if args.is_empty() {
        format!("({head})")
    } else {
        format!("({head} {})", args.join(" "))
    }
}
pub(super) fn fold(op: &str, xs: impl IntoIterator<Item = String>, empty: &str) -> String {
    let xs = xs.into_iter().collect::<Vec<_>>();
    let Some((last, rest)) = xs.split_last() else {
        return empty.into();
    };
    rest.iter()
        .rev()
        .fold(last.clone(), |tail, x| format!("({op} {x} {tail})"))
}
pub(super) fn names(prefix: &str, n: usize) -> Vec<String> {
    (1..=n).map(|i| format!("{prefix}{i}")).collect()
}

pub(super) fn source_expr(term: &Term) -> egglog::ast::Expr {
    use egglog::ast::{Expr, Parser};
    let span = egglog::span!();
    match term {
        Term::Slot(s) | Term::Variable(s) | Term::Global(s) | Term::PayloadVariable(s) => {
            Expr::Var(span, s.clone())
        }
        Term::Payload(s) => Parser::default()
            .get_expr_from_string(None, s)
            .expect("validated payload literal"),
        Term::Node(head, args) => {
            Expr::Call(span, head.clone(), args.iter().map(source_expr).collect())
        }
        Term::Subst(args) => {
            Expr::Call(span, "subst".into(), args.iter().map(source_expr).collect())
        }
    }
}
