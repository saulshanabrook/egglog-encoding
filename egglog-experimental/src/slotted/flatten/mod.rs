//! Flatten nested patterns into constructor atoms and lift proofs back to source rules.

pub(super) mod unflatten;

use super::model::*;
use super::query::{Conditions, ProofNames};
use egglog::ast::{Expr, Fact, Rewrite as SourceRewrite};
use std::collections::BTreeSet;

#[derive(Clone, Debug)]
pub(crate) struct Rewrite {
    pub rule: SourceRewrite,
    pub names: ProofNames,
}

#[derive(Clone, Debug)]
pub(super) struct Atom {
    pub root: String,
    /// Position in the surface pattern, before matching reorders the atoms.
    pub path: Vec<usize>,
    pub op: String,
    pub kids: Vec<Term>,
    pub pays: Vec<Term>,
}

/// Names shared by all patterns in one query, including generated names.
#[derive(Default)]
pub(super) struct PatternNames(BTreeSet<String>);

impl PatternNames {
    pub fn reserve(&mut self, name: &str) {
        self.0.insert(name.to_owned());
    }

    pub fn fresh(&mut self, stem: &str) -> String {
        let mut name = stem.to_owned();
        let mut suffix = 0;
        while !self.0.insert(name.clone()) {
            suffix += 1;
            name = format!("{stem}_{suffix}");
        }
        name
    }
}

pub(super) fn flatten(
    lang: &Language,
    t: &Term,
    root: &str,
    tmp: &str,
    names: &mut PatternNames,
) -> Result<Vec<Atom>, String> {
    fn go(
        lang: &Language,
        t: &Term,
        at: (String, Vec<usize>),
        tmp: &str,
        id: &mut usize,
        names: &mut PatternNames,
        out: &mut Vec<Atom>,
    ) -> Result<(), String> {
        let Term::Node(n, args) = t else {
            return Err("a pattern's root must be a constructor call".into());
        };
        let (root, path) = at;
        let op = &lang.constructors[n];
        let (children, pays) = op.split(args);
        let mut kids = Vec::new();
        let mut nested = Vec::new();
        let columns = op
            .columns
            .iter()
            .enumerate()
            .filter_map(|(i, c)| (!matches!(c, Column::Payload(_))).then_some(i));
        for (j, c) in columns.zip(children) {
            match c {
                Term::Variable(_) | Term::Slot(_) => kids.push(c.clone()),
                Term::Node(n, _)
                    if lang.constructors[n].children().is_empty() && !c.has_payload_variable() =>
                {
                    kids.push(c.clone())
                }
                Term::Node(_, _) => {
                    *id += 1;
                    let name = names.fresh(&format!("{tmp}{id}"));
                    kids.push(Term::Variable(name.clone()));
                    let mut subpath = path.clone();
                    subpath.push(j);
                    nested.push((c, (name, subpath)));
                }
                _ => return Err("unsupported term in pattern".into()),
            }
        }
        out.push(Atom {
            root,
            path,
            op: n.clone(),
            kids,
            pays: pays.into_iter().cloned().collect(),
        });
        for (c, name) in nested {
            go(lang, c, name, tmp, id, names, out)?;
        }
        Ok(())
    }
    let mut t = t.clone();
    lang.refresh_shadowed(&mut t);
    let mut out = Vec::new();
    names.reserve(root);
    go(
        lang,
        &t,
        (root.into(), vec![]),
        tmp,
        &mut 0,
        names,
        &mut out,
    )?;
    Ok(out)
}

pub(super) fn pattern_names(atoms: &[Atom]) -> Vec<(Vec<usize>, String)> {
    atoms
        .iter()
        .map(|a| (a.path.clone(), a.root.clone()))
        .collect()
}

pub(super) fn rewrite(
    lang: &Language,
    root: &str,
    lhs: &Term,
    rhs: &Term,
    atoms: &[Atom],
    conditions: &Conditions,
    mut names: ProofNames,
) -> Rewrite {
    let atom_term = |atom: &Atom| {
        let mut kids = atom.kids.iter();
        let mut pays = atom.pays.iter();
        let args = lang.constructors[&atom.op].columns.iter().map(|column| {
            source_expr(match column {
                Column::Payload(_) => pays.next().unwrap(),
                _ => kids.next().unwrap(),
            })
        });
        Expr::Call(egglog::span!(), atom.op.clone(), args.collect())
    };
    let root_atom = atoms
        .iter()
        .find(|atom| matches!(lhs, Term::Node(..)) && atom.root == root && atom.path.is_empty());
    let flat_lhs = root_atom.map_or_else(|| Expr::Var(egglog::span!(), root.to_owned()), atom_term);
    let mut flat_names = vec![
        root_atom
            .map(|atom| vec![(vec![], atom.root.clone())])
            .unwrap_or_default(),
    ];
    let mut facts = Vec::new();
    for atom in atoms {
        if root_atom.is_some_and(|a| a.root == atom.root && a.path == atom.path) {
            continue;
        }
        facts.push(Fact::Eq(
            egglog::span!(),
            Expr::Var(egglog::span!(), atom.root.clone()),
            atom_term(atom),
        ));
        flat_names.push(vec![(vec![], atom.root.clone())]);
    }
    for (var, value, _) in &conditions.values {
        facts.push(Fact::Eq(
            egglog::span!(),
            Expr::Var(egglog::span!(), var.clone()),
            source_expr(value),
        ));
        flat_names.push(vec![]);
    }

    let vars = |names: &[String]| {
        names
            .iter()
            .map(|name| Expr::Var(egglog::span!(), name.clone()))
            .collect()
    };
    let predicate = |head: &str, args| Fact::Fact(Expr::Call(egglog::span!(), head.into(), args));
    facts.extend(conditions.comparisons.iter().map(|(comparison, a, b)| {
        match (comparison.modulo_renaming, comparison.negated) {
            (false, false) => Fact::Eq(
                egglog::span!(),
                Expr::Var(egglog::span!(), a.clone()),
                Expr::Var(egglog::span!(), b.clone()),
            ),
            (false, true) => predicate("!=", vars(&[a.clone(), b.clone()])),
            (true, false) => predicate("renaming-=", vars(&[a.clone(), b.clone()])),
            (true, true) => predicate("renaming-!=", vars(&[a.clone(), b.clone()])),
        }
    }));
    facts.extend(
        conditions
            .payload_comparisons
            .iter()
            .map(|(negated, a, b)| {
                if *negated {
                    predicate("!=", vec![source_expr(a), source_expr(b)])
                } else {
                    Fact::Eq(egglog::span!(), source_expr(a), source_expr(b))
                }
            }),
    );
    facts.extend(conditions.free_names.iter().map(|(var, slots)| {
        predicate(
            "free-names-are",
            vars(
                &std::iter::once(var.clone())
                    .chain(slots.iter().cloned())
                    .collect::<Vec<_>>(),
            ),
        )
    }));
    facts.extend(conditions.free.iter().map(|(free, slot, names)| {
        predicate(
            if *free { "free" } else { "not-free" },
            vars(
                &std::iter::once(slot.clone())
                    .chain(names.iter().cloned())
                    .collect::<Vec<_>>(),
            ),
        )
    }));
    names.patterns = flat_names;
    Rewrite {
        rule: SourceRewrite {
            span: egglog::span!(),
            lhs: flat_lhs,
            rhs: source_expr(rhs),
            conditions: facts,
            name: String::new(),
        },
        names,
    }
}
