//! Multipattern matching, shared by rewrites and checks.
use super::model::*;
use super::syntax::quote;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Debug)]
pub(super) struct Atom {
    pub root: String,
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
        root: String,
        tmp: &str,
        id: &mut usize,
        names: &mut PatternNames,
        out: &mut Vec<Atom>,
    ) -> Result<(), String> {
        let Term::Node(n, args) = t else {
            return Err("a pattern's root must be a constructor call".into());
        };
        let (children, pays) = lang.constructors[n].split(args);
        let mut kids = Vec::new();
        let mut nested = Vec::new();
        for c in children {
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
                    nested.push((c, name));
                }
                _ => return Err("unsupported term in pattern".into()),
            }
        }
        out.push(Atom {
            root,
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
    go(lang, &t, root.into(), tmp, &mut 0, names, &mut out)?;
    Ok(out)
}

fn variables(a: &Atom) -> BTreeSet<String> {
    std::iter::once(a.root.clone()).chain(children(a)).collect()
}
fn children(a: &Atom) -> BTreeSet<String> {
    a.kids
        .iter()
        .filter_map(|k| {
            if let Term::Variable(v) = k {
                Some(v.clone())
            } else {
                None
            }
        })
        .collect()
}
/// Order a nonempty multipattern to join connected atoms before disconnected ones.
pub(super) fn connected(mut atoms: Vec<Atom>) -> Vec<Atom> {
    let a = atoms.remove(0);
    let mut seen = variables(&a);
    let mut roots = BTreeSet::from([a.root.clone()]);
    let mut kids = children(&a);
    let mut out = vec![a];
    while !atoms.is_empty() {
        let i = atoms
            .iter()
            .position(|a| kids.contains(&a.root) || !children(a).is_disjoint(&roots))
            .or_else(|| atoms.iter().position(|a| !variables(a).is_disjoint(&seen)))
            .unwrap_or(0);
        let a = atoms.remove(i);
        seen.extend(variables(&a));
        roots.insert(a.root.clone());
        kids.extend(children(&a));
        out.push(a);
    }
    out
}

/// Equality of applied terms, or just their classes.
#[derive(Clone, Copy)]
pub(super) struct Comparison {
    pub modulo_renaming: bool,
    pub negated: bool,
}

impl Comparison {
    pub fn parse(name: &str) -> Option<Self> {
        let (modulo_renaming, negated) = match name {
            "=" => (false, false),
            "!=" => (false, true),
            "renaming-=" => (true, false),
            "renaming-!=" => (true, true),
            _ => return None,
        };
        Some(Self {
            modulo_renaming,
            negated,
        })
    }

    /// Class constraints can filter candidates before slot refinement.
    pub fn classes(self, a: &str, b: &str) -> Option<String> {
        if !self.negated {
            Some(format!("(= {a} {b})"))
        } else if self.modulo_renaming {
            Some(format!("(guard (bool-!= {a} {b}))"))
        } else {
            None
        }
    }

    /// Compare two (class, renaming) invocations in a common slot frame, allowing
    /// the class's known symmetries. Class-only comparisons need no slot guard.
    pub fn invocations(self, group: &str, a: (&str, &str), b: (&str, &str)) -> Option<String> {
        if self.modulo_renaming {
            return None;
        }
        let same = format!("(coset-same {} {} ({group} {}))", a.1, b.1, a.0);
        Some(if self.negated {
            format!("(guard (or (bool-!= {} {}) (not {same})))", a.0, b.0)
        } else {
            format!("(guard {same})")
        })
    }
}

#[derive(Default, Clone)]
pub(super) struct Conditions {
    pub free: Vec<(bool, String, Vec<String>)>,
    pub free_names: Vec<(String, Vec<String>)>,
    pub comparisons: Vec<(Comparison, String, String)>,
    pub fresh: BTreeSet<String>,
    pub values: Vec<(String, Term, String)>,
    pub concrete_slots: BTreeMap<String, i64>,
    pub global_frame: String,
}

/// Slot sets are identity maps; membership and exact-set queries use the same
/// representation for checks and rewrite guards.
pub(super) fn free_condition(want: bool, slot: &str, maps: &[String]) -> String {
    let image = maps.iter().fold("(map-empty)".to_owned(), |set, map| {
        format!("(map-union {set} (map-image {map}))")
    });
    format!(
        "({} {image} {slot})",
        if want {
            "map-contains"
        } else {
            "map-not-contains"
        }
    )
}

pub(super) fn free_names_condition(map: &str, slots: &[String]) -> String {
    let wanted = if slots.is_empty() {
        "(map-empty)".into()
    } else {
        call("map-of", slots.iter().flat_map(|s| [s.clone(), s.clone()]))
    };
    format!("(= (map-image {map}) {wanted})")
}

#[derive(Default)]
pub(super) struct Query {
    pub body: Vec<String>,
    pub classes: Vec<(String, String)>,
    pub sorts: BTreeMap<String, String>,
    pub slots: BTreeMap<String, String>,
    pub maps: BTreeMap<String, String>,
    pub pays: BTreeMap<String, (String, String)>,
    pub frame: String,
    pub split: Option<usize>,
    pub refined: String,
    pub length: String,
    pub filter_start: usize,
    used: BTreeSet<String>,
    prefix: String,
    id: usize,
}
impl Query {
    pub fn fresh(&mut self, stem: &str) -> String {
        let mut name = format!("{}{stem}", self.prefix);
        while !self.used.insert(name.clone()) {
            self.id += 1;
            name = format!("{}{stem}_{}", self.prefix, self.id);
        }
        name
    }
    pub fn class(&self, pv: &str) -> Result<String, String> {
        self.classes
            .iter()
            .find(|(p, _)| p == pv)
            .map(|(_, c)| c.clone())
            .ok_or_else(|| format!("pattern variable {pv:?} is not bound"))
    }
    fn bind(&mut self, pv: &str) -> String {
        if let Ok(c) = self.class(pv) {
            c
        } else {
            let c = self.fresh(&format!("cls_{}", label(pv)));
            self.classes.push((pv.into(), c.clone()));
            c
        }
    }
    pub fn payload(&self, t: &Term) -> Result<String, String> {
        match t {
            Term::Payload(s) => Ok(s.clone()),
            Term::PayloadVariable(p) => self
                .pays
                .get(p)
                .map(|(v, _)| v.clone())
                .ok_or_else(|| format!("payload variable {p:?} is not bound")),
            _ => Err("invalid payload".into()),
        }
    }
}
fn label(s: &str) -> &str {
    let s = s.trim_start_matches('_');
    if s.is_empty() { "v" } else { s }
}
pub(super) fn names_expr(xs: impl IntoIterator<Item = String>) -> String {
    call("names", xs.into_iter().map(|x| quote(&x)))
}

fn occurrence(
    q: &mut Query,
    lang: &Language,
    pv: &str,
    root: bool,
    parents: &BTreeMap<String, (String, String, usize)>,
    groups: &mut BTreeMap<String, String>,
    facts: &mut Vec<String>,
) -> Result<String, String> {
    let symbols = lang.symbols(&q.sorts[pv]);
    if root
        && pv.starts_with('_')
        && let Some((op, cols, j)) = parents.get(pv)
    {
        let sym = q.fresh(&format!("sym_{}", label(pv)));
        let pinned = q.fresh(&format!("pinned_{}", label(pv)));
        facts.push(format!("(= {pinned} (_pinned_{op} {cols} {j}))"));
        facts.push(format!(
            "({} {} {pinned} {sym})",
            symbols.reading,
            q.class(pv)?
        ));
        return Ok(format!(" {sym}"));
    }
    if !groups.contains_key(pv) {
        let g = q.fresh(&format!("grp_{}", label(pv)));
        facts.push(format!("(= {g} ({} {}))", symbols.group, q.class(pv)?));
        groups.insert(pv.into(), g);
    }
    Ok(format!(" {}", groups[pv]))
}

pub(super) fn compile(
    lang: &Language,
    atoms: &[Atom],
    conditions: &Conditions,
    prefix: &str,
    refine: bool,
    anchor: Option<&str>,
    nested: bool,
) -> Result<Query, String> {
    let mut q = Query {
        prefix: prefix.into(),
        ..Default::default()
    };
    for (root, _, sort) in &conditions.values {
        q.sorts.insert(root.clone(), sort.clone());
    }
    for a in atoms {
        let sort = &lang.constructors[&a.op].sort;
        for pv in variables(a) {
            if let Some(previous) = q.sorts.insert(pv.clone(), sort.clone())
                && previous != *sort
            {
                return Err(format!(
                    "pattern variable {pv:?} has incompatible sorts {previous} and {sort}"
                ));
            }
        }
    }
    let mut seen = BTreeSet::new();
    let mut literals = BTreeSet::new();
    let mut avs = Vec::new();
    let mut parents = BTreeMap::new();
    let mut groups = BTreeMap::new();
    let mut globals = Vec::new();
    for (root, value, sort) in &conditions.values {
        let sy = lang.symbols(sort);
        let class = q.bind(root);
        let label = q.fresh("value");
        match value {
            Term::Global(_) => {
                let edge = q.fresh("global_edge");
                q.body.push(format!(
                    "({} {} {edge} {class})",
                    sy.renames,
                    lang.encode(value, sort)
                ));
                globals.push(format!(
                    "(child {} (compose {} {edge}) ({} {class}))",
                    quote(root),
                    lang.edge(value),
                    sy.free_vars
                ));
            }
            Term::Slot(slot) => {
                q.body.push(format!("(= {class} ({} 0))", sy.var));
                q.body.push(format!(
                    "(= {label} (atom {} (root {} ({} {class})) (lit {} (map-of 0 0))))",
                    quote(&label),
                    quote(root),
                    sy.free_vars,
                    quote(slot)
                ));
                literals.insert(slot.clone());
                avs.push(label);
            }
            _ => unreachable!("query values are globals or slots"),
        }
        seen.insert(root.clone());
    }
    for id in conditions.concrete_slots.values() {
        globals.push(format!("(leaf (map-of 0 {id}))"));
    }
    if !globals.is_empty() {
        let label = q.fresh("globals");
        q.body.push(format!(
            "(= {label} (global-frame {} {}))",
            quote(&conditions.global_frame),
            globals.join(" ")
        ));
        avs.push(label);
    }
    for (idx, a) in atoms.iter().enumerate() {
        let op = &lang.constructors[&a.op];
        let sy = lang.symbols(&op.sort);
        let edges = a
            .kids
            .iter()
            .enumerate()
            .map(|(j, k)| {
                q.fresh(&format!(
                    "e{idx}_{}",
                    match k {
                        Term::Variable(v) => label(v).into(),
                        Term::Slot(s) => format!("lit_{}", &s[1..]),
                        _ => format!("leaf{j}"),
                    }
                ))
            })
            .collect::<Vec<_>>();
        let pay_cols = op.columns.iter().filter_map(|c| {
            if let Column::Payload(s) = c {
                Some(s)
            } else {
                None
            }
        });
        for (col, p) in pay_cols.zip(&a.pays) {
            if let Term::PayloadVariable(p) = p {
                if let Some((_, sort)) = q.pays.get(p) {
                    if sort != col {
                        return Err(format!("payload variable {p:?} has incompatible sorts"));
                    }
                } else {
                    let name = q.fresh(&format!("pay_{p}"));
                    q.pays.insert(p.clone(), (name, col.clone()));
                }
            }
        }
        let rv = q.bind(&a.root);
        let mut facts = Vec::new();
        let mut bindings = Vec::new();
        let mut kids = Vec::new();
        let mut reached = Vec::new();
        let reading = if seen.contains(&a.root) {
            occurrence(
                &mut q,
                lang,
                &a.root,
                true,
                &parents,
                &mut groups,
                &mut facts,
            )?
        } else {
            String::new()
        };
        bindings.push(format!(
            "(root {} ({} {rv}){reading})",
            quote(&a.root),
            sy.free_vars
        ));
        seen.insert(a.root.clone());
        for (j, (k, e)) in a.kids.iter().zip(&edges).enumerate() {
            match k {
                Term::Variable(pv) => {
                    let c = q.bind(pv);
                    kids.push(c.clone());
                    let reading = if seen.contains(pv) {
                        occurrence(&mut q, lang, pv, false, &parents, &mut groups, &mut facts)?
                    } else {
                        String::new()
                    };
                    bindings.push(format!(
                        "(child {} {e} ({} {c}){reading})",
                        quote(pv),
                        sy.free_vars
                    ));
                    seen.insert(pv.clone());
                }
                Term::Slot(s) => {
                    kids.push(format!("({} 0)", sy.var));
                    literals.insert(s.clone());
                    bindings.push(format!(
                        "({} {} {e})",
                        if op.binders().contains(&j) {
                            "bound"
                        } else {
                            "lit"
                        },
                        quote(s)
                    ));
                }
                Term::Node(_, _) => {
                    let c = q.fresh(&format!("leaf{idx}_{j}"));
                    kids.push(c.clone());
                    reached.push((k, c, j));
                    bindings.push(format!("(leaf {e})"));
                }
                _ => return Err("invalid flattened child".into()),
            }
        }
        let pays = a
            .pays
            .iter()
            .map(|p| q.payload(p))
            .collect::<Result<Vec<_>, _>>()?;
        let node = op.node(&op.name, &edges, &kids, &pays);
        q.body.push(format!("(= {rv} {node})"));
        let cols = node[op.name.len() + 1..node.len() - 1]
            .trim_start()
            .to_owned();
        for (j, k) in a.kids.iter().enumerate() {
            if let Term::Variable(pv) = k {
                parents
                    .entry(pv.clone())
                    .or_insert((op.name.clone(), cols.clone(), j + 1));
            }
        }
        for (t, c, j) in reached {
            let ren = q.fresh(&format!("leafren{idx}_{j}"));
            q.body.push(format!(
                "({} {} {ren} {c})",
                sy.renames,
                lang.encode(t, &op.sort)
            ));
        }
        q.body.extend(facts);
        let av = q.fresh(&format!("atom_{idx}"));
        q.body.push(format!(
            "(= {av} ({} \"@atom:{idx}\" {}))",
            if nested { "nested-atom" } else { "atom" },
            bindings.join(" ")
        ));
        avs.push(av);
    }
    for (comparison, a, b) in &conditions.comparisons {
        let (ca, cb) = (q.class(a)?, q.class(b)?);
        if q.sorts[a] != q.sorts[b] {
            return Err("equality compares different carrier sorts".into());
        }
        q.body.extend(comparison.classes(&ca, &cb));
    }
    let mut frame = avs.first().cloned().unwrap_or_else(|| "(frame)".into());
    for av in avs.iter().skip(1) {
        frame = format!("(frame-join {frame} {av})");
    }
    if avs.len() > 1 {
        let f = q.fresh("f");
        q.body.push(format!("(= {f} {frame})"));
        frame = f;
    }
    if let Some(root) = anchor
        && !avs.is_empty()
    {
        frame = format!("(anchor {frame} {})", quote(root));
    }
    if refine && !avs.is_empty() {
        q.refined = q.fresh("refined");
        let choice = q.fresh("choice");
        q.length = q.fresh("refined_len");
        q.body.extend([
            format!("(= {} (refinements {frame}))", q.refined),
            format!("(= {} (vec-length {}))", q.length, q.refined),
            format!("(> {} 0)", q.length),
        ]);
        q.split = Some(q.body.len());
        q.body.push(format!("(Idx {} {choice})", q.length));
        frame = format!("(vec-get {} {choice})", q.refined);
    }
    if !conditions.fresh.is_empty() {
        frame = format!(
            "(mint {frame} {})",
            names_expr(conditions.fresh.iter().cloned())
        );
    }
    q.frame = q.fresh("m");
    q.body.push(format!("(= {} {frame})", q.frame));
    for (pv, _) in &q.classes {
        q.maps
            .insert(pv.clone(), format!("(ren {} {})", q.frame, quote(pv)));
    }
    for lit in literals.union(&conditions.fresh) {
        q.slots.insert(
            lit.clone(),
            format!("(map-get (ren {} {}) 0)", q.frame, quote(lit)),
        );
    }
    for (name, id) in &conditions.concrete_slots {
        q.slots.insert(
            name.clone(),
            format!(
                "(map-get (ren {} {}) {id})",
                q.frame,
                quote(&conditions.global_frame)
            ),
        );
    }
    q.filter_start = q.body.len();
    for (want, slot, pvars) in &conditions.free {
        if !q.slots.contains_key(slot) {
            return Err(format!("slot {slot} is not bound by the pattern"));
        }
        let maps = pvars
            .iter()
            .map(|v| {
                q.class(v)?;
                Ok(q.maps[v].clone())
            })
            .collect::<Result<Vec<_>, String>>()?;
        q.body.push(free_condition(*want, &q.slots[slot], &maps));
    }
    for (v, slots) in &conditions.free_names {
        q.class(v)?;
        let slots = slots
            .iter()
            .map(|s| {
                q.slots
                    .get(s)
                    .cloned()
                    .ok_or_else(|| format!("slot {s} is not bound by the pattern"))
            })
            .collect::<Result<Vec<_>, _>>()?;
        q.body.push(free_names_condition(&q.maps[v], &slots));
    }
    for (comparison, a, b) in &conditions.comparisons {
        let (ca, cb) = (q.class(a)?, q.class(b)?);
        q.body.extend(comparison.invocations(
            &lang.symbols(&q.sorts[a]).group,
            (&ca, &q.maps[a]),
            (&cb, &q.maps[b]),
        ));
    }
    Ok(q)
}
