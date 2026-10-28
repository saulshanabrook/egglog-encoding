//! Translation of an egglog proof over the encoded program to a slotted proof
//! over surface terms; see *Translation* in `egglog-experimental/src/slotted/PROOFS.md`.
//!
//! Encoded rows are interpreted as ordinary surface equalities. The translation
//! rules and their derivations are described in the proof guide above.

use super::format::{SlottedConclusion, SlottedProofStore, SlottedProposition};
use super::lifting::{LiftedId, Lifting};
use super::pipeline::EncodingNames;
use super::source::{Claim, ColumnKind, Rhs, SlottedProgram};
use super::terms::{FreshSlots, Renaming, all_slots, rename, slot_of, slot_term};

use super::{HashMap, HashSet};
use crate::slotted::query::ProofNames;
use crate::slotted::runtime::frame_from_term;
use crate::slotted::runtime::renaming::shape;
use crate::slotted::runtime::terms::{group_from_term, renaming_from_term, renamings_from_term};
use crate::slotted::runtime::{Fr, Renaming as SlotMap, SlotSet};
use egglog::ast::Literal;
use egglog::proof::{Justification, ProofId, ProofStore};
use egglog::util::IndexMap;
use egglog::{Term, TermDag, TermId};
use std::collections::{BTreeMap, BTreeSet};

type R<T> = Result<T, String>;
type ShapeKey = (String, Vec<SlotMap>, Vec<TermId>, Vec<TermId>);
type SymmetryPremises = Vec<(TermId, ProofId)>;
type ConditionProof = (String, TermId, LiftedId, HashMap<Vec<usize>, Occurrence>);

/// Translate the egglog proof `root`, which proves the encoded form of `claim`,
/// into a slotted proof of the claim over `dag`, the program's term dag.
/// `query` records the generated bindings and `roots` identifies its two sides.
#[allow(clippy::too_many_arguments)]
pub(super) fn translate(
    program: &SlottedProgram,
    dag: TermDag,
    names: &EncodingNames,
    egg: &ProofStore,
    root: ProofId,
    claim: &Claim,
    query: &ProofNames,
    roots: [&str; 2],
) -> R<(SlottedProofStore, SlottedConclusion)> {
    let mut tr = Translator::new(program, dag, names, egg);
    let id = tr.claim(root, claim, query, roots)?;
    Ok(tr.out.finish(id))
}

fn query_firing(egg: &ProofStore, root: ProofId, frame: &str) -> R<ProofId> {
    match egg.get(root).justification() {
        Justification::Rule { substitution, .. } if substitution.contains_key(frame) => Ok(root),
        Justification::Congr { proof, .. } | Justification::Sym(proof) => {
            query_firing(egg, *proof, frame)
        }
        Justification::Trans(a, b) => {
            query_firing(egg, *a, frame).or_else(|_| query_firing(egg, *b, frame))
        }
        _ => Err(format!("existence proof has no query binding {frame}")),
    }
}

pub(super) fn matched_frame(egg: &ProofStore, root: ProofId, names: &ProofNames) -> R<Fr> {
    let root = query_firing(egg, root, &names.frame)?;
    let Justification::Rule { substitution, .. } = egg.get(root).justification() else {
        unreachable!("query_firing returns a rule firing")
    };
    frame_from_term(egg.term_dag(), substitution[&names.frame])
        .ok_or_else(|| "query frame is not a frame".into())
}

struct Translator<'a> {
    program: &'a SlottedProgram,
    names: &'a EncodingNames,
    egg: &'a ProofStore,
    out: Lifting,
    /// Encoded term -> its surface term.
    dec_memo: HashMap<TermId, TermId>,
    /// (encoded node, surface column) -> the permutation that completed the
    /// column's edge when the node was decoded.
    edge_memo: HashMap<(TermId, usize), Renaming>,
    /// Egglog proof -> the slotted proof of the equality it denotes.
    eq_memo: HashMap<ProofId, LiftedId>,
    /// Surface term -> a slotted proof whose left side it is, from which its
    /// reflexivity follows.
    known: HashMap<TermId, LiftedId>,
    /// A node spelled with canonical edges, shared by every row that has that shape.
    shape_terms: HashMap<ShapeKey, TermId>,
    /// Proofs of `FreeVars` rows by class, for redundancy certificates.
    free_vars_index: Option<HashMap<TermId, Vec<ProofId>>>,
    group_index: Option<HashMap<TermId, Vec<ProofId>>>,
    /// The `(class, slot)` certificates being derived, against circularity.
    cert_stack: HashSet<(TermId, i64)>,
    fresh: FreshSlots,
    reserved_terms: usize,
}

/// A pattern position's class, and the row an atom there matched.
#[derive(Clone, Copy)]
struct Occurrence {
    cls: TermId,
    row: Option<(TermId, LiftedId)>,
}

/// A pattern expansion and its local bindings.
struct Expansion {
    proof: LiftedId,
    variables: HashMap<String, TermId>,
    occurrences: HashMap<Vec<usize>, Occurrence>,
}

/// What an expansion walks over: the match's premises and substitution, the
/// compiler's actual bindings, and the flattener's atom names by path.
#[derive(Clone)]
struct ExpandCtx<'a> {
    prems: &'a [ProofId],
    subst: &'a IndexMap<String, TermId>,
    names: HashMap<Vec<usize>, String>,
    classes: BTreeMap<String, String>,
    readings: BTreeMap<String, String>,
    /// Classes the stored match was re-keyed to after its firing: the class a
    /// premise row mentions -> the proof that it equals the class it became.
    bridges: &'a HashMap<TermId, ProofId>,
}

/// What a relation row stands for.
enum RowKind {
    /// `(R a m b)`: `dec(a) = m·dec(b)`.
    Edge,
    /// `(Invocation c name a)`: `dec(a) = name·dec(c)`.
    Invocation,
    Other,
}

fn row_kind(head: &str) -> RowKind {
    let base = head.rsplit_once('_').map_or(head, |(b, _)| b);
    match base {
        "RenamesToLeader" | "Equated" | "ShapeEqual" => RowKind::Edge,
        "Invocation" => RowKind::Invocation,
        _ => RowKind::Other,
    }
}

/// Index proofs of rows in one family by the class in their first column.
fn row_proofs(egg: &ProofStore, prefix: &str) -> HashMap<TermId, Vec<ProofId>> {
    egg.proofs()
        .filter_map(|(id, proof)| {
            let Term::App(head, args) = egg.term_dag().get(proof.lhs()) else {
                return None;
            };
            (proof.lhs() == proof.rhs() && head.starts_with(prefix) && args.len() >= 2)
                .then(|| (args[0], id))
        })
        .fold(HashMap::default(), |mut index, (cls, id)| {
            index.entry(cls).or_default().push(id);
            index
        })
}

/// What a compiled rule is: a user rewrite's own rule `name` or its `name/apply`,
/// found by the program's rewrites, or else the machinery's `slotted/<kind>/...`.
/// A user rewrite named `slotted/custom` is still the user's.
fn rule_kind<'n>(program: &SlottedProgram, name: &'n str) -> (&'n str, &'n str) {
    if let Some(user) = name.strip_suffix("/apply")
        && program.rewrites.contains_key(user)
    {
        return (user, "apply");
    }
    if program.rewrites.contains_key(name) {
        return (name, "");
    }
    if let Some(rest) = name.strip_prefix("slotted/") {
        let kind = rest.split('/').next().unwrap_or(rest);
        ("slotted", kind)
    } else {
        (name, "")
    }
}

impl<'a> Translator<'a> {
    fn new(
        program: &'a SlottedProgram,
        dag: TermDag,
        names: &'a EncodingNames,
        egg: &'a ProofStore,
    ) -> Self {
        // Every encoded slot/renaming coordinate is an integer term. Reserving all
        // integer literals also excludes payloads, harmlessly, without guessing the
        // types of extracted primitive values. Reserve surface names as well: a
        // claim may mention slots that the encoding has already canonicalized away.
        let fresh = FreshSlots::new(
            (0..dag.size())
                .filter_map(|t| slot_of(&dag, t))
                .chain(program.slot_names.values().copied())
                .chain(
                    (0..egg.term_dag().size()).filter_map(|t| match egg.term_dag().get(t) {
                        Term::Lit(Literal::Int(n)) => Some(*n),
                        _ => None,
                    }),
                ),
        );
        let reserved_terms = dag.size();
        Self {
            program,
            names,
            egg,
            out: Lifting::new(SlottedProofStore::new(dag).with_slot_names(&program.slot_names)),
            dec_memo: HashMap::default(),
            edge_memo: HashMap::default(),
            eq_memo: HashMap::default(),
            known: HashMap::default(),
            shape_terms: HashMap::default(),
            free_vars_index: None,
            group_index: None,
            cert_stack: Default::default(),
            fresh,
            reserved_terms,
        }
    }

    fn egg(&self) -> &'a TermDag {
        self.egg.term_dag()
    }

    fn fresh(&mut self) -> i64 {
        // Binder normalization and rule instantiation can introduce more names
        // between allocations. Each newly interned term is visited only once.
        let dag = &self.out.term_dag;
        self.fresh
            .reserve((self.reserved_terms..dag.size()).filter_map(|t| slot_of(dag, t)));
        self.reserved_terms = dag.size();
        self.fresh.fresh()
    }

    fn egg_string(&self, t: TermId) -> String {
        self.egg().to_string(t)
    }

    fn out_string(&self, t: TermId) -> String {
        self.out.term_dag.to_string(t)
    }

    fn prop_string(&self, p: LiftedId) -> String {
        self.out.proposition_to_string(self.out.proposition(p))
    }

    fn app(&self, t: TermId) -> Option<(&'a str, &'a [TermId])> {
        match self.egg().get(t) {
            Term::App(head, args) => Some((head.as_str(), args.as_slice())),
            _ => None,
        }
    }

    fn is_carrier_term(&self, t: TermId) -> bool {
        self.app(t).is_some_and(|(head, _)| {
            self.program.constructors.contains_key(head) || self.names.is_var_constructor(head)
        })
    }

    fn slot_map(&self, t: TermId) -> R<SlotMap> {
        renaming_from_term(self.egg(), t)
            .ok_or_else(|| format!("not a renaming: {}", self.egg_string(t)))
    }

    fn group(&self, t: TermId) -> R<Vec<SlotMap>> {
        group_from_term(self.egg(), t).ok_or_else(|| format!("not a group: {}", self.egg_string(t)))
    }

    /// The group a row's second column holds, naming the row on failure.
    fn group_of_row(&self, row: TermId) -> R<Vec<SlotMap>> {
        let (_, args) = self.app(row).ok_or("not a row")?;
        args.get(1)
            .and_then(|group| group_from_term(self.egg(), *group))
            .ok_or_else(|| format!("row {} holds no group", self.egg_string(row)))
    }

    fn sub(&self, subst: &IndexMap<String, TermId>, var: &str) -> R<TermId> {
        subst
            .get(var)
            .copied()
            .ok_or_else(|| format!("rule substitution has no {var}"))
    }

    // ----- decoding -----------------------------------------------------------

    /// The permutation completing an edge: a slot of the child outside the edge's
    /// domain -- bound, or one the child's class does not depend on -- gets a
    /// fresh name, so that it collides with nothing the parent names.
    fn complete(&mut self, m: &SlotMap, child: TermId) -> Renaming {
        let slots = all_slots(&self.out.term_dag, child);
        self.fresh.reserve(m.iter().flat_map(|(k, v)| [*k, *v]));
        let mut entries: Vec<(i64, i64)> = m.iter().map(|(k, v)| (*k, *v)).collect();
        for s in slots {
            if !m.contains_key(&s) {
                let f = self.fresh();
                entries.push((s, f));
            }
        }
        Renaming::completing(entries).expect("an edge's renaming is injective")
    }

    /// The surface term an encoded carrier term denotes.
    fn dec(&mut self, t: TermId) -> R<TermId> {
        if let Some(&d) = self.dec_memo.get(&t) {
            return Ok(d);
        }
        let (head, args) = self
            .app(t)
            .ok_or_else(|| format!("not an encoded carrier term: {}", self.egg_string(t)))?;
        let out = if self.names.is_var_constructor(head) {
            let slot = match self.egg().get(args[0]) {
                Term::Lit(Literal::Int(n)) => *n,
                _ => return Err(format!("variable without a slot: {}", self.egg_string(t))),
            };
            slot_term(&mut self.out.term_dag, slot)
        } else if self.program.constructors.contains_key(head) {
            let head = head.to_string();
            self.build_node(&head, args, None, Some(t))?
        } else {
            return Err(format!(
                "not an encoded carrier term: {}",
                self.egg_string(t)
            ));
        };
        log::debug!("dec {} = {}", self.egg_string(t), self.out_string(out));
        self.dec_memo.insert(t, out);
        Ok(out)
    }

    /// A node's surface term from its constructor's columns: each slotted column
    /// is the child's term under the column's edge completed to a permutation,
    /// and each of the node's own bound slots is named apart. `edges` overrides
    /// the edges the row carries; the completions are recorded under `memo_for`.
    fn build_node(
        &mut self,
        head: &str,
        args: &[TermId],
        edges: Option<&[SlotMap]>,
        memo_for: Option<TermId>,
    ) -> R<TermId> {
        let columns = self
            .program
            .constructors
            .get(head)
            .ok_or_else(|| format!("unknown constructor {head}"))?
            .columns
            .clone();
        let mut children = Vec::with_capacity(columns.len());
        let mut i = 0;
        let mut k = 0;
        // the node's own bound slots, named apart: (column, node slot, new name)
        let mut pending: Vec<(usize, i64, i64)> = vec![];
        for (j, col) in columns.iter().enumerate() {
            match col {
                ColumnKind::Binder => {
                    let m = match edges {
                        Some(e) => e[k].clone(),
                        None => self.slot_map(*args.get(i).ok_or("short row")?)?,
                    };
                    let slot = *m.get(&0).ok_or("a binder column without its slot")?;
                    let b = self.fresh();
                    pending.push((j, slot, b));
                    children.push(slot_term(&mut self.out.term_dag, b));
                    if let Some(t) = memo_for {
                        self.edge_memo
                            .insert((t, j), Renaming::new([(0, b), (b, 0)]).unwrap());
                    }
                    i += 2;
                    k += 1;
                }
                ColumnKind::Child => {
                    let m = match edges {
                        Some(e) => e[k].clone(),
                        None => self.slot_map(*args.get(i).ok_or("short row")?)?,
                    };
                    let class = *args.get(i + 1).ok_or("short row")?;
                    let child = self.dec(class)?;
                    let mut completion = self.complete(&m, child);
                    // the binders this column is under, innermost first
                    for (_, slot, b) in pending.drain(..).rev() {
                        let swap = Renaming::new([(slot, b), (b, slot)]).unwrap();
                        completion = swap.compose(&completion);
                    }
                    let renamed = rename(&mut self.out.term_dag, &completion, child);
                    if let Some(t) = memo_for {
                        self.edge_memo.insert((t, j), completion);
                    }
                    children.push(renamed);
                    i += 2;
                    k += 1;
                }
                ColumnKind::Payload => {
                    let lit = match self.egg().get(args[i]) {
                        Term::Lit(l) => l.clone(),
                        _ => return Err(format!("payload is not a literal in {head}")),
                    };
                    children.push(self.out.term_dag.lit(lit));
                    i += 1;
                }
            }
        }
        Ok(self.out.term_dag.app(head.to_string(), children))
    }

    /// Surface column index of an encoded row's physical child index.
    fn surface_column(&self, head: &str, physical: usize) -> R<usize> {
        let ctor = self
            .program
            .constructors
            .get(head)
            .ok_or_else(|| format!("unknown constructor {head}"))?;
        let mut i = 0;
        for (j, col) in ctor.columns.iter().enumerate() {
            let width = match col {
                ColumnKind::Child | ColumnKind::Binder => 2,
                ColumnKind::Payload => 1,
            };
            if physical == i + width - 1 && width == 2 {
                return Ok(j);
            }
            if physical < i + width {
                return Err(format!(
                    "physical column {physical} of {head} is not a class column"
                ));
            }
            i += width;
        }
        Err(format!(
            "physical column {physical} out of range for {head}"
        ))
    }

    // ----- proof algebra --------------------------------------------------------

    /// Record that `proof` proves `lhs = …`, so `lhs`'s reflexivity is available.
    fn note(&mut self, proof: LiftedId) -> LiftedId {
        let p = self.out.proposition(proof).clone();
        self.known.entry(p.lhs).or_insert(proof);
        if p.rhs != p.lhs {
            let s = self.out.sym(proof);
            self.known.entry(p.rhs).or_insert(s);
        }
        proof
    }

    /// `t = t`: by fiat for a term the program built, else from any proof
    /// stating something about it.
    fn reflexive(&mut self, t: TermId) -> R<LiftedId> {
        if self.program.is_built(&self.out.term_dag, t) {
            return Ok(self.out.fiat(t, t));
        }
        if let Some(&p) = self.known.get(&t) {
            let s = self.out.sym(p);
            return self.out.trans(p, s).map_err(|e| e.0);
        }
        // a term the same as a built or known one up to a renaming of its slots:
        // its reflexivity follows by equivariance of the known equality
        let candidates: Vec<TermId> = self
            .program
            .built_terms(&self.out.term_dag)
            .into_iter()
            .chain(self.known.keys().copied())
            .collect();
        for other in candidates {
            let mut pairs = BTreeMap::new();
            if other == t || self.unify_slots(other, t, &mut pairs).is_err() {
                continue;
            }
            let Some(sigma) = Renaming::completing(pairs.iter().map(|(k, v)| (*k, *v))) else {
                continue;
            };
            let r = self.reflexive(other)?; // other = other
            let reframed = self.out.reframe(r, sigma); // other = σ⁻¹·t
            let s = self.out.sym(reframed); // t = σ·other
            let back = self.out.trans(s, reframed).map_err(|e| e.0)?; // t = t
            return Ok(self.note(back));
        }
        Err(format!(
            "no proof establishes the term {}",
            self.out_string(t)
        ))
    }

    /// Establish a class from the carrier equalities in a premise's derivation.
    fn establish(&mut self, class: TermId, premise: ProofId) -> R<LiftedId> {
        let term = self.dec(class)?;
        let mut pending = vec![premise];
        let mut seen = HashSet::default();
        while let Some(id) = pending.pop() {
            if !seen.insert(id) {
                continue;
            }
            let proof = self.egg.get(id);
            if (proof.lhs() == class || proof.rhs() == class)
                && self.eq(id).is_ok()
                && let Ok(proof) = self.reflexive(term)
            {
                return Ok(proof);
            }
            match proof.justification() {
                Justification::Rule { premise_proofs, .. } => pending.extend(premise_proofs),
                Justification::MergeFn {
                    old_proof,
                    new_proof,
                    ..
                } => pending.extend([*old_proof, *new_proof]),
                Justification::Trans(a, b) => pending.extend([*a, *b]),
                Justification::Congr {
                    proof, child_proof, ..
                } => pending.extend([*proof, *child_proof]),
                Justification::Sym(proof)
                | Justification::Proj { proof, .. }
                | Justification::ContainerNormalize { proof } => pending.push(*proof),
                Justification::Fiat | Justification::Eval => {}
            }
        }
        self.reflexive(term)
    }

    fn trans(&mut self, p: LiftedId, q: LiftedId) -> R<LiftedId> {
        let r = self.out.trans(p, q).map_err(|e| e.0)?;
        Ok(self.note(r))
    }

    /// `σ·t1 = (σ∘m)·t2` from `t1 = m·t2`.
    fn rename_both(&mut self, p: LiftedId, sigma: &Renaming) -> LiftedId {
        if sigma.is_identity() {
            return p;
        }
        let r = self.out.equivariance(p, sigma);
        self.note(r)
    }

    /// Reframe `p`'s right-hand side onto `target`, which must be the same term up
    /// to a bijection of slot names.
    fn align(&mut self, p: LiftedId, target: TermId) -> R<LiftedId> {
        let rhs = self.out.proposition(p).rhs;
        if rhs == target {
            return Ok(p);
        }
        let mut pairs: BTreeMap<i64, i64> = BTreeMap::new();
        self.unify_slots(rhs, target, &mut pairs).map_err(|e| {
            format!(
                "aligning {} with {}: {e}",
                self.out_string(rhs),
                self.out_string(target)
            )
        })?;
        let sigma = Renaming::completing(pairs.iter().map(|(k, v)| (*k, *v))).ok_or_else(|| {
            format!(
                "aligning {} with {} needs a non-bijective renaming {pairs:?}",
                self.out_string(rhs),
                self.out_string(target)
            )
        })?;
        let r = self.out.reframe(p, sigma);
        let got = self.out.proposition(r).rhs;
        if got != target {
            return Err(format!(
                "alignment of {} with {} produced {}",
                self.out_string(rhs),
                self.out_string(target),
                self.out_string(got)
            ));
        }
        Ok(self.note(r))
    }

    fn unify_slots(&self, a: TermId, b: TermId, pairs: &mut BTreeMap<i64, i64>) -> R<()> {
        let dag = &self.out.term_dag;
        match (dag.get(a).clone(), dag.get(b).clone()) {
            (Term::Var(x), Term::Var(y)) => {
                let (sa, sb) = (super::terms::slot_of(dag, a), super::terms::slot_of(dag, b));
                match (sa, sb) {
                    (Some(sa), Some(sb)) => match pairs.get(&sa) {
                        Some(&prev) if prev != sb => Err(format!(
                            "slot ${sa} would have to be both ${prev} and ${sb}"
                        )),
                        _ => {
                            pairs.insert(sa, sb);
                            Ok(())
                        }
                    },
                    _ if x == y => Ok(()),
                    _ => Err(format!("cannot align {x} with {y}")),
                }
            }
            (Term::Lit(x), Term::Lit(y)) if x == y => Ok(()),
            (Term::App(h1, c1), Term::App(h2, c2)) if h1 == h2 && c1.len() == c2.len() => {
                for (x, y) in c1.iter().zip(c2.iter()) {
                    self.unify_slots(*x, *y, pairs)?;
                }
                Ok(())
            }
            _ => Err(format!(
                "cannot align {} with {}",
                self.out_string(a),
                self.out_string(b)
            )),
        }
    }

    // ----- translating egglog proofs ---------------------------------------------

    /// The slotted proof of the equality an egglog proof denotes: for a carrier
    /// equality, that equality; for a row, the equality the row as the consumer
    /// reads it (its right-hand side) denotes.
    fn eq(&mut self, id: ProofId) -> R<LiftedId> {
        if let Some(&p) = self.eq_memo.get(&id) {
            return Ok(p);
        }
        let proof = self.egg.get(id).clone();
        let result = if self.is_carrier_term(proof.lhs()) {
            self.eq_direct(id)?
        } else {
            self.row_eq(id, true)?
        };
        self.eq_memo.insert(id, result);
        Ok(result)
    }

    /// The equality an egglog proof denotes, by its justification.
    fn eq_direct(&mut self, id: ProofId) -> R<LiftedId> {
        let proof = self.egg.get(id).clone();
        let (lhs, rhs) = (proof.lhs(), proof.rhs());
        let result = match proof.justification() {
            Justification::Fiat => {
                if lhs == rhs {
                    if self.is_carrier_term(lhs) {
                        let t = self.dec(lhs)?;
                        self.reflexive(t)?
                    } else {
                        self.row_fiat(lhs)?
                    }
                } else {
                    let (l, r) = (self.dec(lhs)?, self.dec(rhs)?);
                    self.source_union(l, &Renaming::identity(), r)?
                }
            }
            Justification::Sym(p) => {
                let q = self.eq(*p)?;
                let s = self.out.sym(q);
                self.note(s)
            }
            Justification::Trans(p, q) => {
                let (a, b) = (self.eq(*p)?, self.eq(*q)?);
                self.trans(a, b)?
            }
            Justification::Congr {
                proof,
                child_index,
                child_proof,
            } => self
                .congr(*proof, *child_index, *child_proof, rhs)
                .map_err(|e| format!("in a congruence at {child_index}: {e}"))?,
            Justification::Proj { proof, .. } => {
                // Reuse an established surface term, translating the parent if needed.
                let term = self.dec(lhs)?;
                self.reflexive(term).or_else(|_| {
                    self.eq(*proof)?;
                    self.reflexive(term)
                })?
            }
            Justification::Rule {
                name,
                premise_proofs,
                substitution,
            } => {
                let name = name.clone();
                let prems = premise_proofs.clone();
                let subst = substitution.clone();
                if lhs == rhs
                    && self.is_carrier_term(lhs)
                    && let Ok(t) = self.dec(lhs)
                    && let Ok(r) = self.reflexive(t)
                {
                    // a term the rule built that is already at hand
                    return Ok(r);
                }
                let r = self
                    .rule(&name, &prems, &subst, lhs, rhs)
                    .map_err(|e| format!("in rule {:?}: {e}", name.lines().next().unwrap_or("")))?;
                if lhs == rhs && self.is_carrier_term(lhs) {
                    // the term the rule built equals itself
                    self.orient(r, lhs, rhs)?
                } else {
                    r
                }
            }
            Justification::MergeFn { function, .. } => {
                return Err(format!("merge of {function} does not denote an equality"));
            }
            Justification::ContainerNormalize { .. } | Justification::Eval => {
                return Err(format!(
                    "proof {id} ({}) does not denote an equality",
                    self.egg_string(lhs)
                ));
            }
        };
        Ok(result)
    }

    /// A row stated at the top level.
    fn row_fiat(&mut self, row: TermId) -> R<LiftedId> {
        let (head, args) = self.app(row).ok_or("not a row")?;
        match row_kind(head) {
            RowKind::Edge => {
                let (a, b) = (self.dec(args[0])?, self.dec(args[2])?);
                let m = self.slot_map(args[1])?;
                let completion = self.complete(&m, b);
                if a == b && completion.is_identity() {
                    self.reflexive(a)
                } else {
                    self.source_union(a, &completion, b)
                }
            }
            _ => Err(format!(
                "top-level row {} denotes no equality",
                self.egg_string(row)
            )),
        }
    }

    /// Decoding gives binders fresh names, independently of the source reader.
    /// Only the recorded source union is Fiat; transport it to the decoded
    /// spellings using the proof algebra, keeping the source's free slots fixed.
    fn source_union(&mut self, lhs: TermId, m: &Renaming, rhs: TermId) -> R<LiftedId> {
        let target = rename(&mut self.out.term_dag, m, rhs);
        for u in &self.program.unions {
            for (a, b) in [(u.lhs, u.rhs), (u.rhs, u.lhs)] {
                let mut left = BTreeMap::new();
                let mut right = BTreeMap::new();
                if self.unify_slots(a, lhs, &mut left).is_err()
                    || self.unify_slots(b, target, &mut right).is_err()
                    || self
                        .program
                        .free_slots(&self.out.term_dag, a)
                        .iter()
                        .any(|s| left.get(s) != Some(s))
                    || self
                        .program
                        .free_slots(&self.out.term_dag, b)
                        .iter()
                        .any(|s| right.get(s) != Some(s))
                {
                    continue;
                }
                let Some(rho) = Renaming::completing(left) else {
                    continue;
                };
                let p = self.out.fiat(a, b);
                let p = self.rename_both(p, &rho);
                return self.align(p, rhs);
            }
        }
        Err(format!(
            "no source union establishes {} = {m}·{}",
            self.out_string(lhs),
            self.out_string(rhs)
        ))
    }

    /// The equality a row denotes, from a proof of the row: `(a, m, b)` as
    /// surface terms with the completed renaming.
    fn row_sides(&mut self, row: TermId) -> R<(TermId, SlotMap, TermId)> {
        let (head, args) = self.app(row).ok_or("not a row")?;
        match row_kind(head) {
            RowKind::Edge => Ok((args[0], self.slot_map(args[1])?, args[2])),
            RowKind::Invocation => Ok((args[2], self.slot_map(args[1])?, args[0])),
            RowKind::Other => Err(format!("row {} denotes no equality", self.egg_string(row))),
        }
    }

    fn congr(
        &mut self,
        proof: ProofId,
        child_index: usize,
        child_proof: ProofId,
        conclusion_rhs: TermId,
    ) -> R<LiftedId> {
        let base = self.egg.get(proof).clone();
        let base_rhs = base.rhs();
        if self.is_carrier_term(base_rhs) {
            // `t1 = F(.., c, ..)` and `c = c'`: congruence at the surface column.
            let p = self.eq(proof)?;
            let (head, _) = self.app(base_rhs).ok_or("congr on a non-application")?;
            let j = self.surface_column(head, child_index)?;
            let completion = self.edge_memo.get(&(base_rhs, j)).cloned().ok_or_else(|| {
                format!(
                    "no decoded edge for column {j} of {}",
                    self.egg_string(base_rhs)
                )
            })?;
            let c = self.eq(child_proof)?;
            let renamed = self.rename_both(c, &completion);
            let r = self.out.congr(p, j, renamed).map_err(|e| e.0)?;
            let target = self.dec(conclusion_rhs)?;
            let aligned = self.align(r, target)?;
            // A congruence whose base is reflexive may be read in either
            // direction later; both endpoints are now known.
            Ok(self.note(aligned))
        } else {
            // A row re-keyed by a union: the same statement about an equal term.
            let old = self.eq(proof)?;
            let (head, args) = self.app(base_rhs).ok_or("congr on a non-row")?;
            // the child proof relates the column's old class with the new, in
            // whichever direction the union-find stated it
            let c = self.eq(child_proof)?;
            let old_col = self.dec(args[child_index])?;
            let c = if self.out.proposition(c).lhs == old_col {
                c
            } else {
                let s = self.out.sym(c);
                self.note(s)
            };
            let kind = row_kind(head);
            let (lhs_col, rhs_col) = match kind {
                RowKind::Edge => (0, 2),
                RowKind::Invocation => (2, 0),
                RowKind::Other => {
                    return Err(format!(
                        "congruence on a row that denotes no equality: {}",
                        self.egg_string(base_rhs)
                    ));
                }
            };
            let _ = args;
            let context = |this: &Self, e: String| {
                format!(
                    "re-keying {} at {child_index} by {}: {e}",
                    this.egg_string(base_rhs),
                    this.prop_string(c)
                )
            };
            if child_index == lhs_col {
                let s = self.out.sym(c);
                self.trans(s, old).map_err(|e| context(self, e))
            } else if child_index == rhs_col {
                self.trans(old, c).map_err(|e| context(self, e))
            } else {
                Err(format!(
                    "congruence on the renaming column of {}",
                    self.egg_string(base_rhs)
                ))
            }
        }
    }

    /// The equality a rule firing concludes, by the rule.
    fn rule(
        &mut self,
        name: &str,
        prems: &[ProofId],
        subst: &IndexMap<String, TermId>,
        lhs: TermId,
        rhs: TermId,
    ) -> R<LiftedId> {
        let (owner, kind) = rule_kind(self.program, name);
        match (owner, kind) {
            ("slotted", "orient-max") => self.eq(prems[0]),
            ("slotted", "orient-min") => {
                let p = self.eq(prems[0])?;
                let s = self.out.sym(p);
                Ok(self.note(s))
            }
            ("slotted", "seed-identity") => {
                let c = self.sub(subst, "_c")?;
                let t = self.dec(c)?;
                self.reflexive(t).or_else(|_| self.establish(c, prems[0]))
            }
            ("slotted", "transitivity") => {
                let (p, q) = (self.eq(prems[0])?, self.eq(prems[1])?);
                self.trans(p, q)
            }
            ("slotted", "one-leader") => {
                let (p, q) = (self.eq(prems[0])?, self.eq(prems[1])?);
                let s = self.out.sym(p);
                self.trans(s, q)
            }
            ("slotted", "restate-edge")
            | ("slotted", "shape-equal")
            | ("slotted", "binder-strip") => self.eq(prems[0]),
            ("slotted", "binder-refresh") => {
                // the node rebuilt with its bound slot renamed: the same term up to
                // the names of its binders
                let node = self.eq(prems[0])?; // node = row
                let node_egg = self.sub(subst, "_node")?;
                self.finish_union(node, lhs, rhs, node_egg)
            }
            ("slotted", "var-normalize") => {
                // `e = (Var v)` becomes `e = {0->v}·$0`.
                let p = self.eq(prems[0])?;
                let v = self.out.proposition(p).rhs;
                let slot = super::terms::slot_of(&self.out.term_dag, v)
                    .ok_or("var-normalize on a non-variable")?;
                if slot == 0 {
                    return Ok(p);
                }
                let sigma = Renaming::new([(slot, 0), (0, slot)]).unwrap();
                let r = self.out.reframe(p, sigma);
                Ok(self.note(r))
            }
            ("slotted", "invocation") => {
                // `a = m·c` and `name = m∘g`: `a = name·c` through the symmetry g.
                let p = self.eq(prems[0])?;
                let (m, c, name) = (
                    self.slot_map(self.sub(subst, "_m")?)?,
                    self.sub(subst, "_c")?,
                    self.slot_map(self.sub(subst, "_name")?)?,
                );
                let grp = self.group(self.sub(subst, "_grp")?)?;
                let g = grp
                    .iter()
                    .find(|g| compose(&m, g) == name)
                    .cloned()
                    .ok_or("coset-min's element is not in the group")?;
                if is_identity(&g) {
                    return Ok(p);
                }
                let s = self.symmetry(c, &g, prems[1])?;
                self.trans(p, s)
            }
            ("slotted", "invocation-merge") => {
                let (pa, pb) = (self.eq(prems[0])?, self.eq(prems[1])?);
                let s = self.out.sym(pb);
                let r = self.trans(pa, s)?;
                self.orient(r, lhs, rhs)
            }
            ("slotted", "shape-collision") => {
                let r = self.shape_collision(prems, subst)?;
                Ok(r)
            }
            ("slotted", "shape-dedup") => {
                let r = self.shape_dedup(prems, subst)?;
                Ok(r)
            }
            ("slotted", "migration") => {
                let edge = self.eq(prems[0])?; // e2 = m·e1
                let row = self.eq(prems[1])?; // e2 = row
                let s = self.out.sym(edge); // e1 = m⁻¹·e2
                let p = self.trans(s, row)?; // e1 = ·row
                let e1 = self.sub(subst, "_e1")?;
                self.finish_union(p, lhs, rhs, e1)
            }
            ("slotted", "child-update") => {
                let edge = self.eq(prems[0])?; // c = m·c'
                let node = self.eq(prems[1])?; // node = row
                let j: usize = name
                    .rsplit('/')
                    .next()
                    .and_then(|s| s.parse().ok())
                    .ok_or("child-update without a column")?;
                let row = self.out.proposition(node).rhs;
                let row_egg = self.egg.get(prems[1]).rhs();
                let completion = self.edge_memo.get(&(row_egg, j)).cloned().ok_or_else(|| {
                    format!("no decoded edge for column {j} of {}", self.out_string(row))
                })?;
                let renamed = self.rename_both(edge, &completion);
                let r = self.out.congr(node, j, renamed).map_err(|e| e.0)?;
                let r = self.note(r);
                let node_egg = self.sub(subst, "_node")?;
                self.finish_union(r, lhs, rhs, node_egg)
            }
            (user, "apply") => self.apply_rule(user, prems, subst, lhs, rhs),
            _ => Err(format!("no translation for rule {name:?}")),
        }
    }

    /// `p: origin = ·X` where the egglog step relates `origin` with the term it
    /// built, or states the built term's own reflexivity: align `X` with the
    /// built term's surface form and turn the proof the way the step states it.
    fn finish_union(
        &mut self,
        p: LiftedId,
        lhs: TermId,
        rhs: TermId,
        origin: TermId,
    ) -> R<LiftedId> {
        let built = if lhs == rhs {
            lhs
        } else if lhs == origin {
            rhs
        } else if rhs == origin {
            lhs
        } else {
            return Err(format!(
                "the step relates {} and {}, neither of which is its origin {}",
                self.egg_string(lhs),
                self.egg_string(rhs),
                self.egg_string(origin)
            ));
        };
        let target = self.dec(built)?;
        let occ = self.row_occurrences(built)?;
        let p = self.fit(p, target, &occ)?;
        self.orient(p, lhs, rhs)
    }

    /// The occurrences of an encoded row: itself, and each slotted column's class.
    fn row_occurrences(&self, row: TermId) -> R<HashMap<Vec<usize>, Occurrence>> {
        let mut occ: HashMap<Vec<usize>, Occurrence> = HashMap::default();
        occ.insert(
            vec![],
            Occurrence {
                cls: row,
                row: None,
            },
        );
        let (head, args) = self.app(row).ok_or("not a row")?;
        if let Some(ctor) = self.program.constructors.get(head) {
            let mut i = 0;
            for (j, col) in ctor.columns.iter().enumerate() {
                match col {
                    ColumnKind::Child => {
                        occ.insert(
                            vec![j],
                            Occurrence {
                                cls: args[i + 1],
                                row: None,
                            },
                        );
                        i += 2;
                    }
                    ColumnKind::Binder => i += 2,
                    ColumnKind::Payload => i += 1,
                }
            }
        }
        Ok(occ)
    }

    /// Turn `p` (an equality between the surface forms of the egglog proof's
    /// two sides, in some direction) around to match the egglog proposition.
    fn orient(&mut self, p: LiftedId, lhs: TermId, rhs: TermId) -> R<LiftedId> {
        let (l, r) = (self.dec(lhs)?, self.dec(rhs)?);
        let prop = self.out.proposition(p).clone();
        if l == r {
            // the step's own conclusion: the term it built equals itself
            if prop.lhs == l {
                let s = self.out.sym(p);
                return self.trans(p, s);
            }
            if prop.rhs == l {
                let s = self.out.sym(p);
                return self.trans(s, p);
            }
        }
        if prop.lhs == l {
            Ok(p)
        } else if prop.lhs == r && prop.rhs == l {
            let s = self.out.sym(p);
            Ok(self.note(s))
        } else {
            Err(format!(
                "derived {} where the egglog step relates {} and {}",
                self.prop_string(p),
                self.out_string(l),
                self.out_string(r)
            ))
        }
    }

    // ----- shapes and symmetries --------------------------------------------------

    /// `dec(row) = back·N` where `N` is the row's node spelled with its canonical
    /// edges: the readings `g_i` of the children that make the edges canonical,
    /// applied by congruence, then the renaming back.
    fn shape_form(
        &mut self,
        row_eq: LiftedId,
        row: TermId,
        groups: &[(TermId, ProofId)],
    ) -> R<(LiftedId, TermId)> {
        let (head, args) = self.app(row).ok_or("not a row")?;
        let head = head.to_string();
        let ctor = self
            .program
            .constructors
            .get(&head)
            .ok_or("unknown constructor")?
            .clone();
        // the edges and classes of the slotted columns, and the payloads
        let mut edges: Vec<SlotMap> = vec![];
        let mut classes: Vec<TermId> = vec![];
        let mut payloads: Vec<TermId> = vec![];
        let mut i = 0;
        for col in &ctor.columns {
            match col {
                ColumnKind::Child | ColumnKind::Binder => {
                    edges.push(self.slot_map(args[i])?);
                    classes.push(args[i + 1]);
                    i += 2;
                }
                ColumnKind::Payload => {
                    payloads.push(args[i]);
                    i += 1;
                }
            }
        }
        let group_values: Vec<Vec<SlotMap>> = groups
            .iter()
            .map(|(g, _)| self.group(*g))
            .collect::<R<_>>()?;
        let own = shape(&edges);
        // the least reading over the children's groups, as node-shape computes it
        let mut best: Option<(Vec<SlotMap>, Vec<SlotMap>)> = None;
        for variant in readings(&edges, &group_values) {
            let spelled = shape(&variant.0);
            if best.as_ref().is_none_or(|b| spelled.edges < b.0) {
                best = Some((spelled.edges, variant.1));
            }
        }
        let (canonical_edges, gs) = best.unwrap_or((own.edges.clone(), vec![]));
        let _ = own;
        // apply each child's reading by congruence: child j: m̂_j·dec(c_j) = (m̂_j∘ĝ_j)·dec(c_j)
        let mut p = row_eq;
        let mut slotted_j = 0;
        for (j, col) in ctor.columns.iter().enumerate() {
            if matches!(col, ColumnKind::Payload) {
                continue;
            }
            let k = slotted_j;
            slotted_j += 1;
            let g = match gs.get(k) {
                Some(g) if !is_identity(g) => g.clone(),
                _ => continue,
            };
            let (gterm, gproof) = groups[k];
            let _ = gterm;
            let s = self.symmetry(classes[k], &g, gproof)?;
            let completion = self.edge_memo[&(row, j)].clone();
            let renamed = self.rename_both(s, &completion);
            p = self.out.congr(p, j, renamed).map_err(|e| e.0)?;
            p = self.note(p);
        }
        // the shape node: canonical edges over the same children
        let key = (
            head.clone(),
            canonical_edges.clone(),
            classes.clone(),
            payloads,
        );
        let node = if let Some(&n) = self.shape_terms.get(&key) {
            n
        } else {
            let n = self.build_node(&head, args, Some(&canonical_edges), None)?;
            self.shape_terms.insert(key, n);
            n
        };
        // `p` now ends in the row spelled through the readings; align its coordinates with the shape node
        let aligned = self.align(p, node)?;
        Ok((aligned, node))
    }

    /// Two rows meeting on one shape: `c = (back∘back0⁻¹)·c0`.
    fn shape_collision(
        &mut self,
        prems: &[ProofId],
        subst: &IndexMap<String, TermId>,
    ) -> R<LiftedId> {
        // premises: c = row, g1.., shapeof-edges row, (vec-get facts), c0 = shape-class row, back0 row, guard
        let row_eq = self.eq(prems[0])?;
        let row = self.egg.get(prems[0]).rhs();
        let classes = self.slotted_classes(row)?;
        let groups: Vec<(TermId, ProofId)> = classes
            .iter()
            .enumerate()
            .map(|(k, &class)| {
                let g = self.sub(subst, &format!("_g{}", k + 1))?;
                Ok((g, self.group_premise(prems, class)?))
            })
            .collect::<R<_>>()?;
        let (to_shape, node) = self.shape_form(row_eq, row, &groups)?;
        // the stored class: through the proof of the `_shape_class` row
        let class_row_proof = prems
            .iter()
            .copied()
            .find(|p| {
                let t = self.egg.get(*p).lhs();
                self.app(t)
                    .is_some_and(|(h, _)| h.starts_with("_shape_class_"))
            })
            .ok_or("shape-collision without its class row")?;
        let (c0_eq, c0_row, c0_groups) = self.shape_entry(class_row_proof)?;
        if c0_row == row && self.sub(subst, "_c")? == self.sub(subst, "_c0")? {
            // the row met its own entry under another reading: a symmetry of its class
            let c = self.sub(subst, "_c")?;
            let back = self.slot_map(self.sub(subst, "_back")?)?;
            let back0 = self.slot_map(self.sub(subst, "_back0")?)?;
            let g = compose(&back, &inverse(&back0));
            return self.node_symmetry(row_eq, row, &groups, c, &g);
        }
        let (to_shape0, node0) = self.shape_form(c0_eq, c0_row, &c0_groups)?;
        if node0 != node {
            return Err(format!(
                "shape collision on different nodes {} and {}",
                self.out_string(node),
                self.out_string(node0)
            ));
        }
        let s = self.out.sym(to_shape0);
        self.trans(to_shape, s)
    }

    /// Two rows of one class with one shape: the symmetry between them.
    fn shape_dedup(&mut self, prems: &[ProofId], subst: &IndexMap<String, TermId>) -> R<LiftedId> {
        let row1_eq = self.eq(prems[0])?;
        let row1 = self.egg.get(prems[0]).rhs();
        let n = self.slotted_columns(row1)?;
        let classes = self.slotted_classes(row1)?;
        let groups: Vec<(TermId, ProofId)> = classes
            .iter()
            .enumerate()
            .map(|(k, &class)| {
                Ok((
                    self.sub(subst, &format!("_g{}", k + 1))?,
                    self.group_premise(prems, class)?,
                ))
            })
            .collect::<R<_>>()?;
        // the second row's premise is the one after the first shapeof row
        let row2_prem = prems[1 + n + 1];
        let row2_eq = self.eq(row2_prem)?;
        let row2 = self.egg.get(row2_prem).rhs();
        let (a, node) = self.shape_form(row1_eq, row1, &groups)?;
        let (b, node2) = self.shape_form(row2_eq, row2, &groups)?;
        if node != node2 {
            return Err("dedup rows have different shapes".into());
        }
        let s = self.out.sym(b);
        self.trans(a, s)
    }

    fn slotted_columns(&self, row: TermId) -> R<usize> {
        let (head, _) = self.app(row).ok_or("not a row")?;
        let ctor = self
            .program
            .constructors
            .get(head)
            .ok_or("unknown constructor")?;
        Ok(ctor
            .columns
            .iter()
            .filter(|c| !matches!(c, ColumnKind::Payload))
            .count())
    }

    /// Through the proof of a `_shape_class_F` row: the stored class's row
    /// equality, the row, and the group rows its index firing read.
    fn shape_entry(&mut self, proof: ProofId) -> R<(LiftedId, TermId, SymmetryPremises)> {
        let p = self.egg.get(proof).clone();
        match p.justification() {
            Justification::Rule {
                name,
                premise_proofs,
                substitution,
            } if rule_kind(self.program, name).1 == "shape-index" => {
                let row_eq = self.eq(premise_proofs[0])?;
                let row = self.egg.get(premise_proofs[0]).rhs();
                let classes = self.slotted_classes(row)?;
                let groups = classes
                    .iter()
                    .enumerate()
                    .map(|(k, &class)| {
                        Ok((
                            self.sub(substitution, &format!("_g{}", k + 1))?,
                            self.group_premise(premise_proofs, class)?,
                        ))
                    })
                    .collect::<R<_>>()?;
                Ok((row_eq, row, groups))
            }
            Justification::MergeFn { old_proof, .. } => self.shape_entry(*old_proof),
            Justification::Congr {
                proof,
                child_index,
                child_proof,
            } => {
                // the stored class moved: c0 = c0', so the entry's row equality is
                // restated from the new class
                let (row_eq, row, groups) = self.shape_entry(*proof)?;
                let (head, args) = self.app(p.lhs()).ok_or("not a row")?;
                let _ = head;
                if *child_index == args.len() - 1 {
                    let c = self.eq(*child_proof)?;
                    let s = self.out.sym(c);
                    let r = self.trans(s, row_eq)?;
                    Ok((r, row, groups))
                } else {
                    // a child class column of the key moved; the row itself is unchanged
                    Ok((row_eq, row, groups))
                }
            }
            Justification::Trans(a, b) => {
                let _ = b;
                self.shape_entry(*a)
            }
            Justification::Sym(a) => self.shape_entry(*a),
            other => Err(format!("unexpected shape entry provenance {other:?}")),
        }
    }

    /// `dec(c) = g·dec(c)` for an element `g` of `c`'s group, through the proof
    /// of the group row.
    fn symmetry(&mut self, c: TermId, g: &SlotMap, grp_proof: ProofId) -> R<LiftedId> {
        self.symmetry_inner(c, g, grp_proof).map_err(|e| {
            format!(
                "symmetry {} of {} through {}: {e}",
                slot_map_string(g),
                self.egg_string(c),
                self.egg_string(self.egg.get(grp_proof).lhs())
            )
        })
    }

    fn symmetry_inner(&mut self, c: TermId, g: &SlotMap, grp_proof: ProofId) -> R<LiftedId> {
        if is_identity(g) {
            let t = self.dec(c)?;
            return self.reflexive(t);
        }
        let proof = self.egg.get(grp_proof).clone();
        match proof.justification() {
            Justification::Rule {
                name,
                premise_proofs,
                substitution,
            } => {
                let name = name.clone();
                let prems = premise_proofs.clone();
                let subst = substitution.clone();
                match rule_kind(self.program, &name).1 {
                    "seed-identity" => Err(format!("{} is not the identity", slot_map_string(g))),
                    "self-symmetry" | "self-edge-symmetry" => {
                        let p = self.eq(prems[0])?;
                        self.symmetry_matches(p, c, g)
                    }
                    "node-symmetry" => {
                        let row_eq = self.eq(prems[0])?;
                        let row = self.egg.get(prems[0]).rhs();
                        let classes = self.slotted_classes(row)?;
                        let groups: Vec<(TermId, ProofId)> = classes
                            .iter()
                            .enumerate()
                            .map(|(k, cls)| {
                                Ok((
                                    self.sub(&subst, &format!("_g{}", k + 1))?,
                                    self.group_premise(&prems, *cls)?,
                                ))
                            })
                            .collect::<R<_>>()?;
                        self.node_symmetry(row_eq, row, &groups, c, g)
                    }
                    "group-restore" => self.symmetry(c, g, prems[0]),
                    "group-empty" => Err("an emptied group has no elements".into()),
                    "group-shrink" => {
                        let source = prems[0];
                        let elements = self
                            .group_of_row(self.egg.get(source).lhs())?
                            .into_iter()
                            .map(|element| (element, source))
                            .collect::<Vec<_>>();
                        let slots = self.slot_map(self.sub(&subst, "_cs")?)?;
                        self.product_symmetry(c, g, &elements, Some(&slots))
                    }
                    other => Err(format!("no symmetry provenance through {other}")),
                }
            }
            Justification::MergeFn {
                function,
                old_proof,
                new_proof,
            } => {
                let (old_proof, new_proof) = (*old_proof, *new_proof);
                if function.starts_with("GroupReplace_") {
                    return self.symmetry(c, g, new_proof);
                }
                let mut elements = Vec::new();
                for side in [old_proof, new_proof] {
                    let maps = self.group_of_row(self.egg.get(side).lhs())?;
                    if maps.contains(g) {
                        return self.symmetry(c, g, side);
                    }
                    elements.extend(maps.into_iter().map(|element| (element, side)));
                }
                self.product_symmetry(c, g, &elements, None)
            }
            Justification::Congr {
                proof: base,
                child_proof,
                ..
            } => {
                // the row's class moved: c0 = c; symmetries of dec(c0) transport
                let (base, child_proof) = (*base, *child_proof);
                let c0 = {
                    let t = self.egg.get(base).lhs();
                    self.app(t).ok_or("not a group row")?.1[0]
                };
                let s0 = self.symmetry(c0, g, base)?;
                let e = self.eq(child_proof)?; // c0 = n·c
                let se = self.out.sym(e);
                let p = self.trans(se, s0)?;
                self.trans(p, e)
            }
            Justification::Trans(a, b) => {
                // a reflexive row restated through a congruence: use the base
                let (a, b) = (*a, *b);
                self.symmetry(c, g, a).or_else(|_| self.symmetry(c, g, b))
            }
            Justification::Sym(a) => self.symmetry(c, g, *a),
            Justification::Fiat => Err("a group stated by fiat".into()),
            other => Err(format!("no symmetry provenance through {other:?}")),
        }
    }

    /// The classes in a row's slotted columns, in column order.
    fn slotted_classes(&self, row: TermId) -> R<Vec<TermId>> {
        let (head, args) = self.app(row).ok_or("not a row")?;
        let ctor = self
            .program
            .constructors
            .get(head)
            .ok_or("unknown constructor")?;
        let mut out = vec![];
        let mut i = 0;
        for col in &ctor.columns {
            match col {
                ColumnKind::Child | ColumnKind::Binder => {
                    out.push(args[i + 1]);
                    i += 2;
                }
                ColumnKind::Payload => i += 1,
            }
        }
        Ok(out)
    }

    /// The premise stating `cls`'s group row.
    fn group_premise(&self, prems: &[ProofId], cls: TermId) -> R<ProofId> {
        prems
            .iter()
            .copied()
            .find(|q| {
                let t = self.egg.get(*q).lhs();
                self.app(t)
                    .is_some_and(|(h, a)| h.starts_with("EclassGroup_") && a.first() == Some(&cls))
            })
            .ok_or_else(|| format!("no group premise for {}", self.egg_string(cls)))
    }

    /// The symmetries a group row's provenance states outright, as proofs
    /// `dec(c) = m̂·dec(c)` with their full renamings: the rows that equate the
    /// class with a renaming of itself, before restriction to its slots.
    fn symmetry_sources(&mut self, grp_proof: ProofId) -> R<Vec<LiftedId>> {
        let proof = self.egg.get(grp_proof).clone();
        match proof.justification().clone() {
            Justification::Rule {
                name,
                premise_proofs: prems,
                ..
            } => match rule_kind(self.program, &name).1 {
                "self-symmetry" | "self-edge-symmetry" => {
                    let p = self.eq(prems[0])?;
                    Ok(vec![p])
                }
                "group-restore" | "group-shrink" => self.symmetry_sources(prems[0]),
                _ => Ok(vec![]),
            },
            Justification::MergeFn {
                function,
                old_proof,
                new_proof,
            } => {
                if function.starts_with("GroupReplace_") {
                    return self.symmetry_sources(new_proof);
                }
                let mut out = self.symmetry_sources(old_proof)?;
                out.extend(self.symmetry_sources(new_proof)?);
                Ok(out)
            }
            Justification::Congr {
                proof: base,
                child_proof,
                ..
            } => {
                let sources = self.symmetry_sources(base)?;
                let e = self.eq(child_proof)?; // c0 = n·c
                let mut out = vec![];
                for s0 in sources {
                    let se = self.out.sym(e);
                    let p = self.trans(se, s0)?;
                    out.push(self.trans(p, e)?);
                }
                Ok(out)
            }
            Justification::Trans(a, b) => {
                let mut out = self.symmetry_sources(a)?;
                out.extend(self.symmetry_sources(b)?);
                Ok(out)
            }
            Justification::Sym(a) => self.symmetry_sources(a),
            _ => Ok(vec![]),
        }
    }

    /// Prove a product of witnessed symmetries, optionally restricted to `slots`.
    fn product_symmetry(
        &mut self,
        c: TermId,
        g: &SlotMap,
        elements: &[(SlotMap, ProofId)],
        slots: Option<&SlotMap>,
    ) -> R<LiftedId> {
        let generators: Vec<_> = elements
            .iter()
            .map(|(element, _)| {
                slots.map_or_else(
                    || element.clone(),
                    |slots| compose(slots, &compose(element, slots)),
                )
            })
            .collect();
        // Find the word on the surviving slots, retaining its original witnesses.
        let mut seen: BTreeMap<SlotMap, Vec<usize>> = BTreeMap::new();
        let mut frontier: Vec<SlotMap> = vec![];
        for (i, e) in generators.iter().enumerate() {
            if seen.insert(e.clone(), vec![i]).is_none() {
                frontier.push(e.clone());
            }
        }
        while !seen.contains_key(g) && !frontier.is_empty() {
            let mut next = vec![];
            for h in &frontier {
                for (i, e) in generators.iter().enumerate() {
                    let prod = compose(h, e);
                    if !seen.contains_key(&prod) {
                        let mut path = seen[h].clone();
                        path.push(i);
                        seen.insert(prod.clone(), path);
                        next.push(prod);
                    }
                }
            }
            frontier = next;
        }
        let path = seen
            .get(g)
            .cloned()
            .ok_or_else(|| format!("{} is not generated by the group", slot_map_string(g)))?;
        let mut proof: Option<LiftedId> = None;
        for i in path {
            let s = self.symmetry(c, &elements[i].0, elements[i].1)?;
            proof = Some(match proof {
                None => s,
                Some(p) => self.trans(p, s)?,
            });
        }
        let proof = proof.ok_or("empty symmetry product")?;
        self.symmetry_matches(proof, c, g)
    }

    /// `p` proves `dec(c) = m·dec(c)`; it is the symmetry `g` when `m` and `g`
    /// agree on the class's slots.
    fn symmetry_matches(&mut self, p: LiftedId, c: TermId, g: &SlotMap) -> R<LiftedId> {
        let t = self.dec(c)?;
        let prop = self.out.proposition(p).clone();
        if prop.lhs != t || prop.rhs != t {
            return Err(format!(
                "{} is not a symmetry of {}",
                self.prop_string(p),
                self.out_string(t)
            ));
        }
        if g.iter().all(|(k, v)| prop.renaming.apply(*k) == *v) {
            return Ok(p);
        }
        Err(format!(
            "{} does not give the symmetry {}",
            self.prop_string(p),
            slot_map_string(g)
        ))
    }

    /// A symmetry a node gives its class: a reading of the children that spells
    /// the row's canonical edges again.
    fn node_symmetry(
        &mut self,
        row_eq: LiftedId,
        row: TermId,
        groups: &[(TermId, ProofId)],
        c: TermId,
        g: &SlotMap,
    ) -> R<LiftedId> {
        let (head, args) = self.app(row).ok_or("not a row")?;
        let ctor = self
            .program
            .constructors
            .get(head)
            .ok_or("unknown constructor")?
            .clone();
        let mut edges: Vec<SlotMap> = vec![];
        let mut classes: Vec<TermId> = vec![];
        let mut i = 0;
        for col in &ctor.columns {
            match col {
                ColumnKind::Child | ColumnKind::Binder => {
                    edges.push(self.slot_map(args[i])?);
                    classes.push(args[i + 1]);
                    i += 2;
                }
                ColumnKind::Payload => i += 1,
            }
        }
        let group_values: Vec<Vec<SlotMap>> = groups
            .iter()
            .map(|(t, _)| self.group(*t))
            .collect::<R<_>>()?;
        let own = shape(&edges);
        for (variant, gs) in readings(&edges, &group_values) {
            let spelled = shape(&variant);
            if spelled.edges != own.edges {
                continue;
            }
            let symmetry: SlotMap = own
                .back
                .iter()
                .filter_map(|(n, &slot)| spelled.back.get(n).map(|&image| (slot, image)))
                .collect();
            if !g.iter().all(|(k, v)| symmetry.get(k) == Some(v)) {
                continue;
            }
            // dec(row) = F(m̂_i·c_i) = F((m̂_i∘ĝ_i)·c_i) = σ·dec(row)
            let mut p = self.reflexive(self.out.proposition(row_eq).rhs)?;
            let mut k = 0;
            for (j, col) in ctor.columns.iter().enumerate() {
                if matches!(col, ColumnKind::Payload) {
                    continue;
                }
                let gi = &gs[k];
                let (ct, gp) = groups[k];
                let _ = ct;
                k += 1;
                if is_identity(gi) {
                    continue;
                }
                let s = self.symmetry(classes[k - 1], gi, gp)?;
                let completion = self.edge_memo[&(row, j)].clone();
                let renamed = self.rename_both(s, &completion);
                p = self.out.congr(p, j, renamed).map_err(|e| e.0)?;
                p = self.note(p);
            }
            // the right-hand side is now σ·dec(row) up to fresh names: align its coordinates
            let row_term = self.out.proposition(row_eq).rhs;
            let sigma = Renaming::completing(symmetry.iter().map(|(k, v)| (*k, *v)))
                .ok_or("node symmetry is not injective")?;
            let target = rename(&mut self.out.term_dag, &sigma, row_term);
            let aligned = self.align(p, target)?;
            // dec(row) = σ'·(σ·row) → reframe by σ⁻¹ to state it on the row itself
            let r = self.out.reframe(aligned, sigma.inverse());
            let r = self.note(r);
            // and the class is the row
            let s = self.out.sym(row_eq);
            let left = self.trans(row_eq, r)?;
            let full = self.trans(left, s)?;
            let t = self.dec(c)?;
            return self.symmetry_matches(full, c, g).map_err(|_| {
                format!(
                    "node symmetry of {} came out as {}",
                    self.out_string(t),
                    self.prop_string(full)
                )
            });
        }
        Err(format!(
            "no reading of {} gives the symmetry {}",
            self.egg_string(row),
            slot_map_string(g)
        ))
    }

    // ----- user rules --------------------------------------------------------------

    fn apply_rule(
        &mut self,
        name: &str,
        prems: &[ProofId],
        subst: &IndexMap<String, TermId>,
        lhs: TermId,
        rhs: TermId,
    ) -> R<LiftedId> {
        let rewrite = self
            .program
            .rewrites
            .get(name)
            .cloned()
            .ok_or_else(|| format!("no source for rule {name}"))?;
        let names = self
            .names
            .rules
            .get(name)
            .ok_or_else(|| format!("no generated names for rule {name}"))?;
        let names = &names.names;
        let root_name = match self.out.term_dag.get(rewrite.lhs) {
            Term::Var(v) => v.clone(),
            _ => names.patterns[0][0].1.clone(),
        };
        let root_class = &names.classes[&root_name];
        // the stored match and its firing
        let (firing, rekeys) = self.unwrap_match(prems[0])?;
        let matched = self.egg.get(firing).clone();
        let Justification::Rule {
            premise_proofs: match_prems,
            substitution: match_subst,
            ..
        } = matched.justification().clone()
        else {
            return Err(format!("the match of {name} is not a rule firing"));
        };
        let bridges: HashMap<TermId, ProofId> = rekeys.into_iter().collect();
        let frame = {
            let m = self.sub(subst, &names.frame)?;
            frame_from_term(self.egg(), m).ok_or("the apply rule's frame is not a frame")?
        };
        // Expand the matched atoms along the patterns, recording each variable's
        // class as the rows show it; the substitution is then read off the
        // expansions' contents, lifted into the frame's slot names.
        let cls_p = self.sub(&match_subst, root_class)?;
        let ctx = ExpandCtx {
            prems: &match_prems,
            subst: &match_subst,
            names: names.patterns[0].iter().cloned().collect(),
            classes: names.classes.clone(),
            readings: names.readings.clone(),
            bridges: &bridges,
        };
        let Expansion {
            proof: root,
            mut variables,
            occurrences: root_occ,
        } = self.expand(cls_p, rewrite.lhs, &[], &ctx, HashMap::default())?;
        let root = self.content_form(root); // cls_p = C
        let root_atom = self
            .atom_label(&frame, &root_name, rewrite.lhs, root_occ.get(&vec![]))
            .or(Some("@atom:0".to_string()));
        let nested = self.nested_node_slots(
            &frame,
            rewrite.lhs,
            &root_occ,
            &ctx.names,
            self.out.proposition(root).rhs,
        )?;
        let (root, _) = self.lift(root, &frame, root_atom.as_deref(), &nested);
        let content = self.out.proposition(root).rhs;
        let mut sigma: HashMap<String, TermId> = HashMap::default();
        let mut contents: Vec<(TermId, TermId)> = vec![(rewrite.lhs, content)];
        let mut condition_proofs: Vec<ConditionProof> = vec![];
        for (i, cond) in rewrite.conditions.iter().enumerate() {
            if let Some((var, call)) = cond.binding(&self.out.term_dag) {
                let var = var.clone();
                let cond_names = names
                    .patterns
                    .get(i + 1)
                    .map(|names| names.iter().cloned().collect())
                    .unwrap_or_default();
                let cond_ctx = ExpandCtx {
                    names: cond_names,
                    ..ctx.clone()
                };
                let cls_v = match variables.get(&var).copied() {
                    Some(c) => c,
                    None => {
                        let binding = names
                            .classes
                            .get(&var)
                            .ok_or_else(|| format!("no class binding for {var}"))?;
                        let class = self.sub(&match_subst, binding)?;
                        variables.insert(var.clone(), class);
                        class
                    }
                };
                let pattern = match self.out.term_dag.get(call) {
                    Term::Var(name) => rewrite.globals.get(name).copied().unwrap_or(call),
                    _ => call,
                };
                let Expansion {
                    proof: p,
                    variables: expanded,
                    occurrences: occ_v,
                } = self.expand(cls_v, pattern, &[], &cond_ctx, variables)?;
                variables = expanded;
                let p = self.content_form(p); // cls_v = C_v
                let atom = self.atom_label(&frame, &var, call, occ_v.get(&vec![]));
                let nested = self.nested_node_slots(
                    &frame,
                    call,
                    &occ_v,
                    &cond_ctx.names,
                    self.out.proposition(p).rhs,
                )?;
                let (p, _) = self.lift(p, &frame, atom.as_deref(), &nested);
                let c_v = self.out.proposition(p).rhs;
                contents.push((call, c_v));
                condition_proofs.push((var.clone(), call, p, occ_v));
            }
        }
        // Each class variable is its class under the frame's renaming of it, as
        // the compiler builds the right-hand side; a slot literal is that slot;
        // what the frame does not name is read off the contents.
        for (v, &cls) in &variables {
            if let Some(r) = frame.ren(v) {
                let m: SlotMap = r.iter().map(|(k, v)| (*k, *v)).collect();
                let d = self.dec(cls)?;
                let completion = self.complete(&m, d);
                let s = rename(&mut self.out.term_dag, &completion, d);
                sigma.insert(v.clone(), s);
            }
        }
        let mut literals: Vec<String> = vec![];
        for (pattern, _) in &contents {
            for v in rewrite.pattern_vars(&self.out.term_dag, *pattern) {
                if v.starts_with('$') && !literals.contains(&v) {
                    literals.push(v);
                }
            }
        }
        for v in literals {
            if let Some(r) = frame.ren(&v)
                && let Some(&s) = r.get(&0)
            {
                let term = slot_term(&mut self.out.term_dag, s);
                sigma.insert(v, term);
            }
        }
        for (pattern, content) in contents {
            self.bind_from_content(pattern, content, &mut sigma)?;
        }
        let coordinates = rewrite
            .globals
            .values()
            .flat_map(|&term| all_slots(&self.out.term_dag, term))
            .filter_map(|slot| frame.node_slot("@globals", slot).map(|at| (at, slot)));
        let to_source = Renaming::completing(coordinates).ok_or("non-injective global frame")?;
        for term in sigma.values_mut() {
            *term = rename(&mut self.out.term_dag, &to_source, *term);
        }
        // minted slots: right-hand-side literals the body never mentions
        if let Rhs::Term(r) = &rewrite.rhs {
            for v in rewrite.pattern_vars(&self.out.term_dag, *r) {
                if !sigma.contains_key(&v) {
                    if !v.starts_with('$') {
                        return Err(format!("{v} occurs only on the right-hand side of {name}"));
                    }
                    let f = self.fresh();
                    sigma.insert(v, slot_term(&mut self.out.term_dag, f));
                }
            }
        }
        let sigma_order: Vec<(String, TermId)> = {
            let mut order = rewrite.pattern_vars(&self.out.term_dag, rewrite.lhs);
            for cond in &rewrite.conditions {
                if let Some((var, call)) = cond.binding(&self.out.term_dag) {
                    let var = var.clone();
                    if !order.contains(&var) {
                        order.push(var.clone());
                    }
                    for v in rewrite.pattern_vars(&self.out.term_dag, call) {
                        if !order.contains(&v) {
                            order.push(v);
                        }
                    }
                }
            }
            if let Rhs::Term(r) = &rewrite.rhs {
                for v in rewrite.pattern_vars(&self.out.term_dag, *r) {
                    if !order.contains(&v) {
                        order.push(v);
                    }
                }
            }
            order.into_iter().map(|v| (v.clone(), sigma[&v])).collect()
        };
        for (v, s) in &sigma_order {
            log::debug!("rule {name}: {v} := {}", self.out_string(*s));
        }
        let instance_lhs = rewrite.instantiate(&mut self.out.term_dag, rewrite.lhs, &sigma)?;
        let instance_lhs = self
            .program
            .refresh_binders(&mut self.out.term_dag, instance_lhs);
        let instance_rhs = match &rewrite.rhs {
            Rhs::Term(r) => rewrite.instantiate(&mut self.out.term_dag, *r, &sigma)?,
            Rhs::Var(v) => *sigma
                .get(v)
                .ok_or_else(|| format!("the match of {name} binds no class for {v}"))?,
        };
        let instance_rhs = self
            .program
            .refresh_binders(&mut self.out.term_dag, instance_rhs);
        // the root premise: cls_p = ·L[σ]
        let root = self
            .fit(root, instance_lhs, &root_occ)
            .map_err(|e| format!("root of {name}: {e}"))?;
        let mut premises = vec![root];
        for (var, call, p, occ_v) in condition_proofs {
            let call_inst = rewrite.instantiate(&mut self.out.term_dag, call, &sigma)?;
            let call_inst = self
                .program
                .refresh_binders(&mut self.out.term_dag, call_inst);
            let p = self
                .fit(p, call_inst, &occ_v)
                .map_err(|e| format!("condition {var} of {name}: {e}"))?; // dec(cls_v) = ·call[σ]
            // from the class to σ(v), a renaming of it
            let d = self.dec(variables[&var])?;
            let target = sigma[&var];
            let mut pairs = BTreeMap::new();
            self.unify_slots(d, target, &mut pairs)
                .map_err(|e| format!("σ({var}) is not a renaming of its class: {e}"))?;
            let rho =
                Renaming::completing(pairs.into_iter()).ok_or("non-injective class renaming")?;
            let p = self.rename_both(p, &rho); // σ(v) = ·call[σ]
            let p = self.fit_content(p, call_inst, &occ_v)?;
            premises.push(p);
        }
        let rule_step = self.out.rule(
            SlottedProposition::equal(instance_lhs, instance_rhs),
            name.to_string(),
            sigma_order.clone(),
            premises.clone(),
            self.program,
        );
        self.note(rule_step);
        let p = self.trans(root, rule_step)?; // cls_p = ·R[σ]
        if lhs == rhs && self.is_carrier_term(lhs) {
            // the step states the reflexivity of a term the head built: a
            // subterm of the instance, which the rule may conclude
            let built = self.dec(lhs)?;
            let found = self
                .find_subterm_like(instance_rhs, built)
                .or(self.find_subterm_like(instance_lhs, built));
            if let Some(sub) = found {
                let refl = self.out.rule(
                    SlottedProposition::equal(sub, sub),
                    name.to_string(),
                    sigma_order,
                    premises,
                    self.program,
                );
                let refl = self.note(refl);
                let reframed = self.align(refl, built)?; // sub = ·built
                let s = self.out.sym(reframed); // built = ·sub
                return self.trans(s, reframed);
            }
        }
        if !self.is_carrier_term(lhs) {
            // a bare-variable right-hand side states an `Equated` row: cls_p = ·cls_x
            let (_, _, cls_x) = self.row_sides(lhs)?;
            let target = self.dec(cls_x)?;
            return self.align(p, target);
        }
        // the built term, which the instance may spell with other names for the
        // slots the class does not depend on
        let origin = self.sub(subst, root_class)?;
        let built = if lhs == rhs {
            lhs
        } else if lhs == origin {
            rhs
        } else if rhs == origin {
            lhs
        } else {
            return Err("the step relates neither side with the matched class".into());
        };
        let target = self.dec(built)?;
        let rhs_occ = match &rewrite.rhs {
            Rhs::Term(r) => self.pattern_occurrences(*r, &variables),
            Rhs::Var(v) => variables
                .get(v)
                .map(|&cls| (vec![], Occurrence { cls, row: None }))
                .into_iter()
                .collect(),
        };
        let p = self
            .fit(p, target, &rhs_occ)
            .map_err(|e| format!("result of {name}: {e}"))?;
        self.orient(p, lhs, rhs)
    }

    /// The classes at a right-hand-side pattern's variable positions.
    fn pattern_occurrences(
        &self,
        pattern: TermId,
        variables: &HashMap<String, TermId>,
    ) -> HashMap<Vec<usize>, Occurrence> {
        match self.out.term_dag.get(pattern) {
            Term::Var(v) => variables
                .get(v)
                .map(|&cls| (vec![], Occurrence { cls, row: None }))
                .into_iter()
                .collect(),
            Term::App(_, kids) => kids
                .iter()
                .enumerate()
                .flat_map(|(j, &kid)| {
                    self.pattern_occurrences(kid, variables).into_iter().map(
                        move |(path, occurrence)| {
                            (std::iter::once(j).chain(path).collect(), occurrence)
                        },
                    )
                })
                .collect(),
            Term::Lit(_) => HashMap::default(),
        }
    }

    /// The label of the atom whose root is `var`, matched at the row the
    /// expansion found for `pattern`: through the root variable's class slots, or
    /// through a child variable's or literal's, which share a block with the
    /// atom's node slots.
    fn atom_label(
        &self,
        frame: &Fr,
        var: &str,
        pattern: TermId,
        occ: Option<&Occurrence>,
    ) -> Option<String> {
        if let Some(a) = frame.atom_of(var) {
            return Some(a);
        }
        let Some(Occurrence {
            row: Some((row, _)),
            ..
        }) = occ
        else {
            return None;
        };
        let Term::App(head, kids) = self.out.term_dag.get(pattern).clone() else {
            return None;
        };
        let (_, args) = self.app(*row)?;
        let ctor = self.program.constructors.get(&head)?;
        let mut i = 0;
        let mut candidates: Option<BTreeSet<String>> = None;
        for (j, col) in ctor.columns.iter().enumerate() {
            match col {
                ColumnKind::Child | ColumnKind::Binder => {
                    if let Term::Var(v) = self.out.term_dag.get(kids[j]) {
                        let edge = renaming_from_term(self.egg(), args[i]);
                        if let Some(edge) = edge {
                            for (t, s) in edge.iter() {
                                let found: BTreeSet<String> = if v.starts_with('$') {
                                    frame.node_atoms_with_literal(v, *s).into_iter().collect()
                                } else {
                                    frame.node_atoms_with(v, *t, *s).into_iter().collect()
                                };
                                if found.is_empty() {
                                    continue;
                                }
                                candidates = Some(match candidates {
                                    None => found,
                                    Some(c) => c.intersection(&found).cloned().collect(),
                                });
                            }
                        }
                    }
                    i += 2;
                }
                ColumnKind::Payload => i += 1,
            }
        }
        candidates.and_then(|c| c.into_iter().next())
    }

    /// The frame coordinates of the nested atoms' node slots, as `(content slot,
    /// frame slot)` pairs: a nested row's node slot reaches the content through
    /// the renaming its occurrence spells it with.
    fn nested_node_slots(
        &mut self,
        frame: &Fr,
        pattern: TermId,
        occ: &HashMap<Vec<usize>, Occurrence>,
        names: &HashMap<Vec<usize>, String>,
        content: TermId,
    ) -> R<Vec<(i64, i64)>> {
        let mut out = vec![];
        let mut paths: Vec<&Vec<usize>> = occ.keys().filter(|p| !p.is_empty()).collect();
        paths.sort();
        for path in paths {
            let o = occ[path];
            let Some((row, _)) = o.row else { continue };
            let Some(name) = names.get(path) else {
                continue;
            };
            let sub_pattern = self.subterm_at(pattern, path)?;
            let Some(label) = self.atom_label(frame, name, sub_pattern, Some(&o)) else {
                continue;
            };
            let dr = self.dec(row)?;
            let sub = self.subterm_at(content, path)?;
            let mut pairs = BTreeMap::new();
            if self.unify_slots(dr, sub, &mut pairs).is_err() {
                continue;
            }
            for (s, cs) in pairs {
                if let Some(f) = frame.node_slot(&label, s) {
                    out.push((cs, f));
                }
            }
        }
        Ok(out)
    }

    /// A content in a matched node's own slot names restated in the frame's: each
    /// node slot goes to the pattern slot the frame gave it (the root atom's
    /// through `atom`, the nested atoms' as `nested` lists them), the rest (slots
    /// the pattern never named) to fresh names. Where two content slots would
    /// take one frame name, only the first does: a redundancy certificate is
    /// needed for the other.
    fn lift(
        &mut self,
        p: LiftedId,
        frame: &Fr,
        atom: Option<&str>,
        nested: &[(i64, i64)],
    ) -> (LiftedId, Renaming) {
        let content = self.out.proposition(p).rhs;
        let slots = all_slots(&self.out.term_dag, content);
        let mut pairs: Vec<(i64, i64)> = vec![];
        let mut taken: BTreeSet<i64> = BTreeSet::new();
        for s in &slots {
            if let Some(a) = atom
                && let Some(f) = frame.node_slot(a, *s)
            {
                pairs.push((*s, f));
                taken.insert(f);
            }
        }
        for (cs, f) in nested {
            if !slots.contains(cs) || pairs.iter().any(|(k, _)| k == cs) || taken.contains(f) {
                continue;
            }
            pairs.push((*cs, *f));
            taken.insert(*f);
        }
        self.fresh.reserve(taken);
        for s in &slots {
            if !pairs.iter().any(|(k, _)| k == s) {
                let f = self.fresh();
                pairs.push((*s, f));
            }
        }
        let Some(pi) = Renaming::completing(pairs) else {
            return (p, Renaming::identity());
        };
        let r = self.out.reframe(p, pi.clone());
        (self.note(r), pi)
    }

    /// A subterm of `haystack` that is `needle` up to a bijection of slots.
    fn find_subterm_like(&self, haystack: TermId, needle: TermId) -> Option<TermId> {
        let mut stack = vec![haystack];
        while let Some(t) = stack.pop() {
            let mut pairs = BTreeMap::new();
            if self.unify_slots(t, needle, &mut pairs).is_ok()
                && Renaming::completing(pairs.into_iter()).is_some()
            {
                return Some(t);
            }
            if let Term::App(_, kids) = self.out.term_dag.get(t) {
                stack.extend(kids.iter().copied());
            }
        }
        None
    }

    /// `t1 = m·t2` restated as `t1 = (m·t2)`: the renaming applied, so the
    /// right-hand side is the term the proposition is about.
    fn content_form(&mut self, p: LiftedId) -> LiftedId {
        let m = self.out.proposition(p).renaming.clone();
        let r = self.out.reframe(p, m);
        self.note(r)
    }

    /// Read a substitution off a pattern's instance: each variable's first
    /// occurrence binds it, a slot literal binds to the slot at its position.
    fn bind_from_content(
        &mut self,
        pattern: TermId,
        content: TermId,
        sigma: &mut HashMap<String, TermId>,
    ) -> R<()> {
        match self.out.term_dag.get(pattern).clone() {
            Term::Var(v) => {
                if sigma.contains_key(&v) {
                    // another occurrence may read the class through a symmetry or
                    // spell a redundant slot otherwise; the first occurrence stands
                    return Ok(());
                }
                if v.starts_with('$')
                    && super::terms::slot_of(&self.out.term_dag, content).is_none()
                {
                    return Err(format!(
                        "literal {v} stands at a non-slot {}",
                        self.out_string(content)
                    ));
                }
                sigma.insert(v, content);
                Ok(())
            }
            Term::Lit(_) => Ok(()),
            Term::App(_, kids) => {
                let Term::App(_, ckids) = self.out.term_dag.get(content).clone() else {
                    return Err(format!(
                        "pattern {} met a non-application {}",
                        self.out_string(pattern),
                        self.out_string(content)
                    ));
                };
                if kids.len() != ckids.len() {
                    return Err("pattern and instance differ in arity".into());
                }
                for (k, c) in kids.iter().zip(ckids.iter()) {
                    self.bind_from_content(*k, *c, sigma)?;
                }
                Ok(())
            }
        }
    }

    /// Which side of a row proof's proposition a consumer reads.
    fn row_side(&self, proof: ProofId, rhs: bool) -> TermId {
        let p = self.egg.get(proof);
        if rhs { p.rhs() } else { p.lhs() }
    }

    /// The equality denoted by one side of a row proof's proposition. A row proof
    /// may relate a row to its re-keyed form, or state a row reflexively through
    /// a composition; the consumer wants the equality of the row as it reads it.
    fn row_eq(&mut self, id: ProofId, rhs_side: bool) -> R<LiftedId> {
        let proof = self.egg.get(id).clone();
        let (lhs, rhs) = (proof.lhs(), proof.rhs());
        if lhs == rhs {
            // a reflexive row: its own justification says how it holds
            return match proof.justification() {
                Justification::Trans(a, b) => {
                    let (a, b) = (*a, *b);
                    match self.egg.get(a).justification() {
                        Justification::Sym(x) => {
                            let x = *x;
                            let want = self.row_side(x, false) == lhs;
                            self.row_eq(x, !want)
                        }
                        _ => self.row_eq(a, true),
                    }
                    .or_else(|_| self.row_eq(b, true))
                }
                Justification::Sym(x) => {
                    let x = *x;
                    self.row_eq(x, false)
                }
                _ => self.eq_direct(id),
            };
        }
        match proof.justification() {
            Justification::Sym(x) => {
                let x = *x;
                self.row_eq(x, !rhs_side)
            }
            Justification::Trans(a, b) => {
                let (a, b) = (*a, *b);
                if rhs_side {
                    self.row_eq(b, true)
                } else {
                    self.row_eq(a, false)
                }
            }
            Justification::Congr { proof: base, .. } if !rhs_side => {
                let base = *base;
                self.row_eq(base, false)
            }
            _ => self.eq_direct(id),
        }
    }

    /// A stored match's proof unwrapped to the rule firing that wrote the row,
    /// with the proofs that re-keyed its class columns since: `(old, old = new)`.
    fn unwrap_match(&self, proof: ProofId) -> R<(ProofId, Vec<(TermId, ProofId)>)> {
        let p = self.egg.get(proof);
        match p.justification() {
            Justification::Rule { .. } => Ok((proof, vec![])),
            Justification::Congr {
                proof: base,
                child_index,
                child_proof,
            } => {
                let (firing, mut bridges) = self.unwrap_match(*base)?;
                // the re-keyed column's old class is in the base row
                let base_row = self.egg.get(*base).rhs();
                let old = self
                    .app(base_row)
                    .and_then(|(_, a)| a.get(*child_index).copied())
                    .unwrap_or(self.egg.get(*child_proof).lhs());
                bridges.push((old, *child_proof));
                Ok((firing, bridges))
            }
            Justification::Trans(a, b) => self.unwrap_match(*a).or_else(|_| self.unwrap_match(*b)),
            Justification::Sym(a) => self.unwrap_match(*a),
            other => Err(format!("a stored match justified by {other:?}")),
        }
    }

    /// A re-key's child proof as `old = ·new`, whichever way it was stated.
    fn bridge_eq(&mut self, bridge: ProofId, old: TermId) -> R<(LiftedId, TermId)> {
        let pr = self.egg.get(bridge);
        let (l, r) = (pr.lhs(), pr.rhs());
        let e = self.eq(bridge)?;
        if l == old {
            Ok((e, r))
        } else if r == old {
            let s = self.out.sym(e);
            Ok((self.note(s), l))
        } else {
            Err(format!(
                "re-key {} relates neither side with {}",
                self.prop_string(e),
                self.egg_string(old)
            ))
        }
    }

    /// `dec(cls) = ·T` where `T` expands the matched atoms below `cls` along the
    /// pattern they matched: each column whose pattern is a call is replaced by
    /// that call's own atom, found among the premises by its class and head, read
    /// through the symmetry the match chose for it.
    fn expand(
        &mut self,
        cls: TermId,
        pattern: TermId,
        path: &[usize],
        ctx: &ExpandCtx<'_>,
        variables: HashMap<String, TermId>,
    ) -> R<Expansion> {
        let cls = if let Term::App(head, _) = self.out.term_dag.get(pattern) {
            let has_row = |class| {
                ctx.prems.iter().any(|&p| {
                    let p = self.egg.get(p);
                    p.lhs() == class && self.app(p.rhs()).is_some_and(|(h, _)| h == head)
                })
            };
            if has_row(cls) {
                cls
            } else {
                ctx.bridges
                    .keys()
                    .copied()
                    .find(|&old| {
                        if !has_row(old) {
                            return false;
                        }
                        let mut current = old;
                        let mut seen = HashSet::default();
                        while seen.insert(current) {
                            if current == cls {
                                return true;
                            }
                            let Some(&p) = ctx.bridges.get(&current) else {
                                break;
                            };
                            let p = self.egg.get(p);
                            current = if p.lhs() == current { p.rhs() } else { p.lhs() };
                        }
                        false
                    })
                    .unwrap_or(cls)
            }
        } else {
            cls
        };
        let mut expanded = self.expand_old(cls, pattern, path, ctx, variables)?;
        // the class may have been re-keyed since the firing, perhaps more than
        // once: state it from the class it became
        let mut current = cls;
        while let Some(&bridge) = ctx.bridges.get(&current) {
            let (e, new) = self.bridge_eq(bridge, current)?; // old = ·new
            let s = self.out.sym(e);
            expanded.proof = self.trans(s, expanded.proof)?;
            current = new;
        }
        // A flattened atom retains the symmetry selected for this occurrence.
        if let Some(name) = ctx.names.get(path)
            && let Some(reading) = ctx.readings.get(name)
            && let Ok(g) = self.sub(ctx.subst, reading)
        {
            let g = self.slot_map(g)?;
            if !is_identity(&g) {
                let group = self.reading_group_proof(cls, &g, ctx.prems)?;
                let symmetry = self.symmetry(cls, &g, group)?;
                let completion = Renaming::completing(g.iter().map(|(k, v)| (*k, *v)))
                    .ok_or("reading is not injective")?;
                let renamed = self.rename_both(expanded.proof, &completion);
                let symmetry = self.out.reframe(symmetry, completion);
                let symmetry = self.note(symmetry);
                expanded.proof = self.trans(symmetry, renamed)?;
            }
        }
        Ok(expanded)
    }

    fn expand_old(
        &mut self,
        cls: TermId,
        pattern: TermId,
        path: &[usize],
        ctx: &ExpandCtx<'_>,
        mut variables: HashMap<String, TermId>,
    ) -> R<Expansion> {
        let mut occurrences = HashMap::from_iter([(path.to_vec(), Occurrence { cls, row: None })]);
        let Term::App(ctor, kids) = self.out.term_dag.get(pattern).clone() else {
            if let Term::Var(v) = self.out.term_dag.get(pattern)
                && !v.starts_with('$')
            {
                variables.insert(v.clone(), cls);
            }
            let t = self.dec(cls)?;
            return Ok(Expansion {
                proof: self.reflexive(t)?,
                variables,
                occurrences,
            });
        };
        let prems = ctx.prems;
        if !ctx.names.contains_key(path)
            && super::terms::pattern_vars(&self.out.term_dag, pattern)
                .iter()
                .all(|v| v.starts_with('$'))
        {
            for &premise in prems {
                let row = self.egg.get(premise).rhs();
                let Some((head, args)) = self.app(row) else {
                    continue;
                };
                if !row_kind(head).is_edge() || args.len() < 3 || args[2] != cls {
                    continue;
                }
                let node = args[0];
                let sources = std::iter::once((node, None))
                    .chain(self.egg.proofs().filter_map(|(p, proof)| {
                        if proof.rhs() == node && self.is_carrier_term(proof.lhs()) {
                            Some((proof.lhs(), Some((p, false))))
                        } else if proof.lhs() == node && self.is_carrier_term(proof.rhs()) {
                            Some((proof.rhs(), Some((p, true))))
                        } else {
                            None
                        }
                    }))
                    .collect::<Vec<_>>();
                for (source, bridge) in sources {
                    let decoded = self.dec(source)?;
                    if !self
                        .program
                        .alpha_eq(&mut self.out.term_dag, decoded, pattern)
                    {
                        continue;
                    }
                    let mut proof = self.eq(premise)?;
                    if let Some((bridge, reversed)) = bridge {
                        let mut bridge = self.eq(bridge)?;
                        if reversed {
                            bridge = self.out.sym(bridge);
                        }
                        proof = self.trans(bridge, proof)?;
                    }
                    let row_eq = self.out.sym(proof);
                    if let Ok(proof) = self.align(row_eq, pattern) {
                        occurrences.insert(
                            path.to_vec(),
                            Occurrence {
                                cls,
                                row: Some((source, row_eq)),
                            },
                        );
                        self.global_occurrences(source, path, &mut occurrences)?;
                        return Ok(Expansion {
                            proof,
                            variables,
                            occurrences,
                        });
                    }
                }
            }
        }
        if self.is_leaf_pattern(pattern) {
            // a leaf: its class reaches the constructor's own class by an edge,
            // or is that class
            if let Some(link) = self.leaf_edge(cls, pattern, prems) {
                let e = self.eq(link)?; // leader = m·cls
                let s = self.out.sym(e);
                return Ok(Expansion {
                    proof: self.note(s),
                    variables,
                    occurrences,
                });
            }
        }
        let columns = self
            .program
            .constructors
            .get(&ctor)
            .ok_or_else(|| format!("unknown constructor {ctor}"))?
            .columns
            .clone();
        // the atom row: `cls = (ctor ...)` whose pattern-variable columns hold the
        // substitution's classes
        let atom = prems
            .iter()
            .copied()
            .find(|q| {
                let pr = self.egg.get(*q);
                pr.lhs() == cls
                    && self.app(pr.rhs()).is_some_and(|(h, args)| {
                        h == ctor
                            && self.columns_match(args, &columns, &kids, path, ctx, &variables)
                    })
            })
            .ok_or_else(|| {
                let listed: Vec<String> = prems
                    .iter()
                    .map(|q| {
                        let pr = self.egg.get(*q);
                        format!(
                            "{} = {}",
                            self.egg_string(pr.lhs()),
                            self.egg_string(pr.rhs())
                        )
                    })
                    .collect();
                format!(
                    "no matched {ctor} row for {} among the premises:\n  {}",
                    self.egg_string(cls),
                    listed.join("\n  ")
                )
            })?;
        let mut p = self.eq(atom)?;
        let row = self.egg.get(atom).rhs();
        log::debug!(
            "expand {} at {path:?}: row {}",
            self.egg_string(cls),
            self.egg_string(row)
        );
        occurrences.insert(
            path.to_vec(),
            Occurrence {
                cls,
                row: Some((row, p)),
            },
        );
        let (_, args) = self.app(row).ok_or("not a row")?;
        let mut i = 0;
        for (j, col) in columns.iter().enumerate() {
            match col {
                ColumnKind::Child => {
                    let child = args[i + 1];
                    i += 2;
                    let kid = kids[j];
                    if let Term::Var(v) = self.out.term_dag.get(kid).clone()
                        && !v.starts_with('$')
                    {
                        let mut current = child;
                        let mut bridged: Option<LiftedId> = None;
                        while let Some(&bridge) = ctx.bridges.get(&current) {
                            let (e, new) = self.bridge_eq(bridge, current)?; // old = ·new
                            bridged = Some(match bridged {
                                None => e,
                                Some(prev) => self.trans(prev, e)?,
                            });
                            current = new;
                        }
                        if let Some(e) = bridged {
                            let completion = self.edge_memo[&(row, j)].clone();
                            let renamed = self.rename_both(e, &completion);
                            p = self.out.congr(p, j, renamed).map_err(|e| e.0)?;
                            p = self.note(p);
                        }
                        variables.entry(v).or_insert(current);
                        let mut sub_path = path.to_vec();
                        sub_path.push(j);
                        occurrences.insert(
                            sub_path,
                            Occurrence {
                                cls: current,
                                row: None,
                            },
                        );
                    }
                    if matches!(self.out.term_dag.get(kid), Term::App(..)) {
                        let mut sub_path = path.to_vec();
                        sub_path.push(j);
                        let Expansion {
                            proof: sub,
                            variables: expanded,
                            occurrences: nested,
                        } = self.expand(child, kid, &sub_path, ctx, variables)?;
                        variables = expanded;
                        occurrences.extend(nested);
                        let completion = self.edge_memo[&(row, j)].clone();
                        let renamed = self.rename_both(sub, &completion);
                        p = self.out.congr(p, j, renamed).map_err(|e| e.0)?;
                        p = self.note(p);
                    }
                }
                ColumnKind::Binder => i += 2,
                ColumnKind::Payload => i += 1,
            }
        }
        Ok(Expansion {
            proof: p,
            variables,
            occurrences,
        })
    }

    /// A pattern the flattener reaches through its class rather than by an atom
    /// of its own: a constructor with no slotted column and no payload variable.
    fn is_leaf_pattern(&self, pattern: TermId) -> bool {
        let Term::App(ctor, kids) = self.out.term_dag.get(pattern) else {
            return false;
        };
        let Some(c) = self.program.constructors.get(ctor) else {
            return false;
        };
        c.columns.iter().all(|k| matches!(k, ColumnKind::Payload))
            && kids
                .iter()
                .all(|k| !matches!(self.out.term_dag.get(*k), Term::Var(_)))
    }

    /// A leaf has no atom name. Its edge premise identifies the matched class,
    /// including the literal payloads that distinguish leaves of one constructor.
    fn leaf_edge(&self, cls: TermId, pattern: TermId, prems: &[ProofId]) -> Option<ProofId> {
        let Term::App(ctor, kids) = self.out.term_dag.get(pattern) else {
            return None;
        };
        prems.iter().copied().find(|&id| {
            self.app(self.egg.get(id).rhs())
                .is_some_and(|(head, args)| {
                    row_kind(head).is_edge()
                        && args.len() >= 3
                        && args[2] == cls
                        && self.app(args[0]).is_some_and(|(head, args)| {
                            head == ctor
                                && args.len() == kids.len()
                                && args
                                    .iter()
                                    .zip(kids)
                                    .all(|(&a, &b)| self.egg().get(a) == self.out.term_dag.get(b))
                        })
                })
        })
    }

    // Prefer a proved representative with fewer free slots so certificates can
    // reach a child whose source spelling still includes a redundant slot.
    fn global_occurrence(&mut self, child: TermId) -> R<Occurrence> {
        let head = self
            .app(child)
            .ok_or("global child is not a constructor")?
            .0;
        let term = self.dec(child)?;
        let mut free = self.program.free_slots(&self.out.term_dag, term).len();
        let mut occurrence = Occurrence {
            cls: child,
            row: None,
        };
        let candidates = self
            .egg
            .proofs()
            .filter_map(|(id, proof)| {
                (proof.lhs() != proof.rhs()
                    && self.is_carrier_term(proof.lhs())
                    && self.is_carrier_term(proof.rhs()))
                .then_some((id, proof.lhs(), proof.rhs()))
            })
            .collect::<Vec<_>>();
        for (id, lhs, rhs) in candidates {
            for (row, cls, reversed) in [(rhs, lhs, false), (lhs, rhs, true)] {
                if self.app(row).is_none_or(|(h, _)| h != head) {
                    continue;
                }
                let decoded = self.dec(row)?;
                let mut pairs = BTreeMap::new();
                if self.unify_slots(decoded, term, &mut pairs).is_err()
                    || Renaming::completing(pairs.into_iter()).is_none()
                {
                    continue;
                }
                let target = self.dec(cls)?;
                let target_free = self.program.free_slots(&self.out.term_dag, target).len();
                if target_free >= free {
                    continue;
                }
                let mut proof = self.eq(id)?;
                if reversed {
                    proof = self.out.sym(proof);
                }
                occurrence = Occurrence {
                    cls,
                    row: Some((row, proof)),
                };
                free = target_free;
            }
        }
        Ok(occurrence)
    }

    fn global_occurrences(
        &mut self,
        node: TermId,
        path: &[usize],
        occurrences: &mut HashMap<Vec<usize>, Occurrence>,
    ) -> R<()> {
        let (head, args) = self.app(node).ok_or("global node is not a constructor")?;
        let Some(constructor) = self.program.constructors.get(head) else {
            return Ok(());
        };
        let mut physical = 0;
        for (column, kind) in constructor.columns.iter().enumerate() {
            match kind {
                ColumnKind::Child => {
                    let child = *args
                        .get(physical + 1)
                        .ok_or("short global constructor row")?;
                    if self
                        .app(child)
                        .is_some_and(|(h, _)| self.program.constructors.contains_key(h))
                    {
                        let mut child_path = path.to_vec();
                        child_path.push(column);
                        occurrences.insert(child_path.clone(), self.global_occurrence(child)?);
                        self.global_occurrences(child, &child_path, occurrences)?;
                    }
                    physical += 2;
                }
                ColumnKind::Binder => physical += 2,
                ColumnKind::Payload => physical += 1,
            }
        }
        Ok(())
    }

    /// The group row a `Reading` row for `(child, g)` among the premises derives
    /// from.
    fn reading_group_proof(&self, child: TermId, g: &SlotMap, prems: &[ProofId]) -> R<ProofId> {
        let reading = prems
            .iter()
            .copied()
            .find(|q| {
                let t = self.egg.get(*q).lhs();
                self.app(t).is_some_and(|(h, a)| {
                    h.starts_with("Reading_")
                        && a.len() >= 3
                        && a[0] == child
                        && renaming_from_term(self.egg(), a[2]).as_ref() == Some(g)
                })
            })
            .ok_or_else(|| {
                format!(
                    "no reading row for {} with {}",
                    self.egg_string(child),
                    slot_map_string(g)
                )
            })?;
        self.group_row_behind(reading)
    }

    /// Walk from a `Reading` or `CosetReps` row's proof to the `EclassGroup` row
    /// its elements came from.
    fn group_row_behind(&self, proof: ProofId) -> R<ProofId> {
        let p = self.egg.get(proof);
        let head = self.app(p.lhs()).map(|(h, _)| h).unwrap_or("");
        if head.starts_with("EclassGroup_") {
            return Ok(proof);
        }
        match p.justification() {
            Justification::Rule {
                premise_proofs,
                name,
                ..
            } => {
                let kind = rule_kind(self.program, name).1;
                match kind {
                    "reading-small" | "reading-big" => self.group_row_behind(
                        *premise_proofs
                            .iter()
                            .find(|q| {
                                let t = self.egg.get(**q).lhs();
                                self.app(t)
                                    .is_some_and(|(h, _)| h.starts_with("CosetReps_"))
                            })
                            .ok_or("reading without its coset row")?,
                    ),
                    "coset-readings" | "coset-repair" => self.group_row_behind(
                        *premise_proofs
                            .iter()
                            .find(|q| {
                                let t = self.egg.get(**q).lhs();
                                self.app(t)
                                    .is_some_and(|(h, _)| h.starts_with("EclassGroup_"))
                            })
                            .ok_or("coset row without its group row")?,
                    ),
                    other => Err(format!("no group behind rule {other}")),
                }
            }
            Justification::MergeFn { new_proof, .. } => self.group_row_behind(*new_proof),
            Justification::Congr { proof, .. } => self.group_row_behind(*proof),
            Justification::Trans(a, _) | Justification::Sym(a) => self.group_row_behind(*a),
            other => Err(format!("no group behind {other:?}")),
        }
    }

    /// Do a row's class columns agree with the substitution where the pattern
    /// names a variable?
    fn columns_match(
        &self,
        args: &[TermId],
        columns: &[ColumnKind],
        kids: &[TermId],
        path: &[usize],
        ctx: &ExpandCtx<'_>,
        variables: &HashMap<String, TermId>,
    ) -> bool {
        let mut i = 0;
        for (j, col) in columns.iter().enumerate() {
            match col {
                ColumnKind::Child => {
                    let class = args.get(i + 1).copied();
                    let is_var_class = class.is_some_and(|c| {
                        self.app(c)
                            .is_some_and(|(h, _)| self.names.is_var_constructor(h))
                    });
                    // the class the match bound the nested atom to, when the
                    // substitution names it
                    let mut sub_path = path.to_vec();
                    sub_path.push(j);
                    let bound = ctx
                        .names
                        .get(&sub_path)
                        .and_then(|name| ctx.classes.get(name))
                        .and_then(|class| ctx.subst.get(class))
                        .copied();
                    match self.out.term_dag.get(kids[j]) {
                        Term::Var(v) if v.starts_with('$') => {
                            if !is_var_class {
                                return false;
                            }
                        }
                        Term::Var(v) => {
                            let bound = ctx.classes.get(v).and_then(|c| ctx.subst.get(c));
                            if let Some(&want) = variables.get(v).or(bound)
                                && class != Some(want)
                            {
                                return false;
                            }
                        }
                        Term::App(..) => match bound {
                            Some(want) => {
                                if class != Some(want) {
                                    return false;
                                }
                            }
                            None if self.is_leaf_pattern(kids[j]) => {
                                if class.is_none_or(|cls| {
                                    self.leaf_edge(cls, kids[j], ctx.prems).is_none()
                                }) {
                                    return false;
                                }
                            }
                            None if is_var_class => return false,
                            None => {}
                        },
                        Term::Lit(_) => {}
                    }
                    i += 2;
                }
                ColumnKind::Binder => i += 2,
                ColumnKind::Payload => {
                    // a literal must be the row's value; a payload variable the
                    // substitution binds must be bound to it
                    let Some(&value) = args.get(i) else {
                        return false;
                    };
                    match self.out.term_dag.get(kids[j]) {
                        Term::Lit(l) => {
                            if !matches!(self.egg().get(value), Term::Lit(m) if m == l) {
                                return false;
                            }
                        }
                        Term::Var(v) => {
                            if let Some(&want) = ctx.subst.get(v)
                                && want != value
                            {
                                return false;
                            }
                        }
                        Term::App(..) => {}
                    }
                    i += 1;
                }
            }
        }
        true
    }

    // ----- redundant slots: certificates ----------------------------------------------

    /// Every proof in the egglog store of a `FreeVars` row, by its class term.
    fn free_vars_proofs(&mut self, cls: TermId) -> Vec<ProofId> {
        self.free_vars_index
            .get_or_insert_with(|| row_proofs(self.egg, "FreeVars_"))
            .get(&cls)
            .cloned()
            .unwrap_or_default()
    }

    /// `dec(c) = (s f)·dec(c)`: slot `s` of `c`'s term is one its class does not
    /// depend on, so it may be renamed to the unused `f`. Derived from how the
    /// class's slot set came to exclude `s`.
    fn class_cert(&mut self, c: TermId, s: i64, f: i64) -> R<LiftedId> {
        let t = self.dec(c)?;
        log::debug!("class_cert {} slot {s} -> {f}", self.out_string(t));
        if !all_slots(&self.out.term_dag, t).contains(&s) {
            return self.reflexive(t);
        }
        if !self.cert_stack.insert((c, s)) {
            return Err(format!(
                "the certificate for ${s} in {} depends on itself",
                self.out_string(t)
            ));
        }
        let r = self.class_cert_inner(c, s, f);
        self.cert_stack.remove(&(c, s));
        r
    }

    fn class_cert_inner(&mut self, c: TermId, s: i64, f: i64) -> R<LiftedId> {
        let t = self.dec(c)?;
        let proofs = self.free_vars_proofs(c);
        let mut errors = vec![];
        for proof in proofs {
            let (_, args) = self.app(self.egg.get(proof).lhs()).ok_or("not a row")?;
            let cs = self.slot_map(args[1])?;
            if cs.contains_key(&s) {
                continue;
            }
            match self.cert_from(proof, c, s, f) {
                Ok(p) => return Ok(p),
                Err(e) => errors.push(e),
            }
        }
        Err(format!(
            "no certificate that ${s} is redundant in {}: {}",
            self.out_string(t),
            if errors.is_empty() {
                "no FreeVars row excludes it".to_string()
            } else {
                errors.join("; ")
            }
        ))
    }

    /// The certificate for `(c, s, f)` through one proof of a `FreeVars` row
    /// that excludes `s`.
    fn cert_from(&mut self, proof: ProofId, c: TermId, s: i64, f: i64) -> R<LiftedId> {
        let p = self.egg.get(proof).clone();
        match p.justification().clone() {
            Justification::Rule {
                name,
                premise_proofs: prems,
                substitution: subst,
            } => match rule_kind(self.program, &name).1 {
                "class-slots" => {
                    // the class is the row, `c = M·row`: a slot the row's content does
                    // not mention is redundant outright; otherwise s is not a node slot
                    // of the row, so it belongs to a child's term, where the child's
                    // class does not depend on it
                    let row = self.egg.get(prems[0]).rhs();
                    let row_eq = self.eq(prems[0])?; // c = M·row
                    let prop = self.out.proposition(row_eq).clone();
                    let content = rename(&mut self.out.term_dag, &prop.renaming, prop.rhs);
                    if !all_slots(&self.out.term_dag, content).contains(&s) {
                        return self.lemma(row_eq, s, f);
                    }
                    let m_inv = prop.renaming.inverse();
                    let (s_row, f_row) = (m_inv.apply(s), m_inv.apply(f));
                    let (head, args) = self.app(row).ok_or("not a row")?;
                    let ctor = self
                        .program
                        .constructors
                        .get(head)
                        .ok_or("unknown constructor")?
                        .clone();
                    let mut i = 0;
                    for (j, col) in ctor.columns.iter().enumerate() {
                        match col {
                            ColumnKind::Child => {
                                let child = args[i + 1];
                                i += 2;
                                let completion = self.edge_memo[&(row, j)].clone();
                                let child_term = self.dec(child)?;
                                let occ = rename(&mut self.out.term_dag, &completion, child_term);
                                if !all_slots(&self.out.term_dag, occ).contains(&s_row) {
                                    continue;
                                }
                                let r = completion.inverse().apply(s_row);
                                let fi = completion.inverse().apply(f_row);
                                let cert = self.class_cert(child, r, fi)?;
                                let lifted = self.rename_both(cert, &completion); // occ = ·child
                                let lifted = self.out.reframe(lifted, completion.clone()); // occ = (s f)·occ
                                let lifted = self.note(lifted);
                                let refl = self.reflexive(prop.rhs)?;
                                let r = self.out.congr(refl, j, lifted).map_err(|e| e.0)?; // row = ·row[s->f]
                                let r = self.note(r);
                                let r = self.out.reframe(
                                    r,
                                    Renaming::new([(s_row, f_row), (f_row, s_row)]).unwrap(),
                                );
                                let r = self.note(r); // row = (s_row f_row)·row
                                // and the class is the row
                                return self.transport(r, row_eq);
                            }
                            ColumnKind::Binder => i += 2,
                            ColumnKind::Payload => i += 1,
                        }
                    }
                    Err(format!("${s} is in no child of {}", self.egg_string(row)))
                }
                "transport-down" => {
                    // FreeVars b ⊆ m⁻¹(FreeVars a) from a = m·b
                    let edge = self.eq(prems[0])?; // a = m·b
                    let q = self.out.sym(edge); // b = m⁻¹·a
                    let q = self.note(q);
                    let prop = self.out.proposition(q).clone();
                    let a_term = prop.rhs;
                    let content = rename(&mut self.out.term_dag, &prop.renaming, a_term);
                    if !all_slots(&self.out.term_dag, content).contains(&s) {
                        return self.lemma(q, s, f);
                    }
                    // the slot of a it comes from is redundant in a
                    let x = prop.renaming.inverse().apply(s);
                    let a = self.sub(&subst, "_a")?;
                    let fa = prop.renaming.inverse().apply(f);
                    let cert_a = self.class_cert(a, x, fa)?;
                    self.transport(cert_a, q)
                }
                "transport-up" => {
                    // FreeVars a ⊆ m(FreeVars b) from a = m·b
                    let edge = self.eq(prems[0])?; // a = m·b
                    let prop = self.out.proposition(edge).clone();
                    let content = rename(&mut self.out.term_dag, &prop.renaming, prop.rhs);
                    if !all_slots(&self.out.term_dag, content).contains(&s) {
                        return self.lemma(edge, s, f);
                    }
                    let r = prop.renaming.inverse().apply(s);
                    let b = self.sub(&subst, "_b")?;
                    let fb = prop.renaming.inverse().apply(f);
                    let cert_b = self.class_cert(b, r, fb)?;
                    self.transport(cert_b, edge)
                }
                "slot-closure" => {
                    let grp = self.group(self.sub(&subst, "_grp")?)?;
                    let old = self.slot_map(self.sub(&subst, "_slots")?)?;
                    let t = self.dec(c)?;
                    // the symmetries behind the group, as stated: a group element
                    // restricted to the class's slots may have lost the entry
                    // that drops the slot
                    let mut syms: Vec<LiftedId> = vec![];
                    for g in grp.iter().filter(|g| !is_identity(g)) {
                        if let Ok(sp) = self.symmetry(c, g, prems[0]) {
                            syms.push(sp);
                        }
                    }
                    let grp_row = prems
                        .iter()
                        .copied()
                        .find(|q| {
                            let t = self.egg.get(*q).lhs();
                            self.app(t)
                                .is_some_and(|(h, _)| h.starts_with("EclassGroup_"))
                        })
                        .unwrap_or(prems[0]);
                    let mut errors = vec![];
                    match self.symmetry_sources(grp_row) {
                        Ok(more) => syms.extend(more),
                        Err(e) => errors.push(e),
                    }
                    for sym in syms {
                        let prop = self.out.proposition(sym).clone(); // t = ĝ·t
                        if prop.lhs != t || prop.rhs != t {
                            continue;
                        }
                        let content = rename(&mut self.out.term_dag, &prop.renaming, t);
                        if !all_slots(&self.out.term_dag, content).contains(&s) {
                            return self.lemma(sym, s, f);
                        }
                        // the conjugation needs a name the symmetry leaves alone:
                        // a fresh one, renamed to f at the end
                        let g = self.fresh();
                        // s = ĝ(y): a slot y the old set lacks gives s through the symmetry
                        let y = prop.renaming.inverse().apply(s);
                        if y != s
                            && !old.contains_key(&y)
                            && all_slots(&self.out.term_dag, t).contains(&y)
                            && let Ok(cert_y) = self.class_cert(c, y, g)
                        {
                            // t = ĝ·t ; t = (y g)·t ; t = ĝ⁻¹·t  →  (ĝ∘(y g)∘ĝ⁻¹) = (s g)
                            let s1 = self.out.sym(sym); // t = ĝ⁻¹·t
                            let left = self.trans(sym, cert_y)?; // t = (ĝ∘(y g))·t
                            let r = self.trans(left, s1)?;
                            return Ok(self.retarget(r, g, f));
                        }
                        let z = prop.renaming.apply(s);
                        if z != s
                            && !old.contains_key(&z)
                            && all_slots(&self.out.term_dag, t).contains(&z)
                            && let Ok(cert_z) = self.class_cert(c, z, g)
                        {
                            let s1 = self.out.sym(sym); // t = ĝ⁻¹·t
                            let left = self.trans(s1, cert_z)?; // t = (ĝ⁻¹∘(z g))·t
                            let r = self.trans(left, sym)?;
                            return Ok(self.retarget(r, g, f));
                        }
                    }
                    Err(format!(
                        "no symmetry drops ${s}{}",
                        if errors.is_empty() {
                            String::new()
                        } else {
                            format!(" ({})", errors.join("; "))
                        }
                    ))
                }
                other => Err(format!("no certificate through rule {other}")),
            },
            Justification::MergeFn {
                old_proof,
                new_proof,
                ..
            } => {
                for side in [old_proof, new_proof] {
                    let t = self.egg.get(side).lhs();
                    if let Some((_, args)) = self.app(t)
                        && let Some(cs) = renaming_from_term(self.egg(), args[1])
                        && !cs.contains_key(&s)
                    {
                        return self.cert_from(side, c, s, f);
                    }
                }
                Err("neither merged slot set excludes the slot".into())
            }
            Justification::Congr {
                proof: base,
                child_proof,
                ..
            } => {
                // the row's class moved from c0 to c: certificates transport
                let c0 = self.app(self.egg.get(base).lhs()).ok_or("not a row")?.1[0];
                let e = self.eq(child_proof)?; // c0 = n·c
                let n = self.out.proposition(e).renaming.clone();
                let cert0 = self.class_cert(c0, n.apply(s), n.apply(f))?;
                let q = self.out.sym(e); // c = n⁻¹·c0
                let q = self.note(q);
                self.transport(cert0, q)
            }
            Justification::Trans(a, b) => self
                .cert_from(a, c, s, f)
                .or_else(|_| self.cert_from(b, c, s, f)),
            Justification::Sym(a) => self.cert_from(a, c, s, f),
            Justification::Fiat => Err("a slot set stated by fiat".into()),
            other => Err(format!("no certificate through {other:?}")),
        }
    }

    /// From `P: L = m·R` whose content (`m·R`) does not mention `s`, with `s` a
    /// slot of `L` and `f` unused: `L = (s f)·L`.
    fn lemma(&mut self, p: LiftedId, s: i64, f: i64) -> R<LiftedId> {
        let pc = self.content_form(p); // L = C
        let content = self.out.proposition(pc).rhs;
        let slots = all_slots(&self.out.term_dag, content);
        if !slots.contains(&s) && slots.contains(&f) {
            // `C` must be fixed by (s f): go through a name it lacks, then
            // rename that name to `f`, which `L` lacks
            let g = self.fresh();
            let r = self.lemma(p, s, g)?; // L = (s g)·L
            let r = self.rename_both(r, &Renaming::new([(g, f), (f, g)]).unwrap()); // L = (s f)·L
            return Ok(self.note(r));
        }
        if slots.contains(&s) {
            return Err(format!(
                "the content {} still mentions ${s}",
                self.out_string(content)
            ));
        }
        let tau = Renaming::new([(s, f), (f, s)]).unwrap();
        let rb = self.rename_both(pc, &tau); // τL = τ·C
        let rb = self.out.reframe(rb, tau.clone()); // τL = C, since τ·C is C
        let back = self.out.sym(rb); // C = τL
        let r = self.trans(pc, back)?; // L = τL
        let r = self.out.reframe(r, tau); // L = τ·L
        Ok(self.note(r))
    }

    /// `L = (s f)·L` from `L = (s g)·L`, for `f` and `g` both absent from `L`.
    fn retarget(&mut self, r: LiftedId, g: i64, f: i64) -> LiftedId {
        if g == f {
            return r;
        }
        let r = self.rename_both(r, &Renaming::new([(g, f), (f, g)]).unwrap());
        self.note(r)
    }

    /// From `cert: X = τ·X` and `q: Y = N·X`: `Y = (N∘τ∘N⁻¹)·Y`.
    fn transport(&mut self, cert: LiftedId, q: LiftedId) -> R<LiftedId> {
        let left = self.trans(q, cert)?; // Y = (N∘τ)·X
        let back = self.out.sym(q); // X = N⁻¹·Y
        self.trans(left, back)
    }

    /// `O = (x y)·O` for the occurrence term `O` of class `c` (a renaming of its
    /// term), where `x` is a slot of `O` the class does not depend on and `y` is
    /// not in `O`.
    fn occurrence_cert(&mut self, o: Occurrence, occ: TermId, x: i64, y: i64) -> R<LiftedId> {
        // the occurrence is a renaming of the class's term, or of the row the
        // atom there matched
        let d = self.dec(o.cls)?;
        let mut pairs = BTreeMap::new();
        let (base, rho) = if self.unify_slots(d, occ, &mut pairs).is_ok()
            && let Some(rho) = Renaming::completing(pairs.iter().map(|(k, v)| (*k, *v)))
        {
            (None, rho)
        } else if let Some((row, row_eq)) = o.row {
            let dr = self.dec(row)?;
            let mut pairs = BTreeMap::new();
            self.unify_slots(dr, occ, &mut pairs).map_err(|e| {
                format!(
                    "occurrence {} is neither a renaming of {} nor of {}: {e}",
                    self.out_string(occ),
                    self.out_string(d),
                    self.out_string(dr)
                )
            })?;
            let rho = Renaming::completing(pairs.into_iter())
                .ok_or("non-injective occurrence renaming")?;
            (Some((row, row_eq)), rho)
        } else {
            return Err(format!(
                "occurrence {} is not a renaming of {}",
                self.out_string(occ),
                self.out_string(d)
            ));
        };
        let s = rho.inverse().apply(x);
        let f = rho.inverse().apply(y);
        let cert = match base {
            None => self.class_cert(o.cls, s, f)?, // d = (s f)·d
            Some((_, row_eq)) => {
                // the row's slot through the class: cls = N·row
                let q = self.out.sym(row_eq); // row = N⁻¹·cls
                let q = self.note(q);
                let qp = self.out.proposition(q).clone();
                let through = rename(&mut self.out.term_dag, &qp.renaming, qp.rhs);
                if !all_slots(&self.out.term_dag, through).contains(&s) {
                    // the class's term does not mention it at all
                    self.lemma(q, s, f)?
                } else {
                    let n = self.out.proposition(row_eq).renaming.clone();
                    let cert_cls = self.class_cert(o.cls, n.apply(s), n.apply(f))?;
                    self.transport(cert_cls, q)? // row = (s f)·row
                }
            }
        };
        let lifted = self.rename_both(cert, &rho); // ρX = (ρ∘(s f))·X
        let lifted = self.out.reframe(lifted, rho); // ρX = (ρ∘(s f)∘ρ⁻¹)·ρX
        Ok(self.note(lifted))
    }

    /// `O = (x y ..)·O` for the occurrence term `O` of class `c`: a symmetry of
    /// the class that sends `x` to `y`, spelled on the occurrence.
    fn occurrence_symmetry(&mut self, o: Occurrence, occ: TermId, x: i64, y: i64) -> R<LiftedId> {
        let d = self.dec(o.cls)?;
        let mut pairs = BTreeMap::new();
        let (base, rho) = if self.unify_slots(d, occ, &mut pairs).is_ok()
            && let Some(rho) = Renaming::completing(pairs.iter().map(|(k, v)| (*k, *v)))
        {
            (None, rho)
        } else if let Some((row, row_eq)) = o.row {
            let dr = self.dec(row)?;
            let mut pairs = BTreeMap::new();
            self.unify_slots(dr, occ, &mut pairs)?;
            let rho = Renaming::completing(pairs.into_iter())
                .ok_or("non-injective occurrence renaming")?;
            (Some((row, row_eq)), rho)
        } else {
            return Err(format!(
                "occurrence {} is not a renaming of {}",
                self.out_string(occ),
                self.out_string(d)
            ));
        };
        let (s, f) = (rho.inverse().apply(x), rho.inverse().apply(y));
        // in the class's own coordinates
        let n = match base {
            None => Renaming::identity(),
            Some((_, row_eq)) => self.out.proposition(row_eq).renaming.clone(),
        };
        let (cs, cf) = (n.apply(s), n.apply(f));
        let mut errors = vec![];
        let mut sym: Option<LiftedId> = None;
        for proof in self.group_proofs(o.cls) {
            let elements = match self.group_of_row(self.egg.get(proof).lhs()) {
                Ok(e) => e,
                Err(e) => {
                    errors.push(e);
                    continue;
                }
            };
            for g in elements.iter().filter(|g| g.get(&cs) == Some(&cf)) {
                match self.symmetry(o.cls, g, proof) {
                    Ok(p) => {
                        sym = Some(p);
                        break;
                    }
                    Err(e) => errors.push(e),
                }
            }
            if sym.is_some() {
                break;
            }
        }
        let Some(cert) = sym else {
            return Err(format!(
                "no symmetry of {} sends ${cs} to ${cf}{}",
                self.out_string(d),
                if errors.is_empty() {
                    String::new()
                } else {
                    format!(" ({})", errors.join("; "))
                }
            ));
        };
        let cert = match base {
            None => cert,
            Some((_, row_eq)) => {
                let q = self.out.sym(row_eq); // row = N⁻¹·cls
                let q = self.note(q);
                self.transport(cert, q)?
            }
        };
        let lifted = self.rename_both(cert, &rho);
        let lifted = self.out.reframe(lifted, rho);
        Ok(self.note(lifted))
    }

    /// Every proof in the egglog store of a group row of `cls`.
    fn group_proofs(&mut self, cls: TermId) -> Vec<ProofId> {
        self.group_index
            .get_or_insert_with(|| row_proofs(self.egg, "EclassGroup_"))
            .get(&cls)
            .cloned()
            .unwrap_or_default()
    }

    /// Apply a child proof at a path below the right-hand side of `p`.
    fn congr_at(&mut self, p: LiftedId, path: &[usize], cert: LiftedId) -> R<LiftedId> {
        let (first, rest) = path.split_first().ok_or("empty path")?;
        let child = if rest.is_empty() {
            cert
        } else {
            let refl = self.out.project(p, *first).map_err(|e| e.0)?;
            self.congr_at(refl, rest, cert)?
        };
        let r = self.out.congr(p, *first, child).map_err(|e| e.0)?;
        Ok(self.note(r))
    }

    /// Reframe `p`'s content onto `target`, renaming redundant slots at the
    /// occurrences where a plain bijection fails.
    fn fit(
        &mut self,
        p: LiftedId,
        target: TermId,
        occ: &HashMap<Vec<usize>, Occurrence>,
    ) -> R<LiftedId> {
        let mut p = self.content_form(p);
        for _ in 0..64 {
            let content = self.out.proposition(p).rhs;
            if content == target {
                return Ok(p);
            }
            let mut pairs: Vec<(Vec<usize>, i64, i64)> = vec![];
            self.slot_pairs(content, target, &mut vec![], &mut pairs)?;
            // a bijection where it is one; a conflict names both positions, since
            // either may be the one holding a redundant slot
            let mut beta: BTreeMap<i64, (i64, Vec<usize>)> = BTreeMap::new();
            let mut inverse_beta: BTreeMap<i64, (i64, Vec<usize>)> = BTreeMap::new();
            let mut conflict: Option<Vec<(Vec<usize>, i64, i64)>> = None;
            for (path, x, t) in &pairs {
                match (beta.get(x), inverse_beta.get(t)) {
                    (Some((t0, path0)), _) if t0 != t => {
                        conflict = Some(vec![(path.clone(), *x, *t), (path0.clone(), *x, *t0)]);
                        break;
                    }
                    (None, Some((x0, path0))) if x0 != x => {
                        conflict = Some(vec![(path.clone(), *x, *t), (path0.clone(), *x0, *t)]);
                        break;
                    }
                    _ => {
                        beta.insert(*x, (*t, path.clone()));
                        inverse_beta.insert(*t, (*x, path.clone()));
                    }
                }
            }
            let beta: BTreeMap<i64, i64> = beta.iter().map(|(k, (v, _))| (*k, *v)).collect();
            let inverse_beta: BTreeMap<i64, i64> =
                inverse_beta.iter().map(|(k, (v, _))| (*k, *v)).collect();
            let Some(candidates) = conflict else {
                let sigma = Renaming::completing(beta.into_iter()).ok_or("non-bijective fit")?;
                let r = self.out.reframe(p, sigma);
                let got = self.out.proposition(r).rhs;
                if got != target {
                    return Err(format!(
                        "fitting {} onto {} produced {}",
                        self.out_string(content),
                        self.out_string(target),
                        self.out_string(got)
                    ));
                }
                return Ok(self.note(r));
            };
            // the names each position may take: the target's, the slot already
            // sent to the target's, and only then a fresh one -- a fresh name is
            // progress only where nothing names the slot's destination
            let mut attempts: Vec<(Vec<usize>, i64, i64)> = vec![];
            for (path, x, t) in &candidates {
                if *t != *x {
                    attempts.push((path.clone(), *x, *t));
                }
                if let Some(&x0) = inverse_beta.get(t)
                    && x0 != *x
                {
                    attempts.push((path.clone(), *x, x0));
                }
            }
            for (path, x, _) in &candidates {
                let f = self.fresh();
                attempts.push((path.clone(), *x, f));
            }
            let mut errors: Vec<String> = vec![];
            let mut found: Option<(Vec<usize>, LiftedId)> = None;
            let mut any = false;
            'attempts: for (path, x, want) in attempts {
                // the occurrences holding this position, innermost first: the
                // slot may be redundant in any of them, or a symmetry of one may
                // move it
                let mut occ_path = path.clone();
                loop {
                    if let Some(&cls) = occ.get(&occ_path) {
                        any = true;
                        let o = self.subterm_at(content, &occ_path)?;
                        if all_slots(&self.out.term_dag, o).contains(&want) {
                            match self.occurrence_symmetry(cls, o, x, want) {
                                Ok(sym) => {
                                    found = Some((occ_path, sym));
                                    break 'attempts;
                                }
                                Err(e) => errors.push(format!(
                                    "slot ${x} of {} would have to become ${want}, which it also holds ({e})",
                                    self.out_string(o)
                                )),
                            }
                        } else {
                            match self.occurrence_cert(cls, o, x, want) {
                                Ok(cert) => {
                                    found = Some((occ_path, cert));
                                    break 'attempts;
                                }
                                Err(e) => errors.push(e),
                            }
                        }
                    }
                    if occ_path.pop().is_none() {
                        break;
                    }
                }
            }
            if !any {
                errors.push("no occurrence holds the conflicting slots".to_string());
            }
            let Some((occ_path, cert)) = found else {
                return Err(format!(
                    "fitting {} onto {}: {}",
                    self.out_string(content),
                    self.out_string(target),
                    errors.join("; ")
                ));
            };
            if occ_path.is_empty() {
                // the whole content: compose directly
                p = self.trans(p, cert)?;
                p = self.content_form(p);
            } else {
                p = self.congr_at(p, &occ_path, cert)?;
                p = self.content_form(p);
            }
            if self.out.proposition(p).rhs == content {
                return Err(format!(
                    "fitting {} onto {}: a certificate changed nothing: {} at {occ_path:?}\n{}",
                    self.out_string(content),
                    self.out_string(target),
                    self.prop_string(cert),
                    self.out.proof_to_string(cert)
                ));
            }
        }
        let content = self.out.proposition(p).rhs;
        Err(format!(
            "fitting {} onto {} did not converge",
            self.out_string(content),
            self.out_string(target)
        ))
    }

    /// Rename the free slots of `p`'s content, one certificate at a time, until
    /// they are the target's; bound names are left to the final coordinate alignment. Fails where
    /// a free slot that differs is not redundant.
    fn fit_content(
        &mut self,
        p: LiftedId,
        target: TermId,
        occ: &HashMap<Vec<usize>, Occurrence>,
    ) -> R<LiftedId> {
        let mut p = self.content_form(p);
        for _ in 0..64 {
            let content = self.out.proposition(p).rhs;
            let free = self.program.free_slots(&self.out.term_dag, content);
            let mut pairs: Vec<(Vec<usize>, i64, i64)> = vec![];
            self.slot_pairs(content, target, &mut vec![], &mut pairs)?;
            let differing: Vec<&(Vec<usize>, i64, i64)> = pairs
                .iter()
                .filter(|(_, x, t)| x != t && free.contains(x))
                .collect();
            let slots = all_slots(&self.out.term_dag, content);
            // a slot whose target name is free to take, else any (through a
            // fresh name, to break a cycle)
            let chosen = differing
                .iter()
                .find(|(_, _, t)| !slots.contains(t))
                .or(differing.first())
                .cloned()
                .cloned();
            let Some((path, x, t)) = chosen else {
                return self.fit(p, target, occ);
            };
            let want = if slots.contains(&t) { self.fresh() } else { t };
            log::debug!(
                "content fit: {} onto {}: ${x} at {path:?} -> ${want}",
                self.out_string(content),
                self.out_string(target)
            );
            let mut occ_path = path.clone();
            let mut errors = Vec::new();
            let (sub, cert) = loop {
                if let Some(&o) = occ.get(&occ_path) {
                    let sub = self.subterm_at(content, &occ_path)?;
                    match self.occurrence_cert(o, sub, x, want) {
                        Ok(cert) => break (sub, cert),
                        Err(error) => errors.push(error),
                    }
                }
                if occ_path.pop().is_none() {
                    return Err(errors.join("; "));
                }
            };
            log::debug!("content fit certificate: {}", self.prop_string(cert));
            p = if occ_path.is_empty() {
                self.trans(p, cert)?
            } else {
                self.congr_at(p, &occ_path, cert)?
            };
            p = self.content_form(p);
            if self.out.proposition(p).rhs == content {
                return Err(format!(
                    "the certificate for ${x} in {} changed nothing: {}\n{}",
                    self.out_string(sub),
                    self.prop_string(cert),
                    self.out.proof_to_string(cert)
                ));
            }
        }
        Err("content fitting did not converge".into())
    }

    fn subterm_at(&self, term: TermId, path: &[usize]) -> R<TermId> {
        let mut t = term;
        for &j in path {
            t = match self.out.term_dag.get(t) {
                Term::App(_, kids) => *kids.get(j).ok_or("path out of range")?,
                _ => return Err("path into a non-application".into()),
            };
        }
        Ok(t)
    }

    fn slot_pairs(
        &self,
        a: TermId,
        b: TermId,
        path: &mut Vec<usize>,
        out: &mut Vec<(Vec<usize>, i64, i64)>,
    ) -> R<()> {
        let dag = &self.out.term_dag;
        match (dag.get(a).clone(), dag.get(b).clone()) {
            (Term::Var(_), Term::Var(_)) => {
                match (super::terms::slot_of(dag, a), super::terms::slot_of(dag, b)) {
                    (Some(x), Some(y)) => {
                        out.push((path.clone(), x, y));
                        Ok(())
                    }
                    _ if a == b => Ok(()),
                    _ => Err(format!(
                        "cannot fit {} to {}",
                        self.out_string(a),
                        self.out_string(b)
                    )),
                }
            }
            (Term::Lit(x), Term::Lit(y)) if x == y => Ok(()),
            (Term::App(h1, c1), Term::App(h2, c2)) if h1 == h2 && c1.len() == c2.len() => {
                for (j, (x, y)) in c1.iter().zip(c2.iter()).enumerate() {
                    path.push(j);
                    self.slot_pairs(*x, *y, path, out)?;
                    path.pop();
                }
                Ok(())
            }
            _ => Err(format!(
                "cannot fit {} to {}",
                self.out_string(a),
                self.out_string(b)
            )),
        }
    }

    // ----- the claim ----------------------------------------------------------------

    fn claim(
        &mut self,
        root: ProofId,
        claim: &Claim,
        query: &ProofNames,
        roots: [&str; 2],
    ) -> R<LiftedId> {
        let frame = matched_frame(self.egg, root, query)?;
        let coset = Self::coset_symmetry(&frame, roots)?;
        let root = query_firing(self.egg, root, &query.frame)?;
        let proof = self.egg.get(root).clone();
        let Justification::Rule {
            premise_proofs,
            substitution,
            ..
        } = proof.justification().clone()
        else {
            unreachable!("query_firing returns a rule firing")
        };
        let classes = roots.map(|root| {
            query
                .classes
                .get(root)
                .ok_or_else(|| format!("no class binding for claim root {root}"))
        });
        let [class_a, class_b] = classes;
        let cls_a = self.sub(&substitution, class_a?)?;
        let cls_b = self.sub(&substitution, class_b?)?;
        let bare = |this: &Self, t: TermId| super::terms::slot_of(&this.out.term_dag, t).is_some();
        if bare(self, claim.lhs) && bare(self, claim.rhs) {
            // both sides are bare slots: one class, the variable's
            if cls_a != cls_b {
                return Err("two bare slots with different classes".into());
            }
            let t = self.dec(cls_a)?;
            let r = self.reflexive(t)?;
            let src_a = self
                .program
                .refresh_binders(&mut self.out.term_dag, claim.lhs);
            let src_b = self
                .program
                .refresh_binders(&mut self.out.term_dag, claim.rhs);
            let pa = self.align(r, src_a)?; // $0 = ·src_a
            let pb = self.align(r, src_b)?; // $0 = ·src_b
            let sa = self.out.sym(pa);
            let result = self.trans(sa, pb)?;
            return self.finish_claim(
                result,
                pb,
                claim,
                cls_a,
                &premise_proofs,
                Some(&coset),
                &HashMap::default(),
            );
        }
        let bridges = HashMap::default();
        let side = |i: usize| -> R<ExpandCtx<'_>> {
            let names = query.patterns.get(i).ok_or("missing claim pattern names")?;
            Ok(ExpandCtx {
                prems: &premise_proofs,
                subst: &substitution,
                classes: query.classes.clone(),
                readings: query.readings.clone(),
                names: names.iter().cloned().collect(),
                bridges: &bridges,
            })
        };
        let src_a = self
            .program
            .refresh_binders(&mut self.out.term_dag, claim.lhs);
        let src_b = self
            .program
            .refresh_binders(&mut self.out.term_dag, claim.rhs);
        let ctx_a = side(0)?;
        let Expansion {
            proof: pa,
            occurrences: occ_a,
            ..
        } = self.expand(cls_a, claim.lhs, &[], &ctx_a, HashMap::default())?;
        let pa = self.fit(pa, src_a, &occ_a)?; // cls_a = ·src_a
        let ctx_b = side(1)?;
        let Expansion {
            proof: pb,
            occurrences: occ_b,
            ..
        } = self.expand(cls_b, claim.rhs, &[], &ctx_b, HashMap::default())?;
        for (path, o) in &occ_b {
            log::debug!(
                "claim side b occurrence {path:?}: {}",
                self.egg_string(o.cls)
            );
        }
        let pb = self.fit(pb, src_b, &occ_b)?; // cls_b = ·src_b
        let e = if cls_a == cls_b {
            let t = self.dec(cls_a)?;
            self.reflexive(t)?
        } else {
            let prem = premise_proofs
                .iter()
                .copied()
                .find(|p| {
                    let pr = self.egg.get(*p);
                    (pr.lhs(), pr.rhs()) == (cls_a, cls_b)
                })
                .ok_or("the claim has no proof of its class equality")?;
            self.eq(prem)?
        };
        let sa = self.out.sym(pa);
        let left = self.trans(sa, e)?;
        let result = self.trans(left, pb)?;
        self.finish_claim(
            result,
            pb,
            claim,
            cls_a,
            &premise_proofs,
            Some(&coset),
            &occ_b,
        )
    }

    /// `result: src_a = M·src_b` says what the claim says once `M` leaves the
    /// free slots of `src_b` alone; redundant slots and the symmetry `coset-same`
    /// chose can fix it.
    #[allow(clippy::too_many_arguments)]
    fn finish_claim(
        &mut self,
        result: LiftedId,
        pb: LiftedId,
        claim: &Claim,
        cls_a: TermId,
        premise_proofs: &[ProofId],
        coset: Option<&SlotMap>,
        occ_b: &HashMap<Vec<usize>, Occurrence>,
    ) -> R<LiftedId> {
        if claim.kind == super::source::ClaimKind::RenamingEq {
            return Ok(result);
        }
        let src_b = self.out.proposition(pb).rhs;
        let src_a = self.out.proposition(result).lhs;
        let free = self.program.free_slots(&self.out.term_dag, src_b);
        let free_a = self.program.free_slots(&self.out.term_dag, src_a);
        let result = self.fix_redundant(result, pb, src_b, &free)?;
        let result = match self.fit_content(result, src_b, occ_b) {
            Ok(r) => r,
            Err(e) => {
                log::debug!("content fit of the claim failed: {e}");
                result
            }
        };
        let prop = self.out.normalize(self.out.proposition(result).clone());
        if !prop.renaming.moves_any(&free) || !prop.renaming.moves_any(&free_a) {
            return Ok(result);
        }
        // try the symmetry coset-same picked, in either direction
        if let Some(g) = coset {
            let grp_proof = premise_proofs
                .iter()
                .copied()
                .find(|p| {
                    let t = self.egg.get(*p).lhs();
                    self.app(t).is_some_and(|(h, a)| {
                        h.starts_with("EclassGroup_") && a.first() == Some(&cls_a)
                    })
                })
                .ok_or("claim without a group row")?;
            let t = self.dec(cls_a)?;
            let mut notes: Vec<String> = vec![];
            for cand in [g.clone(), inverse(g)] {
                let s = match self.symmetry(cls_a, &cand, grp_proof) {
                    Ok(s) => s,
                    Err(e) => {
                        notes.push(format!("symmetry {}: {e}", slot_map_string(&cand)));
                        continue;
                    }
                };
                {
                    // insert the symmetry where the chain passes through the class
                    let Some(at) = self.known.get(&t).copied() else {
                        continue;
                    };
                    let _ = at;
                    // rebuild: result = (src_a = ·cls_a) ; sym ; (cls_a = ·src_b)
                    let to_class = self.chain_to(result, t);
                    let Some((left, right)) = to_class else {
                        continue;
                    };
                    let left = self.trans(left, s)?;
                    let r = self.trans(left, right)?;
                    let r = self.fix_redundant(r, pb, src_b, &free)?;
                    // a redundant slot the symmetry exposed, as on the main path
                    let r = match self.fit_content(r, src_b, occ_b) {
                        Ok(r) => r,
                        Err(e) => {
                            log::debug!("content fit after the symmetry failed: {e}");
                            r
                        }
                    };
                    let prop = self.out.normalize(self.out.proposition(r).clone());
                    if !prop.renaming.moves_any(&free) || !prop.renaming.moves_any(&free_a) {
                        return Ok(r);
                    }
                    notes.push(format!(
                        "with symmetry {}: {}",
                        slot_map_string(&cand),
                        self.prop_string(r)
                    ));
                }
            }
            return Err(format!(
                "the claim's proof came out as {} which moves a free slot of {} ({})",
                self.prop_string(result),
                self.out_string(src_b),
                notes.join("; ")
            ));
        }
        Err(format!(
            "the claim's proof came out as {} which moves a free slot of {}",
            self.prop_string(result),
            self.out_string(src_b)
        ))
    }

    /// Split a transitivity chain at the proof whose right-hand side is `mid`:
    /// `(lhs = ·mid, mid = ·rhs)`.
    fn chain_to(&mut self, proof: LiftedId, mid: TermId) -> Option<(LiftedId, LiftedId)> {
        match self.out.chain(proof) {
            Some((a, b)) => {
                if self.out.proposition(a).rhs == mid {
                    return Some((a, b));
                }
                if let Some((a1, a2)) = self.chain_to(a, mid) {
                    let right = self.out.trans(a2, b).ok()?;
                    return Some((a1, right));
                }
                if let Some((b1, b2)) = self.chain_to(b, mid) {
                    let left = self.out.trans(a, b1).ok()?;
                    return Some((left, b2));
                }
                None
            }
            _ => None,
        }
    }

    /// Where `result: src_a = M·src_b` moves a free slot `s` of `src_b` to a slot
    /// absent from `src_b`, and the class term `pb` reaches `src_b` through lacks
    /// both, the slot is redundant: `src_b = (s u)·src_b` follows, and composing it
    /// in fixes `s`.
    fn fix_redundant(
        &mut self,
        mut result: LiftedId,
        pb: LiftedId,
        src_b: TermId,
        free: &BTreeSet<i64>,
    ) -> R<LiftedId> {
        let src_slots = all_slots(&self.out.term_dag, src_b);
        let to_class = self.out.sym(pb); // src_b = ·cls_b
        for _ in 0..free.len() + 1 {
            let m = self
                .out
                .normalize(self.out.proposition(result).clone())
                .renaming;
            let Some(&s) = free.iter().find(|s| m.apply(**s) != **s) else {
                return Ok(result);
            };
            let u = m.inverse().apply(s);
            if src_slots.contains(&u) {
                return Ok(result);
            }
            let tau = Renaming::new([(s, u), (u, s)]).unwrap();
            let renamed = self.rename_both(to_class, &tau); // τ·src_b = ·cls_b
            let (p1, p2) = (
                self.out.normalize(self.out.proposition(to_class).clone()),
                self.out.normalize(self.out.proposition(renamed).clone()),
            );
            if p1.renaming != p2.renaming || p1.rhs != p2.rhs {
                return Ok(result);
            }
            let back = self.out.sym(renamed);
            let cert = self.trans(to_class, back)?; // src_b = ·(τ·src_b)
            let cert = self.out.reframe(cert, tau.inverse()); // src_b = τ·src_b
            let cert = self.note(cert);
            result = self.trans(result, cert)?;
        }
        Ok(result)
    }

    /// The group element relating the roots in their shared query frame.
    fn coset_symmetry(frame: &Fr, roots: [&str; 2]) -> R<SlotMap> {
        let a = frame.ren(roots[0]).ok_or("claim frame has no left root")?;
        let b = frame.ren(roots[1]).ok_or("claim frame has no right root")?;
        Ok(compose(&inverse(&b), &a))
    }
}

impl RowKind {
    fn is_edge(&self) -> bool {
        matches!(self, RowKind::Edge)
    }
}

/// `a ∘ b`: `b` applies first; undefined wherever either step is.
fn compose(a: &SlotMap, b: &SlotMap) -> SlotMap {
    b.iter()
        .filter_map(|(x, y)| a.get(y).map(|z| (*x, *z)))
        .collect()
}

fn inverse(a: &SlotMap) -> SlotMap {
    a.iter().map(|(k, v)| (*v, *k)).collect()
}

fn is_identity(g: &SlotMap) -> bool {
    g.iter().all(|(k, v)| k == v)
}

fn slot_map_string(g: &SlotMap) -> String {
    let entries: Vec<String> = g.iter().map(|(k, v)| format!("{k}->{v}")).collect();
    format!("{{{}}}", entries.join(", "))
}

/// Each column's edge through every element of its child's group that permutes
/// the column's slots, as `node-shape` reads a row; with the elements chosen.
fn readings(edges: &[SlotMap], groups: &[Vec<SlotMap>]) -> Vec<(Vec<SlotMap>, Vec<SlotMap>)> {
    let columns: Vec<Vec<(SlotMap, SlotMap)>> = edges
        .iter()
        .enumerate()
        .map(|(i, edge)| {
            let domain: BTreeSet<i64> = edge.keys().copied().collect();
            let identity: SlotMap = domain.iter().map(|s| (*s, *s)).collect();
            let mut out: Vec<(SlotMap, SlotMap)> = vec![(edge.clone(), identity)];
            for g in groups.get(i).map(Vec::as_slice).unwrap_or_default() {
                if g.keys().copied().collect::<BTreeSet<_>>() == domain
                    && g.values().copied().collect::<BTreeSet<_>>() == domain
                {
                    let read: SlotMap = g.iter().map(|(&s, &t)| (s, edge[&t])).collect();
                    if !out.iter().any(|(r, _)| *r == read) {
                        out.push((read, g.clone()));
                    }
                }
            }
            out
        })
        .collect();
    let total: usize = columns.iter().map(Vec::len).product();
    (0..total)
        .map(|mut n| {
            let mut variant = Vec::with_capacity(columns.len());
            let mut chosen = Vec::with_capacity(columns.len());
            for column in &columns {
                let (read, g) = &column[n % column.len()];
                variant.push(read.clone());
                chosen.push(g.clone());
                n /= column.len();
            }
            (variant, chosen)
        })
        .collect()
}

#[allow(dead_code)]
fn slot_set_string(s: &SlotSet) -> String {
    format!("{:?}", s.iter().collect::<Vec<_>>())
}

#[allow(dead_code)]
fn renamings_of(dag: &TermDag, t: TermId) -> Option<Vec<SlotMap>> {
    renamings_from_term(dag, t)
}

#[cfg(test)]
pub(super) fn check_restricted_symmetries(
    program: &SlottedProgram,
    dag: TermDag,
    names: &EncodingNames,
    egg: &ProofStore,
) -> R<usize> {
    let mut tr = Translator::new(program, dag, names, egg);
    let mut checked = 0;
    for (id, proof) in egg.proofs() {
        let Justification::Rule {
            name,
            substitution,
            premise_proofs,
        } = proof.justification()
        else {
            continue;
        };
        if rule_kind(program, name).1 != "group-shrink" {
            continue;
        }
        let old = tr.group(substitution["_s"])?;
        let slots = tr.slot_map(substitution["_cs"])?;
        if old
            .iter()
            .all(|g| g.keys().all(|slot| slots.contains_key(slot)))
        {
            continue;
        }
        let restored = egg
            .proofs()
            .find_map(|(restored, proof)| match proof.justification() {
                Justification::Rule {
                    name,
                    premise_proofs,
                    ..
                } if rule_kind(program, name).1 == "group-restore"
                    && premise_proofs.first() == Some(&id) =>
                {
                    Some(restored)
                }
                _ => None,
            })
            .ok_or("restricted group has no restore proof")?;
        let (_, args) = tr.app(proof.lhs()).ok_or("expected staged group row")?;
        let class = args[0];
        for generator in old {
            let restricted = compose(&slots, &compose(&generator, &slots));
            if is_identity(&restricted) || restricted.len() == generator.len() {
                continue;
            }
            let symmetry = tr.product_symmetry(
                class,
                &restricted,
                &[(generator, premise_proofs[0])],
                Some(&slots),
            )?;
            let proof = tr.out.proof(symmetry);
            super::checker::check_proof(&mut tr.out, program, proof).map_err(|e| e.to_string())?;
            checked += 1;
        }
        for g in tr.group(args[1])? {
            if is_identity(&g) {
                continue;
            }
            let symmetry = tr.symmetry(class, &g, restored)?;
            let proof = tr.out.proof(symmetry);
            super::checker::check_proof(&mut tr.out, program, proof).map_err(|e| e.to_string())?;
        }
    }
    Ok(checked)
}
