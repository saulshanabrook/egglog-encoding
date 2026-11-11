//! Lift an egglog proof over the encoded program to a slotted proof
//! over surface terms; see *Slot lifting* in `egglog-experimental/src/slotted/PROOFS.md`.
//!
//! Encoded rows are interpreted as ordinary surface equalities. The lifting
//! rules and their derivations are described in the proof guide above.

use super::context::{ColumnKind, ProofContext, SourceFact, pattern_term};
use super::coordinates::{Coordinates, ViewId};
use super::format::{Claim, SlottedProofStore};
use super::pipeline::EncodingNames;
use super::terms::{
    FreshSlots, Renaming, TermShapes, all_slots, rename, slot_of, slot_term, term_renaming,
};

use super::{HashMap, HashSet};
use crate::slotted::query::ProofNames;
use crate::slotted::runtime::frame_from_term;
use crate::slotted::runtime::renaming::node_shape_with;
use crate::slotted::runtime::terms::{group_from_term, renaming_from_term};
use crate::slotted::runtime::{Fr, Renaming as SlotMap};
use egglog::ast::Literal;
use egglog::proof::{Justification, ProofId, ProofStore, Proposition};
use egglog::util::IndexMap;
use egglog::{Term, TermDag, TermId};
use std::collections::{BTreeMap, BTreeSet};

mod certificates;
mod claim;
mod decode;
mod equality;
mod matching;
mod permutations;
mod rewrite;
mod rule_kind;
mod shape;
pub(super) mod source;
mod symmetry;

use permutations::{compose, inverse, is_identity, slot_map_string};
use rule_kind::{RuleKind, rule_kind};
use shape::ShapeKey;

type LiftResult<T> = Result<T, String>;
type SymmetryPremises = Vec<Option<(TermId, ProofId)>>;

/// Lift the egglog proof `root`, which proves the encoded form of `claim`,
/// into a slotted proof of the claim over `dag`, the program's term dag.
/// `query` records the generated bindings and `roots` identifies its two sides.
#[allow(clippy::too_many_arguments)]
pub(super) fn lift(
    program: &ProofContext,
    dag: TermDag,
    names: &EncodingNames,
    egg: NativeProofs<'_>,
    root: ProofId,
    claim: &Claim,
    query: &ProofNames,
    roots: [&str; 2],
    patterns: [TermId; 2],
    evidence: &source::Certificates,
) -> LiftResult<(SlottedProofStore, ProofId)> {
    let mut tr = SlotLifter::with_evidence(program, dag, names, egg, evidence)?;
    let id = tr.claim(root, claim, query, roots, patterns)?;
    Ok(tr.out.finish(id))
}

/// Recover one substitution from the single firing that witnessed the complete
/// query. All facts use it, including repeated term and payload variables.
#[allow(clippy::too_many_arguments)]
pub(super) fn query_witness(
    program: &ProofContext,
    query_program: &ProofContext,
    dag: &mut TermDag,
    names: &EncodingNames,
    egg: NativeProofs<'_>,
    root: ProofId,
    claims: &[super::pipeline::SlottedClaim],
    evidence: &source::Certificates,
) -> LiftResult<HashMap<String, TermId>> {
    use egglog::ast::Expr;
    fn pattern(dag: &mut TermDag, program: &ProofContext, expr: &Expr) -> TermId {
        match expr {
            Expr::Var(_, name) => program
                .lets
                .get(name)
                .copied()
                .unwrap_or_else(|| dag.var(name.clone())),
            Expr::Lit(_, value) => dag.lit(value.clone()),
            Expr::Call(_, head, args) => {
                let args = args
                    .iter()
                    .enumerate()
                    .map(|(i, arg)| {
                        if matches!(
                            program.constructors[head].columns[i],
                            ColumnKind::Payload(_)
                        ) && let Expr::Var(_, name) = arg
                        {
                            dag.var(name.clone())
                        } else {
                            pattern(dag, program, arg)
                        }
                    })
                    .collect();
                dag.app(head.clone(), args)
            }
        }
    }
    let locals: BTreeSet<_> = claims
        .iter()
        .flat_map(|claim| {
            query_program
                .query_variables(&claim.lhs)
                .into_iter()
                .chain(query_program.query_variables(&claim.rhs))
        })
        .collect();
    if locals.is_empty() {
        return Ok(HashMap::default());
    }
    let mut tr = SlotLifter::with_evidence(program, dag.clone(), names, egg, evidence)?;
    let query = &claims[0].names;
    let frame = matched_frame(egg.store, root, query)?;
    let firing = query_firing(egg.store, root, &query.frame)?;
    let Justification::Rule {
        premise_proofs,
        substitution,
        ..
    } = egg.get(firing).justification()
    else {
        unreachable!()
    };
    let bridges = HashMap::default();
    let selected = tr.selected_readings(firing, None, substitution)?;
    let mut sigma = HashMap::default();
    let mut contents = Vec::new();
    for claim in claims {
        for (i, (expr, name)) in [(&claim.lhs, &claim.lhs_root), (&claim.rhs, &claim.rhs_root)]
            .into_iter()
            .enumerate()
        {
            if query_program.query_variables(expr).is_empty() {
                continue;
            }
            let pattern = pattern(&mut tr.out.term_dag, query_program, expr);
            let class = tr.sub(substitution, &query.classes[name])?;
            let ctx = ExpandCtx {
                firing,
                root_binding: query.classes.get(name).cloned(),
                prems: premise_proofs,
                subst: substitution,
                names: claim.names.patterns[i].iter().cloned().collect(),
                readings: query.readings.clone(),
                labels: &query.atoms,
                selected: &selected,
                bridges: &bridges,
            };
            let Expansion {
                proof,
                variables,
                slots,
                ..
            } = tr.expand(class, pattern, &[], &ctx, HashMap::default())?;
            let proof = tr.lift(proof, &frame, &slots)?;
            contents.push((pattern, tr.out.edge(proof).rhs));
            for (variable, occurrence) in variables {
                if let Some(mapping) = frame.ren(&variable) {
                    let term = tr.dec(occurrence.cls)?;
                    let renaming = tr.complete(&mapping, term);
                    let term = rename(&mut tr.out.term_dag, &renaming, term);
                    sigma.insert(variable, term);
                }
            }
        }
    }
    for (pattern, content) in contents {
        tr.bind_from_content(pattern, content, &mut sigma)?;
    }
    let coordinates = query_program
        .slot_names
        .iter()
        .filter_map(|(name, slot)| {
            frame
                .ren(name)
                .and_then(|r| r.get(&0).copied())
                .map(|at| (at, *slot))
        })
        .chain(
            program
                .slot_names
                .values()
                .filter_map(|slot| frame.node_slot("@globals", *slot).map(|at| (at, *slot))),
        );
    let to_source = Renaming::completing(coordinates).ok_or("non-injective query coordinates")?;
    sigma.retain(|name, _| locals.contains(name));
    for term in sigma.values_mut() {
        *term = rename(&mut tr.out.term_dag, &to_source, *term);
    }
    *dag = tr.out.term_dag.clone();
    Ok(sigma)
}

fn query_firing(egg: &ProofStore, root: ProofId, frame: &str) -> LiftResult<ProofId> {
    fn side(egg: &ProofStore, root: ProofId, rhs: bool, frame: &str) -> LiftResult<ProofId> {
        match egg.get(root).justification() {
            Justification::Rule { substitution, .. } if substitution.contains_key(frame) => {
                Ok(root)
            }
            Justification::Congr { proof, .. } => side(egg, *proof, rhs, frame),
            Justification::Sym(proof) => side(egg, *proof, !rhs, frame),
            Justification::Trans(a, b) => side(egg, if rhs { *b } else { *a }, rhs, frame),
            _ => Err(format!("existence proof has no query binding {frame}")),
        }
    }
    side(egg, root, true, frame)
}

pub(super) fn matched_frame(egg: &ProofStore, root: ProofId, names: &ProofNames) -> LiftResult<Fr> {
    let root = query_firing(egg, root, &names.frame)?;
    let Justification::Rule { substitution, .. } = egg.get(root).justification() else {
        unreachable!("query_firing returns a rule firing")
    };
    frame_from_term(egg.term_dag(), substitution[&names.frame])
        .ok_or_else(|| "query frame is not a frame".into())
}

#[derive(Clone, Copy)]
pub(super) struct NativeProofs<'a> {
    pub store: &'a ProofStore,
    pub program: &'a [egglog::ast::ResolvedNCommand],
}

impl std::ops::Deref for NativeProofs<'_> {
    type Target = ProofStore;
    fn deref(&self) -> &Self::Target {
        self.store
    }
}

struct SlotLifter<'a, E = NativeProofs<'a>> {
    program: &'a ProofContext,
    names: &'a EncodingNames,
    egg: E,
    out: Coordinates,
    /// Encoded term -> its surface term.
    dec_memo: HashMap<TermId, TermId>,
    /// (encoded node, surface column) -> the permutation that completed the
    /// column's edge when the node was decoded.
    edge_memo: HashMap<(TermId, usize), Renaming>,
    /// Egglog proof -> the slotted proof of the equality it denotes.
    eq_memo: HashMap<ProofId, ViewId>,
    symmetry_memo: HashMap<(ProofId, bool, TermId, SlotMap), ViewId>,
    rule_instances: HashMap<rewrite::FiringKey, rewrite::RuleInstance>,
    anchors: HashMap<ProofId, ProofId>,
    /// Source support certificates for restricted children of recorded heads.
    head_supports: HashMap<(ProofId, usize), ProofId>,
    /// Surface term -> a slotted proof whose left side it is, from which its
    /// reflexivity follows.
    known: HashMap<TermId, ViewId>,
    /// A node spelled with canonical edges, shared by every row that has that shape.
    shape_terms: HashMap<ShapeKey, TermId>,
    /// Slot-insensitive hashes; equal hashes still require structural comparison.
    term_shapes: TermShapes,
    fresh: FreshSlots,
    reserved_terms: usize,
}

/// A pattern position's class, and the row an atom there matched.
#[derive(Clone, Copy)]
struct Occurrence {
    cls: TermId,
    row: Option<(TermId, ViewId)>,
    support: Option<Support>,
}

/// Recorded support evidence, optionally transported to the current class.
#[derive(Clone, Copy)]
struct Support {
    origin: SupportOrigin,
    transport: Option<ViewId>,
}

#[derive(Clone, Copy)]
enum SupportOrigin {
    /// A FreeVars row, or the selected endpoint of an encoded equality row.
    Row {
        proof: ProofId,
        column: Option<usize>,
    },
    /// `dec(class) = rhs`; the endpoints' common free slots support the class.
    /// The RHS's bound names are fresh for every free name of the LHS.
    Equality { class: TermId, proof: ViewId },
    /// A child of an exact native constructor conclusion, replayed on demand.
    Constructor {
        proof: ProofId,
        column: usize,
        rhs: bool,
    },
}

impl Support {
    fn new(row: ProofId) -> Self {
        Self {
            origin: SupportOrigin::Row {
                proof: row,
                column: None,
            },
            transport: None,
        }
    }
}

/// A pattern expansion and its local bindings.
struct Expansion {
    proof: ViewId,
    variables: HashMap<String, Occurrence>,
    occurrences: HashMap<Vec<usize>, Occurrence>,
    /// Atom slots in the right-hand side's coordinates, in pattern order.
    slots: Vec<(String, i64, i64)>,
}

/// What an expansion walks over: the match's premises and substitution, the
/// compiler's actual bindings, and the flattener's atom names by path.
#[derive(Clone)]
struct ExpandCtx<'a> {
    firing: ProofId,
    root_binding: Option<String>,
    prems: &'a [ProofId],
    subst: &'a IndexMap<String, TermId>,
    names: HashMap<Vec<usize>, String>,
    readings: BTreeMap<String, String>,
    labels: &'a BTreeMap<String, Option<String>>,
    selected: &'a [crate::slotted::runtime::SelectedReading],
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

impl<'a, E> SlotLifter<'a, E> {
    /// Retain only reconstruction state between scoped native-origin visits.
    fn with_egg<N>(self, egg: N) -> SlotLifter<'a, N> {
        SlotLifter {
            program: self.program,
            names: self.names,
            egg,
            out: self.out,
            dec_memo: self.dec_memo,
            edge_memo: self.edge_memo,
            eq_memo: self.eq_memo,
            symmetry_memo: self.symmetry_memo,
            rule_instances: self.rule_instances,
            anchors: self.anchors,
            head_supports: self.head_supports,
            known: self.known,
            shape_terms: self.shape_terms,
            term_shapes: self.term_shapes,
            fresh: self.fresh,
            reserved_terms: self.reserved_terms,
        }
    }
}

impl<'a, 'e> SlotLifter<'a, NativeProofs<'e>> {
    fn new(
        program: &'a ProofContext,
        dag: TermDag,
        names: &'a EncodingNames,
        egg: NativeProofs<'e>,
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
            out: Coordinates::new(SlottedProofStore::new(dag).with_slot_names(&program.slot_names)),
            dec_memo: HashMap::default(),
            edge_memo: HashMap::default(),
            eq_memo: HashMap::default(),
            symmetry_memo: HashMap::default(),
            rule_instances: HashMap::default(),
            anchors: HashMap::default(),
            head_supports: HashMap::default(),
            known: HashMap::default(),
            shape_terms: HashMap::default(),
            term_shapes: TermShapes::default(),
            fresh,
            reserved_terms,
        }
    }

    fn with_evidence(
        program: &'a ProofContext,
        dag: TermDag,
        names: &'a EncodingNames,
        egg: NativeProofs<'e>,
        evidence: &source::Certificates,
    ) -> LiftResult<Self> {
        let mut tr = Self::new(program, dag.clone(), names, egg);
        let mut store = evidence.store.clone();
        store.term_dag = dag;
        tr.out = Coordinates::new(store.with_slot_names(&program.slot_names));
        tr.anchors = evidence.anchors.clone();
        tr.head_supports = evidence.head_supports.clone();
        let mut anchors: Vec<_> = tr.anchors.keys().copied().collect();
        anchors.sort();
        for proof in anchors {
            tr.eq(proof)?;
        }
        for &proof in &evidence.roots {
            let view = tr.out.plain(proof);
            tr.note(view);
            let reverse = tr.out.sym(view);
            let mut pending = vec![view, reverse];
            let mut seen = HashSet::default();
            while let Some(proof) = pending.pop() {
                let term = tr.out.edge(proof).rhs;
                if !seen.insert(term) {
                    continue;
                }
                let Term::App(head, _) = tr.out.term_dag.get(term).clone() else {
                    continue;
                };
                let Some(op) = program.constructors.get(&head) else {
                    continue;
                };
                for (i, column) in op.columns.iter().enumerate() {
                    if *column == ColumnKind::Child {
                        let child = tr.out.project(proof, i).map_err(|e| e.to_string())?;
                        tr.note(child);
                        pending.push(child);
                    }
                }
            }
        }
        Ok(tr)
    }

    fn egg(&self) -> &'e TermDag {
        self.egg.store.term_dag()
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

    fn prop_string(&self, p: ViewId) -> String {
        self.out.edge_to_string(self.out.edge(p))
    }

    fn app(&self, t: TermId) -> Option<(&'e str, &'e [TermId])> {
        match self.egg().get(t) {
            Term::App(head, args) => Some((head.as_str(), args.as_slice())),
            _ => None,
        }
    }

    fn is_carrier_term(&self, t: TermId) -> bool {
        self.app(t)
            .is_some_and(|(head, _)| self.program.constructors.contains_key(head))
    }

    fn sub(&self, subst: &IndexMap<String, TermId>, var: &str) -> LiftResult<TermId> {
        subst
            .get(var)
            .copied()
            .ok_or_else(|| format!("rule substitution has no {var}"))
    }
}

#[cfg(test)]
#[path = "../tests/lift_slots.rs"]
pub(super) mod tests;
