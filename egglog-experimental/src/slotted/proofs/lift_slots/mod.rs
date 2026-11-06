//! Lift an egglog proof over the encoded program to a slotted proof
//! over surface terms; see *Slot lifting* in `egglog-experimental/src/slotted/PROOFS.md`.
//!
//! Encoded rows are interpreted as ordinary surface equalities. The lifting
//! rules and their derivations are described in the proof guide above.

use super::context::{ColumnKind, ProofContext, SourceFact, pattern_term};
use super::coordinates::{Coordinates, ViewId};
use super::format::{Claim, SlottedProofStore};
use super::pipeline::EncodingNames;
use super::terms::{FreshSlots, Renaming, all_slots, rename, slot_of, slot_term, term_renaming};

use super::{HashMap, HashSet};
use crate::slotted::query::ProofNames;
use crate::slotted::runtime::frame_from_term;
use crate::slotted::runtime::renaming::shape;
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
mod symmetry;

use permutations::{compose, inverse, is_identity, slot_map_string};
use rule_kind::{RuleKind, rule_kind};
use shape::{ShapeKey, readings};

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
    egg: &ProofStore,
    root: ProofId,
    claim: &Claim,
    query: &ProofNames,
    roots: [&str; 2],
) -> LiftResult<(SlottedProofStore, ProofId)> {
    let mut tr = SlotLifter::new(program, dag, names, egg);
    let id = tr.claim(root, claim, query, roots)?;
    Ok(tr.out.finish(id))
}

fn query_firing(egg: &ProofStore, root: ProofId, frame: &str) -> LiftResult<ProofId> {
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

pub(super) fn matched_frame(egg: &ProofStore, root: ProofId, names: &ProofNames) -> LiftResult<Fr> {
    let root = query_firing(egg, root, &names.frame)?;
    let Justification::Rule { substitution, .. } = egg.get(root).justification() else {
        unreachable!("query_firing returns a rule firing")
    };
    frame_from_term(egg.term_dag(), substitution[&names.frame])
        .ok_or_else(|| "query frame is not a frame".into())
}

struct SlotLifter<'a> {
    program: &'a ProofContext,
    names: &'a EncodingNames,
    egg: &'a ProofStore,
    out: Coordinates,
    /// Encoded term -> its surface term.
    dec_memo: HashMap<TermId, TermId>,
    /// (encoded node, surface column) -> the permutation that completed the
    /// column's edge when the node was decoded.
    edge_memo: HashMap<(TermId, usize), Renaming>,
    /// Egglog proof -> the slotted proof of the equality it denotes.
    eq_memo: HashMap<ProofId, ViewId>,
    /// Surface term -> a slotted proof whose left side it is, from which its
    /// reflexivity follows.
    known: HashMap<TermId, ViewId>,
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
    row: Option<(TermId, ViewId)>,
}

/// A pattern expansion and its local bindings.
struct Expansion {
    proof: ViewId,
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

impl<'a> SlotLifter<'a> {
    fn new(
        program: &'a ProofContext,
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
            out: Coordinates::new(SlottedProofStore::new(dag).with_slot_names(&program.slot_names)),
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

    fn prop_string(&self, p: ViewId) -> String {
        self.out.edge_to_string(self.out.edge(p))
    }

    fn app(&self, t: TermId) -> Option<(&'a str, &'a [TermId])> {
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

impl RowKind {
    fn is_edge(&self) -> bool {
        matches!(self, RowKind::Edge)
    }
}

#[cfg(test)]
#[path = "../tests/lift_slots.rs"]
pub(super) mod tests;
