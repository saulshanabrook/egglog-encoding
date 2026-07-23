//! Container rebuild for the term/proof encoding.
//!
//! Registers a container sort's rebuild primitives from its
//! [`ContainerRebuildSpec`] ([`register_container_rebuild_from_spec`]), and
//! defines the `ContainerRebuild` / `ContainerRebuildProof` primitives that
//! canonicalize a container's elements to their union-find leaders (and, in
//! proof mode, prove the rebuild). Also holds the encoder-side spec bookkeeping
//! ([`ProofInstrumentor::build_container_rebuild_spec`] and the primitive-name
//! lookups).

use super::proof_encoding::ProofInstrumentor;
use crate::exec_state::{Internal, RegistrySealed};
use crate::*;
use egglog_backend_trait::CounterId;
use egglog_bridge::TableAction;
use egglog_numeric_id::NumericId;

/// Mint a fresh proof id and assert the relation row `(<action> args… out ())`,
/// returning `out`. Proof constructors are relations, so a proof node is created
/// by minting its id rather than by a constructor's lookup-or-insert.
fn mint_proof_row(
    state: &mut FullState,
    action: &TableAction,
    id_counter: CounterId,
    args: &[Value],
) -> Value {
    let out = Value::from_usize(state.raw_exec_state().inc_counter(id_counter));
    let unit = state.base_values().get::<()>(());
    let row: Vec<Value> = args.iter().copied().chain([out, unit]).collect();
    action.insert(state.raw_exec_state(), row.into_iter());
    out
}

/// Register a container sort's rebuild primitives from its
/// [`ContainerRebuildSpec`]. Called when a container Sort command carrying an
/// `:internal-container-rebuild` annotation is typechecked, so the primitives
/// exist before the rebuild rules — both during encoding and on re-parse.
pub(crate) fn register_container_rebuild_from_spec(
    eg: &mut EGraph,
    sort_name: &str,
    spec: &ContainerRebuildSpec,
) {
    let Some(container_sort) = eg.get_sort_by_name(sort_name).cloned() else {
        return;
    };
    // Each element eq-sort's single UF table, recovered from proof_state (filled
    // by the element sorts' `:internal-uf` on re-parse) rather than the spec.
    let mut uf_names = HashMap::default();
    collect_element_uf_names(eg, &container_sort, &mut uf_names);

    eg.add_read_primitive(
        ContainerRebuild {
            name: spec.internal_rebuild_prim.clone(),
            container_sort: container_sort.clone(),
            uf_names: uf_names.clone(),
            proof_mode: spec.internal_rebuild_proof_prim.is_some(),
        },
        None,
    );

    if let Some(proof_prim) = &spec.internal_rebuild_proof_prim {
        // Proof ids are minted from the backend's id counter; a backend without
        // one can't run these proofs.
        let Some(id_counter) = eg.backend.id_counter() else {
            return;
        };
        // Each container's `<CSort>Proof` table (this sort + nested containers),
        // recovered from proof_state (filled by `:internal-proof-func`).
        let mut cproof_names = HashMap::default();
        collect_container_proof_names(eg, &container_sort, &mut cproof_names);
        // The global proof constructors, recovered from proof_state (repopulated
        // from the `Proof` sort's `:internal-proof-names` on re-parse).
        let names = &eg.proof_state.proof_names;
        let congr_all_name = names.congr_all_constructor.clone();
        let trans_name = names.eq_trans_constructor.clone();
        let sym_name = names.eq_sym_constructor.clone();
        let container_normalize_name = names.container_normalize_constructor.clone();
        let proof_sort: ArcSort = std::sync::Arc::new(EqSort {
            name: names.proof_datatype.clone(),
        });
        eg.add_full_primitive(
            ContainerRebuildProof {
                name: proof_prim.clone(),
                container_sort,
                proof_sort,
                uf_names,
                cproof_names,
                congr_all_name,
                trans_name,
                sym_name,
                container_normalize_name,
                id_counter,
            },
            None,
        );
    }
}

/// Each transitively-reachable eq-sort element's single UF table, from
/// `proof_state.uf_parent` (filled by element sorts' `:internal-uf`).
fn collect_element_uf_names(eg: &EGraph, sort: &ArcSort, out: &mut HashMap<String, String>) {
    for elem in sort.inner_sorts() {
        if elem.is_eq_sort() {
            if let Some(uf) = eg.proof_state.uf_parent.get(elem.name()) {
                out.insert(elem.name().to_string(), uf.clone());
            }
        } else if elem.is_eq_container_sort() {
            collect_element_uf_names(eg, &elem, out);
        }
    }
}

/// The `<CSort>Proof` table for `sort` and every nested container sort, from
/// `proof_state.proof_func_parent` (filled by `:internal-proof-func`).
fn collect_container_proof_names(eg: &EGraph, sort: &ArcSort, out: &mut HashMap<String, String>) {
    if let Some(cp) = eg.proof_state.proof_func_parent.get(sort.name()) {
        out.insert(sort.name().to_string(), cp.clone());
    }
    for elem in sort.inner_sorts() {
        if elem.is_eq_container_sort() {
            collect_container_proof_names(eg, &elem, out);
        }
    }
}

/// Re-intern container `value` of `sort` with each contained value remapped
/// through `leaders` (an old-value -> union-find-leader map); the value-level
/// half of the container rebuild performed by the rebuild rules.
fn rebuild_with_leaders(
    cvs: &ContainerValues,
    es: &mut ExecutionState,
    sort: &ArcSort,
    value: Value,
    leaders: &HashMap<Value, Value>,
) -> Value {
    let type_id = sort
        .value_type()
        .expect("container sorts have a value type");
    cvs.rebuild_val_with(type_id, value, es, &|v| {
        leaders.get(&v).copied().unwrap_or(v)
    })
}

/// Recursively canonicalize a container `value` of sort `sort` for the term
/// encoding, returning the rebuilt interned value. Each element is resolved by
/// a uniform per-child rule: an eq-sort element maps to its union-find leader
/// (via the single `UF_<E>` row), a
/// container element is recursively rebuilt, and anything else is unchanged.
fn rebuild_container_value_rec(
    state: &mut ReadState,
    sort: &ArcSort,
    value: Value,
    uf_names: &HashMap<String, String>,
    proof_mode: bool,
) -> Option<Value> {
    let elements = {
        let cvs = state.container_values();
        sort.inner_values(cvs, value)
    };
    let mut leaders: HashMap<Value, Value> = HashMap::default();
    for (esort, eval) in &elements {
        let new = if esort.is_eq_sort() {
            lookup_uf_row(state, uf_names, esort, *eval, proof_mode)
                .map(|(leader, _)| leader)
                .unwrap_or(*eval)
        } else if esort.is_eq_container_sort() {
            rebuild_container_value_rec(state, esort, *eval, uf_names, proof_mode)?
        } else {
            *eval
        };
        if new != *eval {
            leaders.insert(*eval, new);
        }
    }
    let cvs = state.container_values();
    let es = state.raw_exec_state();
    Some(rebuild_with_leaders(cvs, es, sort, value, &leaders))
}

/// Look up an eq-sort element's single-UF row. The first value column is the
/// leader; proof mode has a second value column containing `key = leader`.
/// A missing row means the element is already a root.
fn lookup_uf_row<'a, 'db: 'a, S>(
    state: &S,
    uf_names: &HashMap<String, String>,
    esort: &ArcSort,
    eval: Value,
    proof_mode: bool,
) -> Option<(Value, Option<Value>)>
where
    S: RegistrySealed<'a, 'db>,
{
    let uf_name = uf_names.get(esort.name())?;
    let action = state.registry().lookup_table(uf_name)?;
    let values = action.lookup_values(state.es(), &[eval])?;
    Some((values[0], proof_mode.then(|| values[1])))
}

/// A term-encoding primitive that canonicalizes a container value's elements to
/// their union-find leaders (recursing through nested containers). Registered
/// per container sort by `container_rebuild_prim` and
/// invoked from the container-column arm of the rebuild rules. It reads the
/// single `UF_<E>` tables, so it is only valid in a `:naive` rule (read-context body).
#[derive(Clone)]
struct ContainerRebuild {
    name: String,
    container_sort: ArcSort,
    /// element-sort name -> single `UF_<E>` table name (all reachable eq-sorts)
    uf_names: HashMap<String, String>,
    /// Whether the single UF row has a second proof value column.
    proof_mode: bool,
}

impl Primitive for ContainerRebuild {
    fn name(&self) -> &str {
        &self.name
    }

    fn get_type_constraints(&self, span: &Span) -> Box<dyn TypeConstraint> {
        SimpleTypeConstraint::new(
            &self.name,
            vec![self.container_sort.clone(), self.container_sort.clone()],
            span.clone(),
        )
        .into_box()
    }
}

impl ReadPrim for ContainerRebuild {
    fn apply<'a, 'db>(&self, mut state: ReadState<'a, 'db>, args: &[Value]) -> Option<Value> {
        rebuild_container_value_rec(
            &mut state,
            &self.container_sort,
            args[0],
            &self.uf_names,
            self.proof_mode,
        )
    }
}

/// Proof-mode counterpart of [`ContainerRebuild`]: mints a `CongrAll` chain
/// proving `old_container = rebuilt_container` (recursing through nested
/// containers). Reads `UF_<E>` (element equality proofs) and `<CSort>Proof`
/// (reflexive bases), mints `CongrAll`/`Trans`/`Sym` terms, and anchors a
/// reflexive proof on each rebuilt container so it can be rebuilt again later.
/// It is a [`FullPrim`], valid only in a `:naive` rule's action.
#[derive(Clone)]
struct ContainerRebuildProof {
    name: String,
    container_sort: ArcSort,
    proof_sort: ArcSort,
    /// element-sort name -> single `UF_<E>` table name (all reachable eq-sorts)
    uf_names: HashMap<String, String>,
    /// container-sort name -> `<CSort>Proof` table name (all reachable containers)
    cproof_names: HashMap<String, String>,
    /// `CongrAll` / `Trans` / `Sym` / `ContainerNormalize` proof constructor names
    congr_all_name: String,
    trans_name: String,
    sym_name: String,
    container_normalize_name: String,
    /// Counter for minting fresh proof ids (see [`mint_proof_row`]).
    id_counter: egglog_backend_trait::CounterId,
}

impl Primitive for ContainerRebuildProof {
    fn name(&self) -> &str {
        &self.name
    }

    fn get_type_constraints(&self, span: &Span) -> Box<dyn TypeConstraint> {
        SimpleTypeConstraint::new(
            &self.name,
            vec![self.container_sort.clone(), self.proof_sort.clone()],
            span.clone(),
        )
        .into_box()
    }
}

impl FullPrim for ContainerRebuildProof {
    fn apply<'a, 'db>(&self, mut state: FullState<'a, 'db>, args: &[Value]) -> Option<Value> {
        let (_rebuilt, proof) =
            rebuild_container_proof_rec(&mut state, self, &self.container_sort, args[0])?;
        Some(proof)
    }
}

/// Recursively rebuild `value` (of container sort `sort`) and produce a proof
/// that `value = rebuilt`. Returns `(rebuilt_value, proof)`. Uses the same
/// per-child resolution as [`rebuild_container_value_rec`], additionally
/// folding a `CongrAll` step for every distinct changed child and recording a
/// reflexive anchor `<CSort>Proof(rebuilt) = Trans(Sym proof, proof)` so the
/// rebuilt value can itself be rebuilt in a later iteration. The steps match
/// elements by term (`CongrAll`), never by position: elements here come in
/// value order, not the term form's canonical child order.
fn rebuild_container_proof_rec(
    state: &mut FullState,
    prim: &ContainerRebuildProof,
    sort: &ArcSort,
    value: Value,
) -> Option<(Value, Value)> {
    // Reflexive base proof `value = value`.
    let base = state
        .lookup(prim.cproof_names.get(sort.name())?, value)
        .expect("container proof lookup failed")?;
    let elements = {
        let cvs = state.container_values();
        sort.inner_values(cvs, value)
    };

    // One entry per distinct changed element: `CongrAll` replaces every
    // occurrence at once, matching `rebuild_with_leaders`.
    let mut leaders: HashMap<Value, Value> = HashMap::default();
    let mut child_proofs: Vec<Value> = vec![];
    for (esort, eval) in &elements {
        if leaders.contains_key(eval) {
            continue;
        }
        if esort.is_eq_sort() {
            if let Some((leader, Some(proof))) =
                lookup_uf_row(state, &prim.uf_names, esort, *eval, true)
                && leader != *eval
            {
                leaders.insert(*eval, leader);
                child_proofs.push(proof);
            }
        } else if esort.is_eq_container_sort() {
            let (rebuilt_child, child_proof) =
                rebuild_container_proof_rec(state, prim, esort, *eval)?;
            if rebuilt_child != *eval {
                leaders.insert(*eval, rebuilt_child);
                child_proofs.push(child_proof);
            }
        }
    }

    // Rebuild the value against the collected leaders.
    let rebuilt = {
        let cvs = state.container_values();
        let es = state.raw_exec_state();
        rebuild_with_leaders(cvs, es, sort, value, &leaders)
    };

    // Fold a `CongrAll` step per changed child onto the reflexive base. This
    // proves `value = raw`, where `raw` is the term with children replaced by
    // their leaders (it may be in non-canonical order, or have duplicate/
    // clobbering entries for collapsing containers).
    let congr_all_action = state.registry().lookup_table(&prim.congr_all_name)?.clone();
    let mut current = base;
    for proof in child_proofs {
        current = mint_proof_row(state, &congr_all_action, prim.id_counter, &[current, proof]);
    }

    // Bridge the (possibly non-canonical) `raw` term to the canonical `rebuilt`
    // term with the container normalization: `ContainerNormalize(current)` proves
    // `value = normalize(raw)`, which the checker recomputes to match
    // `reconstruct_termdag(rebuilt)`. We mint it unconditionally; for
    // order/arity-preserving containers (Vec/Pair) the normalization is the
    // identity, so it is a no-op the proof simplifier removes.
    let normalize_action = state
        .registry()
        .lookup_table(&prim.container_normalize_name)?
        .clone();
    current = mint_proof_row(state, &normalize_action, prim.id_counter, &[current]);

    // Anchor a reflexive proof on the rebuilt value for future rebuilds.
    if rebuilt != value {
        let sym_action = state.registry().lookup_table(&prim.sym_name)?.clone();
        let trans_action = state.registry().lookup_table(&prim.trans_name)?.clone();
        let cproof_action = state
            .registry()
            .lookup_table(prim.cproof_names.get(sort.name())?)?
            .clone();
        // Sym(current): rebuilt = value;  Trans(Sym(current), current): rebuilt = rebuilt.
        let sym_p = mint_proof_row(state, &sym_action, prim.id_counter, &[current]);
        let refl = mint_proof_row(state, &trans_action, prim.id_counter, &[sym_p, current]);
        cproof_action.insert(state.raw_exec_state(), [rebuilt, refl].into_iter());
    }

    Some((rebuilt, current))
}

impl ProofInstrumentor<'_> {
    /// Build the [`ContainerRebuildSpec`] for a container sort: mint and cache
    /// the fresh rebuild-primitive names. The primitives themselves are
    /// registered from the spec when the Sort is typechecked (see
    /// [`register_container_rebuild_from_spec`]).
    pub(super) fn build_container_rebuild_spec(
        &mut self,
        container_sort: &ArcSort,
    ) -> ContainerRebuildSpec {
        let sort_name = container_sort.name().to_string();
        let proof_mode = self.egraph.proof_state.proofs_enabled;

        let internal_rebuild_prim = self.egraph.parser.symbol_gen.fresh("container_rebuild");
        self.egraph
            .proof_state
            .container_rebuild_name
            .insert(sort_name.clone(), internal_rebuild_prim.clone());

        let internal_rebuild_proof_prim = proof_mode.then(|| {
            let proof_prim = self
                .egraph
                .parser
                .symbol_gen
                .fresh("container_rebuild_proof");
            self.egraph
                .proof_state
                .container_rebuild_proof_name
                .insert(sort_name, proof_prim.clone());
            proof_prim
        });

        ContainerRebuildSpec {
            internal_rebuild_prim,
            internal_rebuild_proof_prim,
        }
    }

    /// The (already-built) container value-rebuild primitive name for a sort.
    pub(super) fn container_rebuild_prim(&mut self, container_sort: &ArcSort) -> String {
        self.egraph
            .proof_state
            .container_rebuild_name
            .get(container_sort.name())
            .cloned()
            .unwrap_or_else(|| {
                panic!(
                    "container rebuild primitive not built for sort {}",
                    container_sort.name()
                )
            })
    }

    /// The (already-built) container proof-rebuild primitive name for a sort.
    pub(super) fn container_rebuild_proof_prim(&mut self, container_sort: &ArcSort) -> String {
        self.egraph
            .proof_state
            .container_rebuild_proof_name
            .get(container_sort.name())
            .cloned()
            .unwrap_or_else(|| {
                panic!(
                    "container rebuild proof primitive not built for sort {}",
                    container_sort.name()
                )
            })
    }
}
