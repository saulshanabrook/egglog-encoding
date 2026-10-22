//! Bridge bindings for the encoded, explained UF. Proof constructors remain
//! ordinary tables; the native storage only handles their opaque values.

use super::*;
use core_relations::{ExplainedUfTable, ReasonComposer, ReasonStep};

/// An independent subscriber's acknowledged prefix of one native UF. Copying
/// it creates another reader; polling does not advance it or invoke callbacks.
#[derive(Clone, Copy, Debug)]
pub struct EqualitySubscription {
    function: FunctionId,
    cursor: core_relations::EqualityCursor,
}

/// A borrowed batch from the committed UF. Save `next` after processing it.
/// Events retain their reasons even after view rows are removed or compacted.
pub struct EqualityBatch<'a> {
    pub events: &'a [core_relations::EqualityMerged],
    pub next: EqualitySubscription,
}

pub(super) struct ProofComposer {
    sym: TableAction,
    trans: TableAction,
    ids: CounterId,
    unit: Value,
}

impl ProofComposer {
    pub(super) fn new(eg: &mut EGraph, sym: FunctionId, trans: FunctionId) -> Self {
        Self {
            sym: TableAction::new(eg, sym),
            trans: TableAction::new(eg, trans),
            ids: eg.id_counter,
            unit: eg.db.base_values().get::<()>(()),
        }
    }

    fn mint(&self, action: &TableAction, args: &[Value], state: &mut ExecutionState) -> Value {
        let id = Value::from_usize(state.inc_counter(self.ids));
        action.insert(state, args.iter().copied().chain([id, self.unit]));
        id
    }
}

impl ReasonComposer for ProofComposer {
    fn compose(&self, steps: &[ReasonStep], state: &mut ExecutionState) -> Value {
        let mut result = None;
        for step in steps {
            let proof = if step.reversed {
                self.mint(&self.sym, &[step.reason], state)
            } else {
                step.reason
            };
            result = Some(match result {
                None => proof,
                Some(previous) => self.mint(&self.trans, &[previous, proof], state),
            });
        }
        result.expect("reflexive UF paths must use the caller's existing witness")
    }
}

impl EGraph {
    /// Subscribe at the start of retained history, or at the current end.
    /// Returns `None` for a function that does not use native explained UF.
    pub fn subscribe_equalities(
        &self,
        function: FunctionId,
        include_existing: bool,
    ) -> Option<EqualitySubscription> {
        let info = self.funcs.get(function)?;
        let uf = self
            .db
            .get_table(info.table)
            .as_any()
            .downcast_ref::<ExplainedUfTable>()?;
        Some(EqualitySubscription {
            function,
            cursor: if include_existing {
                uf.start_cursor()
            } else {
                uf.cursor()
            },
        })
    }

    /// Poll a committed batch. `None` means the table was removed/cleared, or
    /// rollback/branch divergence invalidated the acknowledged history prefix.
    /// A cursor on a shared prefix remains valid in a cloned graph.
    pub fn equality_events(&self, subscription: EqualitySubscription) -> Option<EqualityBatch<'_>> {
        let info = self.funcs.get(subscription.function)?;
        let uf = self
            .db
            .get_table(info.table)
            .as_any()
            .downcast_ref::<ExplainedUfTable>()?;
        Some(EqualityBatch {
            events: uf.events_since(subscription.cursor)?,
            next: EqualitySubscription {
                cursor: uf.cursor(),
                ..subscription
            },
        })
    }

    /// Identify an accepted equality produced by a constructor-view collision.
    /// Ordinary rule assertions and custom-function merges are not congruence
    /// events. Redundant congruence candidates never enter the UF event log.
    pub fn congruence_source(&self, event: &core_relations::EqualityMerged) -> Option<FunctionId> {
        let origin = event.origin?;
        if self.db.table_identity(origin.table)? != origin.identity {
            return None;
        }
        self.funcs.iter().find_map(|(id, info)| {
            (info.table == origin.table && info.read_projection.kind == TableKind::Constructor)
                .then_some(id)
        })
    }

    /// Install an encoded UF. Its visible shape is `(S) -> (S, reason)`;
    /// writes assert equalities and reads expose historical root links.
    pub fn add_explained_uf(
        &mut self,
        config: FunctionConfig,
        proof_functions: Option<(FunctionId, FunctionId)>,
    ) -> FunctionId {
        self.add_table_with_storage(config, TableStorage::ExplainedUf(proof_functions), None)
    }

    /// Current representative for a native UF, or `None` for another storage
    /// kind. Legacy internal UF annotations retain their one-hop semantics.
    pub fn native_uf_find(&self, function: FunctionId, value: Value) -> Option<Value> {
        self.db
            .get_table(self.funcs[function].table)
            .as_any()
            .downcast_ref::<ExplainedUfTable>()
            .map(|uf| uf.find(value))
    }

    /// Register action-side canonicalization. Unlike a raw view-column read,
    /// the proof operation composes the path to the current representative.
    pub fn register_uf_read(
        &mut self,
        name: String,
        proof: bool,
        proof_tables: Vec<String>,
    ) -> ExternalFunctionId {
        let registry = self.action_registry.clone();
        let id = self.register_external_func(Box::new(make_external_func(
            move |state: &mut ExecutionState, args: &[Value]| {
                let action = registry.read().lookup_table(&name)?.clone();
                Some(if proof {
                    action.uf_reason(state, args[0]).unwrap_or(args[1])
                } else {
                    action.uf_find(state, args[0])
                })
            },
        )));
        if proof {
            self.external_write_deps.insert(id, proof_tables);
        }
        id
    }
}

impl TableAction {
    pub fn uf_find(&self, state: &ExecutionState, value: Value) -> Value {
        if let Some(uf) = state
            .get_table(self.table)
            .as_any()
            .downcast_ref::<ExplainedUfTable>()
        {
            uf.find(value)
        } else {
            self.lookup_value_col(state, &[value], 0).unwrap_or(value)
        }
    }

    pub fn uf_reason(&self, state: &mut ExecutionState, value: Value) -> Option<Value> {
        if let Some(uf) = state
            .get_table(self.table)
            .as_any()
            .downcast_ref::<ExplainedUfTable>()
        {
            uf.canonical_reason(value, state)
        } else {
            self.lookup_value_col(state, &[value], 1)
        }
    }
}
