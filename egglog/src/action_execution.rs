//! Prepare restricted constructor actions without effects; execute them through
//! the same command dispatch as resolved actions. Only insertion-only runs share
//! a commit. Unions retain an individual rebuild boundary.

use crate::*;
use smallvec::SmallVec;
use std::rc::Rc;

// Consumed directly by command dispatch, never retained in a collection. Keep
// resolved commands inline instead of allocating for each ordinary command.
#[allow(clippy::large_enum_variant)]
pub(super) enum ExecutableCommand {
    Resolved(ResolvedNCommand),
    PreparedActions(Vec<GroundActions>),
}

// Metadata is valid only until a command can change signatures or table
// identities. Bounded flushes and unions preserve it; declined heads are cached.
pub(super) type GroundActionCache =
    HashMap<String, Option<(Arc<FuncType>, Rc<egglog_bridge::TableAction>)>>;

pub(super) struct GroundActions {
    pub(super) lookups: Vec<(Rc<egglog_bridge::TableAction>, SmallVec<[usize; 4]>)>,
    pub(super) union: Option<(usize, usize)>,
}

impl EGraph {
    /// A closed constructor action consists entirely of declared constructor
    /// calls, with nullary calls at its leaves, optionally joined by `union`.
    /// Literals, variables, primitives, globals, views, indexes and custom sorts
    /// retain the ordinary compiler. Preparation never allocates IDs or writes.
    pub(super) fn prepare_ground_action<Node: typechecking::CallView>(
        &self,
        action: Option<typechecking::ClosedAction<&Node>>,
        calls: &mut GroundActionCache,
        permit_call: impl Fn(&str) -> bool,
    ) -> Option<GroundActions> {
        if self.proof_state.original_typechecking.is_some() {
            return None;
        }
        let mut prepared = GroundActions {
            lookups: Vec::new(),
            union: None,
        };
        let checked = self.type_info.check_closed_action(
            action?,
            &mut |head| {
                // Parser overrides can change during an empty parser expansion.
                // Check call admission before cached type/table metadata every time.
                if !permit_call(head) {
                    return None;
                }
                if let Some(cached) = calls.get(head) {
                    return cached.clone();
                }
                let call = self.type_info.closed_call_type(head).and_then(|func| {
                    let function = self.functions.get(&func.name)?;
                    if func.subtype != FunctionSubtype::Constructor
                        || function.subtype() != FunctionSubtype::Constructor
                        || func.role.is_global()
                        || function.is_view()
                        || function.is_let_binding()
                        || self.type_info.indexes.contains_key(&func.name)
                        || !(func.output().as_ref() as &dyn Any).is::<EqSort>()
                    {
                        return None;
                    }
                    let table = egglog_bridge::TableAction::for_constructor_insertions(
                        &self.backend,
                        function.backend_id,
                    )?;
                    (table.input_arity() == func.input.len())
                        .then(|| (func.clone(), Rc::new(table)))
                });
                calls.insert(head.into(), call.clone());
                call
            },
            &mut |table, args: SmallVec<[usize; 4]>| {
                let index = prepared.lookups.len();
                prepared.lookups.push((table, args));
                Some(index)
            },
        )?;
        if let typechecking::ClosedAction::Union(left, right) = checked {
            prepared.union = Some((left, right));
        }
        Some(prepared)
    }

    pub(super) fn eval_ground_actions(
        &mut self,
        prepared: Vec<GroundActions>,
    ) -> Result<(), Error> {
        let union = egglog_bridge::UnionAction::new(&self.backend);
        self.backend
            .run_actions(Some(&self.type_info), |state| {
                let mut values = Vec::new();
                let mut arguments = Vec::new();
                // The metadata cache interns handles and keeps them alive through
                // this call, so pointer identity names one physical table. Values
                // stay fixed only until this backend transaction commits/rebuilds.
                let mut constants = HashMap::default();
                for action in prepared {
                    values.clear();
                    for (table, args) in action.lookups {
                        let value = if args.is_empty() {
                            *constants
                                .entry(Rc::as_ptr(&table))
                                .or_insert_with(|| table.lookup_or_insert(state, &[]).unwrap())
                        } else {
                            arguments.clear();
                            arguments.extend(args.iter().map(|index| values[*index]));
                            table.lookup_or_insert(state, &arguments).unwrap()
                        };
                        values.push(value);
                    }
                    if let Some((left, right)) = action.union {
                        union.union(state, values[left], values[right]);
                    }
                }
            })
            .map_err(|error| Error::BackendError(error.to_string()))
    }

    /// Drain exactly once through command dispatch. Failed batches are never
    /// replayed: rows and extension effects are not transactional.
    pub(super) fn flush_ground_actions(
        &mut self,
        pending: &mut Vec<GroundActions>,
    ) -> Result<(), Error> {
        if !pending.is_empty() {
            self.run_command(ExecutableCommand::PreparedActions(std::mem::take(pending)))?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests;
