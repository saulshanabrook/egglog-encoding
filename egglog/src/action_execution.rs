//! Prepare restricted constructor actions without effects; execute them through
//! the same command dispatch as resolved actions. Each action retains its own
//! commit and rebuild boundary.

use crate::*;

// Consumed directly by command dispatch, never retained in a collection. Keep
// resolved commands inline instead of allocating for each ordinary command.
#[allow(clippy::large_enum_variant)]
pub(super) enum ExecutableCommand {
    Resolved(ResolvedNCommand),
    PreparedActions(Vec<GroundActions>),
}

pub(super) struct GroundActions {
    pub(super) lookups: Vec<(egglog_bridge::TableAction, Vec<usize>)>,
    pub(super) union: Option<(usize, usize)>,
}

impl EGraph {
    /// A closed constructor action consists entirely of declared constructor
    /// calls, with nullary calls at its leaves, optionally joined by `union`.
    /// Literals, variables, primitives, globals, views, indexes and custom sorts
    /// retain the ordinary compiler. Preparation never allocates IDs or writes.
    pub(super) fn prepare_ground_action(&self, action: &Action) -> Option<GroundActions> {
        if self.proof_state.original_typechecking.is_some() {
            return None;
        }
        let mut prepared = GroundActions {
            lookups: Vec::new(),
            union: None,
        };
        let checked = self
            .type_info
            .check_closed_action(action, &mut |_, func, args| {
                let function = self.functions.get(&func.name)?;
                if func.subtype != FunctionSubtype::Constructor
                    || function.subtype() != FunctionSubtype::Constructor
                    || func.num_outputs() != 1
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
                if table.input_arity() != args.len() {
                    return None;
                }
                let index = prepared.lookups.len();
                prepared.lookups.push((table, args));
                Some(index)
            })?;
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
                for action in prepared {
                    values.clear();
                    for (table, args) in action.lookups {
                        let args: smallvec::SmallVec<[Value; 4]> =
                            args.iter().map(|index| values[*index]).collect();
                        values.push(table.lookup_or_insert(state, &args).unwrap());
                    }
                    if let Some((left, right)) = action.union {
                        union.union(state, values[left], values[right]);
                    }
                }
            })
            .map_err(|error| Error::BackendError(error.to_string()))
    }
}

#[cfg(test)]
mod tests;
