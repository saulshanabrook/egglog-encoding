//! Prepare restricted constructor actions without effects; execute them through
//! the existing action owner. Only insertion-only runs share
//! a commit. Unions retain an individual rebuild boundary.

use crate::*;
use smallvec::SmallVec;
use std::rc::Rc;

pub(super) enum ActionBatch<'a> {
    Resolved(&'a ResolvedActions, &'a mut GroundActionCache),
    Ground(Vec<GroundActions>),
    #[cfg(test)]
    CompiledOracle(&'a ResolvedActions),
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
                self.cached_ground_call(head, calls)
            },
            &mut |_, table, args: SmallVec<[usize; 4]>| {
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

    fn cached_ground_call(
        &self,
        head: &str,
        calls: &mut GroundActionCache,
    ) -> Option<(Arc<FuncType>, Rc<egglog_bridge::TableAction>)> {
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
                // Closed children cannot supply a custom/base sort. Avoid its callbacks in preflight.
                || func
                    .input
                    .iter()
                    .any(|sort| !(sort.as_ref() as &dyn Any).is::<EqSort>())
            {
                return None;
            }
            let table = egglog_bridge::TableAction::for_constructor_insertions(
                &self.backend,
                function.backend_id,
            )?;
            (table.input_arity() == func.input.len()).then(|| (func.clone(), Rc::new(table)))
        });
        calls.insert(head.into(), call.clone());
        call
    }

    pub(super) fn ground_action_lookups<Node: typechecking::CallView>(
        &self,
        action: typechecking::ClosedAction<&Node>,
        calls: &mut GroundActionCache,
    ) -> Option<usize> {
        if self.proof_state.original_typechecking.is_some() {
            return None;
        }
        let mut lookups = 0;
        self.type_info.check_closed_action(
            action,
            &mut |head| self.cached_ground_call(head, calls),
            &mut |_, _, _: Vec<()>| {
                lookups += 1;
                Some(())
            },
        )?;
        Some(lookups)
    }

    pub(super) fn prepare_resolved_ground_actions(
        &self,
        actions: &ResolvedActions,
        calls: &mut GroundActionCache,
    ) -> Option<Vec<GroundActions>> {
        if actions.0.is_empty()
            || actions.0.len() > 1
                && actions
                    .0
                    .iter()
                    .any(|action| !matches!(action, ResolvedAction::Expr(..)))
        {
            return None;
        }
        actions
            .0
            .iter()
            .map(|action| {
                self.prepare_ground_action(
                    typechecking::ClosedAction::from_action(action),
                    calls,
                    |_| true,
                )
            })
            .collect()
    }

    pub(super) fn eval_ground_actions(
        &mut self,
        prepared: Vec<GroundActions>,
    ) -> Result<(), Error> {
        #[cfg(test)]
        let batch_event = tests::BATCH_EVENTS.with(|slot| {
            slot.borrow().as_ref().map(|_| {
                (
                    prepared.len(),
                    prepared
                        .first()
                        .map(|action| {
                            action
                                .lookups
                                .iter()
                                .map(|(table, _)| table.clone())
                                .collect::<Vec<_>>()
                        })
                        .unwrap_or_default(),
                )
            })
        });
        let union = egglog_bridge::UnionAction::new(&self.backend);
        let result = self
            .backend
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
            .map_err(|error| Error::BackendError(error.to_string()));
        #[cfg(test)]
        if result.is_ok() {
            if let Some(batch_event) = batch_event {
                tests::BATCH_EVENTS.with(|slot| {
                    if let Some(events) = slot.borrow_mut().as_mut() {
                        events.push(batch_event);
                    }
                });
            }
            tests::ORDER_LOG.with(|slot| {
                if let Some(log) = slot.borrow().as_ref() {
                    log.lock().unwrap().push("commit");
                }
            });
        }
        result
    }

    /// Drain exactly once through command dispatch. Failed batches are never
    /// replayed: rows and extension effects are not transactional.
    pub(super) fn flush_resolved_actions(
        &mut self,
        pending: &mut Vec<ResolvedAction>,
        lookups: &mut usize,
        calls: &mut GroundActionCache,
    ) -> Result<(), Error> {
        let actions = ResolvedActions::new(std::mem::take(pending));
        *lookups = 0;
        if !actions.0.is_empty() {
            self.run_timed_command(CommandPhase::Actions, |graph| {
                graph.eval_actions(ActionBatch::Resolved(&actions, calls))
            })?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests;
