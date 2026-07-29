//! Exact execution of a compiled free-join rule at supplied bindings.
//!
//! Every invocation in a batch is point-probed against the same pre-wave
//! database state. All premises and guards are validated before any head is
//! committed, so a rejected invocation cannot leave partial rule effects.
//! Grounded batches deliberately reject trace capture: they replay recorded
//! history and must not recursively record another history.

use std::{
    panic::{AssertUnwindSafe, catch_unwind, resume_unwind},
    sync::Arc,
};

use smallvec::SmallVec;
use thiserror::Error;
use web_time::{Duration, Instant};

use crate::{
    QueryEntry, Value,
    action::{Bindings, ExecutionState},
    query::GroundedRule,
    table_spec::MutationTransaction,
};

use super::{Database, TableId, Variable};

/// One fully grounded invocation of an already compiled rule tape.
#[derive(Clone, Debug)]
#[doc(hidden)]
pub struct GroundedRuleMatch {
    pub invocation_ordinal: u64,
    pub rule: Arc<GroundedRule>,
    pub bindings: Box<[(Variable, Value)]>,
}

/// Result of one atomic grounded wave.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
#[doc(hidden)]
pub struct GroundedRuleRunOutcome {
    pub changed: bool,
    pub pre_merge_time: Duration,
    pub merge_time: Duration,
}

/// A grounded invocation did not exactly match its declared pre-wave witness.
#[derive(Debug, Error)]
#[doc(hidden)]
pub enum GroundedRuleRunError {
    #[error(
        "grounded invocation ordinals must be strictly increasing; observed {previous} followed by {current}"
    )]
    InvocationOrder { previous: u64, current: u64 },
    #[error("grounded invocation {invocation_ordinal} binds variable {variable:?} more than once")]
    DuplicateBinding {
        invocation_ordinal: u64,
        variable: Variable,
    },
    #[error(
        "grounded invocation {invocation_ordinal} premise {premise} has unbound key variable {variable:?}"
    )]
    UnboundPremiseKey {
        invocation_ordinal: u64,
        premise: usize,
        variable: Variable,
    },
    #[error(
        "grounded invocation {invocation_ordinal} body instruction {instruction} has unbound input variable {variable:?}"
    )]
    UnboundBodyInput {
        invocation_ordinal: u64,
        instruction: usize,
        variable: Variable,
    },
    #[error(
        "grounded invocation {invocation_ordinal} premise {premise} is absent from table {table:?} at key {key:?}"
    )]
    MissingPremise {
        invocation_ordinal: u64,
        premise: usize,
        table: TableId,
        key: Box<[Value]>,
    },
    #[error(
        "grounded invocation {invocation_ordinal} premise {premise} column {column} does not match"
    )]
    PremiseMismatch {
        invocation_ordinal: u64,
        premise: usize,
        column: usize,
    },
    #[error("grounded invocation {invocation_ordinal} body guard rejected its declared bindings")]
    GuardRejected { invocation_ordinal: u64 },
    #[error("grounded invocation {invocation_ordinal} body guard attempted to mutate the database")]
    MutatingGuard { invocation_ordinal: u64 },
    #[error("grounded invocation {invocation_ordinal} changed supplied variable {variable:?}")]
    BindingMismatch {
        invocation_ordinal: u64,
        variable: Variable,
    },
    #[error(
        "grounded invocation {invocation_ordinal} did not bind required head variable {variable:?}"
    )]
    UnboundHeadVariable {
        invocation_ordinal: u64,
        variable: Variable,
    },
    #[error("grounded invocation {invocation_ordinal} head did not complete exactly once")]
    HeadRejected { invocation_ordinal: u64 },
    #[error("grounded execution cannot record causal trace")]
    TraceUnsupported,
    #[error("grounded execution was rejected before publishing staged heads")]
    CommitRejected,
}

impl Database {
    /// Validate and execute a list of exact grounded rule invocations without
    /// constructing or consulting a query plan.
    ///
    /// Every premise and body guard is checked against the same committed
    /// pre-wave view before any head runs. Heads then execute in the supplied
    /// invocation-ordinal order and publish through one mutation transaction
    /// and one merge barrier. `allow_commit` lets an embedding inspect side
    /// channels (notably callback panics) before any staged table or union-find
    /// mutation becomes visible.
    #[doc(hidden)]
    pub fn run_grounded_rule_batch(
        &mut self,
        firings: &[GroundedRuleMatch],
        allow_commit: impl FnOnce() -> bool,
    ) -> Result<GroundedRuleRunOutcome, GroundedRuleRunError> {
        if self.trace.is_some() {
            return Err(GroundedRuleRunError::TraceUnsupported);
        }
        for pair in firings.windows(2) {
            if pair[0].invocation_ordinal >= pair[1].invocation_ordinal {
                return Err(GroundedRuleRunError::InvocationOrder {
                    previous: pair[0].invocation_ordinal,
                    current: pair[1].invocation_ordinal,
                });
            }
        }

        let transaction = MutationTransaction::pending();
        let pre_merge_timer = Instant::now();
        let executed = catch_unwind(AssertUnwindSafe(|| {
            let mut prepared = Vec::with_capacity(firings.len());
            for firing in firings {
                let mut bindings = Bindings::new(1);
                for (variable, value) in firing.bindings.iter().copied() {
                    if bindings.get(variable).is_some() {
                        return Err(GroundedRuleRunError::DuplicateBinding {
                            invocation_ordinal: firing.invocation_ordinal,
                            variable,
                        });
                    }
                    bindings.insert(variable, &[value]);
                }

                // Proof instrumentation can introduce hidden table keys from
                // either another premise or a deterministic body primitive.
                // Close only those exact data dependencies: each ready body
                // instruction executes once and each table access is a point
                // probe. No index choice, scan, join, or query plan is built.
                let mut remaining_probes = (0..firing.rule.probes.len()).collect::<Vec<_>>();
                let mut remaining_instrs = (0..firing.rule.body_end).collect::<Vec<_>>();
                let mut state = ExecutionState::new(self.read_only_view(), Default::default());
                state.defer_mutations_until(transaction.clone());
                while !remaining_probes.is_empty() || !remaining_instrs.is_empty() {
                    let mut progressed = false;
                    // Prefer exact premise probes before body computations.
                    // This both exposes a missing premise at the earliest
                    // point and avoids evaluating a primitive unnecessarily.
                    let mut next_probes = Vec::new();
                    let mut first_unbound_probe = None;
                    for premise in remaining_probes {
                        let probe = &firing.rule.probes[premise];
                        let table = &self.tables[probe.table];
                        if probe.n_keys != table.spec.n_keys
                            || probe.entries.len() != table.spec.arity()
                        {
                            return Err(GroundedRuleRunError::PremiseMismatch {
                                invocation_ordinal: firing.invocation_ordinal,
                                premise,
                                column: 0,
                            });
                        }
                        let mut key = SmallVec::<[Value; 4]>::new();
                        for entry in &probe.entries[..probe.n_keys] {
                            match entry {
                                QueryEntry::Const(value) => key.push(*value),
                                QueryEntry::Var(variable) => {
                                    let Some(value) = bindings
                                        .get(*variable)
                                        .and_then(|values| values.first())
                                        .copied()
                                    else {
                                        first_unbound_probe.get_or_insert((premise, *variable));
                                        key.clear();
                                        break;
                                    };
                                    key.push(value);
                                }
                            }
                        }
                        if key.len() != probe.n_keys {
                            next_probes.push(premise);
                            continue;
                        }
                        let row = table.table.get_row(&key).ok_or_else(|| {
                            GroundedRuleRunError::MissingPremise {
                                invocation_ordinal: firing.invocation_ordinal,
                                premise,
                                table: probe.table,
                                key: key.clone().into_vec().into_boxed_slice(),
                            }
                        })?;
                        for (column, (entry, observed)) in probe
                            .entries
                            .iter()
                            .zip(row.vals.iter().copied())
                            .enumerate()
                        {
                            match entry {
                                QueryEntry::Const(expected) if *expected != observed => {
                                    return Err(GroundedRuleRunError::PremiseMismatch {
                                        invocation_ordinal: firing.invocation_ordinal,
                                        premise,
                                        column,
                                    });
                                }
                                QueryEntry::Const(_) => {}
                                QueryEntry::Var(variable) => {
                                    if let Some(expected) = bindings
                                        .get(*variable)
                                        .and_then(|values| values.first())
                                        .copied()
                                    {
                                        if expected != observed {
                                            return Err(GroundedRuleRunError::PremiseMismatch {
                                                invocation_ordinal: firing.invocation_ordinal,
                                                premise,
                                                column,
                                            });
                                        }
                                    } else {
                                        bindings.insert(*variable, &[observed]);
                                    }
                                }
                            }
                        }
                        progressed = true;
                    }
                    remaining_probes = next_probes;

                    let mut next_instrs = Vec::new();
                    let mut first_unbound_instr = None;
                    for instruction in remaining_instrs {
                        let instr = &firing.rule.action.instrs[instruction];
                        if let Some(variable) = instr.first_unbound_grounded_input(&bindings) {
                            first_unbound_instr.get_or_insert((instruction, variable));
                            next_instrs.push(instruction);
                            continue;
                        }
                        let succeeded =
                            state.run_instrs(std::slice::from_ref(instr), &mut bindings);
                        if state.changed {
                            return Err(GroundedRuleRunError::MutatingGuard {
                                invocation_ordinal: firing.invocation_ordinal,
                            });
                        }
                        if succeeded != 1 {
                            return Err(GroundedRuleRunError::GuardRejected {
                                invocation_ordinal: firing.invocation_ordinal,
                            });
                        }
                        progressed = true;
                    }
                    remaining_instrs = next_instrs;
                    if progressed {
                        continue;
                    }
                    if let Some((premise, variable)) = first_unbound_probe {
                        return Err(GroundedRuleRunError::UnboundPremiseKey {
                            invocation_ordinal: firing.invocation_ordinal,
                            premise,
                            variable,
                        });
                    }
                    let (instruction, variable) = first_unbound_instr
                        .expect("nonempty grounded dependency frontier has one missing input");
                    return Err(GroundedRuleRunError::UnboundBodyInput {
                        invocation_ordinal: firing.invocation_ordinal,
                        instruction,
                        variable,
                    });
                }
                drop(state);
                for (variable, expected) in firing.bindings.iter().copied() {
                    if bindings.get(variable) != Some(std::slice::from_ref(&expected)) {
                        return Err(GroundedRuleRunError::BindingMismatch {
                            invocation_ordinal: firing.invocation_ordinal,
                            variable,
                        });
                    }
                }
                for variable in firing.rule.action.used_vars.iter().copied() {
                    if bindings.get(variable).is_none() {
                        return Err(GroundedRuleRunError::UnboundHeadVariable {
                            invocation_ordinal: firing.invocation_ordinal,
                            variable,
                        });
                    }
                }
                prepared.push((
                    firing.invocation_ordinal,
                    Arc::clone(&firing.rule),
                    bindings,
                ));
            }

            let mut state = ExecutionState::new(self.read_only_view(), Default::default());
            state.defer_mutations_until(transaction.clone());
            for (invocation_ordinal, rule, mut bindings) in prepared {
                let succeeded =
                    state.run_instrs(&rule.action.instrs[rule.body_end..], &mut bindings);
                if succeeded != 1 || state.should_stop() {
                    return Err(GroundedRuleRunError::HeadRejected { invocation_ordinal });
                }
            }
            let changed = state.changed;
            drop(state);
            Ok(changed)
        }));

        let staged_change = match executed {
            Ok(Ok(outcome)) => outcome,
            Ok(Err(error)) => {
                transaction.abort();
                return Err(error);
            }
            Err(payload) => {
                transaction.abort();
                resume_unwind(payload);
            }
        };
        let commit_allowed = catch_unwind(AssertUnwindSafe(allow_commit));
        match commit_allowed {
            Ok(true) => {}
            Ok(false) => {
                transaction.abort();
                return Err(GroundedRuleRunError::CommitRejected);
            }
            Err(payload) => {
                transaction.abort();
                resume_unwind(payload);
            }
        }

        let pre_merge_time = pre_merge_timer.elapsed();
        let merge_timer = Instant::now();
        let committed = transaction.commit();
        assert!(
            committed.rebuild_cursors.is_empty(),
            "grounded rule heads unexpectedly registered rebuild cursors"
        );
        for table in committed.changed_tables {
            self.notification_list.notify(table);
        }
        let merged_change = self.merge_all();
        let merge_time = merge_timer.elapsed();
        Ok(GroundedRuleRunOutcome {
            changed: staged_change || merged_change,
            pre_merge_time,
            merge_time,
        })
    }
}
