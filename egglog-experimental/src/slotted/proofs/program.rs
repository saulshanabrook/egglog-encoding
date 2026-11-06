//! Resolved source programs and their proof-checking contexts.

use super::context::{ColumnKind, Constructor, ProofContext, SourceError, SourceRule, Union};
use super::format::SlottedProofStore;
use super::terms::{FreshSlots, slot_of};
use crate::slotted::slots::Slots;
use egglog::ast::{FunctionSubtype, GenericAction, ResolvedExpr, ResolvedNCommand};
use egglog::{TermDag, TermId};
use std::collections::BTreeMap;

/// An original slotted program after type resolution and rewrite desugaring.
/// Commands retain nested terms and original guards. Popped commands are absent.
/// Guard primitives carry validators for the visible constructors' binding scopes.
/// This program is independent of any proof's term arena and slot IDs.
#[derive(Clone, Debug, Default)]
pub struct ResolvedSlottedProgram {
    /// Typechecked source declarations, top-level actions, and rewrite rules.
    pub commands: Vec<ResolvedNCommand>,
    /// Binder argument indices for each constructor that binds names.
    /// Indices count all arguments, including payloads.
    pub binders: BTreeMap<String, Vec<usize>>,
}

impl ResolvedSlottedProgram {
    /// Build the checking context for this source program in `store`'s term arena.
    /// Source terms are added to the arena, preserving the slot identities named
    /// by `store`; other source names are assigned IDs as needed.
    ///
    /// Errors if slot names are invalid or ambiguous, globals cannot be resolved,
    /// rule names are duplicated, or a resolved command is unsupported.
    pub(super) fn for_proof(
        &self,
        store: &mut SlottedProofStore,
    ) -> Result<ProofContext, SourceError> {
        let mut names = BTreeMap::new();
        for (&id, name) in &store.slot_names {
            let name = Slots::default().intern(name).map_err(SourceError)?;
            if names.insert(name.clone(), id).is_some() {
                return Err(SourceError(format!("ambiguous proof slot name {name}")));
            }
        }
        self.context(&mut store.term_dag, names)
    }

    pub(super) fn context(
        &self,
        dag: &mut TermDag,
        names: BTreeMap<String, i64>,
    ) -> Result<ProofContext, SourceError> {
        self.materialize(dag, names, false)
    }

    pub(super) fn flattened_context(
        &self,
        dag: &mut TermDag,
        names: BTreeMap<String, i64>,
    ) -> Result<ProofContext, SourceError> {
        self.materialize(dag, names, true)
    }

    fn materialize(
        &self,
        dag: &mut TermDag,
        names: BTreeMap<String, i64>,
        refresh: bool,
    ) -> Result<ProofContext, SourceError> {
        let mut fresh = FreshSlots::new(
            (0..dag.size())
                .filter_map(|t| slot_of(dag, t))
                .chain(names.values().copied()),
        );
        let mut program = ProofContext {
            slot_names: names,
            ..Default::default()
        };
        for command in &self.commands {
            match command {
                ResolvedNCommand::Sort { name, .. } => {
                    program.sorts.insert(name.clone());
                }
                ResolvedNCommand::Function(decl)
                    if decl.subtype == FunctionSubtype::Constructor =>
                {
                    let sort = decl.schema.output().to_owned();
                    let binders = self
                        .binders
                        .get(&decl.name)
                        .map(Vec::as_slice)
                        .unwrap_or_default();
                    let columns = decl
                        .schema
                        .input
                        .iter()
                        .enumerate()
                        .map(|(i, ty)| {
                            if binders.contains(&i) {
                                ColumnKind::Binder
                            } else if ty == "Var" {
                                ColumnKind::Var
                            } else if ty == &sort {
                                ColumnKind::Child
                            } else {
                                ColumnKind::Payload(ty.clone())
                            }
                        })
                        .collect();
                    program.constructors.insert(
                        decl.name.clone(),
                        Constructor {
                            name: decl.name.clone(),
                            sort,
                            columns,
                        },
                    );
                }
                ResolvedNCommand::CoreAction(GenericAction::Let(_, name, expr)) => {
                    let term = ground(&mut program, dag, &mut fresh, expr)?;
                    let term = if refresh {
                        program.refresh_binders(dag, term)
                    } else {
                        term
                    };
                    program.lets.insert(name.name.clone(), term);
                }
                ResolvedNCommand::CoreAction(GenericAction::Union(_, lhs, rhs)) => {
                    let lhs = ground(&mut program, dag, &mut fresh, lhs)?;
                    let rhs = ground(&mut program, dag, &mut fresh, rhs)?;
                    let (lhs, rhs) = if refresh {
                        (
                            program.refresh_binders(dag, lhs),
                            program.refresh_binders(dag, rhs),
                        )
                    } else {
                        (lhs, rhs)
                    };
                    program.unions.push(Union { lhs, rhs });
                }
                ResolvedNCommand::NormRule { rule } => {
                    let rule = SourceRule::capture(rule.clone(), &program.lets);
                    if program
                        .rewrites
                        .insert(rule.rule.name.clone(), rule)
                        .is_some()
                    {
                        return Err(SourceError("duplicate source rule name".into()));
                    }
                }
                _ => return Err(SourceError("unsupported resolved slotted command".into())),
            }
        }
        Ok(program)
    }
}

pub(super) fn ground(
    program: &mut ProofContext,
    dag: &mut TermDag,
    fresh: &mut FreshSlots,
    expr: &ResolvedExpr,
) -> Result<TermId, SourceError> {
    for name in expr
        .vars()
        .map(|var| var.name)
        .filter(|name| name.starts_with('$'))
    {
        let name = Slots::default().intern(&name).map_err(SourceError)?;
        if !program.slot_names.contains_key(&name) {
            let numeric = name[1..]
                .parse::<i64>()
                .ok()
                .filter(|id| !program.slot_names.values().any(|other| other == id));
            let id = numeric.unwrap_or_else(|| fresh.fresh());
            fresh.reserve([id]);
            program.slot_names.insert(name, id);
        }
    }
    fn materialize(
        program: &ProofContext,
        dag: &mut TermDag,
        expr: &ResolvedExpr,
    ) -> Result<TermId, SourceError> {
        match expr {
            ResolvedExpr::Var(_, var) => program.ground_name(dag, &var.name),
            ResolvedExpr::Lit(_, literal) => Ok(dag.lit(literal.clone())),
            ResolvedExpr::Call(_, head, args) => {
                let args = args
                    .iter()
                    .map(|arg| materialize(program, dag, arg))
                    .collect::<Result<_, _>>()?;
                Ok(dag.app(head.name().to_owned(), args))
            }
        }
    }
    materialize(program, dag, expr)
}

#[cfg(test)]
#[path = "tests/program.rs"]
mod tests;
