// Registration compiles this IR before the generic queue executor consumes it;
// allow the staged frontier to compile cleanly while that executor is wired.
#![allow(dead_code)]

use std::collections::{BTreeMap, BTreeSet};

use anyhow::{Context, Result, bail, ensure};
use egglog_backend_trait::{
    BaseValues, ColumnTy, ExternalFunctionId, FunctionConfig, FunctionId, MergeAction, MergeFn,
    Value,
};
use egglog_numeric_id::NumericId;

use crate::AuthorityRegistries;
use crate::action_rule::FdDescriptor;
use crate::scalar_expr::ScalarExpression;
use crate::storage::{ScalarSqlType, TableInfo};

pub(crate) type MergeValueId = usize;

#[derive(Clone, Debug)]
pub(crate) struct MergeProgram {
    pub(crate) owner: FunctionId,
    pub(crate) n_keys: usize,
    pub(crate) n_vals: usize,
    pub(crate) n_identity_vals: Option<usize>,
    pub(crate) dependency_level: usize,
    pub(crate) ops: Vec<MergeOp>,
    pub(crate) actions: Vec<MergeProgramAction>,
    pub(crate) results: Vec<MergeValueId>,
    pub(crate) read_deps: BTreeSet<FunctionId>,
    pub(crate) write_targets: BTreeSet<FunctionId>,
    pub(crate) required_authorities: BTreeMap<ExternalFunctionId, u64>,
}

#[derive(Clone, Debug)]
pub(crate) struct MergeOp {
    pub(crate) ty: ColumnTy,
    pub(crate) kind: MergeOpKind,
}

#[derive(Clone, Debug)]
pub(crate) enum MergeOpKind {
    OldCol(usize),
    NewCol(usize),
    Const {
        value: Value,
        sql: String,
    },
    AssertEq {
        old: MergeValueId,
        new: MergeValueId,
    },
    Primitive {
        primitive: MergePrimitive,
        arguments: Vec<MergeValueId>,
    },
    Function {
        target: FunctionId,
        arguments: Vec<MergeValueId>,
    },
    Lookup {
        target: FunctionId,
        arguments: Vec<MergeValueId>,
    },
    UnsupportedUnionId,
}

#[derive(Clone, Debug)]
pub(crate) enum MergePrimitive {
    Fresh {
        token: ExternalFunctionId,
    },
    Fd {
        token: ExternalFunctionId,
        descriptor: FdDescriptor,
    },
    Scalar(ScalarExpression),
    Unauthenticated {
        token: ExternalFunctionId,
    },
}

#[derive(Clone, Debug)]
pub(crate) enum MergeProgramAction {
    Bind {
        slot: usize,
        value: MergeValueId,
    },
    Set {
        target: FunctionId,
        row: Vec<MergeValueId>,
    },
    UnsupportedUnion,
}

impl MergeProgram {
    pub(crate) fn ensure_proof_supported(&self, name: &str) -> Result<()> {
        ensure!(
            !self.ops.iter().any(|op| matches!(
                op.kind,
                MergeOpKind::Function { .. } | MergeOpKind::Lookup { .. }
            )),
            "DuckDB checkpoint-0 generic merge for `{name}` does not support Function or Lookup operations"
        );
        ensure!(
            !self.ops.iter().any(|op| matches!(
                op.kind,
                MergeOpKind::Primitive {
                    primitive: MergePrimitive::Fd { .. },
                    ..
                }
            )),
            "DuckDB checkpoint-0 generic merge for `{name}` does not support FD operations"
        );
        ensure!(
            !self
                .ops
                .iter()
                .any(|op| matches!(op.kind, MergeOpKind::UnsupportedUnionId)),
            "DuckDB generic merge for `{name}` does not support MergeFn::UnionId"
        );
        ensure!(
            !self
                .actions
                .iter()
                .any(|action| matches!(action, MergeProgramAction::UnsupportedUnion)),
            "DuckDB generic merge for `{name}` does not support MergeAction::Union"
        );
        Ok(())
    }
}

pub(crate) fn compile_merge_program<'a>(
    base_values: &'a BaseValues,
    tables: &[TableInfo],
    owner: FunctionId,
    config: &FunctionConfig,
    authorities: Option<&'a AuthorityRegistries<'a>>,
) -> Result<MergeProgram> {
    let mut compiler = Compiler {
        base_values,
        tables,
        owner,
        config,
        authorities,
        ops: Vec::new(),
        actions: Vec::new(),
        environment: Vec::new(),
        read_deps: BTreeSet::new(),
        write_targets: BTreeSet::new(),
        required_authorities: BTreeMap::new(),
    };
    let (actions, result) = match &config.merge {
        MergeFn::Block { actions, result } => (actions.as_slice(), result.as_ref()),
        result => (&[][..], result),
    };
    for action in actions {
        compiler.compile_action(action)?;
    }
    let result_exprs = match result {
        MergeFn::Columns(columns) => columns.as_slice(),
        result => std::slice::from_ref(result),
    };
    ensure!(
        result_exprs.len() == config.n_vals,
        "merge result arity changed after validation"
    );
    let n_keys = config.schema.len() - config.n_vals;
    let mut results = Vec::with_capacity(config.n_vals);
    for (column, expression) in result_exprs.iter().enumerate() {
        results.push(compiler.compile_expr(expression, config.schema[n_keys + column], column)?);
    }
    let dependency_level = compiler
        .read_deps
        .iter()
        .filter(|target| **target != owner)
        .map(|target| tables[target.rep() as usize].merge_program.dependency_level)
        .max()
        .unwrap_or(0)
        .checked_add(1)
        .ok_or_else(|| anyhow::anyhow!("generic merge dependency level overflow"))?;
    Ok(MergeProgram {
        owner,
        n_keys,
        n_vals: config.n_vals,
        n_identity_vals: config.n_identity_vals,
        dependency_level,
        ops: compiler.ops,
        actions: compiler.actions,
        results,
        read_deps: compiler.read_deps,
        write_targets: compiler.write_targets,
        required_authorities: compiler.required_authorities,
    })
}

struct Compiler<'a> {
    base_values: &'a BaseValues,
    tables: &'a [TableInfo],
    owner: FunctionId,
    config: &'a FunctionConfig,
    authorities: Option<&'a AuthorityRegistries<'a>>,
    ops: Vec<MergeOp>,
    actions: Vec<MergeProgramAction>,
    environment: Vec<MergeValueId>,
    read_deps: BTreeSet<FunctionId>,
    write_targets: BTreeSet<FunctionId>,
    required_authorities: BTreeMap<ExternalFunctionId, u64>,
}

impl Compiler<'_> {
    fn value_schema(&self) -> &[ColumnTy] {
        &self.config.schema[self.config.schema.len() - self.config.n_vals..]
    }

    fn target_schema(&self, target: FunctionId) -> Result<&[ColumnTy]> {
        if target == self.owner {
            Ok(&self.config.schema)
        } else {
            self.tables
                .get(target.rep() as usize)
                .map(|table| table.schema.as_slice())
                .ok_or_else(|| {
                    anyhow::anyhow!("generic merge references unknown target {}", target.rep())
                })
        }
    }

    fn push(&mut self, ty: ColumnTy, kind: MergeOpKind) -> MergeValueId {
        let id = self.ops.len();
        self.ops.push(MergeOp { ty, kind });
        id
    }

    fn compile_action(&mut self, action: &MergeAction) -> Result<()> {
        match action {
            MergeAction::Let { slot, value } => {
                ensure!(
                    *slot == self.environment.len(),
                    "merge Let slots must be ordered"
                );
                let expected = self.infer_expr_ty(value, 0)?;
                let value = self.compile_expr(value, expected, 0)?;
                self.environment.push(value);
                self.actions
                    .push(MergeProgramAction::Bind { slot: *slot, value });
            }
            MergeAction::Set(target, arguments) => {
                let schema = self.target_schema(*target)?.to_vec();
                ensure!(
                    arguments.len() == schema.len(),
                    "merge Set arity changed after validation"
                );
                let row = arguments
                    .iter()
                    .zip(schema)
                    .map(|(argument, expected)| self.compile_expr(argument, expected, 0))
                    .collect::<Result<Vec<_>>>()?;
                self.write_targets.insert(*target);
                self.actions.push(MergeProgramAction::Set {
                    target: *target,
                    row,
                });
            }
            MergeAction::Union(_, _) => self.actions.push(MergeProgramAction::UnsupportedUnion),
        }
        Ok(())
    }

    fn infer_expr_ty(&self, expression: &MergeFn, self_col: usize) -> Result<ColumnTy> {
        match expression {
            MergeFn::Old | MergeFn::New | MergeFn::AssertEq => self
                .value_schema()
                .get(self_col)
                .copied()
                .context("merge expression references a missing owner value column"),
            MergeFn::OldCol(column) | MergeFn::NewCol(column) => self
                .value_schema()
                .get(*column)
                .copied()
                .context("merge expression references a missing owner value column"),
            MergeFn::LetVar(slot) => {
                let id = *self
                    .environment
                    .get(*slot)
                    .context("merge LetVar is unbound")?;
                Ok(self.ops[id].ty)
            }
            MergeFn::Const { ty, .. } => Ok(*ty),
            MergeFn::Primitive { output, .. } => Ok(*output),
            MergeFn::Function(target, _) => self
                .target_schema(*target)?
                .last()
                .copied()
                .context("merge Function target has no output column"),
            MergeFn::Lookup(target, _) => {
                let schema = self.target_schema(*target)?;
                let n_keys = if *target == self.owner {
                    self.config.schema.len() - self.config.n_vals
                } else {
                    self.tables[target.rep() as usize].n_keys
                };
                schema
                    .get(n_keys)
                    .copied()
                    .context("merge Lookup target has no value column")
            }
            MergeFn::UnionId => Ok(ColumnTy::Id),
            MergeFn::Columns(_) | MergeFn::Block { .. } => {
                bail!("nested merge aggregate in generic program")
            }
        }
    }

    fn compile_expr(
        &mut self,
        expression: &MergeFn,
        expected: ColumnTy,
        self_col: usize,
    ) -> Result<MergeValueId> {
        let id = match expression {
            MergeFn::Old => {
                ensure!(
                    self.value_schema().get(self_col) == Some(&expected),
                    "mistyped Old in merge program"
                );
                self.push(expected, MergeOpKind::OldCol(self_col))
            }
            MergeFn::New => {
                ensure!(
                    self.value_schema().get(self_col) == Some(&expected),
                    "mistyped New in merge program"
                );
                self.push(expected, MergeOpKind::NewCol(self_col))
            }
            MergeFn::OldCol(column) => {
                ensure!(
                    self.value_schema()[*column] == expected,
                    "mistyped OldCol in merge program"
                );
                self.push(expected, MergeOpKind::OldCol(*column))
            }
            MergeFn::NewCol(column) => {
                ensure!(
                    self.value_schema()[*column] == expected,
                    "mistyped NewCol in merge program"
                );
                self.push(expected, MergeOpKind::NewCol(*column))
            }
            MergeFn::LetVar(slot) => {
                let id = *self
                    .environment
                    .get(*slot)
                    .ok_or_else(|| anyhow::anyhow!("merge LetVar is unbound"))?;
                ensure!(
                    self.ops[id].ty == expected,
                    "mistyped LetVar in merge program"
                );
                return Ok(id);
            }
            MergeFn::Const { value, ty } => {
                ensure!(*ty == expected, "mistyped Const in merge program");
                let sql = ScalarSqlType::from_column(self.base_values, expected)?
                    .sql_literal(self.base_values, *value)?;
                self.push(expected, MergeOpKind::Const { value: *value, sql })
            }
            MergeFn::AssertEq => {
                ensure!(
                    self.value_schema().get(self_col) == Some(&expected),
                    "mistyped AssertEq in merge program"
                );
                let old = self.push(expected, MergeOpKind::OldCol(self_col));
                let new = self.push(expected, MergeOpKind::NewCol(self_col));
                self.push(expected, MergeOpKind::AssertEq { old, new })
            }
            MergeFn::UnionId => self.push(expected, MergeOpKind::UnsupportedUnionId),
            MergeFn::Primitive {
                id,
                input,
                output,
                args,
                ..
            } => {
                ensure!(
                    *output == expected && input.len() == args.len(),
                    "mistyped primitive in merge program"
                );
                let arguments = args
                    .iter()
                    .zip(input)
                    .map(|(argument, &ty)| self.compile_expr(argument, ty, self_col))
                    .collect::<Result<Vec<_>>>()?;
                let primitive = if let Some(authorities) = self.authorities {
                    let Some(epoch) = authorities.authority_epochs.get(id).copied() else {
                        return Ok(self.push(
                            expected,
                            MergeOpKind::Primitive {
                                primitive: MergePrimitive::Unauthenticated { token: *id },
                                arguments,
                            },
                        ));
                    };
                    self.required_authorities.insert(*id, epoch);
                    if authorities.fresh_tokens.contains(id) {
                        ensure!(
                            *output == ColumnTy::Id
                                && input.len() == 1
                                && ScalarSqlType::from_column(self.base_values, input[0])?
                                    == ScalarSqlType::String,
                            "generic merge Fresh requires (String) -> Id"
                        );
                        MergePrimitive::Fresh { token: *id }
                    } else if let Some(descriptor) = authorities.fd_descriptors.get(id) {
                        MergePrimitive::Fd {
                            token: *id,
                            descriptor: descriptor.clone(),
                        }
                    } else {
                        MergePrimitive::Scalar(ScalarExpression::authenticate(
                            self.base_values,
                            authorities.native_primitives,
                            authorities.native_scalar_primitives,
                            *id,
                            input,
                            *output,
                        )?)
                    }
                } else {
                    MergePrimitive::Unauthenticated { token: *id }
                };
                self.push(
                    expected,
                    MergeOpKind::Primitive {
                        primitive,
                        arguments,
                    },
                )
            }
            MergeFn::Function(target, args) => {
                let schema = self.target_schema(*target)?.to_vec();
                let (&output, input) = schema
                    .split_last()
                    .context("merge Function target has no output column")?;
                ensure!(
                    output == expected,
                    "mistyped function result in merge program"
                );
                ensure!(
                    args.len() == input.len(),
                    "merge Function arity changed after validation"
                );
                let arguments = args
                    .iter()
                    .zip(input.iter().copied())
                    .map(|(argument, ty)| self.compile_expr(argument, ty, self_col))
                    .collect::<Result<Vec<_>>>()?;
                self.read_deps.insert(*target);
                self.push(
                    expected,
                    MergeOpKind::Function {
                        target: *target,
                        arguments,
                    },
                )
            }
            MergeFn::Lookup(target, args) => {
                let schema = self.target_schema(*target)?.to_vec();
                let n_keys = if *target == self.owner {
                    self.config.schema.len() - self.config.n_vals
                } else {
                    self.tables[target.rep() as usize].n_keys
                };
                ensure!(
                    schema[n_keys] == expected,
                    "mistyped lookup result in merge program"
                );
                ensure!(
                    args.len() == n_keys,
                    "merge Lookup key arity changed after validation"
                );
                let arguments = args
                    .iter()
                    .zip(schema.into_iter().take(n_keys))
                    .map(|(argument, ty)| self.compile_expr(argument, ty, self_col))
                    .collect::<Result<Vec<_>>>()?;
                self.read_deps.insert(*target);
                self.write_targets.insert(*target);
                self.push(
                    expected,
                    MergeOpKind::Lookup {
                        target: *target,
                        arguments,
                    },
                )
            }
            MergeFn::Columns(_) | MergeFn::Block { .. } => {
                bail!("nested merge aggregate in generic program")
            }
        };
        Ok(id)
    }
}
