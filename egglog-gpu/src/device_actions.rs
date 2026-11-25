//! Batched device action execution with explicit opaque-host-call boundaries.

use crate::{
    columns::{GpuOps, Matrix},
    storage::{Buffer, Store},
};
use egglog_core_relations::{
    ActionInstruction as Op, ExecutionState, QueryEntry as Entry, TableId, Variable, WriteVal,
};
use egglog_numeric_id::NumericId;
use std::{any::Any, collections::BTreeMap};

fn entry(e: Entry, vars: &[Variable]) -> (u32, u32) {
    match e {
        Entry::Const(v) => (0, v.rep()),
        Entry::Var(v) => (
            1,
            vars.iter().position(|w| *w == v).expect("bound variable") as u32,
        ),
    }
}
fn column(vars: &mut Vec<Variable>, dst: Variable) -> usize {
    if let Some(i) = vars.iter().position(|&v| v == dst) {
        i
    } else {
        vars.push(dst);
        vars.len() - 1
    }
}
fn table(state: &ExecutionState, id: TableId) -> Matrix {
    state
        .get_table(id)
        .as_any()
        .downcast_ref::<Store>()
        .expect("replacement storage")
        .current()
}
fn stage(state: &mut ExecutionState, table: TableId, rows: Matrix, remove: bool) {
    state.stage_batch(table, |buffer| {
        (buffer as &mut dyn Any)
            .downcast_mut::<Buffer>()
            .expect("replacement mutation buffer")
            .stage_device(rows, remove);
    });
}
fn write_columns(
    vals: &[WriteVal],
    vars: &[Variable],
    rows: usize,
    state: &ExecutionState,
) -> Result<Vec<(u32, u32)>, String> {
    vals.iter()
        .map(|val| {
            Ok(match *val {
                WriteVal::QueryEntry(e) => entry(e, vars),
                WriteVal::CurrentVal(c) => (3, c as u32),
                WriteVal::IncCounter(c) => (2, state.reserve_counter(c, rows)?.start as u32),
            })
        })
        .collect()
}

pub(crate) fn run(
    gpu: &GpuOps,
    ops: &[Op],
    vars: Vec<Variable>,
    bindings: Matrix,
    state: &mut ExecutionState,
) -> Result<usize, String> {
    if bindings.rows == 0 || state.should_stop() {
        return Ok(0);
    }
    if ops.is_empty() {
        return Ok(bindings.rows);
    }
    let payload = ops
        .iter()
        .map(|op| match op {
            Op::Insert { vals, .. } => vals.len(),
            Op::InsertIfEq { vals, .. } => vals.len(),
            Op::Remove { args, .. }
            | Op::Lookup { args, .. }
            | Op::LookupWithDefault { args, .. } => args.len(),
            Op::LookupOrInsertDefault { args, default, .. } => args.len() + default.len(),
            Op::LookupWithFallback { table_key, .. } => table_key.len(),
            _ => 0,
        })
        .max()
        .unwrap_or(0);
    // At most one new binding per instruction. Include widened request payloads
    // and paired lookup readbacks as well as ordinary action output rows.
    let max_columns = vars
        .len()
        .checked_add(ops.len())
        .and_then(|n| n.checked_add(payload))
        .and_then(|n| n.checked_add(2))
        .ok_or("action width overflow")?;
    let batches = gpu.split_for_width(bindings, max_columns)?;
    run_batches(gpu, ops, vars, batches, state)
}

fn run_batches(
    gpu: &GpuOps,
    ops: &[Op],
    mut vars: Vec<Variable>,
    mut batches: Vec<Matrix>,
    state: &mut ExecutionState,
) -> Result<usize, String> {
    // Finish each instruction across all pieces before starting the next one.
    // In particular, counter reads, host effects and later failures must keep
    // the same instruction-major boundaries as an unpartitioned batch.
    for op in ops {
        let old_vars = vars.clone();
        let mut next = Vec::new();
        for batch in batches {
            if state.should_stop() {
                return Ok(0);
            }
            if batch.rows == 0 {
                continue;
            }
            let (bound, batch) = run_one(gpu, op, old_vars.clone(), batch, state)?;
            vars = bound;
            if batch.rows > 0 {
                next.push(batch);
            }
        }
        batches = next;
        if batches.is_empty() {
            return Ok(0);
        }
    }
    Ok(if state.should_stop() {
        0
    } else {
        batches.iter().map(|b| b.rows).sum()
    })
}

fn run_one(
    gpu: &GpuOps,
    op: &Op,
    mut vars: Vec<Variable>,
    mut bindings: Matrix,
    state: &mut ExecutionState,
) -> Result<(Vec<Variable>, Matrix), String> {
    match op {
        Op::ReadCounter { counter, dst } => {
            bindings = gpu.bind_constant(
                &bindings,
                state.read_counter(*counter) as u32,
                column(&mut vars, *dst),
            )?;
        }
        Op::Insert { table, vals, bind } => {
            let rows = gpu.project(
                &bindings,
                &write_columns(vals, &vars, bindings.rows, state)?,
            )?;
            if let Some((c, dst)) = bind {
                bindings = gpu.bind(&bindings, &rows, c.index(), column(&mut vars, *dst))?;
            }
            stage(state, *table, rows, false);
        }
        Op::Remove { table, args } => {
            let rows = gpu.project(
                &bindings,
                &args.iter().map(|&e| entry(e, &vars)).collect::<Vec<_>>(),
            )?;
            stage(state, *table, rows, true);
        }
        Op::InsertIfEq { table, l, r, vals } => {
            let selected = gpu.filter(
                bindings.clone(),
                true,
                &[(entry(*l, &vars), entry(*r, &vars))],
            )?;
            let rows = gpu.project(
                &selected,
                &vals.iter().map(|&e| entry(e, &vars)).collect::<Vec<_>>(),
            )?;
            stage(state, *table, rows, false);
        }
        Op::AssertEq(l, r) | Op::AssertNe(l, r) => {
            bindings = gpu.filter(
                bindings,
                matches!(op, Op::AssertEq(..)),
                &[(entry(*l, &vars), entry(*r, &vars))],
            )?;
        }
        Op::AssertAnyNe { ops, divider } => {
            let pairs: Vec<_> = ops[..*divider]
                .iter()
                .zip(&ops[*divider..])
                .map(|(&l, &r)| (entry(l, &vars), entry(r, &vars)))
                .collect();
            bindings = gpu.filter(bindings, false, &pairs)?;
        }
        Op::LookupOrInsertDefault {
            table: id,
            args,
            default,
            dst_col,
            dst_var,
        } => {
            let keys = gpu.project(
                &bindings,
                &args.iter().map(|&e| entry(e, &vars)).collect::<Vec<_>>(),
            )?;
            let mut request_cols: Vec<_> = args.iter().map(|&e| entry(e, &vars)).collect();
            request_cols.extend((0..bindings.cols).map(|i| (1, i as u32)));
            // Constants do not distinguish requests. Deduplicate the
            // original binding rows by their variable key columns before
            // widening the compact request payload with copies of keys.
            let key_columns: Vec<_> = args
                .iter()
                .filter_map(|&e| {
                    let (kind, col) = entry(e, &vars);
                    (kind == 1).then_some(col as usize)
                })
                .collect();
            let unique_bindings = gpu.unique_by(bindings.clone(), &key_columns)?;
            let requests = gpu.project(&unique_bindings, &request_cols)?;
            let requested_keys = gpu.project(
                &requests,
                &(0..args.len()).map(|i| (1, i as u32)).collect::<Vec<_>>(),
            )?;
            let current = table(state, *id);
            let existing = gpu.lookup(&requested_keys, &current, dst_col.index())?;
            // Only the compact unique request set crosses this boundary.
            // Shared predictions make separate rules and opaque primitives
            // agree on ids before the next table commit.
            let (requested, existing) = gpu.download_pair(&requests, &existing)?;
            let mut resolved = Vec::new();
            let mut misses = Vec::new();
            for (request, found) in requested.iter().zip(existing) {
                let key = &request[..args.len()];
                let val = if found[0].rep() == 1 {
                    Some(found[1])
                } else {
                    state.predicted_row(*id, key).map(|r| r[dst_col.index()])
                };
                if let Some(val) = val {
                    let mut row = key.to_vec();
                    row.push(val);
                    resolved.push(row);
                } else {
                    misses.push(request[args.len()..].to_vec());
                }
            }
            if !misses.is_empty() {
                let miss_bindings = gpu.upload(&misses, bindings.cols)?;
                let mut columns: Vec<_> = args.iter().map(|&e| entry(e, &vars)).collect();
                columns.extend(write_columns(default, &vars, misses.len(), state)?);
                let fresh = gpu.project(&miss_bindings, &columns)?;
                for row in gpu.download(&fresh)? {
                    let key = &row[..args.len()];
                    let row = state.publish_prediction(*id, key, &row);
                    let mut resolution = key.to_vec();
                    resolution.push(row[dst_col.index()]);
                    resolved.push(resolution);
                }
            }
            if resolved.len() == 1 {
                // Every requester has the same key, so scatter is a constant
                // assignment rather than another keyed lookup and bind.
                bindings = gpu.bind_constant(
                    &bindings,
                    resolved[0][args.len()].rep(),
                    column(&mut vars, *dst_var),
                )?;
            } else {
                let resolutions = gpu.upload(&resolved, args.len() + 1)?;
                let looked_up = gpu.lookup(&keys, &resolutions, args.len())?;
                bindings = gpu.bind(&bindings, &looked_up, 1, column(&mut vars, *dst_var))?;
            }
        }
        Op::Lookup {
            table: id,
            args,
            dst_col,
            dst_var,
        } => {
            let keys = gpu.project(
                &bindings,
                &args.iter().map(|&e| entry(e, &vars)).collect::<Vec<_>>(),
            )?;
            let found = gpu.lookup(&keys, &table(state, *id), dst_col.index())?;
            bindings = gpu.bind(&bindings, &found, 1, column(&mut vars, *dst_var))?;
            let width = bindings.cols;
            let marked = gpu.bind(&bindings, &found, 0, width)?;
            let marked = gpu.filter(marked, true, &[((1, width as u32), (0, 1))])?;
            bindings = gpu.project(
                &marked,
                &(0..width).map(|c| (1, c as u32)).collect::<Vec<_>>(),
            )?;
        }
        Op::LookupWithDefault {
            table: id,
            args,
            dst_col,
            dst_var,
            default,
        } => {
            let keys = gpu.project(
                &bindings,
                &args.iter().map(|&e| entry(e, &vars)).collect::<Vec<_>>(),
            )?;
            let found = gpu.lookup(&keys, &table(state, *id), dst_col.index())?;
            let resolved = gpu.resolve_lookup(&bindings, &found, entry(*default, &vars))?;
            bindings = gpu.bind(&bindings, &resolved, 0, column(&mut vars, *dst_var))?;
        }
        Op::LookupWithFallback {
            table: id,
            table_key,
            func,
            func_args,
            dst_col,
            dst_var,
        } => {
            let keys = gpu.project(
                &bindings,
                &table_key
                    .iter()
                    .map(|&e| entry(e, &vars))
                    .collect::<Vec<_>>(),
            )?;
            let found = gpu.lookup(&keys, &table(state, *id), dst_col.index())?;
            let old_width = bindings.cols;
            let marked = gpu.bind(&bindings, &found, 0, old_width)?;
            let misses = gpu.filter(marked, true, &[((1, old_width as u32), (0, 0))])?;
            let misses = gpu.project(
                &misses,
                &(0..old_width).map(|c| (1, c as u32)).collect::<Vec<_>>(),
            )?;
            let old_vars = vars.clone();
            let hits = gpu.bind(&bindings, &found, 1, column(&mut vars, *dst_var))?;
            let width = hits.cols;
            let hits = gpu.bind(&hits, &found, 0, width)?;
            let hits = gpu.filter(hits, true, &[((1, width as u32), (0, 1))])?;
            let hits = gpu.project(
                &hits,
                &(0..width).map(|c| (1, c as u32)).collect::<Vec<_>>(),
            )?;
            let call = Op::External {
                func: *func,
                args: func_args.clone(),
                dst: *dst_var,
            };
            let resolved = host_call(gpu, &call, &old_vars, &vars, &misses, state)?;
            bindings = gpu.concat(&hits, &resolved)?;
        }
        // Opaque primitives may read/write tables or intern arbitrary host
        // values. Their ABI is intentionally a synchronization boundary.
        Op::External { .. } | Op::ExternalWithFallback { .. } => {
            let dst = match op {
                Op::External { dst, .. } | Op::ExternalWithFallback { dst, .. } => *dst,
                _ => unreachable!(),
            };
            let old_vars = vars.clone();
            column(&mut vars, dst);
            bindings = host_call(gpu, op, &old_vars, &vars, &bindings, state)?;
        }
    }
    Ok((vars, bindings))
}

fn host_call(
    gpu: &GpuOps,
    op: &Op,
    old_vars: &[Variable],
    vars: &[Variable],
    bindings: &Matrix,
    state: &mut ExecutionState,
) -> Result<Matrix, String> {
    let mut results = Vec::new();
    for row in gpu.download(bindings)? {
        if state.should_stop() {
            break;
        }
        let mut mapped: BTreeMap<_, _> = old_vars.iter().copied().zip(row).collect();
        if super::runtime::run_actions(std::slice::from_ref(op), &mut mapped, state)? {
            results.push(vars.iter().map(|v| mapped[v]).collect());
        }
    }
    gpu.upload(&results, vars.len())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{AdapterMode, DeviceJoin};
    use egglog_core_relations::{
        BackendTable, ColumnId, Database, TableSchema, Value, WrappedTable,
    };
    use std::sync::Arc;

    #[test]
    #[ignore = "requires software Vulkan"]
    fn chunks_share_predictions_and_preserve_instruction_boundaries() {
        let gpu = Arc::new(GpuOps::new(
            Arc::new(DeviceJoin::new(AdapterMode::Software).unwrap()),
            100,
        ));
        let mut db = Database::new();
        let mut add = |schema| {
            db.add_wrapped_table_named(
                WrappedTable::new(Store::new(
                    BackendTable {
                        read_only: false,
                        schema,
                        timestamp: None,
                        rebuild_columns: vec![],
                        merge: Some(Box::new(|_, old, new, out| {
                            if old == new {
                                false
                            } else {
                                out.extend_from_slice(new);
                                true
                            }
                        })),
                    },
                    Some(gpu.clone()),
                )),
                "chunk-test".into(),
                [],
                [],
            )
        };
        let ids = add(TableSchema::Flat { n_cols: 1 });
        let lookup = add(TableSchema::Fd {
            n_keys: 1,
            n_vals: 1,
        });
        let output = add(TableSchema::Flat { n_cols: 5 });
        let counter = db.add_counter();
        db.merge_all();
        let [x, before, middle, id, after] = [0, 1, 2, 3, 4].map(Variable::new);
        let ops = [
            Op::ReadCounter {
                counter,
                dst: before,
            },
            Op::Insert {
                table: ids,
                vals: vec![WriteVal::IncCounter(counter)],
                bind: None,
            },
            Op::ReadCounter {
                counter,
                dst: middle,
            },
            Op::LookupOrInsertDefault {
                table: lookup,
                args: vec![Entry::Const(Value::new(7))],
                default: vec![WriteVal::IncCounter(counter)],
                dst_col: ColumnId::new(1),
                dst_var: id,
            },
            Op::ReadCounter {
                counter,
                dst: after,
            },
            Op::AssertNe(Entry::Var(x), Entry::Const(Value::new(4))),
            Op::Insert {
                table: output,
                vals: [x, before, middle, id, after]
                    .map(|v| WriteVal::QueryEntry(Entry::Var(v)))
                    .to_vec(),
                bind: None,
            },
        ];
        let batches = (0..3)
            .map(|chunk| {
                gpu.upload(
                    &[vec![Value::new(chunk * 2)], vec![Value::new(chunk * 2 + 1)]],
                    1,
                )
                .unwrap()
            })
            .collect();
        db.with_execution_state(None, |state| {
            assert_eq!(run_batches(&gpu, &ops, vec![x], batches, state).unwrap(), 5);
            assert_eq!(state.read_counter(counter), 7);
        });
        db.merge_all();
        assert_eq!(
            db.get_table(ids).len(),
            6,
            "later filtering preserves earlier writes"
        );
        let table = db.get_table(output);
        let mut rows: Vec<_> = table
            .scan(table.all().as_ref())
            .iter()
            .map(|(_, row)| row.to_vec())
            .collect();
        rows.sort();
        let expected: Vec<_> = (0..6)
            .filter(|&x| x != 4)
            .map(|x| [x, 0, 6, 6, 7].map(Value::new).to_vec())
            .collect();
        assert_eq!(rows, expected);
    }
}
