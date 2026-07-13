//! Host-side iteration driver for the Differential Dataflow backend.
//!
//! One `run_rules` call = **one bounded egglog iteration**. The body join runs
//! on the in-process, build-once, epoch-driven raw differential-dataflow
//! dataflow (`crate::dd_native`); this module owns the orchestration around it:
//!
//! 1. compute every rule's matches against the same pre-iteration relation
//!    state, following egglog's "match, then apply" model for one bounded hop;
//! 2. drive the ruleset's persistent fused DD dataflow with the per-relation
//!    signed delta vs. what that dataflow was last fed, then re-run body primitives
//!    (`!=` guards, value-computing prims) host-side over the produced bindings;
//! 3. for every surviving binding, execute the head ops in order — `set` /
//!    `remove` / `subsume` writes, RHS `lookup` (eq-sort constructor: create on
//!    miss), RHS primitive `call`, `union`, `panic`;
//! 4. apply all collected writes/removes to the mirror, folding each merge
//!    function's `set`s into a single value per key by its merge mode.
//!
//! ## The engine split
//!
//! Relational table-atom joins are the only operations on the DD engine, and
//! there is no host nested-loop fallback. Any rule the DD plan cannot lower (a
//! binding row exceeding the fixed width cap [`crate::dd_native::W`], or any
//! shape `plan_join` rejects) `panic!`s with a specific reason. Body primitives
//! and head actions are applied host-side here.
//!
//! Primitives are invoked through `Database::with_execution_state`, so they see
//! the same interned base `Value`s the frontend created and preserve bit-for-bit
//! value parity with the reference backend.

use anyhow::{anyhow, Result};
use egglog_backend_trait::{FunctionId, Value};
use egglog_numeric_id::NumericId;
use hashbrown::{HashMap, HashSet};

use crate::compile::{
    row_col, slot_lookup, BodyOp, HeadOp, MergeMode, ReadKey, ReadMode, Row, RuleIr, Slot,
};
use crate::EGraph;

/// Binding environment: variable id → bound `u32` value.
pub(crate) type Env = HashMap<u32, u32>;

type DdDeltaRows = HashMap<ReadKey, Vec<(Vec<u32>, isize)>>;

/// Retractions batched per function: the key length plus the set of keys to
/// remove, so one `retain` pass drops them all.
type RemovesByFunc = HashMap<FunctionId, (usize, HashSet<Box<[u32]>>)>;

/// Map the fused worker's rule order back to positions in the current caller.
/// The worker cache key identifies a set of rule ids, so a cache hit does not
/// imply that the caller supplied those ids in the original build order.
fn fused_caller_positions(
    atom_positions: &[usize],
    atom_rule_idxs: &[usize],
    fused_rule_idxs: &[usize],
) -> Result<Vec<usize>> {
    if atom_positions.len() != atom_rule_idxs.len() || atom_rule_idxs.len() != fused_rule_idxs.len()
    {
        return Err(anyhow!(
            "fused rule mapping length mismatch: caller positions={}, caller ids={}, fused ids={}",
            atom_positions.len(),
            atom_rule_idxs.len(),
            fused_rule_idxs.len()
        ));
    }

    let mut caller_by_rule = HashMap::with_capacity(atom_rule_idxs.len());
    for (&rule_idx, &position) in atom_rule_idxs.iter().zip(atom_positions) {
        if caller_by_rule.insert(rule_idx, position).is_some() {
            return Err(anyhow!(
                "duplicate caller rule index {rule_idx} in fused ruleset"
            ));
        }
    }

    let mut seen = HashSet::with_capacity(fused_rule_idxs.len());
    let mut positions = Vec::with_capacity(fused_rule_idxs.len());
    for &rule_idx in fused_rule_idxs {
        if !seen.insert(rule_idx) {
            return Err(anyhow!(
                "duplicate cached rule index {rule_idx} in fused ruleset"
            ));
        }
        let position = caller_by_rule.get(&rule_idx).copied().ok_or_else(|| {
            anyhow!("cached fused rule index {rule_idx} is absent from the caller ruleset")
        })?;
        positions.push(position);
    }

    Ok(positions)
}

/// A pending write to apply after all matches are computed.
enum Write {
    /// Insert/overwrite a full row.
    Set(FunctionId, Row),
    /// Retract by key (the slots address inputs for a function, whole row for a
    /// relation).
    Remove(FunctionId, Vec<u32>),
    /// Soft-delete: move the row(s) whose leading columns match this prefix into
    /// the `subsumed` side-set (hidden from ordinary matching, still present).
    Subsume(FunctionId, Vec<u32>),
}

/// One bounded egglog iteration with the body join running on the in-process,
/// build-once, epoch-driven raw differential-dataflow dataflow
/// (`crate::dd_native`).
///
/// Compute the signed `+/-` delta of each distinct body-relation view vs. the
/// rows last fed to the ruleset's persistent fused DD dataflow. Each nonempty
/// removal or insertion phase steps the shared worker, feeding only deltas into
/// never-cleared `InputSession`s. Positive per-rule binding deltas become envs;
/// body primitives and head actions then run host-side. Writes and FD merges are
/// applied afterward so results are bit-exact.
pub fn run_iteration(eg: &mut EGraph, rule_idxs: &[usize]) -> Result<bool> {
    // Every rule — including the term encoder's canonicalization rules — lowers
    // as an ordinary rule and joins on the fused DD worker; there is no special
    // casing for any rule kind.

    // Collect each rule's index + IR up front (clone to avoid borrow conflicts
    // while we also mutate the mirror via lookups). Every rule takes the same
    // atom-rule path and joins on the fused DD worker.
    let rules: Vec<(usize, RuleIr)> = rule_idxs
        .iter()
        .filter_map(|&i| eg.rules.get(i).and_then(|r| r.clone()).map(|r| (i, r)))
        .collect();

    // Snapshot the fresh-id counter: any hash-cons (`lookup_or_create`) this
    // call advances it, the O(1) signal that a new term row was created.
    let next_id_at_start = eg.next_id;

    let mut writes: Vec<Write> = Vec::new();
    // Iteration-scoped `key -> output` index for `lookup_or_create` (eq-sort
    // constructor hash-cons). Built lazily per function so repeated lookups in
    // one iteration are O(1) instead of rescanning the growing mirror each time.
    let mut lookup_index: HashMap<FunctionId, HashMap<Box<[u32]>, u32>> = HashMap::new();

    // Compute every rule's binding envs FIRST (so the whole atom-bearing ruleset
    // runs on one fused DD worker via `fused_bindings`), THEN
    // apply head actions in the original rule firing order. Atom-less rules
    // (`(rule () …)`) have no input relation to drive the DD dataflow, so they
    // stay host-side (fire once); they are computed inline below.
    let envs_by_rule = fused_bindings(eg, &rules)?;

    for ((_, rule), envs) in rules.iter().zip(envs_by_rule.into_iter()) {
        for mut env in envs {
            apply_head(eg, &rule.head, &mut env, &mut writes, &mut lookup_index)?;
        }
    }

    // Apply collected writes to the mirror.
    //
    // Removes are BATCHED per function: applying each `Write::Remove` with its
    // own `set.retain` scan is O(|removes| · |state|) — quadratic. We collect all
    // retraction keys per function into a hash set, then do a SINGLE `retain`
    // pass per touched function: O(|state|) total. Removes are applied FIRST
    // (batched), then Sets — preserving the term encoder's `(@uf)` "delete old
    // leader, set new leader" delete-then-set ordering.
    //
    // `changed` is computed INCREMENTALLY as writes land (O(delta)), not via a
    // full before/after content compare. A hash-cons in `lookup_or_create`
    // always allocates a fresh id, so any term created this call advances
    // `next_id` — that alone is a real mirror change.
    let mut changed = eg.next_id != next_id_at_start;
    let mut removes_by_func: RemovesByFunc = HashMap::new();
    let mut sets: Vec<(FunctionId, Row)> = Vec::new();
    let mut subsumes: Vec<(FunctionId, Vec<u32>)> = Vec::new();
    for w in writes {
        match w {
            Write::Set(f, row) => sets.push((f, row)),
            Write::Remove(f, key) => {
                let entry = removes_by_func
                    .entry(f)
                    .or_insert_with(|| (key.len(), HashSet::new()));
                entry.1.insert(key.into_boxed_slice());
            }
            Write::Subsume(f, prefix) => subsumes.push((f, prefix)),
        }
    }
    for (f, (keylen, keys)) in removes_by_func {
        // A `delete`/rebuild retraction clears the row from BOTH the live mirror
        // and the subsumed side-set (a rebuilt-away subsumed row must not linger).
        changed |= eg.remove_matching_keys(f, keylen, &keys);
    }
    // Apply sets. A plain relation (whole-row key) just inserts. A merge function
    // (Old/New/Min) folds each new value against the CURRENT value for its key by
    // the merge mode; the new values are folded in EMISSION order so `New`/`Old`
    // are insertion-order-correct — the pre-set mirror value is the "old" one and
    // the value set this call is the "new" one. (The mirror is an unordered
    // `HashSet`, so a fold that sorted the candidate rows would pick the wrong
    // winner for `New`/`Old`: e.g. a `New` merge of `@UF_Mf` where a leader
    // changes from `3` to `1` must keep `1`, not the sort-larger old value `3`.)
    let mut merge_by_func: HashMap<FunctionId, Vec<Row>> = HashMap::new();
    for (f, row) in sets {
        let arity = eg.info(f).arity;
        let merge = eg.merge_mode(f);
        let is_merge_fn = matches!(
            merge,
            MergeMode::Old | MergeMode::New | MergeMode::Min | MergeMode::Computed
        );
        if arity == 0 || !is_merge_fn {
            changed |= eg.insert_live_row(f, row);
        } else {
            merge_by_func.entry(f).or_default().push(row);
        }
    }
    for (f, rows) in merge_by_func {
        changed |= eg.apply_merge_sets(f, &rows)?;
    }
    // Subsumes last: a row `set` this iteration can then be subsumed, and the
    // move reads the just-updated live mirror.
    for (f, prefix) in subsumes {
        changed |= eg.subsume_rows(f, &prefix);
    }

    Ok(changed)
}

/// Compute every rule's binding envs in ONE fused pass: the whole atom-bearing
/// ruleset's body joins run on a SINGLE shared timely worker
/// ([`dd_native::FusedDdJoin`]) clocked once this iteration, then each rule's
/// host-side body primitives are re-run over its own bindings. Atom-less rules
/// (`(rule () …)`) have no input relation to drive the DD dataflow, so they are
/// fired once host-side. Returns a `Vec<Vec<Env>>` parallel to `rules` (same
/// order), ready for `apply_head`.
fn fused_bindings(eg: &mut EGraph, rules: &[(usize, RuleIr)]) -> Result<Vec<Vec<Env>>> {
    use crate::dd_native;

    let mut out: Vec<Vec<Env>> = vec![Vec::new(); rules.len()];

    // Partition: atom-bearing rules drive the fused DD worker; atom-less rules
    // fire once host-side. Record each atom-bearing rule's POSITION in `rules` so
    // we can scatter the fused output back into `out` in the caller's order.
    let mut atom_positions: Vec<usize> = Vec::new();
    let mut atom_rule_idxs: Vec<usize> = Vec::new();
    for (pos, (idx, rule)) in rules.iter().enumerate() {
        let has_atoms = rule.body.iter().any(|op| matches!(op, BodyOp::Atom(_)));
        if has_atoms {
            atom_positions.push(pos);
            atom_rule_idxs.push(*idx);
        } else {
            // Atom-less rule: fire once (presence in `seen` = already fired).
            if eg.seen.contains_key(idx) {
                continue;
            }
            eg.seen.insert(*idx, ());
            let mut envs: Vec<Env> = vec![Env::new()];
            for op in &rule.body {
                envs = step_prim(eg, op, envs)?;
                if envs.is_empty() {
                    break;
                }
            }
            out[pos] = envs;
        }
    }

    if atom_positions.is_empty() {
        return Ok(out);
    }

    // The fused join is keyed by the SORTED atom-bearing rule-index list (the
    // ruleset identity). Build it ONCE (lazily) per distinct ruleset, planning
    // each rule. Any shape `plan_join` rejects PANICS (no host fallback; the DD
    // dataflow is the only join path).
    let mut key: Vec<usize> = atom_rule_idxs.clone();
    key.sort_unstable();

    if !eg.dd_fused.contains_key(&key) {
        // Plan in the SAME order as `atom_positions` so the fused build order
        // matches our scatter order (the fused join preserves plan order).
        let mut plans: Vec<(usize, dd_native::JoinPlan)> = Vec::with_capacity(atom_positions.len());
        for (&pos, &idx) in atom_positions.iter().zip(atom_rule_idxs.iter()) {
            let rule = &rules[pos].1;
            let plan = match dd_native::plan_join(rule) {
                Ok(p) => p,
                Err(reason) => panic!(
                    "Differential Dataflow join cannot lower rule {:?}: {reason} \
                     (no host fallback; the DD dataflow is the only join path)",
                    rule.name
                ),
            };
            plans.push((idx, plan));
        }
        let fused = dd_native::FusedDdJoin::build(&plans)?;
        eg.dd_fused.insert(key.clone(), fused);
    }

    // Capture the fused worker's build order and map each output slot back to
    // the current caller by stable rule id. The sorted cache key only proves set
    // equality; it does not prove that this call uses the original order.
    let (fused_rule_idxs, fused_body_reads): (Vec<usize>, Vec<Vec<ReadKey>>) = {
        let fused = eg.dd_fused.get(&key).expect("fused join present");
        (
            fused.rule_indices(),
            (0..fused.rule_indices().len())
                .map(|p| fused.rule_body_reads(p).to_vec())
                .collect(),
        )
    };
    let fused_positions =
        fused_caller_positions(&atom_positions, &atom_rule_idxs, &fused_rule_idxs)?;

    // Each atom-bearing rule's canonical var order (for env reconstruction).
    let var_orders: Vec<Vec<u32>> = fused_positions
        .iter()
        .map(|&pos| {
            let rule = &rules[pos].1;
            dd_native::plan_join(rule)
                .expect("plan re-derivable")
                .var_order()
        })
        .collect();

    // Distinct relation read views across the whole ruleset. We diff versioned
    // current snapshots rather than plain row sets: if another ruleset removes and
    // reinserts the same row between two invocations, the row is present in both
    // end states but has a fresh version. Feeding `-row` then `+row` as separate
    // DD steps preserves the reference backend's hidden-timestamp behavior
    // without replaying transient rows that are no longer visible.
    let mut all_reads: Vec<ReadKey> = Vec::new();
    for bf in &fused_body_reads {
        for &read in bf {
            if !all_reads.contains(&read) {
                all_reads.push(read);
            }
        }
    }
    let mut removals_batch: DdDeltaRows = HashMap::new();
    let mut insertions_batch: DdDeltaRows = HashMap::new();
    {
        let fed = eg.dd_fused_fed_versions.entry(key.clone()).or_default();
        for &read in &all_reads {
            let cur = match read.mode {
                ReadMode::Live => eg.live_versions.get(&read.func),
                ReadMode::Subsumed => eg.subsumed_versions.get(&read.func),
                ReadMode::All => eg.all_versions.get(&read.func),
            };
            let cur_empty: HashMap<Row, u64> = HashMap::new();
            let cur = cur.unwrap_or(&cur_empty);
            let prev = fed.entry(read).or_default();
            if prev == cur {
                continue;
            }

            let mut removals = Vec::new();
            let mut insertions = Vec::new();
            for row in prev.keys() {
                if !cur.contains_key(row) {
                    removals.push((row.to_vec(), -1));
                }
            }
            for (row, version) in cur {
                match prev.get(row) {
                    None => insertions.push((row.to_vec(), 1)),
                    Some(prev_version) if prev_version != version => {
                        removals.push((row.to_vec(), -1));
                        insertions.push((row.to_vec(), 1));
                    }
                    Some(_) => {}
                }
            }
            if !removals.is_empty() {
                removals_batch.insert(read, removals);
            }
            if !insertions.is_empty() {
                insertions_batch.insert(read, insertions);
            }
            *prev = cur.clone();
        }
    }
    let mut delta_batches: Vec<DdDeltaRows> = Vec::new();
    if !removals_batch.is_empty() {
        delta_batches.push(removals_batch);
    }
    if !insertions_batch.is_empty() {
        delta_batches.push(insertions_batch);
    }

    // Step the shared worker once per nonempty signed-delta phase. A version
    // change may require a removal phase followed by an insertion phase.
    let mut per_rule_bindings = vec![Vec::new(); fused_positions.len()];
    {
        let fused = eg.dd_fused.get_mut(&key).expect("fused join present");
        for delta in &delta_batches {
            let stepped = fused.step(delta)?;
            for (acc, rows) in per_rule_bindings.iter_mut().zip(stepped) {
                acc.extend(rows);
            }
        }
    }

    // Turn each rule's positive binding deltas into envs; re-run its body prims
    // host-side. Negative weights are integral bookkeeping (a body row retracted)
    // — egglog heads are monotone-fire, so we do NOT re-fire on disappearance.
    for (fpos, bindings) in per_rule_bindings.into_iter().enumerate() {
        let caller_pos = fused_positions[fpos];
        let rule = &rules[caller_pos].1;
        let var_order = &var_orders[fpos];
        let mut envs: Vec<Env> = Vec::new();
        for (bind, w) in &bindings {
            if *w <= 0 {
                continue;
            }
            let mut env: Env = Env::new();
            for (i, &v) in var_order.iter().enumerate() {
                env.insert(v, bind[i]);
            }
            let mut es: Vec<Env> = vec![env];
            for op in &rule.body {
                if let BodyOp::Prim { .. } = op {
                    es = step_prim(eg, op, es)?;
                }
            }
            envs.extend(es);
        }
        out[caller_pos] = envs;
    }

    Ok(out)
}

/// Evaluate a primitive body op over each binding env, returning the new list of
/// envs. A value-computing prim binds (or checks) its return var; a guard prim
/// (`!=`) that fails prunes the env. Table atoms are NOT handled here — they run
/// on the DD dataflow; this is only the host-side primitive phase.
pub(crate) fn step_prim(eg: &mut EGraph, op: &BodyOp, envs: Vec<Env>) -> Result<Vec<Env>> {
    let BodyOp::Prim { id, args, ret } = op else {
        unreachable!("step_prim called on a non-primitive body op");
    };
    let mut out = Vec::new();
    for env in envs {
        let resolved: Option<Vec<Value>> = args
            .iter()
            .map(|s| slot_lookup(s, &|v| env.get(&v).copied()).map(Value::new))
            .collect();
        let Some(argv) = resolved else { continue };
        let result = eg.eval_prim_internal(*id, &argv);
        let Some(result) = result else {
            // Primitive failed (e.g. `!=` of equal args) — prune.
            continue;
        };
        match ret {
            Slot::Var(v) => {
                let mut next = env.clone();
                match next.get(v) {
                    Some(&existing) if existing != result.rep() => continue,
                    _ => {
                        next.insert(*v, result.rep());
                    }
                }
                out.push(next);
            }
            Slot::Const(c) => {
                if *c == result.rep() {
                    out.push(env);
                }
            }
        }
    }
    Ok(out)
}

/// Execute the head ops for one binding, accumulating writes.
fn apply_head(
    eg: &mut EGraph,
    head: &[HeadOp],
    env: &mut Env,
    writes: &mut Vec<Write>,
    lookup_index: &mut HashMap<FunctionId, HashMap<Box<[u32]>, u32>>,
) -> Result<()> {
    for op in head {
        match op {
            HeadOp::Set { func, slots } => {
                let row = build_row(slots, env)?;
                writes.push(Write::Set(*func, row));
            }
            HeadOp::Remove { func, slots } => {
                let key: Vec<u32> = slots
                    .iter()
                    .map(|s| resolve(s, env))
                    .collect::<Result<_>>()?;
                writes.push(Write::Remove(*func, key));
            }
            HeadOp::Subsume { func, slots } => {
                // The subsume action addresses a view row by its children+output
                // columns (a prefix; the trailing epoch is not given). Defer the
                // move to the pending-write phase so it lands after this
                // iteration's sets.
                let prefix: Vec<u32> = slots
                    .iter()
                    .map(|s| resolve(s, env))
                    .collect::<Result<_>>()?;
                writes.push(Write::Subsume(*func, prefix));
            }
            HeadOp::Lookup { func, args, ret } => {
                let key: Vec<Value> = args
                    .iter()
                    .map(|s| resolve(s, env).map(Value::new))
                    .collect::<Result<_>>()?;
                let val = if eg.info(*func).lookup_mints {
                    lookup_or_create(eg, *func, &key, lookup_index)
                } else {
                    lookup_existing(eg, *func, &key, lookup_index).ok_or_else(|| {
                        anyhow!(
                            "lookup on `{}` failed in rule action",
                            eg.relation_name(*func)
                        )
                    })?
                };
                env.insert(*ret, val.rep());
            }
            HeadOp::Call { id, args, ret } => {
                let argv: Vec<Value> = args
                    .iter()
                    .map(|s| resolve(s, env).map(Value::new))
                    .collect::<Result<_>>()?;
                let result = eg.eval_prim_internal(*id, &argv);
                if let Some(v) = result {
                    env.insert(*ret, v.rep());
                }
                // A `None` result (primitive failure) in an action is a no-op;
                // real failures surface as panics through `PanicFunc`.
            }
            HeadOp::Union { .. } => {
                // Term encoding lowers unions to `(set (@uf ...))` writes. Do not
                // silently discard a native union if this backend is driven
                // outside that required frontend mode.
                return Err(anyhow!(
                    "DD backend received a native union; term encoding must lower unions to @uf writes"
                ));
            }
            HeadOp::Panic(msg) => {
                return Err(anyhow!("{msg}"));
            }
        }
    }
    Ok(())
}

/// Build a full row from head-action slots under `env`.
fn build_row(slots: &[Slot], env: &Env) -> Result<Row> {
    let vals: Vec<u32> = slots
        .iter()
        .map(|s| resolve(s, env))
        .collect::<Result<_>>()?;
    Ok(vals.into_boxed_slice())
}

/// Resolve a slot to a concrete value, erroring if it is an unbound variable.
fn resolve(s: &Slot, env: &Env) -> Result<u32> {
    slot_lookup(s, &|v| env.get(&v).copied())
        .ok_or_else(|| anyhow!("unbound variable {s:?} in rule head"))
}

/// Look up the output of `func` for input `key`. If absent, create the row with
/// a fresh id (eq-sort constructor semantics — mirrors `add_term`). The created
/// row is written directly into the mirror so subsequent lookups in the same
/// iteration see it (hash-cons).
pub(crate) fn lookup_or_create(
    eg: &mut EGraph,
    func: FunctionId,
    key: &[Value],
    index: &mut HashMap<FunctionId, HashMap<Box<[u32]>, u32>>,
) -> Value {
    if let Some(value) = lookup_existing(eg, func, key, index) {
        return value;
    }
    let k: Box<[u32]> = key.iter().map(|v| v.rep()).collect();
    let id = eg.fresh_id_internal();
    index.entry(func).or_default().insert(k, id);
    let mut full: Vec<u32> = key.iter().map(|v| v.rep()).collect();
    full.push(id);
    let row: Row = full.into_boxed_slice();
    eg.insert_live_row(func, row);
    Value::new(id)
}

/// Look up the current output of `func` for input `key` without creating a row.
pub(crate) fn lookup_existing(
    eg: &EGraph,
    func: FunctionId,
    key: &[Value],
    index: &mut HashMap<FunctionId, HashMap<Box<[u32]>, u32>>,
) -> Option<Value> {
    let info = eg.info(func);
    let inputs_len = info.arity.saturating_sub(1);
    // Lazily build the key->output index for this function from live ∪ subsumed
    // rows so repeated lookups within one iteration are O(1) instead of O(state)
    // scans. A subsumed constructor row is still the current table row in the
    // reference backend; looking it up must not mint a fresh visible row.
    let idx = index.entry(func).or_insert_with(|| {
        let live_len = eg.mirror.get(&func).map_or(0, |rows| rows.len());
        let subsumed_len = eg.subsumed.get(&func).map_or(0, |rows| rows.len());
        let mut m: HashMap<Box<[u32]>, u32> = HashMap::with_capacity(live_len + subsumed_len);
        if let Some(set) = eg.mirror.get(&func) {
            for row in set.iter() {
                let k: Box<[u32]> = (0..inputs_len).map(|i| row_col(row, i)).collect();
                m.insert(k, row_col(row, inputs_len));
            }
        }
        if let Some(set) = eg.subsumed.get(&func) {
            for row in set.iter() {
                let k: Box<[u32]> = (0..inputs_len).map(|i| row_col(row, i)).collect();
                m.entry(k).or_insert(row_col(row, inputs_len));
            }
        }
        m
    });
    let k: Box<[u32]> = key.iter().map(|v| v.rep()).collect();
    idx.get(&k).copied().map(Value::new)
}

#[cfg(test)]
mod tests {
    use super::fused_caller_positions;

    #[test]
    fn fused_rule_mapping_uses_rule_ids_instead_of_caller_order() {
        assert_eq!(
            fused_caller_positions(&[4, 9], &[10, 20], &[20, 10]).unwrap(),
            [9, 4]
        );
    }

    #[test]
    fn fused_rule_mapping_rejects_inconsistent_cache_entries() {
        let missing = fused_caller_positions(&[4, 9], &[10, 20], &[10, 30]).unwrap_err();
        assert!(missing.to_string().contains("absent from the caller"));

        let duplicate = fused_caller_positions(&[4, 9], &[10, 20], &[10, 10]).unwrap_err();
        assert!(duplicate.to_string().contains("duplicate cached rule"));
    }
}
