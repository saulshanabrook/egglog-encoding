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
//! 4. apply all collected writes/removes to the mirror, evaluating full-row
//!    function merges and merge-generated writes to a fixed point.
//!
//! ## The engine split
//!
//! Relational table-atom joins are the only operations on the DD engine, and
//! there is no host nested-loop fallback. Any rule the DD plan cannot lower (a
//! binding row exceeding the fixed width cap [`crate::dd_native::W`], or any
//! shape `plan_join` rejects) is reported as an error. Body primitives and head
//! actions are applied host-side here.
//!
//! Primitives are invoked through `Database::with_execution_state`, so they see
//! the same interned base `Value`s the frontend created and preserve bit-for-bit
//! value parity with the reference backend.

use anyhow::{anyhow, Result};
use egglog_ast::core::{GenericAtom, GenericAtomTerm, GenericCoreAction, GenericCoreActions};
use egglog_ast::generic_ast::Change;
use egglog_backend_trait::{
    FunctionId, ReadMode, RuleActionCall, RuleBodyCall, RuleSpec, RuleValue, RuleVar, Value,
};
use egglog_numeric_id::NumericId;
use hashbrown::{HashMap, HashSet};
use web_time::{Duration, Instant};

use crate::compile::{ReadKey, Row};
use crate::{EGraph, TableDefault};

/// Binding environment: variable id → bound `u32` value.
pub(crate) type Env = HashMap<u32, u32>;

type DdDeltaRows = HashMap<ReadKey, Vec<(Vec<u32>, isize)>>;
type LookupIndex = HashMap<FunctionId, HashMap<Row, Row>>;

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

pub(crate) struct IterationResult {
    pub changed: bool,
    /// Compatibility total derived from split timing, or zero when disabled.
    pub search_and_apply_time: Duration,
    /// Body matching, fused join execution, and body primitive evaluation.
    pub search_time: Option<Duration>,
    /// Rule-head instruction execution and write staging.
    pub apply_time: Option<Duration>,
    /// Resolving and installing the staged writes.
    pub merge_time: Duration,
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
pub fn run_iteration(
    eg: &mut EGraph,
    rules: &[(usize, RuleSpec)],
    phase_timing_enabled: bool,
) -> Result<IterationResult> {
    // Every rule — including the term encoder's canonicalization rules — lowers
    // as an ordinary rule and joins on the fused DD worker; there is no special
    // casing for any rule kind.

    // Snapshot the fresh-id counter: any hash-cons (`lookup_or_create`) this
    // call advances it, the O(1) signal that a new term row was created.
    let next_id_at_start = eg.next_id;

    let mut writes: Vec<Write> = Vec::new();
    // Iteration-scoped `key -> outputs` index for `lookup_or_create` (eq-sort
    // constructor hash-cons). Built lazily per function so repeated lookups in
    // one iteration are O(1) instead of rescanning the growing mirror each time.
    let mut lookup_index = LookupIndex::new();

    // Compute every rule's binding envs FIRST (so the whole atom-bearing ruleset
    // runs on one fused DD worker via `fused_bindings`), THEN
    // apply head actions in the original rule firing order. Atom-less rules
    // (`(rule () …)`) have no input relation to drive the DD dataflow, so they
    // stay host-side (fire once); they are computed inline below.
    let (envs_by_rule, search_time) = if phase_timing_enabled {
        let search_timer = Instant::now();
        let envs_by_rule = fused_bindings(eg, rules)?;
        (envs_by_rule, Some(search_timer.elapsed()))
    } else {
        (fused_bindings(eg, rules)?, None)
    };

    let apply_timer = phase_timing_enabled.then(Instant::now);
    for ((_, rule), envs) in rules.iter().zip(envs_by_rule) {
        for mut env in envs {
            apply_head(
                eg,
                &rule.core.head,
                &mut env,
                &mut writes,
                &mut lookup_index,
            )?;
        }
    }
    let apply_time = apply_timer.map(|timer| timer.elapsed());
    let search_and_apply_time = match (search_time, apply_time) {
        (Some(search_time), Some(apply_time)) => search_time + apply_time,
        _ => Duration::ZERO,
    };

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
    let merge_timer = phase_timing_enabled.then(Instant::now);
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
    // The backend transaction retains head-emission order within a table,
    // orders tables by merge-read dependencies, and processes merge-generated
    // writes in subsequent waves until reaching a fixed point.
    changed |= eg.apply_sets(sets)?;
    // Subsumes last: a row `set` this iteration can then be subsumed, and the
    // move reads the just-updated live mirror.
    for (f, prefix) in subsumes {
        changed |= eg.subsume_rows(f, &prefix);
    }

    let merge_time = merge_timer
        .map(|timer| timer.elapsed())
        .unwrap_or(Duration::ZERO);
    Ok(IterationResult {
        changed,
        search_and_apply_time,
        search_time,
        apply_time,
        merge_time,
    })
}

/// Compute every rule's binding envs in ONE fused pass: the whole atom-bearing
/// ruleset's body joins run on a SINGLE shared timely worker
/// ([`dd_native::FusedDdJoin`]) clocked once this iteration, then each rule's
/// host-side body primitives are re-run over its own bindings. Atom-less rules
/// (`(rule () …)`) have no input relation to drive the DD dataflow, so they are
/// fired once host-side. Returns a `Vec<Vec<Env>>` parallel to `rules` (same
/// order), ready for `apply_head`.
fn fused_bindings(eg: &mut EGraph, rules: &[(usize, RuleSpec)]) -> Result<Vec<Vec<Env>>> {
    use crate::dd_native;

    let mut out: Vec<Vec<Env>> = vec![Vec::new(); rules.len()];

    // Partition: atom-bearing rules drive the fused DD worker; atom-less rules
    // fire once host-side. Record each atom-bearing rule's POSITION in `rules` so
    // we can scatter the fused output back into `out` in the caller's order.
    let mut atom_positions: Vec<usize> = Vec::new();
    let mut atom_rule_idxs: Vec<usize> = Vec::new();
    for (pos, (idx, rule)) in rules.iter().enumerate() {
        let has_atoms = rule
            .core
            .body
            .atoms
            .iter()
            .any(|atom| matches!(atom.head, RuleBodyCall::Table { .. }));
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
            for atom in &rule.core.body.atoms {
                if matches!(atom.head, RuleBodyCall::Primitive { .. }) {
                    envs = step_prim(eg, atom, envs)?;
                    if envs.is_empty() {
                        break;
                    }
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
    // each rule. Any shape `plan_join` rejects is returned as an error (there is
    // no host fallback; the DD dataflow is the only join path).
    let mut key: Vec<usize> = atom_rule_idxs.clone();
    key.sort_unstable();

    if !eg.dd_fused.contains_key(&key) {
        // Plan in the SAME order as `atom_positions` so the fused build order
        // matches our scatter order (the fused join preserves plan order).
        let mut plans: Vec<(usize, dd_native::JoinPlan)> = Vec::with_capacity(atom_positions.len());
        for (&pos, &idx) in atom_positions.iter().zip(atom_rule_idxs.iter()) {
            let rule = &rules[pos].1;
            let plan = dd_native::plan_join(rule).map_err(|reason| {
                anyhow!(
                    "Differential Dataflow join cannot lower rule {:?}: {reason} \
                     (no host fallback; the DD dataflow is the only join path)",
                    rule.name
                )
            })?;
            plans.push((idx, plan));
        }
        let fused = dd_native::FusedDdJoin::build(&plans)?;
        eg.dd_fused.insert(key.clone(), fused);
    }

    // Capture the fused worker's build order and map each output slot back to
    // the current caller by stable rule id. The sorted cache key only proves set
    // equality; it does not prove that this call uses the original order.
    let (fused_rule_idxs, var_orders, all_reads): (Vec<usize>, Vec<Vec<u32>>, Vec<ReadKey>) = {
        let fused = eg
            .dd_fused
            .get(&key)
            .expect("DD cache invariant: fused join was inserted for this ruleset key");
        let rule_idxs = fused.rule_indices();
        let var_orders = (0..rule_idxs.len())
            .map(|p| fused.rule_var_order(p).to_vec())
            .collect();
        (rule_idxs, var_orders, fused.read_keys().to_vec())
    };
    let fused_positions =
        fused_caller_positions(&atom_positions, &atom_rule_idxs, &fused_rule_idxs)?;

    // Distinct relation read views across the whole ruleset. We diff versioned
    // current snapshots rather than plain row sets: if another ruleset removes and
    // reinserts the same row between two invocations, the row is present in both
    // end states but has a fresh version. Feeding `-row` then `+row` as separate
    // DD steps preserves the reference backend's hidden-timestamp behavior
    // without replaying transient rows that are no longer visible.
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
        let fused = eg
            .dd_fused
            .get_mut(&key)
            .expect("DD cache invariant: fused join was inserted for this ruleset key");
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
            for atom in &rule.core.body.atoms {
                if matches!(atom.head, RuleBodyCall::Primitive { .. }) {
                    es = step_prim(eg, atom, es)?;
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
pub(crate) fn step_prim(
    eg: &mut EGraph,
    atom: &GenericAtom<RuleBodyCall, RuleVar, RuleValue>,
    envs: Vec<Env>,
) -> Result<Vec<Env>> {
    let RuleBodyCall::Primitive { id, .. } = atom.head else {
        unreachable!("step_prim called on a non-primitive body op");
    };
    let (ret, args) = atom
        .args
        .split_last()
        .ok_or_else(|| anyhow!("body primitive has no return term"))?;
    let mut out = Vec::new();
    for env in envs {
        let resolved: Option<Vec<Value>> = args
            .iter()
            .map(|term| term_value(term, &env).map(Value::new))
            .collect();
        let Some(argv) = resolved else { continue };
        let result = eg.eval_prim_internal(id, &argv)?;
        let Some(result) = result else {
            // Primitive failed (e.g. `!=` of equal args) — prune.
            continue;
        };
        match ret {
            GenericAtomTerm::Var(_, variable) => {
                let mut next = env.clone();
                match next.get(&variable.id) {
                    Some(&existing) if existing != result.rep() => continue,
                    _ => {
                        next.insert(variable.id, result.rep());
                    }
                }
                out.push(next);
            }
            GenericAtomTerm::Literal(_, constant) => {
                if constant.value.rep() == result.rep() {
                    out.push(env);
                }
            }
            GenericAtomTerm::Global(..) => {
                unreachable!("DD rule validation must reject global primitive return terms")
            }
        }
    }
    Ok(out)
}

/// Execute the head ops for one binding, accumulating writes.
fn apply_head(
    eg: &mut EGraph,
    head: &GenericCoreActions<RuleActionCall, RuleVar, RuleValue>,
    env: &mut Env,
    writes: &mut Vec<Write>,
    lookup_index: &mut LookupIndex,
) -> Result<()> {
    for action in &head.0 {
        match action {
            GenericCoreAction::Let(_, variable, call, arguments) => {
                let arguments = resolve_terms(arguments, env)?;
                let result = match call {
                    RuleActionCall::Table { id, .. } => {
                        let key = arguments
                            .iter()
                            .copied()
                            .map(Value::new)
                            .collect::<Vec<_>>();
                        let values = lookup_or_create(eg, *id, &key, lookup_index)?;
                        Some(Value::new(values[0]))
                    }
                    RuleActionCall::Primitive { id, .. } => {
                        let arguments = arguments
                            .iter()
                            .copied()
                            .map(Value::new)
                            .collect::<Vec<_>>();
                        eg.eval_prim_internal(*id, &arguments)?
                    }
                };
                if let Some(result) = result {
                    env.insert(variable.id, result.rep());
                }
            }
            GenericCoreAction::LetAtomTerm(_, variable, term) => {
                env.insert(variable.id, resolve_term(term, env)?);
            }
            GenericCoreAction::Set(_, call, arguments, values) => {
                let RuleActionCall::Table { id, .. } = call else {
                    return Err(anyhow!("DD backend cannot set a primitive"));
                };
                let mut row = resolve_terms(arguments, env)?;
                row.extend(resolve_terms(values, env)?);
                writes.push(Write::Set(*id, row.into_boxed_slice()));
            }
            GenericCoreAction::Change(_, change, call, arguments) => {
                let RuleActionCall::Table { id, .. } = call else {
                    return Err(anyhow!("DD backend cannot delete or subsume a primitive"));
                };
                let values = resolve_terms(arguments, env)?;
                match change {
                    Change::Delete => writes.push(Write::Remove(*id, values)),
                    Change::Subsume => writes.push(Write::Subsume(*id, values)),
                }
            }
            GenericCoreAction::Union(..) => {
                // Term encoding lowers unions to `(set (@uf ...))` writes. Do not
                // silently discard a native union if this backend is driven
                // outside that required frontend mode.
                return Err(anyhow!(
                    "DD backend received a native union; term encoding must lower unions to @uf writes"
                ));
            }
            GenericCoreAction::Panic(_, msg) => {
                return Err(anyhow!("{msg}"));
            }
        }
    }
    Ok(())
}

fn term_value(term: &GenericAtomTerm<RuleVar, RuleValue>, env: &Env) -> Option<u32> {
    match term {
        GenericAtomTerm::Var(_, variable) => env.get(&variable.id).copied(),
        GenericAtomTerm::Literal(_, value) => Some(value.value.rep()),
        GenericAtomTerm::Global(..) => {
            unreachable!("DD rule validation must reject residual global terms")
        }
    }
}

fn resolve_term(term: &GenericAtomTerm<RuleVar, RuleValue>, env: &Env) -> Result<u32> {
    term_value(term, env).ok_or_else(|| anyhow!("unbound term {term:?} in rule head"))
}

fn resolve_terms(terms: &[GenericAtomTerm<RuleVar, RuleValue>], env: &Env) -> Result<Vec<u32>> {
    terms.iter().map(|term| resolve_term(term, env)).collect()
}

/// Look up the output of `func` for input `key`. If absent, create the row with
/// a fresh id (eq-sort constructor semantics — mirrors `add_term`). The created
/// row is written directly into the mirror so subsequent lookups in the same
/// iteration see it (hash-cons).
pub(crate) fn lookup_or_create(
    eg: &mut EGraph,
    func: FunctionId,
    key: &[Value],
    index: &mut LookupIndex,
) -> Result<Row> {
    if let Some(values) = lookup_existing(eg, func, key, index) {
        return Ok(values);
    }
    let (n_keys, _, default, _) = eg.function_spec(func);
    if key.len() != n_keys {
        return Err(anyhow!(
            "lookup on `{}` has {} keys, expected {n_keys}",
            eg.relation_name(func),
            key.len()
        ));
    }
    if eg.n_vals(func) != 1 {
        return Err(anyhow!(
            "lookup on tuple-output function `{}` cannot bind one value",
            eg.relation_name(func)
        ));
    }
    let value = match default {
        TableDefault::FreshId => eg.fresh_id_internal(),
        TableDefault::Const(value) => value,
        TableDefault::Fail => {
            return Err(anyhow!(
                "lookup on `{}` failed in rule action",
                eg.relation_name(func)
            ));
        }
    };
    let k: Row = key.iter().map(|value| value.rep()).collect();
    let values: Row = vec![value].into_boxed_slice();
    index.entry(func).or_default().insert(k, values.clone());
    let mut full: Vec<u32> = key.iter().map(|v| v.rep()).collect();
    full.push(value);
    let row = full.into_boxed_slice();
    eg.insert_live_row(func, row);
    Ok(values)
}

/// Look up all current outputs of `func` for input `key` without creating a row.
pub(crate) fn lookup_existing(
    eg: &EGraph,
    func: FunctionId,
    key: &[Value],
    index: &mut LookupIndex,
) -> Option<Row> {
    let n_keys = eg.n_keys(func);
    // Lazily build the key->outputs index for this function from live ∪ subsumed
    // rows so repeated lookups within one iteration are O(1) instead of O(state)
    // scans. A subsumed constructor row is still the current table row in the
    // reference backend; looking it up must not mint a fresh visible row.
    let idx = index.entry(func).or_insert_with(|| {
        let live_len = eg.mirror.get(&func).map_or(0, |rows| rows.len());
        let subsumed_len = eg.subsumed.get(&func).map_or(0, |rows| rows.len());
        let mut values_by_key = HashMap::with_capacity(live_len + subsumed_len);
        if let Some(set) = eg.mirror.get(&func) {
            for row in set.iter() {
                let key: Row = row[..n_keys].into();
                let values: Row = row[n_keys..].into();
                values_by_key.insert(key, values);
            }
        }
        if let Some(set) = eg.subsumed.get(&func) {
            for row in set.iter() {
                let key: Row = row[..n_keys].into();
                let values: Row = row[n_keys..].into();
                values_by_key.entry(key).or_insert(values);
            }
        }
        values_by_key
    });
    let key: Row = key.iter().map(|value| value.rep()).collect();
    idx.get(&key).cloned()
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
