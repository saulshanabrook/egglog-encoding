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

/// Env-gated (`EGGLOG_DD_TIMING=1`) per-iteration phase timing, printed to
/// stderr as one line per `run_iteration`. Diagnostic-only.
pub(crate) mod phase_timing {
    use std::cell::RefCell;
    use std::time::{Duration, Instant};
    thread_local! {
        static PHASES: RefCell<Vec<(&'static str, Duration)>> = const { RefCell::new(Vec::new()) };
        static NOTES: RefCell<Vec<(&'static str, usize)>> = const { RefCell::new(Vec::new()) };
    }
    pub fn enabled() -> bool {
        static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
        *ON.get_or_init(|| std::env::var("EGGLOG_DD_TIMING").is_ok())
    }
    pub fn time<T>(name: &'static str, f: impl FnOnce() -> T) -> T {
        if !enabled() {
            return f();
        }
        let t = Instant::now();
        let r = f();
        let d = t.elapsed();
        PHASES.with(|p| p.borrow_mut().push((name, d)));
        r
    }
    pub fn note(name: &'static str, value: usize) {
        if enabled() {
            NOTES.with(|n| n.borrow_mut().push((name, value)));
        }
    }
    pub fn flush() {
        if !enabled() {
            return;
        }
        let mut parts: Vec<String> = Vec::new();
        PHASES.with(|p| {
            let mut merged: Vec<(&'static str, Duration)> = Vec::new();
            for (n, d) in p.borrow_mut().drain(..) {
                if let Some(e) = merged.iter_mut().find(|(m, _)| *m == n) {
                    e.1 += d;
                } else {
                    merged.push((n, d));
                }
            }
            for (n, d) in merged {
                parts.push(format!("{n}={:.1}ms", d.as_secs_f64() * 1e3));
            }
        });
        NOTES.with(|no| {
            let mut merged: Vec<(&'static str, usize)> = Vec::new();
            for (n, v) in no.borrow_mut().drain(..) {
                if let Some(e) = merged.iter_mut().find(|(m, _)| *m == n) {
                    e.1 += v;
                } else {
                    merged.push((n, v));
                }
            }
            for (n, v) in merged {
                parts.push(format!("{n}={v}"));
            }
        });
        eprintln!("[dd-timing] {}", parts.join(" "));
    }
}
use egglog_ast::generic_ast::Change;
use egglog_backend_trait::{
    FunctionId, ReadMode, RuleActionCall, RuleBodyCall, RuleSpec, RuleValue, RuleVar, Value,
};
use egglog_numeric_id::NumericId;
use hashbrown::{HashMap, HashSet};

use crate::compile::{ReadKey, Row};
use crate::{EGraph, TableDefault, ViewOp};

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
pub fn run_iteration(eg: &mut EGraph, rules: &[(usize, RuleSpec)]) -> Result<bool> {
    // Every rule — including the term encoder's canonicalization rules — lowers
    // as an ordinary rule and joins on the fused DD worker; there is no special
    // casing for any rule kind.

    // Snapshot the fresh-id counter: any hash-cons (`lookup_or_create`) this
    // call advances it, the O(1) signal that a new term row was created.
    let next_id_at_start = eg.db.read_counter(eg.id_counter);

    let mut writes: Vec<Write> = Vec::new();

    // Compute every rule's binding envs FIRST (so the whole atom-bearing ruleset
    // runs on one fused DD worker via `fused_bindings`), THEN
    // apply head actions in the original rule firing order. Atom-less rules
    // (`(rule () …)`) have no input relation to drive the DD dataflow, so they
    // stay host-side (fire once); they are computed inline below.
    let envs_by_rule = fused_bindings(eg, rules)?;

    phase_timing::time("apply_head", || -> Result<()> {
        for ((_, rule), envs) in rules.iter().zip(envs_by_rule.into_iter()) {
            for mut env in envs {
                apply_head(eg, &rule.core.head, &mut env, &mut writes)?;
            }
        }
        Ok(())
    })?;

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
    let mut changed = eg.db.read_counter(eg.id_counter) != next_id_at_start;
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
    phase_timing::note("n_sets", sets.len());
    phase_timing::time("apply_writes", || -> Result<()> {
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
        Ok(())
    })?;
    phase_timing::flush();

    Ok(changed)
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
        let fused = phase_timing::time("dd_build", || dd_native::FusedDdJoin::build(&plans))?;
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

    // Build the signed delta batches for this step. A brand-new worker (no
    // cursors yet — first use, or rebuilt after a clone/free_rule) subscribes to
    // each read view's event log and is seeded with the view's full current
    // contents. An existing worker folds only its unread event-log window per
    // view: a row whose events net to `-1` is retracted, `+1` inserted, and a
    // net-zero row whose LAST event is an insert was removed and reinserted —
    // feeding `-row` then `+row` as separate DD steps preserves the reference
    // backend's hidden-timestamp refire behavior. Net-zero rows ending absent
    // (transients) are never replayed. This is O(delta), not O(state).
    let mut delta_batches: Vec<DdDeltaRows> = Vec::new();
    phase_timing::time("diff", || {
        if !eg.dd_fused_cursors.contains_key(&key) {
            let mut cursors = HashMap::new();
            let mut seed: DdDeltaRows = HashMap::new();
            for &read in &all_reads {
                let log = eg.event_logs.entry(read).or_default();
                cursors.insert(read, log.end());
                let rows = view_rows(eg, read);
                if !rows.is_empty() {
                    seed.insert(read, rows);
                }
            }
            eg.dd_fused_cursors.insert(key.clone(), cursors);
            if !seed.is_empty() {
                delta_batches.push(seed);
            }
            return;
        }

        let mut removals_batch: DdDeltaRows = HashMap::new();
        let mut insertions_batch: DdDeltaRows = HashMap::new();
        let cursors = eg
            .dd_fused_cursors
            .get_mut(&key)
            .expect("DD cursor invariant: checked above");
        for &read in &all_reads {
            let log = eg
                .event_logs
                .get(&read)
                .expect("DD cursor invariant: a cached worker subscribes to every view it reads");
            let cursor = cursors
                .get_mut(&read)
                .expect("DD cursor invariant: a cached worker has a cursor per view");
            let start = cursor
                .checked_sub(log.base)
                .expect("DD cursor invariant: consumed events are never drained past a cursor");
            if start >= log.events.len() {
                continue;
            }
            phase_timing::note("diff_rows_scanned", log.events.len() - start);

            // Fold the window per row: net presence change plus last event
            // sign (events are real state transitions, so the last sign is
            // end-of-window presence).
            let mut folded: HashMap<&Row, (isize, i8)> = HashMap::new();
            for (row, sign) in &log.events[start..] {
                let entry = folded.entry(row).or_insert((0, 0));
                entry.0 += *sign as isize;
                entry.1 = *sign;
            }
            let mut removals = Vec::new();
            let mut insertions = Vec::new();
            for (row, (net, last)) in folded {
                match net.cmp(&0) {
                    std::cmp::Ordering::Less => removals.push((row.to_vec(), -1)),
                    std::cmp::Ordering::Greater => insertions.push((row.to_vec(), 1)),
                    std::cmp::Ordering::Equal if last > 0 => {
                        removals.push((row.to_vec(), -1));
                        insertions.push((row.to_vec(), 1));
                    }
                    std::cmp::Ordering::Equal => {}
                }
            }
            if !removals.is_empty() {
                removals_batch.insert(read, removals);
            }
            if !insertions.is_empty() {
                insertions_batch.insert(read, insertions);
            }
            *cursor = log.end();
        }
        phase_timing::note(
            "delta_removals",
            removals_batch.values().map(|r| r.len()).sum::<usize>(),
        );
        phase_timing::note(
            "delta_insertions",
            insertions_batch.values().map(|r| r.len()).sum::<usize>(),
        );
        if !removals_batch.is_empty() {
            delta_batches.push(removals_batch);
        }
        if !insertions_batch.is_empty() {
            delta_batches.push(insertions_batch);
        }
    });
    drain_consumed_events(eg, &all_reads);

    // Step the shared worker once per nonempty signed-delta phase. A version
    // change may require a removal phase followed by an insertion phase.
    let mut per_rule_bindings = vec![Vec::new(); fused_positions.len()];
    {
        let fused = eg
            .dd_fused
            .get_mut(&key)
            .expect("DD cache invariant: fused join was inserted for this ruleset key");
        for delta in &delta_batches {
            phase_timing::note("epochs", 1);
            phase_timing::note(
                "delta_rows_fed",
                delta.values().map(|rows| rows.len()).sum::<usize>(),
            );
            let stepped = phase_timing::time("dd_step", || fused.step(delta))?;
            for (acc, rows) in per_rule_bindings.iter_mut().zip(stepped) {
                acc.extend(rows);
            }
        }
    }

    // Turn each rule's positive binding deltas into envs; re-run its body prims
    // host-side. Negative weights are integral bookkeeping (a body row retracted)
    // — egglog heads are monotone-fire, so we do NOT re-fire on disappearance.
    phase_timing::note(
        "bindings_out",
        per_rule_bindings.iter().map(|b| b.len()).sum::<usize>(),
    );
    phase_timing::time("envs_prims", || -> Result<()> {
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
        Ok(())
    })?;

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
                        let values = lookup_or_create(eg, *id, &key)?;
                        Some(Value::new(values[0]))
                    }
                    RuleActionCall::Primitive { id, .. } => {
                        let arguments = arguments
                            .iter()
                            .copied()
                            .map(Value::new)
                            .collect::<Vec<_>>();
                        // The term encoder's `set-if-empty` / view-proof ops are
                        // serviced against the mirror here (the db external
                        // function for them only panics); every other primitive
                        // runs on the embedded db.
                        if let Some(op) = eg.set_if_empty_ops.get(id).cloned() {
                            Some(set_if_empty_apply(eg, &op, &arguments)?)
                        } else if let Some(op) = eg.view_proof_ops.get(id).cloned() {
                            Some(view_proof_apply(eg, &op, &arguments)?)
                        } else {
                            eg.eval_prim_internal(*id, &arguments)?
                        }
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

/// All rows currently visible in a relation read view, as `+1` seed deltas for
/// a freshly built fused worker.
fn view_rows(eg: &EGraph, read: ReadKey) -> Vec<(Vec<u32>, isize)> {
    let mut out = Vec::new();
    let mut push = |store: &HashMap<FunctionId, HashSet<Row>>| {
        if let Some(rows) = store.get(&read.func) {
            out.extend(rows.iter().map(|r| (r.to_vec(), 1isize)));
        }
    };
    match read.mode {
        ReadMode::Live => push(&eg.mirror),
        ReadMode::Subsumed => push(&eg.subsumed),
        ReadMode::All => {
            push(&eg.mirror);
            push(&eg.subsumed);
        }
    }
    out
}

/// Advance each view's event log past the prefix that every subscribed fused
/// worker has already consumed, so logs stay proportional to unconsumed work.
fn drain_consumed_events(eg: &mut EGraph, reads: &[ReadKey]) {
    for read in reads {
        let min = eg
            .dd_fused_cursors
            .values()
            .filter_map(|cursors| cursors.get(read))
            .min()
            .copied();
        let Some(min) = min else { continue };
        if let Some(log) = eg.event_logs.get_mut(read) {
            let consumed = min.saturating_sub(log.base);
            if consumed > 0 {
                log.events.drain(..consumed);
                log.base = min;
            }
        }
    }
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
/// row is written directly into the mirror (which maintains the persistent
/// key index) so subsequent lookups in the same iteration see it (hash-cons).
pub(crate) fn lookup_or_create(eg: &mut EGraph, func: FunctionId, key: &[Value]) -> Result<Row> {
    if let Some(values) = lookup_existing(eg, func, key) {
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
    let values: Row = vec![value].into_boxed_slice();
    let mut full: Vec<u32> = key.iter().map(|v| v.rep()).collect();
    full.push(value);
    let row = full.into_boxed_slice();
    eg.insert_live_row(func, row);
    Ok(values)
}

/// Look up the current outputs of `func` for input `key` without creating a
/// row, through the persistent key index. A subsumed constructor row is still
/// the current table row in the reference backend; looking it up must not mint
/// a fresh visible row.
pub(crate) fn lookup_existing(eg: &EGraph, func: FunctionId, key: &[Value]) -> Option<Row> {
    let key: Vec<u32> = key.iter().map(|value| value.rep()).collect();
    eg.index_lookup_live_first(func, &key)
}

/// Service the term encoder's `set-if-empty` op against the mirror: return the
/// e-class (output col 0) of the existing `(view keys)` row, or insert
/// `(keys, default_vals)` — the args after the keys — and return the default
/// e-class. Writes immediately (like `lookup_or_create`) so repeated term
/// construction in one iteration dedups to the same e-class.
fn set_if_empty_apply(eg: &mut EGraph, op: &ViewOp, args: &[Value]) -> Result<Value> {
    let view = *eg
        .table_ids
        .get(&op.view_name)
        .ok_or_else(|| anyhow!("set-if-empty view `{}` is not registered", op.view_name))?;
    let keys = &args[..op.n_keys];
    if let Some(values) = lookup_existing(eg, view, keys) {
        return Ok(Value::new(values[0]));
    }
    let end = op.n_keys + op.out_arity;
    let full: Row = args[..end].iter().map(|v| v.rep()).collect();
    eg.insert_live_row(view, full);
    Ok(args[op.n_keys])
}

/// Service the term encoder's view-proof read against the mirror: the proof
/// column (output col 1) of the existing `(view keys)` row, or the `fallback`
/// arg (the one after the keys) when the key is absent.
fn view_proof_apply(eg: &mut EGraph, op: &ViewOp, args: &[Value]) -> Result<Value> {
    let view = *eg
        .table_ids
        .get(&op.view_name)
        .ok_or_else(|| anyhow!("view-proof view `{}` is not registered", op.view_name))?;
    let keys = &args[..op.n_keys];
    let fallback = args[op.n_keys];
    Ok(match lookup_existing(eg, view, keys) {
        Some(values) => Value::new(values[1]),
        None => fallback,
    })
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
