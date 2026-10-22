//! Maintenance-rule generation for the term/proof encoding: the rebuild rules
//! that keep each function's view and subsumed tables canonical, plus the rule
//! that executes a requested subsumption. Scalar columns use the native bulk pass below.

use super::proof_encoding::ProofInstrumentor;
use super::proof_encoding_helpers::Skeleton;
use crate::*;
use egglog_bridge::{RebuildProof, TableAction};
use egglog_concurrency::ReadOptimizedLock;
use egglog_core_relations::{ColumnId, CounterId, ExecutionState};
use egglog_numeric_id::NumericId;
use smallvec::SmallVec;

/// One packed witness per changed row, using the existing proof algebra.
/// The fixed layout has a slot for every scalar equality column, but its
/// composition names only changed columns. Unused slots carry the old witness.
pub(crate) struct NativeRowProof {
    packed: TableAction,
    ids: CounterId,
    unit: Value,
    columns: Vec<ColumnId>,
    proof_column: ColumnId,
    eclass_column: Option<ColumnId>,
    spellings: ReadOptimizedLock<util::HashMap<SmallVec<[usize; 4]>, Value>>,
}

impl NativeRowProof {
    pub(crate) fn new(
        backend: &mut egglog_bridge::EGraph,
        packed: egglog_bridge::FunctionId,
        columns: Vec<ColumnId>,
        proof_column: ColumnId,
        eclass_column: Option<ColumnId>,
    ) -> Self {
        Self {
            packed: TableAction::new(backend, packed),
            ids: backend.id_counter(),
            unit: backend.base_values().get::<()>(()),
            columns,
            proof_column,
            eclass_column,
            spellings: ReadOptimizedLock::new(Default::default()),
        }
    }
}

impl RebuildProof for NativeRowProof {
    fn compose(
        &self,
        row: &[Value],
        steps: &[(ColumnId, Value)],
        state: &mut ExecutionState,
    ) -> Value {
        let old_proof = row[self.proof_column.index()];
        let mut args = Vec::with_capacity(self.columns.len() + 4);
        // Filled after constructing the composition below.
        args.extend([old_proof, old_proof]);
        let mut pattern = SmallVec::<[usize; 4]>::new();
        for (slot, column) in self.columns.iter().enumerate() {
            if let Some((_, proof)) = steps.iter().find(|(changed, _)| changed == column) {
                args.push(*proof);
                pattern.push(slot);
            } else {
                args.push(old_proof);
            }
        }
        let cached = self.spellings.read().get(&pattern).copied();
        args[0] = cached.unwrap_or_else(|| {
            let mut skeleton = Skeleton::Leaf(0);
            for &slot in &pattern {
                let column = self.columns[slot];
                let step = Skeleton::Leaf(slot + 1);
                skeleton = if Some(column) == self.eclass_column {
                    step.sym().trans(skeleton)
                } else {
                    skeleton.congr(column.index(), step)
                };
            }
            let spelling = state
                .base_values()
                .get::<crate::sort::S>(skeleton.spelling().into());
            // String interning otherwise takes a mutex for every rebuilt row.
            // Cache only observed column patterns, never all 2^arity patterns.
            // Base-value intern storage is shared across database clones, so
            // these immutable string IDs remain valid after push/pop and clone.
            self.spellings.lock().insert(pattern, spelling);
            spelling
        });
        let id = Value::from_usize(state.inc_counter(self.ids));
        args.extend([id, self.unit]);
        self.packed.insert(state, args.into_iter());
        id
    }
}

/// A full rebuild composition for the packed proof algebra tests: the row proof in column
/// 0, then one step proof per canonicalized child in `children`, in the order
/// the composition applies them, then the e-class's own step when `eclass`.
///
/// The native adapter constructs only the non-reflexive subset of these steps.
#[cfg(test)]
pub(super) fn rebuild_skeleton(children: &[usize], eclass: bool) -> Skeleton {
    let mut skeleton = Skeleton::Leaf(0);
    for (step, &child) in children.iter().enumerate() {
        skeleton = skeleton.congr(child, Skeleton::Leaf(1 + step));
    }
    if eclass {
        skeleton = Skeleton::Leaf(1 + children.len()).sym().trans(skeleton);
    }
    skeleton
}

impl ProofInstrumentor<'_> {
    /// The declarations `name`'s subsumption marker needs: the marker relation,
    /// the maintenance rule that applies it to the view, and native scalar
    /// rebuilding keeping the marker keyed on canonical children.
    ///
    /// The marker is what makes subsumption survive rebuilding: re-keying a view
    /// row inserts it afresh, and the new row carries no subsumed bit of its own.
    pub(super) fn subsume_scaffolding(&mut self, name: &str, input: &[ArcSort]) -> String {
        let child = |i: usize| format!("c{i}_");
        let children_vec: Vec<String> = (0..input.len()).map(child).collect();
        let children = children_vec.join(" ");
        let in_sorts = ListDisplay(input.iter().map(|s| s.name()).collect::<Vec<_>>(), " ");
        let subsumed_name = self.subsumed_name(name);
        let view_name = name.to_string();
        let subsume_ruleset = self.proof_names().subsume_ruleset_name.clone();
        let fresh_name = self.egraph.parser.symbol_gen.fresh("subsume_rule");

        // The view is keyed by children only, so match its value tuple to subsume
        // by key (the bridge re-reads every value column when subsuming a
        // tuple-output view). A subsumed row is kept for size/proofs but excluded
        // from matching.
        let e = self.fresh_var();
        let pf = self.fresh_var();
        format!(
            "(function {subsumed_name} ({in_sorts}) Unit :no-merge :internal-hidden :internal-native-rebuild)
             (rule (({subsumed_name} {children})
                    (= (values {e} {pf}) ({view_name} {children})))
                   ((subsume ({view_name} {children})))
                    :ruleset {subsume_ruleset}
                    :name \"{fresh_name}\")\n"
        )
    }

    /// Wrap one maintenance-rebuild rule (`facts` -> `actions`) with the rebuilding
    /// ruleset, a fresh name, and `:internal-include-subsumed` (so stale rows are
    /// rebuilt too). `naive` marks rules whose primitives read `@UF` tables the rule
    /// body doesn't join on.
    fn rebuild_rule(&mut self, facts: &str, actions: &str, naive: bool) -> String {
        let ruleset = self.proof_names().rebuilding_ruleset_name.clone();
        let fresh_name = self.egraph.parser.symbol_gen.fresh("rebuild_rule");
        let naive = if naive { ":naive " } else { "" };
        format!(
            "(rule ({facts})\n     ({actions})\n     :ruleset {ruleset} {naive}:name \"{fresh_name}\" :internal-include-subsumed)\n"
        )
    }

    /// Structural maintenance for container columns. Scalar equality columns
    /// are maintained by the native bulk pass in the same fixed point.
    ///
    /// A child update re-keys the row (`set` at the canonicalized children, then
    /// `delete`); a collision on the new key runs the view's `:merge`. The value
    /// column follows the same structural path. In proof mode each rule composes
    /// the updated view proof.
    pub(super) fn rebuilding_rules(&mut self, fdecl: &ResolvedFunctionDecl) -> Vec<Command> {
        let proofs = self.proofs_enabled();
        // A global's output *is* its e-class (like a constructor's), so it takes the
        // e-class rebuild below (union-tracking) — not the custom-output rebuild
        // (congruence), which would emit a nonsensical `Congr` on its nullary term.
        let output_is_eclass = self.output_is_eclass(fdecl);
        let types = self.column_sorts(fdecl);
        let n = types.len();
        let child = |i: usize| format!("c{i}_");
        // Key columns of the view row: the children (the value tuple is unkeyed).
        let n_keys = n - 1;
        let key_vars: Vec<String> = (0..n_keys).map(child).collect();
        let view_name = fdecl.name.to_string();
        let keys_str = format!("{}", ListDisplay(&key_vars, " "));

        let mut rules = String::new();
        // One rule per rebuildable key column (re-keys the row via set + delete).
        for (i, ty) in types[..n_keys].iter().enumerate() {
            // Scalar children are owned by the native bulk pass.
            if !ty.is_eq_container_sort() {
                continue;
            }
            let ci = child(i);
            let canon = format!("c{i}_canon_");
            let (query_view, value_var, view_prf) = self.query_fd_view(&fdecl.name, &key_vars);
            // The container primitive reads UF tables absent from the query,
            // so these structural maintenance rules remain naive.
            let value_prim = self.container_rebuild_prim(ty);
            let canon_fact = format!("(= {canon} ({value_prim} {ci}))");
            let (proof_lets, pf_arg) = if proofs {
                let (lets, new_pf) = self.container_rebuild_proof(&view_prf, i, ty, &ci);
                (lets.join("\n                             "), new_pf)
            } else {
                (String::new(), "()".to_string())
            };
            let mut updated = key_vars.clone();
            updated[i] = canon.clone();
            let updated_view = self.update_fd_view(&fdecl.name, &updated, &value_var, &pf_arg);
            let facts = format!("{query_view}\n{canon_fact}\n(!= {ci} {canon})");
            let actions =
                format!("{proof_lets}\n{updated_view}\n(delete ({view_name} {keys_str}))");
            rules.push_str(&self.rebuild_rule(&facts, &actions, true));
        }
        // Containers retain structural rebuilding; scalar columns are owned by
        // the native bulk pass, including a custom function's output.
        if !output_is_eclass && types[n - 1].is_eq_container_sort() {
            rules.push_str(&self.fd_container_value_rebuild_rule(fdecl, &key_vars, n - 1));
        }
        self.parse_program(&rules)
    }

    /// The proof that a view row's container column `index` was rebuilt, as the
    /// statements writing it and the variable naming it. The row proof's term has
    /// the container at `index`, so projecting it out is the anchor the rebuild
    /// composes from, and `Congr` at the same position carries the row proof over
    /// the rebuild's step.
    fn container_rebuild_proof(
        &mut self,
        view_prf: &str,
        index: usize,
        container_sort: &ArcSort,
        container_var: &str,
    ) -> (Vec<String>, String) {
        let congr = self.proof_names().congr_constructor.clone();
        let proj = self.proof_names().proj_constructor.clone();
        let proof_prim = self.container_rebuild_proof_prim(container_sort);
        let rebuild_pf = self.fresh_var();
        let mut lets = vec![];
        let anchor = self.mint(&mut lets, &proj, &format!("{view_prf} {index}"));
        lets.push(format!(
            "(let {rebuild_pf} ({proof_prim} {container_var} {anchor}))"
        ));
        let new_pf = self.mint(
            &mut lets,
            &congr,
            &format!("{view_prf} {index} {rebuild_pf}"),
        );
        (lets, new_pf)
    }

    /// A rule for an eq-container output:
    /// containers have no `@UF` to chase, so the value canonicalizes via the
    /// container rebuild primitive (`:naive` — it reads `@UF` tables the rule
    /// doesn't join on).
    fn fd_container_value_rebuild_rule(
        &mut self,
        fdecl: &ResolvedFunctionDecl,
        key_vars: &[String],
        out_idx: usize,
    ) -> String {
        let out_ty = self.sort_by_name(fdecl.schema.output());
        let value_prim = self.container_rebuild_prim(&out_ty);
        let (query_view, value_var, view_prf) = self.query_fd_view(&fdecl.name, key_vars);
        let canon = self.fresh_var();
        let canon_fact = format!("(= {canon} ({value_prim} {value_var}))");
        let (proof_lets, pf_arg) = if self.proofs_enabled() {
            let (lets, new_pf) =
                self.container_rebuild_proof(&view_prf, out_idx, &out_ty, &value_var);
            (lets.join("\n                      "), new_pf)
        } else {
            (String::new(), "()".to_string())
        };
        let set_canon = self.update_fd_view(&fdecl.name, key_vars, &canon, &pf_arg);
        let view_name = fdecl.name.to_string();
        let keys_str = ListDisplay(key_vars, " ").to_string();
        let facts = format!("{query_view}\n{canon_fact}\n(!= {value_var} {canon})");
        let actions = format!("{proof_lets}\n(delete ({view_name} {keys_str}))\n{set_canon}");
        self.rebuild_rule(&facts, &actions, true)
    }
}
