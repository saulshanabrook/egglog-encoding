use std::sync::OnceLock;

use super::*;

fn serial_trace_pool() -> &'static rayon::ThreadPool {
    static SERIAL_POOL: OnceLock<rayon::ThreadPool> = OnceLock::new();
    SERIAL_POOL.get_or_init(|| {
        rayon::ThreadPoolBuilder::new()
            .num_threads(1)
            .build()
            .unwrap()
    })
}

fn replay_slice(egraph: EGraph, slice: &Slice) -> EGraph {
    let replay = crate::slicing::replay::build_replay_program(&egraph, slice).unwrap();
    let commands = replay.to_commands().unwrap();
    drop(egraph);
    let mut proof = EGraph::default().with_proofs_enabled().with_proof_testing();
    serial_trace_pool()
        .install(|| proof.run_program(commands))
        .unwrap();
    proof
}

#[test]
fn repeated_variable_slice_keeps_exact_equality_support() {
    let mut egraph = EGraph::default();
    serial_trace_pool()
        .install(|| egraph.enable_trace())
        .unwrap();
    egraph
        .parse_and_run_program(
            None,
            "(datatype E (A i64) (B i64) (D i64))
                 (relation R (E))
                 (relation S (E))
                 (relation Out (Unit))
                 (relation Noise (E))
                 (relation Dead (Unit))
                 (rule () ((union (A 1) (B 2))) :name \"eq-ab\")
                 (rule ((R x) (S x)) ((Out ())) :name \"join\")
                 (rule ((Noise x)) ((Dead ())) :name \"dead\")
                 (R (A 1))
                 (S (B 2))
                 (Noise (D 3))
                 (run 2)
                 (check (Out ()))",
        )
        .unwrap();

    let slice = slice_all_checks(&egraph).unwrap();
    assert_eq!(slice.firing_bindings.len(), 2);
    assert_eq!(slice.sources.len(), 2);
    assert!(
        slice
            .firing_bindings
            .values()
            .all(|bindings| bindings.len() <= 1)
    );
    replay_slice(egraph, &slice);
}

#[test]
fn interfering_same_wave_delete_retains_its_independent_firing() {
    let mut egraph = EGraph::default();
    serial_trace_pool()
        .install(|| egraph.enable_trace())
        .unwrap();
    egraph
        .parse_and_run_program(
            None,
            "(function f (i64) i64 :merge (max old new))
                 (relation Trigger (Unit))
                 (relation Write (Unit))
                 (relation Done (Unit))
                 (relation Before (i64))
                 (relation After (i64))
                 (set (f 1) 5)
                 (Trigger ())
                 (Write ())
                 (rule ((= value (f 1))) ((Before value)) :name \"observe-before\")
                 (rule ((Trigger u)) ((delete (f 1))) :name \"delete-f\")
                 (rule ((Write u)) ((set (f 1) 2) (Done ())) :name \"rewrite-f\")
                 (rule ((Done u) (= value (f 1))) ((After value)) :name \"observe-after\")
                 (run 2)
                 (check (Before 5) (After 2))",
        )
        .unwrap();

    let bridge = egraph
        .backend
        .as_any()
        .downcast_ref::<egglog_bridge::EGraph>()
        .unwrap();
    bridge
        .with_trace_view(|view| {
            assert_eq!(view.totals().removals, 1);
            Ok(())
        })
        .unwrap();
    let slice = slice_all_checks(&egraph).unwrap();
    assert_eq!(
        slice.firing_bindings.len(),
        4,
        "the independent delete must be rooted"
    );
    assert_eq!(slice.checks.len(), 1);
    assert_eq!(slice.replay_removals.len(), 1);
}

#[test]
fn all_checks_union_disjoint_cones() {
    let mut egraph = EGraph::default();
    serial_trace_pool()
        .install(|| egraph.enable_trace())
        .unwrap();
    egraph
        .parse_and_run_program(
            None,
            "(relation A (Unit))
                 (relation B (Unit))
                 (relation OutA (Unit))
                 (relation OutB (Unit))
                 (A ())
                 (B ())
                 (rule ((A u)) ((OutA ())) :name \"make-a\")
                 (rule ((B u)) ((OutB ())) :name \"make-b\")
                 (run 1)
                 (check (OutA ()))
                 (check (OutB ()))",
        )
        .unwrap();

    let slice = slice_all_checks(&egraph).unwrap();
    assert_eq!(slice.checks, HashSet::from_iter([0, 1]));
    assert_eq!(slice.firing_bindings.len(), 2);
}

#[test]
fn future_selected_child_union_requires_maintenance_congruence_for_interference() {
    let mut egraph = EGraph::default();
    serial_trace_pool()
        .install(|| egraph.enable_trace())
        .unwrap();
    egraph
        .parse_and_run_program(
            None,
            "(datatype E (X) (Y) (F E) (Parent E))
                 (function tag (E) i64 :no-merge)
                 (relation Delete (Unit))
                 (relation Recreate (Unit))
                 (relation Created (E))
                 (relation Before (i64))
                 (relation Out (Unit))
                 (set (tag (Parent (F (X)))) 1)
                 (Delete ())
                 (rule ((= value (tag (Parent (F (X))))))
                       ((Before value))
                       :name \"observe-before\")
                 (rule ((Delete u))
                       ((delete (Parent (F (X)))))
                       :name \"delete-parent\")
                 (run 1)
                 (Recreate ())
                 (rule ((Recreate u))
                       ((set (tag (Parent (F (Y)))) 2)
                        (Created (Parent (F (Y)))))
                       :name \"recreate-parent\")
                 (run 1)
                 (rule ((Created p))
                       ((union (X) (Y)) (Out ()))
                       :name \"merge-children\")
                 (run 1)
                 (check (Before 1) (Out ()))",
        )
        .unwrap();

    let slice = slice_all_checks(&egraph).unwrap();
    assert_eq!(
        slice.replay_removals.len(),
        1,
        "the selected X=Y event automatically makes F(X)=F(Y), so omitting the Parent delete makes replay congruence-collide the stale and recreated rows"
    );

    let mut omitted_creator = EGraph::default();
    serial_trace_pool()
        .install(|| omitted_creator.enable_trace())
        .unwrap();
    omitted_creator
        .parse_and_run_program(
            None,
            "(datatype E (X) (Y) (F E) (Parent E))
                 (function tag (E) i64 :no-merge)
                 (relation Delete (Unit))
                 (relation Recreate (Unit))
                 (relation Created (E))
                 (relation Out (Unit))
                 (set (tag (Parent (F (X)))) 1)
                 (Delete ())
                 (rule ((Delete u))
                       ((delete (Parent (F (X)))))
                       :name \"delete-parent\")
                 (run 1)
                 (Recreate ())
                 (rule ((Recreate u))
                       ((set (tag (Parent (F (Y)))) 2)
                        (Created (Parent (F (Y)))))
                       :name \"recreate-parent\")
                 (run 1)
                 (rule ((Created p))
                       ((union (X) (Y)) (Out ()))
                       :name \"merge-children\")
                 (run 1)
                 (check (Out ()))",
        )
        .unwrap();
    let omitted_slice = slice_all_checks(&omitted_creator).unwrap();
    assert!(
        omitted_slice.replay_removals.is_empty(),
        "when the stale constructor source is absent from replay, its delete is correctly unnecessary"
    );
}

#[test]
fn selected_child_delete_prevents_spurious_parent_delete_interference() {
    let mut egraph = EGraph::default();
    serial_trace_pool()
        .install(|| egraph.enable_trace())
        .unwrap();
    egraph
        .parse_and_run_program(
            None,
            "(datatype E (Leaf i64) (Parent E))
                 (relation DeleteLeaf (Unit))
                 (relation DeleteParent (Unit))
                 (relation Recreate (Unit))
                 (relation Before (E))
                 (relation After (E))
                 (Before (Parent (Leaf 1)))
                 (DeleteLeaf ())
                 (DeleteParent ())
                 (rule ((DeleteLeaf u))
                       ((delete (Leaf 1)))
                       :name \"delete-leaf\")
                 (rule ((DeleteParent u))
                       ((delete (Parent (Leaf 1))))
                       :name \"delete-parent\")
                 (run 1)
                 (Recreate ())
                 (rule ((Recreate u))
                       ((After (Parent (Leaf 1))))
                       :name \"recreate\")
                 (run 1)
                 (check (Before old) (After new))",
        )
        .unwrap();

    let slice = slice_all_checks(&egraph).unwrap();
    assert_eq!(
        slice.replay_removals.len(),
        1,
        "the required Leaf delete prevents old/new Leaf outputs from congruence-colliding, so Parent deletion is noninterfering"
    );
    assert_eq!(
        slice.firing_bindings.len(),
        2,
        "only recreate and the required Leaf delete should replay"
    );
}

#[test]
fn same_syntax_constructor_recreation_retains_raw_reconciliation() {
    let mut egraph = EGraph::default();
    serial_trace_pool()
        .install(|| egraph.enable_trace())
        .unwrap();
    egraph
        .parse_and_run_program(
            None,
            "(datatype E (Leaf i64))
                 (relation Delete (i64))
                 (relation Recreate (i64))
                 (relation Before (E))
                 (relation After (E))
                 (ruleset cleanup)
                 (ruleset recreate)
                 (ruleset reconcile)
                 (rule ((Delete key)) ((delete (Leaf key)))
                       :ruleset cleanup :name \"delete-leaf\")
                 (rule ((Recreate key)) ((After (Leaf key)))
                       :ruleset recreate :name \"recreate-leaf\")
                 (rule ((Before old) (After new)) ((union old new))
                       :ruleset reconcile :name \"reconcile\")
                 (Before (Leaf 1))
                 (Delete 1)
                 (Recreate 1)
                 (run cleanup 1)
                 (run recreate 1)
                 (run reconcile 1)
                 (check (Before x) (After x))",
        )
        .unwrap();

    let slice = slice_all_checks(&egraph).unwrap();
    assert_eq!(slice.replay_removals.len(), 1);
    assert_eq!(
        slice.firing_bindings.len(),
        3,
        "recreate, reconcile, and delete"
    );
    let replay = crate::slicing::replay::build_replay_program(&egraph, &slice).unwrap();
    let commands = replay.to_commands().unwrap();
    drop(egraph);

    let mut proof = EGraph::default().with_proofs_enabled();
    serial_trace_pool()
        .install(|| proof.run_program(commands))
        .unwrap();
}

#[test]
fn parent_alias_waits_for_child_key_bridge_without_borrowing_parent_anchor() {
    let mut egraph = EGraph::default();
    serial_trace_pool()
        .install(|| egraph.enable_trace())
        .unwrap();
    egraph
        .parse_and_run_program(
            None,
            "(datatype E (A i64) (H E))
                 (relation Seed (E))
                 (relation New (E))
                 (relation Trigger ())
                 (relation R (E))
                 (relation Out (E))
                 (ruleset bridge_rules)
                 (ruleset emit_rules)
                 (ruleset consume_rules)
                 (Seed (H (A 0)))
                 (New (A 1))
                 (Trigger)
                 (rule ((Trigger))
                       ((union (A 0) (A 1)))
                       :ruleset bridge_rules :name \"bridge\")
                 (rule ((New child))
                       ((R (H child)))
                       :ruleset emit_rules :name \"emit\")
                 (rule ((R value))
                       ((Out value))
                       :ruleset consume_rules :name \"consume\")
                 (run bridge_rules 1)
                 (run emit_rules 1)
                 (run consume_rules 1)
                 (check (Out value))",
        )
        .unwrap();

    let slice = slice_all_checks(&egraph).unwrap();
    let consume_bindings = slice
        .firing_bindings
        .values()
        .find(|bindings| bindings.len() == 1 && bindings[0].aliases.len() == 2)
        .expect("consume must retain the child and parent alias plans");
    let [child, parent] = consume_bindings[0].aliases.as_ref() else {
        unreachable!("alias plan count was checked above")
    };
    assert!(
        parent.ready_after > child.ready_after,
        "the parent must wait for the child denotation bridge, not merely child creation: {consume_bindings:?}"
    );

    let replay = crate::slicing::replay::build_replay_program(&egraph, &slice).unwrap();
    let commands = replay.to_commands().unwrap();
    let rendered = crate::slicing::replay::ReplayProgram::render_commands(&commands);
    let bridge = rendered
        .find("(run-schedule (run-rule (\"bridge\"")
        .unwrap();
    let parent_alias = rendered[bridge..]
        .find("(H $__slice_replay_")
        .map(|offset| bridge + offset)
        .expect("the H alias must be captured after its child bridge");
    let consume = rendered
        .find("(run-schedule (run-rule (\"consume\"")
        .unwrap();
    assert!(
        bridge < parent_alias && parent_alias < consume,
        "{rendered}"
    );

    drop(egraph);
    let mut proof = EGraph::default().with_proofs_enabled().with_proof_testing();
    serial_trace_pool()
        .install(|| proof.run_program(commands))
        .unwrap();
}

#[test]
fn post_deletion_equality_cannot_select_stale_child_producer() {
    let mut egraph = EGraph::default();
    serial_trace_pool()
        .install(|| egraph.enable_trace())
        .unwrap();
    egraph
        .parse_and_run_program(
            None,
            "(datatype E (A i64) (B i64) (H E))
                 (relation Old (E))
                 (relation New (E))
                 (relation Target (E))
                 (relation Trigger ())
                 (relation Held (E))
                 (relation Deleted ())
                 (relation Out (E))
                 (ruleset cleanup_old)
                 (ruleset recreate_a)
                 (ruleset early_bridge)
                 (ruleset make_h)
                 (ruleset delete_live)
                 (ruleset late_bridge)
                 (ruleset consume)
                 (Old (A 1))
                 (Target (B 0))
                 (Trigger)
                 (rule ((Trigger))
                       ((delete (A 1)))
                       :ruleset cleanup_old :name \"cleanup-old\")
                 (rule ((Trigger))
                       ((New (A 1)))
                       :ruleset recreate_a :name \"recreate-a\")
                 (rule ((New new) (Target target))
                       ((union new target))
                       :ruleset early_bridge :name \"early-bridge\")
                 (rule ((New child))
                       ((Held (H child)))
                       :ruleset make_h :name \"make-h\")
                 (rule ((Held value))
                       ((delete (H (A 1))) (delete (A 1)) (Deleted))
                       :ruleset delete_live :name \"delete-live\")
                 (rule ((Old old) (Target target) (Deleted))
                       ((union old target))
                       :ruleset late_bridge :name \"late-bridge\")
                 (rule ((Held value) (Deleted))
                       ((Out value))
                       :ruleset consume :name \"consume\")
                 (run cleanup_old 1)
                 (run recreate_a 1)
                 (run early_bridge 1)
                 (run make_h 1)
                 (run delete_live 1)
                 (run late_bridge 1)
                 (run consume 1)
                 (check (Out value))",
        )
        .unwrap();

    let slice = slice_all_checks(&egraph).unwrap();
    // The late old-A=B equality is irrelevant. In particular, it must not
    // make the dead old A occurrence win over the recreated A occurrence
    // that addressed H's key while H was still live.
    assert_eq!(slice.replay_removals.len(), 2);
    let h_plans = slice
        .firing_bindings
        .values()
        .flat_map(|bindings| bindings.iter())
        .filter(|binding| binding.aliases.len() == 2)
        .map(|binding| binding.aliases[1])
        .collect::<Vec<_>>();
    assert_eq!(
        h_plans.len(),
        2,
        "delete-live and consume must each retain child and H alias plans"
    );
    for h_plan in h_plans {
        assert!(
            h_plan.producer.is_some(),
            "the H alias must retain its exact producer: {h_plan:?}"
        );
    }

    let replay = crate::slicing::replay::build_replay_program(&egraph, &slice).unwrap();
    let commands = replay.to_commands().unwrap();
    let rendered = crate::slicing::replay::ReplayProgram::render_commands(&commands);
    let h_alias = rendered
        .lines()
        .position(|line| line.starts_with("(let-check ") && line.contains("(H "))
        .expect("H must be captured while its producer row is live");
    let delete_live = rendered
        .lines()
        .position(|line| line.contains("(run-rule (\"delete-live\""))
        .expect("the selected H deletion must replay");
    assert!(h_alias < delete_live, "{rendered}");
    drop(egraph);

    let mut proof = EGraph::default().with_proofs_enabled().with_proof_testing();
    serial_trace_pool()
        .install(|| proof.run_program(commands))
        .unwrap();
}

#[test]
fn duplicate_syntax_in_one_binding_keeps_distinct_occurrence_windows() {
    let mut egraph = EGraph::default();
    serial_trace_pool()
        .install(|| egraph.enable_trace())
        .unwrap();
    egraph
        .parse_and_run_program(
            None,
            "(datatype E (A i64) (Pair E E))
                 (relation Old (E))
                 (relation New (E))
                 (relation Trigger ())
                 (relation Pairs (E))
                 (relation Out (E))
                 (ruleset cleanup)
                 (ruleset recreate)
                 (ruleset pair_rules)
                 (ruleset consume_rules)
                 (Old (A 1))
                 (Trigger)
                 (rule ((Trigger))
                       ((delete (A 1)))
                       :ruleset cleanup :name \"cleanup\")
                 (rule ((Trigger))
                       ((New (A 1)))
                       :ruleset recreate :name \"recreate\")
                 (rule ((Old old) (New new))
                       ((Pairs (Pair old new)))
                       :ruleset pair_rules :name \"pair\")
                 (rule ((Pairs pair)) ((Out pair))
                       :ruleset consume_rules :name \"consume\")
                 (run cleanup 1)
                 (run recreate 1)
                 (run pair_rules 1)
                 (run consume_rules 1)
                 (check (Out pair))",
        )
        .unwrap();

    let slice = slice_all_checks(&egraph).unwrap();
    let consume_bindings = slice
        .firing_bindings
        .values()
        .find(|bindings| bindings.len() == 1 && bindings[0].aliases.len() == 3)
        .expect("consume must retain two child occurrences and their parent");
    let [old_child, recreated_child, parent] = consume_bindings[0].aliases.as_ref() else {
        unreachable!("alias plan count was checked above")
    };
    assert!(
        old_child.ready_after < recreated_child.ready_after
            && recreated_child.ready_after < parent.ready_after,
        "old child, recreated child, and parent need distinct occurrence-local readiness bounds: {consume_bindings:?}"
    );
    let replay = crate::slicing::replay::build_replay_program(&egraph, &slice).unwrap();
    let commands = replay.to_commands().unwrap();
    let rendered = crate::slicing::replay::ReplayProgram::render_commands(&commands);
    assert!(
        rendered.contains(
            "(run-schedule (run-rule (\"pair\" ((old $__slice_replay_0) (new $__slice_replay_1)))))"
        ),
        "the pair firing must keep the two source occurrence aliases:\n{rendered}"
    );
    assert!(
        rendered.contains(
            "(let-check $__slice_replay_2 (Pair $__slice_replay_0 $__slice_replay_1) :sort E)"
        ),
        "the parent recipe must preserve its old/new child occurrence windows:\n{rendered}"
    );
    let cleanup = rendered
        .find("(run-schedule (run-rule (\"cleanup\"")
        .unwrap();
    let recreate = rendered
        .find("(run-schedule (run-rule (\"recreate\"")
        .unwrap();
    let pair = rendered.find("(run-schedule (run-rule (\"pair\"").unwrap();
    let consume = rendered
        .find("(run-schedule (run-rule (\"consume\"")
        .unwrap();
    assert!(cleanup < recreate && recreate < pair && pair < consume);

    let aliases_before_cleanup = rendered[..cleanup].matches("(let-check ").count();
    let aliases_between_recreate_and_pair = rendered[recreate..pair].matches("(let-check ").count();
    let aliases_between_pair_and_consume = rendered[pair..consume].matches("(let-check ").count();
    assert!(
        aliases_before_cleanup >= 1,
        "old occurrence must be named before deletion"
    );
    assert!(
        aliases_between_recreate_and_pair >= 1,
        "recreated occurrence must be named after its creator"
    );
    assert!(
        aliases_between_pair_and_consume >= 1,
        "parent occurrence must be named after its creator"
    );
    assert!(
        rendered.matches("(A 1) :sort E").count() >= 2,
        "identical syntax before and after recreation must keep distinct aliases:\n{rendered}"
    );
    drop(egraph);

    let mut proof = EGraph::default().with_proofs_enabled().with_proof_testing();
    serial_trace_pool()
        .install(|| proof.run_program(commands))
        .unwrap();
}

#[test]
fn noninterfering_and_dead_write_deletes_are_not_retained() {
    for program in [
        "(function f (i64) i64 :merge (max old new))
             (relation Trigger (Unit))
             (relation Before (i64))
             (set (f 1) 5)
             (Trigger ())
             (rule ((= value (f 1))) ((Before value)) :name \"observe\")
             (rule ((Trigger u)) ((delete (f 1))) :name \"delete-f\")
             (run 1)
             (check (Before 5))",
        "(function f (i64) i64 :merge (max old new))
             (relation Trigger (Unit))
             (relation Write (Unit))
             (relation Independent (Unit))
             (relation Out (Unit))
             (set (f 1) 5)
             (Trigger ())
             (Write ())
             (Independent ())
             (rule ((Trigger u)) ((delete (f 1))) :name \"delete-f\")
             (rule ((Write u)) ((set (f 1) 2)) :name \"dead-write\")
             (rule ((Independent u)) ((Out ())) :name \"make-out\")
             (run 1)
             (check (Out ()))",
    ] {
        let mut egraph = EGraph::default();
        serial_trace_pool()
            .install(|| egraph.enable_trace())
            .unwrap();
        egraph.parse_and_run_program(None, program).unwrap();
        let bridge = egraph
            .backend
            .as_any()
            .downcast_ref::<egglog_bridge::EGraph>()
            .unwrap();
        bridge
            .with_trace_view(|view| {
                assert_eq!(view.totals().removals, 1);
                Ok(())
            })
            .unwrap();
        let slice = slice_all_checks(&egraph).unwrap();
        assert!(slice.replay_removals.is_empty());
    }
}

#[test]
fn merge_old_noop_is_retained_only_with_an_effective_sibling() {
    let mut effective_sibling = EGraph::default();
    serial_trace_pool()
        .install(|| effective_sibling.enable_trace())
        .unwrap();
    effective_sibling
        .parse_and_run_program(
            None,
            "(function f (i64) i64 :merge old)
                 (relation Trigger (Unit))
                 (relation Out (Unit))
                 (set (f 1) 5)
                 (Trigger ())
                 (rule ((Trigger u)) ((set (f 1) 2) (Out ())) :name \"noop-with-sibling\")
                 (run 1)
                 (check (Out ()))",
        )
        .unwrap();
    let slice = slice_all_checks(&effective_sibling).unwrap();
    assert_eq!(slice.firing_bindings.len(), 1);
    let mut replay = replay_slice(effective_sibling, &slice);
    replay
        .parse_and_run_program(None, "(check (= value (f 1)) (= value 5))")
        .unwrap();

    let mut noop_only = EGraph::default();
    serial_trace_pool()
        .install(|| noop_only.enable_trace())
        .unwrap();
    noop_only
        .parse_and_run_program(
            None,
            "(function f (i64) i64 :merge old)
                 (relation Trigger (Unit))
                 (relation Keep (Unit))
                 (set (f 1) 5)
                 (Trigger ())
                 (Keep ())
                 (rule ((Trigger u)) ((set (f 1) 2)) :name \"noop-only\")
                 (run 1)
                 (check (Keep ()))",
        )
        .unwrap();
    let slice = slice_all_checks(&noop_only).unwrap();
    assert!(slice.firing_bindings.is_empty());
    // The lower-level recorder contract (including zero durable promotion)
    // is covered by `unchanged_merge_without_effective_sibling_promotes_nothing`.
    // Here the frontend contract is that an unrelated check never selects
    // or replays the no-op-only firing.
}

#[test]
fn same_term_child_occurrences_keep_their_native_bridge() {
    let mut egraph = EGraph::default();
    serial_trace_pool()
        .install(|| egraph.enable_trace())
        .unwrap();
    egraph
        .parse_and_run_program(
            None,
            "(datatype E (A i64) (H E))
                 (relation Trigger ())
                 (relation Old (E))
                 (relation New (E))
                 (relation R (E))
                 (relation S (E))
                 (relation Out ())
                 (ruleset cleanup)
                 (ruleset recreate)
                 (ruleset bridge)
                 (ruleset emit)
                 (ruleset consume)
                 (Trigger)
                 (Old (A 1))
                 (R (H (A 1)))
                 (rule ((Trigger))
                       ((delete (A 1)))
                       :ruleset cleanup
                       :name \"cleanup\")
                 (rule ((Trigger))
                       ((New (A 1)))
                       :ruleset recreate
                       :name \"recreate\")
                 (rule ((Old x) (New y))
                       ((union x y))
                       :ruleset bridge
                       :name \"bridge\")
                 (rule ((New y))
                       ((S (H y)))
                       :ruleset emit
                       :name \"emit\")
                 (rule ((R x) (S x))
                       ((Out))
                       :ruleset consume
                       :name \"consume\")
                 (run cleanup 1)
                 (run recreate 1)
                 (run bridge 1)
                 (run emit 1)
                 (run consume 1)
                 (check (Out))",
        )
        .unwrap();

    let slice = slice_all_checks(&egraph).unwrap();
    let replay = crate::slicing::replay::build_replay_program(&egraph, &slice).unwrap();
    let commands = replay.to_commands().unwrap();
    drop(egraph);

    let mut proof = EGraph::default().with_proofs_enabled();
    serial_trace_pool()
        .install(|| proof.run_program(commands))
        .unwrap();
}

#[test]
fn relational_check_shared_variable_equality_is_retained() {
    let mut egraph = EGraph::default();
    serial_trace_pool()
        .install(|| egraph.enable_trace())
        .unwrap();
    egraph
        .parse_and_run_program(
            None,
            "(datatype E (A i64) (B i64))
                 (relation R (E))
                 (relation S (E))
                 (rule () ((union (A 1) (B 2))) :name \"eq-ab\")
                 (R (A 1))
                 (S (B 2))
                 (run 1)
                 (check (R x) (S x))",
        )
        .unwrap();

    let slice = slice_all_checks(&egraph).unwrap();
    assert_eq!(slice.firing_bindings.len(), 1);
    replay_slice(egraph, &slice);
}

#[test]
fn selected_firing_exposes_whole_head_without_causal_closing_sibling() {
    let mut egraph = EGraph::default();
    serial_trace_pool()
        .install(|| egraph.enable_trace())
        .unwrap();
    egraph
        .parse_and_run_program(
            None,
            "(relation A (Unit))
                 (relation Out (Unit))
                 (relation Sibling (Unit))
                 (A ())
                 (rule ((A u)) ((Out ()) (Sibling ())) :name \"two-effects\")
                 (run 1)
                 (check (Out ()))",
        )
        .unwrap();

    let slice = slice_all_checks(&egraph).unwrap();
    assert_eq!(slice.firing_bindings.len(), 1);
    let replay = crate::slicing::replay::build_replay_program(&egraph, &slice).unwrap();
    let commands = replay.to_commands().unwrap();
    drop(egraph);

    let mut proof = EGraph::default().with_proofs_enabled().with_proof_testing();
    serial_trace_pool()
        .install(|| proof.run_program(commands))
        .unwrap();
    proof
        .parse_and_run_program(None, "(check (Sibling ()))")
        .unwrap();
}

#[test]
fn no_merge_rewrite_retains_the_interfering_delete() {
    let mut egraph = EGraph::default();
    serial_trace_pool()
        .install(|| egraph.enable_trace())
        .unwrap();
    egraph
        .parse_and_run_program(
            None,
            "(function f (i64) i64 :no-merge)
                 (relation Trigger (Unit))
                 (relation Write (Unit))
                 (relation Done (Unit))
                 (relation Before (i64))
                 (relation After (i64))
                 (set (f 1) 5)
                 (Trigger ())
                 (Write ())
                 (rule ((= value (f 1))) ((Before value)) :name \"observe-before\")
                 (rule ((Trigger u)) ((delete (f 1))) :name \"delete-f\")
                 (rule ((Write u)) ((set (f 1) 2) (Done ())) :name \"rewrite-f\")
                 (rule ((Done u) (= value (f 1))) ((After value)) :name \"observe-after\")
                 (run 2)
                 (check (Before 5) (After 2))",
        )
        .unwrap();

    let slice = slice_all_checks(&egraph).unwrap();
    assert_eq!(slice.firing_bindings.len(), 4);
    assert_eq!(slice.replay_removals.len(), 1);
}

#[test]
fn direct_check_retains_nested_child_equality_used_by_a_head_term() {
    let mut egraph = EGraph::default();
    serial_trace_pool()
        .install(|| egraph.enable_trace())
        .unwrap();
    egraph
        .parse_and_run_program(
            None,
            "(datatype E (A i64) (Alias i64))
                 (sort Es (Vec E))
                 (datatype Root (Target Es) (Seed))
                 (ruleset equate)
                 (ruleset finish)
                 (let $seed (Seed))
                 (A 8)
                 (rewrite (A x) (Alias x) :ruleset equate)
                 (rule ()
                       ((union $seed (Target (vec-of (Alias 8)))))
                       :ruleset finish
                       :name \"finish\")
                 (run equate 1)
                 (run finish 1)
                 (check (= $seed (Target (vec-of (A 8)))))",
        )
        .unwrap();

    let slice = slice_all_checks(&egraph).unwrap();
    assert_eq!(
        slice.firing_bindings.len(),
        2,
        "the parent union and nested A/Alias equality are both required"
    );
    let replay = crate::slicing::replay::build_replay_program(&egraph, &slice).unwrap();
    let commands = replay.to_commands().unwrap();
    drop(egraph);

    let mut proof = EGraph::default().with_proofs_enabled();
    serial_trace_pool()
        .install(|| proof.run_program(commands))
        .unwrap();
}

#[test]
fn eqsort_result_of_replay_safe_primitive_is_structurally_available() {
    let mut egraph = EGraph::default();
    serial_trace_pool()
        .install(|| egraph.enable_trace())
        .unwrap();
    egraph
        .parse_and_run_program(
            None,
            "(datatype E (A i64))
                 (sort Es (Vec E))
                 (relation Seed (Es))
                 (relation Out (E))
                 (Seed (vec-of (A 1)))
                 (rule ((Seed xs)
                        (= x (vec-get xs 0)))
                       ((Out x))
                       :name \"read-vec\")
                 (run 1)
                 (check (Out (A 1)))",
        )
        .unwrap();

    let slice = slice_all_checks(&egraph).unwrap();
    assert_eq!(slice.firing_bindings.len(), 1);
    let replay = crate::slicing::replay::build_replay_program(&egraph, &slice).unwrap();
    let commands = replay.to_commands().unwrap();
    drop(egraph);

    let mut proof = EGraph::default().with_proofs_enabled();
    serial_trace_pool()
        .install(|| proof.run_program(commands))
        .unwrap();
}

#[test]
fn repeated_pure_result_guards_share_one_naming_recipe() {
    let mut egraph = EGraph::default();
    serial_trace_pool()
        .install(|| egraph.enable_trace())
        .unwrap();
    egraph
        .parse_and_run_program(
            None,
            "(relation Input (i64))
                 (relation Out (i64))
                 (Input 1)
                 (rule ((Input n)
                        (= x (+ n 1))
                        (= x (* n 2)))
                       ((Out x))
                       :name \"agreeing-guards\")
                 (run 1)
                 (check (Out 2))",
        )
        .unwrap();

    let slice = slice_all_checks(&egraph).unwrap();
    assert_eq!(slice.firing_bindings.len(), 1);
    let replay = crate::slicing::replay::build_replay_program(&egraph, &slice).unwrap();
    let commands = replay.to_commands().unwrap();
    drop(egraph);

    let mut proof = EGraph::default().with_proofs_enabled();
    serial_trace_pool()
        .install(|| proof.run_program(commands))
        .unwrap();
}

#[test]
fn eqsort_projection_retains_the_child_equality_it_observed() {
    let mut egraph = EGraph::default();
    serial_trace_pool()
        .install(|| egraph.enable_trace())
        .unwrap();
    serial_trace_pool()
        .install(|| {
            egraph.parse_and_run_program(
                None,
                "(datatype E (A) (B))
                 (sort Es (Vec E))
                 (relation Inputs (E E))
                 (relation Out ())
                 (ruleset equate)
                 (ruleset make)
                 (ruleset consume)
                 (rule () ((union (A) (B)))
                       :ruleset equate :name \"equate\")
                 (rule ()
                       ((Inputs (vec-get (vec-of (A)) 0)
                                (vec-get (vec-of (B)) 0)))
                       :ruleset make :name \"make\")
                 (rule ((Inputs x x)) ((Out))
                       :ruleset consume :name \"consume\")
                 (run equate 1)
                 (run make 1)
                 (run consume 1)
                 (check (Out))",
            )
        })
        .unwrap();

    let slice = slice_all_checks(&egraph).unwrap();
    assert_eq!(slice.firing_bindings.len(), 3);
    let replay = crate::slicing::replay::build_replay_program(&egraph, &slice).unwrap();
    let commands = replay.to_commands().unwrap();
    drop(egraph);

    let mut proof = EGraph::default().with_proofs_enabled();
    serial_trace_pool()
        .install(|| proof.run_program(commands))
        .unwrap();
}

#[test]
fn congruence_projection_retains_historical_child_union() {
    let mut egraph = EGraph::default();
    serial_trace_pool()
        .install(|| egraph.enable_trace())
        .unwrap();
    egraph
        .parse_and_run_program(
            None,
            "(datatype E (Num i64) (Add E E) (Max E E))
                 (rewrite (Add (Num a) (Num b)) (Num (+ a b)))
                 (rewrite (Max (Num a) (Num b)) (Num (max a b)))
                 (datatype L (Cons L))
                 (constructor Nil () L)
                 (constructor F (i64 L) E)
                 (rule ((= f (F capacity (Cons rest))))
                       ((union f
                               (Max (Add (Num 1) (F (- capacity 1) rest))
                                    (F capacity rest)))))
                 (rule ((= f (F capacity (Nil))))
                       ((union f (Num 0))))
                 (let $test (F 2 (Cons (Cons (Nil)))))
                 (run 10)
                 (check (= $test (Num 2)))",
        )
        .unwrap();

    let slice = slice_all_checks(&egraph).unwrap();
    let replay = crate::slicing::replay::build_replay_program(&egraph, &slice).unwrap();
    let commands = replay.to_commands().unwrap();
    drop(egraph);

    let mut proof = EGraph::default().with_proofs_enabled().with_proof_testing();
    serial_trace_pool()
        .install(|| proof.run_program(commands))
        .unwrap();
}
