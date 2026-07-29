use super::test::FirstNScheduler;
use super::*;

#[test]
fn trace_reject_custom_scheduler_before_internal_table_creation() {
    rayon::ThreadPoolBuilder::new()
        .num_threads(1)
        .build()
        .unwrap()
        .install(|| {
            let mut egraph = EGraph::default();
            egraph.enable_trace().unwrap();
            egraph
                .parse_and_run_program(
                    None,
                    "(ruleset test)\
                     (relation R (i64))\
                     (rule ((R x)) ((R x)) :ruleset test :name \"noop\")",
                )
                .unwrap();
            let scheduler = egraph.add_scheduler(Box::new(FirstNScheduler { n: 1 }));
            let error = egraph
                .step_rules_with_scheduler(scheduler, "test")
                .unwrap_err();
            assert!(error.to_string().contains("does not support run-with"));
            let bridge = egraph
                .backend
                .as_any()
                .downcast_ref::<egglog_bridge::EGraph>()
                .unwrap();
            assert!(
                bridge
                    .action_registry()
                    .read()
                    .unwrap()
                    .lookup_table("backend")
                    .is_none(),
                "rejection must precede custom-scheduler worklist creation"
            );
        });
}
