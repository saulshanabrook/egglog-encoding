use super::*;
use std::sync::OnceLock;

fn serial_pool() -> &'static rayon::ThreadPool {
    static POOL: OnceLock<rayon::ThreadPool> = OnceLock::new();
    POOL.get_or_init(|| {
        rayon::ThreadPoolBuilder::new()
            .num_threads(1)
            .build()
            .unwrap()
    })
}

#[test]
fn experimental_schedule_executes_only_list_form_grounded_run_rule() {
    let mut egraph = new_experimental_egraph();
    egraph
        .parse_and_run_program(
            None,
            "(relation Input (i64))\
             (relation Output (i64))\
             (ruleset derive)\
             (Input 1)\
             (rule ((Input x)) ((Output x))\
               :ruleset derive :name \"copy\")",
        )
        .unwrap();
    let outputs = egraph
        .parse_and_run_program(
            None,
            "(run-schedule\
               (let-scheduler s (back-off))\
               (seq (run-rule (\"copy\" ((x 1)))))\
               (run-with s derive))",
        )
        .unwrap();
    assert_eq!(
        outputs
            .iter()
            .filter(|output| matches!(output, CommandOutput::RunSchedule(_)))
            .count(),
        1,
        "one public schedule must keep one combined report"
    );
    egraph
        .parse_and_run_program(None, "(check (Output 1))")
        .unwrap();

    let error = egraph
        .parse_and_run_program(None, "(run-schedule (run-rule \"copy\"))")
        .unwrap_err();
    assert!(error.to_string().contains("expected run-rule invocation"));

    let marker = "(__experimental-grounded-run-rule\
        (__experimental-grounded-run-rule-invocation\
          \"copy\"\
          (__experimental-grounded-run-rule-binding x 1)))";
    let error = egraph
        .parse_and_run_program(None, &format!("(run-schedule {marker})"))
        .unwrap_err();
    assert!(error.to_string().contains("not source syntax"));
    let error = egraph
        .parse_and_run_program(None, &format!("({EXTENDED_RUN_SCHEDULE_COMMAND} {marker})"))
        .unwrap_err();
    assert!(error.to_string().contains("not source syntax"));
}

#[test]
fn trace_accepts_the_standard_extended_run_schedule() {
    serial_pool().install(|| {
        let mut egraph = new_experimental_egraph();
        egraph.enable_trace().unwrap();
        egraph
            .parse_and_run_program(
                None,
                "(relation Seed (i64))\
                 (relation Done (i64))\
                 (ruleset derive)\
                 (Seed 1)\
                 (rule ((Seed x)) ((Done x)) :ruleset derive :name \"derive-rule\")\
                 (run-schedule (saturate derive))\
                 (check (Done 1))",
            )
            .unwrap();
    });
}

#[test]
fn failed_extended_schedule_poisons_partial_causal_history() {
    serial_pool().install(|| {
        let mut egraph = new_experimental_egraph();
        egraph.enable_trace().unwrap();
        let error = egraph
            .parse_and_run_program(
                None,
                "(relation Seed (i64))\
                 (relation Done (i64))\
                 (ruleset derive)\
                 (ruleset bad)\
                 (Seed 1)\
                 (rule ((Seed x)) ((Done x)) :ruleset derive :name \"derive-rule\")\
                 (rule ((Seed x)) ((panic \"boom\")) :ruleset bad :name \"bad-rule\")\
                 (run-schedule (seq derive bad))",
            )
            .unwrap_err();
        assert!(error.to_string().contains("boom"));
        assert_eq!(
            egraph.get_size("Done"),
            1,
            "the first schedule step is deliberately not rolled back"
        );
        assert!(
            egraph
                .with_trace_view(|_| Ok(()))
                .unwrap_err()
                .to_string()
                .contains("poisoned"),
            "partial native history must never be paired with a rolled-back catalog"
        );
    });
}

#[test]
fn unsupported_extended_schedule_is_preflighted_before_rules_run() {
    serial_pool().install(|| {
        let mut egraph = new_experimental_egraph();
        egraph.enable_trace().unwrap();
        egraph
            .parse_and_run_program(
                None,
                "(relation Seed (i64))\
                 (relation Done (i64))\
                 (ruleset derive)\
                 (Seed 1)\
                 (rule ((Seed x)) ((Done x)) :ruleset derive :name \"derive-rule\")",
            )
            .unwrap();
        let error = egraph
            .parse_and_run_program(None, "(run-schedule (seq derive (eval 1)))")
            .unwrap_err();
        assert!(
            error
                .to_string()
                .contains("unsupported during causal capture")
        );
        assert_eq!(
            egraph.get_size("Done"),
            0,
            "whole-schedule validation must run before the first native step"
        );
        assert!(
            egraph
                .with_trace_view(|_| Ok(()))
                .unwrap_err()
                .to_string()
                .contains("poisoned"),
            "the conservative transaction boundary poisons any entered command error"
        );
    });
}

#[test]
fn grounded_run_rule_is_preflighted_before_a_causal_schedule_prefix() {
    serial_pool().install(|| {
        let mut egraph = new_experimental_egraph();
        egraph.enable_trace().unwrap();
        egraph
            .parse_and_run_program(
                None,
                "(relation Seed (i64))\
                 (relation Done (i64))\
                 (ruleset derive)\
                 (Seed 1)\
                 (rule ((Seed x)) ((Done x)) :ruleset derive :name \"derive-rule\")",
            )
            .unwrap();
        let error = egraph
            .parse_and_run_program(
                None,
                "(run-schedule\
                   (seq derive (run-rule (\"derive-rule\" ((x 1))))))",
            )
            .unwrap_err();
        assert!(
            error
                .to_string()
                .contains("unsupported during causal capture")
        );
        assert_eq!(egraph.get_size("Done"), 0);
    });
}

#[test]
fn trace_refreshes_either_variant_by_its_logical_child_slot() {
    serial_pool().install(|| {
        let mut egraph = new_experimental_egraph();
        egraph.enable_trace().unwrap();
        egraph
            .parse_and_run_program(
                None,
                "(datatype Expr (A i64) (B i64))\
                 (sort Choice (Either Expr i64))\
                 (function Hold (Unit) Choice :no-merge)\
                 (relation Go (Unit))\
                 (relation Done (Unit))\
                 (let $a (A 1))\
                 (Go ())\
                 (rule ((Go u))\
                   ((set (Hold ()) (either-left (B 2)))\
                    (union (A 1) (B 2))) :name \"merge-child\")\
                 (run 1)\
                 (rule ((= v (Hold ()))\
                        (= v (either-left (A 1))))\
                   ((Done ())) :name \"observe-refresh\")\
                 (run 1)\
                 (check (Done ()))",
            )
            .unwrap();
    });
}

#[test]
fn trace_refreshes_either_right_by_its_logical_child_slot() {
    serial_pool().install(|| {
        let mut egraph = new_experimental_egraph();
        egraph.enable_trace().unwrap();
        egraph
            .parse_and_run_program(
                None,
                "(datatype Expr (A i64) (B i64))\
                 (sort Choice (Either i64 Expr))\
                 (function Hold (Unit) Choice :no-merge)\
                 (relation Go (Unit))\
                 (relation Done (Unit))\
                 (let $a (A 1))\
                 (Go ())\
                 (rule ((Go u))\
                   ((set (Hold ()) (either-right (B 2)))\
                    (union (A 1) (B 2))) :name \"merge-child\")\
                 (run 1)\
                 (rule ((= v (Hold ()))\
                        (= v (either-right (A 1))))\
                   ((Done ())) :name \"observe-refresh\")\
                 (run 1)\
                 (check (Done ()))",
            )
            .unwrap();
    });
}

#[test]
fn trace_refreshes_maybe_some_by_its_logical_child_slot() {
    serial_pool().install(|| {
        let mut egraph = new_experimental_egraph();
        egraph.enable_trace().unwrap();
        egraph
            .parse_and_run_program(
                None,
                "(datatype Expr (A i64) (B i64))\
                 (sort Choice (Maybe Expr))\
                 (function Hold (Unit) Choice :no-merge)\
                 (relation Go (Unit))\
                 (relation Done (Unit))\
                 (let $a (A 1))\
                 (Go ())\
                 (rule ((Go u))\
                   ((set (Hold ()) (maybe-some (B 2)))\
                    (union (A 1) (B 2))) :name \"merge-child\")\
                 (run 1)\
                 (rule ((= v (Hold ()))\
                        (= v (maybe-some (A 1))))\
                   ((Done ())) :name \"observe-refresh\")\
                 (run 1)\
                 (check (Done ()))",
            )
            .unwrap();
    });
}
