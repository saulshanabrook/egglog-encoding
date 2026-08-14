//! Regression tests for ruleset runs that bypass core egglog's `run-schedule`
//! command and therefore used to be absent from the overall run report.

use egglog::CommandOutput;
use egglog_reports::RunReport;
use std::collections::BTreeSet;

const PROGRAM: &str = r#"
    (ruleset grow)
    (ruleset copy)
    (relation seed (i64))
    (relation grown (i64))
    (relation copied (i64))
    (rule ((seed x)) ((grown x)) :ruleset grow)
    (rule ((grown x)) ((copied x)) :ruleset copy)
    (seed 1)
"#;

fn ruleset_names(report: &RunReport) -> Vec<String> {
    report
        .iterations
        .iter()
        .map(|iteration| iteration.name.to_string())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

#[test]
fn extended_schedule_records_direct_ruleset_steps() {
    let mut egraph = egglog_experimental::new_experimental_egraph();
    egraph.parse_and_run_program(None, PROGRAM).unwrap();
    egraph
        .parse_and_run_program(None, "(let-scheduler bo (back-off))")
        .unwrap();
    egraph
        .parse_and_run_program(None, "(run-schedule (seq (run grow) (run-with bo copy)))")
        .unwrap();

    assert_eq!(
        ruleset_names(egraph.get_overall_run_report()),
        ["copy", "grow"]
    );
}

#[test]
fn core_schedule_records_each_iteration_once() {
    let mut egraph = egglog::EGraph::default();
    egraph.parse_and_run_program(None, PROGRAM).unwrap();
    let outputs = egraph
        .parse_and_run_program(None, "(run-schedule (run grow))")
        .unwrap();
    let returned = outputs
        .iter()
        .find_map(|output| match output {
            CommandOutput::RunSchedule(report) => Some(report),
            _ => None,
        })
        .expect("run-schedule should return a report");

    assert_eq!(returned.iterations.len(), 1);
    assert_eq!(egraph.get_overall_run_report().iterations.len(), 1);
}
