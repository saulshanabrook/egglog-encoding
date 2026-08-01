//! The extended scheduler runs rule sets without going through the
//! `run-schedule` command, so it is the case that most easily goes unrecorded.

use egglog_reports::RunReport;

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

fn ruleset_names(report: &RunReport) -> Vec<&str> {
    let mut names: Vec<&str> = report
        .ruleset_timings
        .keys()
        .map(|name| name.as_ref())
        .collect();
    names.sort_unstable();
    names
}

/// Both spellings of a schedule step reach the report, though only one of them
/// runs as a command: `(run grow)` calls into the e-graph directly.
#[test]
fn extended_schedule_records_every_ruleset_it_runs() {
    let mut egraph = egglog_experimental::new_experimental_egraph();
    egraph
        .parse_and_run_program(
            None,
            &format!("{PROGRAM}\n(run-schedule (seq (run grow) (saturate copy)))"),
        )
        .unwrap();

    assert_eq!(
        ruleset_names(egraph.get_overall_run_report()),
        ["copy", "grow"]
    );
}

/// The rule sets a schedule runs are not the schedule's own cost, so a schedule
/// that only drives rule sets is charged far less than they are.
#[test]
fn scheduling_costs_less_than_the_rule_sets_it_drives() {
    let mut egraph = egglog_experimental::new_experimental_egraph();
    egraph
        .parse_and_run_program(
            None,
            &format!("{PROGRAM}\n(run-schedule (saturate (seq (run grow) (run copy))))"),
        )
        .unwrap();

    let recorded = egraph.get_overall_run_report().total_ruleset_time();
    assert!(recorded > std::time::Duration::ZERO);
    assert!(
        egraph.phase_timings().schedule < recorded,
        "schedule {:?} should be under the {recorded:?} of rule sets it drove",
        egraph.phase_timings().schedule,
    );
}

/// Time spent inside a `push`/`pop` scope was still spent. Phase timings only
/// ever go up, which the phase wrappers rely on to measure what they nest.
#[test]
fn timings_survive_a_pop() {
    let mut egraph = egglog_experimental::new_experimental_egraph();
    egraph.parse_and_run_program(None, PROGRAM).unwrap();
    let before = egraph.phase_timings().total();
    let recorded_before = egraph.get_overall_run_report().total_ruleset_time();

    egraph
        .parse_and_run_program(
            None,
            "(push)\n(run-schedule (saturate (run grow)))\n(pop)\n(run-schedule (saturate (run copy)))",
        )
        .unwrap();

    assert!(egraph.phase_timings().total() >= before);
    assert!(egraph.get_overall_run_report().total_ruleset_time() >= recorded_before);
    assert_eq!(
        ruleset_names(egraph.get_overall_run_report()),
        ["copy", "grow"]
    );
}
