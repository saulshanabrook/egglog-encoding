//! Joint selection on the case study's acyclic planning graph.

use crate::{Planner, terms::Id};
use anyhow::{Result, ensure};
use highs::{HighsModelStatus, HighsSolutionStatus, RowProblem, Sense};
use serde_json::{Value, json};
use std::{
    collections::{BTreeMap, BTreeSet},
    time::Instant,
};

pub(super) fn solve(g: &Planner, timeout: f64) -> Result<(BTreeMap<Id, usize>, Value)> {
    let start = Instant::now();
    let mut tree = BTreeMap::new();
    let mut selected = BTreeMap::new();
    for c in g.order(None)? {
        let (cost, choice) = g.options[&c]
            .iter()
            .enumerate()
            .map(|(i, v)| {
                (
                    g.cost(v) + v.dependencies().iter().map(|d| tree[d]).sum::<u64>(),
                    i,
                )
            })
            .min()
            .unwrap();
        tree.insert(c, cost);
        selected.insert(c, choice);
    }
    let initial = g.score(&selected)?;
    let mut problem = RowProblem::default();
    let variables: BTreeMap<_, Vec<_>> = g
        .options
        .iter()
        .map(|(&c, vs)| {
            (
                c,
                vs.iter()
                    .map(|v| problem.add_integer_column(g.cost(v) as f64, 0..=1))
                    .collect(),
            )
        })
        .collect();
    let roots: BTreeSet<_> = g.roots.iter().copied().collect();
    for (&c, vars) in &variables {
        problem.add_row(
            i32::from(roots.contains(&c))..=1,
            vars.iter().map(|&v| (v, 1.0)),
        );
        for (v, &x) in g.options[&c].iter().zip(vars) {
            for child in v.dependencies().into_iter().collect::<BTreeSet<_>>() {
                problem.add_row(
                    ..=0,
                    std::iter::once((x, 1.0)).chain(variables[&child].iter().map(|&y| (y, -1.0))),
                );
            }
        }
    }
    let objective: Vec<_> = g
        .options
        .iter()
        .flat_map(|(c, vs)| {
            vs.iter()
                .zip(&variables[c])
                .map(|(v, &x)| (x, g.cost(v) as f64))
        })
        .collect();
    problem.add_row(..=initial as f64, objective.iter().copied());
    let mut warm = vec![0.0; objective.len()];
    for c in g.order(Some(&selected))? {
        warm[variables[&c][selected[&c]].index()] = 1.0;
    }
    let mut model = problem.optimise(Sense::Minimise);
    model.make_quiet();
    model.set_option("threads", 1);
    model.set_option("mip_rel_gap", 0.0);
    model.set_option("mip_abs_gap", 0.0);
    model.set_solution(Some(&warm), None, None, None);
    model.set_option(
        "time_limit",
        (timeout - start.elapsed().as_secs_f64()).max(0.001),
    );
    let solved = model.solve();
    let mut accepted = false;
    if solved.primal_solution_status() == HighsSolutionStatus::Feasible {
        let values = solved.get_solution();
        let candidate: BTreeMap<_, _> = variables
            .iter()
            .filter_map(|(&c, xs)| {
                xs.iter()
                    .position(|&x| values.columns()[x.index()] > 0.5)
                    .map(|i| (c, i))
            })
            .collect();
        ensure!(
            g.score(&candidate)? <= initial,
            "solver returned a worse incumbent"
        );
        selected = candidate;
        accepted = true;
    }
    let cost = g.score(&selected)?;
    let bound = solved
        .double_info_value(c"mip_dual_bound")
        .ok()
        .filter(|v| v.is_finite());
    Ok((
        selected.clone(),
        json!({
            "estimated_cost": cost,
            "initial_tree_plan_dag_cost": initial,
            "selected_nodes": selected,
            "cost_description": "producer + join inputs + grouping columns; per-column update/output + local functions; shared producers charged once",
            "solver": {
                "method": "HiGHS MILP: one joint DAG over all output roots",
                "status": format!("{:?}", solved.status()),
                "optimal": solved.status() == HighsModelStatus::Optimal && accepted,
                "optimality_scope": "configured structural DAG objective within the egraph, not runtime",
                "warm_start": true,
                "accepted_solver_plan": accepted,
                "lower_bound": bound,
                "relative_gap": bound.map(|b| (cost as f64 - b).max(0.0) / (cost as f64).max(1.0)),
                "seconds": start.elapsed().as_secs_f64(),
                "time_limit_seconds": timeout,
                "node_variables": objective.len()
            }
        }),
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Alternative, Column, Region};

    fn problem(options: Vec<Vec<(u64, Vec<Id>)>>, roots: Vec<Id>) -> Planner {
        let regions = BTreeMap::from([(
            0,
            Region {
                origin: 0,
                destination: 0,
                attributes: 0,
                functions: 0,
                local: 0,
                children: vec![],
            },
        )]);
        let options = options
            .into_iter()
            .enumerate()
            .map(|(c, choices)| {
                (
                    c,
                    choices
                        .into_iter()
                        .map(|(cost, incoming)| Alternative {
                            region: 0,
                            keys: 0,
                            column: Some(Column {
                                weights: 0,
                                local: (1 << (cost - 3)) - 1,
                                incoming,
                                producer: None,
                            }),
                        })
                        .collect(),
                )
            })
            .collect();
        Planner {
            regions,
            options,
            roots,
        }
    }

    #[test]
    fn joint_selection_pays_shared_work_once() {
        let g = problem(
            vec![
                vec![(8, vec![]), (3, vec![2])],
                vec![(8, vec![]), (3, vec![2])],
                vec![(8, vec![])],
            ],
            vec![0, 1],
        );
        let (selected, report) = solve(&g, 5.0).unwrap();
        assert_eq!(g.score(&selected).unwrap(), 14);
        assert_eq!(report["initial_tree_plan_dag_cost"], 16);
        assert_eq!(report["solver"]["optimal"], true);
    }

    #[test]
    fn small_dags_match_exhaustive_search() {
        let mut seed = 7814u64;
        let mut next = || {
            seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
            seed >> 32
        };
        for _ in 0..20 {
            let options = (0..4)
                .map(|c| {
                    (0..2)
                        .map(|_| (3 + next() % 7, (0..c).filter(|_| next() % 2 == 0).collect()))
                        .collect()
                })
                .collect();
            let g = problem(options, vec![2, 3]);
            let optimum = (0..16)
                .map(|bits| {
                    let selected = (0..4).map(|c| (c, (bits >> c) & 1)).collect();
                    g.score(&selected).unwrap()
                })
                .min()
                .unwrap();
            let (selected, report) = solve(&g, 5.0).unwrap();
            assert_eq!(g.score(&selected).unwrap(), optimum);
            assert_eq!(report["solver"]["optimal"], true);
        }
    }

    #[test]
    fn cycles_fail_before_solving() {
        for dependency in [0, 1] {
            let g = problem(
                vec![vec![(4, vec![]), (3, vec![dependency])], vec![(3, vec![0])]],
                vec![0],
            );
            assert!(solve(&g, 5.0).unwrap_err().to_string().contains("cyclic"));
        }
    }

    #[test]
    fn solver_limit_keeps_feasible_plan() {
        let g = problem(
            vec![
                vec![(8, vec![]), (3, vec![2])],
                vec![(8, vec![]), (3, vec![2])],
                vec![(8, vec![])],
            ],
            vec![0, 1],
        );
        let (selected, _) = solve(&g, 1e-9).unwrap();
        assert!(g.score(&selected).unwrap() <= 16);
    }
}
