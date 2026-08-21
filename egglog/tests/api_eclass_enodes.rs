//! Tests for `eclass_enodes`, over the `EGraph` form.
//!
//! `agrees_with_a_filtered_scan_over_every_table` is the one to keep passing if this
//! is ever reimplemented over an output-column index.

use egglog::prelude::*;
use egglog::{Error, Value};

const MATH: &str = "
(datatype Math
  (Num i64)
  (Var String)
  (Add Math Math)
  (Mul Math Math))
(function cost (Math) i64 :no-merge)
";

/// Collect `(table, children)` for one eclass, via the new method.
fn by_eclass(egraph: &mut EGraph, eclass: Value) -> Result<Vec<(String, Vec<Value>)>, Error> {
    let mut out = Vec::new();
    egraph.eclass_enodes(eclass, |enode| {
        out.push((enode.name.to_string(), enode.children.to_vec()));
    })?;
    out.sort();
    Ok(out)
}

/// The same, assembled by scanning each table and filtering -- what a caller had
/// to write before, and the answer the method must agree with.
fn by_scan(egraph: &mut EGraph, eclass: Value) -> Result<Vec<(String, Vec<Value>)>, Error> {
    let mut out = Vec::new();
    for table in ["Num", "Var", "Add", "Mul"] {
        egraph.constructor_enodes(table, |enode| {
            if enode.eclass == eclass {
                out.push((table.to_string(), enode.children.to_vec()));
            }
        })?;
    }
    out.sort();
    Ok(out)
}

fn eclass_of_expr(egraph: &mut EGraph, name: &str) -> Value {
    egraph
        .eval_expr(&egglog::var!(name))
        .expect("global should exist")
        .1
}

#[test]
fn agrees_with_a_filtered_scan_over_every_table() -> Result<(), Error> {
    let mut egraph = EGraph::default();
    egraph.parse_and_run_program(
        None,
        &format!(
            "{MATH}
;; two e-nodes of one class in different tables
(let $a (Add (Num 1) (Num 2)))
(let $b (Mul (Num 3) (Num 4)))
(union $a $b)
(let $c (Add (Num 9) (Num 9)))
"
        ),
    )?;

    for global in ["$a", "$c"] {
        let eclass = eclass_of_expr(&mut egraph, global);
        assert_eq!(
            by_eclass(&mut egraph, eclass)?,
            by_scan(&mut egraph, eclass)?,
            "{global}: eclass_enodes disagreed with a filtered scan"
        );
    }
    Ok(())
}

#[test]
fn reports_the_table_each_enode_came_from() -> Result<(), Error> {
    let mut egraph = EGraph::default();
    egraph.parse_and_run_program(
        None,
        &format!(
            "{MATH}
(let $a (Add (Num 1) (Num 2)))
(let $b (Mul (Num 3) (Num 4)))
(union $a $b)
"
        ),
    )?;

    let eclass = eclass_of_expr(&mut egraph, "$a");
    let mut tables: Vec<String> = Vec::new();
    egraph.eclass_enodes(eclass, |enode| tables.push(enode.name.to_string()))?;
    tables.sort();
    assert_eq!(
        tables,
        vec!["Add".to_string(), "Mul".to_string()],
        "a class holding one Add and one Mul should report both tables"
    );
    Ok(())
}

#[test]
fn skips_function_tables() -> Result<(), Error> {
    // `cost` is an analysis over Math, not part of the term structure.
    let mut egraph = EGraph::default();
    egraph.parse_and_run_program(
        None,
        &format!(
            "{MATH}
(let $a (Add (Num 1) (Num 2)))
(set (cost $a) 7)
"
        ),
    )?;

    let eclass = eclass_of_expr(&mut egraph, "$a");
    let mut tables: Vec<String> = Vec::new();
    egraph.eclass_enodes(eclass, |enode| tables.push(enode.name.to_string()))?;
    assert_eq!(tables, vec!["Add".to_string()]);
    Ok(())
}

#[test]
fn stops_early_when_asked() -> Result<(), Error> {
    let mut egraph = EGraph::default();
    egraph.parse_and_run_program(
        None,
        &format!(
            "{MATH}
(let $a (Add (Num 1) (Num 2)))
(let $b (Mul (Num 3) (Num 4)))
(union $a $b)
"
        ),
    )?;

    let eclass = eclass_of_expr(&mut egraph, "$a");
    let mut seen = 0;
    egraph.eclass_enodes_while(eclass, |_| {
        seen += 1;
        false
    })?;
    assert_eq!(
        seen, 1,
        "returning false should stop after the first e-node"
    );
    Ok(())
}

#[test]
fn an_eclass_with_no_enodes_yields_nothing() -> Result<(), Error> {
    let mut egraph = EGraph::default();
    egraph.parse_and_run_program(None, MATH)?;
    // a value that is not any class's eclass column
    let mut seen = 0;
    egraph.eclass_enodes(Value::new_const(12345), |_| seen += 1)?;
    assert_eq!(seen, 0);
    Ok(())
}
