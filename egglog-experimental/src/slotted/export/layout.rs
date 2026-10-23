//! Recover typed layouts from the metadata emitted with lowered constructors.
//!
//! Reading the live metadata also supports already lowered programs. Check it
//! against actual table signatures before interpreting any untyped `Value`.

use std::collections::{BTreeMap, BTreeSet};

use egglog::{EGraph, Value, ast::FunctionSubtype, sort::S};

use super::super::model::{Column, Constructor, Symbols};

pub(super) struct Layouts {
    pub carriers: Vec<Symbols>,
    pub constructors: BTreeMap<String, Constructor>,
}

fn rows(graph: &EGraph, name: &str, sorts: &[&str]) -> Result<Vec<Vec<Value>>, String> {
    let function = graph
        .get_function(name)
        .ok_or_else(|| format!("missing {name}"))?;
    let schema = function.func_type();
    if function.subtype() != FunctionSubtype::Custom
        || schema
            .input
            .iter()
            .map(|s| s.name())
            .ne(sorts.iter().copied())
        || schema.outputs.len() != 1
        || schema.output().name() != "Unit"
    {
        return Err(format!("invalid metadata schema for {name}"));
    }
    let mut out = Vec::new();
    graph
        .function_entries(name, |row| out.push(row.inputs.to_vec()))
        .map_err(|e| e.to_string())?;
    Ok(out)
}

impl Layouts {
    pub fn load(graph: &EGraph) -> Result<Self, String> {
        let text = |v| graph.value_to_base::<S>(v).into_inner();
        let integer = |v| graph.value_to_base::<i64>(v);
        let mut arities = BTreeMap::new();
        for row in rows(graph, "SlottedNodeLayout", &["String", "i64"])? {
            let name = text(row[0]);
            let arity = usize::try_from(integer(row[1]))
                .map_err(|_| format!("negative arity for {name}"))?;
            if arities.insert(name.clone(), arity).is_some() {
                return Err(format!("conflicting node layouts for {name}"));
            }
        }
        let mut columns: BTreeMap<String, BTreeMap<usize, Column>> = BTreeMap::new();
        let mut add = |name: String, column: i64, kind: Column| -> Result<(), String> {
            let column =
                usize::try_from(column).map_err(|_| format!("negative column for {name}"))?;
            if !arities.contains_key(&name)
                || columns
                    .entry(name.clone())
                    .or_default()
                    .insert(column, kind)
                    .is_some()
            {
                return Err(format!(
                    "unknown or overlapping layout for {name} column {column}"
                ));
            }
            Ok(())
        };
        for row in rows(graph, "SlottedEdgeLayout", &["String", "i64"])? {
            add(text(row[0]), integer(row[1]), Column::Child)?;
        }
        for row in rows(graph, "SlottedPayloadLayout", &["String", "i64", "String"])? {
            add(text(row[0]), integer(row[1]), Column::Payload(text(row[2])))?;
        }
        let mut covered = BTreeMap::<String, BTreeSet<usize>>::new();
        for row in rows(
            graph,
            "SlottedBinderLayout",
            &["String", "i64", "i64", "i64", "String"],
        )? {
            let name = text(row[0]);
            let marker = usize::try_from(integer(row[1])).map_err(|_| "negative binder column")?;
            let body = usize::try_from(integer(row[2])).map_err(|_| "negative covered column")?;
            if integer(row[3]) != -1 || !text(row[4]).is_empty() {
                return Err(format!(
                    "conditional binder metadata is unsupported for {name}"
                ));
            }
            let col = columns.get_mut(&name).and_then(|c| c.get_mut(&marker));
            if col.as_deref() != Some(&Column::Child) {
                return Err(format!("invalid binder column {marker} for {name}"));
            }
            *col.unwrap() = Column::Binder;
            covered.entry(name).or_default().insert(body);
        }
        let mut carriers = BTreeMap::new();
        let mut constructors = BTreeMap::new();
        for (name, arity) in arities {
            let function = graph
                .get_function(&name)
                .ok_or_else(|| format!("missing constructor {name}"))?;
            let schema = function.func_type();
            if function.subtype() != FunctionSubtype::Constructor
                || schema.input.len() != arity
                || schema.outputs.len() != 1
                || !schema.output().is_eq_sort()
            {
                return Err(format!("invalid constructor schema for {name}"));
            }
            let sort = schema.output().name().to_owned();
            let cols = columns.remove(&name).unwrap_or_default();
            if let Some(index) = name
                .strip_prefix("SlottedVar_")
                .and_then(|s| s.parse::<usize>().ok())
            {
                if arity != 1 || schema.input[0].name() != "i64" || !cols.is_empty() {
                    return Err(format!("invalid variable layout for {name}"));
                }
                if carriers
                    .insert(sort.clone(), Symbols::new(&sort, index))
                    .is_some()
                {
                    return Err(format!("multiple variable constructors for {sort}"));
                }
                continue;
            }
            let mut physical = 0;
            let mut out = Vec::new();
            let mut edge_columns = Vec::new();
            for (col, kind) in cols {
                if col != physical {
                    return Err(format!(
                        "missing or overlapping column {physical} for {name}"
                    ));
                }
                match &kind {
                    Column::Payload(ty) if ["i64", "String"].contains(&ty.as_str()) => {
                        if schema.input.get(col).map(|s| s.name()) != Some(ty.as_str()) {
                            return Err(format!("payload type mismatch for {name} column {col}"));
                        }
                        physical += 1;
                    }
                    Column::Child | Column::Binder => {
                        edge_columns.push(col);
                        if schema.input.get(col).map(|s| s.name()) != Some("Renaming")
                            || schema.input.get(col + 1).map(|s| s.name()) != Some(sort.as_str())
                        {
                            return Err(format!("edge type mismatch for {name} column {col}"));
                        }
                        physical += 2;
                    }
                    _ => return Err(format!("unsupported payload in {name}")),
                }
                out.push(kind);
            }
            let op = Constructor {
                name: name.clone(),
                sort,
                columns: out,
            };
            let binders = op.binders();
            let covered_column = op.covered().and_then(|i| edge_columns.get(i)).copied();
            if physical != arity
                || (!binders.is_empty() && covered_column.is_none())
                || covered.remove(&name).unwrap_or_default() != covered_column.into_iter().collect()
                || binders.windows(2).any(|w| w[1] != w[0] + 1)
            {
                return Err(format!("incomplete or invalid column layout for {name}"));
            }
            constructors.insert(name, op);
        }
        if carriers.is_empty()
            || !columns.is_empty()
            || !covered.is_empty()
            || constructors
                .values()
                .any(|c| !carriers.contains_key(&c.sort))
        {
            return Err("incomplete slotted layout metadata".into());
        }
        // Counting only the layouts we happened to find could silently lose a
        // constructor if its metadata row were missing. Check declaration coverage.
        for (name, function) in graph.functions_iter() {
            if function.subtype() == FunctionSubtype::Constructor
                && !function.is_let_binding()
                && (carriers.contains_key(function.func_type().output().name())
                    || name.starts_with("SlottedVar_"))
                && !constructors.contains_key(name)
                && !carriers.values().any(|s| s.var == *name)
            {
                return Err(format!("missing node layout for constructor {name}"));
            }
        }
        for s in carriers.values() {
            for (name, kind, input, output) in [
                (
                    &s.free_vars,
                    FunctionSubtype::Custom,
                    vec![s.sort.as_str()],
                    Some("Renaming"),
                ),
                (
                    &s.group,
                    FunctionSubtype::Custom,
                    vec![s.sort.as_str()],
                    Some("Group"),
                ),
                (
                    &s.renames,
                    FunctionSubtype::Constructor,
                    vec![s.sort.as_str(), "Renaming", s.sort.as_str()],
                    None, // Relations have a generated, non-unionable output sort.
                ),
            ] {
                let function = graph
                    .get_function(name)
                    .ok_or_else(|| format!("missing {name}"))?;
                let schema = function.func_type();
                if function.subtype() != kind
                    || schema.input.iter().map(|s| s.name()).ne(input)
                    || schema.outputs.len() != 1
                    || output.is_some_and(|ty| schema.output().name() != ty)
                {
                    return Err(format!("invalid invariant table schema for {name}"));
                }
            }
        }
        Ok(Self {
            carriers: carriers.into_values().collect(),
            constructors,
        })
    }
}
