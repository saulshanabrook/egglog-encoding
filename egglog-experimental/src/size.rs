//! Inspect e-graph table and e-node counts from egglog expressions.
//!
//! `(get-size!)` returns the sum of all non-internal table sizes.
//! `(get-size! "A" "B")` returns the sum for the named tables. The primitive
//! is read-capable, so it can also be used in extended schedule guards and
//! `eval` steps.
//! `(get-node-size!)` returns the visible e-node count.

use std::convert::TryFrom;

use egglog::{
    Core, Primitive, Read, ReadPrim, ReadState, Value,
    ast::FunctionSubtype,
    constraint::{AllEqualTypeConstraint, TypeConstraint},
    prelude::BaseSort,
    prelude::{I64Sort, Span, StringSort},
    sort::S,
    util::INTERNAL_SYMBOL_PREFIX,
};

/// Read primitive implementing `(get-size! "table"...)`.
///
/// With no arguments it sums all non-internal tables. String arguments limit
/// the sum to the named tables.
#[derive(Clone)]
pub struct GetSizePrimitive;

impl Primitive for GetSizePrimitive {
    fn name(&self) -> &str {
        "get-size!"
    }

    fn get_type_constraints(&self, span: &Span) -> Box<dyn TypeConstraint> {
        AllEqualTypeConstraint::new(self.name(), span.clone())
            .with_output_sort(I64Sort.to_arcsort())
            .with_all_arguments_sort(StringSort.to_arcsort())
            .into_box()
    }
}

impl ReadPrim for GetSizePrimitive {
    fn apply<'a, 'db>(&self, state: ReadState<'a, 'db>, args: &[Value]) -> Option<Value> {
        let size: usize = match args {
            [] => state
                .table_sizes()
                .into_iter()
                .filter_map(|(name, size)| {
                    if name.starts_with(INTERNAL_SYMBOL_PREFIX) {
                        global_rows(&state, name, None)
                    } else {
                        Some(size)
                    }
                })
                .sum(),
            tables => tables
                .iter()
                .map(|value| state.base_values().unwrap::<S>(*value).0)
                .map(|name| {
                    state.table_size(&name).unwrap_or_else(|| {
                        state
                            .tables()
                            .filter_map(|table| global_rows(&state, table, Some(&name)))
                            .sum()
                    })
                })
                .sum(),
        };
        let size = i64::try_from(size).ok()?;
        Some(state.base_values().get::<i64>(size))
    }
}

// A shared global table is internal, but its source bindings still count as
// separate user rows. Reading their string keys also works after desugared replay.
fn global_rows(state: &ReadState<'_, '_>, table: &str, requested: Option<&str>) -> Option<usize> {
    let signature = state.function_schema(table).ok()?;
    if !signature.role.is_global()
        || signature.input.len() != 1
        || signature.input[0].name() != "String"
    {
        return None;
    }
    let mut count = 0;
    let mut visit = |keys: &[Value]| {
        let name = state.base_values().unwrap::<S>(keys[0]).0;
        if requested.map_or_else(
            || !name.starts_with(INTERNAL_SYMBOL_PREFIX),
            |requested| name == requested,
        ) {
            count += 1;
        }
    };
    // Eq-sort globals have constructor-style views under term encoding.
    state
        .function_entries(table, |row| visit(row.inputs))
        .or_else(|_| state.constructor_enodes(table, |row| visit(row.children)))
        .ok()?;
    Some(count)
}

/// `(get-node-size!)`: the number of e-nodes in visible constructor tables whose
/// output is a unionable eq-sort.
///
/// Unlike `(get-size!)`, it excludes relations, analysis functions, global
/// aliases, hidden declarations, and internal-prefixed implementation tables.
/// On an ordinary experimental e-graph, this is the same measure as the
/// back-off scheduler's `:node-limit`.
#[derive(Clone)]
pub struct GetNodeSizePrimitive;

impl Primitive for GetNodeSizePrimitive {
    fn name(&self) -> &str {
        "get-node-size!"
    }

    fn get_type_constraints(&self, span: &Span) -> Box<dyn TypeConstraint> {
        AllEqualTypeConstraint::new(self.name(), span.clone())
            .with_output_sort(I64Sort.to_arcsort())
            .with_exact_length(1)
            .into_box()
    }
}

impl ReadPrim for GetNodeSizePrimitive {
    fn apply<'a, 'db>(&self, state: ReadState<'a, 'db>, args: &[Value]) -> Option<Value> {
        if !args.is_empty() {
            return None;
        }
        let size: usize = state
            .table_sizes()
            .into_iter()
            .filter_map(|(name, size)| {
                if name.starts_with(INTERNAL_SYMBOL_PREFIX)
                    || state.is_table_hidden(name)?
                    || state.table_subtype(name)? != FunctionSubtype::Constructor
                {
                    return None;
                }
                let output = state.constructor_schema(name).ok()?.output();
                state.is_sort_unionable(output)?.then_some(size)
            })
            .sum();
        let size = i64::try_from(size).ok()?;
        Some(state.base_values().get::<i64>(size))
    }
}
