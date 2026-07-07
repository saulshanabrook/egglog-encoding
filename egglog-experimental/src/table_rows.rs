use egglog::{ArcSort, EGraph, Error, TypeError, Value, ast::FunctionSubtype, prelude::Span};

pub(crate) struct TableLayout {
    pub(crate) subtype: FunctionSubtype,
    input_sorts: Vec<ArcSort>,
    output_sort: ArcSort,
}

impl TableLayout {
    pub(crate) fn extraction_sorts(&self) -> Vec<ArcSort> {
        match self.subtype {
            FunctionSubtype::Custom => self
                .input_sorts
                .iter()
                .chain(std::iter::once(&self.output_sort))
                .cloned()
                .collect(),
            FunctionSubtype::Constructor => self.input_sorts.clone(),
        }
    }

    pub(crate) fn column_type_names(&self) -> Vec<String> {
        self.input_sorts
            .iter()
            .map(|sort| sort.name().to_owned())
            .chain(std::iter::once(self.output_sort.name().to_owned()))
            .collect()
    }

    pub(crate) fn input_count(&self) -> usize {
        self.input_sorts.len()
    }
}

pub(crate) fn table_layout(egraph: &EGraph, name: &str, span: Span) -> Result<TableLayout, Error> {
    let func = egraph
        .get_function(name)
        .ok_or_else(|| TypeError::UnboundFunction(name.to_owned(), span))?;
    let schema = func.schema();
    Ok(TableLayout {
        subtype: func.subtype(),
        input_sorts: schema.input.clone(),
        output_sort: schema.output.clone(),
    })
}

pub(crate) fn for_each_table_row(
    egraph: &EGraph,
    name: &str,
    layout: &TableLayout,
    include_constructor_eclass: bool,
    mut visit: impl FnMut(Vec<Value>),
) -> Result<(), Error> {
    match layout.subtype {
        FunctionSubtype::Custom => {
            egraph.function_entries(name, |entry| {
                visit(
                    entry
                        .inputs
                        .iter()
                        .copied()
                        .chain(std::iter::once(entry.output))
                        .collect(),
                );
            })?;
        }
        FunctionSubtype::Constructor => {
            egraph.constructor_enodes(name, |enode| {
                let mut row = enode.children.to_vec();
                if include_constructor_eclass {
                    row.push(enode.eclass);
                }
                visit(row);
            })?;
        }
    }
    Ok(())
}
