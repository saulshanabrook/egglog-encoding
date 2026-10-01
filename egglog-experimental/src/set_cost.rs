use egglog::{
    EGraph, Enode, RawValues, Read,
    ast::*,
    extract::{CostModel, DefaultCost, TreeAdditiveCostModel},
    util::FreshGen,
};
use egglog_ast::span::Span;
use std::sync::Arc;

pub fn add_set_cost(egraph: &mut EGraph) {
    egraph
        .parser
        .add_command_macro(Arc::new(SetCostDeclarations));
    egraph.parser.add_action_macro(Arc::new(SetCost));
    egraph.extract_command = |egraph, sort, value, variants| {
        egraph.extract_command_with_cost_model(sort, value, variants, DynamicCostModel)
    };
}

struct SetCost;

impl Macro<Vec<Action>> for SetCost {
    fn name(&self) -> &str {
        "set-cost"
    }

    fn parse(
        &self,
        args: &[Sexp],
        span: Span,
        parser: &mut Parser,
    ) -> Result<Vec<Action>, ParseError> {
        match args {
            [call, value] => {
                let (func, args, call_span) = call.expect_call("table lookup")?;
                let cost_table_name = get_cost_table_name(&func);
                let args = map_fallible(args, parser, Parser::parse_expr)?;
                let value = parser.parse_expr(value)?;

                let mut actions = vec![];
                let args = args
                    .into_iter()
                    .map(|expr| match expr {
                        // Reusing atoms is safe and avoids unsupported primitive
                        // global bindings in proof mode. Evaluate calls only once.
                        Expr::Lit(..) | Expr::Var(..) => expr,
                        expr => {
                            let name = parser.symbol_gen.fresh("set_cost_var");
                            let span = expr.span().clone();
                            actions.push(Action::Let(span.clone(), name.clone(), expr));
                            Expr::Var(span, name)
                        }
                    })
                    .collect::<Vec<_>>();

                // We don't create costs for nodes that don't exist.
                actions.push(Action::Expr(
                    span.clone(),
                    Expr::Call(call_span.clone(), func, args.clone()),
                ));
                actions.push(Action::Set(span, cost_table_name, args, value));
                Ok(actions)
            }
            _ => Err(ParseError(
                span,
                "usage: (set-cost (<table name> <expr>*) <expr>)".to_string(),
            )),
        }
    }
}

struct SetCostDeclarations;

impl Macro<Vec<Command>> for SetCostDeclarations {
    fn name(&self) -> &str {
        "with-dynamic-cost"
    }

    fn parse(
        &self,
        decls: &[Sexp],
        span: Span,
        parser: &mut Parser,
    ) -> Result<Vec<Command>, ParseError> {
        let decls = map_fallible(decls, parser, Parser::parse_command)?
            .into_iter()
            .flatten()
            .collect::<Vec<_>>();
        let mut cost_table_commands = vec![];
        for decl in decls.iter() {
            match decl {
                Command::Datatype { variants, .. } => {
                    let commands = generate_cost_table_commands_from_variants(variants);
                    cost_table_commands.extend(commands);
                }
                Command::Datatypes { datatypes, .. } => {
                    let commands =
                        datatypes.iter().flat_map(
                            |(_span, _name, subdatatypes)| match subdatatypes {
                                Subdatatypes::Variants(variants) => {
                                    generate_cost_table_commands_from_variants(variants)
                                }
                                Subdatatypes::NewSort(..) => vec![],
                            },
                        );
                    cost_table_commands.extend(commands);
                }
                Command::Constructor {
                    name,
                    schema,
                    span,
                    unextractable,
                    ..
                } => {
                    if !*unextractable {
                        let cost_table_name = get_cost_table_name(name);
                        let mut cost_table_schema = schema.clone();
                        cost_table_schema.outputs = vec!["i64".into()];
                        cost_table_commands.push(Command::Function {
                            span: span.clone(),
                            name: cost_table_name,
                            schema: cost_table_schema,
                            merge: None,
                            hidden: false,
                            let_binding: false,
                            internal_view: None,
                            unextractable: false,
                            identity_vals: None,
                            cost: None,
                            term_node: false,
                        });
                    }
                }
                _ => {
                    return Err(ParseError(
                        span,
                        "Expect a datatype declaration".to_string(),
                    ));
                }
            }
        }
        let mut commands = decls;
        commands.extend(cost_table_commands);
        Ok(commands)
    }
}

fn generate_cost_table_commands_from_variants(variants: &[Variant]) -> Vec<Command> {
    variants
        .iter()
        .map(|v| {
            let cost_table_name = get_cost_table_name(&v.name);
            let cost_table_schema = Schema::new(v.types.clone(), "i64".into());

            Command::Function {
                span: v.span.clone(),
                name: cost_table_name,
                schema: cost_table_schema,
                merge: None,
                hidden: false,
                let_binding: false,
                internal_view: None,
                unextractable: false,
                identity_vals: None,
                cost: None,
                term_node: false,
            }
        })
        .collect::<Vec<_>>()
}

fn get_cost_table_name(name: &str) -> String {
    format!("cost_table_{name}")
}

fn map_fallible<T>(
    slice: &[Sexp],
    parser: &mut Parser,
    func: impl Fn(&mut Parser, &Sexp) -> Result<T, ParseError>,
) -> Result<Vec<T>, ParseError> {
    slice
        .iter()
        .map(|sexp| func(parser, sexp))
        .collect::<Result<_, _>>()
}

/// The cost model that handles dynamic costs. Use this cost model if you use the `with-dynamic-cost` / `set-cost`
/// extensions in your egglog program
#[derive(Clone)]
pub struct DynamicCostModel;

impl CostModel<DefaultCost> for DynamicCostModel {
    fn fold(
        &self,
        _head: &str,
        children_cost: &[DefaultCost],
        head_cost: DefaultCost,
    ) -> DefaultCost {
        TreeAdditiveCostModel {}.fold(_head, children_cost, head_cost)
    }

    fn enode_cost(
        &self,
        egraph: &EGraph,
        func: &egglog::Function,
        enode: &Enode<'_>,
    ) -> DefaultCost {
        let name = get_cost_table_name(func.name());
        if egraph.get_function(&name).is_some() {
            egraph
                .read(|state| state.lookup(&name, RawValues(enode.children.to_vec())))
                .expect("dynamic extraction cost table must have the constructor's key schema")
                .map(|c| {
                    let cost = egraph.value_to_base::<i64>(c);
                    assert!(cost >= 0);
                    cost as DefaultCost
                })
                .unwrap_or_else(|| TreeAdditiveCostModel {}.enode_cost(egraph, func, enode))
        } else {
            TreeAdditiveCostModel {}.enode_cost(egraph, func, enode)
        }
    }
}
