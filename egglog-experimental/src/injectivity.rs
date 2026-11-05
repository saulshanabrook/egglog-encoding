//! Opt-in constructor injectivity and its rules encoding.
//!
//! # Reference
//!
//! `:injective` is a flag on a constructor or a datatype variant, including
//! variants in `datatype*`. It combines with `:cost` and `:unextractable`:
//!
//! ```lisp
//! (datatype Term (Leaf String) (Wrap Term :injective))
//! (constructor Tagged (Term i64) Term :injective :cost 2)
//! (union (Tagged (Leaf "a") 7) (Tagged (Leaf "b") 7))
//! (run-schedule (saturate injectivity))
//! (check (= (Leaf "a") (Leaf "b")))
//! ```
//!
//! When two applications of the **same marked constructor** have equal
//! results, corresponding unionable equality-sort arguments are unioned. A
//! differing primitive argument triggers a panic when the `injectivity` ruleset
//! runs. Container and non-unionable equality-sort arguments are rejected at
//! declaration; unmarked constructors do not decompose equal results. Different
//! constructor names imply no disjointness, and subsumed rows still participate
//! in the constraints.
//!
//! The shared `injectivity` ruleset exists on experimental graphs, but its
//! rules run only when scheduled. `(run-schedule (saturate injectivity))`
//! propagates equality through successive constructor layers. The generated
//! rules support ordinary execution, term encoding, and proof testing. It also
//! propagates structural disequalities, described in `disequality.rs`. Queries
//! read the resulting relations without running the ruleset.
//!
//! # Encoding explanation
//!
//! The core AST/parser carries the annotation; this extension consumes it
//! before core desugaring. The expansion preserves the original declaration
//! and options with the flag cleared, then adds ordinary rules. Plain egglog
//! rejects an unconsumed `:injective` flag rather than ignoring its semantics.
//!
//! For a marked `F`, the equality rules join two existing rows on equal output:
//!
//! ```text
//! F(a_0, ..., a_n) = F(b_0, ..., b_n)
//! ```
//!
//! If equality-sort fields exist, one rule unions them all. Each primitive
//! field gets its own rule with an additional native `(!= a_i b_i)` premise
//! and a panic action. Thus primitive contradictions do not require a primitive
//! disequality table. These joins include subsumed rows, and generated rule
//! names are fresh so a declaration reinstated after `pop` has a distinct proof
//! identity. Nullary marked constructors need no equality rule.
//!
//! Additional rules for marked constructors materialize unequal existing outputs
//! from any unequal field. Native primitive differences seed those pairs;
//! equality-sort fields use per-sort Ne relations. For every ordinary constructor,
//! unequal outputs yield an unequal unionable equality-sort field when all other
//! fields agree. This follows from congruence without requiring injectivity.
//! Other fields, including containers, serve only as equality guards on unmarked
//! constructors. Relations are installed only for sorts needed by these rules,
//! including mutually recursive datatype fields, without storing constructor
//! metadata or searching the graph at query time.

use std::{
    collections::{BTreeMap, HashSet},
    sync::Arc,
};

use egglog::{
    CommandMacro, EGraph, Error, TypeError, TypeInfo,
    ast::{
        Action, Actions, Command, Expr, Fact, FunctionRole, ParseError, Rule, RuleEvalMode, Schema,
        Span, Subdatatypes,
    },
    span,
    util::{FreshGen, SymbolGen},
};

pub(crate) fn add_injectivity_support(egraph: &mut EGraph) {
    // Install once, outside user push/pop scopes, even if no constructor is marked.
    egraph
        .run_program(vec![Command::AddRuleset(span!(), "injectivity".into())])
        .unwrap();
    egraph
        .command_macros_mut()
        .register(Arc::new(LowerInjectivity));
}

struct LowerInjectivity;

#[derive(Default)]
struct DatatypeSorts {
    equality: HashSet<String>,
    containers: HashSet<String>,
}

impl CommandMacro for LowerInjectivity {
    fn preserves_closed_constructor_action(&self, _expression_head: Option<&str>) -> bool {
        true
    }

    fn transform(
        &self,
        mut command: Command,
        symbols: &mut SymbolGen,
        types: &TypeInfo,
    ) -> Result<Vec<Command>, Error> {
        // Datatype sorts are not in TypeInfo until this command has been lowered.
        let mut datatype_sorts = DatatypeSorts::default();
        match &command {
            Command::Datatype { name, .. } => {
                datatype_sorts.equality.insert(name.clone());
            }
            Command::Datatypes { datatypes, .. } => {
                for (_, name, datatype) in datatypes {
                    match datatype {
                        Subdatatypes::Variants(_) => {
                            datatype_sorts.equality.insert(name.clone());
                        }
                        Subdatatypes::NewSort(..) => {
                            datatype_sorts.containers.insert(name.clone());
                        }
                    }
                }
            }
            _ => {}
        }

        let mut rules = Vec::new();
        let mut disequality_sorts = BTreeMap::new();
        match &mut command {
            Command::Constructor {
                span,
                name,
                schema,
                injective,
                role,
                ..
            } if *injective || *role == FunctionRole::Ordinary => {
                let (generated, sorts) = constructor_rules(
                    span,
                    name,
                    schema,
                    *injective,
                    symbols,
                    types,
                    &datatype_sorts,
                )?;
                rules.extend(generated);
                disequality_sorts.extend(sorts);
                *injective = false;
            }
            Command::Datatype { name, variants, .. } => {
                for variant in variants {
                    let (generated, sorts) = constructor_rules(
                        &variant.span,
                        &variant.name,
                        &Schema::new(variant.types.clone(), name.clone()),
                        variant.injective,
                        symbols,
                        types,
                        &datatype_sorts,
                    )?;
                    rules.extend(generated);
                    disequality_sorts.extend(sorts);
                    variant.injective = false;
                }
            }
            Command::Datatypes { datatypes, .. } => {
                for (_, sort, datatype) in datatypes {
                    if let Subdatatypes::Variants(variants) = datatype {
                        for variant in variants {
                            let (generated, sorts) = constructor_rules(
                                &variant.span,
                                &variant.name,
                                &Schema::new(variant.types.clone(), sort.clone()),
                                variant.injective,
                                symbols,
                                types,
                                &datatype_sorts,
                            )?;
                            rules.extend(generated);
                            disequality_sorts.extend(sorts);
                            variant.injective = false;
                        }
                    }
                }
            }
            _ => {}
        }
        // Validate every marked signature before installing the declaration.
        let mut commands = vec![command];
        commands.extend(crate::disequality::support_commands(
            disequality_sorts,
            None,
            symbols,
            types,
        ));
        commands.extend(rules);
        Ok(commands)
    }
}

/// Build downward disequality joins for ordinary constructors, plus equality
/// decomposition and upward disequality joins for marked constructors. Validate
/// marked signatures before installation, including newly declared datatype sorts.
fn constructor_rules(
    span: &Span,
    name: &str,
    schema: &Schema,
    injective: bool,
    symbols: &mut SymbolGen,
    types: &TypeInfo,
    datatype_sorts: &DatatypeSorts,
) -> Result<(Vec<Command>, BTreeMap<String, Span>), Error> {
    let inputs = &schema.input;
    let output = schema.output();
    let mut disequality_sorts = BTreeMap::new();
    let mut eq_args = Vec::new();
    let output_unionable = datatype_sorts.equality.contains(output)
        || types
            .get_sort_by_name(output)
            .is_some_and(|sort| types.is_sort_unionable(sort));
    for (index, sort_name) in inputs.iter().enumerate() {
        let is_eq = if datatype_sorts.equality.contains(sort_name) {
            true
        } else if datatype_sorts.containers.contains(sort_name) {
            if injective {
                return Err(ParseError(
                    span.clone(),
                    format!(":injective constructor `{name}` does not support container argument {index} of sort `{sort_name}`"),
                ).into());
            }
            false
        } else {
            let sort = types
                .get_sort_by_name(sort_name)
                .ok_or_else(|| TypeError::UndefinedSort(sort_name.clone(), span.clone()))?;
            if injective && sort.is_container_sort() {
                return Err(ParseError(
                    span.clone(),
                    format!(":injective constructor `{name}` does not support container argument {index} of sort `{sort_name}`"),
                ).into());
            }
            if injective && sort.is_eq_sort() && !types.is_sort_unionable(sort) {
                return Err(TypeError::NonUnionableSort(sort.clone(), span.clone()).into());
            }
            types.is_sort_unionable(sort) && !sort.is_container_sort()
        };
        if is_eq {
            eq_args.push(index);
        }
    }
    if !injective && (!output_unionable || eq_args.is_empty()) {
        return Ok((Vec::new(), disequality_sorts));
    }
    let left: Vec<_> = inputs
        .iter()
        .map(|_| Expr::Var(span.clone(), symbols.fresh("injectivity-left")))
        .collect();
    let right: Vec<_> = inputs
        .iter()
        .map(|_| Expr::Var(span.clone(), symbols.fresh("injectivity-right")))
        .collect();
    let body = vec![Fact::Eq(
        span.clone(),
        Expr::Call(span.clone(), name.into(), left.clone()),
        Expr::Call(span.clone(), name.into(), right.clone()),
    )];
    let mut heads = Vec::new();
    if injective {
        if !eq_args.is_empty() {
            let unions = eq_args
                .iter()
                .map(|&index| {
                    Action::Union(span.clone(), left[index].clone(), right[index].clone())
                })
                .collect();
            heads.push((body.clone(), unions));
        }
        for index in (0..inputs.len()).filter(|index| !eq_args.contains(index)) {
            let mut guarded_body = body.clone();
            guarded_body.push(Fact::Fact(Expr::Call(
                span.clone(),
                "!=".into(),
                vec![left[index].clone(), right[index].clone()],
            )));
            heads.push((guarded_body, vec![Action::Panic(
                span.clone(),
                format!("injectivity violation in constructor `{name}`: unequal primitive argument {index}"),
            )]));
        }
    }
    if !output_unionable || inputs.is_empty() {
        return Ok((
            rules_from_heads(span, name, heads, symbols),
            disequality_sorts,
        ));
    }
    disequality_sorts.insert(output.clone(), span.clone());
    for &index in &eq_args {
        disequality_sorts.insert(inputs[index].clone(), span.clone());
    }
    let lhs = Expr::Var(span.clone(), symbols.fresh("injectivity-output-left"));
    let rhs = Expr::Var(span.clone(), symbols.fresh("injectivity-output-right"));
    let rows = vec![
        Fact::Eq(
            span.clone(),
            lhs.clone(),
            Expr::Call(span.clone(), name.into(), left.clone()),
        ),
        Fact::Eq(
            span.clone(),
            rhs.clone(),
            Expr::Call(span.clone(), name.into(), right.clone()),
        ),
    ];
    let output_ne = Expr::Call(
        span.clone(),
        format!("@disequality-ne-{output}"),
        vec![lhs.clone(), rhs.clone()],
    );
    // Any unequal field proves unequal existing outputs. Primitive differences
    // seed output disequalities without allocating primitive Ne relations.
    if injective {
        for (index, sort) in inputs.iter().enumerate() {
            let mut body = rows.clone();
            body.push(Fact::Fact(Expr::Call(
                span.clone(),
                if eq_args.contains(&index) {
                    format!("@disequality-ne-{sort}")
                } else {
                    "!=".into()
                },
                vec![left[index].clone(), right[index].clone()],
            )));
            heads.push((body, vec![Action::Expr(span.clone(), output_ne.clone())]));
        }
    }
    // An unequal result identifies a field only when every other field agrees.
    // Reusing those variables guards both primitive and equality-sort fields.
    for index in eq_args {
        let mut matching = left.clone();
        matching[index] = right[index].clone();
        let body = vec![
            Fact::Eq(
                span.clone(),
                lhs.clone(),
                Expr::Call(span.clone(), name.into(), left.clone()),
            ),
            Fact::Eq(
                span.clone(),
                rhs.clone(),
                Expr::Call(span.clone(), name.into(), matching),
            ),
            Fact::Fact(output_ne.clone()),
        ];
        heads.push((
            body,
            vec![Action::Expr(
                span.clone(),
                Expr::Call(
                    span.clone(),
                    format!("@disequality-ne-{}", inputs[index]),
                    vec![left[index].clone(), right[index].clone()],
                ),
            )],
        ));
    }
    Ok((
        rules_from_heads(span, name, heads, symbols),
        disequality_sorts,
    ))
}

/// Give each generated join a fresh proof identity and include subsumed rows.
fn rules_from_heads(
    span: &Span,
    name: &str,
    heads: Vec<(Vec<Fact>, Vec<Action>)>,
    symbols: &mut SymbolGen,
) -> Vec<Command> {
    heads
        .into_iter()
        .map(|(body, head)| Command::Rule {
            rule: Rule {
                span: span.clone(),
                // Proof history retains rules after pop, so redeclarations need fresh names.
                name: symbols.fresh(&format!("injectivity-{name}")),
                ruleset: "injectivity".into(),
                body,
                head: Actions::new(head),
                eval_mode: RuleEvalMode::Seminaive,
                no_decomp: false,
                include_subsumed: true,
            },
        })
        .collect()
}
