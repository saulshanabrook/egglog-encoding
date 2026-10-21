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
//! declaration; unmarked constructors retain their ordinary behavior. Different
//! constructor names imply no disjointness, and subsumed rows still participate
//! in the constraints.
//!
//! The shared `injectivity` ruleset exists on experimental graphs, but its
//! rules run only when scheduled. `(run-schedule (saturate injectivity))`
//! propagates equality through successive constructor layers. The generated
//! equality rules support ordinary execution, term encoding, and proof testing.
//! The separate `known-disequal?` read predicate supports ordinary execution
//! only; its reference and witness-search explanation are in `disequality.rs`.
//!
//! # Encoding explanation
//!
//! The core AST/parser carries the annotation; this extension consumes it
//! before core desugaring. The expansion preserves the original declaration
//! and options with the flag cleared, then adds ordinary rules. Plain egglog
//! rejects an unconsumed `:injective` flag rather than ignoring its semantics.
//!
//! For a marked `F`, every rule joins two existing rows on equal output:
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
//! The lazy hidden function `@injectivity-constructors : String -> Unit`
//! records one constructor name per successful marked declaration. This is
//! O(number of marked constructors) declaration metadata, used by the
//! on-demand disequality search; it stores no derived value pairs. Declaring
//! it with its first write lets term/proof lowering instrument both together.
//! Its rows follow normal cloning and `push`/`pop`, failed declarations do not
//! add markers, and `keep-best` preserves this table while compacting data.

use std::{collections::HashSet, sync::Arc};

use egglog::{
    CommandMacro, EGraph, Error, TypeError, TypeInfo,
    ast::{
        Action, Actions, Command, Expr, Fact, Literal, ParseError, Rule, RuleEvalMode, Schema,
        Span, Subdatatypes,
    },
    span,
    util::{FreshGen, SymbolGen},
};

pub(crate) const MARKED_CONSTRUCTORS: &str = "@injectivity-constructors";

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

impl CommandMacro for LowerInjectivity {
    fn transform(
        &self,
        mut command: Command,
        symbols: &mut SymbolGen,
        types: &TypeInfo,
    ) -> Result<Vec<Command>, Error> {
        // Datatype sorts are not in TypeInfo until this command has been lowered.
        let mut eq_sorts = HashSet::new();
        let mut containers = HashSet::new();
        match &command {
            Command::Datatype { name, .. } => {
                eq_sorts.insert(name.clone());
            }
            Command::Datatypes { datatypes, .. } => {
                for (_, name, datatype) in datatypes {
                    match datatype {
                        Subdatatypes::Variants(_) => {
                            eq_sorts.insert(name.clone());
                        }
                        Subdatatypes::NewSort(..) => {
                            containers.insert(name.clone());
                        }
                    }
                }
            }
            _ => {}
        }

        let mut rules = Vec::new();
        let mut marked = Vec::new();
        match &mut command {
            Command::Constructor {
                span,
                name,
                schema,
                injective,
                ..
            } if *injective => {
                rules.extend(injectivity_rules(
                    span,
                    name,
                    &schema.input,
                    symbols,
                    types,
                    &eq_sorts,
                    &containers,
                )?);
                marked.push((span.clone(), name.clone()));
                *injective = false;
            }
            Command::Datatype { variants, .. } => {
                for variant in variants.iter_mut().filter(|v| v.injective) {
                    rules.extend(injectivity_rules(
                        &variant.span,
                        &variant.name,
                        &variant.types,
                        symbols,
                        types,
                        &eq_sorts,
                        &containers,
                    )?);
                    marked.push((variant.span.clone(), variant.name.clone()));
                    variant.injective = false;
                }
            }
            Command::Datatypes { datatypes, .. } => {
                for (_, _, datatype) in datatypes {
                    if let Subdatatypes::Variants(variants) = datatype {
                        for variant in variants.iter_mut().filter(|v| v.injective) {
                            rules.extend(injectivity_rules(
                                &variant.span,
                                &variant.name,
                                &variant.types,
                                symbols,
                                types,
                                &eq_sorts,
                                &containers,
                            )?);
                            marked.push((variant.span.clone(), variant.name.clone()));
                            variant.injective = false;
                        }
                    }
                }
            }
            _ => {}
        }
        // Validate every marked signature before installing the declaration.
        let mut commands = vec![command];
        // Declare lazily so term/proof encoding instruments the table together
        // with its first write rather than seeing an unencoded startup table.
        if !marked.is_empty() && types.get_func_type(MARKED_CONSTRUCTORS).is_none() {
            commands.push(Command::Function {
                span: span!(),
                name: MARKED_CONSTRUCTORS.into(),
                schema: Schema::new(vec!["String".into()], "Unit".into()),
                merge: None,
                hidden: true,
                let_binding: false,
                internal_view: None,
                unextractable: true,
                identity_vals: None,
                cost: None,
                term_node: false,
            });
        }
        commands.extend(rules);
        // Database metadata follows clone/push/pop and is written only after
        // the declaration and its generated rules have installed successfully.
        commands.extend(marked.into_iter().map(|(span, name)| {
            Command::Action(Action::Set(
                span.clone(),
                MARKED_CONSTRUCTORS.into(),
                vec![Expr::Lit(span.clone(), Literal::String(name))],
                Expr::Lit(span, Literal::Unit),
            ))
        }));
        Ok(commands)
    }
}

/// Build the equal-output join, one combined equality-sort union head, and
/// one independently guarded panic rule per primitive field. Sort validation
/// happens before any declaration or marker is installed in the live graph.
fn injectivity_rules(
    span: &Span,
    name: &str,
    inputs: &[String],
    symbols: &mut SymbolGen,
    types: &TypeInfo,
    eq_sorts: &HashSet<String>,
    containers: &HashSet<String>,
) -> Result<Vec<Command>, Error> {
    let mut left = Vec::new();
    let mut right = Vec::new();
    let mut unions = Vec::new();
    let mut primitive_args = Vec::new();
    for (index, sort_name) in inputs.iter().enumerate() {
        let is_eq = if eq_sorts.contains(sort_name) {
            true
        } else if containers.contains(sort_name) {
            return Err(ParseError(
                span.clone(),
                format!(":injective constructor `{name}` does not support container argument {index} of sort `{sort_name}`"),
            ).into());
        } else {
            let sort = types
                .get_sort_by_name(sort_name)
                .ok_or_else(|| TypeError::UndefinedSort(sort_name.clone(), span.clone()))?;
            if sort.is_container_sort() {
                return Err(ParseError(
                    span.clone(),
                    format!(":injective constructor `{name}` does not support container argument {index} of sort `{sort_name}`"),
                ).into());
            }
            if sort.is_eq_sort() && !types.is_sort_unionable(sort) {
                return Err(TypeError::NonUnionableSort(sort.clone(), span.clone()).into());
            }
            sort.is_eq_sort()
        };
        let lhs = Expr::Var(span.clone(), symbols.fresh("injectivity-left"));
        let rhs = Expr::Var(span.clone(), symbols.fresh("injectivity-right"));
        if is_eq {
            unions.push(Action::Union(span.clone(), lhs.clone(), rhs.clone()));
        } else {
            primitive_args.push((index, lhs.clone(), rhs.clone()));
        }
        left.push(lhs);
        right.push(rhs);
    }
    let body = vec![Fact::Eq(
        span.clone(),
        Expr::Call(span.clone(), name.into(), left),
        Expr::Call(span.clone(), name.into(), right),
    )];
    let mut heads = Vec::new();
    if !unions.is_empty() {
        heads.push((body.clone(), unions));
    }
    for (index, lhs, rhs) in primitive_args {
        let mut guarded_body = body.clone();
        guarded_body.push(Fact::Fact(Expr::Call(
            span.clone(),
            "!=".into(),
            vec![lhs, rhs],
        )));
        heads.push((guarded_body, vec![Action::Panic(
            span.clone(),
            format!("injectivity violation in constructor `{name}`: unequal primitive argument {index}"),
        )]));
    }
    Ok(heads
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
        .collect())
}
