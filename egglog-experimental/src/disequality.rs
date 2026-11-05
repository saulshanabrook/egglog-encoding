//! Relation-based disequality assertions, propagation, and read-only queries.
//!
//! # Reference
//!
//! ## Assertions and contradiction checks
//!
//! `(disequal left right)` is an **action**, usable at top level or in a rule
//! head. Both operands must have the same unionable equality sort. Primitive
//! values use native `!=`; mismatched sorts, non-unionable sorts, primitive
//! operands, and incorrect arity are errors. `disequal` is not a query predicate.
//!
//! Assertions use relation-based NEE, which supports ordinary execution,
//! term encoding, and proof testing for commands supported by those modes.
//!
//! `(check-contradiction)` saturates the private `@disequality` ruleset and
//! succeeds **if a contradiction is present**; it fails otherwise. It does not
//! run `injectivity`. Assertions record constraints without preventing later
//! unions, so an inconsistency can become visible after congruence rebuilding:
//!
//! ```lisp
//! (datatype Term (A) (B))
//! (disequal (A) (B))
//! (fail (check-contradiction))
//! (union (A) (B))
//! (check-contradiction)
//! ```
//!
//! ## Queries and explicit propagation
//!
//! `(known-disequal? left right)` accepts two values of the same unionable
//! equality sort. In query facts it returns `Unit` for a stored disequality and
//! is undefined otherwise. Unknown supplies no equality conclusion. Use it in
//! checks, rule bodies, rewrite conditions, and run-until conditions. Action
//! expressions are rejected because ordinary relation calls there insert rows.
//! Direct primitive comparisons use native `!=`.
//!
//! ```lisp
//! (datatype Expr (Num i64 :injective))
//! (Num 1) (Num 2)
//! (fail (check (known-disequal? (Num 1) (Num 2))))
//! (run-schedule (saturate injectivity))
//! (check (known-disequal? (Num 1) (Num 2)))
//! ```
//!
//! The `injectivity` ruleset materializes structural disequalities and symmetry
//! only when scheduled. For the same marked constructor, one unequal field
//! implies unequal existing outputs; primitive differences can seed this rule.
//! For any ordinary constructor, unequal outputs imply an unequal unionable
//! equality-sort field when every other corresponding field is equal. This
//! includes unmarked unary constructors and follows from congruence. There is no
//! inequality from missing equality or different constructor names. These rules
//! include subsumed rows and support ordinary, term, and proof modes.
//!
//! This local propagation is incomplete for disequalities implied by congruence.
//! For example, unequal `Pair(a, a)` and `Pair(b, b)` imply unequal `a` and `b`,
//! but neither per-field rule fires until the other field is already equal.
//! A failed query therefore does not show that the two values could be equal.
//!
//! # Encoding explanation
//!
//! Parsing represents an assertion with a private action placeholder. A command
//! pass checks its operands using union's type constraints and replaces it with
//! a per-sort relation insertion. The same pass uses a type-only query marker
//! to infer query operands, then emits ordinary relation facts. Nested query
//! expressions retain `Unit` by hoisting their relation fact. No marker reaches
//! execution or proof encoding, and rule dependencies are visible to ordinary
//! seminaive evaluation.
//!
//! Each needed equality sort `S` has `Ne_S : (S, S)`, named
//! `@disequality-ne-S`. Constructor declarations install relations for the sorts
//! needed by their propagation rules; assertion and query uses install other sorts
//! lazily, including a valid empty relation for query-only use. Scoped relations
//! and rules follow `push`/`pop`; fresh rule names preserve proof identities.
//! Rebuilding canonicalizes relation operands after unions.
//!
//! The `injectivity` ruleset contains symmetry and the structural joins. Those
//! joins read existing constructor rows and insert only disequality pairs: they
//! never create constructor applications. Materializing the closure can store
//! quadratically many pairs, including primitive-seeded output pairs.
//!
//! Each sort also gets a rule in the separate private `@disequality` ruleset:
//!
//! ```text
//! Ne_S(x, x) -> @disequality-contradiction()
//! ```
//!
//! `(check-contradiction)` saturates only this private self-edge ruleset and
//! checks the nullary contradiction relation. It does not run structural
//! propagation. A stored self-disequality remains queryable, and assertions
//! themselves do not union user values.

use std::{collections::BTreeMap, sync::Arc};

use egglog::{
    ArcSort, AtomTerm, CommandMacro, Context, EGraph, Error, Primitive, PurePrim, PureState,
    TypeError, TypeInfo, Value,
    ast::{
        Action, Actions, Command, Expr, Fact, FunctionDecl, Literal, Macro, ParseError, Parser,
        ResolvedExpr, ResolvedFact, Rule, RuleEvalMode, RunConfig, Schedule, Sexp, Span,
    },
    constraint::{Constraint, TypeConstraint},
    util::{FreshGen, SymbolGen},
};

const PLACEHOLDER: &str = "@disequal";
const RULESET: &str = "@disequality";
const CONTRADICTION: &str = "@disequality-contradiction";

/// Install syntax and its lowering pass before enabling term/proof encoding.
/// Call once on a fresh graph.
pub(crate) fn add_disequality_support(egraph: &mut EGraph) {
    egraph.add_pure_primitive(KnownDisequal, None);
    egraph.parser.add_action_macro(Arc::new(Disequal));
    egraph
        .parser
        .add_command_macro(Arc::new(CheckContradiction));
    egraph
        .command_macros_mut()
        .register(Arc::new(LowerDisequality));
}

/// Type-inference marker, always eliminated by the command pass before execution.
/// Its signature enforces same-unionable-equality-sort query operands, including
/// inference performed by FreshMacro before ordinary relation calls are emitted.
#[derive(Clone)]
struct KnownDisequal;

impl Primitive for KnownDisequal {
    fn name(&self) -> &str {
        "known-disequal?"
    }

    fn get_type_constraints(&self, span: &Span) -> Box<dyn TypeConstraint> {
        Box::new(KnownDisequalConstraint(span.clone()))
    }
}

struct KnownDisequalConstraint(Span);

impl TypeConstraint for KnownDisequalConstraint {
    fn get(
        &self,
        arguments: &[AtomTerm],
        types: &TypeInfo,
    ) -> Vec<Box<dyn Constraint<AtomTerm, ArcSort>>> {
        let unit = types.get_sort_by_name("Unit").unwrap();
        let mut sorts = types.get_arcsorts_by(|sort| types.is_sort_unionable(sort));
        sorts.sort_by_key(|sort| sort.name().to_owned());
        crate::type_constraints::exact_signatures(
            "known-disequal?",
            &self.0,
            arguments,
            3,
            sorts
                .into_iter()
                .map(|sort| vec![sort.clone(), sort, unit.clone()]),
        )
    }
}

impl PurePrim for KnownDisequal {
    fn apply<'a, 'db>(&self, _state: PureState<'a, 'db>, _args: &[Value]) -> Option<Value> {
        // Direct Rust expression evaluation and indirect function targets can
        // bypass command lowering. Fail as an ordinary undefined primitive.
        None
    }
}

/// Install the ordinary relation and its rules once per scoped sort. Structural
/// rules and symmetry run explicitly in `injectivity`; contradiction checks only
/// saturate the private self-edge ruleset.
pub(crate) fn support_commands(
    sorts: BTreeMap<String, Span>,
    support_span: Option<Span>,
    symbols: &mut SymbolGen,
    types: &TypeInfo,
) -> Vec<Command> {
    let Some(span) = sorts.values().next().cloned().or(support_span) else {
        return Vec::new();
    };
    let mut commands = Vec::new();
    if types.get_func_type(CONTRADICTION).is_none() {
        commands.push(Command::AddRuleset(span.clone(), RULESET.into()));
        commands.push(Command::Relation {
            span,
            name: CONTRADICTION.into(),
            inputs: vec![],
        });
    }
    for (sort, span) in sorts {
        let name = format!("@disequality-ne-{sort}");
        if types.get_func_type(&name).is_some() {
            continue;
        }
        commands.push(Command::Relation {
            span: span.clone(),
            name: name.clone(),
            inputs: vec![sort.clone(), sort.clone()],
        });
        let x = Expr::Var(span.clone(), "x".into());
        let y = Expr::Var(span.clone(), "y".into());
        for (suffix, ruleset, body, head, include_subsumed) in [
            (
                "self",
                RULESET,
                vec![Fact::Fact(Expr::Call(
                    span.clone(),
                    name.clone(),
                    vec![x.clone(), x.clone()],
                ))],
                Expr::Call(span.clone(), CONTRADICTION.into(), vec![]),
                false,
            ),
            (
                "symmetric",
                "injectivity",
                vec![Fact::Fact(Expr::Call(
                    span.clone(),
                    name.clone(),
                    vec![x.clone(), y.clone()],
                ))],
                Expr::Call(span.clone(), name, vec![y, x]),
                true,
            ),
        ] {
            commands.push(Command::Rule {
                rule: Rule {
                    span: span.clone(),
                    name: symbols.fresh(&format!("@disequality-ne-{suffix}-{sort}")),
                    ruleset: ruleset.into(),
                    body,
                    head: Actions::singleton(Action::Expr(span.clone(), head)),
                    eval_mode: RuleEvalMode::Seminaive,
                    no_decomp: false,
                    include_subsumed,
                },
            });
        }
    }
    commands
}

struct Disequal;

impl Macro<Vec<Action>> for Disequal {
    fn name(&self) -> &str {
        "disequal"
    }

    fn parse(
        &self,
        args: &[Sexp],
        span: Span,
        parser: &mut Parser,
    ) -> Result<Vec<Action>, ParseError> {
        let [lhs, rhs] = args else {
            return Err(ParseError(span, "usage: (disequal <expr> <expr>)".into()));
        };
        Ok(vec![Action::Expr(
            span.clone(),
            Expr::Call(
                span,
                PLACEHOLDER.into(),
                vec![parser.parse_expr(lhs)?, parser.parse_expr(rhs)?],
            ),
        )])
    }
}

struct CheckContradiction;

impl Macro<Vec<Command>> for CheckContradiction {
    fn name(&self) -> &str {
        "check-contradiction"
    }

    fn parse(
        &self,
        args: &[Sexp],
        span: Span,
        _parser: &mut Parser,
    ) -> Result<Vec<Command>, ParseError> {
        if !args.is_empty() {
            return Err(ParseError(span, "usage: (check-contradiction)".into()));
        }
        Ok(vec![
            Command::RunSchedule(Schedule::Saturate(
                span.clone(),
                Box::new(Schedule::Run(
                    span.clone(),
                    RunConfig {
                        ruleset: RULESET.into(),
                        until: None,
                    },
                )),
            )),
            Command::Check(
                span.clone(),
                vec![Fact::Fact(Expr::Call(span, CONTRADICTION.into(), vec![]))],
            ),
        ])
    }
}

struct LowerDisequality;

impl CommandMacro for LowerDisequality {
    fn preserves_closed_constructor_action(&self, expression_head: Option<&str>) -> bool {
        !matches!(expression_head, Some(PLACEHOLDER | "known-disequal?"))
    }

    fn transform(
        &self,
        command: Command,
        symbols: &mut SymbolGen,
        types: &TypeInfo,
    ) -> Result<Vec<Command>, Error> {
        let expanded = crate::fresh_macro::FreshMacro::new().transform(command, symbols, types)?;
        let expanded_fresh = expanded.len() > 1;
        let mut local_types = std::borrow::Cow::Borrowed(types);
        let mut result = Vec::new();
        for command in expanded {
            // FreshMacro emits a constructor before its rule. Make that signature
            // visible to this pass without installing anything in the live graph.
            if expanded_fresh
                && let Command::Constructor {
                    span,
                    name,
                    schema,
                    cost,
                    unextractable,
                    injective: _,
                    hidden,
                    role,
                } = &command
            {
                let mut declaration = FunctionDecl::constructor(
                    span.clone(),
                    name.clone(),
                    schema.clone(),
                    *cost,
                    *unextractable,
                    *hidden,
                );
                declaration.role = *role;
                local_types
                    .to_mut()
                    .typecheck_function(symbols, &declaration)?;
                result.push(command);
            } else {
                result.extend(Self::lower(command, symbols, &local_types)?);
            }
        }
        Ok(result)
    }
}

impl LowerDisequality {
    fn lower(
        mut command: Command,
        symbols: &mut SymbolGen,
        types: &TypeInfo,
    ) -> Result<Vec<Command>, Error> {
        let mut sorts = BTreeMap::new();
        let mut support_span = None;
        Self::lower_command(&mut command, symbols, types, &mut sorts, &mut support_span)?;
        let mut commands = support_commands(sorts, support_span, symbols, types);
        commands.push(command);
        Ok(commands)
    }

    fn lower_command(
        command: &mut Command,
        symbols: &mut SymbolGen,
        types: &TypeInfo,
        sorts: &mut BTreeMap<String, Span>,
        support_span: &mut Option<Span>,
    ) -> Result<(), Error> {
        match command {
            Command::Rule { rule }
                if contains_disequal(&rule.head) || contains_query(&rule.body) =>
            {
                // Union has the same operand constraints as disequal. Use it only
                // for inference, never execution, so head uses can constrain the body.
                let mut probe = rule.clone();
                probe.head = union_probe(&rule.head);
                let resolved = types.typecheck_rule(symbols, &probe, false)?;
                rule.body = lower_typed_facts(resolved.body, sorts);
                lower_typed_actions(&mut rule.head, resolved.head, sorts);
            }
            Command::Action(action) if matches!(&*action, Action::Expr(_, Expr::Call(_, head, _)) if head == PLACEHOLDER) =>
            {
                let Action::Expr(span, Expr::Call(_, _, args)) = action else {
                    unreachable!()
                };
                let [lhs, rhs] = args.as_slice() else {
                    unreachable!("parser checks disequal arity")
                };
                let left = operand_sort(types, symbols, lhs)?;
                let right = operand_sort(types, symbols, rhs)?;
                if left.name() != right.name() {
                    return Err(TypeError::Mismatch {
                        expr: rhs.clone(),
                        expected: left,
                        actual: right,
                    }
                    .into());
                }
                if !left.is_eq_sort() {
                    return Err(TypeError::NonEqsortUnion(left, span.clone()).into());
                }
                if !types.is_sort_unionable(&left) {
                    return Err(TypeError::NonUnionableSort(left, span.clone()).into());
                }
                sorts.insert(left.name().into(), span.clone());
                *action = Action::Expr(
                    span.clone(),
                    Expr::Call(
                        span.clone(),
                        format!("@disequality-ne-{}", left.name()),
                        args.to_vec(),
                    ),
                );
            }
            Command::LetBegin(span, _, actions) if matches!(actions.0.last(), Some(Action::Expr(_, Expr::Call(_, head, _))) if head == PLACEHOLDER) =>
            {
                return Err(Error::DesugarError(
                    span.clone(),
                    "let-begin must end with a value, not disequal".into(),
                ));
            }
            Command::Actions(actions) | Command::LetBegin(_, _, actions)
                if contains_disequal(actions) =>
            {
                let resolved = types.typecheck_standalone_actions(
                    symbols,
                    &union_probe(actions),
                    &Default::default(),
                    Context::Full,
                )?;
                lower_typed_actions(actions, resolved, sorts);
            }
            Command::Check(_, facts) | Command::Prove(_, facts) if contains_query(facts) => {
                *facts = lower_typed_facts(types.typecheck_facts(symbols, facts)?, sorts);
            }
            Command::Rewrite(_, rewrite, _) | Command::BiRewrite(_, rewrite)
                if contains_query(&rewrite.conditions) =>
            {
                let value = Expr::Var(rewrite.span.clone(), symbols.fresh("disequality-rewrite"));
                let mut body = vec![Fact::Eq(
                    rewrite.span.clone(),
                    value.clone(),
                    rewrite.lhs.clone(),
                )];
                body.extend(rewrite.conditions.clone());
                let probe = Rule {
                    span: rewrite.span.clone(),
                    name: String::new(),
                    ruleset: String::new(),
                    body,
                    head: Actions::singleton(Action::Union(
                        rewrite.span.clone(),
                        value,
                        rewrite.rhs.clone(),
                    )),
                    eval_mode: RuleEvalMode::Seminaive,
                    no_decomp: false,
                    include_subsumed: false,
                };
                let resolved = types.typecheck_rule(symbols, &probe, false)?;
                rewrite.conditions =
                    lower_typed_facts(resolved.body.into_iter().skip(1).collect(), sorts);
            }
            Command::Fail(_, commands) => {
                for command in commands {
                    Self::lower_command(command, symbols, types, sorts, support_span)?;
                }
            }
            Command::RunSchedule(schedule) => {
                lower_schedule(schedule, symbols, types, sorts, support_span)?;
            }
            _ => {}
        }
        // Relation calls in actions insert rows. Never turn a read predicate
        // into an insertion: every remaining occurrence is outside query facts.
        let mut unsupported = None;
        let mut inspect = |expr: Expr| {
            if let Expr::Call(span, head, args) = &expr
                && (head == "known-disequal?"
                    || head == "unstable-fn"
                        && matches!(args.first(), Some(Expr::Lit(_, Literal::String(name))) if name == "known-disequal?"))
            {
                unsupported = Some(span.clone());
            }
            expr
        };
        if let Command::UserDefined(_, name, args) = command {
            for arg in args {
                // Extended schedules lower their until expressions through
                // Command::Check at execution time. Other expressions, such as
                // eval actions or scheduler-builder arguments, must reject it.
                let expression = if name == "run-schedule" {
                    mask_schedule_queries(arg.clone())
                } else {
                    arg.clone()
                };
                let _ = expression.visit_exprs(&mut inspect);
            }
        } else {
            let _ = command.clone().visit_exprs(&mut inspect);
        }
        if let Some(span) = unsupported {
            return Err(ParseError(span, "known-disequal? is only supported in query facts (checks, rule bodies, rewrite conditions, or run-until conditions)".into()).into());
        }
        Ok(())
    }
}

/// Exclude only extended scheduler conditions from the action-position scan.
/// Those conditions are passed to Command::Check by the interpreter; schedule
/// eval steps and forwarded command arguments still pass through the scan.
fn mask_schedule_queries(expr: Expr) -> Expr {
    let Expr::Call(span, name, mut args) = expr else {
        return expr;
    };
    match name.as_str() {
        "run" | "run-with" => {
            let rest = if name == "run-with" {
                match args.as_slice() {
                    [Expr::Var(..), rest @ ..] => rest,
                    _ => &[],
                }
            } else {
                &args
            };
            let has_condition = match rest {
                [Expr::Var(_, until), _] | [Expr::Var(_, _), Expr::Var(_, until), _] => {
                    until == ":until"
                }
                _ => false,
            };
            if has_condition {
                let condition = args.last_mut().unwrap();
                *condition = Expr::Lit(condition.span(), Literal::Unit);
            }
        }
        "seq" | "saturate" | "repeat" | "run-schedule" => {
            args = args.into_iter().map(mask_schedule_queries).collect();
        }
        _ => {}
    }
    Expr::Call(span, name, args)
}

/// Infer each query as a whole, then expose its per-sort relation dependency.
/// Reconstructing from typed expressions preserves local/global variable names
/// while selecting the relation from the already-checked operand sort.
fn lower_typed_facts(facts: Vec<ResolvedFact>, sorts: &mut BTreeMap<String, Span>) -> Vec<Fact> {
    let mut lowered = Vec::new();
    for fact in facts {
        let fact = match fact {
            ResolvedFact::Eq(span, lhs, rhs) => Fact::Eq(
                span,
                lower_typed_expr(lhs, sorts, &mut lowered),
                lower_typed_expr(rhs, sorts, &mut lowered),
            ),
            ResolvedFact::Fact(expr) => Fact::Fact(lower_typed_expr(expr, sorts, &mut lowered)),
        };
        // A root known-disequal? call becomes a relation atom with no extra
        // tautology; nested calls retain their original Unit expression type.
        if !matches!(&fact, Fact::Fact(Expr::Lit(_, Literal::Unit))) {
            lowered.push(fact);
        }
    }
    lowered
}

fn lower_typed_expr(
    expr: ResolvedExpr,
    sorts: &mut BTreeMap<String, Span>,
    facts: &mut Vec<Fact>,
) -> Expr {
    match expr {
        ResolvedExpr::Var(span, var) => Expr::Var(span, var.name),
        ResolvedExpr::Lit(span, literal) => Expr::Lit(span, literal),
        ResolvedExpr::Call(span, call, args) => {
            let args = args
                .into_iter()
                .map(|arg| lower_typed_expr(arg, sorts, facts))
                .collect();
            if call.name() == "known-disequal?" {
                let egglog::ResolvedCall::Primitive(primitive) = call else {
                    unreachable!("known-disequal? is an inference-only primitive")
                };
                let sort = primitive.input()[0].name();
                sorts.insert(sort.into(), span.clone());
                facts.push(Fact::Fact(Expr::Call(
                    span.clone(),
                    format!("@disequality-ne-{sort}"),
                    args,
                )));
                Expr::Lit(span, Literal::Unit)
            } else {
                Expr::Call(span, call.name().into(), args)
            }
        }
    }
}

fn contains_query(facts: &[Fact]) -> bool {
    facts.iter().any(|fact| {
        let mut found = false;
        let _ = fact.clone().visit_exprs(&mut |expr| {
            found |= matches!(&expr, Expr::Call(_, name, _) if name == "known-disequal?");
            expr
        });
        found
    })
}

fn lower_schedule(
    schedule: &mut Schedule,
    symbols: &mut SymbolGen,
    types: &TypeInfo,
    sorts: &mut BTreeMap<String, Span>,
    support_span: &mut Option<Span>,
) -> Result<(), Error> {
    match schedule {
        Schedule::Saturate(span, inner) => {
            if matches!(inner.as_ref(), Schedule::Run(_, config) if config.ruleset == RULESET) {
                *support_span = Some(span.clone());
            }
            lower_schedule(inner, symbols, types, sorts, support_span)?;
        }
        Schedule::Repeat(_, _, inner) => {
            lower_schedule(inner, symbols, types, sorts, support_span)?
        }
        Schedule::Sequence(_, schedules) => {
            for inner in schedules {
                lower_schedule(inner, symbols, types, sorts, support_span)?;
            }
        }
        Schedule::Run(_, config) => {
            if let Some(facts) = &mut config.until
                && contains_query(facts)
            {
                *facts = lower_typed_facts(types.typecheck_facts(symbols, facts)?, sorts);
            }
        }
    }
    Ok(())
}

/// Rewrite assertions with the operand sorts already checked by the union probe.
fn lower_typed_actions(
    actions: &mut Actions,
    resolved: egglog::ast::GenericActions<egglog::ResolvedCall, egglog::ResolvedVar>,
    sorts: &mut BTreeMap<String, Span>,
) {
    for (action, typed) in actions.0.iter_mut().zip(resolved.0) {
        if let Action::Expr(span, Expr::Call(_, head, args)) = action
            && head == PLACEHOLDER
        {
            let egglog::ast::GenericAction::Union(_, lhs, _) = typed else {
                unreachable!()
            };
            let sort = match lhs {
                egglog::ast::ResolvedExpr::Var(_, var) => var.sort,
                egglog::ast::ResolvedExpr::Call(_, call, _) => call.output().clone(),
                egglog::ast::ResolvedExpr::Lit(_, literal) => egglog::sort::literal_sort(&literal),
            };
            sorts.insert(sort.name().into(), span.clone());
            *action = Action::Expr(
                span.clone(),
                Expr::Call(
                    span.clone(),
                    format!("@disequality-ne-{}", sort.name()),
                    args.to_vec(),
                ),
            );
        }
    }
}

/// Use union's operand constraints without ever executing the inferred action.
fn union_probe(actions: &Actions) -> Actions {
    actions.clone().visit_actions(&mut |action| match action {
        Action::Expr(span, Expr::Call(_, head, mut args)) if head == PLACEHOLDER => {
            Action::Union(span, args.remove(0), args.remove(0))
        }
        action => action,
    })
}

/// Declared calls already determine their result sort. Avoid solving the full
/// expression twice; the emitted action still validates all argument types.
fn operand_sort(
    types: &TypeInfo,
    symbols: &mut SymbolGen,
    expr: &Expr,
) -> Result<ArcSort, TypeError> {
    let declared = match expr {
        Expr::Var(_, name) => types.get_global_sort(name),
        Expr::Call(_, head, _) if !types.is_primitive(head) => {
            types.get_func_type(head).map(|f| f.output())
        }
        _ => None,
    };
    match declared {
        Some(sort) => Ok(sort.clone()),
        None => types.infer_expr_sort(symbols, expr, &[], Context::Full),
    }
}

fn contains_disequal(actions: &Actions) -> bool {
    actions
        .0
        .iter()
        .any(|a| matches!(a, Action::Expr(_, Expr::Call(_, head, _)) if head == PLACEHOLDER))
}
