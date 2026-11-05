//! Relation-based disequality assertions and read-only structural witness queries.
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
//! ## On-demand query
//!
//! `(known-disequal? left right)` accepts two values of the same unionable
//! equality sort. It returns `Unit` when a finite disequality witness is found
//! and is undefined otherwise. The test is sound but incomplete: undefined
//! denotes unknown and supplies no equality conclusion. It can be used in
//! `check`, `fail (check ...)`, and rule bodies; such rules use `:naive` because
//! the predicate reads tables beyond the body's explicit atoms. Direct primitive
//! operands still use `!=`.
//!
//! ```lisp
//! (datatype Expr (Num i64 :injective))
//! (Num 1) (Num 2)
//! (check (known-disequal? (Num 1) (Num 2)))
//! ```
//!
//! The query combines stored disequalities with structural implications for
//! `:injective` constructors, without saturation. A differing corresponding
//! argument can establish unequal results at any arity. Unequal results can
//! establish unequal arguments only for a marked unary constructor with an
//! equality-sort argument. There is no reverse rule for multiple arguments,
//! inequality from missing equality, or disjointness between constructor names.
//! Subsumed constructor rows participate. The query has no validator and
//! currently supports ordinary execution only, without term/proof encoding.
//!
//! # Encoding explanation
//!
//! ## Lazy ordinary-language support
//!
//! Parsing first represents an assertion with a private placeholder action.
//! The command pass enforces the same operand constraints as union and
//! replaces it with a per-sort relation insertion. The first assertion use or
//! contradiction check installs private support lazily; per-sort tables are
//! added as needed. Rules receive fresh names when reinstalled after `pop`.
//! The encoding uses ordinary egglog tables, actions, and rebuilding rather than
//! a custom union-find extension.
//!
//! ## Disequality relations (NEE)
//!
//! Each needed sort `S` gets a private relation `Ne_S : (S, S)`, named
//! `@disequality-ne-S`. An assertion inserts `Ne_S(left, right)`. Rebuilding
//! canonicalizes the relation's operands after unions. Each sort gets one rule:
//!
//! ```text
//! Ne_S(x, x) -> @disequality-contradiction()
//! ```
//!
//! The contradiction check tests this nullary relation after saturating the
//! private ruleset. Assertion storage does not itself union user values.
//!
//! ## Finite witness search
//!
//! The read predicate first probes existing encoded facts in either
//! orientation; absent lazy support means no stored witness.
//! A stored self-disequality is observable even when the operands are equal.
//!
//! Structural search reads the scoped marked-constructor names recorded by
//! `injectivity.rs`. Its breadth-first queue contains `(left, right)` goals.
//! Each pair is sorted before insertion into a per-call visited set, so
//! orientation changes and cycles do not cause repeated exploration. Equality
//! sorts share one global ID counter: probing another equality sort's tables
//! cannot match these values. Only equality-sort values enter the queue;
//! primitive fields are compared directly, never used as reverse-lookup keys.
//!
//! For a result pair, indexed reads find existing rows of the same marked
//! constructor. Their row cross-product supplies one alternative per argument:
//! a native primitive mismatch is a witness, and an equality-sort field adds a
//! child-pair goal. For a unary equality-sort argument pair, read-only
//! constructor lookups add the existing parent-result pair as a reverse goal.
//! Each queued alternative suffices to establish the goal it came from; a
//! path to a stored fact or primitive mismatch is a finite witness. A cycle
//! with no such endpoint establishes nothing.
//!
//! The search creates no constructor applications, unions, or persistent
//! derived-pair cache. Only its queue, visited pairs, and fetched row groups are
//! temporary. Worst-case work can still include many value pairs and matching
//! row cross-products. Ordinary assertion storage and private contradiction
//! normalization remain separate from this demand-driven search.

use std::{
    collections::{BTreeMap, HashSet, VecDeque},
    sync::Arc,
};

use egglog::{
    ArcSort, AtomTerm, CommandMacro, Context, Core, EGraph, Error, Primitive, RawValues, Read,
    ReadPrim, ReadState, TypeError, TypeInfo, Value,
    ast::{
        Action, Actions, Command, Expr, Fact, FunctionDecl, Macro, ParseError, Parser, Rule,
        RuleEvalMode, RunConfig, Schedule, Sexp, Span,
    },
    constraint::{Constraint, TypeConstraint},
    sort::S,
    util::{FreshGen, SymbolGen},
};

const PLACEHOLDER: &str = "@disequal";
const RULESET: &str = "@disequality";
const CONTRADICTION: &str = "@disequality-contradiction";

/// Install syntax and its lowering pass before enabling term/proof encoding.
/// Call once on a fresh graph.
pub(crate) fn add_disequality_support(egraph: &mut EGraph) {
    egraph.add_read_primitive(KnownDisequal, None);
    egraph.parser.add_action_macro(Arc::new(Disequal));
    egraph
        .parser
        .add_command_macro(Arc::new(CheckContradiction));
    egraph
        .command_macros_mut()
        .register(Arc::new(LowerDisequality));
}

/// Partial read predicate: `Unit` for a finite witness, undefined otherwise.
/// Its same-unionable-equality-sort signature excludes direct primitive inputs.
/// No validator is registered, so term/proof modes reject this predicate;
/// assertions retain their existing mode support.
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

impl ReadPrim for KnownDisequal {
    fn apply<'a, 'db>(&self, state: ReadState<'a, 'db>, args: &[Value]) -> Option<Value> {
        let [lhs, rhs] = args else {
            unreachable!("known-disequal? arity is checked before execution")
        };
        match known_disequal(&state, *lhs, *rhs) {
            Ok(true) => Some(state.base_to_value(())),
            Ok(false) => None,
            Err(error) => {
                log::error!("known-disequal?: {error}");
                None
            }
        }
    }
}

/// Search unordered equality-sort pairs against the current committed graph.
/// Every edge is a sound same-constructor forward or unary reverse implication;
/// any path to a stored assertion or native primitive mismatch is a witness.
/// The per-call visited set terminates cycles, and all row/parent lookups are
/// read-only, including subsumed rows. See the module explanation for costs.
fn known_disequal<'db>(state: &ReadState<'_, 'db>, lhs: Value, rhs: Value) -> Result<bool, Error> {
    let mut assertion_tables = Vec::new();
    // The common explicit-assertion case needs no structural search.
    for name in state.tables() {
        if name.starts_with("@disequality-ne-") {
            if asserted_disequal(state, name, lhs, rhs)? {
                return Ok(true);
            }
            assertion_tables.push(name);
        }
    }
    let mut names = Vec::new();
    if state
        .table_size(crate::injectivity::MARKED_CONSTRUCTORS)
        .is_some()
    {
        state.function_entries(crate::injectivity::MARKED_CONSTRUCTORS, |entry| {
            names.push(state.value_to_base::<S>(entry.inputs[0]).0);
        })?;
    }
    let mut constructors = Vec::new();
    for name in &names {
        constructors.push((name.as_str(), state.constructor_schema(name)?));
    }
    // All queued values are equality-sort IDs from the same global counter.
    let mut pending = VecDeque::from([(lhs, rhs)]);
    let mut visited = HashSet::new();
    while let Some((mut left, mut right)) = pending.pop_front() {
        if left > right {
            std::mem::swap(&mut left, &mut right);
        }
        if !visited.insert((left, right)) {
            continue;
        }
        for name in &assertion_tables {
            if asserted_disequal(state, name, left, right)? {
                return Ok(true);
            }
        }
        for &(name, schema) in &constructors {
            let mut left_rows = Vec::new();
            let mut right_rows = Vec::new();
            state.constructor_enodes_for_eclass(name, left, |node| {
                left_rows.push(node.children.to_vec())
            })?;
            state.constructor_enodes_for_eclass(name, right, |node| {
                right_rows.push(node.children.to_vec())
            })?;
            for a in &left_rows {
                for b in &right_rows {
                    for ((&a, &b), input) in a.iter().zip(b).zip(&schema.input) {
                        if input.is_eq_sort() {
                            pending.push_back((a, b));
                        } else if a != b {
                            return Ok(true);
                        }
                    }
                }
            }
            if let [input] = schema.input.as_slice()
                && input.is_eq_sort()
            {
                // Constructor lookup is read-only and includes subsumed rows.
                // Missing applications supply no reverse implication.
                if let (Some(a), Some(b)) = (
                    state.eclass_of(name, RawValues(vec![left]))?,
                    state.eclass_of(name, RawValues(vec![right]))?,
                ) {
                    pending.push_back((a, b));
                }
            }
        }
    }
    Ok(false)
}

/// Probe an existing assertion relation in either orientation without adding rows.
fn asserted_disequal(
    state: &ReadState<'_, '_>,
    name: &str,
    lhs: Value,
    rhs: Value,
) -> Result<bool, Error> {
    Ok(state.contains(name, RawValues(vec![lhs, rhs]))?
        || state.contains(name, RawValues(vec![rhs, lhs]))?)
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
        expression_head != Some(PLACEHOLDER)
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
        let Some(span) = sorts.values().next().cloned().or(support_span) else {
            return Ok(vec![command]);
        };
        let mut commands = Vec::new();
        if types.get_func_type(CONTRADICTION).is_none() {
            commands.push(Command::AddRuleset(span.clone(), RULESET.into()));
            commands.push(Command::Relation {
                span: span.clone(),
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
            commands.push(Command::Rule {
                rule: Rule {
                    span: span.clone(),
                    // Proof history survives pop, so reinstalled rules need fresh names.
                    name: symbols.fresh(&format!("@disequality-ne-self-{sort}")),
                    ruleset: RULESET.into(),
                    body: vec![Fact::Fact(Expr::Call(
                        span.clone(),
                        name,
                        vec![x.clone(), x],
                    ))],
                    head: Actions::singleton(Action::Expr(
                        span.clone(),
                        Expr::Call(span, CONTRADICTION.into(), vec![]),
                    )),
                    eval_mode: RuleEvalMode::Seminaive,
                    no_decomp: false,
                    include_subsumed: false,
                },
            });
        }
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
            Command::Rule { rule } if contains_disequal(&rule.head) => {
                // Union has the same operand constraints as disequal. Use it only
                // for inference, never execution, so head uses can constrain the body.
                let mut probe = rule.clone();
                probe.head = union_probe(&rule.head);
                let resolved = types.typecheck_rule(symbols, &probe, false)?;
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
            Command::Fail(_, commands) => {
                for command in commands {
                    Self::lower_command(command, symbols, types, sorts, support_span)?;
                }
            }
            Command::RunSchedule(Schedule::Saturate(span, schedule)) if matches!(schedule.as_ref(), Schedule::Run(_, config) if config.ruleset == RULESET) =>
            {
                *support_span = Some(span.clone());
            }
            _ => {}
        }
        Ok(())
    }
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
