use egglog::{
    ArcSort, CommandMacro, Context, Error, TypeError, TypeInfo,
    ast::{
        Action, Actions, Command, Expr, Fact, Macro, ParseError, Parser, Rule, RuleEvalMode,
        RunConfig, Schedule, Schema, Sexp, Span,
    },
    util::SymbolGen,
};
use std::{collections::BTreeMap, fmt::Write, sync::Arc};
use std::{fmt, str::FromStr};

const PLACEHOLDER: &str = "@disequal";
const CHECK_PLACEHOLDER: &str = "@check-disequal";
const CHECK_RULESET: &str = "@disequality";
const SUPPORT_SORT: &str = "@disequality-support";
const TRUTH_SORT: &str = "@disequality-truth";
const TRUE: &str = "@disequality-true";
const FALSE: &str = "@disequality-false";

/// Published encodings supported by the `(disequal lhs rhs)` action.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum DisequalityEncoding {
    /// The five-rule equality embedding (EE) from Zakhour et al.
    #[default]
    EqualityEmbedding,
    /// Equality embedding with self-equality contradiction detection (OEE).
    OptimizedEqualityEmbedding,
    /// A private `ne` e-node with self-loop contradiction detection (NEE).
    NegatedEqualityEmbedding,
    /// A symmetric database relation over e-classes (DE).
    DisequalityEdges,
}

impl DisequalityEncoding {
    pub const POSSIBLE_VALUES: &str = "ee, oee, nee, de";

    pub const fn cli_name(self) -> &'static str {
        match self {
            Self::EqualityEmbedding => "ee",
            Self::OptimizedEqualityEmbedding => "oee",
            Self::NegatedEqualityEmbedding => "nee",
            Self::DisequalityEdges => "de",
        }
    }
}

impl FromStr for DisequalityEncoding {
    type Err = String;

    fn from_str(value: &str) -> Result<Self, Self::Err> {
        match value {
            "ee" => Ok(Self::EqualityEmbedding),
            "oee" => Ok(Self::OptimizedEqualityEmbedding),
            "nee" => Ok(Self::NegatedEqualityEmbedding),
            "de" => Ok(Self::DisequalityEdges),
            _ => Err(format!(
                "unknown disequality encoding `{value}`; expected one of: {}",
                Self::POSSIBLE_VALUES
            )),
        }
    }
}

impl fmt::Display for DisequalityEncoding {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.cli_name())
    }
}

pub(crate) fn add_disequality_support(egraph: &mut egglog::EGraph, encoding: DisequalityEncoding) {
    egraph.parser.add_action_macro(Arc::new(DisequalAction));
    egraph.parser.add_command_macro(Arc::new(CheckDisequal));
    egraph
        .parser
        .add_command_macro(Arc::new(CheckDisequalities));
    egraph
        .command_macros_mut()
        .register(Arc::new(DisequalityMacro { encoding }));
}

/// The relationship known between two terms in a consistent e-graph.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DisequalityComparison {
    Equal,
    Unequal,
    Indeterminate,
}

/// Query equality and compiled disequality without exposing an encoding's
/// generated functions or relations.
pub fn compare_disequality(
    egraph: &mut egglog::EGraph,
    encoding: DisequalityEncoding,
    lhs: Expr,
    rhs: Expr,
) -> Result<DisequalityComparison, Error> {
    let span = egglog::span!();
    let equality = Command::Check(
        span.clone(),
        vec![Fact::Eq(span.clone(), lhs.clone(), rhs.clone())],
    );
    match egraph.run_program(vec![equality]) {
        Ok(_) => return Ok(DisequalityComparison::Equal),
        Err(Error::CheckError(_, _)) => {}
        Err(error) => return Err(error),
    }

    let (sort, _) = egraph.eval_expr(&lhs)?;
    let support = match encoding {
        DisequalityEncoding::EqualityEmbedding
        | DisequalityEncoding::OptimizedEqualityEmbedding => equality_symbol(sort.name()),
        DisequalityEncoding::NegatedEqualityEmbedding => negated_equality_symbol(sort.name()),
        DisequalityEncoding::DisequalityEdges => disequality_edge_symbol(sort.name()),
    };
    if egraph.get_function(&support).is_none() {
        return Ok(DisequalityComparison::Indeterminate);
    }
    let disequality = symmetric_disequality_check(span, lhs, rhs, sort.name(), encoding);
    match egraph.run_program(vec![disequality]) {
        Ok(_) => Ok(DisequalityComparison::Unequal),
        Err(Error::ExpectFail(_)) => Ok(DisequalityComparison::Indeterminate),
        Err(error) => Err(error),
    }
}

/// Run the private propagation schedule and report whether no disequality has
/// collapsed to a self-edge. The outer `fail` converts the generated panic
/// into a boolean result without inspecting backend diagnostic text.
pub fn disequalities_are_consistent(egraph: &mut egglog::EGraph) -> Result<bool, Error> {
    if egraph.get_sort_by_name(SUPPORT_SORT).is_none() {
        return Ok(true);
    }
    let span = egglog::span!();
    match egraph.run_program(vec![Command::Fail(
        span.clone(),
        vec![Command::RunSchedule(disequality_schedule(span))],
    )]) {
        Ok(_) => Ok(false),
        Err(Error::ExpectFail(_)) => Ok(true),
        Err(error) => Err(error),
    }
}

struct CheckDisequalities;

impl Macro<Vec<Command>> for CheckDisequalities {
    fn name(&self) -> &str {
        "check-disequalities"
    }

    fn parse(
        &self,
        args: &[Sexp],
        span: Span,
        _parser: &mut Parser,
    ) -> Result<Vec<Command>, ParseError> {
        if !args.is_empty() {
            return Err(ParseError(span, "usage: (check-disequalities)".to_owned()));
        }
        Ok(vec![Command::RunSchedule(disequality_schedule(span))])
    }
}

struct CheckDisequal;

impl Macro<Vec<Command>> for CheckDisequal {
    fn name(&self) -> &str {
        "check-disequal"
    }

    fn parse(
        &self,
        args: &[Sexp],
        span: Span,
        parser: &mut Parser,
    ) -> Result<Vec<Command>, ParseError> {
        let [lhs, rhs] = args else {
            return Err(ParseError(
                span,
                "usage: (check-disequal <expr> <expr>)".to_owned(),
            ));
        };
        Ok(vec![Command::Check(
            span.clone(),
            vec![Fact::Fact(call(
                &span,
                CHECK_PLACEHOLDER,
                vec![parser.parse_expr(lhs)?, parser.parse_expr(rhs)?],
            ))],
        )])
    }
}

struct DisequalAction;

impl Macro<Vec<Action>> for DisequalAction {
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
            return Err(ParseError(
                span,
                "usage: (disequal <expr> <expr>)".to_owned(),
            ));
        };
        let lhs = parser.parse_expr(lhs)?;
        let rhs = parser.parse_expr(rhs)?;
        Ok(vec![Action::Expr(
            span.clone(),
            Expr::Call(span, PLACEHOLDER.to_owned(), vec![lhs, rhs]),
        )])
    }
}

struct DisequalityMacro {
    encoding: DisequalityEncoding,
}

impl CommandMacro for DisequalityMacro {
    fn transform(
        &self,
        command: Command,
        symbol_gen: &mut SymbolGen,
        type_info: &TypeInfo,
    ) -> Result<Vec<Command>, Error> {
        match command {
            Command::RunSchedule(schedule)
                if is_disequality_schedule(&schedule)
                    && type_info.get_sort_by_name(SUPPORT_SORT).is_none() =>
            {
                Ok(Vec::new())
            }
            Command::Check(span, facts) => {
                let [Fact::Fact(Expr::Call(_, head, args))] = facts.as_slice() else {
                    return Ok(vec![Command::Check(span, facts)]);
                };
                if head != CHECK_PLACEHOLDER {
                    return Ok(vec![Command::Check(span, facts)]);
                }
                let [lhs, rhs] = args.as_slice() else {
                    return Err(Error::DesugarError(
                        span,
                        "internal check-disequal command must have two operands".to_owned(),
                    ));
                };
                let sort = disequality_operand_sort(
                    type_info,
                    symbol_gen,
                    lhs,
                    rhs,
                    &[],
                    Context::Full,
                    &span,
                )?;
                let mut required_sorts = BTreeMap::new();
                required_sorts.insert(sort.name().to_owned(), span.clone());
                let mut commands = support_commands(type_info, required_sorts, self.encoding);
                commands.push(Command::RunSchedule(disequality_schedule(span.clone())));
                commands.push(symmetric_disequality_check(
                    span,
                    lhs.clone(),
                    rhs.clone(),
                    sort.name(),
                    self.encoding,
                ));
                Ok(commands)
            }
            Command::Rule { mut rule } if contains_disequality(&rule.head) => {
                let mut bindings = Vec::new();
                for fact in type_info.typecheck_facts(symbol_gen, &rule.body)? {
                    fact.visit_vars(&mut |span, var| {
                        if !bindings
                            .iter()
                            .any(|(name, _, _): &(String, Span, ArcSort)| name == &var.name)
                        {
                            bindings.push((var.name.clone(), span.clone(), var.sort.clone()));
                        }
                    });
                }
                let (head, required_sorts) = lower_actions(
                    rule.head,
                    bindings,
                    Context::Full,
                    symbol_gen,
                    type_info,
                    self.encoding,
                )?;
                rule.head = head;
                let mut commands = support_commands(type_info, required_sorts, self.encoding);
                commands.push(Command::Rule { rule });
                Ok(commands)
            }
            Command::Action(action)
                if contains_disequality(&Actions::singleton(action.clone())) =>
            {
                let (mut actions, required_sorts) = lower_actions(
                    Actions::singleton(action),
                    Vec::new(),
                    Context::Full,
                    symbol_gen,
                    type_info,
                    self.encoding,
                )?;
                let mut commands = support_commands(type_info, required_sorts, self.encoding);
                if actions.0.len() == 1 {
                    commands.push(Command::Action(actions.0.remove(0)));
                } else {
                    commands.push(Command::Actions(actions));
                }
                Ok(commands)
            }
            Command::Actions(actions) if contains_disequality(&actions) => {
                let (actions, required_sorts) = lower_actions(
                    actions,
                    Vec::new(),
                    Context::Full,
                    symbol_gen,
                    type_info,
                    self.encoding,
                )?;
                let mut commands = support_commands(type_info, required_sorts, self.encoding);
                commands.push(Command::Actions(actions));
                Ok(commands)
            }
            Command::LetBegin(span, name, actions) if contains_disequality(&actions) => {
                let (actions, required_sorts) = lower_actions(
                    actions,
                    Vec::new(),
                    Context::Full,
                    symbol_gen,
                    type_info,
                    self.encoding,
                )?;
                let mut commands = support_commands(type_info, required_sorts, self.encoding);
                commands.push(Command::LetBegin(span, name, actions));
                Ok(commands)
            }
            command => Ok(vec![command]),
        }
    }
}

fn contains_disequality(actions: &Actions) -> bool {
    actions.0.iter().any(|action| {
        matches!(
            action,
            Action::Expr(_, Expr::Call(_, head, _)) if head == PLACEHOLDER
        )
    })
}

fn lower_actions(
    actions: Actions,
    mut bindings: Vec<(String, Span, ArcSort)>,
    context: Context,
    symbol_gen: &mut SymbolGen,
    type_info: &TypeInfo,
    encoding: DisequalityEncoding,
) -> Result<(Actions, BTreeMap<String, Span>), Error> {
    let mut lowered = Vec::with_capacity(actions.0.len());
    let mut required_sorts = BTreeMap::new();

    for action in actions.0 {
        match action {
            Action::Expr(action_span, Expr::Call(_, head, args)) if head == PLACEHOLDER => {
                let [lhs, rhs] = args.as_slice() else {
                    return Err(Error::DesugarError(
                        action_span,
                        "internal disequal action must have two operands".to_owned(),
                    ));
                };
                let lhs_sort = disequality_operand_sort(
                    type_info,
                    symbol_gen,
                    lhs,
                    rhs,
                    &bindings,
                    context,
                    &action_span,
                )?;

                required_sorts
                    .entry(lhs_sort.name().to_owned())
                    .or_insert_with(|| action_span.clone());
                lowered.extend(lower_disequality(
                    action_span,
                    lhs.clone(),
                    rhs.clone(),
                    lhs_sort.name(),
                    encoding,
                ));
            }
            Action::Let(span, name, value) => {
                let sort = type_info.infer_expr_sort(symbol_gen, &value, &bindings, context)?;
                if bindings.iter().any(|(bound, _, _)| bound == &name) {
                    return Err(TypeError::AlreadyDefined(name, span).into());
                }
                bindings.push((name.clone(), span.clone(), sort));
                lowered.push(Action::Let(span, name, value));
            }
            action => lowered.push(action),
        }
    }

    Ok((Actions::new(lowered), required_sorts))
}

fn disequality_operand_sort(
    type_info: &TypeInfo,
    symbol_gen: &mut SymbolGen,
    lhs: &Expr,
    rhs: &Expr,
    bindings: &[(String, Span, ArcSort)],
    context: Context,
    span: &Span,
) -> Result<ArcSort, Error> {
    let lhs_sort = operand_sort(type_info, symbol_gen, lhs, bindings, context)?;
    let rhs_sort = operand_sort(type_info, symbol_gen, rhs, bindings, context)?;
    if lhs_sort.name() != rhs_sort.name() {
        return Err(TypeError::Mismatch {
            expr: rhs.clone(),
            expected: lhs_sort,
            actual: rhs_sort,
        }
        .into());
    }
    if !lhs_sort.is_eq_sort() {
        return Err(TypeError::NonEqsortUnion(lhs_sort, span.clone()).into());
    }
    if !type_info.is_sort_unionable(&lhs_sort) {
        return Err(TypeError::NonUnionableSort(lhs_sort, span.clone()).into());
    }
    Ok(lhs_sort)
}

fn symmetric_disequality_check(
    span: Span,
    lhs: Expr,
    rhs: Expr,
    sort: &str,
    encoding: DisequalityEncoding,
) -> Command {
    let forward = known_disequality_fact(&span, lhs.clone(), rhs.clone(), sort, encoding);
    let reverse = known_disequality_fact(&span, rhs, lhs, sort, encoding);
    Command::Fail(
        span.clone(),
        vec![
            Command::Fail(
                span.clone(),
                vec![Command::Check(span.clone(), vec![forward])],
            ),
            Command::Fail(
                span.clone(),
                vec![Command::Check(span.clone(), vec![reverse])],
            ),
        ],
    )
}

fn known_disequality_fact(
    span: &Span,
    lhs: Expr,
    rhs: Expr,
    sort: &str,
    encoding: DisequalityEncoding,
) -> Fact {
    match encoding {
        DisequalityEncoding::EqualityEmbedding
        | DisequalityEncoding::OptimizedEqualityEmbedding => Fact::Eq(
            span.clone(),
            call(span, &equality_symbol(sort), vec![lhs, rhs]),
            call(span, FALSE, vec![]),
        ),
        DisequalityEncoding::NegatedEqualityEmbedding => {
            Fact::Fact(call(span, &negated_equality_symbol(sort), vec![lhs, rhs]))
        }
        DisequalityEncoding::DisequalityEdges => {
            Fact::Fact(call(span, &disequality_edge_symbol(sort), vec![lhs, rhs]))
        }
    }
}

/// Select the sort-specific encoding before the generated action is typechecked.
///
/// A variable or declared function has a fixed output sort independent of its
/// operands, so avoid invoking general constraint solving for these common
/// cases. The generated action still goes through normal typechecking and
/// validates the complete operand expressions.
fn operand_sort(
    type_info: &TypeInfo,
    symbol_gen: &mut SymbolGen,
    expr: &Expr,
    bindings: &[(String, Span, ArcSort)],
    context: Context,
) -> Result<ArcSort, TypeError> {
    let declared = match expr {
        Expr::Var(_, name) => bindings
            .iter()
            .find_map(|(bound, _, sort)| (bound == name).then_some(sort))
            .or_else(|| type_info.get_global_sort(name)),
        Expr::Call(_, head, _) if !type_info.is_primitive(head) => type_info
            .get_func_type(head)
            .map(|function| function.output()),
        _ => None,
    };
    match declared {
        Some(sort) => Ok(sort.clone()),
        None => type_info.infer_expr_sort(symbol_gen, expr, bindings, context),
    }
}

fn lower_disequality(
    span: Span,
    lhs: Expr,
    rhs: Expr,
    sort: &str,
    encoding: DisequalityEncoding,
) -> Vec<Action> {
    match encoding {
        DisequalityEncoding::EqualityEmbedding => vec![Action::Union(
            span.clone(),
            call(&span, &equality_symbol(sort), vec![lhs, rhs]),
            call(&span, FALSE, vec![]),
        )],
        DisequalityEncoding::OptimizedEqualityEmbedding => vec![Action::Union(
            span.clone(),
            call(&span, &equality_symbol(sort), vec![lhs, rhs]),
            call(&span, FALSE, vec![]),
        )],
        DisequalityEncoding::NegatedEqualityEmbedding => vec![Action::Expr(
            span.clone(),
            call(&span, &negated_equality_symbol(sort), vec![lhs, rhs]),
        )],
        DisequalityEncoding::DisequalityEdges => {
            let edge = disequality_edge_symbol(sort);
            vec![Action::Expr(
                span.clone(),
                call(&span, &edge, vec![lhs, rhs]),
            )]
        }
    }
}

fn support_commands(
    type_info: &TypeInfo,
    required_sorts: BTreeMap<String, Span>,
    encoding: DisequalityEncoding,
) -> Vec<Command> {
    let Some(base_span) = required_sorts.values().next().cloned() else {
        return Vec::new();
    };
    let mut commands = Vec::new();

    if type_info.get_sort_by_name(SUPPORT_SORT).is_none() {
        commands.push(Command::Sort {
            span: base_span.clone(),
            name: SUPPORT_SORT.to_owned(),
            presort_and_args: None,
            uf: None,
            container_rebuild: None,
            proof_constructors: None,
            unionable: true,
        });
        commands.push(Command::AddRuleset(
            base_span.clone(),
            CHECK_RULESET.to_owned(),
        ));
    }

    match encoding {
        DisequalityEncoding::EqualityEmbedding
        | DisequalityEncoding::OptimizedEqualityEmbedding => {
            if type_info.get_sort_by_name(TRUTH_SORT).is_none() {
                commands.push(Command::Sort {
                    span: base_span.clone(),
                    name: TRUTH_SORT.to_owned(),
                    presort_and_args: None,
                    uf: None,
                    container_rebuild: None,
                    proof_constructors: None,
                    unionable: true,
                });
                commands.push(constructor(&base_span, TRUE, vec![], TRUTH_SORT));
                commands.push(constructor(&base_span, FALSE, vec![], TRUTH_SORT));
                if encoding == DisequalityEncoding::EqualityEmbedding {
                    commands.push(equality_embedding_contradiction_rule(&base_span));
                }
            }

            let truth_equality = equality_symbol(TRUTH_SORT);
            if type_info.get_func_type(&truth_equality).is_none() {
                commands.extend(equality_support(&base_span, TRUTH_SORT, encoding));
            }

            for (sort, span) in required_sorts {
                let equality = equality_symbol(&sort);
                if type_info.get_func_type(&equality).is_none() && sort != TRUTH_SORT {
                    commands.extend(equality_support(&span, &sort, encoding));
                }
            }
        }
        DisequalityEncoding::NegatedEqualityEmbedding => {
            for (sort, span) in required_sorts {
                let negated_equality = negated_equality_symbol(&sort);
                if type_info.get_func_type(&negated_equality).is_none() {
                    commands.extend(negated_equality_support(&span, &sort));
                }
            }
        }
        DisequalityEncoding::DisequalityEdges => {
            for (sort, span) in required_sorts {
                let edge = disequality_edge_symbol(&sort);
                if type_info.get_func_type(&edge).is_none() {
                    commands.extend(disequality_edge_support(&span, &sort));
                }
            }
        }
    }

    commands
}

fn equality_support(span: &Span, sort: &str, encoding: DisequalityEncoding) -> Vec<Command> {
    match encoding {
        DisequalityEncoding::EqualityEmbedding => equality_embedding_support(span, sort),
        DisequalityEncoding::OptimizedEqualityEmbedding => {
            optimized_equality_embedding_support(span, sort)
        }
        DisequalityEncoding::NegatedEqualityEmbedding | DisequalityEncoding::DisequalityEdges => {
            unreachable!()
        }
    }
}

fn equality_embedding_support(span: &Span, sort: &str) -> Vec<Command> {
    let equality = equality_symbol(sort);
    let suffix = symbol_component(sort);
    let x = Expr::Var(span.clone(), "@disequality-x".to_owned());
    let y = Expr::Var(span.clone(), "@disequality-y".to_owned());
    let eq_xy = call(span, &equality, vec![x.clone(), y.clone()]);
    let eq_yx = call(span, &equality, vec![y.clone(), x.clone()]);
    let eq_xx = call(span, &equality, vec![x.clone(), x.clone()]);
    let eq_yy = call(span, &equality, vec![y.clone(), y.clone()]);
    let true_expr = call(span, TRUE, vec![]);
    let false_expr = call(span, FALSE, vec![]);
    let truth_equality = equality_symbol(TRUTH_SORT);

    vec![
        constructor(span, &equality, vec![sort, sort], TRUTH_SORT),
        rule(
            span,
            format!("@disequality-ee-lift-{suffix}"),
            vec![Fact::Eq(span.clone(), eq_xy.clone(), true_expr.clone())],
            vec![Action::Union(span.clone(), x.clone(), y.clone())],
        ),
        rule(
            span,
            format!("@disequality-ee-symmetry-{suffix}"),
            vec![Fact::Eq(span.clone(), eq_xy.clone(), false_expr.clone())],
            vec![Action::Union(span.clone(), eq_yx, false_expr.clone())],
        ),
        rule(
            span,
            format!("@disequality-ee-double-negation-{suffix}"),
            vec![Fact::Eq(
                span.clone(),
                call(
                    span,
                    &truth_equality,
                    vec![eq_xy.clone(), false_expr.clone()],
                ),
                false_expr.clone(),
            )],
            vec![Action::Union(span.clone(), x.clone(), y.clone())],
        ),
        rule(
            span,
            format!("@disequality-ee-reflexive-left-{suffix}"),
            vec![Fact::Eq(span.clone(), eq_xy.clone(), false_expr.clone())],
            vec![Action::Union(span.clone(), eq_xx, true_expr.clone())],
        ),
        rule(
            span,
            format!("@disequality-ee-reflexive-right-{suffix}"),
            vec![Fact::Eq(span.clone(), eq_xy, false_expr)],
            vec![Action::Union(span.clone(), eq_yy, true_expr)],
        ),
    ]
}

fn optimized_equality_embedding_support(span: &Span, sort: &str) -> Vec<Command> {
    let equality = equality_symbol(sort);
    let suffix = symbol_component(sort);
    let x = Expr::Var(span.clone(), "@disequality-x".to_owned());
    let y = Expr::Var(span.clone(), "@disequality-y".to_owned());
    let eq_xy = call(span, &equality, vec![x.clone(), y.clone()]);
    let false_expr = call(span, FALSE, vec![]);
    let truth_equality = equality_symbol(TRUTH_SORT);

    vec![
        constructor(span, &equality, vec![sort, sort], TRUTH_SORT),
        rule(
            span,
            format!("@disequality-oee-lift-{suffix}"),
            vec![Fact::Eq(
                span.clone(),
                eq_xy.clone(),
                call(span, TRUE, vec![]),
            )],
            vec![Action::Union(span.clone(), x.clone(), y.clone())],
        ),
        rule(
            span,
            format!("@disequality-oee-double-negation-{suffix}"),
            vec![Fact::Eq(
                span.clone(),
                call(
                    span,
                    &truth_equality,
                    vec![eq_xy.clone(), false_expr.clone()],
                ),
                false_expr.clone(),
            )],
            vec![Action::Union(span.clone(), x.clone(), y.clone())],
        ),
        rule(
            span,
            format!("@disequality-oee-contradiction-{suffix}"),
            vec![Fact::Eq(
                span.clone(),
                call(span, &equality, vec![x.clone(), x]),
                false_expr,
            )],
            vec![Action::Panic(
                span.clone(),
                "disequality constraint contradicted".to_owned(),
            )],
        ),
    ]
}

fn negated_equality_support(span: &Span, sort: &str) -> Vec<Command> {
    let negated_equality = negated_equality_symbol(sort);
    let x = Expr::Var(span.clone(), "@disequality-x".to_owned());
    vec![
        constructor(span, &negated_equality, vec![sort, sort], sort),
        rule(
            span,
            format!("@disequality-nee-contradiction-{}", symbol_component(sort)),
            vec![Fact::Fact(call(
                span,
                &negated_equality,
                vec![x.clone(), x],
            ))],
            vec![Action::Panic(
                span.clone(),
                "disequality constraint contradicted".to_owned(),
            )],
        ),
    ]
}

fn disequality_edge_support(span: &Span, sort: &str) -> Vec<Command> {
    let edge = disequality_edge_symbol(sort);
    let x = Expr::Var(span.clone(), "@disequality-x".to_owned());
    let y = Expr::Var(span.clone(), "@disequality-y".to_owned());
    vec![
        Command::Relation {
            span: span.clone(),
            name: edge.clone(),
            inputs: vec![sort.to_owned(), sort.to_owned()],
        },
        rule(
            span,
            format!("@disequality-de-symmetry-{}", symbol_component(sort)),
            vec![Fact::Fact(call(span, &edge, vec![x.clone(), y.clone()]))],
            vec![Action::Expr(
                span.clone(),
                call(span, &edge, vec![y, x.clone()]),
            )],
        ),
        rule(
            span,
            format!("@disequality-de-contradiction-{}", symbol_component(sort)),
            vec![Fact::Fact(call(span, &edge, vec![x.clone(), x]))],
            vec![Action::Panic(
                span.clone(),
                "disequality constraint contradicted".to_owned(),
            )],
        ),
    ]
}

fn equality_embedding_contradiction_rule(span: &Span) -> Command {
    rule(
        span,
        "@disequality-contradiction".to_owned(),
        vec![Fact::Eq(
            span.clone(),
            call(span, TRUE, vec![]),
            call(span, FALSE, vec![]),
        )],
        vec![Action::Panic(
            span.clone(),
            "disequality constraint contradicted".to_owned(),
        )],
    )
}

fn constructor(span: &Span, name: &str, inputs: Vec<&str>, output: &str) -> Command {
    Command::Constructor {
        span: span.clone(),
        name: name.to_owned(),
        schema: Schema {
            input: inputs.into_iter().map(str::to_owned).collect(),
            outputs: vec![output.to_owned()],
        },
        cost: None,
        unextractable: true,
        hidden: true,
        let_binding: false,
        term_constructor: None,
    }
}

fn rule(span: &Span, name: String, body: Vec<Fact>, head: Vec<Action>) -> Command {
    Command::Rule {
        rule: Rule {
            span: span.clone(),
            head: Actions::new(head),
            body,
            name,
            ruleset: CHECK_RULESET.to_owned(),
            eval_mode: RuleEvalMode::Seminaive,
            no_decomp: false,
            include_subsumed: false,
        },
    }
}

fn disequality_schedule(span: Span) -> Schedule {
    Schedule::Saturate(
        span.clone(),
        Box::new(Schedule::Run(
            span,
            RunConfig {
                ruleset: CHECK_RULESET.to_owned(),
                until: None,
            },
        )),
    )
}

fn is_disequality_schedule(schedule: &Schedule) -> bool {
    matches!(
        schedule,
        Schedule::Saturate(
            _,
            inner
        ) if matches!(
            inner.as_ref(),
            Schedule::Run(_, RunConfig { ruleset, until: None }) if ruleset == CHECK_RULESET
        )
    )
}

fn call(span: &Span, head: &str, args: Vec<Expr>) -> Expr {
    Expr::Call(span.clone(), head.to_owned(), args)
}

fn equality_symbol(sort: &str) -> String {
    format!("@disequality-eq-{}", symbol_component(sort))
}

fn negated_equality_symbol(sort: &str) -> String {
    format!("@disequality-ne-{}", symbol_component(sort))
}

fn disequality_edge_symbol(sort: &str) -> String {
    format!("@disequality-edge-{}", symbol_component(sort))
}

fn symbol_component(value: &str) -> String {
    let mut encoded = String::with_capacity(value.len() * 2);
    for byte in value.bytes() {
        write!(encoded, "{byte:02x}").expect("writing to a String cannot fail");
    }
    encoded
}

#[cfg(test)]
mod tests {
    use crate::{
        DisequalityComparison, DisequalityEncoding, compare_disequality,
        disequalities_are_consistent, new_experimental_egraph,
        new_experimental_egraph_for_proofs_with_disequality_encoding,
        new_experimental_egraph_with_disequality_encoding,
    };
    use egglog::ast::sanitize_internal_names;
    use std::path::Path;
    use tempfile::TempDir;

    const ENCODINGS: [DisequalityEncoding; 4] = [
        DisequalityEncoding::EqualityEmbedding,
        DisequalityEncoding::OptimizedEqualityEmbedding,
        DisequalityEncoding::NegatedEqualityEmbedding,
        DisequalityEncoding::DisequalityEdges,
    ];

    fn parameter_analysis_facts() -> TempDir {
        let directory = tempfile::tempdir().unwrap();
        for (name, contents) in [
            ("config.tsv", "2\n"),
            ("f.tsv", "3\t2\n5\t4\n"),
            ("g.tsv", "8\t6\t7\n11\t9\t10\n"),
            ("h.tsv", "15\t12\t13\t14\n19\t16\t17\t18\n"),
            (
                "numerals.tsv",
                "0\t1\n1\t2\n2\t1\n4\t2\n6\t1\n7\t2\n9\t2\n10\t1\n12\t1\n13\t2\n14\t3\n16\t1\n17\t2\n18\t3\n",
            ),
            ("pairs.tsv", "0\t0\t1\n1\t3\t5\n2\t8\t11\n3\t15\t19\n"),
        ] {
            std::fs::write(directory.path().join(name), contents).unwrap();
        }
        directory
    }

    #[test]
    fn equality_embedding_accepts_consistent_disequality() {
        let mut egraph = new_experimental_egraph();
        egraph
            .parse_and_run_program(
                None,
                r#"
                (datatype Math (A) (B))
                (disequal (A) (B))
                (check-disequalities)
                "#,
            )
            .unwrap();
    }

    #[test]
    fn equality_embedding_rejects_reflexive_disequality() {
        let mut egraph = new_experimental_egraph();
        let error = egraph
            .parse_and_run_program(
                None,
                r#"
                (datatype Math (A))
                (disequal (A) (A))
                (check-disequalities)
                "#,
            )
            .unwrap_err();
        assert!(
            error
                .to_string()
                .contains("disequality constraint contradicted")
        );
    }

    #[test]
    fn equality_embedding_detects_congruence_after_union() {
        let mut egraph = new_experimental_egraph();
        let error = egraph
            .parse_and_run_program(
                None,
                r#"
                (datatype Math (A) (B) (F Math))
                (disequal (F (A)) (F (B)))
                (union (A) (B))
                (check-disequalities)
                "#,
            )
            .unwrap_err();
        assert!(
            error
                .to_string()
                .contains("disequality constraint contradicted")
        );
    }

    #[test]
    fn check_disequalities_is_explicit_and_noops_without_constraints() {
        for encoding in ENCODINGS {
            let mut empty = new_experimental_egraph_with_disequality_encoding(encoding);
            empty
                .parse_and_run_program(None, "(check-disequalities)")
                .unwrap_or_else(|error| panic!("{encoding:?} rejected an empty check: {error}"));

            let mut contradictory = new_experimental_egraph_with_disequality_encoding(encoding);
            contradictory
                .parse_and_run_program(
                    None,
                    r#"
                    (datatype Math (A))
                    (disequal (A) (A))
                    (run 10)
                    "#,
                )
                .unwrap_or_else(|error| {
                    panic!("{encoding:?} ran private rules from the default ruleset: {error}")
                });
            let error = contradictory
                .parse_and_run_program(None, "(check-disequalities)")
                .expect_err("the explicit check must detect the stored contradiction");
            assert!(
                error
                    .to_string()
                    .contains("disequality constraint contradicted"),
                "unexpected {encoding:?} error: {error}"
            );
        }
    }

    #[test]
    fn check_disequalities_rejects_arguments() {
        let mut egraph = new_experimental_egraph();
        let error = egraph
            .parse_program(None, "(check-disequalities 1)")
            .unwrap_err();
        assert!(error.to_string().contains("usage: (check-disequalities)"));
    }

    #[test]
    fn all_encodings_query_known_disequalities_without_exposing_support_tables() {
        let program = r#"
            (datatype Math (A) (B) (C) (F Math))
            (disequal (F (A)) (F (B)))
            (check-disequal (F (A)) (F (B)))
            (check-disequal (F (B)) (F (A)))
            (union (A) (C))
            (check-disequal (F (C)) (F (B)))
        "#;

        for encoding in ENCODINGS {
            let mut egraph = new_experimental_egraph_with_disequality_encoding(encoding);
            egraph
                .parse_and_run_program(None, program)
                .unwrap_or_else(|error| panic!("{encoding:?} failed per-pair queries: {error}"));
            let unknown = egraph
                .parse_and_run_program(None, "(check-disequal (A) (B))")
                .expect_err("the query must fail when no relationship is known");
            assert!(
                matches!(unknown, egglog::Error::ExpectFail(_)),
                "unexpected {encoding:?} unknown-query error: {unknown}"
            );
        }
    }

    #[test]
    fn all_encodings_support_typed_comparison_and_consistency_queries() {
        for encoding in ENCODINGS {
            let mut egraph = new_experimental_egraph_with_disequality_encoding(encoding);
            egraph
                .parse_and_run_program(None, "(datatype Math (A) (B) (C))")
                .unwrap();
            let a = egraph.parser.get_expr_from_string(None, "(A)").unwrap();
            let b = egraph.parser.get_expr_from_string(None, "(B)").unwrap();
            assert_eq!(
                compare_disequality(&mut egraph, encoding, a.clone(), b.clone()).unwrap(),
                DisequalityComparison::Indeterminate,
                "{encoding:?} should allow queries before its first disequality"
            );
            egraph
                .parse_and_run_program(
                    None,
                    r#"
                    (disequal (A) (B))
                    "#,
                )
                .unwrap();
            let c = egraph.parser.get_expr_from_string(None, "(C)").unwrap();

            assert_eq!(
                compare_disequality(&mut egraph, encoding, a.clone(), a.clone()).unwrap(),
                DisequalityComparison::Equal,
                "{encoding:?} did not report reflexive equality"
            );
            assert_eq!(
                compare_disequality(&mut egraph, encoding, a.clone(), b.clone()).unwrap(),
                DisequalityComparison::Unequal,
                "{encoding:?} did not report the stored disequality"
            );
            assert_eq!(
                compare_disequality(&mut egraph, encoding, a.clone(), c).unwrap(),
                DisequalityComparison::Indeterminate,
                "{encoding:?} invented a relationship"
            );
            assert!(
                disequalities_are_consistent(&mut egraph).unwrap(),
                "{encoding:?} rejected a consistent graph"
            );

            egraph
                .parse_and_run_program(None, "(union (A) (B))")
                .unwrap();
            assert!(
                !disequalities_are_consistent(&mut egraph).unwrap(),
                "{encoding:?} missed a contradiction"
            );
            assert_eq!(
                compare_disequality(&mut egraph, encoding, a.clone(), b.clone()).unwrap(),
                DisequalityComparison::Equal,
                "{encoding:?} could not query an inconsistent graph"
            );
        }
    }

    #[test]
    fn per_pair_query_placeholder_is_fully_desugared() {
        for encoding in ENCODINGS {
            let mut egraph = new_experimental_egraph_with_disequality_encoding(encoding);
            let commands = egraph
                .resolve_program(
                    None,
                    r#"
                    (datatype Math (A) (B))
                    (disequal (A) (B))
                    (check-disequal (A) (B))
                    "#,
                )
                .unwrap_or_else(|error| panic!("{encoding:?} failed to desugar: {error}"));
            let rendered = commands
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join("\n");
            assert!(
                !rendered.contains(super::CHECK_PLACEHOLDER),
                "{encoding:?} leaked the query placeholder:\n{rendered}"
            );
            assert!(
                rendered.contains(super::CHECK_RULESET),
                "{encoding:?} omitted the private propagation schedule"
            );
        }
    }

    #[test]
    fn equality_embedding_works_in_rule_actions() {
        let mut egraph = new_experimental_egraph();
        let error = egraph
            .parse_and_run_program(
                None,
                r#"
                (datatype Math (A) (B))
                (relation apart (Math Math))
                (apart (A) (B))
                (rule ((apart x y)) ((disequal x y)))
                (run 10)
                (check-disequalities)
                (union (A) (B))
                (check-disequalities)
                "#,
            )
            .unwrap_err();
        assert!(
            error
                .to_string()
                .contains("disequality constraint contradicted")
        );
    }

    #[test]
    fn disequality_requires_matching_unionable_sorts() {
        let mut egraph = new_experimental_egraph();
        let mismatch = egraph
            .parse_and_run_program(
                None,
                r#"
                (datatype Left (L))
                (datatype Right (R))
                (disequal (L) (R))
                "#,
            )
            .unwrap_err();
        assert!(mismatch.to_string().contains("to have type Left"));

        let mut egraph = new_experimental_egraph();
        let primitive = egraph
            .parse_and_run_program(None, "(disequal 1 2)")
            .unwrap_err();
        assert!(
            primitive
                .to_string()
                .contains("Cannot union values of sort i64")
        );

        let mut egraph = new_experimental_egraph();
        let malformed = egraph
            .parse_and_run_program(
                None,
                r#"
                (datatype Math (A) (F Math))
                (disequal (F) (A))
                "#,
            )
            .unwrap_err();
        assert!(
            malformed.to_string().contains("Arity mismatch"),
            "unexpected malformed-operand error: {malformed}"
        );
    }

    #[test]
    fn all_encodings_detect_direct_and_congruence_contradictions() {
        for encoding in ENCODINGS {
            let mut egraph = new_experimental_egraph_with_disequality_encoding(encoding);
            egraph
                .parse_and_run_program(
                    None,
                    r#"
                    (datatype Math (A) (B) (F Math))
                    (disequal (A) (B))
                    (check-disequalities)
                    "#,
                )
                .unwrap_or_else(|error| {
                    panic!("{encoding:?} rejected a consistent graph: {error}")
                });

            let mut egraph = new_experimental_egraph_with_disequality_encoding(encoding);
            let direct = egraph
                .parse_and_run_program(
                    None,
                    r#"
                    (datatype Math (A))
                    (disequal (A) (A))
                    (check-disequalities)
                    "#,
                )
                .expect_err("a reflexive disequality must be contradictory");
            assert!(
                direct
                    .to_string()
                    .contains("disequality constraint contradicted"),
                "unexpected {encoding:?} error: {direct}"
            );

            let mut egraph = new_experimental_egraph_with_disequality_encoding(encoding);
            let congruence = egraph
                .parse_and_run_program(
                    None,
                    r#"
                    (datatype Math (A) (B) (F Math))
                    (disequal (F (A)) (F (B)))
                    (union (A) (B))
                    (check-disequalities)
                    "#,
                )
                .expect_err("congruence must expose the disequality self-loop");
            assert!(
                congruence
                    .to_string()
                    .contains("disequality constraint contradicted"),
                "unexpected {encoding:?} error: {congruence}"
            );
        }
    }

    #[test]
    fn all_encodings_support_rule_and_action_local_bindings() {
        let program = r#"
            (datatype Math (A) (B) (F Math))
            (relation apart (Math Math))
            (apart (A) (B))
            (rule ((apart x y))
                  ((let fy (F y))
                   (disequal (F x) fy)))
            (begin
              (let left (A))
              (disequal left (B)))
            (run 10)
            (check-disequalities)
            (union (A) (B))
            (fail (check-disequalities))
        "#;

        for encoding in ENCODINGS {
            let mut egraph = new_experimental_egraph_with_disequality_encoding(encoding);
            egraph
                .parse_and_run_program(None, program)
                .unwrap_or_else(|error| panic!("{encoding:?} failed local bindings: {error}"));
        }
    }

    #[test]
    fn all_encodings_generate_independent_support_for_each_sort() {
        let program = r#"
            (datatype Left (L0) (L1))
            (datatype Right (R0) (R1))
            (disequal (L0) (L1))
            (disequal (R0) (R1))
            (check-disequalities)
            (union (L0) (L1))
            (fail (check-disequalities))
        "#;

        for encoding in ENCODINGS {
            let mut egraph = new_experimental_egraph_with_disequality_encoding(encoding);
            egraph
                .parse_and_run_program(None, program)
                .unwrap_or_else(|error| panic!("{encoding:?} failed multiple sorts: {error}"));
        }
    }

    #[test]
    fn all_encodings_regenerate_support_after_pop() {
        let program = r#"
            (datatype Math (A) (B))
            (push)
            (disequal (A) (B))
            (pop)
            (disequal (A) (B))
            (check-disequalities)
        "#;

        for encoding in ENCODINGS {
            let mut egraph = new_experimental_egraph_with_disequality_encoding(encoding);
            egraph
                .parse_and_run_program(None, program)
                .unwrap_or_else(|error| panic!("{encoding:?} failed push/pop: {error}"));
        }
    }

    #[test]
    fn disequality_edges_are_materialized_symmetrically() {
        let mut egraph = new_experimental_egraph_with_disequality_encoding(
            DisequalityEncoding::DisequalityEdges,
        );
        egraph
            .parse_and_run_program(
                None,
                r#"
                (datatype Math (A) (B))
                (disequal (A) (B))
                (check-disequalities)
                "#,
            )
            .unwrap();

        assert_eq!(egraph.get_size(&super::disequality_edge_symbol("Math")), 2);
    }

    #[test]
    fn all_encodings_run_paper_and_artifact_ports() {
        let fixture_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/disequality");
        for fixture in [
            "paper-figure-2.egg",
            "artifact-euf-example.egg",
            "artifact-propel-example.egg",
            "artifact-parameter-shape.egg",
        ] {
            let program = std::fs::read_to_string(fixture_dir.join(fixture)).unwrap();
            for encoding in ENCODINGS {
                let mut egraph = new_experimental_egraph_with_disequality_encoding(encoding);
                egraph
                    .parse_and_run_program(Some(fixture.to_owned()), &program)
                    .unwrap_or_else(|error| panic!("{encoding:?} failed {fixture}: {error}"));
            }
        }
    }

    #[test]
    fn relational_parameter_analysis_composes_with_all_proof_modes() {
        let crate_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
        let program_path = crate_dir.join("benchmarks/disequality/parameter-analysis.egg");
        let program = std::fs::read_to_string(&program_path).unwrap();
        let facts = parameter_analysis_facts();

        for encoding in ENCODINGS {
            let ordinary = new_experimental_egraph_with_disequality_encoding(encoding);
            let term = new_experimental_egraph_for_proofs_with_disequality_encoding(encoding)
                .with_term_encoding_enabled();
            let proof_testing =
                new_experimental_egraph_for_proofs_with_disequality_encoding(encoding)
                    .with_proofs_enabled()
                    .with_proof_testing();
            for (mode, mut egraph) in [
                ("ordinary", ordinary),
                ("term", term),
                ("proof-testing", proof_testing),
            ] {
                egraph.fact_directory = Some(facts.path().to_owned());
                egraph
                    .parse_and_run_program(Some(program_path.display().to_string()), &program)
                    .unwrap_or_else(|error| {
                        panic!("{encoding:?} {mode} failed relational input: {error}")
                    });
                egraph
                    .parse_and_run_program(None, "(check (TermAt 3 (f (N1))))")
                    .unwrap_or_else(|error| {
                        panic!("{encoding:?} {mode} failed reconstructed-term check: {error}")
                    });
            }
        }
    }

    #[test]
    fn parameter_analysis_desugared_snapshots_match_and_replay() {
        let crate_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
        let program_path = crate_dir.join("benchmarks/disequality/parameter-analysis.egg");
        let program = std::fs::read_to_string(&program_path).unwrap();
        let facts = parameter_analysis_facts();

        for encoding in ENCODINGS {
            let mut compiler = new_experimental_egraph_with_disequality_encoding(encoding);
            let resolved = compiler
                .resolve_program(Some(program_path.display().to_string()), &program)
                .unwrap_or_else(|error| panic!("{encoding:?} failed to desugar: {error}"));
            let rendered = sanitize_internal_names(&resolved)
                .into_iter()
                .map(|command| command.to_string() + "\n")
                .collect::<String>();
            let snapshot_path = crate_dir.join(format!(
                "benchmarks/disequality/desugared/{}.egg",
                encoding.cli_name()
            ));
            let snapshot = std::fs::read_to_string(&snapshot_path).unwrap();
            assert_eq!(rendered, snapshot, "stale {} snapshot", encoding.cli_name());

            let mut replay = new_experimental_egraph();
            replay.fact_directory = Some(facts.path().to_owned());
            replay
                .parse_and_run_program(Some(snapshot_path.display().to_string()), &snapshot)
                .unwrap_or_else(|error| panic!("{encoding:?} snapshot failed to replay: {error}"));
            replay
                .parse_and_run_program(None, "(check (TermAt 3 (f (N1))))")
                .unwrap_or_else(|error| {
                    panic!("{encoding:?} snapshot lost reconstructed terms: {error}")
                });
        }
    }

    #[test]
    fn all_encodings_compose_with_term_and_proof_modes() {
        let program = r#"
            (datatype Math (A) (B) (C) (F Math))
            (disequal (F (A)) (F (C)))
            (union (A) (B))
            (check-disequalities)
            (check (= (A) (B)))
            (union (B) (C))
            (fail (check-disequalities))
        "#;

        for encoding in ENCODINGS {
            let mut term_egraph =
                new_experimental_egraph_for_proofs_with_disequality_encoding(encoding)
                    .with_term_encoding_enabled();
            term_egraph
                .parse_and_run_program(None, program)
                .unwrap_or_else(|error| panic!("{encoding:?} failed term encoding: {error}"));

            let mut proof_egraph =
                new_experimental_egraph_for_proofs_with_disequality_encoding(encoding)
                    .with_proofs_enabled()
                    .with_proof_testing();
            proof_egraph
                .parse_and_run_program(None, program)
                .unwrap_or_else(|error| panic!("{encoding:?} failed proof testing: {error}"));
        }
    }
}
