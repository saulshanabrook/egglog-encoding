//! Disequality as ordinary rules and relations, before term/proof encoding.
//!
//! NE detects a self-edge after congruence; EE implements the paper's five-rule
//! equality embedding. Neither changes union-find or infers new inequalities
//! from missing equalities. The private rules run only at `check-contradiction`.

use std::{collections::BTreeMap, str::FromStr, sync::Arc};

use egglog::{
    ArcSort, CommandMacro, Context, EGraph, Error, TypeError, TypeInfo,
    ast::{
        Action, Actions, Command, Expr, Fact, Macro, ParseError, Parser, Rule, RuleEvalMode,
        RunConfig, Schedule, Schema, Sexp, Span,
    },
    util::{FreshGen, SymbolGen},
};

const PLACEHOLDER: &str = "@disequal";
const RULESET: &str = "@disequality";
const CONTRADICTION: &str = "@disequality-contradiction";
const TRUTH: &str = "@disequality-truth";
const TRUE: &str = "@disequality-true";
const FALSE: &str = "@disequality-false";

/// Encodings from Dis-Equality Graphs, with a relation for NE's private terms.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum DisequalityEncoding {
    /// A private relation per equality sort; a self-edge derives contradiction.
    #[default]
    Nee,
    /// Equality embedding into a private truth sort (the paper's five rules).
    Ee,
}

impl FromStr for DisequalityEncoding {
    type Err = String;

    fn from_str(value: &str) -> Result<Self, Self::Err> {
        match value {
            "nee" => Ok(Self::Nee),
            "ee" => Ok(Self::Ee),
            _ => Err(format!(
                "unknown disequality encoding `{value}`; expected nee or ee"
            )),
        }
    }
}

/// Install syntax and its lowering pass before enabling term/proof encoding.
/// Call once on a fresh graph; the encoding is fixed for that graph.
pub(crate) fn add_disequality_support(egraph: &mut EGraph, encoding: DisequalityEncoding) {
    egraph.parser.add_action_macro(Arc::new(Disequal));
    egraph
        .parser
        .add_command_macro(Arc::new(CheckContradiction));
    egraph
        .command_macros_mut()
        .register(Arc::new(LowerDisequality(encoding)));
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

struct LowerDisequality(DisequalityEncoding);

impl CommandMacro for LowerDisequality {
    fn transform(
        &self,
        command: Command,
        symbols: &mut SymbolGen,
        types: &TypeInfo,
    ) -> Result<Vec<Command>, Error> {
        let expanded = crate::fresh_macro::FreshMacro::new().transform(command, symbols, types)?;
        let needs_inference = expanded
            .iter()
            .any(|c| matches!(c, Command::Rule { rule } if contains_disequal(&rule.head)));
        let mut local_types = std::borrow::Cow::Borrowed(types);
        let mut result = Vec::new();
        for command in expanded {
            // FreshMacro emits a constructor before its rule. Make that signature
            // visible to this pass without installing anything in the live graph.
            if needs_inference
                && let Command::Constructor {
                    span,
                    name,
                    schema,
                    cost,
                    unextractable,
                    hidden,
                    let_binding,
                } = &command
            {
                let mut declaration = egglog::ast::FunctionDecl::constructor(
                    span.clone(),
                    name.clone(),
                    schema.clone(),
                    *cost,
                    *unextractable,
                    *hidden,
                );
                declaration.internal_let = *let_binding;
                local_types
                    .to_mut()
                    .typecheck_function(symbols, &declaration)?;
                result.push(command);
            } else {
                result.extend(self.lower(command, symbols, &local_types)?);
            }
        }
        Ok(result)
    }
}

impl LowerDisequality {
    fn lower(
        &self,
        mut command: Command,
        symbols: &mut SymbolGen,
        types: &TypeInfo,
    ) -> Result<Vec<Command>, Error> {
        let mut sorts = BTreeMap::new();
        let mut support_span = None;
        self.lower_command(&mut command, symbols, types, &mut sorts, &mut support_span)?;
        let Some(span) = support_span else {
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
        if self.0 == DisequalityEncoding::Ee
            && !sorts.is_empty()
            && types.get_sort_by_name(TRUTH).is_none()
        {
            commands.push(Command::Sort {
                span: span.clone(),
                name: TRUTH.into(),
                presort_and_args: None,
                uf: None,
                container_rebuild: None,
                proof_constructors: None,
                unionable: true,
            });
            commands.push(constructor(&span, TRUE.into(), vec![], TRUTH));
            commands.push(constructor(&span, FALSE.into(), vec![], TRUTH));
            commands.push(rule(
                &span,
                "truth-conflict".into(),
                vec![Fact::Eq(
                    span.clone(),
                    Expr::Call(span.clone(), TRUE.into(), vec![]),
                    Expr::Call(span.clone(), FALSE.into(), vec![]),
                )],
                vec![Action::Expr(
                    span.clone(),
                    Expr::Call(span.clone(), CONTRADICTION.into(), vec![]),
                )],
            ));
            commands.extend(equality_rules(&span, TRUTH));
        }
        for (sort, span) in sorts {
            let name = match self.0 {
                DisequalityEncoding::Nee => format!("@disequality-ne-{sort}"),
                DisequalityEncoding::Ee => equality_name(&sort),
            };
            if types.get_func_type(&name).is_some() {
                continue;
            }
            match self.0 {
                DisequalityEncoding::Nee => {
                    commands.push(Command::Relation {
                        span: span.clone(),
                        name: name.clone(),
                        inputs: vec![sort.clone(), sort.clone()],
                    });
                    let x = Expr::Var(span.clone(), "x".into());
                    commands.push(rule(
                        &span,
                        format!("ne-self-{sort}"),
                        vec![Fact::Fact(Expr::Call(
                            span.clone(),
                            name,
                            vec![x.clone(), x],
                        ))],
                        vec![Action::Expr(
                            span.clone(),
                            Expr::Call(span.clone(), CONTRADICTION.into(), vec![]),
                        )],
                    ));
                }
                DisequalityEncoding::Ee => commands.extend(equality_rules(&span, &sort)),
            }
        }
        // Proof history survives pop, so a reinstalled rule needs a fresh identity.
        for generated in &mut commands {
            if let Command::Rule { rule } = generated {
                rule.name = symbols.fresh(&rule.name);
            }
        }
        commands.push(command);
        Ok(commands)
    }
}

impl LowerDisequality {
    fn lower_command(
        &self,
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
                for (action, typed) in rule.head.0.iter_mut().zip(resolved.head.0) {
                    if let Action::Expr(span, Expr::Call(_, head, args)) = action
                        && head == PLACEHOLDER
                    {
                        let egglog::ast::GenericAction::Union(_, lhs, _) = typed else {
                            unreachable!()
                        };
                        let sort = match lhs {
                            egglog::ast::ResolvedExpr::Var(_, var) => var.sort,
                            egglog::ast::ResolvedExpr::Call(_, call, _) => call.output().clone(),
                            egglog::ast::ResolvedExpr::Lit(_, literal) => {
                                egglog::sort::literal_sort(&literal)
                            }
                        };
                        if !sort.is_eq_sort() {
                            return Err(TypeError::NonEqsortUnion(sort, span.clone()).into());
                        }
                        if !types.is_sort_unionable(&sort) {
                            return Err(TypeError::NonUnionableSort(sort, span.clone()).into());
                        }
                        sorts.insert(sort.name().into(), span.clone());
                        *action = self.encoded_action(span, args, sort.name());
                    }
                }
            }
            Command::Action(Action::Expr(_, Expr::Call(_, head, _))) if head == PLACEHOLDER => {
                let Command::Action(action) = command else {
                    unreachable!()
                };
                let mut actions = Actions::singleton(action.clone());
                self.lower_actions(&mut actions, vec![], symbols, types, sorts)?;
                *action = actions.0.remove(0);
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
                let bindings = resolved
                    .0
                    .into_iter()
                    .filter_map(|action| match action {
                        egglog::ast::GenericAction::Let(span, var, _) => {
                            Some((var.name, span, var.sort))
                        }
                        _ => None,
                    })
                    .collect();
                self.lower_actions(actions, bindings, symbols, types, sorts)?;
            }
            Command::Fail(_, commands) => {
                for command in commands {
                    self.lower_command(command, symbols, types, sorts, support_span)?;
                }
            }
            Command::RunSchedule(Schedule::Saturate(span, schedule)) if matches!(schedule.as_ref(), Schedule::Run(_, config) if config.ruleset == RULESET) =>
            {
                *support_span = Some(span.clone());
            }
            _ => {}
        }
        if let Some(span) = sorts.values().next() {
            *support_span = Some(span.clone());
        }
        Ok(())
    }

    fn lower_actions(
        &self,
        actions: &mut Actions,
        bindings: Vec<(String, Span, ArcSort)>,
        symbols: &mut SymbolGen,
        types: &TypeInfo,
        sorts: &mut BTreeMap<String, Span>,
    ) -> Result<(), Error> {
        for action in &mut actions.0 {
            match action {
                Action::Expr(span, Expr::Call(_, head, args)) if head == PLACEHOLDER => {
                    let [lhs, rhs] = args.as_slice() else {
                        unreachable!("parser checks disequal arity")
                    };
                    let left = operand_sort(types, symbols, lhs, &bindings)?;
                    let right = operand_sort(types, symbols, rhs, &bindings)?;
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
                    *action = self.encoded_action(span, args, left.name());
                }
                _ => {}
            }
        }
        Ok(())
    }

    fn encoded_action(&self, span: &Span, args: &[Expr], sort: &str) -> Action {
        match self.0 {
            DisequalityEncoding::Nee => Action::Expr(
                span.clone(),
                Expr::Call(
                    span.clone(),
                    format!("@disequality-ne-{sort}"),
                    args.to_vec(),
                ),
            ),
            DisequalityEncoding::Ee => Action::Union(
                span.clone(),
                Expr::Call(span.clone(), equality_name(sort), args.to_vec()),
                Expr::Call(span.clone(), FALSE.into(), vec![]),
            ),
        }
    }
}

/// Use union's operand constraints without ever executing the inferred action.
fn union_probe(actions: &Actions) -> Actions {
    egglog::ast::GenericActions(
        actions
            .0
            .iter()
            .map(|action| match action {
                Action::Expr(span, Expr::Call(_, head, args)) if head == PLACEHOLDER => {
                    Action::Union(span.clone(), args[0].clone(), args[1].clone())
                }
                _ => action.clone(),
            })
            .collect(),
    )
}

/// Declared calls already determine their result sort. Avoid solving the full
/// expression twice; the emitted action still validates all argument types.
fn operand_sort(
    types: &TypeInfo,
    symbols: &mut SymbolGen,
    expr: &Expr,
    bindings: &[(String, Span, ArcSort)],
) -> Result<ArcSort, TypeError> {
    let declared = match expr {
        Expr::Var(_, name) => bindings
            .iter()
            .find_map(|(n, _, s)| (n == name).then_some(s))
            .or_else(|| types.get_global_sort(name)),
        Expr::Call(_, head, _) if !types.is_primitive(head) => {
            types.get_func_type(head).map(|f| f.output())
        }
        _ => None,
    };
    match declared {
        Some(sort) => Ok(sort.clone()),
        None => types.infer_expr_sort(symbols, expr, bindings, Context::Full),
    }
}

fn contains_disequal(actions: &Actions) -> bool {
    actions
        .0
        .iter()
        .any(|a| matches!(a, Action::Expr(_, Expr::Call(_, head, _)) if head == PLACEHOLDER))
}

fn equality_name(sort: &str) -> String {
    if sort == TRUTH {
        "@disequality-eq".into()
    } else {
        format!("@disequality-eq-{sort}")
    }
}

fn constructor(span: &Span, name: String, input: Vec<String>, output: &str) -> Command {
    Command::Constructor {
        span: span.clone(),
        name,
        schema: Schema::new(input, output.into()),
        cost: None,
        unextractable: true,
        hidden: true,
        let_binding: false,
    }
}

fn rule(span: &Span, name: String, body: Vec<Fact>, head: Vec<Action>) -> Command {
    Command::Rule {
        rule: Rule {
            span: span.clone(),
            name: format!("@disequality-{name}"),
            ruleset: RULESET.into(),
            body,
            head: Actions::new(head),
            eval_mode: RuleEvalMode::Seminaive,
            no_decomp: false,
            include_subsumed: false,
        },
    }
}

fn equality_rules(span: &Span, sort: &str) -> Vec<Command> {
    let eq = equality_name(sort);
    let x = Expr::Var(span.clone(), "x".into());
    let y = Expr::Var(span.clone(), "y".into());
    let t = Expr::Call(span.clone(), TRUE.into(), vec![]);
    let f = Expr::Call(span.clone(), FALSE.into(), vec![]);
    let xy = Expr::Call(span.clone(), eq.clone(), vec![x.clone(), y.clone()]);
    vec![
        constructor(span, eq.clone(), vec![sort.into(), sort.into()], TRUTH),
        rule(
            span,
            format!("ee-lift-{sort}"),
            vec![Fact::Eq(span.clone(), xy.clone(), t.clone())],
            vec![Action::Union(span.clone(), x.clone(), y.clone())],
        ),
        rule(
            span,
            format!("ee-symmetry-{sort}"),
            vec![Fact::Eq(span.clone(), xy.clone(), f.clone())],
            vec![Action::Union(
                span.clone(),
                Expr::Call(span.clone(), eq.clone(), vec![y.clone(), x.clone()]),
                f.clone(),
            )],
        ),
        rule(
            span,
            format!("ee-double-negation-{sort}"),
            vec![Fact::Eq(
                span.clone(),
                Expr::Call(
                    span.clone(),
                    equality_name(TRUTH),
                    vec![xy.clone(), f.clone()],
                ),
                f.clone(),
            )],
            vec![Action::Union(span.clone(), x.clone(), y.clone())],
        ),
        rule(
            span,
            format!("ee-reflexive-left-{sort}"),
            vec![Fact::Eq(span.clone(), xy.clone(), f.clone())],
            vec![Action::Union(
                span.clone(),
                Expr::Call(span.clone(), eq.clone(), vec![x.clone(), x]),
                t.clone(),
            )],
        ),
        rule(
            span,
            format!("ee-reflexive-right-{sort}"),
            vec![Fact::Eq(span.clone(), xy, f)],
            vec![Action::Union(
                span.clone(),
                Expr::Call(span.clone(), eq, vec![y.clone(), y]),
                t,
            )],
        ),
    ]
}
