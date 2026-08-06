use super::{Rewrite, Rule};
use crate::ast::{Action, Actions, Expr, Fact};
use crate::command_origin::{
    CommandOriginDisposition, CommandOriginDispositionAt, CommandOriginError, LocalCommandOrigins,
    OriginatedProgram,
};
use crate::frontend_program::{CommandOrigin, GeneratedCommandRole};
use crate::*;
use egglog_ast::span::Span;

/// Desugars a single command, removing syntactic sugar.
pub(crate) fn desugar_command(
    command: Command,
    parser: &mut Parser,
    proof_testing: bool,
) -> Result<Vec<NCommand>, Error> {
    Ok(desugar_command_with_dispositions(command, parser, proof_testing)?.commands)
}

/// Desugar one command and compose its producer-stamped local provenance with
/// the authoritative origin assigned before desugaring.
#[allow(dead_code)] // consumed by the pending compile-only mapper
pub(crate) fn desugar_command_with_origin(
    command: Command,
    parser: &mut Parser,
    proof_testing: bool,
    incoming: &CommandOrigin,
) -> Result<OriginatedProgram<NCommand>, DesugarCommandOriginError> {
    // Origin composition can reject an otherwise valid fanout.  Desugar on a
    // staged parser so such a provenance failure cannot consume fresh names or
    // registration identities before the command forest is admitted whole.
    let mut staged_parser = parser.clone();
    let desugared = desugar_command_with_dispositions(command, &mut staged_parser, proof_testing)?;
    let origins = desugared.origins.compose(&desugared.commands, incoming)?;
    let originated = OriginatedProgram::try_new(desugared.commands, origins)?;
    *parser = staged_parser;
    Ok(originated)
}

/// A failure either from ordinary desugaring or from exact-origin composition.
#[derive(Debug, thiserror::Error)]
pub(crate) enum DesugarCommandOriginError {
    #[error(transparent)]
    Desugar(#[from] Error),
    #[error(transparent)]
    Origin(#[from] CommandOriginError),
}

struct DesugaredCommand {
    commands: Vec<NCommand>,
    origins: LocalCommandOrigins,
}

impl DesugaredCommand {
    fn inherited(command: NCommand) -> Self {
        Self::top_level(vec![command], vec![CommandOriginDisposition::Inherit])
    }

    fn top_level(commands: Vec<NCommand>, dispositions: Vec<CommandOriginDisposition>) -> Self {
        let origins = LocalCommandOrigins::from_top_level(&commands, dispositions)
            .expect("desugar producer emitted an invalid top-level command-origin plan");
        Self { commands, origins }
    }

    fn recursive(
        commands: Vec<NCommand>,
        entries: Vec<CommandOriginDispositionAt>,
        contains_empty_producer: bool,
    ) -> Self {
        let origins = LocalCommandOrigins::try_new_with_empty_producer(
            &commands,
            entries,
            contains_empty_producer,
        )
        .expect("desugar producer emitted an invalid recursive command-origin plan");
        Self { commands, origins }
    }

    fn into_parts(self) -> (Vec<NCommand>, Vec<CommandOriginDispositionAt>, bool) {
        let (origins, contains_empty_producer) = self.origins.into_parts();
        (self.commands, origins, contains_empty_producer)
    }
}

fn generated() -> CommandOriginDisposition {
    CommandOriginDisposition::Generated(GeneratedCommandRole::FrontendDesugaring)
}

fn desugar_command_with_dispositions(
    command: Command,
    parser: &mut Parser,
    proof_testing: bool,
) -> Result<DesugaredCommand, Error> {
    let rule_name = rule_name(&command);
    let res = match command {
        Command::Function {
            span,
            name,
            schema,
            merge,
            hidden,
            let_binding,
            term_constructor,
            unextractable,
            identity_vals,
            cost,
            term_node,
        } => {
            let mut fdecl = FunctionDecl::function(span, name, schema, merge);
            fdecl.internal_hidden = hidden;
            fdecl.internal_let = let_binding;
            fdecl.term_constructor = term_constructor;
            fdecl.identity_vals = identity_vals;
            fdecl.cost = cost;
            fdecl.internal_term_node = term_node;
            // Functions with term_constructor are view tables that should be
            // extractable unless explicitly marked unextractable
            if fdecl.term_constructor.is_some() {
                fdecl.unextractable = unextractable;
            } else if unextractable {
                fdecl.unextractable = true;
            }
            // For regular functions without term_constructor, keep the default
            // unextractable=true from FunctionDecl::function()
            DesugaredCommand::inherited(NCommand::Function(fdecl))
        }
        Command::Constructor {
            span,
            name,
            schema,
            cost,
            unextractable,
            hidden,
            let_binding,
            term_constructor,
        } => {
            let mut fdecl =
                FunctionDecl::constructor(span, name, schema, cost, unextractable, hidden);
            fdecl.internal_let = let_binding;
            fdecl.term_constructor = term_constructor;
            DesugaredCommand::inherited(NCommand::Function(fdecl))
        }
        Command::Relation { span, name, inputs } => desugar_relation(parser, span, name, inputs),
        Command::Datatype {
            span,
            name,
            variants,
        } => desugar_datatype(span, name, variants),
        Command::Datatypes { span: _, datatypes } => {
            // first declare all the datatypes as sorts, then add all explicit sorts which could refer to the datatypes, and finally add all the variants as functions
            let mut res = vec![];
            let mut dispositions = vec![];
            // Capture which source entry owns this producer's sole inherited
            // output before output-order partitioning occurs.
            let datatypes = datatypes
                .into_iter()
                .enumerate()
                .map(|(source_index, datatype)| (source_index == 0, datatype))
                .collect::<Vec<_>>();
            for (inherits_input, datatype) in datatypes.iter() {
                let span = datatype.0.clone();
                let name = datatype.1.clone();
                if let Subdatatypes::Variants(..) = datatype.2 {
                    res.push(NCommand::Sort {
                        span,
                        name,
                        presort_and_args: None,
                        uf: None,
                        proof_func: None,
                        container_rebuild: None,
                        proof_constructors: None,
                        unionable: true,
                    });
                    dispositions.push(if *inherits_input {
                        CommandOriginDisposition::Inherit
                    } else {
                        generated()
                    });
                }
            }
            let (variants_vec, sorts): (Vec<_>, Vec<_>) = datatypes
                .into_iter()
                .partition(|(_, datatype)| matches!(datatype.2, Subdatatypes::Variants(..)));

            for (inherits_input, sort) in sorts {
                let span = sort.0.clone();
                let name = sort.1;
                let Subdatatypes::NewSort(sort, args) = sort.2 else {
                    unreachable!()
                };
                res.push(NCommand::Sort {
                    span,
                    name,
                    presort_and_args: Some((sort, args)),
                    uf: None,
                    proof_func: None,
                    container_rebuild: None,
                    proof_constructors: None,
                    unionable: true,
                });
                dispositions.push(if inherits_input {
                    CommandOriginDisposition::Inherit
                } else {
                    generated()
                });
            }

            for (_, variants) in variants_vec {
                let datatype = variants.1;
                let Subdatatypes::Variants(variants) = variants.2 else {
                    unreachable!();
                };
                for variant in variants {
                    res.push(NCommand::Function(FunctionDecl::constructor(
                        variant.span,
                        variant.name,
                        Schema {
                            input: variant.types,
                            outputs: vec![datatype.clone()],
                        },
                        variant.cost,
                        false,
                        false,
                    )));
                    dispositions.push(generated());
                }
            }

            DesugaredCommand::top_level(res, dispositions)
        }
        Command::Rewrite(ruleset, rewrite, subsume) => {
            let resolved_name = if rewrite.name.is_empty() {
                rule_name
            } else {
                rewrite.name.clone()
            };
            let commands = desugar_rewrite(ruleset, resolved_name, rewrite, subsume, parser);
            DesugaredCommand::top_level(commands, vec![CommandOriginDisposition::Inherit])
        }
        Command::BiRewrite(ruleset, rewrite) => {
            desugar_birewrite(ruleset, rule_name, rewrite, parser)
        }
        Command::Include(_span, _file) => {
            unreachable!("Include commands should be expanded before desugaring")
        }
        Command::Rule { mut rule } => {
            if rule.name.is_empty() {
                // format rule and use it as the name
                rule.name = rule_name;
            }
            DesugaredCommand::inherited(NCommand::NormRule { rule })
        }
        Command::Sort {
            span,
            name,
            presort_and_args,
            uf,
            proof_func,
            container_rebuild,
            proof_constructors,
            unionable,
        } => DesugaredCommand::inherited(NCommand::Sort {
            span,
            name,
            presort_and_args,
            uf,
            proof_func,
            container_rebuild,
            proof_constructors,
            unionable,
        }),
        Command::Index {
            span,
            name,
            function,
            any_of,
        } => DesugaredCommand::inherited(NCommand::Index {
            span,
            name,
            function,
            any_of,
            resolution: None,
        }),
        Command::AddRuleset(span, name) => {
            DesugaredCommand::inherited(NCommand::AddRuleset(span, name))
        }
        Command::UnstableCombinedRuleset(span, name, subrulesets) => {
            DesugaredCommand::inherited(NCommand::UnstableCombinedRuleset(span, name, subrulesets))
        }
        Command::Action(action) => DesugaredCommand::inherited(NCommand::CoreAction(action)),
        Command::Actions(actions) => DesugaredCommand::inherited(NCommand::CoreActions(actions)),
        Command::LetBegin(span, name, actions) => {
            DesugaredCommand::inherited(NCommand::LetBegin(span, name, actions))
        }
        Command::RunSchedule(sched) => {
            DesugaredCommand::inherited(NCommand::RunSchedule(sched.clone()))
        }
        Command::PrintOverallStatistics(span, file) => {
            DesugaredCommand::inherited(NCommand::PrintOverallStatistics(span, file.clone()))
        }
        Command::Extract(span, expr, variants) => {
            DesugaredCommand::inherited(NCommand::Extract(span, expr, variants))
        }
        Command::Check(span, facts) => {
            if proof_testing {
                desugar_prove(parser, span.clone(), facts.clone())
            } else {
                DesugaredCommand::inherited(NCommand::Check(span, facts))
            }
        }
        Command::PrintFunction(span, symbol, size, file, mode) => {
            DesugaredCommand::inherited(NCommand::PrintFunction(span, symbol, size, file, mode))
        }
        Command::PrintSize(span, symbol) => {
            DesugaredCommand::inherited(NCommand::PrintSize(span, symbol))
        }
        Command::Output { span, file, exprs } => {
            DesugaredCommand::inherited(NCommand::Output { span, file, exprs })
        }
        Command::Push(num) => DesugaredCommand::inherited(NCommand::Push(num)),
        Command::Pop(span, num) => DesugaredCommand::inherited(NCommand::Pop(span, num)),
        Command::Fail(span, cmds) => {
            // Desugar every wrapped command and wrap the whole flattened result in
            // one `fail`, so the assertion covers all of them.
            let mut desugared = vec![];
            let mut dispositions = vec![CommandOriginDispositionAt {
                command_path: vec![0],
                disposition: CommandOriginDisposition::Inherit,
            }];
            let mut contains_empty_producer = false;
            for cmd in cmds {
                let child = desugar_command_with_dispositions(cmd, parser, proof_testing)?;
                let offset = desugared.len();
                let (child_commands, child_dispositions, child_contains_empty_producer) =
                    child.into_parts();
                contains_empty_producer |= child_contains_empty_producer;
                for mut disposition in child_dispositions {
                    let top = disposition
                        .command_path
                        .first_mut()
                        .expect("validated child command-origin paths are nonempty");
                    *top += offset;
                    disposition.command_path.insert(0, 0);
                    dispositions.push(disposition);
                }
                desugared.extend(child_commands);
            }
            DesugaredCommand::recursive(
                vec![NCommand::Fail(span, desugared)],
                dispositions,
                contains_empty_producer,
            )
        }
        Command::Input { span, name, file } => {
            DesugaredCommand::inherited(NCommand::Input { span, name, file })
        }
        Command::UserDefined(span, name, args) => {
            DesugaredCommand::inherited(NCommand::UserDefined(span, name, args))
        }
        Command::Prove(span, query) => desugar_prove(parser, span, query),
        Command::ProveExists(span, constructor) => {
            DesugaredCommand::inherited(NCommand::ProveExists(span, constructor))
        }
    };

    Ok(res)
}

/// Desugars a `prove` command into egglog commands.
/// For example, `(prove (= a b))` becomes:
/// ```text
/// (sort ExistsSort)
/// (function ExistsConstructor () ExistsSort)
/// (ruleset exists)
/// (rule ((= a b))
///       ((ExistsConstructor))
///       :ruleset exists
///       :name "prove_exists_rule")
/// (run exists)
/// (prove-exists ExistsConstructor)
/// ```
/// This creates a fresh constructor that can only be created if the query holds.
/// Then `prove-exists` extracts a proof that the constructor exists.
fn desugar_prove(parser: &mut Parser, span: Span, query: Vec<Fact>) -> DesugaredCommand {
    let fresh_sort = parser.symbol_gen.fresh("ExistsSort");
    let constructor_name = parser.symbol_gen.fresh("ExistsConstructor");
    let ruleset = parser.symbol_gen.fresh("exists");
    let name = parser.symbol_gen.fresh("prove_exists_rule");
    let commands = vec![
        NCommand::Sort {
            span: span.clone(),
            name: fresh_sort.clone(),
            presort_and_args: None,
            uf: None,
            proof_func: None,
            container_rebuild: None,
            proof_constructors: None,
            unionable: false,
        },
        NCommand::Function(FunctionDecl::constructor(
            span.clone(),
            constructor_name.clone(),
            Schema {
                input: vec![],
                outputs: vec![fresh_sort.clone()],
            },
            None,
            false,
            true, // hidden - internal to prove desugaring
        )),
        NCommand::AddRuleset(span.clone(), ruleset.clone()),
        // rule that constructs the new constructor
        NCommand::NormRule {
            rule: Rule {
                span: span.clone(),
                body: query,
                head: Actions::singleton(Action::Expr(
                    span.clone(),
                    Expr::Call(span.clone(), constructor_name.clone(), vec![]),
                )),
                ruleset: ruleset.clone(),
                name,
                eval_mode: RuleEvalMode::Seminaive,
                no_decomp: false,
                include_subsumed: false,
            },
        },
        // run the rule
        NCommand::RunSchedule(GenericSchedule::Run(
            span.clone(),
            GenericRunConfig {
                ruleset,
                until: None,
            },
        )),
        // get a proof for the constructor
        NCommand::ProveExists(span, constructor_name),
    ];
    DesugaredCommand::top_level(
        commands,
        vec![
            generated(),
            generated(),
            generated(),
            generated(),
            generated(),
            CommandOriginDisposition::Inherit,
        ],
    )
}

fn desugar_datatype(span: Span, name: String, variants: Vec<Variant>) -> DesugaredCommand {
    let commands = vec![NCommand::Sort {
        span: span.clone(),
        name: name.clone(),
        presort_and_args: None,
        uf: None,
        proof_func: None,
        container_rebuild: None,
        proof_constructors: None,
        unionable: true,
    }]
    .into_iter()
    .chain(variants.into_iter().map(|variant| {
        NCommand::Function(FunctionDecl::constructor(
            variant.span,
            variant.name,
            Schema {
                input: variant.types,
                outputs: vec![name.clone()],
            },
            variant.cost,
            variant.unextractable,
            false,
        ))
    }))
    .collect::<Vec<_>>();
    let dispositions = std::iter::once(CommandOriginDisposition::Inherit)
        .chain((1..commands.len()).map(|_| generated()))
        .collect();
    DesugaredCommand::top_level(commands, dispositions)
}

fn desugar_rewrite(
    ruleset: String,
    name: String,
    rewrite: Rewrite,
    subsume: bool,
    parser: &mut Parser,
) -> Vec<NCommand> {
    let span = rewrite.span.clone();
    let var = parser.symbol_gen.fresh("rewrite_var__");
    let mut head = Actions::singleton(Action::Union(
        span.clone(),
        Expr::Var(span.clone(), var.clone()),
        rewrite.rhs.clone(),
    ));
    if subsume {
        match &rewrite.lhs {
            Expr::Call(_, f, args) => {
                head.0.push(Action::Change(
                    span.clone(),
                    Change::Subsume,
                    f.clone(),
                    args.to_vec(),
                ));
            }
            _ => {
                panic!("Subsumed rewrite must have a function call on the lhs");
            }
        }
    }
    // make two rules- one to insert the rhs, and one to union
    // this way, the union rule can only be fired once,
    // which helps proofs not add too much info
    vec![NCommand::NormRule {
        rule: Rule {
            span: span.clone(),
            body: [Fact::Eq(
                span.clone(),
                Expr::Var(span, var),
                rewrite.lhs.clone(),
            )]
            .into_iter()
            .chain(rewrite.conditions.clone())
            .collect(),
            head,
            ruleset,
            name,
            eval_mode: RuleEvalMode::Seminaive,
            no_decomp: false,
            include_subsumed: false,
        },
    }]
}

fn desugar_birewrite(
    ruleset: String,
    name: String,
    rewrite: Rewrite,
    parser: &mut Parser,
) -> DesugaredCommand {
    let span = rewrite.span.clone();
    let rewrite_name = if rewrite.name.is_empty() {
        name
    } else {
        rewrite.name.clone()
    };
    let rw2 = Rewrite {
        span,
        lhs: rewrite.rhs.clone(),
        rhs: rewrite.lhs.clone(),
        conditions: rewrite.conditions.clone(),
        name: rewrite_name.clone(),
    };
    let commands = desugar_rewrite(
        ruleset.clone(),
        format!("{rewrite_name}=>"),
        rewrite,
        false,
        parser,
    )
    .into_iter()
    .chain(desugar_rewrite(
        ruleset,
        format!("{rewrite_name}<="),
        rw2,
        false,
        parser,
    ))
    .collect::<Vec<_>>();
    DesugaredCommand::top_level(
        commands,
        vec![CommandOriginDisposition::Inherit, generated()],
    )
}

/// Desugar relation by making a new sort and a constructor for it.
/// The sort is marked as non-unionable since relations don't support union.
fn desugar_relation(
    parser: &mut Parser,
    span: Span,
    name: String,
    inputs: Vec<String>,
) -> DesugaredCommand {
    let dashes_removed = name.replace('-', "");
    let fresh_sort = parser.symbol_gen.fresh(&format!("{dashes_removed}Sort"));
    let commands = vec![
        NCommand::Sort {
            span: span.clone(),
            name: fresh_sort.clone(),
            presort_and_args: None,
            uf: None,
            proof_func: None,
            container_rebuild: None,
            proof_constructors: None,
            unionable: false,
        },
        NCommand::Function(FunctionDecl::constructor(
            span,
            name,
            Schema {
                input: inputs,
                outputs: vec![fresh_sort],
            },
            None,
            false,
            false,
        )),
    ];
    DesugaredCommand::top_level(
        commands,
        vec![generated(), CommandOriginDisposition::Inherit],
    )
}

pub fn rule_name<Head, Leaf>(command: &GenericCommand<Head, Leaf>) -> String
where
    Head: Clone + Display,
    Leaf: Clone + PartialEq + Eq + Hash + Display,
{
    command.to_string().replace('\"', "'")
}

#[cfg(test)]
mod tests {
    use crate::command_origin::CommandOriginAt;
    use crate::frontend_program::{SourceGroupId, SourceSubcommandId, SourceSubcommandRef};

    use super::*;

    fn source_ref() -> SourceSubcommandRef {
        SourceSubcommandRef::new(SourceGroupId::new(7), SourceSubcommandId::new(3))
    }

    fn source_origin() -> CommandOrigin {
        CommandOrigin::Source(source_ref())
    }

    fn parse_one(parser: &mut Parser, source: &str) -> Command {
        let commands = parser.get_program_from_string(None, source).unwrap();
        let [command] = commands.as_slice() else {
            panic!("expected one parsed command, found {commands:?}")
        };
        command.clone()
    }

    fn desugar_source(
        source: &str,
        proof_testing: bool,
        incoming: &CommandOrigin,
    ) -> (Vec<NCommand>, Vec<CommandOriginAt>) {
        let mut parser = Parser::default();
        let command = parse_one(&mut parser, source);
        let originated =
            desugar_command_with_origin(command, &mut parser, proof_testing, incoming).unwrap();
        (
            originated.commands().to_vec(),
            originated.origins().as_slice().to_vec(),
        )
    }

    fn assert_source_pattern(origins: &[CommandOriginAt], expected: &[(&[usize], bool)]) {
        assert_eq!(origins.len(), expected.len());
        for (origin, (path, inherited)) in origins.iter().zip(expected) {
            assert_eq!(origin.command_path, *path);
            if *inherited {
                assert_eq!(origin.origin, source_origin());
            } else {
                assert_eq!(
                    origin.origin,
                    CommandOrigin::Generated {
                        trigger: Some(source_ref()),
                        role: GeneratedCommandRole::FrontendDesugaring,
                    }
                );
            }
        }
    }

    #[test]
    fn command_origin_producer_matrix_is_explicit() {
        let cases: &[(&str, bool, &[bool])] = &[
            ("(sort S)", false, &[true]),
            ("(relation edge (i64 i64))", false, &[false, true]),
            ("(datatype D (MkD i64))", false, &[true, false]),
            ("(birewrite (left x) (right x))", false, &[true, false]),
            (
                "(prove (= 1 1))",
                false,
                &[false, false, false, false, false, true],
            ),
            ("(check (= 1 1))", false, &[true]),
            (
                "(check (= 1 1))",
                true,
                &[false, false, false, false, false, true],
            ),
        ];

        for (source, proof_testing, expected) in cases {
            let (_, origins) = desugar_source(source, *proof_testing, &source_origin());
            let expected = expected
                .iter()
                .enumerate()
                .map(|(index, inherited)| (vec![index], *inherited))
                .collect::<Vec<_>>();
            let expected = expected
                .iter()
                .map(|(path, inherited)| (path.as_slice(), *inherited))
                .collect::<Vec<_>>();
            assert_source_pattern(&origins, &expected);
        }
    }

    #[test]
    fn command_origin_datatypes_anchor_is_captured_before_partition() {
        let (commands, origins) = desugar_source(
            "(datatype* (sort A (Vec i64)) (B (MkB)))",
            false,
            &source_origin(),
        );
        let [
            NCommand::Sort { name: first, .. },
            NCommand::Sort { name: second, .. },
            NCommand::Function(constructor),
        ] = commands.as_slice()
        else {
            panic!("unexpected datatype* output: {commands:?}")
        };
        assert_eq!(first, "B");
        assert_eq!(second, "A");
        assert_eq!(constructor.name, "MkB");
        assert_source_pattern(&origins, &[(&[0], false), (&[1], true), (&[2], false)]);
    }

    #[test]
    fn command_origin_recursive_fail_rebases_flattened_child_fanouts() {
        let (_, origins) = desugar_source(
            "(fail (relation r (i64)) (datatype D (MkD)) (fail (birewrite (f x) (g x))))",
            false,
            &source_origin(),
        );
        assert_source_pattern(
            &origins,
            &[
                (&[0], true),
                (&[0, 0], false),
                (&[0, 1], true),
                (&[0, 2], true),
                (&[0, 3], false),
                (&[0, 4], true),
                (&[0, 4, 0], true),
                (&[0, 4, 1], false),
            ],
        );
    }

    #[test]
    fn command_origin_inherit_preserves_generated_role_and_siblings_restamp() {
        let incoming = CommandOrigin::Generated {
            trigger: Some(source_ref()),
            role: GeneratedCommandRole::ProofInstrumentation,
        };
        let (_, origins) = desugar_source("(relation edge (i64))", false, &incoming);
        assert_eq!(origins[0].command_path, [0]);
        assert_eq!(
            origins[0].origin,
            CommandOrigin::Generated {
                trigger: Some(source_ref()),
                role: GeneratedCommandRole::FrontendDesugaring,
            }
        );
        assert_eq!(origins[1].command_path, [1]);
        assert_eq!(origins[1].origin, incoming);
    }

    #[test]
    fn command_origin_source_less_singleton_succeeds_and_fanout_fails_closed() {
        for role in [
            GeneratedCommandRole::FrontendPrelude,
            GeneratedCommandRole::ProofHeader,
        ] {
            let incoming = CommandOrigin::Generated {
                trigger: None,
                role,
            };
            let (_, origins) = desugar_source("(sort S)", false, &incoming);
            assert_eq!(
                origins,
                vec![CommandOriginAt {
                    command_path: vec![0],
                    origin: incoming.clone(),
                }]
            );

            let mut parser = Parser::default();
            let relation = parse_one(&mut parser, "(relation edge (i64))");
            let fresh_before = parser.symbol_gen.clone();
            assert!(matches!(
                desugar_command_with_origin(relation, &mut parser, false, &incoming),
                Err(DesugarCommandOriginError::Origin(
                    CommandOriginError::GeneratedWithoutTrigger {
                        command_path,
                        role: GeneratedCommandRole::FrontendDesugaring,
                    }
                )) if command_path == [0]
            ));
            assert_eq!(parser.symbol_gen, fresh_before);
        }
    }

    #[test]
    fn command_origin_empty_datatypes_rejects_top_level_and_nested_composition() {
        let mut parser = Parser::default();
        let empty = parse_one(&mut parser, "(datatype*)");
        assert!(
            desugar_command(empty.clone(), &mut parser, false)
                .unwrap()
                .is_empty()
        );
        assert!(matches!(
            desugar_command_with_origin(empty, &mut parser, false, &source_origin()),
            Err(DesugarCommandOriginError::Origin(
                CommandOriginError::UnanchoredEmptyProducer
            ))
        ));

        let nested = parse_one(&mut parser, "(fail (datatype*) (sort S))");
        assert!(matches!(
            desugar_command_with_origin(nested, &mut parser, false, &source_origin()),
            Err(DesugarCommandOriginError::Origin(
                CommandOriginError::UnanchoredEmptyProducer
            ))
        ));
    }

    #[test]
    fn command_origin_aware_api_matches_legacy_output_and_fresh_consumption() {
        let mut source_parser = Parser::default();
        let command = parse_one(&mut source_parser, "(prove (= 1 1))");
        let mut legacy_parser = Parser::default();
        let mut origin_parser = Parser::default();

        let legacy = desugar_command(command.clone(), &mut legacy_parser, false).unwrap();
        let origin_aware =
            desugar_command_with_origin(command, &mut origin_parser, false, &source_origin())
                .unwrap();

        assert_eq!(origin_aware.commands(), legacy);
        assert_eq!(origin_parser.symbol_gen, legacy_parser.symbol_gen);
    }
}
