//! Portable typed lowering for extraction, queries, schedules, and wrappers.
//!
//! These commands deliberately stay separate from declaration and standalone
//! action lowering.  In particular, extraction setup has top-level-global
//! semantics even though it is produced by the action-expression kernel.
//! ProveExists/Input resolve through the encoded-role overlay, while Output
//! preserves the source call shape for its historical generated-frontend pass.

use crate::ast::{
    FunctionSubtype, GenericAction, GenericExpr, GenericRunConfig, GenericSchedule, ResolvedExpr,
    ResolvedSchedule, Span,
};
use crate::core::ResolvedCall;
use crate::proofs::generated_binder::{
    CallKey, FunctionKey, GeneratedBindError, GeneratedCommand, GeneratedExpr,
    GeneratedExtractionStep, GeneratedFact, GeneratedRuleBuilder, GeneratedSchedule,
    GeneratedSignatureCatalog, GeneratedVarRole, SortKey,
};

use super::ProofInstrumentor;
use super::action_direct;
use super::declaration_direct::{EncodedFunctionCatalog, TypedHoistGroup};
use super::source_rule_direct::{self, LoweredQueryFacts};

/// The exact generated maintenance schedule. Every synthesized node inherits
/// the enclosing command or source-schedule span, so direct emission never
/// relies on offsets into ephemeral generated source or on synthetic spans.
pub(super) fn rebuild_schedule(
    instrumentor: &ProofInstrumentor<'_>,
    enclosing_span: &Span,
) -> GeneratedSchedule {
    let names = instrumentor.proof_names();
    let generated = enclosing_span.clone();
    GenericSchedule::Sequence(
        generated.clone(),
        vec![
            GenericSchedule::Saturate(
                generated.clone(),
                Box::new(GenericSchedule::Sequence(
                    generated.clone(),
                    vec![
                        GenericSchedule::Run(
                            generated.clone(),
                            GenericRunConfig {
                                ruleset: names.rebuilding_cleanup_ruleset_name.clone(),
                                until: None,
                            },
                        ),
                        GenericSchedule::Saturate(
                            generated.clone(),
                            Box::new(GenericSchedule::Sequence(
                                generated.clone(),
                                vec![GenericSchedule::Run(
                                    generated.clone(),
                                    GenericRunConfig {
                                        ruleset: names.path_compress_ruleset_name.clone(),
                                        until: None,
                                    },
                                )],
                            )),
                        ),
                        GenericSchedule::Run(
                            generated.clone(),
                            GenericRunConfig {
                                ruleset: names.rebuilding_ruleset_name.clone(),
                                until: None,
                            },
                        ),
                    ],
                )),
            ),
            GenericSchedule::Run(
                generated,
                GenericRunConfig {
                    ruleset: names.subsume_ruleset_name.clone(),
                    until: None,
                },
            ),
        ],
    )
}

/// Lower a Check through the source-rule fact kernel, while making the source
/// discard of query-only lookup actions and premise values explicit here.
pub(super) struct LoweredCheck {
    pub(super) span: Span,
    pub(super) facts: Vec<GeneratedFact>,
}

pub(super) fn lower_check(
    instrumentor: &mut ProofInstrumentor<'_>,
    span: &Span,
    facts: &[crate::ast::ResolvedFact],
) -> LoweredCheck {
    let LoweredQueryFacts {
        facts,
        action_lookups: _discarded_action_lookups,
        premises: _discarded_premises,
    } = source_rule_direct::lower_query_facts(instrumentor, span, facts);
    LoweredCheck {
        span: span.clone(),
        facts,
    }
}

/// Recursively lower schedule queries and preserve the historical rebuild
/// appended after every Run. The outer command driver still appends its own
/// post-command rebuild, yielding the intentional duplicate around a top-level
/// run-schedule.
pub(super) fn lower_schedule(
    instrumentor: &mut ProofInstrumentor<'_>,
    schedule: &ResolvedSchedule,
) -> GeneratedSchedule {
    fn lower_node(
        instrumentor: &mut ProofInstrumentor<'_>,
        schedule: &ResolvedSchedule,
    ) -> GeneratedSchedule {
        match schedule {
            GenericSchedule::Run(span, config) => {
                let until = config.until.as_ref().map(|facts| {
                    let LoweredQueryFacts {
                        facts,
                        action_lookups: _discarded_action_lookups,
                        premises: _discarded_premises,
                    } = source_rule_direct::lower_query_facts(instrumentor, span, facts);
                    facts
                });
                let run = GenericSchedule::Run(
                    span.clone(),
                    GenericRunConfig {
                        ruleset: config.ruleset.clone(),
                        until,
                    },
                );
                GenericSchedule::Sequence(
                    span.clone(),
                    vec![run, rebuild_schedule(instrumentor, span)],
                )
            }
            GenericSchedule::Sequence(span, schedules) => GenericSchedule::Sequence(
                span.clone(),
                schedules
                    .iter()
                    .map(|schedule| lower_node(instrumentor, schedule))
                    .collect(),
            ),
            GenericSchedule::Saturate(span, schedule) => GenericSchedule::Saturate(
                span.clone(),
                Box::new(lower_node(instrumentor, schedule)),
            ),
            GenericSchedule::Repeat(span, count, schedule) => GenericSchedule::Repeat(
                span.clone(),
                *count,
                Box::new(lower_node(instrumentor, schedule)),
            ),
        }
    }

    lower_node(instrumentor, schedule)
}

pub(super) fn register_schedule_signatures(
    schedule: &GeneratedSchedule,
    signatures: &mut GeneratedSignatureCatalog,
) {
    match schedule {
        GenericSchedule::Saturate(_, child) | GenericSchedule::Repeat(_, _, child) => {
            register_schedule_signatures(child, signatures)
        }
        GenericSchedule::Sequence(_, children) => {
            for child in children {
                register_schedule_signatures(child, signatures);
            }
        }
        GenericSchedule::Run(_, config) => {
            if let Some(facts) = &config.until {
                source_rule_direct::register_query_signatures(facts, signatures);
            }
        }
    }
}

/// Lower both extraction operands in one lexical action session, then reclassify
/// each generated Let as a scratch global. The binder expands those scratch
/// entries to hidden nullary Function+Set pairs without registering a FuncType
/// or persistent call-cache entry; non-Let setup actions remain ordered actions.
pub(super) struct ExtractionPlan {
    span: Span,
    lowered: action_direct::LoweredExpressions,
    rebuild: GeneratedSchedule,
}

impl ExtractionPlan {
    /// Register the original lexical expression plan before reclassifying its
    /// Lets as scratch globals, then build the one command consumed by the
    /// extraction expander. Keeping those operations together prevents a
    /// caller from registering only the final values and omitting setup calls.
    pub(super) fn register_and_into_command(
        self,
        signatures: &mut GeneratedSignatureCatalog,
    ) -> GeneratedCommand {
        action_direct::register_expression_signatures(&self.lowered, signatures);
        let action_direct::LoweredExpressions { setup, values } = self.lowered;
        let [expr, variants]: [GeneratedExpr; 2] = values
            .try_into()
            .expect("extraction lowering must return exactly its two operands");
        let setup = setup
            .0
            .into_iter()
            .map(|action| match action {
                GenericAction::Let(span, variable, value) => GeneratedExtractionStep::Scratch(
                    crate::proofs::generated_binder::ExtractionScratch {
                        span,
                        variable,
                        value,
                    },
                ),
                action => GeneratedExtractionStep::Action(action),
            })
            .collect();
        GeneratedCommand::Extraction {
            span: self.span,
            setup,
            rebuild: self.rebuild,
            expr,
            variants,
        }
    }
}

pub(super) fn lower_extraction(
    instrumentor: &mut ProofInstrumentor<'_>,
    span: &Span,
    expr: &ResolvedExpr,
    variants: &ResolvedExpr,
) -> ExtractionPlan {
    let lowered = action_direct::lower_expressions(instrumentor, &[expr, variants]);
    ExtractionPlan {
        span: span.clone(),
        lowered,
        rebuild: rebuild_schedule(instrumentor, span),
    }
}

/// Keep native Input execution separate from `lower_inputs`, which has already
/// materialized the original per-row actions consumed only by the proof checker.
/// Proof-mode native loading writes Fiat rows without mentioning their relation
/// in generated expressions, so this planner returns that typed declaration.
/// The caller queues the group after lowering; the shared pending-declaration
/// boundary registers it exactly once and the outer lexical splice inserts it
/// ahead of the native load.
#[derive(Debug)]
pub(super) struct InputPlan {
    pub(super) fiat: TypedHoistGroup,
    pub(super) command: GeneratedCommand,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct EncodedFunctionRole {
    pub(super) term: FunctionKey,
    pub(super) term_eclass_sort: SortKey,
}

/// Resolve one source spelling through the exact lexical role universe:
/// declarations planned earlier in this batch shadow the persistent catalog,
/// while a missing role fails before Input can claim a Fiat declaration or
/// otherwise mutate generation state. Project only the two fields command
/// lowering consumes; declaration-only view/index metadata stays out of this
/// boundary and is never cloned per wrapper.
pub(super) fn resolve_encoded_function_role(
    span: &Span,
    source_name: &str,
    staged: &EncodedFunctionCatalog,
    persistent: &EncodedFunctionCatalog,
) -> Result<EncodedFunctionRole, GeneratedBindError> {
    let layout = staged
        .by_source
        .get(source_name)
        .or_else(|| persistent.by_source.get(source_name))
        .ok_or_else(|| GeneratedBindError::MissingCatalogSignature {
            kind: "encoded function role",
            name: source_name.to_owned(),
            span: span.clone(),
        })?;
    Ok(EncodedFunctionRole {
        term: layout.term.clone(),
        term_eclass_sort: layout.term_eclass_sort.clone(),
    })
}

pub(super) fn lower_input(
    instrumentor: &mut ProofInstrumentor<'_>,
    span: &Span,
    file: &str,
    role: &EncodedFunctionRole,
) -> InputPlan {
    let fiat = if instrumentor.proofs_enabled() {
        instrumentor
            .plan_fiat_pending_direct(span, role.term_eclass_sort.clone())
            .1
    } else {
        TypedHoistGroup::default()
    };
    InputPlan {
        fiat,
        command: GeneratedCommand::Input {
            span: span.clone(),
            name: role.term.name.clone(),
            file: file.to_owned(),
        },
    }
}

#[derive(Debug)]
pub(super) struct OutputPlan {
    pub(super) span: Span,
    pub(super) file: String,
    pub(super) exprs: Vec<GeneratedExpr>,
}

impl OutputPlan {
    pub(super) fn register_signatures(&self, signatures: &mut GeneratedSignatureCatalog) {
        fn register_expr(expr: &GeneratedExpr, signatures: &mut GeneratedSignatureCatalog) {
            if let GenericExpr::Call(span, call, args) = expr {
                // Source function keys deliberately describe the pre-encoding
                // expression accepted by the first frontend. They are replayed
                // against the encoded TypeInfo, where every such call acquires
                // the source arity error before binding, and therefore must not
                // conflict with the term relation's same-name catalog entry.
                if !matches!(call, CallKey::Function(_)) {
                    signatures
                        .register_call_key(call, span)
                        .expect("output call signatures must be internally consistent");
                }
                for arg in args {
                    register_expr(arg, signatures);
                }
            }
        }

        for expr in &self.exprs {
            register_expr(expr, signatures);
        }
    }
}

struct SourceExprLowerer {
    variables: GeneratedRuleBuilder,
}

impl SourceExprLowerer {
    /// Retain the source-resolved call signature and one portable local
    /// namespace. Output is replayed through the generated frontend unchanged;
    /// using the post-encoding term signature here would replace its historical
    /// TypeError with a binder error.
    fn lower(&mut self, expr: &ResolvedExpr) -> Result<GeneratedExpr, GeneratedBindError> {
        match expr {
            GenericExpr::Lit(span, literal) => Ok(GenericExpr::Lit(span.clone(), literal.clone())),
            GenericExpr::Var(span, variable) => {
                let variable = self.variables.variable(
                    variable.name.clone(),
                    SortKey::from_sort(&variable.sort),
                    if variable.is_global_ref {
                        GeneratedVarRole::Global
                    } else {
                        GeneratedVarRole::Local
                    },
                    span,
                )?;
                Ok(GenericExpr::Var(span.clone(), variable))
            }
            GenericExpr::Call(span, call, args) => {
                let args = args
                    .iter()
                    .map(|arg| self.lower(arg))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(GenericExpr::Call(
                    span.clone(),
                    CallKey::from_resolved(call),
                    args,
                ))
            }
        }
    }
}

/// Output is deliberately not action instrumentation. Its source expressions
/// are replayed and rebound in Full context with their source-resolved shape,
/// matching the source post-encoding typecheck and error boundary.
pub(super) fn lower_output(
    span: &Span,
    file: &str,
    exprs: &[ResolvedExpr],
) -> Result<OutputPlan, GeneratedBindError> {
    let mut lowerer = SourceExprLowerer {
        variables: GeneratedRuleBuilder::default(),
    };
    let exprs = exprs
        .iter()
        .map(|expr| lowerer.lower(expr))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(OutputPlan {
        span: span.clone(),
        file: file.to_owned(),
        exprs,
    })
}

/// Resolve ProveExists to the exact encoded term relation. The generated binder
/// owns the subsequent Read-context resolution and its frontend diagnostics.
#[derive(Debug)]
pub(super) struct ProveExistsPlan {
    pub(super) span: Span,
    pub(super) function: FunctionKey,
}

pub(super) fn lower_prove_exists(
    span: &Span,
    call: &ResolvedCall,
    staged: &EncodedFunctionCatalog,
    persistent: &EncodedFunctionCatalog,
) -> Result<ProveExistsPlan, GeneratedBindError> {
    let ResolvedCall::Func(function) = call else {
        return Err(GeneratedBindError::InternalInvariant {
            message: "source ProveExists did not resolve to a function",
            span: span.clone(),
        });
    };
    let role = resolve_encoded_function_role(span, &function.name, staged, persistent)?;
    Ok(ProveExistsPlan {
        span: span.clone(),
        function: role.term,
    })
}

/// Preserve the source universe boundary for PrintSize. Only a constructor
/// already committed in the live encoded TypeInfo maps to its FD view; a
/// same-surface declaration exists only in original TypeInfo while planning,
/// so its source/term spelling remains unchanged.
pub(super) fn lower_print_size(
    instrumentor: &mut ProofInstrumentor<'_>,
    span: &Span,
    source_name: Option<&str>,
) -> GeneratedCommand {
    let name = source_name.map(|source_name| {
        if instrumentor
            .egraph
            .type_info
            .get_func_type(source_name)
            .is_some_and(|function| function.subtype == FunctionSubtype::Constructor)
        {
            instrumentor.view_name(source_name)
        } else {
            source_name.to_owned()
        }
    });
    GeneratedCommand::PrintSize(span.clone(), name)
}
