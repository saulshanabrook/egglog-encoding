use crate::proofs::generated_binder::{
    CallKey, GeneratedBatch, GeneratedCommand, GeneratedEntry, GeneratedPhase,
    GeneratedSignatureCatalog,
};
#[doc = include_str!("proof_encoding.md")]
use crate::proofs::proof_encoding_helpers::EncodingNames;
use crate::typechecking::FuncType;
use crate::*;
use std::time::Instant;

mod action_direct;
mod command_direct;
pub(super) mod declaration_direct;
mod source_rule_direct;

/// The source envelope whose generated commands a normalized command inherits.
/// Empty action blocks cannot manufacture a source location, but they emit no
/// instrumentation or pending declarations.
fn enclosing_source_span(command: &ResolvedNCommand) -> Option<&Span> {
    fn action_span(action: &ResolvedAction) -> &Span {
        match action {
            GenericAction::Let(span, ..)
            | GenericAction::Set(span, ..)
            | GenericAction::Change(span, ..)
            | GenericAction::Union(span, ..)
            | GenericAction::Panic(span, ..)
            | GenericAction::Expr(span, ..) => span,
        }
    }

    match command {
        ResolvedNCommand::Sort { span, .. }
        | ResolvedNCommand::Index { span, .. }
        | ResolvedNCommand::Input { span, .. }
        | ResolvedNCommand::Output { span, .. } => Some(span),
        ResolvedNCommand::Function(declaration) => Some(&declaration.span),
        ResolvedNCommand::AddRuleset(span, ..)
        | ResolvedNCommand::UnstableCombinedRuleset(span, ..)
        | ResolvedNCommand::LetBegin(span, ..)
        | ResolvedNCommand::Extract(span, ..)
        | ResolvedNCommand::PrintOverallStatistics(span, ..)
        | ResolvedNCommand::Check(span, ..)
        | ResolvedNCommand::PrintFunction(span, ..)
        | ResolvedNCommand::ProveExists(span, ..)
        | ResolvedNCommand::PrintSize(span, ..)
        | ResolvedNCommand::Pop(span, ..)
        | ResolvedNCommand::Fail(span, ..)
        | ResolvedNCommand::UserDefined(span, ..) => Some(span),
        ResolvedNCommand::NormRule { rule } => Some(&rule.span),
        ResolvedNCommand::CoreAction(action) => Some(action_span(action)),
        ResolvedNCommand::CoreActions(actions) => actions.0.first().map(action_span),
        ResolvedNCommand::RunSchedule(schedule) => Some(match schedule {
            GenericSchedule::Run(span, ..)
            | GenericSchedule::Sequence(span, ..)
            | GenericSchedule::Saturate(span, ..)
            | GenericSchedule::Repeat(span, ..) => span,
        }),
        ResolvedNCommand::Push(span, _) => Some(span),
    }
}

/// How a built term's connector proof `natural = canonical` is named.
#[derive(Clone)]
pub(crate) enum Connector {
    /// A proof node the encoding already minted.
    Node(String),
    /// A rule head's, named by the column of the head's proof (see
    /// [`crate::proofs::proof_head`]), so a row is minted only where the encoding
    /// stores the proof.
    Column(usize),
}

/// A declared index on a function's view, covering the view columns of one
/// eq-sort — its children and its e-class. An `@UF` edge on a term reaches every
/// row mentioning it at any of them.
#[derive(Clone)]
pub(crate) struct ViewIndex {
    pub name: String,
    pub sort_name: String,
}

// TODO refactor so that encoding state is optional on the e-graph, ProofNames not optional on EncodingState. Then we don't have to clone proof names everywhere.
#[derive(Clone)]
pub(crate) struct EncodingState {
    pub uf_parent: HashMap<String, String>,
    /// Maps container sort name -> the name of its registered container-rebuild
    /// primitive (`ContainerRebuild`). Cached so each container sort gets
    /// a single rebuild primitive shared across all functions using it.
    pub container_rebuild_name: HashMap<String, String>,
    /// Maps container sort name -> the name of its registered proof-producing
    /// container-rebuild primitive (`ContainerRebuildProof`). Proof mode only.
    pub container_rebuild_proof_name: HashMap<String, String>,
    /// Function name -> the rebuild indexes declared on its view, one per
    /// distinct eq-sort among the view's columns (see [`ViewIndex`]).
    pub view_index: HashMap<String, Vec<ViewIndex>>,
    pub term_header_added: bool,
    // TODO this is very ugly- we should separate out a typechecking struct
    // since we didn't need an entire e-graph
    // When Some term encoding is enabled.
    pub original_typechecking: Option<Box<EGraph>>,
    pub proofs_enabled: bool,
    pub proof_testing: bool,
    /// Whether extracted proofs are verified.
    pub verify_proofs: bool,
    pub proof_names: EncodingNames,
    /// Source functions whose generated view declaration has committed. This
    /// lives in the pushed/cloned proof state so wrapper role lookup follows
    /// the same scope lifecycle as the encoded TypeInfo it describes.
    pub(super) encoded_functions: declaration_direct::EncodedFunctionCatalog,
    /// Test-only knob: annotate RHS-reading rules `:naive` (the safe
    /// whole-database baseline) instead of `:unsafe-seminaive`, so tests can
    /// assert the two produce the same database.
    pub force_proof_naive: bool,
}

impl EncodingState {
    pub(crate) fn new(symbol_gen: &mut SymbolGen) -> Self {
        Self {
            uf_parent: HashMap::default(),
            container_rebuild_name: HashMap::default(),
            container_rebuild_proof_name: HashMap::default(),
            view_index: HashMap::default(),
            term_header_added: false,
            original_typechecking: None,
            proofs_enabled: false,
            proof_names: EncodingNames::new(symbol_gen),
            encoded_functions: declaration_direct::EncodedFunctionCatalog::default(),
            proof_testing: false,
            verify_proofs: true,
            force_proof_naive: false,
        }
    }
}

/// Thin wrapper around an [`EGraph`] for the term encoding
pub(crate) struct ProofInstrumentor<'a> {
    pub(crate) egraph: &'a mut EGraph,
    /// Portable signatures accumulated in lexical emission order for this
    /// production encoder invocation.
    pub(super) signatures: GeneratedSignatureCatalog,
    /// Declarations the statements written so far need — packed proof
    /// constructors and subsumption scaffolding — to be emitted ahead of the
    /// command using them.
    pending_decls: Vec<declaration_direct::TypedDeclarationEntry>,
    /// Roles declared earlier in this still-unbound batch. Committed roles stay
    /// in EncodingState and are consulted as a fallback, avoiding a deep clone
    /// for every source command; each staged role reaches persistent state only
    /// when its receipt-bearing view declaration binds successfully.
    declaration_overlay: declaration_direct::EncodedFunctionPlanningOverlay,
    /// The normalized command currently being lowered. Shared lowering kernels
    /// read this only to stamp
    /// typed pending declarations with their real source envelope.
    enclosing_source_span: Option<Span>,
}

/// Where a variable a rule body binds gets its reflexive `t = t` proof from: a
/// view atom's row proof states an equality whose right-hand side is the row's
/// term, so every variable that term mentions is reachable from it.
#[derive(Clone, Copy)]
pub(crate) enum Anchor {
    /// The variable is the row term's child at this position.
    Child(usize),
    /// The variable is the row proof's left-hand side.
    Lhs,
}

/// A value a body primitive read out of a container. Nothing in the query names
/// it as a term, but it is a child of whichever of `containers` it came out of,
/// so an anchor for one of those projects it out by term.
#[derive(Clone)]
struct Element {
    containers: Vec<String>,
    /// The value variable the projection anchoring it names.
    value: String,
    /// The `@ProjAll_<Sort>` relation projecting a value of the element's sort.
    proj_all: String,
}

/// What a body variable's anchor is projected out of.
enum Source {
    /// A view row proof the body reads, which mentions the variable's term.
    Row(String, Anchor),
    /// A container the body read the variable out of.
    Element(Element),
}

/// The reflexive anchors one rule body offers, collected while its facts are
/// instrumented and read once the whole body is walked — a variable's anchor may
/// come from a fact later than the one asking for it.
#[derive(Default)]
pub(crate) struct BodyAnchors {
    /// Value variable -> the row proof it is reachable from, and how.
    supply: HashMap<String, (String, Anchor)>,
    /// Value variable -> the containers it was read out of.
    elements: HashMap<String, Element>,
    /// Value variables the body forces to be equal, so either one's anchor
    /// proves the other reflexive.
    aliases: Vec<(String, String)>,
    /// Anchors asked for, as proof variable and the value it is about.
    requests: Vec<(String, String)>,
}

impl BodyAnchors {
    /// Record that `row_proof`'s equality reaches `value` at `anchor`. The first
    /// atom binding a variable wins; a later one says the same thing.
    fn offer(&mut self, value: &str, row_proof: &str, anchor: Anchor) {
        self.supply
            .entry(value.to_string())
            .or_insert_with(|| (row_proof.to_string(), anchor));
    }

    /// Record that a body primitive read `element` out of a container.
    fn offer_element(&mut self, element: Element) {
        self.elements
            .entry(element.value.clone())
            .or_insert(element);
    }

    /// Record that the body only matches when `left` and `right` hold the same
    /// value, so one anchor serves both.
    fn alias(&mut self, left: &str, right: &str) {
        self.aliases.push((left.to_string(), right.to_string()));
    }

    /// Ask for `value`'s anchor, to be bound to the proof variable `proof`.
    fn request(&mut self, proof: &str, value: &str) {
        self.requests.push((proof.to_string(), value.to_string()));
    }

    /// Where `value`'s anchor comes from, following the body's aliases when the
    /// variable itself is not one an atom reaches. A row proof wins over a
    /// container projection.
    fn resolve(&self, value: &str) -> Option<Source> {
        let mut seen: HashSet<&str> = HashSet::default();
        let mut reached: Vec<&str> = vec![];
        let mut frontier = vec![value];
        while let Some(var) = frontier.pop() {
            if !seen.insert(var) {
                continue;
            }
            reached.push(var);
            for (left, right) in &self.aliases {
                if left == var {
                    frontier.push(right);
                } else if right == var {
                    frontier.push(left);
                }
            }
        }
        let row = reached.iter().find_map(|var| {
            let (row_proof, anchor) = self.supply.get(*var)?;
            Some(Source::Row(row_proof.clone(), *anchor))
        });
        row.or_else(|| {
            reached
                .iter()
                .find_map(|var| Some(Source::Element(self.elements.get(*var)?.clone())))
        })
    }

    /// How `value`'s anchor is reached: the row proof it bottoms out in and how
    /// that row mentions its term, plus the container projections leading back
    /// to `value`, outermost container first.
    fn anchor_chain(&self, value: &str) -> Option<(String, Anchor, Vec<Element>)> {
        match self.resolve(value)? {
            Source::Row(row_proof, anchor) => Some((row_proof, anchor, vec![])),
            Source::Element(element) => {
                let (row_proof, anchor, mut chain) = element
                    .containers
                    .iter()
                    .find_map(|container| self.anchor_chain(container))?;
                chain.push(element);
                Some((row_proof, anchor, chain))
            }
        }
    }
}

impl<'a> ProofInstrumentor<'a> {
    pub(crate) fn new(egraph: &'a mut EGraph) -> Self {
        Self {
            egraph,
            signatures: GeneratedSignatureCatalog::default(),
            pending_decls: vec![],
            declaration_overlay: declaration_direct::EncodedFunctionPlanningOverlay::default(),
            enclosing_source_span: None,
        }
    }

    pub(super) fn queue_pending_declaration_group(
        &mut self,
        group: declaration_direct::TypedHoistGroup,
    ) {
        group.register_signatures(&mut self.signatures);
        self.pending_decls.extend(
            group
                .declarations
                .into_iter()
                .map(declaration_direct::PlannedDeclaration::into_entry),
        );
    }

    pub(super) fn register_inline_declaration_group(
        &mut self,
        group: declaration_direct::TypedHoistGroup,
    ) -> Vec<GeneratedEntry> {
        group.register_signatures(&mut self.signatures);
        if !group.declarations.is_empty() {
            self.egraph.parser.ensure_no_reserved_symbols = true;
        }
        group
            .declarations
            .into_iter()
            .map(declaration_direct::PlannedDeclaration::into_entry)
            .map(|entry| GeneratedEntry::Declaration(Box::new(entry)))
            .collect()
    }

    pub(super) fn queue_packed_declaration(&mut self, span: &Span, columns: usize) -> String {
        let (name, group) = self.plan_packed_pending_direct(span, columns);
        self.queue_pending_declaration_group(group);
        name
    }

    fn plan_declaration_entries(
        &mut self,
        plan: impl FnOnce(
            &mut Self,
            &mut GeneratedSignatureCatalog,
            &mut declaration_direct::EncodedFunctionPlanningOverlay,
        ) -> declaration_direct::TypedHoistGroup,
    ) -> Vec<GeneratedEntry> {
        let mut signatures = std::mem::take(&mut self.signatures);
        let mut overlay = std::mem::take(&mut self.declaration_overlay);
        let group = plan(self, &mut signatures, &mut overlay);
        if !group.declarations.is_empty() {
            self.egraph.parser.ensure_no_reserved_symbols = true;
        }
        self.declaration_overlay = overlay;
        self.signatures = signatures;
        group
            .declarations
            .into_iter()
            .map(declaration_direct::PlannedDeclaration::into_entry)
            .map(|entry| GeneratedEntry::Declaration(Box::new(entry)))
            .collect()
    }

    pub(crate) fn add_term_encoding(
        egraph: &'a mut EGraph,
        program: Vec<ResolvedNCommand>,
    ) -> Result<GeneratedBatch, Error> {
        GeneratedPhase::Signatures.reset();
        let started = Instant::now();
        let mut instrumentor = Self::new(egraph);
        let result = instrumentor.add_term_encoding_helper(program);
        let signatures = GeneratedPhase::Signatures.drain();
        let total = started.elapsed();
        instrumentor.egraph.overall_report.generated_signatures += signatures;
        instrumentor.egraph.overall_report.generated_construct += total.saturating_sub(signatures);
        result.map(|entries| GeneratedBatch { entries })
    }

    pub(crate) fn lower_inputs(
        egraph: &EGraph,
        program: Vec<ResolvedNCommand>,
    ) -> Result<Vec<ResolvedNCommand>, Error> {
        let mut lowered = Vec::with_capacity(program.len());
        for command in program {
            if let ResolvedNCommand::Input { span, name, file } = &command {
                lowered.extend(
                    Self::input_actions(egraph, span, name, file)?
                        .into_iter()
                        .map(ResolvedNCommand::CoreAction),
                );
            } else {
                lowered.push(command);
            }
        }
        Ok(lowered)
    }

    fn input_actions(
        egraph: &EGraph,
        span: &Span,
        name: &str,
        file: &str,
    ) -> Result<Vec<ResolvedAction>, Error> {
        let function_type = egraph
            .proof_state
            .original_typechecking
            .as_ref()
            .and_then(|typechecker| typechecker.type_info.get_func_type(name))
            .unwrap_or_else(|| panic!("Unrecognized function name {name}"))
            .clone();
        let rows =
            EGraph::read_input_file(egraph.fact_directory.as_deref(), &function_type, span, file)?;
        let mut actions = vec![];
        for row in rows {
            let mut expressions = row
                .into_iter()
                .map(|literal| ResolvedExpr::Lit(span.clone(), literal));
            let inputs = expressions
                .by_ref()
                .take(function_type.input.len())
                .collect::<Vec<_>>();
            actions.push(if function_type.subtype == FunctionSubtype::Constructor {
                ResolvedAction::Expr(
                    span.clone(),
                    ResolvedExpr::Call(
                        span.clone(),
                        ResolvedCall::Func(function_type.clone()),
                        inputs,
                    ),
                )
            } else {
                let output = expressions
                    .next()
                    .expect("custom input row must contain its output value");
                ResolvedAction::Set(
                    span.clone(),
                    ResolvedCall::Func(function_type.clone()),
                    inputs,
                    output,
                )
            });
        }
        Ok(actions)
    }

    pub(super) fn output_is_eclass(&self, declaration: &ResolvedFunctionDecl) -> bool {
        declaration.subtype == FunctionSubtype::Constructor || declaration.internal_let
    }

    fn take_pending_decls(&mut self) -> Vec<GeneratedEntry> {
        let pending = std::mem::take(&mut self.pending_decls);
        if !pending.is_empty() {
            self.egraph.parser.ensure_no_reserved_symbols = true;
        }
        pending
            .into_iter()
            .map(|entry| GeneratedEntry::Declaration(Box::new(entry)))
            .collect()
    }

    fn subsume_marker(&mut self, span: &Span, function: &FuncType) -> String {
        if !self
            .egraph
            .proof_state
            .proof_names
            .subsume_declared
            .contains(&function.name)
        {
            self.subsume_scaffolding(span, function);
        }
        self.subsumed_name(&function.name)
    }

    fn instrument_rule(&mut self, rule: &ResolvedRule) -> Vec<GeneratedEntry> {
        let generated = source_rule_direct::lower(self, rule);
        source_rule_direct::register_signatures(&generated, &mut self.signatures);
        vec![GeneratedEntry::Rule(generated)]
    }

    fn term_encode_command(
        &mut self,
        command: &ResolvedNCommand,
        entries: &mut Vec<GeneratedEntry>,
    ) -> Result<(), Error> {
        log::trace!("Term encoding for {command}");
        if let Some(span) = enclosing_source_span(command) {
            self.enclosing_source_span = Some(span.clone());
        }
        match command {
            ResolvedNCommand::Sort {
                span,
                name,
                presort_and_args,
                unionable,
                ..
            } => {
                entries.extend(
                    self.plan_declaration_entries(|instrumentor, catalog, _overlay| {
                        instrumentor.plan_source_sort_direct(
                            catalog,
                            span,
                            name,
                            presort_and_args,
                            *unionable,
                        )
                    }),
                );
            }
            ResolvedNCommand::Function(declaration) => {
                entries.extend(
                    self.plan_declaration_entries(|instrumentor, catalog, overlay| {
                        instrumentor
                            .plan_term_and_view_direct(
                                catalog,
                                overlay,
                                &declaration.span,
                                declaration,
                            )
                            .0
                    }),
                );
                entries.extend(self.rebuilding_rules(declaration));
            }
            ResolvedNCommand::NormRule { rule } => entries.extend(self.instrument_rule(rule)),
            ResolvedNCommand::CoreAction(_) | ResolvedNCommand::CoreActions(_) => {
                let actions: &[ResolvedAction] = match command {
                    ResolvedNCommand::CoreAction(action) => std::slice::from_ref(action),
                    ResolvedNCommand::CoreActions(actions) => &actions.0,
                    _ => unreachable!("guarded by the match arm"),
                };
                if let Some(lowered) = action_direct::lower(self, actions) {
                    action_direct::register_signatures(&lowered, &mut self.signatures);
                    entries.push(GeneratedEntry::Command(Box::new(
                        GeneratedCommand::Actions(lowered),
                    )));
                }
            }
            ResolvedNCommand::LetBegin(..) => {
                unreachable!("LetBegin is removed by remove_globals")
            }
            ResolvedNCommand::Check(span, facts) => {
                let lowered = command_direct::lower_check(self, span, facts);
                source_rule_direct::register_query_signatures(&lowered.facts, &mut self.signatures);
                entries.push(GeneratedEntry::Command(Box::new(GeneratedCommand::Check(
                    lowered.span,
                    lowered.facts,
                ))));
            }
            ResolvedNCommand::RunSchedule(schedule) => {
                let lowered = command_direct::lower_schedule(self, schedule);
                command_direct::register_schedule_signatures(&lowered, &mut self.signatures);
                entries.push(GeneratedEntry::Command(Box::new(
                    GeneratedCommand::Schedule(lowered),
                )));
            }
            ResolvedNCommand::Fail(span, commands) => {
                let mut children = vec![];
                for command in commands {
                    self.term_encode_command(command, &mut children)?;
                }
                entries.push(GeneratedEntry::Fail(span.clone(), children));
            }
            ResolvedNCommand::Input { span, name, file } => {
                let role = command_direct::resolve_encoded_function_role(
                    span,
                    name,
                    &self.declaration_overlay.staged,
                    &self.egraph.proof_state.encoded_functions,
                )?;
                let plan = command_direct::lower_input(self, span, file, &role);
                self.queue_pending_declaration_group(plan.fiat);
                entries.push(GeneratedEntry::Command(Box::new(plan.command)));
            }
            ResolvedNCommand::Extract(span, expr, variants) => {
                let plan = command_direct::lower_extraction(self, span, expr, variants);
                entries.push(GeneratedEntry::Command(Box::new(
                    plan.register_and_into_command(&mut self.signatures),
                )));
            }
            ResolvedNCommand::PrintSize(span, name) => {
                entries.push(GeneratedEntry::Command(Box::new(
                    command_direct::lower_print_size(self, span, name.as_deref()),
                )));
            }
            ResolvedNCommand::AddRuleset(span, name) => {
                entries.push(GeneratedEntry::Command(Box::new(
                    GeneratedCommand::AddRuleset(span.clone(), name.clone()),
                )));
            }
            ResolvedNCommand::UnstableCombinedRuleset(span, name, rulesets) => {
                entries.push(GeneratedEntry::Command(Box::new(
                    GeneratedCommand::CombinedRuleset(span.clone(), name.clone(), rulesets.clone()),
                )));
            }
            ResolvedNCommand::Output { span, file, exprs } => {
                let plan = command_direct::lower_output(span, file, exprs)?;
                plan.register_signatures(&mut self.signatures);
                entries.push(GeneratedEntry::Command(Box::new(
                    GeneratedCommand::Output {
                        span: plan.span,
                        file: plan.file,
                        exprs: plan.exprs,
                    },
                )));
            }
            ResolvedNCommand::PrintOverallStatistics(span, file) => {
                entries.push(GeneratedEntry::Command(Box::new(
                    GeneratedCommand::PrintOverallStatistics(span.clone(), file.clone()),
                )));
            }
            ResolvedNCommand::PrintFunction(span, name, limit, file, mode) => {
                entries.push(GeneratedEntry::Command(Box::new(
                    GeneratedCommand::PrintFunction(
                        span.clone(),
                        name.clone(),
                        *limit,
                        file.clone(),
                        *mode,
                    ),
                )));
            }
            ResolvedNCommand::ProveExists(span, call) => {
                let plan = command_direct::lower_prove_exists(
                    span,
                    call,
                    &self.declaration_overlay.staged,
                    &self.egraph.proof_state.encoded_functions,
                )?;
                self.signatures
                    .register_call_key(&CallKey::Function(plan.function.clone()), &plan.span)?;
                entries.push(GeneratedEntry::Command(Box::new(
                    GeneratedCommand::ProveExists(plan.span, plan.function),
                )));
            }
            ResolvedNCommand::Push(span, count) => {
                entries.push(GeneratedEntry::Command(Box::new(GeneratedCommand::Push(
                    span.clone(),
                    *count,
                ))));
            }
            ResolvedNCommand::Pop(span, count) => {
                entries.push(GeneratedEntry::Command(Box::new(GeneratedCommand::Pop(
                    span.clone(),
                    *count,
                ))));
            }
            ResolvedNCommand::Index { .. } => {
                unreachable!(
                    "proof-support validation must reject source Index declarations before encoding"
                )
            }
            ResolvedNCommand::UserDefined(..) => {
                panic!("User defined commands unsupported in term encoding");
            }
        }
        Ok(())
    }

    fn add_term_encoding_helper(
        &mut self,
        program: Vec<ResolvedNCommand>,
    ) -> Result<Vec<GeneratedEntry>, Error> {
        let mut entries = vec![];

        if !self.egraph.proof_state.term_header_added {
            let header_span = program
                .iter()
                .find_map(enclosing_source_span)
                .cloned()
                .expect("a nonempty instrumented batch has an enclosing source span");
            entries.extend(
                self.plan_declaration_entries(|instrumentor, catalog, _overlay| {
                    instrumentor.plan_term_header_direct(catalog, &header_span)
                }),
            );
            if self.egraph.proof_state.proofs_enabled {
                entries.extend(
                    self.plan_declaration_entries(|instrumentor, catalog, _overlay| {
                        instrumentor.plan_proof_header_direct(catalog, &header_span)
                    }),
                );
            }
            self.egraph.proof_state.term_header_added = true;
        }

        if self.egraph.proof_state.proofs_enabled {
            entries.extend(
                self.plan_declaration_entries(|instrumentor, catalog, _overlay| {
                    instrumentor.plan_rule_arity_header_direct(catalog, &program)
                }),
            );
        }

        for command in program {
            let at = entries.len();
            self.term_encode_command(&command, &mut entries)?;
            entries.splice(at..at, self.take_pending_decls());

            if !command_skips_rebuild(&command) {
                let span = enclosing_source_span(&command)
                    .cloned()
                    .expect("an instrumented command has an enclosing source span");
                entries.push(GeneratedEntry::Command(Box::new(
                    GeneratedCommand::Schedule(command_direct::rebuild_schedule(self, &span)),
                )));
            }
        }

        Ok(entries)
    }
}

/// Whether no maintenance rebuild is needed after `command`.
///
/// Declarations (sorts, functions, rules) run no actions. A `set` (including a
/// global-let's `(set (g) e)`), a `let`, or a top-level expression over
/// non-container sorts builds and dedups terms via `set-if-empty` without
/// merging e-classes or deferring work, so no maintenance rebuild is needed
/// after it — this is what stops N global-let `set`s from each triggering a
/// rebuild (quadratic). A block skips when all of its actions do.
/// Everything else still rebuilds: `union` merges e-classes, `subsume` defers
/// work to the maintenance ruleset, `delete` drops a row other rows may be
/// stale against, and a container-valued action needs the (`:naive`) container
/// rebuild to recanonicalize it — all need the following rebuild to run.
fn command_skips_rebuild(command: &ResolvedNCommand) -> bool {
    fn touches_container(e: &ResolvedExpr) -> bool {
        e.output_type().is_eq_container_sort()
            || matches!(e, ResolvedExpr::Call(_, _, args) if args.iter().any(touches_container))
    }
    fn action_skips_rebuild(action: &ResolvedAction) -> bool {
        match action {
            ResolvedAction::Expr(_, e) | ResolvedAction::Let(_, _, e) => !touches_container(e),
            ResolvedAction::Set(_, _, args, rhs) => !args
                .iter()
                .chain(std::iter::once(rhs))
                .any(touches_container),
            _ => false,
        }
    }
    match command {
        ResolvedNCommand::Function(..)
        | ResolvedNCommand::NormRule { .. }
        | ResolvedNCommand::Sort { .. } => true,
        ResolvedNCommand::CoreAction(action) => action_skips_rebuild(action),
        ResolvedNCommand::CoreActions(actions) => actions.0.iter().all(action_skips_rebuild),
        _ => false,
    }
}

#[cfg(test)]
mod generated_timing_tests {
    use super::*;

    #[test]
    fn construction_timing_is_drained_after_error_before_next_producer() {
        let span = crate::span!();
        let mut egraph = EGraph::new_with_proofs();
        let missing_input = ResolvedNCommand::Input {
            span: span.clone(),
            name: "missing".to_owned(),
            file: "missing.csv".to_owned(),
        };

        assert!(ProofInstrumentor::add_term_encoding(&mut egraph, vec![missing_input]).is_err());
        assert!(egraph.overall_report.generated_construct > std::time::Duration::ZERO);
        assert!(egraph.overall_report.generated_signatures > std::time::Duration::ZERO);

        let construct_after_error = egraph.overall_report.generated_construct;
        ProofInstrumentor::add_term_encoding(
            &mut egraph,
            vec![ResolvedNCommand::AddRuleset(span, "after-error".to_owned())],
        )
        .unwrap();
        assert!(egraph.overall_report.generated_construct > construct_after_error);
    }
}

#[cfg(test)]
mod path_compression_direct_tests {
    use std::sync::Arc;

    use super::*;
    use crate::ast::RustSpan;
    use crate::proofs::generated_binder::{
        CallKey, FunctionKey, GeneratedExpr, LocalId, SortKey, SortSemanticClass, ValueShape,
    };

    fn assert_expr_span(expr: &GeneratedExpr, expected: &Span) {
        match expr {
            GenericExpr::Var(span, _) | GenericExpr::Lit(span, _) => assert_eq!(span, expected),
            GenericExpr::Call(span, _, args) => {
                assert_eq!(span, expected);
                for arg in args {
                    assert_expr_span(arg, expected);
                }
            }
        }
    }

    #[test]
    fn path_compression_direct_shape_pins_keys_ids_order_flags_and_source_span() {
        let span = Span::Rust(Arc::new(RustSpan {
            file: "path-compression-canary.egg",
            line: 7,
            column: 11,
        }));
        let mut proof_egraph = EGraph::new_with_proofs();
        proof_egraph.proof_state.proof_names.eq_trans_constructor = "@Trans".to_owned();
        let instrumentor = ProofInstrumentor::new(&mut proof_egraph);
        let mut catalog = GeneratedSignatureCatalog::default();
        let pc_sort = SortKey {
            name: "Pc".to_owned(),
            class: SortSemanticClass::Eq,
        };
        let proof = SortKey {
            name: "@Proof".to_owned(),
            class: SortSemanticClass::Eq,
        };
        let rule = instrumentor.path_compression_rule_direct(
            &mut catalog,
            &span,
            pc_sort.clone(),
            proof.clone(),
            FunctionKey {
                name: "@UF_Pc".to_owned(),
                subtype: FunctionSubtype::Custom,
                inputs: vec![pc_sort.clone()],
                output: ValueShape::Tuple(vec![pc_sort.clone(), proof]),
            },
            "@uf_path_compress".to_owned(),
            "@path_compress".to_owned(),
            "@uf_a".to_owned(),
            "@uf_b".to_owned(),
            "@uf_c".to_owned(),
            "@uf_pb".to_owned(),
            "@uf_pc".to_owned(),
            Some("@pv1".to_owned()),
        );
        assert_eq!(rule.span, span);
        assert_eq!(rule.name, "@uf_path_compress");
        assert_eq!(rule.ruleset, "@path_compress");
        assert_eq!(rule.eval_mode, RuleEvalMode::Seminaive);
        assert!(!rule.no_decomp);
        assert!(!rule.include_subsumed);
        assert_eq!(rule.body.len(), 3);
        assert_eq!(rule.head.0.len(), 2);

        let GenericFact::Eq(
            _,
            GenericExpr::Call(_, CallKey::Values(values), first),
            GenericExpr::Call(_, CallKey::Function(uf), first_uf),
        ) = &rule.body[0]
        else {
            panic!("expected first values/UF equality")
        };
        assert_eq!(
            values
                .iter()
                .map(|sort| sort.name.as_str())
                .collect::<Vec<_>>(),
            ["Pc", "@Proof"]
        );
        assert_eq!(uf.name, "@UF_Pc");
        let [GenericExpr::Var(_, b), GenericExpr::Var(_, pb)] = &first[..] else {
            panic!("expected b and pb variables")
        };
        let [GenericExpr::Var(_, a)] = &first_uf[..] else {
            panic!("expected a variable")
        };
        assert_eq!((b.name.as_str(), b.id), ("@uf_b", LocalId(0)));
        assert_eq!((pb.name.as_str(), pb.id), ("@uf_pb", LocalId(1)));
        assert_eq!((a.name.as_str(), a.id), ("@uf_a", LocalId(2)));

        let GenericFact::Eq(
            _,
            GenericExpr::Call(_, CallKey::Values(_), second),
            GenericExpr::Call(_, CallKey::Function(_), second_uf),
        ) = &rule.body[1]
        else {
            panic!("expected second values/UF equality")
        };
        let [GenericExpr::Var(_, c), GenericExpr::Var(_, pc)] = &second[..] else {
            panic!("expected c and pc variables")
        };
        let [GenericExpr::Var(_, repeated_b)] = &second_uf[..] else {
            panic!("expected repeated b variable")
        };
        assert_eq!((c.name.as_str(), c.id), ("@uf_c", LocalId(3)));
        assert_eq!((pc.name.as_str(), pc.id), ("@uf_pc", LocalId(4)));
        assert_eq!(repeated_b.id, LocalId(0));

        let GenericFact::Fact(GenericExpr::Call(_, CallKey::Primitive(not_equal), unequal)) =
            &rule.body[2]
        else {
            panic!("expected inequality fact")
        };
        assert_eq!(not_equal.name, "!=");
        assert_eq!(
            not_equal
                .inputs
                .iter()
                .map(|sort| sort.name.as_str())
                .collect::<Vec<_>>(),
            ["Pc", "Pc"]
        );
        assert_eq!(not_equal.output.name, "Unit");
        assert_eq!(unequal.len(), 2);

        let GenericAction::Let(
            _,
            compressed,
            GenericExpr::Call(_, CallKey::Primitive(mint), mint_args),
        ) = &rule.head.0[0]
        else {
            panic!("expected transitivity mint before the UF set")
        };
        assert_eq!(
            (compressed.name.as_str(), compressed.id),
            ("@pv1", LocalId(5))
        );
        assert_eq!(mint.name, "mint-@Trans!");
        assert_eq!(
            mint.inputs
                .iter()
                .map(|sort| sort.name.as_str())
                .collect::<Vec<_>>(),
            ["@Proof", "@Proof"]
        );
        assert_eq!(mint.output.name, "@Proof");
        assert_eq!(mint_args.len(), 2);
        let GenericAction::Set(_, CallKey::Function(set_uf), set_args, set_value) = &rule.head.0[1]
        else {
            panic!("expected UF set after the transitivity mint")
        };
        assert_eq!(set_uf.name, "@UF_Pc");
        let [GenericExpr::Var(_, set_a)] = &set_args[..] else {
            panic!("expected set key a")
        };
        assert_eq!(set_a.id, LocalId(2));
        let GenericExpr::Call(_, CallKey::Values(_), set_row) = set_value else {
            panic!("expected tuple-valued UF row")
        };
        let [
            GenericExpr::Var(_, set_c),
            GenericExpr::Var(_, set_compressed),
        ] = &set_row[..]
        else {
            panic!("expected c and compressed proof")
        };
        assert_eq!(set_c.id, LocalId(3));
        assert_eq!(set_compressed.id, LocalId(5));

        for fact in &rule.body {
            match fact {
                GenericFact::Eq(fact_span, left, right) => {
                    assert_eq!(fact_span, &span);
                    assert_expr_span(left, &span);
                    assert_expr_span(right, &span);
                }
                GenericFact::Fact(expr) => assert_expr_span(expr, &span),
            }
        }
        for action in &rule.head.0 {
            match action {
                GenericAction::Let(action_span, _, value) => {
                    assert_eq!(action_span, &span);
                    assert_expr_span(value, &span);
                }
                GenericAction::Set(action_span, _, args, value) => {
                    assert_eq!(action_span, &span);
                    for arg in args {
                        assert_expr_span(arg, &span);
                    }
                    assert_expr_span(value, &span);
                }
                action => panic!("unexpected path-compression action {action:?}"),
            }
        }
        let mut term_egraph = EGraph::new_with_term_encoding();
        let term_instrumentor = ProofInstrumentor::new(&mut term_egraph);
        let mut term_catalog = GeneratedSignatureCatalog::default();
        let unit = SortKey {
            name: "Unit".to_owned(),
            class: SortSemanticClass::Value,
        };
        let term = term_instrumentor.path_compression_rule_direct(
            &mut term_catalog,
            &span,
            pc_sort.clone(),
            unit.clone(),
            FunctionKey {
                name: "@UF_Pc".to_owned(),
                subtype: FunctionSubtype::Custom,
                inputs: vec![pc_sort.clone()],
                output: ValueShape::Tuple(vec![pc_sort, unit]),
            },
            "@uf_path_compress".to_owned(),
            "@path_compress".to_owned(),
            "@uf_a".to_owned(),
            "@uf_b".to_owned(),
            "@uf_c".to_owned(),
            "@uf_pb".to_owned(),
            "@uf_pc".to_owned(),
            None,
        );
        assert_eq!(term.head.0.len(), 1);
        let GenericFact::Eq(_, GenericExpr::Call(_, CallKey::Values(term_values), term_first), _) =
            &term.body[0]
        else {
            panic!("expected term-mode values equality")
        };
        assert_eq!(
            term_values
                .iter()
                .map(|sort| sort.name.as_str())
                .collect::<Vec<_>>(),
            ["Pc", "Unit"]
        );
        let [_, GenericExpr::Var(_, term_pb)] = &term_first[..] else {
            panic!("expected term-mode carried Unit variable")
        };
        assert_eq!(term_pb.id, LocalId(1));
        assert_eq!(term_pb.sort.name, "Unit");
        let GenericAction::Set(_, _, _, GenericExpr::Call(_, CallKey::Values(_), term_row)) =
            &term.head.0[0]
        else {
            panic!("expected term-mode UF set")
        };
        assert!(matches!(term_row[1], GenericExpr::Lit(_, Literal::Unit)));
    }
}
