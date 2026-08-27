//! Portable typed lowering for source-derived rules.
//!
//! It constructs one typed draft, assigns portable locals only after the final
//! body/head order is known, and produces a structured [`GeneratedRule`].

use std::fmt::{Display, Formatter};

use crate::ast::{
    GenericAction, GenericActions, GenericExpr, GenericFact, GenericRule, Literal, ResolvedAction,
    ResolvedExpr, ResolvedExprExt, ResolvedFact, ResolvedRule, RuleEvalMode, Span,
};
use crate::core::ResolvedCall;
use crate::proofs::generated_binder::{
    CallKey, FunctionKey, GeneratedActions, GeneratedExpr, GeneratedFact, GeneratedRule,
    GeneratedSignatureCatalog, GeneratedVar, GeneratedVarRole, LocalId, PrimitiveKey, SortKey,
    SortSemanticClass, ValueShape,
};
use crate::proofs::proof_checker::is_container_side_condition;
use crate::proofs::proof_encoding_helpers::{Composition, holds_sort, recomputable_premises};
use crate::proofs::proof_fresh::{
    GET_FRESH_PRIM_NAME, mint_prim_name, set_if_empty_prim_name, view_proof_prim_name,
};
use crate::proofs::proof_head::{
    Head, HeadPlan, HeadPosition, HeadProof, HeadRun, ProofAlgebra, constructor_operand,
};
use crate::typechecking::FuncType;
use crate::util::{FreshGen, HashMap};
use crate::{Change, FunctionSubtype, literal_sort};

use super::action_direct::{
    Deferred, DeferredProofs, EmissionNatural, EmissionOperand, EmissionScope, PendingLocal,
    lower_single_step, proof_constructor, value_sort, visit_action_dependencies,
};
use super::{Anchor, BodyAnchors, Connector, Element, ProofInstrumentor};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct DraftVar {
    name: String,
    sort: SortKey,
    role: GeneratedVarRole,
}

impl Display for DraftVar {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.name)
    }
}

impl PendingLocal for DraftVar {
    fn pending_local(&self) -> Option<&str> {
        (self.role == GeneratedVarRole::Local).then_some(&self.name)
    }
}

type DraftExpr = GenericExpr<CallKey, DraftVar>;
type DraftFact = GenericFact<CallKey, DraftVar>;
type DraftAction = GenericAction<CallKey, DraftVar>;
type DraftRule = GenericRule<CallKey, DraftVar>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct LoweredQueryFacts {
    pub(super) facts: Vec<GeneratedFact>,
    pub(super) action_lookups: GeneratedActions,
    pub(super) premises: Vec<GeneratedExpr>,
}

pub(super) fn register_signatures(rule: &GeneratedRule, catalog: &mut GeneratedSignatureCatalog) {
    fn register_expr(catalog: &mut GeneratedSignatureCatalog, value: &GeneratedExpr) {
        if let GenericExpr::Call(span, call, args) = value {
            catalog
                .register_call_key(call, span)
                .expect("source-rule call signatures must be internally consistent");
            for arg in args {
                register_expr(catalog, arg);
            }
        }
    }

    for fact in &rule.body {
        match fact {
            GenericFact::Eq(_, left, right) => {
                register_expr(catalog, left);
                register_expr(catalog, right);
            }
            GenericFact::Fact(value) => register_expr(catalog, value),
        }
    }
    for action in &rule.head.0 {
        match action {
            GenericAction::Let(_, _, value) | GenericAction::Expr(_, value) => {
                register_expr(catalog, value)
            }
            GenericAction::Set(span, call, args, value) => {
                catalog
                    .register_call_key(call, span)
                    .expect("source-rule set signature must be internally consistent");
                for arg in args {
                    register_expr(catalog, arg);
                }
                register_expr(catalog, value);
            }
            GenericAction::Change(span, _, call, args) => {
                catalog
                    .register_call_key(call, span)
                    .expect("source-rule change signature must be internally consistent");
                for arg in args {
                    register_expr(catalog, arg);
                }
            }
            GenericAction::Union(_, left, right) => {
                register_expr(catalog, left);
                register_expr(catalog, right);
            }
            GenericAction::Panic(..) => {}
        }
    }
}

/// Register precisely the calls retained by a top-level query consumer.
///
/// Check and schedule-until discard proof lookup actions and premise values;
/// registering them would make discarded code affect the signature universe.
pub(super) fn register_query_signatures(
    facts: &[GeneratedFact],
    catalog: &mut GeneratedSignatureCatalog,
) {
    fn register_expr(catalog: &mut GeneratedSignatureCatalog, value: &GeneratedExpr) {
        if let GenericExpr::Call(span, call, args) = value {
            catalog
                .register_call_key(call, span)
                .expect("query-fact call signatures must be internally consistent");
            for arg in args {
                register_expr(catalog, arg);
            }
        }
    }

    for fact in facts {
        match fact {
            GenericFact::Eq(_, left, right) => {
                register_expr(catalog, left);
                register_expr(catalog, right);
            }
            GenericFact::Fact(value) => register_expr(catalog, value),
        }
    }
}

type DraftOperand = EmissionOperand<DraftExpr, Connector>;
type DraftScope = EmissionScope<DraftExpr, Connector>;
type DraftNatural = EmissionNatural<DraftExpr, Option<String>>;

#[derive(Clone)]
struct RuleJustification {
    rule_name: Option<String>,
    premises: Vec<String>,
    column: DraftExpr,
}

impl RuleJustification {
    fn at(&self, column: DraftExpr) -> Self {
        Self {
            rule_name: self.rule_name.clone(),
            premises: self.premises.clone(),
            column,
        }
    }
}

struct DraftEmit<'a> {
    actions: &'a mut Vec<DraftAction>,
    head: &'a mut Head,
    justification: &'a RuleJustification,
}

impl<'a> DraftEmit<'a> {
    fn justified_by<'b>(&'b mut self, justification: &'b RuleJustification) -> DraftEmit<'b> {
        DraftEmit {
            actions: &mut *self.actions,
            head: &mut *self.head,
            justification,
        }
    }

    fn composing<R>(&mut self, lower: impl FnOnce(&mut DraftEmit<'_>) -> R) -> R {
        let DraftEmit {
            actions,
            head,
            justification,
        } = self;
        let justification = *justification;
        head.composing(|head| {
            lower(&mut DraftEmit {
                actions,
                head,
                justification,
            })
        })
    }
}

struct SourceRuleLowerer<'instrumentor, 'egraph> {
    instrumentor: &'instrumentor mut ProofInstrumentor<'egraph>,
    span: Span,
    proofs: bool,
    unit_sort: SortKey,
    string_sort: SortKey,
    i64_sort: SortKey,
    carry_sort: SortKey,
    variables: HashMap<(String, GeneratedVarRole), SortKey>,
    proofs_state: DeferredProofs<DraftAction>,
    anchors: BodyAnchors,
    unanchored: HashMap<String, String>,
}

pub(super) fn lower(
    instrumentor: &mut ProofInstrumentor<'_>,
    rule: &ResolvedRule,
) -> GeneratedRule {
    let mut lowerer = SourceRuleLowerer::new(instrumentor, rule.span.clone());
    let draft = lowerer.lower_rule(rule);
    finalize_rule(draft)
}

/// Lower facts through the same proof-aware kernel used by source rules.
///
/// The auxiliary products are intentionally retained here. Top-level Check and
/// schedule-until consumers own the source-compatible decision to discard them;
/// this boundary must not hide freshness or pending-declaration side effects.
pub(super) fn lower_query_facts(
    instrumentor: &mut ProofInstrumentor<'_>,
    span: &Span,
    facts: &[ResolvedFact],
) -> LoweredQueryFacts {
    let mut lowerer = SourceRuleLowerer::new(instrumentor, span.clone());
    let (facts, action_lookups, premises) = lowerer.instrument_facts(facts);
    let premises = premises
        .into_iter()
        .map(|premise| lowerer.proof_expr(&premise))
        .collect();

    // This is the direct counterpart of `ProofInstrumentor::drop_pending_lookups`.
    // These three collections contain unmaterialized draft work, so they stay
    // producer-local and cannot be part of `LoweredQueryFacts`. Declarations and
    // consumed SymbolGen names already live on the instrumentor and deliberately
    // survive; the returned actions and premises are the complete materialized
    // auxiliary product which each top-level query consumer explicitly discards.
    lowerer.proofs_state.discard_unobserved();
    if lowerer.proofs {
        lowerer.unanchored.clear();
    }

    finalize_query(facts, GenericActions(action_lookups), premises)
}

impl<'instrumentor, 'egraph> SourceRuleLowerer<'instrumentor, 'egraph> {
    /// Establish every proof-mode-dependent sort and all per-lowering lexical
    /// state together, so rule and standalone-query lowering cannot drift.
    fn new(instrumentor: &'instrumentor mut ProofInstrumentor<'egraph>, span: Span) -> Self {
        let proofs = instrumentor.proofs_enabled();
        let carry_sort = if proofs {
            SortKey {
                name: instrumentor
                    .egraph
                    .proof_state
                    .proof_names
                    .proof_datatype
                    .clone(),
                class: SortSemanticClass::Eq,
            }
        } else {
            value_sort("Unit")
        };
        Self {
            instrumentor,
            span,
            proofs,
            unit_sort: value_sort("Unit"),
            string_sort: value_sort("String"),
            i64_sort: value_sort("i64"),
            carry_sort,
            variables: HashMap::default(),
            proofs_state: DeferredProofs::default(),
            anchors: BodyAnchors::default(),
            unanchored: HashMap::default(),
        }
    }
}

impl SourceRuleLowerer<'_, '_> {
    fn variable(
        &mut self,
        name: impl Into<String>,
        sort: SortKey,
        role: GeneratedVarRole,
    ) -> DraftVar {
        let name = name.into();
        let identity = (name.clone(), role);
        if let Some(existing) = self.variables.get(&identity) {
            assert_eq!(
                existing, &sort,
                "source-rule variable `{name}` changed sort while lowering"
            );
        } else {
            self.variables.insert(identity, sort.clone());
        }
        DraftVar { name, sort, role }
    }

    fn fresh_expr(&mut self, sort: SortKey) -> DraftExpr {
        let name = self.instrumentor.fresh_var();
        let variable = self.variable(name, sort, GeneratedVarRole::Local);
        GenericExpr::Var(self.span.clone(), variable)
    }

    fn primitive(
        &self,
        name: impl Into<String>,
        args: Vec<DraftExpr>,
        output: SortKey,
    ) -> DraftExpr {
        let inputs = args.iter().map(Self::scalar_expr_sort).collect();
        GenericExpr::Call(
            self.span.clone(),
            CallKey::Primitive(PrimitiveKey {
                name: name.into(),
                inputs,
                output,
            }),
            args,
        )
    }

    fn values(&self, values: Vec<DraftExpr>) -> DraftExpr {
        let sorts = values.iter().map(Self::scalar_expr_sort).collect();
        GenericExpr::Call(self.span.clone(), CallKey::Values(sorts), values)
    }

    fn scalar_expr_sort(expr: &DraftExpr) -> SortKey {
        match expr {
            GenericExpr::Var(_, variable) => variable.sort.clone(),
            GenericExpr::Lit(_, literal) => SortKey::from_sort(&literal_sort(literal)),
            GenericExpr::Call(_, CallKey::Function(key), _) => match &key.output {
                ValueShape::Scalar(sort) => sort.clone(),
                ValueShape::Tuple(_) => panic!("tuple-valued expression used in scalar position"),
            },
            GenericExpr::Call(_, CallKey::Primitive(key), _) => key.output.clone(),
            GenericExpr::Call(_, CallKey::Values(_), _) => {
                panic!("values tuple used in scalar position")
            }
        }
    }

    fn view_call_key(&mut self, function: &FuncType) -> CallKey {
        let name = self.instrumentor.view_name(&function.name);
        CallKey::Function(FunctionKey {
            name,
            subtype: FunctionSubtype::Custom,
            inputs: function.input.iter().map(SortKey::from_sort).collect(),
            output: ValueShape::Tuple(vec![
                SortKey::from_sort(function.output()),
                self.carry_sort.clone(),
            ]),
        })
    }

    fn uf_call_key(&mut self, sort: SortKey) -> CallKey {
        let name = self.instrumentor.uf_name(&sort.name);
        CallKey::Function(FunctionKey {
            name,
            subtype: FunctionSubtype::Custom,
            inputs: vec![sort.clone()],
            output: ValueShape::Tuple(vec![sort, self.carry_sort.clone()]),
        })
    }

    fn relation_call_key(&self, name: impl Into<String>, inputs: Vec<SortKey>) -> CallKey {
        CallKey::Function(FunctionKey {
            name: name.into(),
            subtype: FunctionSubtype::Custom,
            inputs,
            output: ValueShape::Scalar(self.unit_sort.clone()),
        })
    }

    fn term_sort(&self, function: &str) -> SortKey {
        SortKey {
            name: self
                .instrumentor
                .proof_names()
                .fn_to_term_sort
                .get(function)
                .unwrap_or_else(|| panic!("term sort for `{function}` was not declared"))
                .clone(),
            class: SortSemanticClass::Eq,
        }
    }

    fn map_resolved_expr(&mut self, expr: &ResolvedExpr) -> DraftExpr {
        match expr {
            GenericExpr::Var(_, variable) => {
                let variable = self.variable(
                    variable.name.clone(),
                    SortKey::from_sort(&variable.sort),
                    if variable.is_global_ref {
                        GeneratedVarRole::Global
                    } else {
                        GeneratedVarRole::Local
                    },
                );
                GenericExpr::Var(self.span.clone(), variable)
            }
            GenericExpr::Lit(_, literal) => GenericExpr::Lit(self.span.clone(), literal.clone()),
            GenericExpr::Call(_, call, args) => {
                let args = args.iter().map(|arg| self.map_resolved_expr(arg)).collect();
                GenericExpr::Call(self.span.clone(), CallKey::from_resolved(call), args)
            }
        }
    }

    fn map_resolved_fact(&mut self, fact: &ResolvedFact) -> DraftFact {
        match fact {
            GenericFact::Eq(_, left, right) => GenericFact::Eq(
                self.span.clone(),
                self.map_resolved_expr(left),
                self.map_resolved_expr(right),
            ),
            GenericFact::Fact(expr) => GenericFact::Fact(self.map_resolved_expr(expr)),
        }
    }

    fn get_fresh(&mut self, actions: &mut Vec<DraftAction>, sort: SortKey) -> DraftExpr {
        let target = self.fresh_expr(sort.clone());
        let sort_name = GenericExpr::Lit(self.span.clone(), Literal::String(sort.name.clone()));
        let value = self.primitive(GET_FRESH_PRIM_NAME, vec![sort_name], sort);
        actions.push(GenericAction::Let(
            self.span.clone(),
            Self::expect_variable(&target).clone(),
            value,
        ));
        target
    }

    /// Assert the draft invariant that a binding/proof name is represented by a
    /// variable expression and expose the checked variable.
    fn expect_variable(expr: &DraftExpr) -> &DraftVar {
        let GenericExpr::Var(_, variable) = expr else {
            panic!("internal source-rule lowering expected a variable")
        };
        variable
    }

    fn emit_action(&mut self, actions: &mut Vec<DraftAction>, action: DraftAction) {
        visit_action_dependencies(&action, &mut |proof| {
            self.emit_pending_group(actions, proof)
        });
        actions.push(action);
    }

    fn mint_as(
        &mut self,
        actions: &mut Vec<DraftAction>,
        target: DraftExpr,
        relation: &str,
        args: Vec<DraftExpr>,
        output: SortKey,
    ) -> DraftExpr {
        let value = self.primitive(mint_prim_name(relation), args, output);
        self.emit_action(
            actions,
            GenericAction::Let(
                self.span.clone(),
                Self::expect_variable(&target).clone(),
                value,
            ),
        );
        target
    }

    fn mint(
        &mut self,
        actions: &mut Vec<DraftAction>,
        relation: &str,
        args: Vec<DraftExpr>,
        output: SortKey,
    ) -> DraftExpr {
        let target = self.fresh_expr(output.clone());
        self.mint_as(actions, target, relation, args, output)
    }

    fn proof_expr(&mut self, proof: &str) -> DraftExpr {
        let variable = self.variable(
            proof.to_owned(),
            self.carry_sort.clone(),
            GeneratedVarRole::Local,
        );
        GenericExpr::Var(self.span.clone(), variable)
    }

    fn compose(&mut self, composition: Composition) -> String {
        let name = Self::expect_variable(&self.fresh_expr(self.carry_sort.clone()))
            .name
            .clone();
        self.proofs_state.defer(name, composition)
    }

    fn mint_proj(&mut self, base: &str, child: usize) -> String {
        let base = self.proofs_state.composition(base);
        let proof = self.compose(base.proj(child));
        self.proofs_state.reflexive.insert(proof.clone());
        proof
    }

    fn mint_lhs_reflexive(&mut self, base: &str) -> String {
        let back = self.sym(base.to_owned());
        let proof = self.trans(base.to_owned(), back);
        self.proofs_state.reflexive.insert(proof.clone());
        proof
    }

    fn single_step(&mut self, composition: &Composition) -> Option<(String, Vec<DraftExpr>)> {
        let relation = proof_constructor(composition, self.instrumentor.proof_names())?;
        let span = self.span.clone();
        lower_single_step(composition, relation, &span, |proof| self.proof_expr(proof))
    }

    fn emit_composition(
        &mut self,
        actions: &mut Vec<DraftAction>,
        proof: &str,
        composition: Composition,
    ) {
        let (skeleton, columns) = composition.pack();
        for leaf in &columns {
            self.emit_pending_group(actions, leaf);
        }
        let (name, args) = self.single_step(&composition).unwrap_or_else(|| {
            let name = self
                .instrumentor
                .queue_packed_declaration(&self.span, columns.len());
            let mut args = vec![GenericExpr::Lit(
                self.span.clone(),
                Literal::String(skeleton.spelling()),
            )];
            args.extend(columns.iter().map(|column| self.proof_expr(column)));
            (name, args)
        });
        let variable = self.variable(
            proof.to_owned(),
            self.carry_sort.clone(),
            GeneratedVarRole::Local,
        );
        let target = GenericExpr::Var(self.span.clone(), variable);
        self.mint_as(actions, target, &name, args, self.carry_sort.clone());
    }

    fn emit_pending_group(&mut self, actions: &mut Vec<DraftAction>, proof: &str) {
        match self.proofs_state.pending.remove(proof) {
            Some(Deferred::Composed(composition)) => {
                self.emit_composition(actions, proof, composition)
            }
            Some(Deferred::Actions(group)) => actions.extend(group),
            None => {
                assert!(
                    !self.unanchored.contains_key(proof),
                    "internal invariant: the body variable `{}` has no reflexive anchor",
                    self.unanchored[proof]
                );
            }
        }
    }

    fn fiat_reflexive(
        &mut self,
        actions: &mut Vec<DraftAction>,
        value: DraftExpr,
        sort: SortKey,
    ) -> String {
        let (relation, declaration) = self
            .instrumentor
            .plan_fiat_pending_direct(&self.span, sort.clone());
        self.instrumentor
            .queue_pending_declaration_group(declaration);
        let proof = self.mint(
            actions,
            &relation,
            vec![value.clone(), value],
            self.carry_sort.clone(),
        );
        let name = Self::expect_variable(&proof).name.clone();
        self.proofs_state.reflexive.insert(name.clone());
        name
    }

    fn deferred_fiat_reflexive(&mut self, value: DraftExpr, sort: SortKey) -> String {
        let mut actions = vec![];
        let proof = self.fiat_reflexive(&mut actions, value, sort);
        self.proofs_state
            .pending
            .insert(proof.clone(), Deferred::Actions(actions));
        proof
    }

    fn request_anchor(&mut self, value: &str) -> String {
        let proof = self.fresh_expr(self.carry_sort.clone());
        let proof_name = Self::expect_variable(&proof).name.clone();
        self.anchors.request(&proof_name, value);
        self.proofs_state.reflexive.insert(proof_name.clone());
        proof_name
    }

    fn request_element_anchor(
        &mut self,
        value: &str,
        sort: &SortKey,
        containers: Vec<String>,
    ) -> String {
        let (projection, declaration) = self
            .instrumentor
            .plan_projection_pending_direct(&self.span, sort.clone());
        self.instrumentor
            .queue_pending_declaration_group(declaration);
        self.anchors.offer_element(Element {
            containers,
            value: value.to_owned(),
            proj_all: projection,
        });
        self.request_anchor(value)
    }

    fn anchor_composition(&mut self, row_proof: &str, anchor: Anchor) -> String {
        match anchor {
            Anchor::Child(child) => self.mint_proj(row_proof, child),
            Anchor::Lhs => self.mint_lhs_reflexive(row_proof),
        }
    }

    fn bind_anchors(&mut self) {
        let anchors = std::mem::take(&mut self.anchors);
        for (proof, value) in &anchors.requests {
            let Some((row_proof, anchor, chain)) = anchors.anchor_chain(value) else {
                self.unanchored.insert(proof.clone(), value.clone());
                continue;
            };
            let derived = self.anchor_composition(&row_proof, anchor);
            if chain.is_empty() {
                let held = self
                    .proofs_state
                    .pending
                    .remove(&derived)
                    .expect("a minted anchor composition is held back");
                self.proofs_state.pending.insert(proof.clone(), held);
                continue;
            }
            let mut group = vec![];
            self.emit_pending_group(&mut group, &derived);
            let mut base = derived;
            for (depth, element) in chain.iter().enumerate() {
                let projected = if depth + 1 == chain.len() {
                    let variable = self.variable(
                        proof.clone(),
                        self.carry_sort.clone(),
                        GeneratedVarRole::Local,
                    );
                    GenericExpr::Var(self.span.clone(), variable)
                } else {
                    self.fresh_expr(self.carry_sort.clone())
                };
                let value_sort = self
                    .variables
                    .get(&(element.value.clone(), GeneratedVarRole::Local))
                    .unwrap_or_else(|| {
                        panic!("projected value `{}` has no recorded sort", element.value)
                    })
                    .clone();
                let variable =
                    self.variable(element.value.clone(), value_sort, GeneratedVarRole::Local);
                let value = GenericExpr::Var(self.span.clone(), variable.clone());
                let base_expr = self.proof_expr(&base);
                self.mint_as(
                    &mut group,
                    projected.clone(),
                    &element.proj_all,
                    vec![base_expr, value],
                    self.carry_sort.clone(),
                );
                base = Self::expect_variable(&projected).name.clone();
            }
            self.proofs_state
                .pending
                .insert(proof.clone(), Deferred::Actions(group));
        }
    }

    fn level_connector(&mut self, chain: &str, dedup: &str) -> String {
        let composed = matches!(
            self.proofs_state.pending.get(chain),
            Some(Deferred::Composed(_))
        );
        let connector = self.connect(chain.to_owned(), dedup.to_owned());
        if composed {
            self.proofs_state.sealed.insert(connector.clone());
        }
        connector
    }
}

impl ProofAlgebra for SourceRuleLowerer<'_, '_> {
    type Proof = String;

    fn sym(&mut self, proof: String) -> String {
        let planned = self.proofs_state.sym(proof);
        planned.realize(|composition| self.compose(composition))
    }

    fn trans(&mut self, left: String, right: String) -> String {
        let planned = self.proofs_state.trans(left, right);
        planned.realize(|composition| self.compose(composition))
    }

    fn congr(&mut self, base: String, child: usize, step: String) -> String {
        let planned = self.proofs_state.congr(base, child, step);
        planned.realize(|composition| self.compose(composition))
    }
}

impl SourceRuleLowerer<'_, '_> {
    fn instrument_fact_expr(
        &mut self,
        expr: &ResolvedExpr,
        facts: &mut Vec<DraftFact>,
    ) -> (DraftExpr, String) {
        match expr {
            GenericExpr::Lit(_, literal) => {
                let value = GenericExpr::Lit(self.span.clone(), literal.clone());
                let proof = if self.proofs {
                    self.deferred_fiat_reflexive(
                        value.clone(),
                        SortKey::from_sort(&literal_sort(literal)),
                    )
                } else {
                    "()".to_owned()
                };
                (value, proof)
            }
            GenericExpr::Var(_, variable) => {
                let variable = self.variable(
                    variable.name.clone(),
                    SortKey::from_sort(&variable.sort),
                    if variable.is_global_ref {
                        GeneratedVarRole::Global
                    } else {
                        GeneratedVarRole::Local
                    },
                );
                let value = GenericExpr::Var(self.span.clone(), variable.clone());
                let proof = if !self.proofs {
                    "()".to_owned()
                } else if matches!(
                    variable.sort.class,
                    SortSemanticClass::Eq | SortSemanticClass::EqContainer
                ) {
                    self.request_anchor(&variable.name)
                } else {
                    self.deferred_fiat_reflexive(value.clone(), variable.sort.clone())
                };
                (value, proof)
            }
            GenericExpr::Call(_, call, args) => {
                let mut values = Vec::with_capacity(args.len());
                let mut proofs = Vec::with_capacity(args.len());
                for arg in args {
                    if matches!(arg, GenericExpr::Var(..) | GenericExpr::Lit(..)) {
                        values.push(self.map_resolved_expr(arg));
                        proofs.push(None);
                    } else {
                        let (value, proof) = self.instrument_fact_expr(arg, facts);
                        values.push(value);
                        proofs.push(Some(proof));
                    }
                }
                match call {
                    ResolvedCall::Func(function) => {
                        assert!(
                            function.subtype == FunctionSubtype::Constructor
                                || self.instrumentor.egraph.type_info.is_global(&function.name),
                            "proof-normal-form fact call must be a constructor or encoded global"
                        );
                        let value = self.fresh_expr(SortKey::from_sort(function.output()));
                        let row_proof = self.fresh_expr(self.carry_sort.clone());
                        let tuple = self.values(vec![value.clone(), row_proof.clone()]);
                        let view_key = self.view_call_key(function);
                        let view = GenericExpr::Call(self.span.clone(), view_key, values.clone());
                        facts.push(GenericFact::Eq(self.span.clone(), tuple, view));
                        let row_name = Self::expect_variable(&row_proof).name.clone();
                        if self.proofs {
                            for (index, arg) in values.iter().enumerate() {
                                self.anchors.offer(
                                    &arg.to_string(),
                                    &row_name,
                                    Anchor::Child(index),
                                );
                            }
                            self.anchors.offer(
                                &Self::expect_variable(&value).name,
                                &row_name,
                                Anchor::Lhs,
                            );
                        }
                        let proof = if self.proofs {
                            let mut proof = row_name;
                            for (index, child) in proofs.into_iter().enumerate() {
                                if let Some(child) = child {
                                    proof = self.congr(proof, index, child);
                                }
                            }
                            proof
                        } else {
                            "()".to_owned()
                        };
                        (value, proof)
                    }
                    ResolvedCall::Primitive(primitive) => {
                        let output = SortKey::from_sort(primitive.output());
                        let value = self.fresh_expr(output.clone());
                        let computed = GenericExpr::Call(
                            self.span.clone(),
                            CallKey::from_resolved(call),
                            values.clone(),
                        );
                        facts.push(GenericFact::Eq(self.span.clone(), value.clone(), computed));
                        let proof = if !self.proofs || primitive.output().is_eq_container_sort() {
                            "()".to_owned()
                        } else if primitive.output().is_eq_sort() {
                            let containers = primitive
                                .input()
                                .iter()
                                .zip(&values)
                                .filter(|(sort, _)| holds_sort(sort, primitive.output().name()))
                                .map(|(_, value)| value.to_string())
                                .collect();
                            self.request_element_anchor(
                                &Self::expect_variable(&value).name,
                                &output,
                                containers,
                            )
                        } else {
                            self.deferred_fiat_reflexive(value.clone(), output)
                        };
                        (value, proof)
                    }
                    ResolvedCall::Values(_) => {
                        panic!("tuple-output (`values`) calls are unsupported in proofs")
                    }
                }
            }
        }
    }

    fn eval_marker(&mut self, actions: &mut Vec<DraftAction>) -> String {
        let relation = self.instrumentor.proof_names().eval_constructor.clone();
        let proof = self.mint(actions, &relation, vec![], self.carry_sort.clone());
        Self::expect_variable(&proof).name.clone()
    }

    fn instrument_fact(
        &mut self,
        fact: &ResolvedFact,
        facts: &mut Vec<DraftFact>,
        action_lookups: &mut Vec<DraftAction>,
    ) -> String {
        if is_container_side_condition(fact) {
            facts.push(self.map_resolved_fact(fact));
            return if self.proofs {
                self.eval_marker(action_lookups)
            } else {
                "()".to_owned()
            };
        }
        match fact {
            GenericFact::Eq(
                _,
                GenericExpr::Call(_, ResolvedCall::Func(function), args),
                GenericExpr::Var(_, output),
            ) if function.subtype == FunctionSubtype::Custom => {
                let mut values = Vec::with_capacity(args.len());
                let mut proofs = Vec::with_capacity(args.len());
                for arg in args {
                    let (value, proof) = self.instrument_fact_expr(arg, facts);
                    values.push(value);
                    proofs.push(proof);
                }
                let output_variable = self.variable(
                    output.name.clone(),
                    SortKey::from_sort(&output.sort),
                    if output.is_global_ref {
                        GeneratedVarRole::Global
                    } else {
                        GeneratedVarRole::Local
                    },
                );
                let output = GenericExpr::Var(self.span.clone(), output_variable);
                let row_proof = self.fresh_expr(self.carry_sort.clone());
                let tuple = self.values(vec![output.clone(), row_proof.clone()]);
                let view_key = self.view_call_key(function);
                let view = GenericExpr::Call(self.span.clone(), view_key, values.clone());
                facts.push(GenericFact::Eq(self.span.clone(), tuple, view));
                let row_name = Self::expect_variable(&row_proof).name.clone();
                if self.proofs {
                    for (index, value) in values.iter().enumerate() {
                        self.anchors
                            .offer(&value.to_string(), &row_name, Anchor::Child(index));
                    }
                    self.anchors.offer(
                        &Self::expect_variable(&output).name,
                        &row_name,
                        Anchor::Child(values.len()),
                    );
                    proofs
                        .into_iter()
                        .enumerate()
                        .fold(row_name, |proof, (index, child)| {
                            self.congr(proof, index, child)
                        })
                } else {
                    "()".to_owned()
                }
            }
            GenericFact::Eq(_, left, right) => {
                let (left, left_proof) = self.instrument_fact_expr(left, facts);
                let (right, right_proof) = self.instrument_fact_expr(right, facts);
                facts.push(GenericFact::Eq(
                    self.span.clone(),
                    left.clone(),
                    right.clone(),
                ));
                if self.proofs {
                    self.anchors.alias(&left.to_string(), &right.to_string());
                    let back = self.sym(left_proof);
                    self.trans(back, right_proof)
                } else {
                    "()".to_owned()
                }
            }
            GenericFact::Fact(expr) => {
                let (_, proof) = self.instrument_fact_expr(expr, facts);
                if self.proofs
                    && matches!(
                        expr,
                        GenericExpr::Call(_, ResolvedCall::Primitive(primitive), _)
                            if primitive.output().is_eq_container_sort()
                    )
                {
                    self.eval_marker(action_lookups)
                } else {
                    proof
                }
            }
        }
    }

    fn instrument_facts(
        &mut self,
        source: &[ResolvedFact],
    ) -> (Vec<DraftFact>, Vec<DraftAction>, Vec<String>) {
        let mut facts = vec![];
        let mut action_lookups = vec![];
        let mut premises = vec![];
        let recomputable = recomputable_premises(source, &|_| false);
        for (fact, recomputable) in source.iter().zip(recomputable) {
            let proof = self.instrument_fact(fact, &mut facts, &mut action_lookups);
            if !recomputable {
                premises.push(proof);
            }
        }
        if self.proofs {
            self.bind_anchors();
        }
        (facts, action_lookups, premises)
    }

    fn column(&self, run: Option<HeadRun>, proof: HeadProof) -> DraftExpr {
        GenericExpr::Lit(
            self.span.clone(),
            Literal::Int(run.map_or(-1, |run| run.column(proof) as i64)),
        )
    }

    fn rule_row(&mut self, emit: &mut DraftEmit<'_>) -> String {
        assert!(self.proofs, "term-only lowering cannot mint a rule proof");
        let proof = if let Some((previous, bridge)) = emit.head.link() {
            let relation = self
                .instrumentor
                .proof_names()
                .rule_link_constructor
                .clone();
            let previous = self.proof_expr(&previous);
            let bridge = self.proof_expr(&bridge);
            self.mint(
                emit.actions,
                &relation,
                vec![previous, bridge, emit.justification.column.clone()],
                self.carry_sort.clone(),
            )
        } else {
            let relation = self
                .instrumentor
                .proof_names()
                .fused_rule(emit.justification.premises.len());
            let rule_name = self.variable(
                emit.justification
                    .rule_name
                    .clone()
                    .expect("source rule proof must name its rule variable"),
                self.string_sort.clone(),
                GeneratedVarRole::Local,
            );
            let mut args = vec![GenericExpr::Var(self.span.clone(), rule_name)];
            for premise in &emit.justification.premises {
                args.push(self.proof_expr(premise));
            }
            args.push(emit.justification.column.clone());
            self.mint(emit.actions, &relation, args, self.carry_sort.clone())
        };
        let name = Self::expect_variable(&proof).name.clone();
        emit.head.minted(&name);
        name
    }

    fn connector_node(&mut self, emit: &mut DraftEmit<'_>, connector: &Connector) -> String {
        match connector {
            Connector::Node(node) => node.clone(),
            Connector::Column(column) => {
                let justification = emit.justification.at(GenericExpr::Lit(
                    self.span.clone(),
                    Literal::Int(*column as i64),
                ));
                self.rule_row(&mut emit.justified_by(&justification))
            }
        }
    }

    fn reflexive_for_rule(
        &mut self,
        emit: &mut DraftEmit<'_>,
        _value: &DraftExpr,
        _sort: &SortKey,
    ) -> String {
        let proof = self.rule_row(emit);
        self.proofs_state.reflexive.insert(proof.clone());
        proof
    }

    fn set_if_empty(
        &mut self,
        function: &FuncType,
        children: Vec<DraftExpr>,
        fallback: DraftExpr,
        proof: DraftExpr,
    ) -> DraftExpr {
        let output = SortKey::from_sort(function.output());
        let view_name = self.instrumentor.view_name(&function.name);
        let mut args = children;
        args.push(fallback);
        args.push(proof);
        self.primitive(set_if_empty_prim_name(&view_name), args, output)
    }

    fn read_view_proof(
        &mut self,
        function: &FuncType,
        children: Vec<DraftExpr>,
        fallback: DraftExpr,
    ) -> DraftExpr {
        let view_name = self.instrumentor.view_name(&function.name);
        let mut args = children;
        args.push(fallback);
        self.primitive(
            view_proof_prim_name(&view_name),
            args,
            self.carry_sort.clone(),
        )
    }

    fn update_view(
        &mut self,
        actions: &mut Vec<DraftAction>,
        function: &FuncType,
        children: Vec<DraftExpr>,
        value: DraftExpr,
        proof: DraftExpr,
    ) {
        let key = self.view_call_key(function);
        let tuple = self.values(vec![value, proof]);
        self.emit_action(
            actions,
            GenericAction::Set(self.span.clone(), key, children, tuple),
        );
    }

    fn term_mint(
        &mut self,
        actions: &mut Vec<DraftAction>,
        function: &FuncType,
        args: Vec<DraftExpr>,
    ) -> DraftExpr {
        self.mint(
            actions,
            &function.name,
            args,
            self.term_sort(&function.name),
        )
    }

    fn add_custom_row(
        &mut self,
        emit: &mut DraftEmit<'_>,
        function: &FuncType,
        args: Vec<DraftExpr>,
    ) -> DraftExpr {
        let term = self.term_mint(emit.actions, function, args.clone());
        let proof = if self.proofs {
            let sort = self.term_sort(&function.name);
            let own = self.reflexive_for_rule(emit, &term, &sort);
            self.proof_expr(&own)
        } else {
            GenericExpr::Lit(self.span.clone(), Literal::Unit)
        };
        let (output, children) = args
            .split_last()
            .expect("custom set must include an output value");
        self.update_view(
            emit.actions,
            function,
            children.to_vec(),
            output.clone(),
            proof,
        );
        term
    }

    fn add_constructor_term_only(
        &mut self,
        actions: &mut Vec<DraftAction>,
        function: &FuncType,
        args: Vec<DraftExpr>,
    ) -> DraftExpr {
        let term = self.term_mint(actions, function, args.clone());
        let canonical = self.fresh_expr(SortKey::from_sort(function.output()));
        let unit = GenericExpr::Lit(self.span.clone(), Literal::Unit);
        let value = self.set_if_empty(function, args, term, unit);
        self.emit_action(
            actions,
            GenericAction::Let(
                self.span.clone(),
                Self::expect_variable(&canonical).clone(),
                value,
            ),
        );
        canonical
    }

    fn build_natural_with_congr(
        &mut self,
        emit: &mut DraftEmit<'_>,
        function: &FuncType,
        args: &[DraftOperand],
    ) -> DraftNatural {
        let natural_args = args.iter().map(|arg| arg.natural.clone()).collect();
        let dedup_args: Vec<_> = args.iter().map(|arg| arg.value.clone()).collect();
        let natural = self.term_mint(emit.actions, function, natural_args);
        let to_dedup = emit.head.composes().then(|| {
            let sort = self.term_sort(&function.name);
            let own = self.reflexive_for_rule(emit, &natural, &sort);
            let mut steps = vec![];
            for (index, arg) in args.iter().enumerate() {
                if let Some(connector) = &arg.connector {
                    steps.push((index, self.connector_node(emit, connector)));
                }
            }
            self.canonicalize(own, steps)
        });
        DraftNatural {
            dedup_args,
            natural,
            to_dedup,
        }
    }

    fn add_constructor_with_proof(
        &mut self,
        emit: &mut DraftEmit<'_>,
        function: &FuncType,
        args: &[DraftOperand],
        run: Option<HeadRun>,
    ) -> DraftOperand {
        let DraftNatural {
            dedup_args,
            natural,
            to_dedup,
        } = self.build_natural_with_congr(emit, function, args);
        let canonical_term = self.term_mint(emit.actions, function, dedup_args.clone());
        let canonical_proof = if let Some(chain) = &to_dedup {
            self.reflexive(chain.clone())
        } else {
            let justification = emit
                .justification
                .at(self.column(run, HeadProof::Canonical));
            self.reflexive_for_rule(
                &mut emit.justified_by(&justification),
                &canonical_term,
                &self.term_sort(&function.name),
            )
        };
        self.emit_pending_group(emit.actions, &canonical_proof);
        let canonical = self.fresh_expr(SortKey::from_sort(function.output()));
        let canonical_proof_expr = self.proof_expr(&canonical_proof);
        let set_if_empty = self.set_if_empty(
            function,
            dedup_args.clone(),
            canonical_term,
            canonical_proof_expr,
        );
        self.emit_action(
            emit.actions,
            GenericAction::Let(
                self.span.clone(),
                Self::expect_variable(&canonical).clone(),
                set_if_empty,
            ),
        );
        let view_proof = self.fresh_expr(self.carry_sort.clone());
        let canonical_proof_expr = self.proof_expr(&canonical_proof);
        let read = self.read_view_proof(function, dedup_args, canonical_proof_expr);
        self.emit_action(
            emit.actions,
            GenericAction::Let(
                self.span.clone(),
                Self::expect_variable(&view_proof).clone(),
                read,
            ),
        );
        let view_name = Self::expect_variable(&view_proof).name.clone();
        emit.head.record_bridge(&view_name);
        let connector = match to_dedup {
            Some(chain) => Connector::Node(self.level_connector(&chain, &view_name)),
            None => Connector::Column(
                run.expect("numbered rule-head constructor")
                    .column(HeadProof::Connector),
            ),
        };
        DraftOperand::built(canonical, natural, connector)
    }

    fn add_term_and_view(
        &mut self,
        emit: &mut DraftEmit<'_>,
        function: &FuncType,
        args: &[DraftOperand],
        run: Option<HeadRun>,
    ) -> DraftOperand {
        if function.subtype != FunctionSubtype::Constructor {
            DraftOperand::plain(self.add_custom_row(
                emit,
                function,
                args.iter().map(|arg| arg.value.clone()).collect(),
            ))
        } else if !self.proofs {
            DraftOperand::plain(self.add_constructor_term_only(
                emit.actions,
                function,
                args.iter().map(|arg| arg.value.clone()).collect(),
            ))
        } else {
            self.add_constructor_with_proof(emit, function, args, run)
        }
    }

    fn lookup_global(&mut self, actions: &mut Vec<DraftAction>, function: &FuncType) -> DraftExpr {
        let fallback = self.get_fresh(actions, self.term_sort(&function.name));
        let proof = if self.proofs {
            self.get_fresh(actions, self.carry_sort.clone())
        } else {
            GenericExpr::Lit(self.span.clone(), Literal::Unit)
        };
        let value = self.fresh_expr(SortKey::from_sort(function.output()));
        let read = self.set_if_empty(function, vec![], fallback, proof);
        self.emit_action(
            actions,
            GenericAction::Let(
                self.span.clone(),
                Self::expect_variable(&value).clone(),
                read,
            ),
        );
        value
    }

    fn global_value_proof(
        &mut self,
        emit: &mut DraftEmit<'_>,
        function: &FuncType,
        value: &DraftOperand,
    ) -> String {
        match &value.connector {
            Some(Connector::Node(connector)) => {
                let sym = self.instrumentor.proof_names().eq_sym_constructor.clone();
                let trans = self.instrumentor.proof_names().eq_trans_constructor.clone();
                let connector_expr = self.proof_expr(connector);
                let reversed = self.mint(
                    emit.actions,
                    &sym,
                    vec![connector_expr],
                    self.carry_sort.clone(),
                );
                let connector_expr = self.proof_expr(connector);
                let proof = self.mint(
                    emit.actions,
                    &trans,
                    vec![reversed, connector_expr],
                    self.carry_sort.clone(),
                );
                Self::expect_variable(&proof).name.clone()
            }
            Some(Connector::Column(column)) => {
                panic!("a global value cannot be named by rule-head column {column}")
            }
            None => self.reflexive_for_rule(emit, &value.value, &self.term_sort(&function.name)),
        }
    }

    fn term_relation_key(&self, function: &FuncType, args: &[DraftExpr]) -> CallKey {
        self.relation_call_key(
            function.name.clone(),
            args.iter().map(Self::scalar_expr_sort).collect(),
        )
    }

    fn instrument_action_expr(
        &mut self,
        expr: &ResolvedExpr,
        emit: &mut DraftEmit<'_>,
        scope: &DraftScope,
    ) -> DraftOperand {
        match expr {
            GenericExpr::Lit(_, literal) => {
                DraftOperand::plain(GenericExpr::Lit(self.span.clone(), literal.clone()))
            }
            GenericExpr::Var(_, variable) => {
                if variable.is_global_ref {
                    let variable = self.variable(
                        variable.name.clone(),
                        SortKey::from_sort(&variable.sort),
                        GeneratedVarRole::Global,
                    );
                    DraftOperand::plain(GenericExpr::Var(self.span.clone(), variable))
                } else if let Some(operand) = scope.0.get(&variable.name) {
                    operand.clone()
                } else {
                    let variable = self.variable(
                        variable.name.clone(),
                        SortKey::from_sort(&variable.sort),
                        GeneratedVarRole::Local,
                    );
                    DraftOperand::plain(GenericExpr::Var(self.span.clone(), variable))
                }
            }
            GenericExpr::Call(_, call, source_args) => {
                let args: Vec<_> = source_args
                    .iter()
                    .map(|arg| self.instrument_action_expr(arg, emit, scope))
                    .collect();
                let run = emit.head.claim(if constructor_operand(expr).is_some() {
                    HeadPosition::Built
                } else {
                    HeadPosition::Call
                });
                let justification = emit.justification.at(self.column(run, HeadProof::Own));
                let emit = &mut emit.justified_by(&justification);
                match call {
                    ResolvedCall::Func(function) => {
                        if function.subtype == FunctionSubtype::Custom {
                            if self.instrumentor.egraph.type_info.is_global(&function.name) {
                                DraftOperand::plain(self.lookup_global(emit.actions, function))
                            } else {
                                panic!(
                                    "function lookup in rule actions should be rejected before proof encoding"
                                )
                            }
                        } else {
                            self.add_term_and_view(emit, function, &args, run)
                        }
                    }
                    ResolvedCall::Primitive(primitive) => {
                        let container_proof =
                            self.proofs && primitive.output().is_eq_container_sort();
                        let mut build_args = Vec::with_capacity(args.len());
                        for (arg, input_sort) in args.iter().zip(primitive.input()) {
                            match &arg.connector {
                                Some(connector) if container_proof && input_sort.is_eq_sort() => {
                                    let connector = self.connector_node(emit, connector);
                                    self.emit_pending_group(emit.actions, &connector);
                                    let uf = self.uf_call_key(SortKey::from_sort(input_sort));
                                    let carried = self.proof_expr(&connector);
                                    let value = self.values(vec![arg.value.clone(), carried]);
                                    self.emit_action(
                                        emit.actions,
                                        GenericAction::Set(
                                            self.span.clone(),
                                            uf,
                                            vec![arg.natural.clone()],
                                            value,
                                        ),
                                    );
                                    build_args.push(arg.natural.clone());
                                }
                                _ => build_args.push(arg.value.clone()),
                            }
                        }
                        let value = self.fresh_expr(SortKey::from_sort(primitive.output()));
                        let computed = GenericExpr::Call(
                            self.span.clone(),
                            CallKey::from_resolved(call),
                            build_args,
                        );
                        self.emit_action(
                            emit.actions,
                            GenericAction::Let(
                                self.span.clone(),
                                Self::expect_variable(&value).clone(),
                                computed,
                            ),
                        );
                        DraftOperand::plain(value)
                    }
                    ResolvedCall::Values(_) => {
                        panic!("tuple-output (`values`) calls are unsupported in proofs")
                    }
                }
            }
        }
    }

    fn ordered_endpoints(
        &self,
        left: &DraftOperand,
        right: &DraftOperand,
        sort: SortKey,
    ) -> (DraftExpr, DraftExpr) {
        (
            self.primitive(
                "ordering-max",
                vec![left.value.clone(), right.value.clone()],
                sort.clone(),
            ),
            self.primitive(
                "ordering-min",
                vec![left.value.clone(), right.value.clone()],
                sort,
            ),
        )
    }

    fn skeleton_union_edge(
        &mut self,
        emit: &mut DraftEmit<'_>,
        left: &DraftOperand,
        right: &DraftOperand,
        run: Option<HeadRun>,
    ) -> String {
        let run = run.expect("rule-head union must have numbered columns");
        let oriented = self.primitive(
            "proof-of-max",
            vec![
                left.value.clone(),
                GenericExpr::Lit(
                    self.span.clone(),
                    Literal::Int(run.column(HeadProof::EdgeFromLhs) as i64),
                ),
                right.value.clone(),
                GenericExpr::Lit(
                    self.span.clone(),
                    Literal::Int(run.column(HeadProof::EdgeFromRhs) as i64),
                ),
            ],
            self.i64_sort.clone(),
        );
        let justification = emit.justification.at(oriented);
        self.rule_row(&mut emit.justified_by(&justification))
    }

    fn union(
        &mut self,
        emit: &mut DraftEmit<'_>,
        sort: SortKey,
        left: &DraftOperand,
        right: &DraftOperand,
    ) -> DraftAction {
        let run = emit.head.claim(HeadPosition::Union);
        let (larger, smaller) = self.ordered_endpoints(left, right, sort.clone());
        let proof = if self.proofs {
            self.skeleton_union_edge(emit, left, right, run)
        } else {
            "()".to_owned()
        };
        let carried = if self.proofs {
            self.proof_expr(&proof)
        } else {
            GenericExpr::Lit(self.span.clone(), Literal::Unit)
        };
        GenericAction::Set(
            self.span.clone(),
            self.uf_call_key(sort),
            vec![larger],
            self.values(vec![smaller, carried]),
        )
    }

    fn instrument_construct_into(
        &mut self,
        emit: &mut DraftEmit<'_>,
        expr: &ResolvedExpr,
        target: &DraftOperand,
        scope: &DraftScope,
    ) -> DraftOperand {
        let (function, source_args) = constructor_operand(expr)
            .expect("construct-into guest must be a constructor application");
        let args: Vec<_> = source_args
            .iter()
            .map(|arg| self.instrument_action_expr(arg, emit, scope))
            .collect();
        let run = emit.head.claim(HeadPosition::Guest);
        let child_values: Vec<_> = args.iter().map(|arg| arg.value.clone()).collect();
        if !self.proofs {
            let mut row_args = child_values.clone();
            row_args.push(target.value.clone());
            let relation = self.term_relation_key(function, &row_args);
            self.emit_action(
                emit.actions,
                GenericAction::Set(
                    self.span.clone(),
                    relation,
                    row_args,
                    GenericExpr::Lit(self.span.clone(), Literal::Unit),
                ),
            );
            self.update_view(
                emit.actions,
                function,
                child_values,
                target.value.clone(),
                GenericExpr::Lit(self.span.clone(), Literal::Unit),
            );
            return DraftOperand::plain(target.value.clone());
        }

        let own = emit.justification.at(self.column(run, HeadProof::Own));
        let DraftNatural {
            dedup_args,
            natural,
            to_dedup,
        } = self.build_natural_with_congr(&mut emit.justified_by(&own), function, &args);
        let view_proof = if let Some(chain) = &to_dedup {
            let edge = self.rule_row(emit);
            let target_connector = target
                .connector
                .as_ref()
                .map(|connector| self.connector_node(emit, connector));
            self.guest_view(edge, chain.clone(), target_connector)
        } else {
            let justification = emit
                .justification
                .at(self.column(run, HeadProof::GuestView));
            self.rule_row(&mut emit.justified_by(&justification))
        };
        self.emit_pending_group(emit.actions, &view_proof);
        let view_proof_expr = self.proof_expr(&view_proof);
        self.update_view(
            emit.actions,
            function,
            dedup_args,
            target.value.clone(),
            view_proof_expr,
        );
        let connector = match to_dedup {
            Some(chain) => Connector::Node(self.level_connector(&chain, &view_proof)),
            None => Connector::Column(
                run.expect("numbered construct-into guest")
                    .column(HeadProof::Connector),
            ),
        };
        DraftOperand::built(target.value.clone(), natural, connector)
    }
}

impl SourceRuleLowerer<'_, '_> {
    fn instrument_action(
        &mut self,
        action: &ResolvedAction,
        emit: &mut DraftEmit<'_>,
        scope: &mut DraftScope,
    ) {
        match action {
            GenericAction::Let(_, variable, expr) => {
                let operand = self.instrument_action_expr(expr, emit, scope);
                let bound_variable = self.variable(
                    variable.name.clone(),
                    SortKey::from_sort(&variable.sort),
                    if variable.is_global_ref {
                        GeneratedVarRole::Global
                    } else {
                        GeneratedVarRole::Local
                    },
                );
                let bound = GenericExpr::Var(self.span.clone(), bound_variable);
                self.emit_action(
                    emit.actions,
                    GenericAction::Let(
                        self.span.clone(),
                        Self::expect_variable(&bound).clone(),
                        operand.value.clone(),
                    ),
                );
                scope.bind(&variable.name, &operand, bound);
            }
            GenericAction::Set(_, call, source_args, source_value) => {
                let ResolvedCall::Func(function) = call else {
                    panic!("set on a primitive should have been rejected by typechecking")
                };
                let mut values = Vec::with_capacity(source_args.len() + 1);
                for expr in source_args.iter().chain(std::iter::once(source_value)) {
                    values.push(self.instrument_action_expr(expr, emit, scope));
                }
                assert_ne!(
                    function.subtype,
                    FunctionSubtype::Constructor,
                    "set on a constructor should have been rejected by typechecking"
                );
                let run = emit.head.claim(HeadPosition::Set);
                if source_args.is_empty()
                    && self.instrumentor.egraph.type_info.is_global(&function.name)
                {
                    let value = values.pop().expect("set must have an output value");
                    let proof = if self.proofs {
                        let proof = self.global_value_proof(emit, function, &value);
                        self.proof_expr(&proof)
                    } else {
                        GenericExpr::Lit(self.span.clone(), Literal::Unit)
                    };
                    let relation =
                        self.term_relation_key(function, std::slice::from_ref(&value.value));
                    self.emit_action(
                        emit.actions,
                        GenericAction::Set(
                            self.span.clone(),
                            relation,
                            vec![value.value.clone()],
                            GenericExpr::Lit(self.span.clone(), Literal::Unit),
                        ),
                    );
                    self.update_view(emit.actions, function, vec![], value.value, proof);
                    return;
                }
                let own = emit.justification.at(self.column(run, HeadProof::Own));
                self.add_term_and_view(&mut emit.justified_by(&own), function, &values, run);
            }
            GenericAction::Change(span, change, call, source_args) => {
                let ResolvedCall::Func(function) = call else {
                    panic!("change on a primitive should have been rejected by typechecking")
                };
                let children = emit.composing(|emit| {
                    source_args
                        .iter()
                        .map(|expr| self.instrument_action_expr(expr, emit, scope))
                        .collect::<Vec<_>>()
                });
                let args: Vec<_> = children.into_iter().map(|child| child.value).collect();
                match change {
                    Change::Delete => {
                        let key = self.view_call_key(function);
                        self.emit_action(
                            emit.actions,
                            GenericAction::Change(self.span.clone(), Change::Delete, key, args),
                        );
                    }
                    Change::Subsume => {
                        let name = self.instrumentor.subsume_marker(span, function);
                        let key = self.relation_call_key(
                            name,
                            function.input.iter().map(SortKey::from_sort).collect(),
                        );
                        self.emit_action(
                            emit.actions,
                            GenericAction::Set(
                                self.span.clone(),
                                key,
                                args,
                                GenericExpr::Lit(self.span.clone(), Literal::Unit),
                            ),
                        );
                    }
                }
            }
            GenericAction::Union(_, left, right) => {
                let sort = SortKey::from_sort(&left.output_type());
                let left = self.instrument_action_expr(left, emit, scope);
                let right = self.instrument_action_expr(right, emit, scope);
                let action = self.union(emit, sort, &left, &right);
                self.emit_action(emit.actions, action);
            }
            GenericAction::Panic(_, message) => emit
                .actions
                .push(GenericAction::Panic(self.span.clone(), message.clone())),
            GenericAction::Expr(_, expr) => {
                self.instrument_action_expr(expr, emit, scope);
            }
        }
    }

    fn instrument_actions(
        &mut self,
        actions: &[ResolvedAction],
        justification: &RuleJustification,
    ) -> Vec<DraftAction> {
        let plan = {
            let symbol_gen = &mut self.instrumentor.egraph.parser.symbol_gen;
            let mut fresh = || symbol_gen.fresh("union_operand");
            HeadPlan::new(actions, &mut fresh)
        };
        // The layout remains useful in term mode for preserving the exact
        // position walk even though no proof column is materialized there.
        let mut head = Head::skeleton(plan.layout.clone());
        let mut scope = DraftScope::default();
        let mut lowered = vec![];
        let mut emit = DraftEmit {
            actions: &mut lowered,
            head: &mut head,
            justification,
        };
        for (index, action) in plan.actions.iter().enumerate() {
            if plan.dropped.contains(&index) {
                continue;
            }
            match action {
                GenericAction::Let(_, variable, expr)
                    if plan.construct_into.contains_key(&variable.name) =>
                {
                    let target_name = &plan.construct_into[&variable.name];
                    let target_sort = self
                        .variables
                        .get(&(target_name.clone(), GeneratedVarRole::Local))
                        .unwrap_or_else(|| {
                            panic!("construct-into target `{target_name}` has no recorded sort")
                        })
                        .clone();
                    let target_variable =
                        self.variable(target_name.clone(), target_sort, GeneratedVarRole::Local);
                    let target_expr = GenericExpr::Var(self.span.clone(), target_variable);
                    let target_operand = scope
                        .0
                        .get(target_name)
                        .cloned()
                        .unwrap_or_else(|| DraftOperand::plain(target_expr));
                    let guest =
                        self.instrument_construct_into(&mut emit, expr, &target_operand, &scope);
                    let bound_variable = self.variable(
                        variable.name.clone(),
                        SortKey::from_sort(&variable.sort),
                        if variable.is_global_ref {
                            GeneratedVarRole::Global
                        } else {
                            GeneratedVarRole::Local
                        },
                    );
                    let bound = GenericExpr::Var(self.span.clone(), bound_variable);
                    self.emit_action(
                        emit.actions,
                        GenericAction::Let(
                            self.span.clone(),
                            Self::expect_variable(&bound).clone(),
                            guest.value.clone(),
                        ),
                    );
                    scope.bind(&variable.name, &guest, bound);
                }
                _ => self.instrument_action(action, &mut emit, &mut scope),
            }
        }
        lowered
    }

    fn lower_rule(&mut self, rule: &ResolvedRule) -> DraftRule {
        self.proofs_state = DeferredProofs::default();
        if self.proofs {
            self.anchors = BodyAnchors::default();
            self.unanchored.clear();
        }

        let (body, mut actions, premises) = self.instrument_facts(&rule.body);
        let rule_name = if self.proofs {
            let name = self
                .instrumentor
                .egraph
                .parser
                .symbol_gen
                .fresh("rule_name");
            let rule_name_variable = self.variable(
                name.clone(),
                self.string_sort.clone(),
                GeneratedVarRole::Local,
            );
            let variable = GenericExpr::Var(self.span.clone(), rule_name_variable);
            actions.insert(
                0,
                GenericAction::Let(
                    self.span.clone(),
                    Self::expect_variable(&variable).clone(),
                    GenericExpr::Lit(self.span.clone(), Literal::String(rule.name.clone())),
                ),
            );
            Some(name)
        } else {
            None
        };
        let justification = RuleJustification {
            rule_name,
            premises,
            column: GenericExpr::Lit(self.span.clone(), Literal::Int(-1)),
        };
        actions.extend(self.instrument_actions(&rule.head.0, &justification));

        // Anything still deferred reached no emitted statement and must not
        // leak into the next rule.
        self.proofs_state.discard_unobserved();
        if self.proofs {
            self.unanchored.clear();
        }

        let eval_mode = if rule.eval_mode.is_naive()
            || (self.proofs && self.instrumentor.egraph.proof_state.force_proof_naive)
        {
            RuleEvalMode::Naive
        } else if self.proofs {
            RuleEvalMode::UnsafeSeminaive
        } else {
            RuleEvalMode::Seminaive
        };
        GenericRule {
            span: self.span.clone(),
            body,
            head: GenericActions(actions),
            name: rule.name.clone(),
            ruleset: rule.ruleset.clone(),
            eval_mode,
            // Source-rule instrumentation does not carry internal maintenance
            // flags, regardless of their values on the source rule.
            no_decomp: false,
            include_subsumed: false,
        }
    }
}

fn final_generated_var(
    variables: &mut HashMap<(String, GeneratedVarRole), GeneratedVar>,
    next: &mut u32,
    variable: DraftVar,
) -> GeneratedVar {
    let identity = (variable.name.clone(), variable.role);
    if let Some(existing) = variables.get(&identity) {
        assert_eq!(
            existing.sort, variable.sort,
            "source-rule variable `{}` changed sort during finalization",
            variable.name
        );
        return existing.clone();
    }
    let generated = GeneratedVar {
        id: LocalId(*next),
        name: variable.name.clone(),
        sort: variable.sort,
        role: variable.role,
    };
    *next = next
        .checked_add(1)
        .expect("source-rule finalizer exhausted portable local IDs");
    variables.insert(identity, generated.clone());
    generated
}

/// Finalize in query-then-head lexical order.  `GenericRule::map_symbols`
/// visits the head first, so using it directly would give body variables IDs
/// after head-only temporaries.
fn finalize_rule(rule: DraftRule) -> GeneratedRule {
    let DraftRule {
        span,
        head,
        body,
        name,
        ruleset,
        eval_mode,
        no_decomp,
        include_subsumed,
    } = rule;
    let mut variables = HashMap::default();
    let mut next = 0;
    let mut map_head = |head: CallKey| head;
    let mut map_leaf =
        |variable: DraftVar| final_generated_var(&mut variables, &mut next, variable);
    let body: Vec<GeneratedFact> = body
        .into_iter()
        .map(|fact| fact.map_symbols(&mut map_head, &mut map_leaf))
        .collect();
    let head: GeneratedActions = head.map_symbols(&mut map_head, &mut map_leaf);
    GenericRule {
        span,
        head,
        body,
        name,
        ruleset,
        eval_mode,
        no_decomp,
        include_subsumed,
    }
}

/// Assign one portable local namespace in the same lexical order a query
/// consumer observes: retained facts first, then the explicitly exposed
/// auxiliary lookup actions and premise values.
fn finalize_query(
    facts: Vec<DraftFact>,
    action_lookups: GenericActions<CallKey, DraftVar>,
    premises: Vec<DraftExpr>,
) -> LoweredQueryFacts {
    let mut variables = HashMap::default();
    let mut next = 0;
    let mut map_head = |head: CallKey| head;
    let mut map_leaf =
        |variable: DraftVar| final_generated_var(&mut variables, &mut next, variable);
    let facts = facts
        .into_iter()
        .map(|fact| fact.map_symbols(&mut map_head, &mut map_leaf))
        .collect();
    let action_lookups = action_lookups.map_symbols(&mut map_head, &mut map_leaf);
    let premises = premises
        .into_iter()
        .map(|premise| premise.map_symbols(&mut map_head, &mut map_leaf))
        .collect();
    LoweredQueryFacts {
        facts,
        action_lookups,
        premises,
    }
}
