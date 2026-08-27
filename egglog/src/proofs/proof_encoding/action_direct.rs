//! Portable typed lowering for standalone source actions.
//!
//! A source `Action` or `Actions` command is lowered as one lexical local-scope
//! block.  The block is absent when instrumentation emits no statements (for
//! example a literal-only `Expr`).  Fresh spellings continue to come from the
//! production [`ProofInstrumentor`], while portable calls are resolved only by
//! the generated binder's shared signature catalog.
//!
//! `CoreActions` has no separate wrapper span, so the first source action's span
//! is the enclosing generated-command span. Every synthesized helper call and
//! action uses that envelope; source literal/variable leaves and a passthrough
//! `panic` retain their own spans. Thus diagnostics always point into stable
//! source text rather than a synthesized representation.

use std::fmt::Display;
use std::hash::Hash;

use crate::ast::{
    GenericAction, GenericActions, GenericExpr, Literal, ResolvedAction, ResolvedExpr,
    ResolvedExprExt, Span,
};
use crate::core::ResolvedCall;
use crate::proofs::generated_binder::{
    CallKey, FunctionKey, GeneratedAction, GeneratedActions, GeneratedExpr, GeneratedRuleBuilder,
    GeneratedSignatureCatalog, GeneratedVar, GeneratedVarRole, PrimitiveKey, SortKey,
    SortSemanticClass, ValueShape,
};
use crate::proofs::proof_encoding_helpers::{Composition, EncodingNames, ProofTree};
use crate::proofs::proof_fresh::{
    GET_FRESH_PRIM_NAME, mint_prim_name, set_if_empty_prim_name, view_proof_prim_name,
};
use crate::proofs::proof_head::{ProofAlgebra, constructor_operand};
use crate::typechecking::FuncType;
use crate::util::{FreshGen, HashMap, HashSet};
use crate::{Change, FunctionSubtype, literal_sort};

use super::{Connector, ProofInstrumentor};

type ActionExpr = GeneratedExpr;
type ActionStmt = GeneratedAction;

#[derive(Clone)]
pub(super) struct EmissionOperand<E, C> {
    pub(super) value: E,
    pub(super) natural: E,
    pub(super) connector: Option<C>,
}

impl<E: Clone, C> EmissionOperand<E, C> {
    pub(super) fn plain(value: E) -> Self {
        Self {
            natural: value.clone(),
            value,
            connector: None,
        }
    }
}

impl<E, C> EmissionOperand<E, C> {
    pub(super) fn built(value: E, natural: E, connector: C) -> Self {
        Self {
            value,
            natural,
            connector: Some(connector),
        }
    }
}

pub(super) struct EmissionScope<E, C>(pub(super) HashMap<String, EmissionOperand<E, C>>);

impl<E, C> Default for EmissionScope<E, C> {
    fn default() -> Self {
        Self(HashMap::default())
    }
}

impl<E: Clone, C: Clone> EmissionScope<E, C> {
    pub(super) fn bind(&mut self, name: &str, operand: &EmissionOperand<E, C>, bound: E) {
        if operand.connector.is_some() {
            self.0.insert(
                name.to_owned(),
                EmissionOperand {
                    value: bound,
                    ..operand.clone()
                },
            );
        }
    }
}

pub(super) struct EmissionNatural<E, D> {
    pub(super) dedup_args: Vec<E>,
    pub(super) natural: E,
    pub(super) to_dedup: D,
}

pub(super) enum Deferred<A> {
    Actions(Vec<A>),
    Composed(Composition),
}

pub(super) enum PlannedComposition {
    Existing(String),
    Deferred(Composition),
}

impl PlannedComposition {
    pub(super) fn realize(self, compose: impl FnOnce(Composition) -> String) -> String {
        match self {
            Self::Existing(proof) => proof,
            Self::Deferred(composition) => compose(composition),
        }
    }
}

pub(super) struct DeferredProofs<A> {
    pub(super) reflexive: HashSet<String>,
    pub(super) pending: HashMap<String, Deferred<A>>,
    pub(super) sealed: HashSet<String>,
}

impl<A> Default for DeferredProofs<A> {
    fn default() -> Self {
        Self {
            reflexive: HashSet::default(),
            pending: HashMap::default(),
            sealed: HashSet::default(),
        }
    }
}

impl<A> DeferredProofs<A> {
    pub(super) fn discard_unobserved(&mut self) {
        self.pending.clear();
        self.sealed.clear();
    }

    pub(super) fn composition(&self, proof: &str) -> Composition {
        match self.pending.get(proof) {
            Some(Deferred::Composed(composition)) if !self.sealed.contains(proof) => {
                composition.clone()
            }
            _ => Composition::Leaf(proof.to_owned()),
        }
    }

    pub(super) fn defer(&mut self, proof: String, composition: Composition) -> String {
        self.pending
            .insert(proof.clone(), Deferred::Composed(composition));
        proof
    }

    pub(super) fn sym(&self, proof: String) -> PlannedComposition {
        if self.reflexive.contains(&proof) {
            PlannedComposition::Existing(proof)
        } else {
            PlannedComposition::Deferred(self.composition(&proof).sym())
        }
    }

    pub(super) fn trans(&self, left: String, right: String) -> PlannedComposition {
        if self.reflexive.contains(&left) {
            PlannedComposition::Existing(right)
        } else if self.reflexive.contains(&right) {
            PlannedComposition::Existing(left)
        } else {
            PlannedComposition::Deferred(self.composition(&left).trans(self.composition(&right)))
        }
    }

    pub(super) fn congr(&self, base: String, child: usize, step: String) -> PlannedComposition {
        if self.reflexive.contains(&step) {
            PlannedComposition::Existing(base)
        } else {
            PlannedComposition::Deferred(
                self.composition(&base)
                    .congr(child, self.composition(&step)),
            )
        }
    }
}

pub(super) trait PendingLocal: Clone + Eq + Display + Hash {
    fn pending_local(&self) -> Option<&str>;
}

impl PendingLocal for GeneratedVar {
    fn pending_local(&self) -> Option<&str> {
        (self.role == GeneratedVarRole::Local).then_some(&self.name)
    }
}

fn visit_expr_dependencies<C, V: PendingLocal>(
    expr: &GenericExpr<C, V>,
    visit: &mut impl FnMut(&str),
) {
    match expr {
        GenericExpr::Var(_, variable) => {
            if let Some(name) = variable.pending_local() {
                visit(name);
            }
        }
        GenericExpr::Call(_, _, args) => {
            for arg in args {
                visit_expr_dependencies(arg, visit);
            }
        }
        GenericExpr::Lit(..) => {}
    }
}

/// Visit action inputs in evaluation order so deferred proof groups are
/// materialized before the action which first observes them.
pub(super) fn visit_action_dependencies<C: Clone + Display, V: PendingLocal>(
    action: &GenericAction<C, V>,
    visit: &mut impl FnMut(&str),
) {
    match action {
        GenericAction::Let(_, _, value) | GenericAction::Expr(_, value) => {
            visit_expr_dependencies(value, visit)
        }
        GenericAction::Set(_, _, args, value) => {
            for arg in args {
                visit_expr_dependencies(arg, visit);
            }
            visit_expr_dependencies(value, visit);
        }
        GenericAction::Change(_, _, _, args) => {
            for arg in args {
                visit_expr_dependencies(arg, visit);
            }
        }
        GenericAction::Union(_, left, right) => {
            visit_expr_dependencies(left, visit);
            visit_expr_dependencies(right, visit);
        }
        GenericAction::Panic(..) => {}
    }
}

pub(super) fn proof_constructor(
    composition: &Composition,
    names: &EncodingNames,
) -> Option<String> {
    Some(match composition {
        ProofTree::Sym(_) => names.eq_sym_constructor.clone(),
        ProofTree::Trans(_, _) => names.eq_trans_constructor.clone(),
        ProofTree::Congr(_, _, _) => names.congr_constructor.clone(),
        ProofTree::Proj(_, _) => names.proj_constructor.clone(),
        ProofTree::Leaf(_) => return None,
    })
}

pub(super) fn lower_single_step<V>(
    composition: &Composition,
    relation: String,
    span: &Span,
    mut proof_expr: impl FnMut(&str) -> GenericExpr<CallKey, V>,
) -> Option<(String, Vec<GenericExpr<CallKey, V>>)> {
    let args = match composition {
        ProofTree::Sym(inner) => vec![proof_expr(inner.leaf()?)],
        ProofTree::Trans(left, right) => {
            vec![proof_expr(left.leaf()?), proof_expr(right.leaf()?)]
        }
        ProofTree::Congr(base, index, child) => vec![
            proof_expr(base.leaf()?),
            GenericExpr::Lit(span.clone(), Literal::Int(*index as i64)),
            proof_expr(child.leaf()?),
        ],
        ProofTree::Proj(base, index) => vec![
            proof_expr(base.leaf()?),
            GenericExpr::Lit(span.clone(), Literal::Int(*index as i64)),
        ],
        ProofTree::Leaf(_) => return None,
    };
    Some((relation, args))
}

type Operand = EmissionOperand<ActionExpr, Connector>;
type Scope = EmissionScope<ActionExpr, Connector>;
type Natural = EmissionNatural<ActionExpr, String>;

struct ActionLowerer<'instrumentor, 'egraph> {
    instrumentor: &'instrumentor mut ProofInstrumentor<'egraph>,
    span: Span,
    proofs: bool,
    unit_sort: SortKey,
    carry_sort: SortKey,
    builder: GeneratedRuleBuilder,
    variables: HashMap<(String, GeneratedVarRole), SortKey>,
    proofs_state: DeferredProofs<ActionStmt>,
}

/// Lower one source action command to its portable semantic payload.
///
/// The caller must wrap a returned payload as `GeneratedCommand::Actions`
/// after this function's mutable `ProofInstrumentor` borrow ends.  Keeping the
/// result catalog-free lets that caller then register its signatures after the
/// mutable lowering borrow ends. The wrapper must always be
/// `Actions`, never a top-level `Action`, so all generated `let`s and source
/// block locals share one scope.  `None` preserves the source parser's
/// zero-command result for an expression that emits no instrumentation
/// statements.
pub(super) fn lower(
    instrumentor: &mut ProofInstrumentor<'_>,
    actions: &[ResolvedAction],
) -> Option<GeneratedActions> {
    let first = actions.first()?;
    let span = match first {
        GenericAction::Let(span, ..)
        | GenericAction::Set(span, ..)
        | GenericAction::Change(span, ..)
        | GenericAction::Union(span, ..)
        | GenericAction::Panic(span, ..)
        | GenericAction::Expr(span, ..) => span.clone(),
    };
    let mut lowerer = ActionLowerer::new(instrumentor, span);
    let lowered = lowerer.lower_actions(actions);

    // A connector nothing consumes has no observable row and must not survive
    // into the next command.
    lowerer.proofs_state.discard_unobserved();

    if lowered.is_empty() {
        None
    } else {
        Some(GenericActions(lowered))
    }
}

/// Typed setup actions and values for consumers such as extraction that use
/// standalone action-expression semantics without emitting an action command.
pub(super) struct LoweredExpressions {
    pub(super) setup: GeneratedActions,
    pub(super) values: Vec<GeneratedExpr>,
}

/// Lower a nonempty expression sequence in one lexical session under
/// Fiat/composed semantics. Consumers use the first source expression as the
/// generated setup envelope; accepting an empty sequence would force emitted
/// helpers to carry a synthetic span.
pub(super) fn lower_expressions(
    instrumentor: &mut ProofInstrumentor<'_>,
    expressions: &[&ResolvedExpr],
) -> LoweredExpressions {
    let first = expressions
        .first()
        .expect("typed expression lowering requires a source span");
    let span = match first {
        GenericExpr::Lit(span, ..) | GenericExpr::Var(span, ..) | GenericExpr::Call(span, ..) => {
            span.clone()
        }
    };
    let mut lowerer = ActionLowerer::new(instrumentor, span);
    let scope = Scope::default();
    let mut setup = vec![];
    let values = expressions
        .iter()
        .map(|expr| lowerer.instrument_expr(expr, &mut setup, &scope).value)
        .collect();
    lowerer.proofs_state.discard_unobserved();
    LoweredExpressions {
        setup: GenericActions(setup),
        values,
    }
}

pub(super) fn register_expression_signatures(
    lowered: &LoweredExpressions,
    catalog: &mut GeneratedSignatureCatalog,
) {
    register_signatures(&lowered.setup, catalog);
    for value in &lowered.values {
        register_expr_signatures(value, catalog);
    }
}

pub(super) fn value_sort(name: &str) -> SortKey {
    SortKey {
        name: name.to_owned(),
        class: SortSemanticClass::Value,
    }
}

impl<'instrumentor, 'egraph> ActionLowerer<'instrumentor, 'egraph> {
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
        ActionLowerer {
            instrumentor,
            span,
            proofs,
            unit_sort: value_sort("Unit"),
            carry_sort,
            builder: GeneratedRuleBuilder::default(),
            variables: HashMap::default(),
            proofs_state: DeferredProofs::default(),
        }
    }
}

impl ActionLowerer<'_, '_> {
    fn variable(
        &mut self,
        name: impl Into<String>,
        sort: SortKey,
        role: GeneratedVarRole,
    ) -> GeneratedVar {
        let name = name.into();
        let identity = (name.clone(), role);
        if let Some(existing) = self.variables.get(&identity) {
            assert_eq!(
                existing, &sort,
                "standalone-action variable `{name}` changed sort while lowering"
            );
        } else {
            self.variables.insert(identity, sort.clone());
        }
        self.builder
            .variable(name, sort, role, &self.span)
            .expect("standalone-action variable changed sort while lowering")
    }

    fn fresh_expr(&mut self, sort: SortKey) -> ActionExpr {
        let name = self.instrumentor.fresh_var();
        let variable = self.variable(name, sort, GeneratedVarRole::Local);
        GenericExpr::Var(self.span.clone(), variable)
    }

    fn primitive(
        &self,
        name: impl Into<String>,
        args: Vec<ActionExpr>,
        output: SortKey,
    ) -> ActionExpr {
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

    fn values(&self, values: Vec<ActionExpr>) -> ActionExpr {
        let sorts = values.iter().map(Self::scalar_expr_sort).collect();
        GenericExpr::Call(self.span.clone(), CallKey::Values(sorts), values)
    }

    fn scalar_expr_sort(expr: &ActionExpr) -> SortKey {
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

    fn expect_variable(expr: &ActionExpr) -> &GeneratedVar {
        let GenericExpr::Var(_, variable) = expr else {
            panic!("internal standalone-action lowering expected a variable")
        };
        variable
    }

    fn emit_action(&mut self, actions: &mut Vec<ActionStmt>, action: ActionStmt) {
        visit_action_dependencies(&action, &mut |proof| {
            self.emit_pending_group(actions, proof)
        });
        actions.push(action);
    }

    fn get_fresh(&mut self, actions: &mut Vec<ActionStmt>, sort: SortKey) -> ActionExpr {
        let target = self.fresh_expr(sort.clone());
        let sort_name = GenericExpr::Lit(self.span.clone(), Literal::String(sort.name.clone()));
        let value = self.primitive(GET_FRESH_PRIM_NAME, vec![sort_name], sort);
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

    fn mint_as(
        &mut self,
        actions: &mut Vec<ActionStmt>,
        target: ActionExpr,
        relation: &str,
        args: Vec<ActionExpr>,
        output: SortKey,
    ) -> ActionExpr {
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
        actions: &mut Vec<ActionStmt>,
        relation: &str,
        args: Vec<ActionExpr>,
        output: SortKey,
    ) -> ActionExpr {
        let target = self.fresh_expr(output.clone());
        self.mint_as(actions, target, relation, args, output)
    }

    fn proof_expr(&mut self, proof: &str) -> ActionExpr {
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

    fn single_step(&mut self, composition: &Composition) -> Option<(String, Vec<ActionExpr>)> {
        let relation = proof_constructor(composition, self.instrumentor.proof_names())?;
        let span = self.span.clone();
        lower_single_step(composition, relation, &span, |proof| self.proof_expr(proof))
    }

    fn emit_composition(
        &mut self,
        actions: &mut Vec<ActionStmt>,
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

    fn emit_pending_group(&mut self, actions: &mut Vec<ActionStmt>, proof: &str) {
        match self.proofs_state.pending.remove(proof) {
            Some(Deferred::Composed(composition)) => {
                self.emit_composition(actions, proof, composition)
            }
            Some(Deferred::Actions(_)) => {
                unreachable!("standalone action lowering never defers action groups")
            }
            None => {}
        }
    }

    fn fiat_reflexive(
        &mut self,
        actions: &mut Vec<ActionStmt>,
        value: ActionExpr,
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

    fn fiat_edge(
        &mut self,
        actions: &mut Vec<ActionStmt>,
        sort: &SortKey,
        left: ActionExpr,
        right: ActionExpr,
    ) -> String {
        let (relation, declaration) = self
            .instrumentor
            .plan_fiat_pending_direct(&self.span, sort.clone());
        self.instrumentor
            .queue_pending_declaration_group(declaration);
        let proof = self.mint(
            actions,
            &relation,
            vec![left, right],
            self.carry_sort.clone(),
        );
        Self::expect_variable(&proof).name.clone()
    }

    fn connector_node(&self, connector: &Connector) -> String {
        match connector {
            Connector::Node(node) => node.clone(),
            Connector::Column(column) => {
                panic!("standalone action unexpectedly references rule-head column {column}")
            }
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

    fn set_if_empty(
        &mut self,
        function: &FuncType,
        children: Vec<ActionExpr>,
        fallback: ActionExpr,
        proof: ActionExpr,
    ) -> ActionExpr {
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
        children: Vec<ActionExpr>,
        fallback: ActionExpr,
    ) -> ActionExpr {
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
        actions: &mut Vec<ActionStmt>,
        function: &FuncType,
        children: Vec<ActionExpr>,
        value: ActionExpr,
        proof: ActionExpr,
    ) {
        let key = self.view_call_key(function);
        let tuple = self.values(vec![value, proof]);
        self.emit_action(
            actions,
            GenericAction::Set(self.span.clone(), key, children, tuple),
        );
    }

    fn add_custom_row(
        &mut self,
        actions: &mut Vec<ActionStmt>,
        function: &FuncType,
        args: Vec<ActionExpr>,
    ) -> ActionExpr {
        let term_sort = self.term_sort(&function.name);
        let term = self.mint(actions, &function.name, args.clone(), term_sort);
        let proof = if self.proofs {
            let term_sort = self.term_sort(&function.name);
            let proof = self.fiat_reflexive(actions, term.clone(), term_sort);
            self.proof_expr(&proof)
        } else {
            GenericExpr::Lit(self.span.clone(), Literal::Unit)
        };
        let (output, children) = args
            .split_last()
            .expect("custom set must include an output value");
        self.update_view(actions, function, children.to_vec(), output.clone(), proof);
        term
    }

    fn add_constructor_term_only(
        &mut self,
        actions: &mut Vec<ActionStmt>,
        function: &FuncType,
        args: Vec<ActionExpr>,
    ) -> ActionExpr {
        let term_sort = self.term_sort(&function.name);
        let term = self.mint(actions, &function.name, args.clone(), term_sort);
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
        actions: &mut Vec<ActionStmt>,
        function: &FuncType,
        args: &[Operand],
    ) -> Natural {
        let natural_args = args.iter().map(|arg| arg.natural.clone()).collect();
        let dedup_args = args.iter().map(|arg| arg.value.clone()).collect();
        let term_sort = self.term_sort(&function.name);
        let natural = self.mint(actions, &function.name, natural_args, term_sort.clone());
        let own = self.fiat_reflexive(actions, natural.clone(), term_sort);
        let steps = args
            .iter()
            .enumerate()
            .filter_map(|(index, arg)| {
                arg.connector
                    .as_ref()
                    .map(|connector| (index, self.connector_node(connector)))
            })
            .collect::<Vec<_>>();
        let to_dedup = self.canonicalize(own, steps);
        Natural {
            dedup_args,
            natural,
            to_dedup,
        }
    }

    fn add_constructor_with_proof(
        &mut self,
        actions: &mut Vec<ActionStmt>,
        function: &FuncType,
        args: &[Operand],
    ) -> Operand {
        let Natural {
            dedup_args,
            natural,
            to_dedup,
        } = self.build_natural_with_congr(actions, function, args);
        let term_sort = self.term_sort(&function.name);
        let canonical_term = self.mint(actions, &function.name, dedup_args.clone(), term_sort);
        let canonical_proof = self.reflexive(to_dedup.clone());
        self.emit_pending_group(actions, &canonical_proof);

        let canonical = self.fresh_expr(SortKey::from_sort(function.output()));
        let fallback = self.proof_expr(&canonical_proof);
        let set_if_empty = self.set_if_empty(
            function,
            dedup_args.clone(),
            canonical_term,
            fallback.clone(),
        );
        self.emit_action(
            actions,
            GenericAction::Let(
                self.span.clone(),
                Self::expect_variable(&canonical).clone(),
                set_if_empty,
            ),
        );
        let view_proof = self.fresh_expr(self.carry_sort.clone());
        let read = self.read_view_proof(function, dedup_args, fallback);
        self.emit_action(
            actions,
            GenericAction::Let(
                self.span.clone(),
                Self::expect_variable(&view_proof).clone(),
                read,
            ),
        );
        let view_name = Self::expect_variable(&view_proof).name.clone();
        let connector = Connector::Node(self.level_connector(&to_dedup, &view_name));
        Operand::built(canonical, natural, connector)
    }

    fn add_term_and_view(
        &mut self,
        actions: &mut Vec<ActionStmt>,
        function: &FuncType,
        args: &[Operand],
    ) -> Operand {
        if function.subtype != FunctionSubtype::Constructor {
            Operand::plain(self.add_custom_row(
                actions,
                function,
                args.iter().map(|arg| arg.value.clone()).collect(),
            ))
        } else if self.proofs {
            self.add_constructor_with_proof(actions, function, args)
        } else {
            Operand::plain(self.add_constructor_term_only(
                actions,
                function,
                args.iter().map(|arg| arg.value.clone()).collect(),
            ))
        }
    }

    fn lookup_global(&mut self, actions: &mut Vec<ActionStmt>, function: &FuncType) -> ActionExpr {
        // These are deliberately unconstrained fresh fallbacks.  In a valid
        // source program the zero-input view already contains the global row;
        // a lookup must never mint a term row for the global itself.
        let term_sort = self.term_sort(&function.name);
        let fallback = self.get_fresh(actions, term_sort);
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
        actions: &mut Vec<ActionStmt>,
        function: &FuncType,
        value: &Operand,
    ) -> String {
        match &value.connector {
            Some(Connector::Node(connector)) => {
                let (sym_relation, trans_relation) = {
                    let names = self.instrumentor.proof_names();
                    (
                        names.eq_sym_constructor.clone(),
                        names.eq_trans_constructor.clone(),
                    )
                };
                let connector_expr = self.proof_expr(connector);
                let reversed = self.mint(
                    actions,
                    &sym_relation,
                    vec![connector_expr],
                    self.carry_sort.clone(),
                );
                let connector_expr = self.proof_expr(connector);
                let proof = self.mint(
                    actions,
                    &trans_relation,
                    vec![reversed, connector_expr],
                    self.carry_sort.clone(),
                );
                Self::expect_variable(&proof).name.clone()
            }
            Some(Connector::Column(column)) => {
                panic!("a standalone global value references rule-head column {column}")
            }
            None => {
                let term_sort = self.term_sort(&function.name);
                self.fiat_reflexive(actions, value.value.clone(), term_sort)
            }
        }
    }

    fn instrument_expr(
        &mut self,
        expr: &ResolvedExpr,
        actions: &mut Vec<ActionStmt>,
        scope: &Scope,
    ) -> Operand {
        match expr {
            GenericExpr::Lit(span, literal) => {
                Operand::plain(GenericExpr::Lit(span.clone(), literal.clone()))
            }
            GenericExpr::Var(span, variable) => {
                if variable.is_global_ref {
                    let variable = self.variable(
                        variable.name.clone(),
                        SortKey::from_sort(&variable.sort),
                        GeneratedVarRole::Global,
                    );
                    Operand::plain(GenericExpr::Var(span.clone(), variable))
                } else if let Some(operand) = scope.0.get(&variable.name) {
                    operand.clone()
                } else {
                    let variable = self.variable(
                        variable.name.clone(),
                        SortKey::from_sort(&variable.sort),
                        GeneratedVarRole::Local,
                    );
                    Operand::plain(GenericExpr::Var(span.clone(), variable))
                }
            }
            GenericExpr::Call(_, call, source_args) => {
                let args = source_args
                    .iter()
                    .map(|arg| self.instrument_expr(arg, actions, scope))
                    .collect::<Vec<_>>();
                match call {
                    ResolvedCall::Func(function) => {
                        if function.subtype == FunctionSubtype::Custom {
                            if self.instrumentor.egraph.type_info.is_global(&function.name) {
                                Operand::plain(self.lookup_global(actions, function))
                            } else {
                                panic!(
                                    "function lookup in standalone actions should be rejected before proof encoding"
                                )
                            }
                        } else {
                            self.add_term_and_view(actions, function, &args)
                        }
                    }
                    ResolvedCall::Primitive(primitive) => {
                        let container_proof =
                            self.proofs && primitive.output().is_eq_container_sort();
                        let mut build_args = Vec::with_capacity(args.len());
                        for (arg, input_sort) in args.iter().zip(primitive.input()) {
                            match &arg.connector {
                                Some(connector) if container_proof && input_sort.is_eq_sort() => {
                                    let connector = self.connector_node(connector);
                                    self.emit_pending_group(actions, &connector);
                                    let uf = self.uf_call_key(SortKey::from_sort(input_sort));
                                    let carried = self.proof_expr(&connector);
                                    let value = self.values(vec![arg.value.clone(), carried]);
                                    self.emit_action(
                                        actions,
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
                            actions,
                            GenericAction::Let(
                                self.span.clone(),
                                Self::expect_variable(&value).clone(),
                                computed,
                            ),
                        );
                        Operand::plain(value)
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
        left: &Operand,
        right: &Operand,
        sort: SortKey,
    ) -> (ActionExpr, ActionExpr) {
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

    fn composed_union_edge(
        &mut self,
        actions: &mut Vec<ActionStmt>,
        sort: &SortKey,
        left: &Operand,
        right: &Operand,
    ) -> String {
        if left.connector.is_none() && right.connector.is_none() {
            let (larger, smaller) = self.ordered_endpoints(left, right, sort.clone());
            return self.fiat_edge(actions, sort, larger, smaller);
        }

        let base = self.fiat_edge(actions, sort, left.natural.clone(), right.natural.clone());
        let left_connector = left
            .connector
            .as_ref()
            .map(|connector| self.connector_node(connector));
        let right_connector = right
            .connector
            .as_ref()
            .map(|connector| self.connector_node(connector));
        let (left_to_shared, right_to_shared) =
            self.union_to_shared(base, left_connector, right_connector);
        self.emit_pending_group(actions, &left_to_shared);
        self.emit_pending_group(actions, &right_to_shared);

        let max_proof = self.fresh_expr(self.carry_sort.clone());
        let max_left = self.proof_expr(&left_to_shared);
        let max_right = self.proof_expr(&right_to_shared);
        let max_value = self.primitive(
            "proof-of-max",
            vec![left.value.clone(), max_left, right.value.clone(), max_right],
            self.carry_sort.clone(),
        );
        self.emit_action(
            actions,
            GenericAction::Let(
                self.span.clone(),
                Self::expect_variable(&max_proof).clone(),
                max_value,
            ),
        );
        let min_proof = self.fresh_expr(self.carry_sort.clone());
        let min_left = self.proof_expr(&left_to_shared);
        let min_right = self.proof_expr(&right_to_shared);
        let min_value = self.primitive(
            "proof-of-min",
            vec![left.value.clone(), min_left, right.value.clone(), min_right],
            self.carry_sort.clone(),
        );
        self.emit_action(
            actions,
            GenericAction::Let(
                self.span.clone(),
                Self::expect_variable(&min_proof).clone(),
                min_value,
            ),
        );
        let min_name = Self::expect_variable(&min_proof).name.clone();
        let reversed_min = self.sym(min_name);
        let max_name = Self::expect_variable(&max_proof).name.clone();
        let edge = self.trans(max_name, reversed_min);
        self.emit_pending_group(actions, &edge);
        edge
    }

    fn union(
        &mut self,
        actions: &mut Vec<ActionStmt>,
        sort: SortKey,
        left: &Operand,
        right: &Operand,
    ) -> ActionStmt {
        let (larger, smaller) = self.ordered_endpoints(left, right, sort.clone());
        let proof = if self.proofs {
            self.composed_union_edge(actions, &sort, left, right)
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
        actions: &mut Vec<ActionStmt>,
        expr: &ResolvedExpr,
        target: &Operand,
        scope: &Scope,
    ) -> Operand {
        let (function, source_args) = constructor_operand(expr)
            .expect("construct-into guest must be a constructor application");
        let args = source_args
            .iter()
            .map(|arg| self.instrument_expr(arg, actions, scope))
            .collect::<Vec<_>>();
        let child_values = args.iter().map(|arg| arg.value.clone()).collect::<Vec<_>>();
        if !self.proofs {
            let mut row_args = child_values.clone();
            row_args.push(target.value.clone());
            let relation = self.relation_call_key(
                function.name.clone(),
                row_args.iter().map(Self::scalar_expr_sort).collect(),
            );
            self.emit_action(
                actions,
                GenericAction::Set(
                    self.span.clone(),
                    relation,
                    row_args,
                    GenericExpr::Lit(self.span.clone(), Literal::Unit),
                ),
            );
            self.update_view(
                actions,
                function,
                child_values,
                target.value.clone(),
                GenericExpr::Lit(self.span.clone(), Literal::Unit),
            );
            return Operand::plain(target.value.clone());
        }

        let Natural {
            dedup_args,
            natural,
            to_dedup,
        } = self.build_natural_with_congr(actions, function, &args);
        let edge = self.fiat_edge(
            actions,
            &SortKey::from_sort(function.output()),
            target.natural.clone(),
            natural.clone(),
        );
        let target_connector = target
            .connector
            .as_ref()
            .map(|connector| self.connector_node(connector));
        let view_proof = self.guest_view(edge, to_dedup.clone(), target_connector);
        self.emit_pending_group(actions, &view_proof);
        let view_proof_expr = self.proof_expr(&view_proof);
        self.update_view(
            actions,
            function,
            dedup_args,
            target.value.clone(),
            view_proof_expr,
        );
        let connector = Connector::Node(self.level_connector(&to_dedup, &view_proof));
        Operand::built(target.value.clone(), natural, connector)
    }

    fn lower_action(
        &mut self,
        action: &ResolvedAction,
        actions: &mut Vec<ActionStmt>,
        scope: &mut Scope,
    ) {
        match action {
            GenericAction::Let(_, variable, expr) => {
                let operand = self.instrument_expr(expr, actions, scope);
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
                    actions,
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
                    values.push(self.instrument_expr(expr, actions, scope));
                }
                assert_ne!(
                    function.subtype,
                    FunctionSubtype::Constructor,
                    "set on a constructor should have been rejected by typechecking"
                );
                if source_args.is_empty()
                    && self.instrumentor.egraph.type_info.is_global(&function.name)
                {
                    let value = values.pop().expect("set must have an output value");
                    let proof = if self.proofs {
                        let proof = self.global_value_proof(actions, function, &value);
                        self.proof_expr(&proof)
                    } else {
                        GenericExpr::Lit(self.span.clone(), Literal::Unit)
                    };
                    let relation = self.relation_call_key(
                        function.name.clone(),
                        vec![Self::scalar_expr_sort(&value.value)],
                    );
                    self.emit_action(
                        actions,
                        GenericAction::Set(
                            self.span.clone(),
                            relation,
                            vec![value.value.clone()],
                            GenericExpr::Lit(self.span.clone(), Literal::Unit),
                        ),
                    );
                    self.update_view(actions, function, vec![], value.value, proof);
                    return;
                }
                self.add_term_and_view(actions, function, &values);
            }
            GenericAction::Change(span, change, call, source_args) => {
                let ResolvedCall::Func(function) = call else {
                    panic!("change on a primitive should have been rejected by typechecking")
                };
                let args = source_args
                    .iter()
                    .map(|expr| self.instrument_expr(expr, actions, scope).value)
                    .collect::<Vec<_>>();
                match change {
                    Change::Delete => {
                        let key = self.view_call_key(function);
                        self.emit_action(
                            actions,
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
                            actions,
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
                let left = self.instrument_expr(left, actions, scope);
                let right = self.instrument_expr(right, actions, scope);
                let union = self.union(actions, sort, &left, &right);
                self.emit_action(actions, union);
            }
            GenericAction::Panic(span, message) => {
                actions.push(GenericAction::Panic(span.clone(), message.clone()))
            }
            GenericAction::Expr(_, expr) => {
                self.instrument_expr(expr, actions, scope);
            }
        }
    }

    fn lower_actions(&mut self, source: &[ResolvedAction]) -> Vec<ActionStmt> {
        let plan = {
            let symbol_gen = &mut self.instrumentor.egraph.parser.symbol_gen;
            let mut fresh = || symbol_gen.fresh("union_operand");
            crate::proofs::proof_head::HeadPlan::new(source, &mut fresh)
        };
        let mut scope = Scope::default();
        let mut lowered_actions = vec![];
        for (index, action) in plan.actions.iter().enumerate() {
            if plan.dropped.contains(&index) {
                continue;
            }
            match action {
                GenericAction::Let(_, variable, expr)
                    if plan.construct_into.contains_key(&variable.name) =>
                {
                    let target_name = &plan.construct_into[&variable.name];
                    let target = scope.0.get(target_name).cloned().unwrap_or_else(|| {
                        let sort = self
                            .variables
                            .get(&(target_name.clone(), GeneratedVarRole::Local))
                            .cloned()
                            .unwrap_or_else(|| {
                                panic!("construct-into target `{target_name}` has no recorded sort")
                            });
                        let target =
                            self.variable(target_name.clone(), sort, GeneratedVarRole::Local);
                        Operand::plain(GenericExpr::Var(self.span.clone(), target))
                    });
                    let guest =
                        self.instrument_construct_into(&mut lowered_actions, expr, &target, &scope);
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
                        &mut lowered_actions,
                        GenericAction::Let(
                            self.span.clone(),
                            Self::expect_variable(&bound).clone(),
                            guest.value.clone(),
                        ),
                    );
                    scope.bind(&variable.name, &guest, bound);
                }
                _ => self.lower_action(action, &mut lowered_actions, &mut scope),
            }
        }
        lowered_actions
    }
}

impl ProofAlgebra for ActionLowerer<'_, '_> {
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

fn register_expr_signatures(expr: &GeneratedExpr, catalog: &mut GeneratedSignatureCatalog) {
    if let GenericExpr::Call(span, call, args) = expr {
        catalog
            .register_call_key(call, span)
            .expect("standalone-action call signatures must be internally consistent");
        for arg in args {
            register_expr_signatures(arg, catalog);
        }
    }
}

pub(super) fn register_signatures(
    actions: &GeneratedActions,
    catalog: &mut GeneratedSignatureCatalog,
) {
    for action in &actions.0 {
        match action {
            GenericAction::Let(_, _, value) | GenericAction::Expr(_, value) => {
                register_expr_signatures(value, catalog)
            }
            GenericAction::Set(span, call, args, value) => {
                catalog
                    .register_call_key(call, span)
                    .expect("standalone-action set signature must be internally consistent");
                for arg in args {
                    register_expr_signatures(arg, catalog);
                }
                register_expr_signatures(value, catalog);
            }
            GenericAction::Change(span, _, call, args) => {
                catalog
                    .register_call_key(call, span)
                    .expect("standalone-action change signature must be internally consistent");
                for arg in args {
                    register_expr_signatures(arg, catalog);
                }
            }
            GenericAction::Union(_, left, right) => {
                register_expr_signatures(left, catalog);
                register_expr_signatures(right, catalog);
            }
            GenericAction::Panic(..) => {}
        }
    }
}
