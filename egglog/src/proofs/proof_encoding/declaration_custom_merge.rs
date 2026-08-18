//! Typed lowering for the merge attached to a custom function's encoded FD
//! view.  Merge expressions run inside a function declaration, so their proof
//! semantics are deliberately separate from standalone action lowering:
//! subexpressions mint `MergeIdx` rows and the final view row mints `MergeRow`.

use super::{PlannedDeclaration, TypedHoistGroup};
use crate::ast::{
    GenericAction, GenericActions, GenericExpr, Literal, ResolvedExpr, ResolvedFunctionDecl, Span,
};
use crate::core::ResolvedCall;
use crate::proofs::generated_binder::{
    CallKey, FunctionKey, GeneratedAction, GeneratedExpr, GeneratedMerge, GeneratedRuleBuilder,
    GeneratedVar, GeneratedVarRole, PrimitiveKey, SortKey, SortSemanticClass, ValueShape,
};
use crate::proofs::proof_encoding_helpers::{Composition, ProofTree};
use crate::proofs::proof_fresh::{
    GET_FRESH_PRIM_NAME, mint_prim_name, set_if_empty_prim_name, view_proof_prim_name,
};
use crate::proofs::proof_head::ProofAlgebra;
use crate::typechecking::FuncType;
use crate::util::{HashMap, HashSet};
use crate::{FunctionSubtype, literal_sort};

use super::ProofInstrumentor;

#[derive(Clone)]
struct Operand {
    value: GeneratedExpr,
    natural: GeneratedExpr,
    connector: Option<String>,
}

impl Operand {
    fn plain(value: GeneratedExpr) -> Self {
        Self {
            natural: value.clone(),
            value,
            connector: None,
        }
    }

    fn built(value: GeneratedExpr, natural: GeneratedExpr, connector: String) -> Self {
        Self {
            value,
            natural,
            connector: Some(connector),
        }
    }
}

struct Natural {
    dedup_args: Vec<GeneratedExpr>,
    natural: GeneratedExpr,
    to_dedup: String,
}

enum Deferred {
    Composed(Composition),
}

struct CustomMergeLowerer<'lower, 'egraph> {
    instrumentor: &'lower mut ProofInstrumentor<'egraph>,
    span: Span,
    source_name: String,
    proofs: bool,
    carry_sort: SortKey,
    variables: HashMap<(String, GeneratedVarRole), SortKey>,
    builder: GeneratedRuleBuilder,
    reflexive: HashSet<String>,
    deferred: HashMap<String, Deferred>,
    sealed: HashSet<String>,
    pending: Vec<PlannedDeclaration>,
}

/// Build one custom FD view merge and the first-use packed declarations its
/// proof compositions discover.  The caller places `pending` immediately before
/// the view declaration which owns `merge`.
pub(super) fn lower(
    instrumentor: &mut ProofInstrumentor<'_>,
    span: &Span,
    declaration: &ResolvedFunctionDecl,
) -> (TypedHoistGroup, GeneratedMerge) {
    let source_merge = declaration
        .merge
        .as_ref()
        .expect("custom view lowering requires a source merge");
    let proofs = instrumentor.proofs_enabled();
    let carry_sort = if proofs {
        SortKey {
            name: instrumentor.proof_names().proof_datatype.clone(),
            class: SortSemanticClass::Eq,
        }
    } else {
        SortKey {
            name: "Unit".to_owned(),
            class: SortSemanticClass::Value,
        }
    };
    let mut lowerer = CustomMergeLowerer {
        instrumentor,
        span: span.clone(),
        source_name: declaration.name.clone(),
        proofs,
        carry_sort,
        variables: HashMap::default(),
        builder: GeneratedRuleBuilder::default(),
        reflexive: HashSet::default(),
        deferred: HashMap::default(),
        sealed: HashSet::default(),
        pending: vec![],
    };
    let mut actions = vec![];
    let mut index = 0;
    let merged = lowerer
        .instrument(&source_merge.result, &mut index, &mut actions)
        .value;

    // A composition which the merge result never reads has no observable row.
    // Do not let it leak into the whole-row proof or a later declaration.
    lowerer.deferred.clear();
    lowerer.sealed.clear();

    let row_proof = if lowerer.proofs {
        let fresh = lowerer.merge_row_proof(&mut actions);
        let output = scalar_expr_sort(&merged);
        let new_value = lowerer.variable_expr("new0", output.clone());
        let new_proof = lowerer.proof_expr("new1");
        let fresh_proof = lowerer.proof_expr(&fresh);
        let carry_sort = lowerer.carry_sort.clone();
        let inner = lowerer.primitive(
            "select-eq",
            vec![merged.clone(), new_value, new_proof, fresh_proof],
            carry_sort.clone(),
        );
        let old_value = lowerer.variable_expr("old0", output);
        let old_proof = lowerer.proof_expr("old1");
        lowerer.primitive(
            "select-eq",
            vec![merged.clone(), old_value, old_proof, inner],
            carry_sort,
        )
    } else {
        GenericExpr::Lit(span.clone(), Literal::Unit)
    };
    let result = lowerer.values(vec![merged, row_proof]);
    (
        TypedHoistGroup {
            declarations: lowerer.pending,
        },
        crate::ast::GenericMerge {
            actions: GenericActions(actions),
            result,
        },
    )
}

fn scalar_expr_sort(expr: &GeneratedExpr) -> SortKey {
    match expr {
        GenericExpr::Var(_, variable) => variable.sort.clone(),
        GenericExpr::Lit(_, literal) => SortKey::from_sort(&literal_sort(literal)),
        GenericExpr::Call(_, CallKey::Function(function), _) => match &function.output {
            ValueShape::Scalar(sort) => sort.clone(),
            ValueShape::Tuple(_) => panic!("tuple-valued merge expression used as a scalar"),
        },
        GenericExpr::Call(_, CallKey::Primitive(primitive), _) => primitive.output.clone(),
        GenericExpr::Call(_, CallKey::Values(_), _) => {
            panic!("values tuple used as a scalar merge expression")
        }
    }
}

impl CustomMergeLowerer<'_, '_> {
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
                "custom merge variable `{name}` changed portable sort"
            );
        } else {
            self.variables.insert(identity, sort.clone());
        }
        self.builder
            .variable(name, sort, role, &self.span)
            .expect("custom merge variable changed sort while lowering")
    }

    fn variable_expr(&mut self, name: impl Into<String>, sort: SortKey) -> GeneratedExpr {
        GenericExpr::Var(
            self.span.clone(),
            self.variable(name, sort, GeneratedVarRole::Local),
        )
    }

    fn fresh_expr(&mut self, sort: SortKey) -> GeneratedExpr {
        let name = self.instrumentor.fresh_var();
        self.variable_expr(name, sort)
    }

    fn primitive(
        &self,
        name: impl Into<String>,
        args: Vec<GeneratedExpr>,
        output: SortKey,
    ) -> GeneratedExpr {
        let inputs = args.iter().map(scalar_expr_sort).collect();
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

    fn values(&self, values: Vec<GeneratedExpr>) -> GeneratedExpr {
        let sorts = values.iter().map(scalar_expr_sort).collect();
        GenericExpr::Call(self.span.clone(), CallKey::Values(sorts), values)
    }

    fn expect_variable(expr: &GeneratedExpr) -> &GeneratedVar {
        let GenericExpr::Var(_, variable) = expr else {
            panic!("custom merge lowering expected a generated variable")
        };
        variable
    }

    fn proof_expr(&mut self, name: &str) -> GeneratedExpr {
        assert!(
            self.proofs,
            "custom merge requested a proof variable while proofs are disabled"
        );
        self.variable_expr(name.to_owned(), self.carry_sort.clone())
    }

    fn emit_pending_for_expr(&mut self, actions: &mut Vec<GeneratedAction>, expr: &GeneratedExpr) {
        match expr {
            GenericExpr::Var(_, variable) if variable.role == GeneratedVarRole::Local => {
                self.emit_pending_group(actions, &variable.name)
            }
            GenericExpr::Var(..) => {}
            GenericExpr::Call(_, _, args) => {
                for arg in args {
                    self.emit_pending_for_expr(actions, arg);
                }
            }
            GenericExpr::Lit(..) => {}
        }
    }

    fn emit_action(&mut self, actions: &mut Vec<GeneratedAction>, action: GeneratedAction) {
        match &action {
            GenericAction::Let(_, _, value) | GenericAction::Expr(_, value) => {
                self.emit_pending_for_expr(actions, value);
            }
            GenericAction::Set(_, _, args, value) => {
                for arg in args {
                    self.emit_pending_for_expr(actions, arg);
                }
                self.emit_pending_for_expr(actions, value);
            }
            GenericAction::Change(_, _, _, args) => {
                for arg in args {
                    self.emit_pending_for_expr(actions, arg);
                }
            }
            GenericAction::Union(_, left, right) => {
                self.emit_pending_for_expr(actions, left);
                self.emit_pending_for_expr(actions, right);
            }
            GenericAction::Panic(..) => {}
        }
        actions.push(action);
    }

    fn mint_as(
        &mut self,
        actions: &mut Vec<GeneratedAction>,
        target: GeneratedExpr,
        relation: &str,
        args: Vec<GeneratedExpr>,
        output: SortKey,
    ) -> GeneratedExpr {
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
        actions: &mut Vec<GeneratedAction>,
        relation: &str,
        args: Vec<GeneratedExpr>,
        output: SortKey,
    ) -> GeneratedExpr {
        let target = self.fresh_expr(output.clone());
        self.mint_as(actions, target, relation, args, output)
    }

    fn get_fresh(&mut self, actions: &mut Vec<GeneratedAction>, sort: SortKey) -> GeneratedExpr {
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

    /// Read a source global through its encoded zero-input FD view. The term and
    /// proof fallbacks are intentionally unconstrained: a valid program has
    /// already set the global, so they are observed only if the view is empty.
    /// In particular, this must not mint a row in the global's term relation.
    fn lookup_global(
        &mut self,
        actions: &mut Vec<GeneratedAction>,
        name: &str,
        output: SortKey,
    ) -> GeneratedExpr {
        let fallback = self.get_fresh(actions, self.term_sort(name));
        let proof = if self.proofs {
            self.get_fresh(actions, self.carry_sort.clone())
        } else {
            GenericExpr::Lit(self.span.clone(), Literal::Unit)
        };
        let value = self.fresh_expr(output.clone());
        let view = self.instrumentor.view_name(name);
        let read = self.primitive(set_if_empty_prim_name(&view), vec![fallback, proof], output);
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

    fn merge_idx_proof(&mut self, actions: &mut Vec<GeneratedAction>, index: usize) -> String {
        let relation = self
            .instrumentor
            .proof_names()
            .merge_fn_idx_constructor
            .clone();
        let old = self.proof_expr("old1");
        let new = self.proof_expr("new1");
        let carry_sort = self.carry_sort.clone();
        let proof = self.mint(
            actions,
            &relation,
            vec![
                GenericExpr::Lit(self.span.clone(), Literal::String(self.source_name.clone())),
                old,
                new,
                GenericExpr::Lit(
                    self.span.clone(),
                    Literal::Int(i64::try_from(index).expect("merge expression index exceeds i64")),
                ),
            ],
            carry_sort,
        );
        let proof = Self::expect_variable(&proof).name.clone();
        self.reflexive.insert(proof.clone());
        proof
    }

    fn merge_row_proof(&mut self, actions: &mut Vec<GeneratedAction>) -> String {
        let relation = self
            .instrumentor
            .proof_names()
            .merge_fn_row_constructor
            .clone();
        let old = self.proof_expr("old1");
        let new = self.proof_expr("new1");
        let carry_sort = self.carry_sort.clone();
        let proof = self.mint(
            actions,
            &relation,
            vec![
                GenericExpr::Lit(self.span.clone(), Literal::String(self.source_name.clone())),
                old,
                new,
            ],
            carry_sort,
        );
        let proof = Self::expect_variable(&proof).name.clone();
        self.reflexive.insert(proof.clone());
        proof
    }

    fn composition(&self, proof: &str) -> Composition {
        match self.deferred.get(proof) {
            Some(Deferred::Composed(composition)) if !self.sealed.contains(proof) => {
                composition.clone()
            }
            _ => ProofTree::Leaf(proof.to_owned()),
        }
    }

    fn compose(&mut self, composition: Composition) -> String {
        let proof = self.fresh_expr(self.carry_sort.clone());
        let name = Self::expect_variable(&proof).name.clone();
        self.deferred
            .insert(name.clone(), Deferred::Composed(composition));
        name
    }

    fn single_step(&mut self, composition: &Composition) -> Option<(String, Vec<GeneratedExpr>)> {
        Some(match composition {
            ProofTree::Sym(inner) => {
                let relation = self.instrumentor.proof_names().eq_sym_constructor.clone();
                (relation, vec![self.proof_expr(inner.leaf()?)])
            }
            ProofTree::Trans(left, right) => {
                let relation = self.instrumentor.proof_names().eq_trans_constructor.clone();
                (
                    relation,
                    vec![
                        self.proof_expr(left.leaf()?),
                        self.proof_expr(right.leaf()?),
                    ],
                )
            }
            ProofTree::Congr(base, index, child) => {
                let relation = self.instrumentor.proof_names().congr_constructor.clone();
                (
                    relation,
                    vec![
                        self.proof_expr(base.leaf()?),
                        GenericExpr::Lit(self.span.clone(), Literal::Int(*index as i64)),
                        self.proof_expr(child.leaf()?),
                    ],
                )
            }
            ProofTree::Proj(base, index) => {
                let relation = self.instrumentor.proof_names().proj_constructor.clone();
                (
                    relation,
                    vec![
                        self.proof_expr(base.leaf()?),
                        GenericExpr::Lit(self.span.clone(), Literal::Int(*index as i64)),
                    ],
                )
            }
            ProofTree::Leaf(_) => return None,
        })
    }

    fn emit_composition(
        &mut self,
        actions: &mut Vec<GeneratedAction>,
        proof: &str,
        composition: Composition,
    ) {
        let (skeleton, columns) = composition.pack();
        for leaf in &columns {
            self.emit_pending_group(actions, leaf);
        }
        let (relation, args) = if let Some(single) = self.single_step(&composition) {
            single
        } else {
            let (relation, pending) = self
                .instrumentor
                .plan_packed_pending_direct(&self.span, columns.len());
            self.pending.extend(pending.declarations);
            let mut args = vec![GenericExpr::Lit(
                self.span.clone(),
                Literal::String(skeleton.spelling()),
            )];
            args.extend(columns.iter().map(|column| self.proof_expr(column)));
            (relation, args)
        };
        let target = self.variable_expr(proof.to_owned(), self.carry_sort.clone());
        let carry_sort = self.carry_sort.clone();
        self.mint_as(actions, target, &relation, args, carry_sort);
    }

    fn emit_pending_group(&mut self, actions: &mut Vec<GeneratedAction>, proof: &str) {
        if let Some(Deferred::Composed(composition)) = self.deferred.remove(proof) {
            self.emit_composition(actions, proof, composition);
        }
    }

    fn level_connector(&mut self, chain: &str, dedup: &str) -> String {
        let composed = matches!(self.deferred.get(chain), Some(Deferred::Composed(_)));
        let connector = self.connect(chain.to_owned(), dedup.to_owned());
        if composed {
            self.sealed.insert(connector.clone());
        }
        connector
    }

    fn term_sort(&self, function: &str) -> SortKey {
        SortKey {
            name: self
                .instrumentor
                .proof_names()
                .fn_to_term_sort
                .get(function)
                .unwrap_or_else(|| panic!("term sort for `{function}` was not planned"))
                .clone(),
            class: SortSemanticClass::Eq,
        }
    }

    fn view_call_key(&mut self, function: &FuncType) -> CallKey {
        CallKey::Function(FunctionKey {
            name: self.instrumentor.view_name(&function.name),
            subtype: FunctionSubtype::Custom,
            inputs: function.input.iter().map(SortKey::from_sort).collect(),
            output: ValueShape::Tuple(vec![
                SortKey::from_sort(function.output()),
                self.carry_sort.clone(),
            ]),
        })
    }

    fn term_mint(
        &mut self,
        actions: &mut Vec<GeneratedAction>,
        function: &FuncType,
        args: Vec<GeneratedExpr>,
    ) -> GeneratedExpr {
        let sort = self.term_sort(&function.name);
        self.mint(actions, &function.name, args, sort)
    }

    fn update_view(
        &mut self,
        actions: &mut Vec<GeneratedAction>,
        function: &FuncType,
        children: Vec<GeneratedExpr>,
        value: GeneratedExpr,
        proof: GeneratedExpr,
    ) {
        let view = self.view_call_key(function);
        let row = self.values(vec![value, proof]);
        self.emit_action(
            actions,
            GenericAction::Set(self.span.clone(), view, children, row),
        );
    }

    fn set_if_empty(
        &mut self,
        function: &FuncType,
        mut children: Vec<GeneratedExpr>,
        fallback: GeneratedExpr,
        proof: GeneratedExpr,
    ) -> GeneratedExpr {
        let view = self.instrumentor.view_name(&function.name);
        children.extend([fallback, proof]);
        self.primitive(
            set_if_empty_prim_name(&view),
            children,
            SortKey::from_sort(function.output()),
        )
    }

    fn read_view_proof(
        &mut self,
        function: &FuncType,
        mut children: Vec<GeneratedExpr>,
        fallback: GeneratedExpr,
    ) -> GeneratedExpr {
        let view = self.instrumentor.view_name(&function.name);
        children.push(fallback);
        self.primitive(
            view_proof_prim_name(&view),
            children,
            self.carry_sort.clone(),
        )
    }

    fn add_custom_row(
        &mut self,
        actions: &mut Vec<GeneratedAction>,
        function: &FuncType,
        args: Vec<GeneratedExpr>,
        index: usize,
    ) -> GeneratedExpr {
        let term = self.term_mint(actions, function, args.clone());
        let proof = if self.proofs {
            let proof = self.merge_idx_proof(actions, index);
            self.proof_expr(&proof)
        } else {
            GenericExpr::Lit(self.span.clone(), Literal::Unit)
        };
        let (output, children) = args
            .split_last()
            .expect("custom merge function row must include its output");
        self.update_view(actions, function, children.to_vec(), output.clone(), proof);
        term
    }

    fn add_constructor_term_only(
        &mut self,
        actions: &mut Vec<GeneratedAction>,
        function: &FuncType,
        args: Vec<GeneratedExpr>,
    ) -> GeneratedExpr {
        let term = self.term_mint(actions, function, args.clone());
        let canonical = self.fresh_expr(SortKey::from_sort(function.output()));
        let value = self.set_if_empty(
            function,
            args,
            term,
            GenericExpr::Lit(self.span.clone(), Literal::Unit),
        );
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
        actions: &mut Vec<GeneratedAction>,
        function: &FuncType,
        args: &[Operand],
        index: usize,
    ) -> Natural {
        let natural_args = args.iter().map(|arg| arg.natural.clone()).collect();
        let dedup_args = args.iter().map(|arg| arg.value.clone()).collect();
        let natural = self.term_mint(actions, function, natural_args);
        let own = self.merge_idx_proof(actions, index);
        let steps = args
            .iter()
            .enumerate()
            .filter_map(|(child, arg)| arg.connector.clone().map(|proof| (child, proof)))
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
        actions: &mut Vec<GeneratedAction>,
        function: &FuncType,
        args: &[Operand],
        index: usize,
    ) -> Operand {
        let Natural {
            dedup_args,
            natural,
            to_dedup,
        } = self.build_natural_with_congr(actions, function, args, index);
        let canonical_term = self.term_mint(actions, function, dedup_args.clone());
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
        let connector = self.level_connector(&to_dedup, &Self::expect_variable(&view_proof).name);
        Operand::built(canonical, natural, connector)
    }

    fn add_term_and_view(
        &mut self,
        actions: &mut Vec<GeneratedAction>,
        function: &FuncType,
        args: &[Operand],
        index: usize,
    ) -> Operand {
        if function.subtype != FunctionSubtype::Constructor {
            Operand::plain(self.add_custom_row(
                actions,
                function,
                args.iter().map(|arg| arg.value.clone()).collect(),
                index,
            ))
        } else if self.proofs {
            self.add_constructor_with_proof(actions, function, args, index)
        } else {
            Operand::plain(self.add_constructor_term_only(
                actions,
                function,
                args.iter().map(|arg| arg.value.clone()).collect(),
            ))
        }
    }

    fn instrument(
        &mut self,
        expr: &ResolvedExpr,
        next_index: &mut usize,
        actions: &mut Vec<GeneratedAction>,
    ) -> Operand {
        let index = *next_index;
        *next_index = (*next_index)
            .checked_add(1)
            .expect("custom merge expression index overflow");
        match expr {
            GenericExpr::Lit(span, literal) => {
                Operand::plain(GenericExpr::Lit(span.clone(), literal.clone()))
            }
            GenericExpr::Var(span, variable) => {
                let sort = SortKey::from_sort(&variable.sort);
                if variable.is_global_ref {
                    Operand::plain(self.lookup_global(actions, &variable.name, sort))
                } else {
                    let name = match variable.name.as_str() {
                        "old" => "old0",
                        "new" => "new0",
                        other => other,
                    };
                    let variable = self.variable(name.to_owned(), sort, GeneratedVarRole::Local);
                    Operand::plain(GenericExpr::Var(span.clone(), variable))
                }
            }
            GenericExpr::Call(_, ResolvedCall::Func(function), args)
                if args.is_empty()
                    && (self.instrumentor.egraph.type_info.is_global(&function.name)
                        || self
                            .instrumentor
                            .egraph
                            .proof_state
                            .original_typechecking
                            .as_ref()
                            .is_some_and(|source| source.type_info.is_global(&function.name))) =>
            {
                Operand::plain(self.lookup_global(
                    actions,
                    &function.name,
                    SortKey::from_sort(function.output()),
                ))
            }
            GenericExpr::Call(_, ResolvedCall::Func(function), args) => {
                let args = args
                    .iter()
                    .map(|arg| self.instrument(arg, next_index, actions))
                    .collect::<Vec<_>>();
                self.add_term_and_view(actions, function, &args, index)
            }
            GenericExpr::Call(_, call @ ResolvedCall::Primitive(primitive), args) => {
                let args = args
                    .iter()
                    .map(|arg| self.instrument(arg, next_index, actions).value)
                    .collect::<Vec<_>>();
                let value = self.fresh_expr(SortKey::from_sort(primitive.output()));
                let computed =
                    GenericExpr::Call(self.span.clone(), CallKey::from_resolved(call), args);
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
            GenericExpr::Call(_, ResolvedCall::Values(_), _) => {
                panic!("tuple-output (`values`) calls are unsupported in proof-mode merges")
            }
        }
    }
}

impl ProofAlgebra for CustomMergeLowerer<'_, '_> {
    type Proof = String;

    fn sym(&mut self, proof: String) -> String {
        if self.reflexive.contains(&proof) {
            return proof;
        }
        let composition = self.composition(&proof);
        self.compose(composition.sym())
    }

    fn trans(&mut self, left: String, right: String) -> String {
        if self.reflexive.contains(&left) {
            return right;
        }
        if self.reflexive.contains(&right) {
            return left;
        }
        let (left, right) = (self.composition(&left), self.composition(&right));
        self.compose(left.trans(right))
    }

    fn congr(&mut self, base: String, child: usize, step: String) -> String {
        if self.reflexive.contains(&step) {
            return base;
        }
        let (base, step) = (self.composition(&base), self.composition(&step));
        self.compose(base.congr(child, step))
    }
}
