//! Typed declaration planning for the generated term/proof encoding.
//!
//! This module owns the declaration-side invariants: lexical command order,
//! declaration metadata, portable presort payloads, name/state side effects,
//! and the exact grouping of declarations hoisted ahead of their first user.
//!
//! The parent module still owns the semantic lowering which *uses* these
//! declarations. Keeping the plan inspectable until the final
//! [`GeneratedCommand`] conversion gives emission a structural boundary which
//! contains no parser tokens or checker-universe handles.

use crate::ast::{
    ContainerRebuildSpec, Expr, FunctionSubtype, GenericAction, GenericActions, GenericExpr,
    GenericFunctionDecl, GenericMerge, GenericRule, Literal, ProofConstructorNames,
    ResolvedFunctionDecl, ResolvedNCommand, RuleEvalMode, Schema, Span,
};
use crate::core::ResolvedCall;
use crate::proofs::generated_binder::{
    CallKey, FunctionKey, GeneratedCommand, GeneratedExpr, GeneratedFunctionDecl,
    GeneratedIndexDecl, GeneratedMerge, GeneratedPresort, GeneratedPresortArg, GeneratedRule,
    GeneratedRuleBuilder, GeneratedSignatureCatalog, GeneratedSortDecl, GeneratedVarRole,
    PrimitiveKey, SortKey, SortSemanticClass, ValueShape,
};
use crate::proofs::proof_encoding_helpers::{Skeleton, recomputable_premises};
use crate::typechecking::FuncType;
use crate::util::{FreshGen, HashMap};

use super::{ProofInstrumentor, ViewIndex};

#[path = "declaration_custom_merge.rs"]
mod custom_merge_direct;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct PlannedSortDeclaration {
    pub(super) span: Span,
    pub(super) key: SortKey,
    pub(super) presort: Option<GeneratedPresort>,
    pub(super) uf: Option<(String, Option<String>)>,
    pub(super) container_rebuild: Option<ContainerRebuildSpec>,
    pub(super) proof_constructors: Option<ProofConstructorNames>,
    pub(super) unionable: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct PlannedIndexDeclaration {
    pub(super) span: Span,
    pub(super) name: String,
    pub(super) function: FunctionKey,
    pub(super) any_of: Vec<usize>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum PlannedDeclarationKind {
    Sort(PlannedSortDeclaration),
    Function(GeneratedFunctionDecl),
    Index(PlannedIndexDeclaration),
    Ruleset(Span, String),
    Rule(GeneratedRule),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct PlannedDeclaration {
    pub(super) kind: PlannedDeclarationKind,
    /// Applied to persistent encoding state only after this exact declaration
    /// has committed to TypeInfo.  Keeping it on the entry prevents integration
    /// from re-inferring a role transition from a generated spelling.
    pub(super) layout_commit: Option<EncodedFunctionLayoutCommit>,
}

impl PlannedDeclaration {
    /// Cross the sole planning-to-binding boundary.
    pub(super) fn into_entry(self) -> TypedDeclarationEntry {
        let PlannedDeclaration {
            kind,
            layout_commit,
        } = self;
        let command = match kind {
            PlannedDeclarationKind::Sort(decl) => GeneratedCommand::Sort(GeneratedSortDecl {
                span: decl.span,
                key: decl.key,
                presort: decl.presort,
                uf: decl.uf,
                container_rebuild: decl.container_rebuild,
                proof_constructors: decl.proof_constructors,
                unionable: decl.unionable,
            }),
            PlannedDeclarationKind::Function(decl) => GeneratedCommand::Function(decl),
            PlannedDeclarationKind::Index(decl) => GeneratedCommand::Index(GeneratedIndexDecl {
                span: decl.span,
                name: decl.name,
                function: decl.function,
                any_of: decl.any_of,
            }),
            PlannedDeclarationKind::Ruleset(span, name) => GeneratedCommand::AddRuleset(span, name),
            PlannedDeclarationKind::Rule(rule) => GeneratedCommand::Rule(rule),
        };
        TypedDeclarationEntry {
            command,
            layout_commit,
        }
    }
}

/// One direct command paired with the state delta whose commit point is that
/// command's successful declaration registration.
#[derive(Clone, Debug)]
pub(in crate::proofs) struct TypedDeclarationEntry {
    pub(in crate::proofs) command: GeneratedCommand,
    pub(in crate::proofs) layout_commit: Option<EncodedFunctionLayoutCommit>,
}

/// One indivisible lexical run which must be inserted at a single hoist point.
/// In particular, a subsumption marker and its rules may not be split, and a
/// packed declaration stays adjacent to the first rule or merge which uses it.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(in crate::proofs) struct TypedHoistGroup {
    pub(super) declarations: Vec<PlannedDeclaration>,
}

impl TypedHoistGroup {
    /// Register the complete portable signature envelope in the same lexical
    /// order in which the declarations will bind.  Pending-only planners leave
    /// this step to their insertion boundary so lowering can discover hoists
    /// without borrowing the batch catalog.  A consumer must register each
    /// returned group exactly once before appending it: function declarations
    /// own the calls in their merge bodies, rules own every body/head call, and
    /// an index is not accepted until its exact target declaration is present.
    pub(super) fn register_signatures(&self, catalog: &mut GeneratedSignatureCatalog) {
        fn register_expr(expr: &GeneratedExpr, catalog: &mut GeneratedSignatureCatalog) {
            if let GenericExpr::Call(span, call, args) = expr {
                catalog
                    .register_call_key(call, span)
                    .expect("declaration expression signatures must be internally consistent");
                for arg in args {
                    register_expr(arg, catalog);
                }
            }
        }

        fn register_action(
            action: &crate::proofs::generated_binder::GeneratedAction,
            catalog: &mut GeneratedSignatureCatalog,
        ) {
            match action {
                GenericAction::Let(_, _, value) | GenericAction::Expr(_, value) => {
                    register_expr(value, catalog);
                }
                GenericAction::Set(span, call, args, value) => {
                    catalog
                        .register_call_key(call, span)
                        .expect("declaration set signature must be internally consistent");
                    for arg in args {
                        register_expr(arg, catalog);
                    }
                    register_expr(value, catalog);
                }
                GenericAction::Change(span, _, call, args) => {
                    catalog
                        .register_call_key(call, span)
                        .expect("declaration change signature must be internally consistent");
                    for arg in args {
                        register_expr(arg, catalog);
                    }
                }
                GenericAction::Union(_, left, right) => {
                    register_expr(left, catalog);
                    register_expr(right, catalog);
                }
                GenericAction::Panic(..) => {}
            }
        }

        fn register_fact(
            fact: &crate::proofs::generated_binder::GeneratedFact,
            catalog: &mut GeneratedSignatureCatalog,
        ) {
            match fact {
                crate::ast::GenericFact::Fact(expr) => register_expr(expr, catalog),
                crate::ast::GenericFact::Eq(_, left, right) => {
                    register_expr(left, catalog);
                    register_expr(right, catalog);
                }
            }
        }

        for declaration in &self.declarations {
            match &declaration.kind {
                PlannedDeclarationKind::Sort(decl) => {
                    catalog
                        .register_sort(decl.key.clone(), &decl.span)
                        .expect("planned sort signature must be internally consistent");
                }
                PlannedDeclarationKind::Function(decl) => {
                    catalog
                        .register_call_key(&decl.resolved_schema, &decl.span)
                        .expect("planned function signature must be internally consistent");
                    if let Some(merge) = &decl.merge {
                        for action in &merge.actions.0 {
                            register_action(action, catalog);
                        }
                        register_expr(&merge.result, catalog);
                    }
                }
                PlannedDeclarationKind::Index(decl) => {
                    catalog
                        .register_index(decl.name.clone(), &decl.function, &decl.any_of, &decl.span)
                        .expect("planned index signature must be internally consistent");
                }
                PlannedDeclarationKind::Ruleset(..) => {}
                PlannedDeclarationKind::Rule(rule) => {
                    for fact in &rule.body {
                        register_fact(fact, catalog);
                    }
                    for action in &rule.head.0 {
                        register_action(action, catalog);
                    }
                }
            }
        }
    }
}

/// Portable roles of one source function after the encoding replaces it with
/// a term-node relation and an FD view.  Wrappers use these exact keys rather
/// than re-deriving names or resolving checker-universe `FuncType`s.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::proofs) struct EncodedFunctionLayout {
    pub(in crate::proofs) source_name: String,
    pub(in crate::proofs) source_subtype: FunctionSubtype,
    pub(in crate::proofs) term: FunctionKey,
    pub(in crate::proofs) view: FunctionKey,
    pub(in crate::proofs) term_eclass_sort: SortKey,
    pub(in crate::proofs) output_is_eclass: bool,
    pub(super) indexes: Vec<PlannedIndexDeclaration>,
}

/// Name-to-role catalog shared by declaration planning and name-only wrapper
/// lowering.  Insertion rejects two different layouts for one source spelling;
/// silently replacing one would let `PrintSize` and `ProveExists` target
/// different tables depending on which producer happened to run last.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(in crate::proofs) struct EncodedFunctionCatalog {
    pub(in crate::proofs) by_source: HashMap<String, EncodedFunctionLayout>,
}

impl EncodedFunctionCatalog {
    /// Publish a role only at the declaration's successful TypeInfo commit.
    pub(in crate::proofs) fn commit(&mut self, receipt: EncodedFunctionLayoutCommit) {
        let layout = receipt.layout;
        if let Some(existing) = self.by_source.get(&layout.source_name) {
            assert_eq!(
                existing, &layout,
                "one source function acquired two encoded declaration layouts"
            );
        } else {
            self.by_source.insert(layout.source_name.clone(), layout);
        }
    }
}

/// Batch-local lexical declarations which have been planned but have not yet
/// committed. Persistent roles remain in [`super::EncodingState`] and are consulted
/// as a fallback rather than cloned into every source command's instrumentor.
/// This keeps command-by-command declaration planning linear while retaining
/// exact same-batch visibility and per-entry commit semantics.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(super) struct EncodedFunctionPlanningOverlay {
    pub(super) staged: EncodedFunctionCatalog,
}

impl EncodedFunctionPlanningOverlay {
    pub(super) fn stage(
        &mut self,
        persistent: &EncodedFunctionCatalog,
        layout: EncodedFunctionLayout,
    ) -> EncodedFunctionLayoutCommit {
        if let Some(existing) = persistent.by_source.get(&layout.source_name) {
            assert_eq!(
                existing, &layout,
                "planned declaration conflicts with its committed encoded layout"
            );
        }
        let receipt = EncodedFunctionLayoutCommit { layout };
        self.staged.commit(receipt.clone());
        receipt
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::proofs) struct EncodedFunctionLayoutCommit {
    pub(in crate::proofs) layout: EncodedFunctionLayout,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct FunctionDeclarationMetadata {
    pub(super) cost: Option<u64>,
    pub(super) unextractable: bool,
    pub(super) internal_hidden: bool,
    pub(super) internal_let: bool,
    pub(super) term_constructor: Option<String>,
    pub(super) identity_vals: Option<usize>,
    pub(super) internal_term_node: bool,
}

/// Construct a declaration from one exact portable signature.  This is the
/// single place which must keep the unresolved schema and resolved key in
/// lockstep; the binder intentionally treats a mismatch as malformed IR.
fn function_declaration(
    span: Span,
    key: FunctionKey,
    merge: Option<GeneratedMerge>,
    metadata: FunctionDeclarationMetadata,
) -> GeneratedFunctionDecl {
    let outputs = match &key.output {
        ValueShape::Scalar(sort) => vec![sort.name.clone()],
        ValueShape::Tuple(sorts) => sorts.iter().map(|sort| sort.name.clone()).collect(),
    };
    GenericFunctionDecl {
        name: key.name.clone(),
        subtype: key.subtype,
        schema: Schema::new_tuple(
            key.inputs.iter().map(|sort| sort.name.clone()).collect(),
            outputs,
        ),
        resolved_schema: CallKey::Function(key),
        merge,
        cost: metadata.cost,
        unextractable: metadata.unextractable,
        internal_hidden: metadata.internal_hidden,
        internal_let: metadata.internal_let,
        span,
        term_constructor: metadata.term_constructor,
        identity_vals: metadata.identity_vals,
        internal_term_node: metadata.internal_term_node,
    }
}

fn proof_relation(span: &Span, name: String, inputs: Vec<SortKey>) -> PlannedDeclaration {
    let unit = SortKey {
        name: "Unit".to_owned(),
        class: SortSemanticClass::Value,
    };
    let key = FunctionKey {
        name,
        subtype: FunctionSubtype::Custom,
        inputs,
        output: ValueShape::Scalar(unit),
    };
    PlannedDeclaration {
        kind: PlannedDeclarationKind::Function(function_declaration(
            span.clone(),
            key,
            None,
            FunctionDeclarationMetadata {
                cost: None,
                // The generated source used `function` rather than
                // `constructor`; desugaring makes an ordinary function
                // unextractable unless it is an FD view carrying
                // `term_constructor` metadata.
                unextractable: true,
                internal_hidden: true,
                internal_let: false,
                term_constructor: None,
                identity_vals: None,
                internal_term_node: true,
            },
        )),
        layout_commit: None,
    }
}

impl ProofInstrumentor<'_> {
    pub(super) fn plan_term_header_direct(
        &self,
        catalog: &mut GeneratedSignatureCatalog,
        span: &Span,
    ) -> TypedHoistGroup {
        let names = self.proof_names();
        let group = TypedHoistGroup {
            declarations: [
                &names.path_compress_ruleset_name,
                &names.rebuilding_ruleset_name,
                &names.rebuilding_cleanup_ruleset_name,
                &names.subsume_ruleset_name,
            ]
            .into_iter()
            .map(|name| PlannedDeclaration {
                kind: PlannedDeclarationKind::Ruleset(span.clone(), name.clone()),
                layout_commit: None,
            })
            .collect(),
        };
        group.register_signatures(catalog);
        group
    }

    pub(super) fn plan_proof_header_direct(
        &self,
        catalog: &mut GeneratedSignatureCatalog,
        span: &Span,
    ) -> TypedHoistGroup {
        let names = self.proof_names();
        let proof = SortKey {
            name: names.proof_datatype.clone(),
            class: SortSemanticClass::Eq,
        };
        let string = SortKey {
            name: "String".to_owned(),
            class: SortSemanticClass::Value,
        };
        let i64_sort = SortKey {
            name: "i64".to_owned(),
            class: SortSemanticClass::Value,
        };
        let mut declarations = vec![PlannedDeclaration {
            kind: PlannedDeclarationKind::Sort(PlannedSortDeclaration {
                span: span.clone(),
                key: proof.clone(),
                presort: None,
                uf: None,
                container_rebuild: None,
                proof_constructors: Some(ProofConstructorNames {
                    congr: names.congr_constructor.clone(),
                    congr_all: names.congr_all_constructor.clone(),
                    trans: names.eq_trans_constructor.clone(),
                    sym: names.eq_sym_constructor.clone(),
                    normalize: names.container_normalize_constructor.clone(),
                    fiat: names.fiat_prefix.clone(),
                    proj: names.proj_constructor.clone(),
                    proj_all: names.proj_all_prefix.clone(),
                }),
                unionable: true,
            }),
            layout_commit: None,
        }];
        declarations.extend([
            proof_relation(
                span,
                names.rule_link_constructor.clone(),
                vec![
                    proof.clone(),
                    proof.clone(),
                    i64_sort.clone(),
                    proof.clone(),
                ],
            ),
            proof_relation(
                span,
                names.merge_fn_idx_constructor.clone(),
                vec![
                    string.clone(),
                    proof.clone(),
                    proof.clone(),
                    i64_sort.clone(),
                    proof.clone(),
                ],
            ),
            proof_relation(
                span,
                names.merge_fn_row_constructor.clone(),
                vec![string, proof.clone(), proof.clone(), proof.clone()],
            ),
            proof_relation(
                span,
                names.eq_trans_constructor.clone(),
                vec![proof.clone(), proof.clone(), proof.clone()],
            ),
            proof_relation(
                span,
                names.eq_sym_constructor.clone(),
                vec![proof.clone(), proof.clone()],
            ),
            proof_relation(
                span,
                names.congr_constructor.clone(),
                vec![
                    proof.clone(),
                    i64_sort.clone(),
                    proof.clone(),
                    proof.clone(),
                ],
            ),
            proof_relation(
                span,
                names.congr_all_constructor.clone(),
                vec![proof.clone(), proof.clone(), proof.clone()],
            ),
            proof_relation(
                span,
                names.proj_constructor.clone(),
                vec![proof.clone(), i64_sort, proof.clone()],
            ),
            proof_relation(
                span,
                names.container_normalize_constructor.clone(),
                vec![proof.clone(), proof.clone()],
            ),
            proof_relation(span, names.eval_constructor.clone(), vec![proof.clone()]),
        ]);
        let group = TypedHoistGroup { declarations };
        group.register_signatures(catalog);
        group
    }

    /// Sort and deduplicate arities into one declaration per arity. The
    /// declaration span is the first source rule which required that arity;
    /// nested `fail` commands participate in the same global header.
    pub(super) fn plan_rule_arity_header_direct(
        &mut self,
        catalog: &mut GeneratedSignatureCatalog,
        program: &[ResolvedNCommand],
    ) -> TypedHoistGroup {
        fn collect(commands: &[ResolvedNCommand], out: &mut Vec<(usize, Span)>) {
            for command in commands {
                match command {
                    ResolvedNCommand::NormRule { rule } => out.push((
                        recomputable_premises(&rule.body, &|_| false)
                            .iter()
                            .filter(|recomputable| !**recomputable)
                            .count(),
                        rule.span.clone(),
                    )),
                    ResolvedNCommand::Fail(_, nested) => collect(nested, out),
                    _ => {}
                }
            }
        }

        let mut arities = vec![];
        collect(program, &mut arities);
        arities.sort_by_key(|(arity, _)| *arity);
        arities.dedup_by_key(|(arity, _)| *arity);

        let proof = SortKey {
            name: self.proof_names().proof_datatype.clone(),
            class: SortSemanticClass::Eq,
        };
        let string = SortKey {
            name: "String".to_owned(),
            class: SortSemanticClass::Value,
        };
        let i64_sort = SortKey {
            name: "i64".to_owned(),
            class: SortSemanticClass::Value,
        };
        let mut declarations = vec![];
        for (arity, span) in arities {
            if !self
                .egraph
                .proof_state
                .proof_names
                .rule_fused_declared
                .insert(arity)
            {
                continue;
            }
            let mut inputs = vec![string.clone()];
            inputs.extend(std::iter::repeat_n(proof.clone(), arity));
            inputs.extend([i64_sort.clone(), proof.clone()]);
            declarations.push(proof_relation(
                &span,
                self.proof_names().fused_rule(arity),
                inputs,
            ));
        }
        let group = TypedHoistGroup { declarations };
        group.register_signatures(catalog);
        group
    }

    /// Claim the one-shot Fiat relation and return its unregistered lexical
    /// hoist.  The command producer registers the group after its instrumentor
    /// borrow ends and immediately before inserting the hoist.
    pub(super) fn plan_fiat_pending_direct(
        &mut self,
        span: &Span,
        sort: SortKey,
    ) -> (String, TypedHoistGroup) {
        let name = self.proof_names().fiat(&sort.name);
        let inserted = self
            .egraph
            .proof_state
            .proof_names
            .fiat_declared
            .insert(sort.name.clone());
        let declarations = inserted
            .then(|| {
                let proof = SortKey {
                    name: self.proof_names().proof_datatype.clone(),
                    class: SortSemanticClass::Eq,
                };
                proof_relation(span, name.clone(), vec![sort.clone(), sort, proof])
            })
            .into_iter()
            .collect();
        (name, TypedHoistGroup { declarations })
    }

    /// Return the unregistered first-use element-projection hoist.
    pub(super) fn plan_projection_pending_direct(
        &mut self,
        span: &Span,
        sort: SortKey,
    ) -> (String, TypedHoistGroup) {
        let name = self.proof_names().proj_all(&sort.name);
        let inserted = self
            .egraph
            .proof_state
            .proof_names
            .proj_all_declared
            .insert(sort.name.clone());
        let declarations = inserted
            .then(|| {
                let proof = SortKey {
                    name: self.proof_names().proof_datatype.clone(),
                    class: SortSemanticClass::Eq,
                };
                proof_relation(span, name.clone(), vec![proof.clone(), sort, proof])
            })
            .into_iter()
            .collect();
        (name, TypedHoistGroup { declarations })
    }

    /// Return the unregistered first-use packed-composition hoist.
    pub(in crate::proofs) fn plan_packed_pending_direct(
        &mut self,
        span: &Span,
        columns: usize,
    ) -> (String, TypedHoistGroup) {
        let name = self.proof_names().packed_proof(columns);
        let inserted = self
            .egraph
            .proof_state
            .proof_names
            .packed_declared
            .insert(columns);
        let declarations = inserted
            .then(|| {
                let proof = SortKey {
                    name: self.proof_names().proof_datatype.clone(),
                    class: SortSemanticClass::Eq,
                };
                let string = SortKey {
                    name: "String".to_owned(),
                    class: SortSemanticClass::Value,
                };
                let mut inputs = vec![string];
                inputs.extend(std::iter::repeat_n(proof.clone(), columns));
                inputs.push(proof);
                proof_relation(span, name.clone(), inputs)
            })
            .into_iter()
            .collect();
        (name, TypedHoistGroup { declarations })
    }

    /// Translate the only presort syntax admitted by the proof-support gate to
    /// stable sort keys.  A call-shaped argument is structural list syntax
    /// (used by `UnstableFn`), never an executable unresolved expression.
    fn portable_presort(&self, presort: &str, args: &[Expr], span: &Span) -> GeneratedPresort {
        let source_types = self
            .egraph
            .proof_state
            .original_typechecking
            .as_deref()
            .unwrap_or(self.egraph);
        let sort_key = |name: &str| {
            let sort = source_types
                .type_info
                .get_sort_by_name(name)
                .unwrap_or_else(|| {
                    panic!(
                        "resolved presort `{presort}` retained unknown sort argument `{name}` at {span}"
                    )
                });
            SortKey::from_sort(sort)
        };
        let args = args
            .iter()
            .map(|arg| match arg {
                GenericExpr::Var(_, name) => GeneratedPresortArg::Sort(sort_key(name)),
                GenericExpr::Lit(_, Literal::Unit) => GeneratedPresortArg::SortList(Vec::new()),
                GenericExpr::Call(_, first, rest) => {
                    let mut sorts = vec![sort_key(first)];
                    sorts.extend(rest.iter().map(|arg| match arg {
                        GenericExpr::Var(_, name) => sort_key(name),
                        _ => panic!(
                            "resolved presort `{presort}` retained a non-sort list member at {span}"
                        ),
                    }));
                    GeneratedPresortArg::SortList(sorts)
                }
                _ => panic!(
                    "resolved presort `{presort}` retained a non-portable argument at {span}"
                ),
            })
            .collect();
        GeneratedPresort {
            name: presort.to_owned(),
            args,
        }
    }

    /// Build the tuple-valued merge shared by an equality sort's UF relation
    /// and an e-class-valued FD view.  The returned declaration group contains
    /// the first-use `Packed_2` relation, if any, and must be emitted directly
    /// before the function owning `merge`.
    fn plan_ordered_union_merge_direct(
        &mut self,
        span: &Span,
        value_sort: SortKey,
        uf: FunctionKey,
        composition: Skeleton,
    ) -> (TypedHoistGroup, GeneratedMerge) {
        let carried_sort = if self.proofs_enabled() {
            SortKey {
                name: self.proof_names().proof_datatype.clone(),
                class: SortSemanticClass::Eq,
            }
        } else {
            SortKey {
                name: "Unit".to_owned(),
                class: SortSemanticClass::Value,
            }
        };
        let ordering_max = CallKey::Primitive(PrimitiveKey {
            name: "ordering-max".to_owned(),
            inputs: vec![value_sort.clone(), value_sort.clone()],
            output: value_sort.clone(),
        });
        let ordering_min = CallKey::Primitive(PrimitiveKey {
            name: "ordering-min".to_owned(),
            inputs: vec![value_sort.clone(), value_sort.clone()],
            output: value_sort.clone(),
        });
        let values = CallKey::Values(vec![value_sort.clone(), carried_sort.clone()]);

        let var = |variable| GenericExpr::Var(span.clone(), variable);
        let mut actions = vec![];
        let (pending, old0, new0, displaced, retained) = if self.proofs_enabled() {
            // `proof-of-max` observes old0, old1, new0, new1 in that order.
            // Preserve those local IDs even though `ordering-max` appears
            // later in the action sequence.
            let mut locals = GeneratedRuleBuilder::default();
            let old0 = locals
                .variable("old0", value_sort.clone(), GeneratedVarRole::Local, span)
                .expect("old0 merge variable must keep the value sort");
            let old1 = locals
                .variable("old1", carried_sort.clone(), GeneratedVarRole::Local, span)
                .expect("old1 merge variable must keep the proof sort");
            let new0 = locals
                .variable("new0", value_sort.clone(), GeneratedVarRole::Local, span)
                .expect("new0 merge variable must keep the value sort");
            let new1 = locals
                .variable("new1", carried_sort.clone(), GeneratedVarRole::Local, span)
                .expect("new1 merge variable must keep the proof sort");
            let proof_selector = |name: &str| {
                CallKey::Primitive(PrimitiveKey {
                    name: name.to_owned(),
                    inputs: vec![
                        value_sort.clone(),
                        carried_sort.clone(),
                        value_sort.clone(),
                        carried_sort.clone(),
                    ],
                    output: carried_sort.clone(),
                })
            };
            let selector_args = vec![var(old0.clone()), var(old1), var(new0.clone()), var(new1)];
            let hi = locals
                .variable(
                    "hi_pf_",
                    carried_sort.clone(),
                    GeneratedVarRole::Local,
                    span,
                )
                .expect("selected displaced proof must keep the proof sort");
            actions.push(GenericAction::Let(
                span.clone(),
                hi.clone(),
                GenericExpr::Call(
                    span.clone(),
                    proof_selector("proof-of-max"),
                    selector_args.clone(),
                ),
            ));
            let lo = locals
                .variable(
                    "lo_pf_",
                    carried_sort.clone(),
                    GeneratedVarRole::Local,
                    span,
                )
                .expect("selected retained proof must keep the proof sort");
            actions.push(GenericAction::Let(
                span.clone(),
                lo.clone(),
                GenericExpr::Call(span.clone(), proof_selector("proof-of-min"), selector_args),
            ));
            let (packed, pending) = self.plan_packed_pending_direct(span, composition.width());
            let displaced_name = self.fresh_var();
            let displaced = locals
                .variable(
                    displaced_name,
                    carried_sort.clone(),
                    GeneratedVarRole::Local,
                    span,
                )
                .expect("packed displaced proof must keep the proof sort");
            let mint = CallKey::Primitive(PrimitiveKey {
                name: crate::proofs::proof_fresh::mint_prim_name(&packed),
                inputs: vec![
                    SortKey {
                        name: "String".to_owned(),
                        class: SortSemanticClass::Value,
                    },
                    carried_sort.clone(),
                    carried_sort.clone(),
                ],
                output: carried_sort.clone(),
            });
            actions.push(GenericAction::Let(
                span.clone(),
                displaced.clone(),
                GenericExpr::Call(
                    span.clone(),
                    mint,
                    vec![
                        GenericExpr::Lit(span.clone(), Literal::String(composition.spelling())),
                        var(hi),
                        var(lo.clone()),
                    ],
                ),
            ));
            (pending, old0, new0, var(displaced), var(lo))
        } else {
            let mut locals = GeneratedRuleBuilder::default();
            let old0 = locals
                .variable("old0", value_sort.clone(), GeneratedVarRole::Local, span)
                .expect("old0 merge variable must keep the value sort");
            let new0 = locals
                .variable("new0", value_sort.clone(), GeneratedVarRole::Local, span)
                .expect("new0 merge variable must keep the value sort");
            (
                TypedHoistGroup::default(),
                old0,
                new0,
                GenericExpr::Lit(span.clone(), Literal::Unit),
                GenericExpr::Lit(span.clone(), Literal::Unit),
            )
        };
        let order = |call: CallKey| {
            GenericExpr::Call(
                span.clone(),
                call,
                vec![var(old0.clone()), var(new0.clone())],
            )
        };
        actions.push(GenericAction::Set(
            span.clone(),
            CallKey::Function(uf),
            vec![order(ordering_max.clone())],
            GenericExpr::Call(
                span.clone(),
                values.clone(),
                vec![order(ordering_min.clone()), displaced],
            ),
        ));
        let result = GenericExpr::Call(span.clone(), values, vec![order(ordering_min), retained]);
        (
            pending,
            GenericMerge {
                actions: GenericActions(actions),
                result,
            },
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn path_compression_rule_direct(
        &self,
        catalog: &mut GeneratedSignatureCatalog,
        span: &Span,
        sort: SortKey,
        carried: SortKey,
        uf: FunctionKey,
        name: String,
        ruleset: String,
        a_name: String,
        b_name: String,
        c_name: String,
        pb_name: String,
        pc_name: String,
        compressed_name: Option<String>,
    ) -> GeneratedRule {
        for key in [sort.clone(), carried.clone()] {
            catalog
                .register_sort(key, span)
                .expect("path-compression sort signatures must be consistent");
        }
        let unit = catalog
            .register_sort(
                SortKey {
                    name: "Unit".to_owned(),
                    class: SortSemanticClass::Value,
                },
                span,
            )
            .expect("Unit signature must be consistent");
        let uf = catalog
            .register_function(uf, span)
            .expect("path-compression UF signature must be consistent");
        let unequal = catalog
            .register_primitive(
                PrimitiveKey {
                    name: "!=".to_owned(),
                    inputs: vec![sort.clone(), sort.clone()],
                    output: unit,
                },
                span,
            )
            .expect("path-compression inequality signature must be consistent");
        let values = catalog
            .values_call(vec![sort.clone(), carried.clone()], span)
            .expect("path-compression row signature must be consistent");
        let trans = compressed_name.as_ref().map(|_| {
            catalog
                .register_primitive(
                    PrimitiveKey {
                        name: crate::proofs::proof_fresh::mint_prim_name(
                            &self.proof_names().eq_trans_constructor,
                        ),
                        inputs: vec![carried.clone(), carried.clone()],
                        output: carried.clone(),
                    },
                    span,
                )
                .expect("path-compression transitivity mint must be consistent")
        });

        let mut builder = GeneratedRuleBuilder::default();
        let b = builder
            .variable(b_name, sort.clone(), GeneratedVarRole::Local, span)
            .expect("path-compression b must keep the equality sort");
        let pb = builder
            .variable(pb_name, carried.clone(), GeneratedVarRole::Local, span)
            .expect("path-compression pb must keep the carried sort");
        let a = builder
            .variable(a_name, sort.clone(), GeneratedVarRole::Local, span)
            .expect("path-compression a must keep the equality sort");
        let c = builder
            .variable(c_name, sort.clone(), GeneratedVarRole::Local, span)
            .expect("path-compression c must keep the equality sort");
        let pc = builder
            .variable(pc_name, carried.clone(), GeneratedVarRole::Local, span)
            .expect("path-compression pc must keep the carried sort");
        let var = |variable| GenericExpr::Var(span.clone(), variable);
        let body = vec![
            crate::ast::GenericFact::Eq(
                span.clone(),
                GenericExpr::Call(
                    span.clone(),
                    values.clone(),
                    vec![var(b.clone()), var(pb.clone())],
                ),
                GenericExpr::Call(span.clone(), uf.clone(), vec![var(a.clone())]),
            ),
            crate::ast::GenericFact::Eq(
                span.clone(),
                GenericExpr::Call(
                    span.clone(),
                    values.clone(),
                    vec![var(c.clone()), var(pc.clone())],
                ),
                GenericExpr::Call(span.clone(), uf.clone(), vec![var(b.clone())]),
            ),
            crate::ast::GenericFact::Fact(GenericExpr::Call(
                span.clone(),
                unequal,
                vec![var(b), var(c.clone())],
            )),
        ];
        let carried_value = if let (Some(name), Some(trans)) = (compressed_name, trans) {
            let compressed = builder
                .variable(name, carried, GeneratedVarRole::Local, span)
                .expect("compressed proof must keep the carried sort");
            let action = GenericAction::Let(
                span.clone(),
                compressed.clone(),
                GenericExpr::Call(span.clone(), trans, vec![var(pb), var(pc)]),
            );
            (Some(action), var(compressed))
        } else {
            (None, GenericExpr::Lit(span.clone(), Literal::Unit))
        };
        let mut head = carried_value.0.into_iter().collect::<Vec<_>>();
        head.push(GenericAction::Set(
            span.clone(),
            uf,
            vec![var(a)],
            GenericExpr::Call(span.clone(), values, vec![var(c), carried_value.1]),
        ));
        GenericRule {
            span: span.clone(),
            body,
            head: GenericActions(head),
            name,
            ruleset,
            eval_mode: RuleEvalMode::Seminaive,
            no_decomp: false,
            include_subsumed: false,
        }
    }

    /// Plan one source sort and every declaration which follows it immediately,
    /// mutating the required name/state registries before returning the
    /// inspectable lexical run.
    pub(super) fn plan_source_sort_direct(
        &mut self,
        catalog: &mut GeneratedSignatureCatalog,
        span: &Span,
        name: &str,
        presort_and_args: &Option<(String, Vec<Expr>)>,
        unionable: bool,
    ) -> TypedHoistGroup {
        let source_sort = self
            .egraph
            .proof_state
            .original_typechecking
            .as_deref()
            .unwrap_or(self.egraph)
            .type_info
            .get_sort_by_name(name)
            .unwrap_or_else(|| panic!("resolved source sort `{name}` is absent at {span}"))
            .clone();
        let key = SortKey::from_sort(&source_sort);
        catalog
            .register_sort(key.clone(), span)
            .expect("source sort signature must be consistent");
        let is_container = presort_and_args.is_some();
        let uf_name = (!is_container).then(|| self.uf_name(name));
        let container_rebuild =
            is_container.then(|| self.build_container_rebuild_spec(&source_sort));
        let presort = presort_and_args
            .as_ref()
            .map(|(presort, args)| self.portable_presort(presort, args, span));
        let mut declarations = vec![PlannedDeclaration {
            kind: PlannedDeclarationKind::Sort(PlannedSortDeclaration {
                span: span.clone(),
                key: key.clone(),
                presort,
                uf: uf_name.clone().map(|name| (name, None)),
                container_rebuild,
                proof_constructors: None,
                unionable,
            }),
            layout_commit: None,
        }];

        if is_container {
            if self.proofs_enabled() {
                let (_, projection) = self.plan_projection_pending_direct(span, key);
                declarations.extend(projection.declarations);
            }
            let group = TypedHoistGroup { declarations };
            group.register_signatures(catalog);
            return group;
        }

        let carried = if self.proofs_enabled() {
            SortKey {
                name: self.proof_names().proof_datatype.clone(),
                class: SortSemanticClass::Eq,
            }
        } else {
            SortKey {
                name: "Unit".to_owned(),
                class: SortSemanticClass::Value,
            }
        };
        let uf_name = uf_name.expect("non-container sort must have a UF name");
        let uf = FunctionKey {
            name: uf_name,
            subtype: FunctionSubtype::Custom,
            inputs: vec![key.clone()],
            output: ValueShape::Tuple(vec![key.clone(), carried.clone()]),
        };
        let path_rule_name = self.egraph.parser.symbol_gen.fresh("uf_path_compress");
        let a = self.egraph.parser.symbol_gen.fresh("uf_a");
        let b = self.egraph.parser.symbol_gen.fresh("uf_b");
        let c = self.egraph.parser.symbol_gen.fresh("uf_c");
        let pb = self.egraph.parser.symbol_gen.fresh("uf_pb");
        let pc = self.egraph.parser.symbol_gen.fresh("uf_pc");
        let (packed, merge) = self.plan_ordered_union_merge_direct(
            span,
            key.clone(),
            uf.clone(),
            Skeleton::Leaf(0).sym().trans(Skeleton::Leaf(1)),
        );
        declarations.extend(packed.declarations);
        declarations.push(PlannedDeclaration {
            kind: PlannedDeclarationKind::Function(function_declaration(
                span.clone(),
                uf.clone(),
                Some(merge),
                FunctionDeclarationMetadata {
                    cost: None,
                    unextractable: true,
                    internal_hidden: true,
                    internal_let: false,
                    term_constructor: None,
                    identity_vals: Some(1),
                    internal_term_node: false,
                },
            )),
            layout_commit: None,
        });
        let compressed = self.proofs_enabled().then(|| self.fresh_var());
        let rule = self.path_compression_rule_direct(
            catalog,
            span,
            key,
            carried,
            uf,
            path_rule_name,
            self.proof_names().path_compress_ruleset_name.clone(),
            a,
            b,
            c,
            pb,
            pc,
            compressed,
        );
        declarations.push(PlannedDeclaration {
            kind: PlannedDeclarationKind::Rule(rule),
            layout_commit: None,
        });
        let group = TypedHoistGroup { declarations };
        group.register_signatures(catalog);
        group
    }

    /// Plan the replacement term relation, FD view, and occurrence indexes for
    /// one source declaration.  A custom FD merge is supplied by the merge-body
    /// lowerer because it owns `MergeIdx`/`MergeRow` proof semantics; this
    /// method owns the declaration schema and metadata around that merge.
    pub(super) fn plan_term_and_view_direct(
        &mut self,
        catalog: &mut GeneratedSignatureCatalog,
        overlay: &mut EncodedFunctionPlanningOverlay,
        span: &Span,
        fdecl: &ResolvedFunctionDecl,
    ) -> (TypedHoistGroup, EncodedFunctionLayout) {
        let ResolvedCall::Func(source_type) = &fdecl.resolved_schema else {
            panic!(
                "resolved source declaration `{}` is not a function",
                fdecl.name
            )
        };
        let source_inputs = source_type
            .input
            .iter()
            .map(SortKey::from_sort)
            .collect::<Vec<_>>();
        let source_output = SortKey::from_sort(source_type.output());
        let view_name = self.view_name(&fdecl.name);

        // This allocation is intentionally unconditional.  Constructors and
        // encoded globals reuse their output sort, but the historical producer
        // still consumed `fresh("view")` before it learned that the name was
        // unused.  Later generated names and printed proofs depend on it.
        let fresh_view_name = self.egraph.parser.symbol_gen.fresh("view");
        let output_is_eclass = self.output_is_eclass(fdecl);
        let term_eclass_sort = if output_is_eclass {
            source_output.clone()
        } else {
            SortKey {
                name: fresh_view_name,
                class: SortSemanticClass::Eq,
            }
        };
        let carried = if self.proofs_enabled() {
            SortKey {
                name: self.proof_names().proof_datatype.clone(),
                class: SortSemanticClass::Eq,
            }
        } else {
            SortKey {
                name: "Unit".to_owned(),
                class: SortSemanticClass::Value,
            }
        };
        let view = FunctionKey {
            name: view_name,
            subtype: FunctionSubtype::Custom,
            inputs: source_inputs.clone(),
            output: ValueShape::Tuple(vec![source_output.clone(), carried]),
        };

        // Group positions by first sort occurrence, keeping all columns of one
        // sort in one disjunctive index.  A custom function's distinct output
        // column is deliberately excluded; containers and value sorts have no
        // UF rows and are excluded as well.
        let types = fdecl.resolved_schema.view_types();
        let indexable = if output_is_eclass {
            types.len()
        } else {
            types.len() - 1
        };
        let mut by_sort: Vec<(String, Vec<usize>)> = Vec::new();
        for (position, sort) in types[..indexable].iter().enumerate() {
            if sort.is_eq_container_sort() || !sort.is_eq_sort() {
                continue;
            }
            match by_sort.iter_mut().find(|(name, _)| name == sort.name()) {
                Some((_, positions)) => positions.push(position),
                None => by_sort.push((sort.name().to_owned(), vec![position])),
            }
        }
        let mut indexes = Vec::with_capacity(by_sort.len());
        let mut state_indexes = Vec::with_capacity(by_sort.len());
        for (sort_name, any_of) in by_sort {
            let name = self
                .egraph
                .parser
                .symbol_gen
                .fresh(&format!("{}Occ_{sort_name}", fdecl.name));
            indexes.push(PlannedIndexDeclaration {
                span: span.clone(),
                name: name.clone(),
                function: view.clone(),
                any_of,
            });
            state_indexes.push(ViewIndex { name, sort_name });
        }
        self.egraph
            .proof_state
            .view_index
            .insert(fdecl.name.clone(), state_indexes);
        self.egraph
            .proof_state
            .proof_names
            .fn_to_term_sort
            .insert(fdecl.name.clone(), term_eclass_sort.name.clone());

        let mut term_inputs = source_inputs;
        if !output_is_eclass {
            term_inputs.push(source_output.clone());
        }
        term_inputs.push(term_eclass_sort.clone());
        let term = FunctionKey {
            name: fdecl.name.clone(),
            subtype: FunctionSubtype::Custom,
            inputs: term_inputs,
            output: ValueShape::Scalar(SortKey {
                name: "Unit".to_owned(),
                class: SortSemanticClass::Value,
            }),
        };

        let mut declarations = vec![];
        if !output_is_eclass {
            declarations.push(PlannedDeclaration {
                kind: PlannedDeclarationKind::Sort(PlannedSortDeclaration {
                    span: span.clone(),
                    key: term_eclass_sort.clone(),
                    presort: None,
                    uf: None,
                    container_rebuild: None,
                    proof_constructors: None,
                    unionable: true,
                }),
                layout_commit: None,
            });
        }
        declarations.push(PlannedDeclaration {
            kind: PlannedDeclarationKind::Function(function_declaration(
                span.clone(),
                term.clone(),
                None,
                FunctionDeclarationMetadata {
                    cost: None,
                    // A term relation is an ordinary generated function, so
                    // source desugaring made it unextractable by default.
                    unextractable: true,
                    internal_hidden: true,
                    internal_let: false,
                    term_constructor: None,
                    identity_vals: None,
                    internal_term_node: true,
                },
            )),
            layout_commit: None,
        });

        let mut custom_merge_hoist = Vec::new();
        let view_merge = if output_is_eclass {
            let uf = FunctionKey {
                name: self.uf_name(&source_output.name),
                subtype: FunctionSubtype::Custom,
                inputs: vec![source_output.clone()],
                output: ValueShape::Tuple(vec![
                    source_output.clone(),
                    if self.proofs_enabled() {
                        SortKey {
                            name: self.proof_names().proof_datatype.clone(),
                            class: SortSemanticClass::Eq,
                        }
                    } else {
                        SortKey {
                            name: "Unit".to_owned(),
                            class: SortSemanticClass::Value,
                        }
                    },
                ]),
            };
            let (packed, merge) = self.plan_ordered_union_merge_direct(
                span,
                source_output.clone(),
                uf,
                Skeleton::Leaf(0).trans(Skeleton::Leaf(1).sym()),
            );
            declarations.extend(packed.declarations);
            Some(merge)
        } else if fdecl.merge.is_some() {
            // Lower only here: the source producer did not allocate merge-body
            // names until after the unused `view` name, occurrence-index names,
            // and persistent layout state. Its first-use Packed declarations
            // entered the source command's pending queue, which was spliced
            // before the fresh term sort and relation. Congruence Packed above
            // was embedded inline and deliberately keeps its later position.
            let (pending, merge) = custom_merge_direct::lower(self, span, fdecl);
            custom_merge_hoist = pending.declarations;
            Some(merge)
        } else {
            debug_assert!(
                !source_type.output().is_eq_sort(),
                "eq-sort :no-merge must be rejected by proof-support validation"
            );
            None
        };
        if !custom_merge_hoist.is_empty() {
            custom_merge_hoist.append(&mut declarations);
            declarations = custom_merge_hoist;
        }
        let view_declaration_index = declarations.len();
        declarations.push(PlannedDeclaration {
            kind: PlannedDeclarationKind::Function(function_declaration(
                span.clone(),
                view.clone(),
                view_merge,
                FunctionDeclarationMetadata {
                    cost: fdecl.cost,
                    unextractable: fdecl.unextractable,
                    internal_hidden: fdecl.internal_hidden,
                    internal_let: fdecl.internal_let,
                    term_constructor: Some(fdecl.name.clone()),
                    identity_vals: Some(1),
                    internal_term_node: false,
                },
            )),
            layout_commit: None,
        });
        declarations.extend(indexes.iter().cloned().map(|index| PlannedDeclaration {
            kind: PlannedDeclarationKind::Index(index),
            layout_commit: None,
        }));

        let layout = EncodedFunctionLayout {
            source_name: fdecl.name.clone(),
            source_subtype: fdecl.subtype,
            term,
            view,
            term_eclass_sort,
            output_is_eclass,
            indexes,
        };
        let mut group = TypedHoistGroup { declarations };
        group.register_signatures(catalog);
        group.declarations[view_declaration_index].layout_commit =
            Some(overlay.stage(&self.egraph.proof_state.encoded_functions, layout.clone()));
        (group, layout)
    }

    /// Finish the unregistered typed declaration/rule run for first-use
    /// subsumption scaffolding.  The rule builder owns semantic rule contents
    /// and fresh-name allocation; this boundary owns one-shot state and lexical
    /// adjacency.
    pub(in crate::proofs) fn plan_subsumption_pending_direct(
        &mut self,
        span: &Span,
        function: &FuncType,
        marker_name: String,
        rules: Vec<GeneratedRule>,
    ) -> TypedHoistGroup {
        if !self
            .egraph
            .proof_state
            .proof_names
            .subsume_declared
            .insert(function.name.clone())
        {
            assert!(
                rules.is_empty(),
                "already-declared subsumption marker supplied duplicate rules"
            );
            return TypedHoistGroup::default();
        }
        let unit = SortKey {
            name: "Unit".to_owned(),
            class: SortSemanticClass::Value,
        };
        let marker = FunctionKey {
            name: marker_name,
            subtype: FunctionSubtype::Custom,
            inputs: function.input.iter().map(SortKey::from_sort).collect(),
            output: ValueShape::Scalar(unit),
        };
        let mut declarations = vec![PlannedDeclaration {
            kind: PlannedDeclarationKind::Function(function_declaration(
                span.clone(),
                marker,
                None,
                FunctionDeclarationMetadata {
                    cost: None,
                    // The marker was parsed as an ordinary function, whose
                    // frontend default is unextractable.
                    unextractable: true,
                    internal_hidden: true,
                    internal_let: false,
                    term_constructor: None,
                    identity_vals: None,
                    internal_term_node: false,
                },
            )),
            layout_commit: None,
        }];
        declarations.extend(rules.into_iter().map(|rule| PlannedDeclaration {
            kind: PlannedDeclarationKind::Rule(rule),
            layout_commit: None,
        }));
        TypedHoistGroup { declarations }
    }
}

#[cfg(test)]
#[path = "declaration_direct_tests.rs"]
mod tests;
