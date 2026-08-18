//! Maintenance-rule generation for the term/proof encoding: the rebuild rules
//! that keep each function's view and subsumed tables canonical, plus the rule
//! that executes a requested subsumption. (`@UF` path compression stays in
//! [`super::proof_encoding`].)

use super::proof_encoding::{ProofInstrumentor, ViewIndex};
use super::proof_encoding_helpers::{DROP_REFLEXIVE_STEP, Skeleton};
use crate::ast::GenericRule;
use crate::proofs::generated_binder::{
    CallKey, FunctionKey, GeneratedEntry, GeneratedRule, GeneratedRuleBuilder,
    GeneratedSignatureCatalog, GeneratedVarRole, PrimitiveKey, SortKey, SortSemanticClass,
    ValueShape,
};
use crate::typechecking::FuncType;
use crate::*;

/// A container-column rebuild proof as semantic steps for portable emission.
/// The encoder deliberately allocates `rebuild_proof` before `anchor`, even
/// though the anchor is the first lexical action; retaining both orders pins
/// the direct builder's local-ID and head-action order.
#[derive(Clone, Debug)]
struct ContainerRebuildProofPlan {
    view_proof: String,
    index: usize,
    container: String,
    projection_constructor: String,
    rebuild_primitive: String,
    congruence_constructor: String,
    rebuild_proof: String,
    anchor: String,
    result: String,
}

/// The single congruence step used by a custom function's direct-equality
/// output rebuild. Keeping this structured pins both the child index and the
/// proof input used by the portable action.
#[derive(Clone, Debug)]
struct CongruenceProofPlan {
    view_proof: String,
    index: usize,
    equality_proof: String,
    constructor: String,
    result: String,
}

struct SubsumeRekeyRuleSpec {
    position: usize,
    leader: String,
    proof: String,
    uf: String,
    name: String,
}

struct SubsumptionRuleSpec {
    span: Span,
    function: FuncType,
    proof_sort: String,
    proofs_enabled: bool,
    marker: String,
    view: String,
    apply_name: String,
    apply_value: String,
    apply_proof: String,
    subsume_ruleset: String,
    rebuilding_ruleset: String,
    rekeys: Vec<SubsumeRekeyRuleSpec>,
}

impl SubsumptionRuleSpec {
    fn build(self, catalog: &mut GeneratedSignatureCatalog) -> Vec<GeneratedRule> {
        let span = &self.span;
        let input_sorts = self
            .function
            .input
            .iter()
            .map(SortKey::from_sort)
            .map(|sort| {
                catalog
                    .register_sort(sort, span)
                    .expect("subsumption input signature must be internally consistent")
            })
            .collect::<Vec<_>>();
        let output_sort = catalog
            .register_sort(SortKey::from_sort(self.function.output()), span)
            .expect("subsumption output signature must be internally consistent");
        let unit_sort = catalog
            .register_sort(
                SortKey {
                    name: "Unit".to_owned(),
                    class: SortSemanticClass::Value,
                },
                span,
            )
            .expect("Unit signature must be internally consistent");
        let proof_sort = if self.proofs_enabled {
            catalog
                .register_sort(
                    SortKey {
                        name: self.proof_sort,
                        class: SortSemanticClass::Eq,
                    },
                    span,
                )
                .expect("proof signature must be internally consistent")
        } else {
            unit_sort.clone()
        };
        let marker_call = catalog
            .register_function(
                FunctionKey {
                    name: self.marker.clone(),
                    subtype: FunctionSubtype::Custom,
                    inputs: input_sorts.clone(),
                    output: ValueShape::Scalar(unit_sort.clone()),
                },
                span,
            )
            .expect("subsumption marker signature must be internally consistent");
        let view_call = catalog
            .register_function(
                FunctionKey {
                    name: self.view.clone(),
                    subtype: FunctionSubtype::Custom,
                    inputs: input_sorts.clone(),
                    output: ValueShape::Tuple(vec![output_sort.clone(), proof_sort.clone()]),
                },
                span,
            )
            .expect("subsumption view signature must be internally consistent");
        let view_values_call = catalog
            .values_call(vec![output_sort.clone(), proof_sort.clone()], span)
            .expect("subsumption view row signature must be internally consistent");

        // The frontend observes all key variables in the marker atom first,
        // followed by the view's value and proof tuple.
        let mut apply_builder = GeneratedRuleBuilder::default();
        let apply_children = input_sorts
            .iter()
            .enumerate()
            .map(|(index, sort)| {
                apply_builder
                    .variable(
                        format!("c{index}_"),
                        sort.clone(),
                        GeneratedVarRole::Local,
                        span,
                    )
                    .expect("subsumption key variable must keep one sort")
            })
            .collect::<Vec<_>>();
        let apply_value = apply_builder
            .variable(self.apply_value, output_sort, GeneratedVarRole::Local, span)
            .expect("subsumption value variable must keep one sort");
        let apply_proof = apply_builder
            .variable(
                self.apply_proof,
                proof_sort.clone(),
                GeneratedVarRole::Local,
                span,
            )
            .expect("subsumption proof variable must keep one sort");
        let var = |variable| GenericExpr::Var(span.clone(), variable);
        let apply_args = apply_children.iter().cloned().map(&var).collect::<Vec<_>>();
        let apply = GenericRule {
            span: span.clone(),
            body: vec![
                GenericFact::Fact(GenericExpr::Call(
                    span.clone(),
                    marker_call.clone(),
                    apply_args.clone(),
                )),
                GenericFact::Eq(
                    span.clone(),
                    GenericExpr::Call(
                        span.clone(),
                        view_values_call.clone(),
                        vec![var(apply_value), var(apply_proof)],
                    ),
                    GenericExpr::Call(span.clone(), view_call.clone(), apply_args.clone()),
                ),
            ],
            head: GenericActions(vec![GenericAction::Change(
                span.clone(),
                Change::Subsume,
                view_call,
                apply_args,
            )]),
            name: self.apply_name,
            ruleset: self.subsume_ruleset,
            eval_mode: RuleEvalMode::Seminaive,
            no_decomp: false,
            include_subsumed: false,
        };
        let mut rules = vec![apply];

        for rekey in self.rekeys {
            let eq_sort = input_sorts[rekey.position].clone();
            debug_assert_eq!(eq_sort.class, SortSemanticClass::Eq);
            let uf_call = catalog
                .register_function(
                    FunctionKey {
                        name: rekey.uf.clone(),
                        subtype: FunctionSubtype::Custom,
                        inputs: vec![eq_sort.clone()],
                        output: ValueShape::Tuple(vec![eq_sort.clone(), proof_sort.clone()]),
                    },
                    span,
                )
                .expect("subsumption UF signature must be internally consistent");
            let not_equal_call = catalog
                .register_primitive(
                    PrimitiveKey {
                        name: "!=".to_owned(),
                        inputs: vec![eq_sort.clone(), eq_sort.clone()],
                        output: unit_sort.clone(),
                    },
                    span,
                )
                .expect("subsumption inequality signature must be internally consistent");
            let uf_values_call = catalog
                .values_call(vec![eq_sort.clone(), proof_sort.clone()], span)
                .expect("subsumption UF row signature must be internally consistent");

            // Each re-key rule has its own local scope: children in lexical key
            // order, then the selected column's leader and unused UF proof.
            let mut builder = GeneratedRuleBuilder::default();
            let children = input_sorts
                .iter()
                .enumerate()
                .map(|(index, sort)| {
                    builder
                        .variable(
                            format!("c{index}_"),
                            sort.clone(),
                            GeneratedVarRole::Local,
                            span,
                        )
                        .expect("subsumption key variable must keep one sort")
                })
                .collect::<Vec<_>>();
            let leader = builder
                .variable(rekey.leader, eq_sort, GeneratedVarRole::Local, span)
                .expect("subsumption leader must keep its equality sort");
            let proof = builder
                .variable(
                    rekey.proof,
                    proof_sort.clone(),
                    GeneratedVarRole::Local,
                    span,
                )
                .expect("subsumption UF proof must keep its carried sort");
            let old_args = children.iter().cloned().map(&var).collect::<Vec<_>>();
            let mut updated_args = old_args.clone();
            updated_args[rekey.position] = var(leader.clone());
            let selected = var(children[rekey.position].clone());
            let direct = GenericRule {
                span: span.clone(),
                body: vec![
                    GenericFact::Fact(GenericExpr::Call(
                        span.clone(),
                        marker_call.clone(),
                        old_args.clone(),
                    )),
                    GenericFact::Eq(
                        span.clone(),
                        GenericExpr::Call(
                            span.clone(),
                            uf_values_call,
                            vec![var(leader), var(proof)],
                        ),
                        GenericExpr::Call(span.clone(), uf_call, vec![selected.clone()]),
                    ),
                    GenericFact::Fact(GenericExpr::Call(
                        span.clone(),
                        not_equal_call,
                        vec![selected, updated_args[rekey.position].clone()],
                    )),
                ],
                head: GenericActions(vec![
                    GenericAction::Set(
                        span.clone(),
                        marker_call.clone(),
                        updated_args,
                        GenericExpr::Lit(span.clone(), Literal::Unit),
                    ),
                    GenericAction::Change(
                        span.clone(),
                        Change::Delete,
                        marker_call.clone(),
                        old_args,
                    ),
                ]),
                name: rekey.name,
                ruleset: self.rebuilding_ruleset.clone(),
                eval_mode: RuleEvalMode::Seminaive,
                no_decomp: false,
                include_subsumed: true,
            };
            rules.push(direct);
        }
        rules
    }
}

#[derive(Clone)]
struct RebuildRuleCommonSpec {
    span: Span,
    function: FuncType,
    proof_sort: String,
    proofs_enabled: bool,
    view: String,
    name: String,
    ruleset: String,
}

struct RegisteredRebuildSignatures {
    input_sorts: Vec<SortKey>,
    output_sort: SortKey,
    carried_sort: SortKey,
    unit_sort: SortKey,
    view_call: CallKey,
    values_call: CallKey,
}

impl RebuildRuleCommonSpec {
    /// Register the signatures every FD-view rebuild shares. This is the one
    /// source of truth for the portable view shape: children are keys and the
    /// value is the `(output, Proof|Unit)` pair carried by the source view.
    fn register(&self, catalog: &mut GeneratedSignatureCatalog) -> RegisteredRebuildSignatures {
        let input_sorts = self
            .function
            .input
            .iter()
            .map(SortKey::from_sort)
            .map(|sort| {
                catalog
                    .register_sort(sort, &self.span)
                    .expect("rebuild input signature must be internally consistent")
            })
            .collect::<Vec<_>>();
        let output_sort = catalog
            .register_sort(SortKey::from_sort(self.function.output()), &self.span)
            .expect("rebuild output signature must be internally consistent");
        let unit_sort = catalog
            .register_sort(
                SortKey {
                    name: "Unit".to_owned(),
                    class: SortSemanticClass::Value,
                },
                &self.span,
            )
            .expect("Unit signature must be internally consistent");
        let carried_sort = if self.proofs_enabled {
            catalog
                .register_sort(
                    SortKey {
                        name: self.proof_sort.clone(),
                        class: SortSemanticClass::Eq,
                    },
                    &self.span,
                )
                .expect("proof signature must be internally consistent")
        } else {
            unit_sort.clone()
        };
        let view_call = catalog
            .register_function(
                FunctionKey {
                    name: self.view.clone(),
                    subtype: FunctionSubtype::Custom,
                    inputs: input_sorts.clone(),
                    output: ValueShape::Tuple(vec![output_sort.clone(), carried_sort.clone()]),
                },
                &self.span,
            )
            .expect("rebuild view signature must be internally consistent");
        let values_call = catalog
            .values_call(vec![output_sort.clone(), carried_sort.clone()], &self.span)
            .expect("rebuild row signature must be internally consistent");
        RegisteredRebuildSignatures {
            input_sorts,
            output_sort,
            carried_sort,
            unit_sort,
            view_call,
            values_call,
        }
    }
}

struct EqContainerKeyRebuildSpec {
    common: RebuildRuleCommonSpec,
    position: usize,
    keys: Vec<String>,
    value: String,
    view_proof: String,
    canonical: String,
    value_primitive: String,
    proof: Option<ContainerRebuildProofPlan>,
}

impl EqContainerKeyRebuildSpec {
    fn build(self, catalog: &mut GeneratedSignatureCatalog) -> GeneratedRule {
        let signatures = self.common.register(catalog);
        let span = &self.common.span;
        let key_sort = signatures.input_sorts[self.position].clone();
        debug_assert_eq!(key_sort.class, SortSemanticClass::EqContainer);
        let rebuild_call = catalog
            .register_primitive(
                PrimitiveKey {
                    name: self.value_primitive.clone(),
                    inputs: vec![key_sort.clone()],
                    output: key_sort.clone(),
                },
                span,
            )
            .expect("container rebuild signature must be internally consistent");
        let not_equal_call = catalog
            .register_primitive(
                PrimitiveKey {
                    name: "!=".to_owned(),
                    inputs: vec![key_sort.clone(), key_sort.clone()],
                    output: signatures.unit_sort.clone(),
                },
                span,
            )
            .expect("container inequality signature must be internally consistent");

        // The view tuple is observed before its key arguments; the canonical
        // value is first introduced by the second body equality.
        let mut builder = GeneratedRuleBuilder::default();
        let value = builder
            .variable(
                self.value,
                signatures.output_sort.clone(),
                GeneratedVarRole::Local,
                span,
            )
            .expect("view value must keep its output sort");
        let view_proof = builder
            .variable(
                self.view_proof,
                signatures.carried_sort.clone(),
                GeneratedVarRole::Local,
                span,
            )
            .expect("view proof must keep its carried sort");
        let keys = self
            .keys
            .into_iter()
            .zip(signatures.input_sorts.iter().cloned())
            .map(|(name, sort)| {
                builder
                    .variable(name, sort, GeneratedVarRole::Local, span)
                    .expect("view key must keep its declared sort")
            })
            .collect::<Vec<_>>();
        let canonical = builder
            .variable(
                self.canonical,
                key_sort.clone(),
                GeneratedVarRole::Local,
                span,
            )
            .expect("rebuilt container must keep the container sort");
        let var = |variable| GenericExpr::Var(span.clone(), variable);
        let old_args = keys.iter().cloned().map(&var).collect::<Vec<_>>();
        let mut updated_args = old_args.clone();
        updated_args[self.position] = var(canonical.clone());
        let selected = var(keys[self.position].clone());
        let body = vec![
            GenericFact::Eq(
                span.clone(),
                GenericExpr::Call(
                    span.clone(),
                    signatures.values_call.clone(),
                    vec![var(value.clone()), var(view_proof.clone())],
                ),
                GenericExpr::Call(span.clone(), signatures.view_call.clone(), old_args.clone()),
            ),
            GenericFact::Eq(
                span.clone(),
                var(canonical.clone()),
                GenericExpr::Call(span.clone(), rebuild_call, vec![selected.clone()]),
            ),
            GenericFact::Fact(GenericExpr::Call(
                span.clone(),
                not_equal_call,
                vec![selected, var(canonical)],
            )),
        ];

        let mut head = Vec::new();
        let carried = if let Some(proof) = self.proof.clone() {
            assert_eq!(
                proof.index, self.position,
                "container proof plan must target the rebuilt key column"
            );
            let planned_view_proof = builder
                .variable(
                    &proof.view_proof,
                    signatures.carried_sort.clone(),
                    GeneratedVarRole::Local,
                    span,
                )
                .expect("planned view proof must keep the carried sort");
            assert_eq!(
                planned_view_proof, view_proof,
                "container proof plan must use the queried row proof"
            );
            let planned_container = builder
                .variable(
                    &proof.container,
                    key_sort.clone(),
                    GeneratedVarRole::Local,
                    span,
                )
                .expect("planned container must keep the rebuilt key sort");
            assert_eq!(
                planned_container, keys[self.position],
                "container proof plan must use the selected key"
            );
            let i64_sort = catalog
                .register_sort(
                    SortKey {
                        name: "i64".to_owned(),
                        class: SortSemanticClass::Value,
                    },
                    span,
                )
                .expect("i64 signature must be internally consistent");
            let projection_call = catalog
                .register_primitive(
                    PrimitiveKey {
                        name: crate::proofs::proof_fresh::mint_prim_name(
                            &proof.projection_constructor,
                        ),
                        inputs: vec![signatures.carried_sort.clone(), i64_sort.clone()],
                        output: signatures.carried_sort.clone(),
                    },
                    span,
                )
                .expect("projection mint signature must be internally consistent");
            let rebuild_proof_call = catalog
                .register_primitive(
                    PrimitiveKey {
                        name: proof.rebuild_primitive.clone(),
                        inputs: vec![key_sort.clone(), signatures.carried_sort.clone()],
                        output: signatures.carried_sort.clone(),
                    },
                    span,
                )
                .expect("container proof signature must be internally consistent");
            let congruence_call = catalog
                .register_primitive(
                    PrimitiveKey {
                        name: crate::proofs::proof_fresh::mint_prim_name(
                            &proof.congruence_constructor,
                        ),
                        inputs: vec![
                            signatures.carried_sort.clone(),
                            i64_sort,
                            signatures.carried_sort.clone(),
                        ],
                        output: signatures.carried_sort.clone(),
                    },
                    span,
                )
                .expect("congruence mint signature must be internally consistent");
            let anchor = builder
                .variable(
                    proof.anchor,
                    signatures.carried_sort.clone(),
                    GeneratedVarRole::Local,
                    span,
                )
                .expect("container anchor must keep the proof sort");
            head.push(GenericAction::Let(
                span.clone(),
                anchor.clone(),
                GenericExpr::Call(
                    span.clone(),
                    projection_call,
                    vec![
                        var(planned_view_proof.clone()),
                        GenericExpr::Lit(span.clone(), Literal::Int(proof.index as i64)),
                    ],
                ),
            ));
            let rebuild_proof = builder
                .variable(
                    proof.rebuild_proof,
                    signatures.carried_sort.clone(),
                    GeneratedVarRole::Local,
                    span,
                )
                .expect("container rebuild proof must keep the proof sort");
            head.push(GenericAction::Let(
                span.clone(),
                rebuild_proof.clone(),
                GenericExpr::Call(
                    span.clone(),
                    rebuild_proof_call,
                    vec![var(planned_container), var(anchor)],
                ),
            ));
            let result = builder
                .variable(
                    proof.result,
                    signatures.carried_sort.clone(),
                    GeneratedVarRole::Local,
                    span,
                )
                .expect("rebuilt row proof must keep the proof sort");
            head.push(GenericAction::Let(
                span.clone(),
                result.clone(),
                GenericExpr::Call(
                    span.clone(),
                    congruence_call,
                    vec![
                        var(planned_view_proof),
                        GenericExpr::Lit(span.clone(), Literal::Int(proof.index as i64)),
                        var(rebuild_proof),
                    ],
                ),
            ));
            var(result)
        } else {
            GenericExpr::Lit(span.clone(), Literal::Unit)
        };
        // Re-keying must insert first: on a collision the view merge observes
        // the replacement before the stale key is removed.
        head.push(GenericAction::Set(
            span.clone(),
            signatures.view_call.clone(),
            updated_args,
            GenericExpr::Call(
                span.clone(),
                signatures.values_call,
                vec![var(value), carried],
            ),
        ));
        head.push(GenericAction::Change(
            span.clone(),
            Change::Delete,
            signatures.view_call,
            old_args,
        ));

        GenericRule {
            span: span.clone(),
            body,
            head: GenericActions(head),
            name: self.common.name,
            ruleset: self.common.ruleset,
            eval_mode: RuleEvalMode::Naive,
            no_decomp: false,
            include_subsumed: true,
        }
    }
}

#[derive(Clone)]
struct IndexedCanonicalStepSpec {
    position: usize,
    sort: ArcSort,
    before: String,
    canonical: String,
    value_primitive: String,
    proof_step: Option<(String, String)>,
}

struct IndexedPackedProofSpec {
    skeleton: String,
    narrowed: Vec<String>,
    constructor: String,
    result: String,
}

struct IndexedWholeRowRebuildSpec {
    common: RebuildRuleCommonSpec,
    index: ViewIndex,
    index_sort: ArcSort,
    uf: String,
    follower: String,
    leader: String,
    leader_proof: String,
    keys: Vec<String>,
    value: String,
    row_proof: String,
    children: Vec<IndexedCanonicalStepSpec>,
    output: Option<IndexedCanonicalStepSpec>,
    packed: Option<IndexedPackedProofSpec>,
    eval_mode: RuleEvalMode,
}

impl IndexedWholeRowRebuildSpec {
    fn build(self, catalog: &mut GeneratedSignatureCatalog) -> GeneratedRule {
        let signatures = self.common.register(catalog);
        let span = &self.common.span;
        let index_sort = catalog
            .register_sort(SortKey::from_sort(&self.index_sort), span)
            .expect("indexed rebuild sort must be internally consistent");
        debug_assert_eq!(index_sort.class, SortSemanticClass::Eq);
        let uf_call = catalog
            .register_function(
                FunctionKey {
                    name: self.uf.clone(),
                    subtype: FunctionSubtype::Custom,
                    inputs: vec![index_sort.clone()],
                    output: ValueShape::Tuple(vec![
                        index_sort.clone(),
                        signatures.carried_sort.clone(),
                    ]),
                },
                span,
            )
            .expect("indexed rebuild UF signature must be internally consistent");
        let uf_values_call = catalog
            .values_call(
                vec![index_sort.clone(), signatures.carried_sort.clone()],
                span,
            )
            .expect("indexed rebuild UF row must be internally consistent");
        let not_equal_call = catalog
            .register_primitive(
                PrimitiveKey {
                    name: "!=".to_owned(),
                    inputs: vec![index_sort.clone(), index_sort.clone()],
                    output: signatures.unit_sort.clone(),
                },
                span,
            )
            .expect("indexed rebuild inequality must be internally consistent");
        let mut index_inputs = vec![index_sort.clone()];
        index_inputs.extend(signatures.input_sorts.iter().cloned());
        index_inputs.push(signatures.output_sort.clone());
        index_inputs.push(signatures.carried_sort.clone());
        let index_call = catalog
            .register_function(
                FunctionKey {
                    name: self.index.name.clone(),
                    subtype: FunctionSubtype::Custom,
                    inputs: index_inputs,
                    output: ValueShape::Scalar(signatures.unit_sort.clone()),
                },
                span,
            )
            .expect("view index signature must be internally consistent");

        // The first UF tuple binds leader/proof before its follower. The index
        // atom then introduces the whole view row in declared column order.
        let mut builder = GeneratedRuleBuilder::default();
        let leader = builder
            .variable(
                self.leader,
                index_sort.clone(),
                GeneratedVarRole::Local,
                span,
            )
            .expect("UF leader must keep the indexed sort");
        let leader_proof = builder
            .variable(
                self.leader_proof,
                signatures.carried_sort.clone(),
                GeneratedVarRole::Local,
                span,
            )
            .expect("UF proof must keep the carried sort");
        let follower = builder
            .variable(self.follower, index_sort, GeneratedVarRole::Local, span)
            .expect("UF follower must keep the indexed sort");
        let keys = self
            .keys
            .into_iter()
            .zip(signatures.input_sorts.iter().cloned())
            .map(|(name, sort)| {
                builder
                    .variable(name, sort, GeneratedVarRole::Local, span)
                    .expect("indexed view key must keep its declared sort")
            })
            .collect::<Vec<_>>();
        let value = builder
            .variable(
                self.value,
                signatures.output_sort.clone(),
                GeneratedVarRole::Local,
                span,
            )
            .expect("indexed view value must keep its output sort");
        let row_proof = builder
            .variable(
                self.row_proof,
                signatures.carried_sort.clone(),
                GeneratedVarRole::Local,
                span,
            )
            .expect("indexed row proof must keep the carried sort");
        let var = |variable| GenericExpr::Var(span.clone(), variable);
        let mut index_args = vec![var(follower.clone())];
        index_args.extend(keys.iter().cloned().map(&var));
        index_args.push(var(value.clone()));
        index_args.push(var(row_proof.clone()));
        let body = vec![
            GenericFact::Eq(
                span.clone(),
                GenericExpr::Call(
                    span.clone(),
                    uf_values_call,
                    vec![var(leader.clone()), var(leader_proof)],
                ),
                GenericExpr::Call(span.clone(), uf_call, vec![var(follower.clone())]),
            ),
            GenericFact::Fact(GenericExpr::Call(
                span.clone(),
                not_equal_call,
                vec![var(follower), var(leader)],
            )),
            GenericFact::Fact(GenericExpr::Call(span.clone(), index_call, index_args)),
        ];

        let mut head = Vec::new();
        let mut updated_args = keys.iter().cloned().map(&var).collect::<Vec<_>>();
        let mut moved = Vec::new();
        let mut step_proofs = Vec::new();
        for step in self.children {
            let sort = catalog
                .register_sort(SortKey::from_sort(&step.sort), span)
                .expect("canonicalized child sort must be internally consistent");
            debug_assert_eq!(sort, signatures.input_sorts[step.position]);
            let value_call = catalog
                .register_primitive(
                    PrimitiveKey {
                        name: step.value_primitive.clone(),
                        inputs: vec![sort.clone(), sort.clone()],
                        output: sort.clone(),
                    },
                    span,
                )
                .expect("UF canonicalization signature must be internally consistent");
            let before = keys[step.position].clone();
            debug_assert_eq!(before.name, step.before);
            let canonical = builder
                .variable(step.canonical, sort.clone(), GeneratedVarRole::Local, span)
                .expect("canonicalized child must keep its equality sort");
            head.push(GenericAction::Let(
                span.clone(),
                canonical.clone(),
                GenericExpr::Call(
                    span.clone(),
                    value_call,
                    vec![var(before.clone()), var(before.clone())],
                ),
            ));
            if let Some((proof_name, proof_primitive)) = step.proof_step {
                let proof_call = catalog
                    .register_primitive(
                        PrimitiveKey {
                            name: proof_primitive.clone(),
                            inputs: vec![sort.clone(), signatures.carried_sort.clone()],
                            output: signatures.carried_sort.clone(),
                        },
                        span,
                    )
                    .expect("UF canonical proof signature must be internally consistent");
                let proof = builder
                    .variable(
                        proof_name,
                        signatures.carried_sort.clone(),
                        GeneratedVarRole::Local,
                        span,
                    )
                    .expect("canonical child proof must keep the proof sort");
                head.push(GenericAction::Let(
                    span.clone(),
                    proof.clone(),
                    GenericExpr::Call(
                        span.clone(),
                        proof_call,
                        vec![var(before.clone()), var(row_proof.clone())],
                    ),
                ));
                step_proofs.push(proof);
                moved.push((sort, before, canonical.clone()));
            }
            updated_args[step.position] = var(canonical);
        }

        let mut updated_value = value.clone();
        if let Some(step) = self.output {
            let sort = catalog
                .register_sort(SortKey::from_sort(&step.sort), span)
                .expect("canonicalized e-class sort must be internally consistent");
            debug_assert_eq!(sort, signatures.output_sort);
            let value_call = catalog
                .register_primitive(
                    PrimitiveKey {
                        name: step.value_primitive.clone(),
                        inputs: vec![sort.clone(), sort.clone()],
                        output: sort.clone(),
                    },
                    span,
                )
                .expect("e-class canonicalization signature must be internally consistent");
            debug_assert_eq!(value.name, step.before);
            let canonical = builder
                .variable(step.canonical, sort.clone(), GeneratedVarRole::Local, span)
                .expect("canonicalized e-class must keep the output sort");
            head.push(GenericAction::Let(
                span.clone(),
                canonical.clone(),
                GenericExpr::Call(
                    span.clone(),
                    value_call,
                    vec![var(value.clone()), var(value.clone())],
                ),
            ));
            if let Some((proof_name, proof_primitive)) = step.proof_step {
                let proof_call = catalog
                    .register_primitive(
                        PrimitiveKey {
                            name: proof_primitive.clone(),
                            inputs: vec![sort.clone(), signatures.carried_sort.clone()],
                            output: signatures.carried_sort.clone(),
                        },
                        span,
                    )
                    .expect("e-class canonical proof signature must be internally consistent");
                let proof = builder
                    .variable(
                        proof_name,
                        signatures.carried_sort.clone(),
                        GeneratedVarRole::Local,
                        span,
                    )
                    .expect("canonical e-class proof must keep the proof sort");
                head.push(GenericAction::Let(
                    span.clone(),
                    proof.clone(),
                    GenericExpr::Call(
                        span.clone(),
                        proof_call,
                        vec![var(value.clone()), var(row_proof.clone())],
                    ),
                ));
                step_proofs.push(proof);
                moved.push((sort, value.clone(), canonical.clone()));
            }
            updated_value = canonical;
        }

        let carried = if let Some(packed) = self.packed {
            debug_assert_eq!(packed.narrowed.len(), moved.len());
            let string_sort = catalog
                .register_sort(
                    SortKey {
                        name: "String".to_owned(),
                        class: SortSemanticClass::Value,
                    },
                    span,
                )
                .expect("String signature must be internally consistent");
            let i64_sort = catalog
                .register_sort(
                    SortKey {
                        name: "i64".to_owned(),
                        class: SortSemanticClass::Value,
                    },
                    span,
                )
                .expect("i64 signature must be internally consistent");
            let mut spelling = GenericExpr::Lit(span.clone(), Literal::String(packed.skeleton));
            for (column, (result, (sort, before, after))) in packed
                .narrowed
                .into_iter()
                .zip(moved.into_iter())
                .enumerate()
            {
                let drop_call = catalog
                    .register_primitive(
                        PrimitiveKey {
                            name: DROP_REFLEXIVE_STEP.to_owned(),
                            inputs: vec![string_sort.clone(), i64_sort.clone(), sort.clone(), sort],
                            output: string_sort.clone(),
                        },
                        span,
                    )
                    .expect("proof-spelling narrowing must be internally consistent");
                let narrowed = builder
                    .variable(result, string_sort.clone(), GeneratedVarRole::Local, span)
                    .expect("narrowed proof spelling must keep String sort");
                head.push(GenericAction::Let(
                    span.clone(),
                    narrowed.clone(),
                    GenericExpr::Call(
                        span.clone(),
                        drop_call,
                        vec![
                            spelling,
                            GenericExpr::Lit(span.clone(), Literal::Int((column + 1) as i64)),
                            var(before),
                            var(after),
                        ],
                    ),
                ));
                spelling = var(narrowed);
            }
            let mut mint_inputs = vec![string_sort];
            mint_inputs.extend(std::iter::repeat_n(
                signatures.carried_sort.clone(),
                1 + step_proofs.len(),
            ));
            let mint_name = crate::proofs::proof_fresh::mint_prim_name(&packed.constructor);
            let packed_call = catalog
                .register_primitive(
                    PrimitiveKey {
                        name: mint_name.clone(),
                        inputs: mint_inputs,
                        output: signatures.carried_sort.clone(),
                    },
                    span,
                )
                .expect("packed proof mint signature must be internally consistent");
            let result = builder
                .variable(
                    packed.result,
                    signatures.carried_sort.clone(),
                    GeneratedVarRole::Local,
                    span,
                )
                .expect("packed proof must keep the proof sort");
            let mut args = vec![spelling, var(row_proof.clone())];
            args.extend(step_proofs.into_iter().map(&var));
            head.push(GenericAction::Let(
                span.clone(),
                result.clone(),
                GenericExpr::Call(span.clone(), packed_call, args),
            ));
            var(result)
        } else if self.common.proofs_enabled {
            var(row_proof)
        } else {
            GenericExpr::Lit(span.clone(), Literal::Unit)
        };

        // Whole-row rebuilds delete first: an e-class-only move leaves the key
        // unchanged, and the replacement must survive that case.
        head.push(GenericAction::Change(
            span.clone(),
            Change::Delete,
            signatures.view_call.clone(),
            keys.iter().cloned().map(&var).collect(),
        ));
        head.push(GenericAction::Set(
            span.clone(),
            signatures.view_call.clone(),
            updated_args,
            GenericExpr::Call(
                span.clone(),
                signatures.values_call,
                vec![var(updated_value), carried],
            ),
        ));
        GenericRule {
            span: span.clone(),
            body,
            head: GenericActions(head),
            name: self.common.name,
            ruleset: self.common.ruleset,
            eval_mode: self.eval_mode,
            no_decomp: false,
            include_subsumed: true,
        }
    }
}

struct CustomDirectOutputRebuildSpec {
    common: RebuildRuleCommonSpec,
    keys: Vec<String>,
    value: String,
    view_proof: String,
    canonical: String,
    equality_proof: String,
    uf: String,
    proof: Option<CongruenceProofPlan>,
}

impl CustomDirectOutputRebuildSpec {
    fn build(self, catalog: &mut GeneratedSignatureCatalog) -> GeneratedRule {
        let signatures = self.common.register(catalog);
        let span = &self.common.span;
        debug_assert_eq!(signatures.output_sort.class, SortSemanticClass::Eq);
        let uf_call = catalog
            .register_function(
                FunctionKey {
                    name: self.uf.clone(),
                    subtype: FunctionSubtype::Custom,
                    inputs: vec![signatures.output_sort.clone()],
                    output: ValueShape::Tuple(vec![
                        signatures.output_sort.clone(),
                        signatures.carried_sort.clone(),
                    ]),
                },
                span,
            )
            .expect("custom-output UF signature must be internally consistent");
        let uf_values_call = catalog
            .values_call(
                vec![
                    signatures.output_sort.clone(),
                    signatures.carried_sort.clone(),
                ],
                span,
            )
            .expect("custom-output UF row must be internally consistent");
        let not_equal_call = catalog
            .register_primitive(
                PrimitiveKey {
                    name: "!=".to_owned(),
                    inputs: vec![
                        signatures.output_sort.clone(),
                        signatures.output_sort.clone(),
                    ],
                    output: signatures.unit_sort.clone(),
                },
                span,
            )
            .expect("custom-output inequality must be internally consistent");

        let mut builder = GeneratedRuleBuilder::default();
        let value = builder
            .variable(
                self.value,
                signatures.output_sort.clone(),
                GeneratedVarRole::Local,
                span,
            )
            .expect("custom output must keep its declared sort");
        let view_proof = builder
            .variable(
                self.view_proof,
                signatures.carried_sort.clone(),
                GeneratedVarRole::Local,
                span,
            )
            .expect("view proof must keep the carried sort");
        let keys = self
            .keys
            .into_iter()
            .zip(signatures.input_sorts.iter().cloned())
            .map(|(name, sort)| {
                builder
                    .variable(name, sort, GeneratedVarRole::Local, span)
                    .expect("custom view key must keep its declared sort")
            })
            .collect::<Vec<_>>();
        let canonical = builder
            .variable(
                self.canonical,
                signatures.output_sort.clone(),
                GeneratedVarRole::Local,
                span,
            )
            .expect("canonical output must keep its equality sort");
        let equality_proof = builder
            .variable(
                self.equality_proof,
                signatures.carried_sort.clone(),
                GeneratedVarRole::Local,
                span,
            )
            .expect("output UF proof must keep the carried sort");
        let var = |variable| GenericExpr::Var(span.clone(), variable);
        let args = keys.iter().cloned().map(&var).collect::<Vec<_>>();
        let body = vec![
            GenericFact::Eq(
                span.clone(),
                GenericExpr::Call(
                    span.clone(),
                    signatures.values_call.clone(),
                    vec![var(value.clone()), var(view_proof.clone())],
                ),
                GenericExpr::Call(span.clone(), signatures.view_call.clone(), args.clone()),
            ),
            GenericFact::Eq(
                span.clone(),
                GenericExpr::Call(
                    span.clone(),
                    uf_values_call,
                    vec![var(canonical.clone()), var(equality_proof.clone())],
                ),
                GenericExpr::Call(span.clone(), uf_call, vec![var(value.clone())]),
            ),
            GenericFact::Fact(GenericExpr::Call(
                span.clone(),
                not_equal_call,
                vec![var(value.clone()), var(canonical.clone())],
            )),
        ];

        let mut head = Vec::new();
        let carried = if let Some(proof) = self.proof.clone() {
            let planned_view_proof = builder
                .variable(
                    &proof.view_proof,
                    signatures.carried_sort.clone(),
                    GeneratedVarRole::Local,
                    span,
                )
                .expect("planned view proof must keep the carried sort");
            assert_eq!(
                planned_view_proof, view_proof,
                "congruence plan must use the queried row proof"
            );
            let planned_equality_proof = builder
                .variable(
                    &proof.equality_proof,
                    signatures.carried_sort.clone(),
                    GeneratedVarRole::Local,
                    span,
                )
                .expect("planned equality proof must keep the carried sort");
            assert_eq!(
                planned_equality_proof, equality_proof,
                "congruence plan must use the output UF proof"
            );
            let i64_sort = catalog
                .register_sort(
                    SortKey {
                        name: "i64".to_owned(),
                        class: SortSemanticClass::Value,
                    },
                    span,
                )
                .expect("i64 signature must be internally consistent");
            let congruence_call = catalog
                .register_primitive(
                    PrimitiveKey {
                        name: crate::proofs::proof_fresh::mint_prim_name(&proof.constructor),
                        inputs: vec![
                            signatures.carried_sort.clone(),
                            i64_sort,
                            signatures.carried_sort.clone(),
                        ],
                        output: signatures.carried_sort.clone(),
                    },
                    span,
                )
                .expect("custom-output congruence must be internally consistent");
            let result = builder
                .variable(
                    proof.result,
                    signatures.carried_sort.clone(),
                    GeneratedVarRole::Local,
                    span,
                )
                .expect("rewritten row proof must keep the proof sort");
            head.push(GenericAction::Let(
                span.clone(),
                result.clone(),
                GenericExpr::Call(
                    span.clone(),
                    congruence_call,
                    vec![
                        var(planned_view_proof),
                        GenericExpr::Lit(span.clone(), Literal::Int(proof.index as i64)),
                        var(planned_equality_proof),
                    ],
                ),
            ));
            var(result)
        } else {
            GenericExpr::Lit(span.clone(), Literal::Unit)
        };
        // Delete first so this maintenance rewrite cannot re-run the custom
        // view merge against the stale value it is replacing.
        head.push(GenericAction::Change(
            span.clone(),
            Change::Delete,
            signatures.view_call.clone(),
            args.clone(),
        ));
        head.push(GenericAction::Set(
            span.clone(),
            signatures.view_call.clone(),
            args,
            GenericExpr::Call(
                span.clone(),
                signatures.values_call,
                vec![var(canonical), carried],
            ),
        ));

        GenericRule {
            span: span.clone(),
            body,
            head: GenericActions(head),
            name: self.common.name,
            ruleset: self.common.ruleset,
            eval_mode: RuleEvalMode::Seminaive,
            no_decomp: false,
            include_subsumed: true,
        }
    }
}

struct CustomContainerOutputRebuildSpec {
    common: RebuildRuleCommonSpec,
    position: usize,
    keys: Vec<String>,
    value: String,
    view_proof: String,
    canonical: String,
    value_primitive: String,
    proof: Option<ContainerRebuildProofPlan>,
}

impl CustomContainerOutputRebuildSpec {
    fn build(self, catalog: &mut GeneratedSignatureCatalog) -> GeneratedRule {
        let signatures = self.common.register(catalog);
        let span = &self.common.span;
        debug_assert_eq!(signatures.output_sort.class, SortSemanticClass::EqContainer);
        let rebuild_call = catalog
            .register_primitive(
                PrimitiveKey {
                    name: self.value_primitive.clone(),
                    inputs: vec![signatures.output_sort.clone()],
                    output: signatures.output_sort.clone(),
                },
                span,
            )
            .expect("output-container rebuild must be internally consistent");
        let not_equal_call = catalog
            .register_primitive(
                PrimitiveKey {
                    name: "!=".to_owned(),
                    inputs: vec![
                        signatures.output_sort.clone(),
                        signatures.output_sort.clone(),
                    ],
                    output: signatures.unit_sort.clone(),
                },
                span,
            )
            .expect("output-container inequality must be internally consistent");

        let mut builder = GeneratedRuleBuilder::default();
        let value = builder
            .variable(
                self.value,
                signatures.output_sort.clone(),
                GeneratedVarRole::Local,
                span,
            )
            .expect("container output must keep its declared sort");
        let view_proof = builder
            .variable(
                self.view_proof,
                signatures.carried_sort.clone(),
                GeneratedVarRole::Local,
                span,
            )
            .expect("view proof must keep the carried sort");
        let keys = self
            .keys
            .into_iter()
            .zip(signatures.input_sorts.iter().cloned())
            .map(|(name, sort)| {
                builder
                    .variable(name, sort, GeneratedVarRole::Local, span)
                    .expect("container-output view key must keep its declared sort")
            })
            .collect::<Vec<_>>();
        let canonical = builder
            .variable(
                self.canonical,
                signatures.output_sort.clone(),
                GeneratedVarRole::Local,
                span,
            )
            .expect("rebuilt output must keep its container sort");
        let var = |variable| GenericExpr::Var(span.clone(), variable);
        let args = keys.iter().cloned().map(&var).collect::<Vec<_>>();
        let body = vec![
            GenericFact::Eq(
                span.clone(),
                GenericExpr::Call(
                    span.clone(),
                    signatures.values_call.clone(),
                    vec![var(value.clone()), var(view_proof.clone())],
                ),
                GenericExpr::Call(span.clone(), signatures.view_call.clone(), args.clone()),
            ),
            GenericFact::Eq(
                span.clone(),
                var(canonical.clone()),
                GenericExpr::Call(span.clone(), rebuild_call, vec![var(value.clone())]),
            ),
            GenericFact::Fact(GenericExpr::Call(
                span.clone(),
                not_equal_call,
                vec![var(value.clone()), var(canonical.clone())],
            )),
        ];

        let mut head = Vec::new();
        let carried = if let Some(proof) = self.proof.clone() {
            assert_eq!(
                proof.index, self.position,
                "container proof plan must target the rebuilt output column"
            );
            let planned_view_proof = builder
                .variable(
                    &proof.view_proof,
                    signatures.carried_sort.clone(),
                    GeneratedVarRole::Local,
                    span,
                )
                .expect("planned view proof must keep the carried sort");
            assert_eq!(
                planned_view_proof, view_proof,
                "output-container plan must use the queried row proof"
            );
            let planned_container = builder
                .variable(
                    &proof.container,
                    signatures.output_sort.clone(),
                    GeneratedVarRole::Local,
                    span,
                )
                .expect("planned container must keep the output sort");
            assert_eq!(
                planned_container, value,
                "output-container plan must use the stale output value"
            );
            let i64_sort = catalog
                .register_sort(
                    SortKey {
                        name: "i64".to_owned(),
                        class: SortSemanticClass::Value,
                    },
                    span,
                )
                .expect("i64 signature must be internally consistent");
            let projection_call = catalog
                .register_primitive(
                    PrimitiveKey {
                        name: crate::proofs::proof_fresh::mint_prim_name(
                            &proof.projection_constructor,
                        ),
                        inputs: vec![signatures.carried_sort.clone(), i64_sort.clone()],
                        output: signatures.carried_sort.clone(),
                    },
                    span,
                )
                .expect("output projection mint must be internally consistent");
            let rebuild_proof_call = catalog
                .register_primitive(
                    PrimitiveKey {
                        name: proof.rebuild_primitive.clone(),
                        inputs: vec![
                            signatures.output_sort.clone(),
                            signatures.carried_sort.clone(),
                        ],
                        output: signatures.carried_sort.clone(),
                    },
                    span,
                )
                .expect("output-container proof must be internally consistent");
            let congruence_call = catalog
                .register_primitive(
                    PrimitiveKey {
                        name: crate::proofs::proof_fresh::mint_prim_name(
                            &proof.congruence_constructor,
                        ),
                        inputs: vec![
                            signatures.carried_sort.clone(),
                            i64_sort,
                            signatures.carried_sort.clone(),
                        ],
                        output: signatures.carried_sort.clone(),
                    },
                    span,
                )
                .expect("output congruence mint must be internally consistent");
            let anchor = builder
                .variable(
                    proof.anchor,
                    signatures.carried_sort.clone(),
                    GeneratedVarRole::Local,
                    span,
                )
                .expect("output-container anchor must keep the proof sort");
            head.push(GenericAction::Let(
                span.clone(),
                anchor.clone(),
                GenericExpr::Call(
                    span.clone(),
                    projection_call,
                    vec![
                        var(planned_view_proof.clone()),
                        GenericExpr::Lit(span.clone(), Literal::Int(proof.index as i64)),
                    ],
                ),
            ));
            let rebuild_proof = builder
                .variable(
                    proof.rebuild_proof,
                    signatures.carried_sort.clone(),
                    GeneratedVarRole::Local,
                    span,
                )
                .expect("output-container rebuild proof must keep the proof sort");
            head.push(GenericAction::Let(
                span.clone(),
                rebuild_proof.clone(),
                GenericExpr::Call(
                    span.clone(),
                    rebuild_proof_call,
                    vec![var(planned_container), var(anchor)],
                ),
            ));
            let result = builder
                .variable(
                    proof.result,
                    signatures.carried_sort.clone(),
                    GeneratedVarRole::Local,
                    span,
                )
                .expect("output-container row proof must keep the proof sort");
            head.push(GenericAction::Let(
                span.clone(),
                result.clone(),
                GenericExpr::Call(
                    span.clone(),
                    congruence_call,
                    vec![
                        var(planned_view_proof),
                        GenericExpr::Lit(span.clone(), Literal::Int(proof.index as i64)),
                        var(rebuild_proof),
                    ],
                ),
            ));
            var(result)
        } else {
            GenericExpr::Lit(span.clone(), Literal::Unit)
        };
        head.push(GenericAction::Change(
            span.clone(),
            Change::Delete,
            signatures.view_call.clone(),
            args.clone(),
        ));
        head.push(GenericAction::Set(
            span.clone(),
            signatures.view_call.clone(),
            args,
            GenericExpr::Call(
                span.clone(),
                signatures.values_call,
                vec![var(canonical), carried],
            ),
        ));

        GenericRule {
            span: span.clone(),
            body,
            head: GenericActions(head),
            name: self.common.name,
            ruleset: self.common.ruleset,
            eval_mode: RuleEvalMode::Naive,
            no_decomp: false,
            include_subsumed: true,
        }
    }
}

/// The composition a view rebuild's packed row states, over the columns
/// [`ProofInstrumentor::indexed_rebuild_rule_direct`] writes: the row proof in column
/// 0, then one step proof per canonicalized child in `children`, in the order
/// the composition applies them, then the e-class's own step when `eclass`.
///
/// The firing narrows this to the columns that moved, so the row it writes may
/// name fewer (see [`DROP_REFLEXIVE_STEP`]).
pub(super) fn rebuild_skeleton(children: &[usize], eclass: bool) -> Skeleton {
    let mut skeleton = Skeleton::Leaf(0);
    for (step, &child) in children.iter().enumerate() {
        skeleton = skeleton.congr(child, Skeleton::Leaf(1 + step));
    }
    if eclass {
        skeleton = Skeleton::Leaf(1 + children.len()).sym().trans(skeleton);
    }
    skeleton
}

impl ProofInstrumentor<'_> {
    /// The declarations `name`'s subsumption marker needs: the marker relation,
    /// the maintenance rule that applies it to the view, and one rebuild rule per
    /// eq-sort child keeping the marker keyed on canonical children.
    ///
    /// The marker is what makes subsumption survive rebuilding: re-keying a view
    /// row inserts it afresh, and the new row carries no subsumed bit of its own.
    pub(super) fn subsume_scaffolding(&mut self, span: &Span, function: &FuncType) {
        let name = &function.name;
        let input = &function.input;
        let subsumed_name = self.subsumed_name(name);
        let view_name = self.view_name(name);
        let subsume_ruleset = self.proof_names().subsume_ruleset_name.clone();
        let rebuilding_ruleset = self.proof_names().rebuilding_ruleset_name.clone();
        let apply_name = self.egraph.parser.symbol_gen.fresh("subsume_rule");

        // The view is keyed by children only, so match its value tuple to subsume
        // by key (the bridge re-reads every value column when subsuming a
        // tuple-output view). A subsumed row is kept for size/proofs but excluded
        // from matching.
        let e = self.fresh_var();
        let pf = self.fresh_var();

        // Mirrors [`Self::rebuilding_rules`]: the single-key `@UF` has no row for
        // a canonical node, so a per-column lookup only fires when there is work.
        // The `@UF` proof column is unused for subsumed rows.
        let mut rekeys = Vec::new();
        for (i, ty) in input.iter().enumerate() {
            if !ty.is_eq_sort() {
                continue;
            }
            let leader = format!("c{i}_leader_");
            let uf_name = self.uf_name(ty.name());
            let proof_var = self.fresh_var();
            let rekey_name = self
                .egraph
                .parser
                .symbol_gen
                .fresh("rebuild_to_subsume_rule");
            rekeys.push(SubsumeRekeyRuleSpec {
                position: i,
                leader: leader.clone(),
                proof: proof_var.clone(),
                uf: uf_name.clone(),
                name: rekey_name.clone(),
            });
        }
        let spec = SubsumptionRuleSpec {
            span: span.clone(),
            function: function.clone(),
            proof_sort: self.proof_type_str().to_owned(),
            proofs_enabled: self.proofs_enabled(),
            marker: subsumed_name.clone(),
            view: view_name,
            apply_name,
            apply_value: e,
            apply_proof: pf,
            subsume_ruleset,
            rebuilding_ruleset,
            rekeys,
        };
        let rules = spec.build(&mut GeneratedSignatureCatalog::default());
        let declarations =
            self.plan_subsumption_pending_direct(span, function, subsumed_name, rules);
        self.queue_pending_declaration_group(declarations);
    }

    /// Production maintenance lowering. It allocates stable semantic names and
    /// constructs portable specs plus the non-rule packed declarations that
    /// remain in the command stream.
    pub(super) fn rebuilding_rules(&mut self, fdecl: &ResolvedFunctionDecl) -> Vec<GeneratedEntry> {
        let proofs = self.proofs_enabled();
        let output_is_eclass = self.output_is_eclass(fdecl);
        let types = fdecl.resolved_schema.view_types();
        let n = types.len();
        let n_keys = n - 1;
        let key_vars = (0..n_keys)
            .map(|index| format!("c{index}_"))
            .collect::<Vec<_>>();
        let view_name = self.view_name(&fdecl.name);
        let function = match &fdecl.resolved_schema {
            crate::core::ResolvedCall::Func(function) => (**function).clone(),
            _ => unreachable!("function declarations resolve to function calls"),
        };
        let proof_sort = self.proof_type_str().to_owned();
        let ruleset = self.proof_names().rebuilding_ruleset_name.clone();
        let mut commands = Vec::new();

        for (position, sort) in types[..n_keys].iter().enumerate() {
            if !sort.is_eq_container_sort() {
                continue;
            }
            // `query_fd_view` historically minted these two names in this order.
            let value = self.fresh_var();
            let view_proof = self.fresh_var();
            let canonical = format!("c{position}_canon_");
            let value_primitive = self.container_rebuild_prim(sort);
            let proof = proofs.then(|| {
                self.container_rebuild_proof_plan(&view_proof, position, sort, &key_vars[position])
            });
            let name = self.egraph.parser.symbol_gen.fresh("rebuild_rule");
            let spec = EqContainerKeyRebuildSpec {
                common: RebuildRuleCommonSpec {
                    span: fdecl.span.clone(),
                    function: function.clone(),
                    proof_sort: proof_sort.clone(),
                    proofs_enabled: proofs,
                    view: view_name.clone(),
                    name,
                    ruleset: ruleset.clone(),
                },
                position,
                keys: key_vars.clone(),
                value,
                view_proof,
                canonical,
                value_primitive,
                proof,
            };
            commands.push(GeneratedEntry::Rule(spec.build(&mut self.signatures)));
        }

        for index in self
            .egraph
            .proof_state
            .view_index
            .get(&fdecl.name)
            .cloned()
            .unwrap_or_default()
        {
            commands.extend(self.indexed_rebuild_rule_direct(fdecl, &key_vars, &types, &index));
        }

        if !output_is_eclass && fdecl.subtype == FunctionSubtype::Custom && !fdecl.internal_let {
            if types[n - 1].is_eq_sort() {
                commands.extend(self.fd_custom_value_rebuild_rule_direct(fdecl, &key_vars, n - 1));
            } else if types[n - 1].is_eq_container_sort() {
                commands.extend(self.fd_container_value_rebuild_rule_direct(
                    fdecl,
                    &key_vars,
                    n - 1,
                ));
            }
        }
        commands
    }

    /// Allocate the portable proof plan in the source construction order:
    /// rebuild result first, then the lexically earlier projection anchor, then
    /// the congruence result.
    fn container_rebuild_proof_plan(
        &mut self,
        view_proof: &str,
        index: usize,
        container_sort: &ArcSort,
        container: &str,
    ) -> ContainerRebuildProofPlan {
        let congruence_constructor = self.proof_names().congr_constructor.clone();
        let projection_constructor = self.proof_names().proj_constructor.clone();
        let rebuild_primitive = self.container_rebuild_proof_prim(container_sort);
        let rebuild_proof = self.fresh_var();
        let anchor = self.fresh_var();
        let result = self.fresh_var();
        ContainerRebuildProofPlan {
            view_proof: view_proof.to_owned(),
            index,
            container: container.to_owned(),
            projection_constructor,
            rebuild_primitive,
            congruence_constructor,
            rebuild_proof,
            anchor,
            result,
        }
    }

    fn indexed_rebuild_rule_direct(
        &mut self,
        fdecl: &ResolvedFunctionDecl,
        key_vars: &[String],
        types: &[ArcSort],
        index: &ViewIndex,
    ) -> Vec<GeneratedEntry> {
        use crate::proofs::proof_container_rebuild::{
            uf_canon_prim_name, uf_canon_proof_prim_name,
        };

        let proofs = self.proofs_enabled();
        let n_keys = key_vars.len();
        let follower = self.fresh_var();
        let leader = self.fresh_var();
        let leader_proof = self.fresh_var();
        let value = format!("e{n_keys}_");
        let row_proof = self.fresh_var();
        let uf = self.uf_name(&index.sort_name);
        let index_sort = types
            .iter()
            .find(|sort| sort.name() == index.sort_name)
            .expect("view index sort must occur in the indexed view")
            .clone();
        let mut children = Vec::new();
        let mut moved_positions = Vec::new();
        for position in 0..n_keys {
            if types[position].is_eq_container_sort() || !types[position].is_eq_sort() {
                continue;
            }
            let before = key_vars[position].clone();
            let canonical = format!("c{position}_canon_");
            let child_uf = self.uf_name(types[position].name());
            let value_primitive = uf_canon_prim_name(&child_uf);
            let proof_step = proofs.then(|| {
                let result = self.fresh_var();
                (result, uf_canon_proof_prim_name(&child_uf))
            });
            if proofs {
                moved_positions.push(position);
            }
            children.push(IndexedCanonicalStepSpec {
                position,
                sort: types[position].clone(),
                before,
                canonical,
                value_primitive,
                proof_step,
            });
        }

        let output = if self.output_is_eclass(fdecl)
            && types[n_keys].is_eq_sort()
            && !types[n_keys].is_eq_container_sort()
        {
            let output_uf = self.uf_name(types[n_keys].name());
            let proof_step = proofs.then(|| {
                let result = self.fresh_var();
                (result, uf_canon_proof_prim_name(&output_uf))
            });
            if proofs {
                moved_positions.push(n_keys);
            }
            Some(IndexedCanonicalStepSpec {
                position: n_keys,
                sort: types[n_keys].clone(),
                before: value.clone(),
                canonical: format!("e{n_keys}_canon_"),
                value_primitive: uf_canon_prim_name(&output_uf),
                proof_step,
            })
        } else {
            None
        };

        let child_positions = children
            .iter()
            .filter_map(|step| step.proof_step.as_ref().map(|_| step.position))
            .collect::<Vec<_>>();
        let has_output_step = output
            .as_ref()
            .is_some_and(|step| step.proof_step.is_some());
        let skeleton = rebuild_skeleton(&child_positions, has_output_step);
        let step_count = child_positions.len() + usize::from(has_output_step);
        let mut declaration_entries = Vec::new();
        let packed = if step_count == 0 {
            None
        } else {
            let (constructor, declaration) =
                self.plan_packed_pending_direct(&fdecl.span, 1 + step_count);
            declaration_entries.extend(self.register_inline_declaration_group(declaration));
            let narrowed = moved_positions
                .iter()
                .map(|_| self.fresh_var())
                .collect::<Vec<_>>();
            let result = self.fresh_var();
            Some(IndexedPackedProofSpec {
                skeleton: skeleton.spelling(),
                narrowed,
                constructor,
                result,
            })
        };
        let name = self.egraph.parser.symbol_gen.fresh("rebuild_rule");
        let eval_mode = if self.egraph.proof_state.force_proof_naive {
            RuleEvalMode::Naive
        } else {
            RuleEvalMode::UnsafeSeminaive
        };
        let function = match &fdecl.resolved_schema {
            crate::core::ResolvedCall::Func(function) => (**function).clone(),
            _ => unreachable!("function declarations resolve to function calls"),
        };
        let spec = IndexedWholeRowRebuildSpec {
            common: RebuildRuleCommonSpec {
                span: fdecl.span.clone(),
                function,
                proof_sort: self.proof_type_str().to_owned(),
                proofs_enabled: proofs,
                view: self.view_name(&fdecl.name),
                name,
                ruleset: self.proof_names().rebuilding_ruleset_name.clone(),
            },
            index: index.clone(),
            index_sort,
            uf,
            follower,
            leader,
            leader_proof,
            keys: key_vars.to_vec(),
            value,
            row_proof,
            children,
            output,
            packed,
            eval_mode,
        };
        declaration_entries.push(GeneratedEntry::Rule(spec.build(&mut self.signatures)));
        declaration_entries
    }

    fn fd_custom_value_rebuild_rule_direct(
        &mut self,
        fdecl: &ResolvedFunctionDecl,
        key_vars: &[String],
        out_idx: usize,
    ) -> Vec<GeneratedEntry> {
        let uf = self.uf_name(fdecl.resolved_schema.output().name());
        let value = self.fresh_var();
        let view_proof = self.fresh_var();
        let canonical = self.fresh_var();
        let equality_proof = self.fresh_var();
        let proofs = self.proofs_enabled();
        let proof = proofs.then(|| {
            let constructor = self.proof_names().congr_constructor.clone();
            let result = self.fresh_var();
            CongruenceProofPlan {
                view_proof: view_proof.clone(),
                index: out_idx,
                equality_proof: equality_proof.clone(),
                constructor,
                result,
            }
        });
        let name = self.egraph.parser.symbol_gen.fresh("rebuild_rule");
        let function = match &fdecl.resolved_schema {
            crate::core::ResolvedCall::Func(function) => (**function).clone(),
            _ => unreachable!("function declarations resolve to function calls"),
        };
        let spec = CustomDirectOutputRebuildSpec {
            common: RebuildRuleCommonSpec {
                span: fdecl.span.clone(),
                function,
                proof_sort: self.proof_type_str().to_owned(),
                proofs_enabled: proofs,
                view: self.view_name(&fdecl.name),
                name,
                ruleset: self.proof_names().rebuilding_ruleset_name.clone(),
            },
            keys: key_vars.to_vec(),
            value,
            view_proof,
            canonical,
            equality_proof,
            uf,
            proof,
        };
        vec![GeneratedEntry::Rule(spec.build(&mut self.signatures))]
    }

    fn fd_container_value_rebuild_rule_direct(
        &mut self,
        fdecl: &ResolvedFunctionDecl,
        key_vars: &[String],
        out_idx: usize,
    ) -> Vec<GeneratedEntry> {
        let output_sort = fdecl.resolved_schema.output().clone();
        let value_primitive = self.container_rebuild_prim(&output_sort);
        let value = self.fresh_var();
        let view_proof = self.fresh_var();
        let canonical = self.fresh_var();
        let proofs = self.proofs_enabled();
        let proof = proofs
            .then(|| self.container_rebuild_proof_plan(&view_proof, out_idx, &output_sort, &value));
        let name = self.egraph.parser.symbol_gen.fresh("rebuild_rule");
        let function = match &fdecl.resolved_schema {
            crate::core::ResolvedCall::Func(function) => (**function).clone(),
            _ => unreachable!("function declarations resolve to function calls"),
        };
        let spec = CustomContainerOutputRebuildSpec {
            common: RebuildRuleCommonSpec {
                span: fdecl.span.clone(),
                function,
                proof_sort: self.proof_type_str().to_owned(),
                proofs_enabled: proofs,
                view: self.view_name(&fdecl.name),
                name,
                ruleset: self.proof_names().rebuilding_ruleset_name.clone(),
            },
            position: out_idx,
            keys: key_vars.to_vec(),
            value,
            view_proof,
            canonical,
            value_primitive,
            proof,
        };
        vec![GeneratedEntry::Rule(spec.build(&mut self.signatures))]
    }
}
