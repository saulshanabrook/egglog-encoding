//! Maintenance-rule generation for the term/proof encoding: the rebuild rules
//! that keep each function's view and subsumed tables canonical, plus the rule
//! that executes a requested subsumption. (`@UF` path compression stays in
//! [`super::proof_encoding`].)

use super::proof_encoding::{ProofInstrumentor, ViewIndex};
use super::proof_encoding_helpers::{DROP_REFLEXIVE_STEP, Skeleton};
use crate::proofs::generated_binder::{
    CallKey, FunctionKey, GeneratedEntry, GeneratedRule, GeneratedSemanticEmitter,
    GeneratedSignatureCatalog, PrimitiveKey, SortKey, SortSemanticClass, ValueShape,
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
        let (input_sorts, output_sort, unit_sort, proof_sort, marker_call, view_call, view_values) = {
            let mut signatures = GeneratedSemanticEmitter::new(catalog, span);
            let input_sorts = self
                .function
                .input
                .iter()
                .map(SortKey::from_sort)
                .map(|sort| signatures.sort(sort))
                .collect::<Vec<_>>();
            let output_sort = signatures.sort(SortKey::from_sort(self.function.output()));
            let unit_sort = signatures.sort(SortKey {
                name: "Unit".to_owned(),
                class: SortSemanticClass::Value,
            });
            let proof_sort = if self.proofs_enabled {
                signatures.sort(SortKey {
                    name: self.proof_sort,
                    class: SortSemanticClass::Eq,
                })
            } else {
                unit_sort.clone()
            };
            let marker_call = signatures.function(FunctionKey {
                name: self.marker.clone(),
                subtype: FunctionSubtype::Custom,
                inputs: input_sorts.clone(),
                output: ValueShape::Scalar(unit_sort.clone()),
            });
            let view_call = signatures.function(FunctionKey {
                name: self.view.clone(),
                subtype: FunctionSubtype::Custom,
                inputs: input_sorts.clone(),
                output: ValueShape::Tuple(vec![output_sort.clone(), proof_sort.clone()]),
            });
            let view_values = signatures.values(vec![output_sort.clone(), proof_sort.clone()]);
            (
                input_sorts,
                output_sort,
                unit_sort,
                proof_sort,
                marker_call,
                view_call,
                view_values,
            )
        };

        // The frontend observes all key variables in the marker atom first,
        // followed by the view's value and proof tuple.
        let mut apply_emitter = GeneratedSemanticEmitter::new(catalog, span);
        let apply_children = input_sorts
            .iter()
            .enumerate()
            .map(|(index, sort)| apply_emitter.local(format!("c{index}_"), sort.clone()))
            .collect::<Vec<_>>();
        let apply_value = apply_emitter.local(self.apply_value, output_sort);
        let apply_proof = apply_emitter.local(self.apply_proof, proof_sort.clone());
        let var = |variable| GenericExpr::Var(span.clone(), variable);
        let apply_args = apply_children.iter().cloned().map(&var).collect::<Vec<_>>();
        let marker = apply_emitter.call(marker_call.clone(), apply_args.clone());
        let row = apply_emitter.call(
            view_values.clone(),
            vec![var(apply_value), var(apply_proof)],
        );
        let view = apply_emitter.call(view_call.clone(), apply_args.clone());
        let body = vec![
            GenericFact::Fact(marker),
            GenericFact::Eq(span.clone(), row, view),
        ];
        apply_emitter.change(Change::Subsume, view_call.clone(), apply_args);
        let apply = apply_emitter.finish_rule(
            body,
            self.apply_name,
            self.subsume_ruleset,
            RuleEvalMode::Seminaive,
            false,
        );
        let mut rules = vec![apply];

        for rekey in self.rekeys {
            let eq_sort = input_sorts[rekey.position].clone();
            debug_assert_eq!(eq_sort.class, SortSemanticClass::Eq);
            let mut emitter = GeneratedSemanticEmitter::new(catalog, span);
            let uf_call = emitter.function(FunctionKey {
                name: rekey.uf.clone(),
                subtype: FunctionSubtype::Custom,
                inputs: vec![eq_sort.clone()],
                output: ValueShape::Tuple(vec![eq_sort.clone(), proof_sort.clone()]),
            });
            let not_equal_call = emitter.primitive(PrimitiveKey {
                name: "!=".to_owned(),
                inputs: vec![eq_sort.clone(), eq_sort.clone()],
                output: unit_sort.clone(),
            });
            let uf_values = emitter.values(vec![eq_sort.clone(), proof_sort.clone()]);

            // Each re-key rule has its own local scope: children in lexical key
            // order, then the selected column's leader and unused UF proof.
            let children = input_sorts
                .iter()
                .enumerate()
                .map(|(index, sort)| emitter.local(format!("c{index}_"), sort.clone()))
                .collect::<Vec<_>>();
            let leader = emitter.local(rekey.leader, eq_sort);
            let proof = emitter.local(rekey.proof, proof_sort.clone());
            let old_args = children.iter().cloned().map(&var).collect::<Vec<_>>();
            let mut updated_args = old_args.clone();
            updated_args[rekey.position] = var(leader.clone());
            let selected = var(children[rekey.position].clone());
            let marker = emitter.call(marker_call.clone(), old_args.clone());
            let uf_row = emitter.call(uf_values, vec![var(leader), var(proof)]);
            let uf = emitter.call(uf_call, vec![selected.clone()]);
            let unequal = emitter.call(
                not_equal_call,
                vec![selected, updated_args[rekey.position].clone()],
            );
            let body = vec![
                GenericFact::Fact(marker),
                GenericFact::Eq(span.clone(), uf_row, uf),
                GenericFact::Fact(unequal),
            ];
            emitter.set(
                marker_call.clone(),
                updated_args,
                GenericExpr::Lit(span.clone(), Literal::Unit),
            );
            emitter.change(Change::Delete, marker_call.clone(), old_args);
            let direct = emitter.finish_rule(
                body,
                rekey.name,
                self.rebuilding_ruleset.clone(),
                RuleEvalMode::Seminaive,
                true,
            );
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
        let mut emitter = GeneratedSemanticEmitter::new(catalog, &self.span);
        let input_sorts = self
            .function
            .input
            .iter()
            .map(SortKey::from_sort)
            .map(|sort| emitter.sort(sort))
            .collect::<Vec<_>>();
        let output_sort = emitter.sort(SortKey::from_sort(self.function.output()));
        let unit_sort = emitter.sort(SortKey {
            name: "Unit".to_owned(),
            class: SortSemanticClass::Value,
        });
        let carried_sort = if self.proofs_enabled {
            emitter.sort(SortKey {
                name: self.proof_sort.clone(),
                class: SortSemanticClass::Eq,
            })
        } else {
            unit_sort.clone()
        };
        let view_call = emitter.function(FunctionKey {
            name: self.view.clone(),
            subtype: FunctionSubtype::Custom,
            inputs: input_sorts.clone(),
            output: ValueShape::Tuple(vec![output_sort.clone(), carried_sort.clone()]),
        });
        let values_call = emitter.values(vec![output_sort.clone(), carried_sort.clone()]);
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
        let mut emitter = GeneratedSemanticEmitter::new(catalog, span);
        let rebuild_call = emitter.primitive(PrimitiveKey {
            name: self.value_primitive.clone(),
            inputs: vec![key_sort.clone()],
            output: key_sort.clone(),
        });
        let not_equal_call = emitter.primitive(PrimitiveKey {
            name: "!=".to_owned(),
            inputs: vec![key_sort.clone(), key_sort.clone()],
            output: signatures.unit_sort.clone(),
        });

        // The view tuple is observed before its key arguments; the canonical
        // value is first introduced by the second body equality.
        let value = emitter.local(self.value, signatures.output_sort.clone());
        let view_proof = emitter.local(self.view_proof, signatures.carried_sort.clone());
        let keys = self
            .keys
            .into_iter()
            .zip(signatures.input_sorts.iter().cloned())
            .map(|(name, sort)| emitter.local(name, sort))
            .collect::<Vec<_>>();
        let canonical = emitter.local(self.canonical, key_sort.clone());
        let var = |variable| GenericExpr::Var(span.clone(), variable);
        let old_args = keys.iter().cloned().map(&var).collect::<Vec<_>>();
        let mut updated_args = old_args.clone();
        updated_args[self.position] = var(canonical.clone());
        let selected = var(keys[self.position].clone());
        let view_row = emitter.call(
            signatures.values_call.clone(),
            vec![var(value.clone()), var(view_proof.clone())],
        );
        let view = emitter.call(signatures.view_call.clone(), old_args.clone());
        let rebuilt = emitter.call(rebuild_call, vec![selected.clone()]);
        let unequal = emitter.call(not_equal_call, vec![selected, var(canonical.clone())]);
        let body = vec![
            GenericFact::Eq(span.clone(), view_row, view),
            GenericFact::Eq(span.clone(), var(canonical.clone()), rebuilt),
            GenericFact::Fact(unequal),
        ];

        let carried = if let Some(proof) = self.proof.clone() {
            assert_eq!(
                proof.index, self.position,
                "container proof plan must target the rebuilt key column"
            );
            let planned_view_proof =
                emitter.local(&proof.view_proof, signatures.carried_sort.clone());
            assert_eq!(
                planned_view_proof, view_proof,
                "container proof plan must use the queried row proof"
            );
            let planned_container = emitter.local(&proof.container, key_sort.clone());
            assert_eq!(
                planned_container, keys[self.position],
                "container proof plan must use the selected key"
            );
            let i64_sort = emitter.sort(SortKey {
                name: "i64".to_owned(),
                class: SortSemanticClass::Value,
            });
            let projection_call = emitter.primitive(PrimitiveKey {
                name: crate::proofs::proof_fresh::mint_prim_name(&proof.projection_constructor),
                inputs: vec![signatures.carried_sort.clone(), i64_sort.clone()],
                output: signatures.carried_sort.clone(),
            });
            let rebuild_proof_call = emitter.primitive(PrimitiveKey {
                name: proof.rebuild_primitive.clone(),
                inputs: vec![key_sort.clone(), signatures.carried_sort.clone()],
                output: signatures.carried_sort.clone(),
            });
            let congruence_call = emitter.primitive(PrimitiveKey {
                name: crate::proofs::proof_fresh::mint_prim_name(&proof.congruence_constructor),
                inputs: vec![
                    signatures.carried_sort.clone(),
                    i64_sort,
                    signatures.carried_sort.clone(),
                ],
                output: signatures.carried_sort.clone(),
            });
            let anchor = emitter.bind_call(
                proof.anchor,
                signatures.carried_sort.clone(),
                projection_call,
                vec![
                    var(planned_view_proof.clone()),
                    GenericExpr::Lit(span.clone(), Literal::Int(proof.index as i64)),
                ],
            );
            let rebuild_proof = emitter.bind_call(
                proof.rebuild_proof,
                signatures.carried_sort.clone(),
                rebuild_proof_call,
                vec![var(planned_container), var(anchor)],
            );
            let result = emitter.bind_call(
                proof.result,
                signatures.carried_sort.clone(),
                congruence_call,
                vec![
                    var(planned_view_proof),
                    GenericExpr::Lit(span.clone(), Literal::Int(proof.index as i64)),
                    var(rebuild_proof),
                ],
            );
            var(result)
        } else {
            GenericExpr::Lit(span.clone(), Literal::Unit)
        };
        // Re-keying must insert first: on a collision the view merge observes
        // the replacement before the stale key is removed.
        let row = emitter.call(signatures.values_call, vec![var(value), carried]);
        emitter.set(signatures.view_call.clone(), updated_args, row);
        emitter.change(Change::Delete, signatures.view_call, old_args);

        emitter.finish_rule(
            body,
            self.common.name,
            self.common.ruleset,
            RuleEvalMode::Naive,
            true,
        )
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
        let mut emitter = GeneratedSemanticEmitter::new(catalog, span);
        let index_sort = emitter.sort(SortKey::from_sort(&self.index_sort));
        debug_assert_eq!(index_sort.class, SortSemanticClass::Eq);
        let uf_call = emitter.function(FunctionKey {
            name: self.uf.clone(),
            subtype: FunctionSubtype::Custom,
            inputs: vec![index_sort.clone()],
            output: ValueShape::Tuple(vec![index_sort.clone(), signatures.carried_sort.clone()]),
        });
        let uf_values = emitter.values(vec![index_sort.clone(), signatures.carried_sort.clone()]);
        let not_equal_call = emitter.primitive(PrimitiveKey {
            name: "!=".to_owned(),
            inputs: vec![index_sort.clone(), index_sort.clone()],
            output: signatures.unit_sort.clone(),
        });
        let mut index_inputs = vec![index_sort.clone()];
        index_inputs.extend(signatures.input_sorts.iter().cloned());
        index_inputs.push(signatures.output_sort.clone());
        index_inputs.push(signatures.carried_sort.clone());
        let index_call = emitter.function(FunctionKey {
            name: self.index.name.clone(),
            subtype: FunctionSubtype::Custom,
            inputs: index_inputs,
            output: ValueShape::Scalar(signatures.unit_sort.clone()),
        });

        // The first UF tuple binds leader/proof before its follower. The index
        // atom then introduces the whole view row in declared column order.
        let leader = emitter.local(self.leader, index_sort.clone());
        let leader_proof = emitter.local(self.leader_proof, signatures.carried_sort.clone());
        let follower = emitter.local(self.follower, index_sort);
        let keys = self
            .keys
            .into_iter()
            .zip(signatures.input_sorts.iter().cloned())
            .map(|(name, sort)| emitter.local(name, sort))
            .collect::<Vec<_>>();
        let value = emitter.local(self.value, signatures.output_sort.clone());
        let row_proof = emitter.local(self.row_proof, signatures.carried_sort.clone());
        let var = |variable| GenericExpr::Var(span.clone(), variable);
        let mut index_args = vec![var(follower.clone())];
        index_args.extend(keys.iter().cloned().map(&var));
        index_args.push(var(value.clone()));
        index_args.push(var(row_proof.clone()));
        let uf_row = emitter.call(uf_values, vec![var(leader.clone()), var(leader_proof)]);
        let uf = emitter.call(uf_call, vec![var(follower.clone())]);
        let unequal = emitter.call(not_equal_call, vec![var(follower), var(leader)]);
        let index = emitter.call(index_call, index_args);
        let body = vec![
            GenericFact::Eq(span.clone(), uf_row, uf),
            GenericFact::Fact(unequal),
            GenericFact::Fact(index),
        ];

        let mut updated_args = keys.iter().cloned().map(&var).collect::<Vec<_>>();
        let mut moved = Vec::new();
        let mut step_proofs = Vec::new();
        for step in self.children {
            let sort = emitter.sort(SortKey::from_sort(&step.sort));
            debug_assert_eq!(sort, signatures.input_sorts[step.position]);
            let value_call = emitter.primitive(PrimitiveKey {
                name: step.value_primitive.clone(),
                inputs: vec![sort.clone(), sort.clone()],
                output: sort.clone(),
            });
            let before = keys[step.position].clone();
            debug_assert_eq!(before.name, step.before);
            let canonical = emitter.bind_call(
                step.canonical,
                sort.clone(),
                value_call,
                vec![var(before.clone()), var(before.clone())],
            );
            if let Some((proof_name, proof_primitive)) = step.proof_step {
                let proof_call = emitter.primitive(PrimitiveKey {
                    name: proof_primitive.clone(),
                    inputs: vec![sort.clone(), signatures.carried_sort.clone()],
                    output: signatures.carried_sort.clone(),
                });
                let proof = emitter.bind_call(
                    proof_name,
                    signatures.carried_sort.clone(),
                    proof_call,
                    vec![var(before.clone()), var(row_proof.clone())],
                );
                step_proofs.push(proof);
                moved.push((sort, before, canonical.clone()));
            }
            updated_args[step.position] = var(canonical);
        }

        let mut updated_value = value.clone();
        if let Some(step) = self.output {
            let sort = emitter.sort(SortKey::from_sort(&step.sort));
            debug_assert_eq!(sort, signatures.output_sort);
            let value_call = emitter.primitive(PrimitiveKey {
                name: step.value_primitive.clone(),
                inputs: vec![sort.clone(), sort.clone()],
                output: sort.clone(),
            });
            debug_assert_eq!(value.name, step.before);
            let canonical = emitter.bind_call(
                step.canonical,
                sort.clone(),
                value_call,
                vec![var(value.clone()), var(value.clone())],
            );
            if let Some((proof_name, proof_primitive)) = step.proof_step {
                let proof_call = emitter.primitive(PrimitiveKey {
                    name: proof_primitive.clone(),
                    inputs: vec![sort.clone(), signatures.carried_sort.clone()],
                    output: signatures.carried_sort.clone(),
                });
                let proof = emitter.bind_call(
                    proof_name,
                    signatures.carried_sort.clone(),
                    proof_call,
                    vec![var(value.clone()), var(row_proof.clone())],
                );
                step_proofs.push(proof);
                moved.push((sort, value.clone(), canonical.clone()));
            }
            updated_value = canonical;
        }

        let carried = if let Some(packed) = self.packed {
            debug_assert_eq!(packed.narrowed.len(), moved.len());
            let string_sort = emitter.sort(SortKey {
                name: "String".to_owned(),
                class: SortSemanticClass::Value,
            });
            let i64_sort = emitter.sort(SortKey {
                name: "i64".to_owned(),
                class: SortSemanticClass::Value,
            });
            let mut spelling = GenericExpr::Lit(span.clone(), Literal::String(packed.skeleton));
            for (column, (result, (sort, before, after))) in packed
                .narrowed
                .into_iter()
                .zip(moved.into_iter())
                .enumerate()
            {
                let drop_call = emitter.primitive(PrimitiveKey {
                    name: DROP_REFLEXIVE_STEP.to_owned(),
                    inputs: vec![string_sort.clone(), i64_sort.clone(), sort.clone(), sort],
                    output: string_sort.clone(),
                });
                let narrowed = emitter.bind_call(
                    result,
                    string_sort.clone(),
                    drop_call,
                    vec![
                        spelling,
                        GenericExpr::Lit(span.clone(), Literal::Int((column + 1) as i64)),
                        var(before),
                        var(after),
                    ],
                );
                spelling = var(narrowed);
            }
            let mut mint_inputs = vec![string_sort];
            mint_inputs.extend(std::iter::repeat_n(
                signatures.carried_sort.clone(),
                1 + step_proofs.len(),
            ));
            let mint_name = crate::proofs::proof_fresh::mint_prim_name(&packed.constructor);
            let packed_call = emitter.primitive(PrimitiveKey {
                name: mint_name.clone(),
                inputs: mint_inputs,
                output: signatures.carried_sort.clone(),
            });
            let mut args = vec![spelling, var(row_proof.clone())];
            args.extend(step_proofs.into_iter().map(&var));
            let result = emitter.bind_call(
                packed.result,
                signatures.carried_sort.clone(),
                packed_call,
                args,
            );
            var(result)
        } else if self.common.proofs_enabled {
            var(row_proof)
        } else {
            GenericExpr::Lit(span.clone(), Literal::Unit)
        };

        // Whole-row rebuilds delete first: an e-class-only move leaves the key
        // unchanged, and the replacement must survive that case.
        emitter.change(
            Change::Delete,
            signatures.view_call.clone(),
            keys.iter().cloned().map(&var).collect(),
        );
        let row = emitter.call(signatures.values_call, vec![var(updated_value), carried]);
        emitter.set(signatures.view_call.clone(), updated_args, row);
        emitter.finish_rule(
            body,
            self.common.name,
            self.common.ruleset,
            self.eval_mode,
            true,
        )
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
        let mut emitter = GeneratedSemanticEmitter::new(catalog, span);
        let uf_call = emitter.function(FunctionKey {
            name: self.uf.clone(),
            subtype: FunctionSubtype::Custom,
            inputs: vec![signatures.output_sort.clone()],
            output: ValueShape::Tuple(vec![
                signatures.output_sort.clone(),
                signatures.carried_sort.clone(),
            ]),
        });
        let uf_values = emitter.values(vec![
            signatures.output_sort.clone(),
            signatures.carried_sort.clone(),
        ]);
        let not_equal_call = emitter.primitive(PrimitiveKey {
            name: "!=".to_owned(),
            inputs: vec![
                signatures.output_sort.clone(),
                signatures.output_sort.clone(),
            ],
            output: signatures.unit_sort.clone(),
        });

        let value = emitter.local(self.value, signatures.output_sort.clone());
        let view_proof = emitter.local(self.view_proof, signatures.carried_sort.clone());
        let keys = self
            .keys
            .into_iter()
            .zip(signatures.input_sorts.iter().cloned())
            .map(|(name, sort)| emitter.local(name, sort))
            .collect::<Vec<_>>();
        let canonical = emitter.local(self.canonical, signatures.output_sort.clone());
        let equality_proof = emitter.local(self.equality_proof, signatures.carried_sort.clone());
        let var = |variable| GenericExpr::Var(span.clone(), variable);
        let args = keys.iter().cloned().map(&var).collect::<Vec<_>>();
        let view_row = emitter.call(
            signatures.values_call.clone(),
            vec![var(value.clone()), var(view_proof.clone())],
        );
        let view = emitter.call(signatures.view_call.clone(), args.clone());
        let uf_row = emitter.call(
            uf_values,
            vec![var(canonical.clone()), var(equality_proof.clone())],
        );
        let uf = emitter.call(uf_call, vec![var(value.clone())]);
        let unequal = emitter.call(
            not_equal_call,
            vec![var(value.clone()), var(canonical.clone())],
        );
        let body = vec![
            GenericFact::Eq(span.clone(), view_row, view),
            GenericFact::Eq(span.clone(), uf_row, uf),
            GenericFact::Fact(unequal),
        ];

        let carried = if let Some(proof) = self.proof.clone() {
            let planned_view_proof =
                emitter.local(&proof.view_proof, signatures.carried_sort.clone());
            assert_eq!(
                planned_view_proof, view_proof,
                "congruence plan must use the queried row proof"
            );
            let planned_equality_proof =
                emitter.local(&proof.equality_proof, signatures.carried_sort.clone());
            assert_eq!(
                planned_equality_proof, equality_proof,
                "congruence plan must use the output UF proof"
            );
            let i64_sort = emitter.sort(SortKey {
                name: "i64".to_owned(),
                class: SortSemanticClass::Value,
            });
            let congruence_call = emitter.primitive(PrimitiveKey {
                name: crate::proofs::proof_fresh::mint_prim_name(&proof.constructor),
                inputs: vec![
                    signatures.carried_sort.clone(),
                    i64_sort,
                    signatures.carried_sort.clone(),
                ],
                output: signatures.carried_sort.clone(),
            });
            let result = emitter.bind_call(
                proof.result,
                signatures.carried_sort.clone(),
                congruence_call,
                vec![
                    var(planned_view_proof),
                    GenericExpr::Lit(span.clone(), Literal::Int(proof.index as i64)),
                    var(planned_equality_proof),
                ],
            );
            var(result)
        } else {
            GenericExpr::Lit(span.clone(), Literal::Unit)
        };
        // Delete first so this maintenance rewrite cannot re-run the custom
        // view merge against the stale value it is replacing.
        emitter.change(Change::Delete, signatures.view_call.clone(), args.clone());
        let row = emitter.call(signatures.values_call, vec![var(canonical), carried]);
        emitter.set(signatures.view_call.clone(), args, row);

        emitter.finish_rule(
            body,
            self.common.name,
            self.common.ruleset,
            RuleEvalMode::Seminaive,
            true,
        )
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
        let mut emitter = GeneratedSemanticEmitter::new(catalog, span);
        let rebuild_call = emitter.primitive(PrimitiveKey {
            name: self.value_primitive.clone(),
            inputs: vec![signatures.output_sort.clone()],
            output: signatures.output_sort.clone(),
        });
        let not_equal_call = emitter.primitive(PrimitiveKey {
            name: "!=".to_owned(),
            inputs: vec![
                signatures.output_sort.clone(),
                signatures.output_sort.clone(),
            ],
            output: signatures.unit_sort.clone(),
        });

        let value = emitter.local(self.value, signatures.output_sort.clone());
        let view_proof = emitter.local(self.view_proof, signatures.carried_sort.clone());
        let keys = self
            .keys
            .into_iter()
            .zip(signatures.input_sorts.iter().cloned())
            .map(|(name, sort)| emitter.local(name, sort))
            .collect::<Vec<_>>();
        let canonical = emitter.local(self.canonical, signatures.output_sort.clone());
        let var = |variable| GenericExpr::Var(span.clone(), variable);
        let args = keys.iter().cloned().map(&var).collect::<Vec<_>>();
        let view_row = emitter.call(
            signatures.values_call.clone(),
            vec![var(value.clone()), var(view_proof.clone())],
        );
        let view = emitter.call(signatures.view_call.clone(), args.clone());
        let rebuilt = emitter.call(rebuild_call, vec![var(value.clone())]);
        let unequal = emitter.call(
            not_equal_call,
            vec![var(value.clone()), var(canonical.clone())],
        );
        let body = vec![
            GenericFact::Eq(span.clone(), view_row, view),
            GenericFact::Eq(span.clone(), var(canonical.clone()), rebuilt),
            GenericFact::Fact(unequal),
        ];

        let carried = if let Some(proof) = self.proof.clone() {
            assert_eq!(
                proof.index, self.position,
                "container proof plan must target the rebuilt output column"
            );
            let planned_view_proof =
                emitter.local(&proof.view_proof, signatures.carried_sort.clone());
            assert_eq!(
                planned_view_proof, view_proof,
                "output-container plan must use the queried row proof"
            );
            let planned_container = emitter.local(&proof.container, signatures.output_sort.clone());
            assert_eq!(
                planned_container, value,
                "output-container plan must use the stale output value"
            );
            let i64_sort = emitter.sort(SortKey {
                name: "i64".to_owned(),
                class: SortSemanticClass::Value,
            });
            let projection_call = emitter.primitive(PrimitiveKey {
                name: crate::proofs::proof_fresh::mint_prim_name(&proof.projection_constructor),
                inputs: vec![signatures.carried_sort.clone(), i64_sort.clone()],
                output: signatures.carried_sort.clone(),
            });
            let rebuild_proof_call = emitter.primitive(PrimitiveKey {
                name: proof.rebuild_primitive.clone(),
                inputs: vec![
                    signatures.output_sort.clone(),
                    signatures.carried_sort.clone(),
                ],
                output: signatures.carried_sort.clone(),
            });
            let congruence_call = emitter.primitive(PrimitiveKey {
                name: crate::proofs::proof_fresh::mint_prim_name(&proof.congruence_constructor),
                inputs: vec![
                    signatures.carried_sort.clone(),
                    i64_sort,
                    signatures.carried_sort.clone(),
                ],
                output: signatures.carried_sort.clone(),
            });
            let anchor = emitter.bind_call(
                proof.anchor,
                signatures.carried_sort.clone(),
                projection_call,
                vec![
                    var(planned_view_proof.clone()),
                    GenericExpr::Lit(span.clone(), Literal::Int(proof.index as i64)),
                ],
            );
            let rebuild_proof = emitter.bind_call(
                proof.rebuild_proof,
                signatures.carried_sort.clone(),
                rebuild_proof_call,
                vec![var(planned_container), var(anchor)],
            );
            let result = emitter.bind_call(
                proof.result,
                signatures.carried_sort.clone(),
                congruence_call,
                vec![
                    var(planned_view_proof),
                    GenericExpr::Lit(span.clone(), Literal::Int(proof.index as i64)),
                    var(rebuild_proof),
                ],
            );
            var(result)
        } else {
            GenericExpr::Lit(span.clone(), Literal::Unit)
        };
        emitter.change(Change::Delete, signatures.view_call.clone(), args.clone());
        let row = emitter.call(signatures.values_call, vec![var(canonical), carried]);
        emitter.set(signatures.view_call.clone(), args, row);

        emitter.finish_rule(
            body,
            self.common.name,
            self.common.ruleset,
            RuleEvalMode::Naive,
            true,
        )
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

    /// Rebuild rules that keep a view canonical: one rule per rebuildable child
    /// column (a canonical column has no `@UF` row, so the rule simply doesn't
    /// match), plus a rule for the FD view's value column. A stale eq-sort column is
    /// replaced by its `@UF` leader, a stale container by its rebuilt value.
    ///
    /// A child update re-keys the row (`set` at the canonicalized children, then
    /// `delete`); a collision on the new key runs the view's `:merge`. The value
    /// column is canonicalized by [`Self::fd_custom_value_rebuild_rule_direct`]. In
    /// proof mode each rule composes the updated view proof.
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

        if output_is_eclass {
            // Covered by the index rule above, which indexes the e-class column too.
        } else if fdecl.subtype == FunctionSubtype::Custom && !fdecl.internal_let {
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

    /// The rebuild rule for one child eq-sort, driven by an `@UF_<S>` edge joined
    /// against that sort's declared index.
    ///
    /// The index reaches every row mentioning the moved term — at any child
    /// position or at the e-class — by lookup rather than by matching the view,
    /// and its atom binds the whole row, so nothing else need be read. The action
    /// then re-canonicalizes *every* eq-sort column with `uf_canon`, so one firing
    /// yields the fully canonical row. Two children moving in the same iteration
    /// therefore fire twice with the same result, rather than each producing a
    /// differently half-rewritten row for a later pass to merge.
    ///
    /// `uf_canon` reads `@UF_<S>` in the action, which is what makes the rule
    /// `:unsafe-seminaive` (or `:naive` under the test knob); the driving `@UF`
    /// delta in the body is what makes that read sound.
    ///
    /// In proof mode a firing writes one packed-proof row, or none at all when
    /// nothing was canonicalized and the view's output is not an e-class.
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

    /// One rule that canonicalizes a custom function's stale eq-sort output, at
    /// child index `out_idx`: chase the output's `@UF` edge, `delete` the stale
    /// row first so the re-`set` inserts without re-running the user merge, and in
    /// proof mode rewrite the row proof's output child by `Congr` at that position.
    ///
    /// A view whose value *is* an e-class needs no rule of its own — the whole-row
    /// rebuild canonicalizes that column too (see [`Self::indexed_rebuild_rule_direct`]).
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

    /// [`Self::fd_custom_value_rebuild_rule_direct`] for an eq-container output:
    /// containers have no `@UF` to chase, so the value canonicalizes via the
    /// container rebuild primitive (`:naive` — it reads `@UF` tables the rule
    /// doesn't join on).
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
