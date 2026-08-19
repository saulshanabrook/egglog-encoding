//! Maintenance-rule generation for the term/proof encoding: the rebuild rules
//! that keep each function's view and subsumed tables canonical, plus the rule
//! that executes a requested subsumption. (`@UF` path compression stays in
//! [`super::proof_encoding`].)

use super::proof_encoding::{ProofInstrumentor, ViewIndex};
use super::proof_encoding_helpers::{DROP_REFLEXIVE_STEP, Skeleton};
use crate::proofs::generated_binder::{
    CheckedRuleBuilder, FunctionKey, FunctionRef, GeneratedEntry, GeneratedRule,
    GeneratedSignatureCatalog, SortKey, SortRef, SortSemanticClass, ValueShape, ValuesRef,
    build_checked_rule,
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

#[derive(Clone)]
struct SubsumptionSignatures {
    input_keys: Vec<SortKey>,
    carried_key: SortKey,
    marker: String,
}

impl SubsumptionSignatures {
    /// Register the marker's shared inputs and carried sort in one rule scope.
    /// `between` inserts the apply-only output sort before Unit and Proof.
    fn register_checked<'id, Extra>(
        &self,
        builder: &mut CheckedRuleBuilder<'_, 'id>,
        between: impl FnOnce(&mut CheckedRuleBuilder<'_, 'id>) -> Extra,
    ) -> (
        (Vec<SortRef<'id>>, Extra),
        [SortRef<'id>; 2],
        FunctionRef<'id>,
    ) {
        let input_sorts = self
            .input_keys
            .iter()
            .cloned()
            .map(|key| builder.sort(key))
            .collect();
        let extra = between(builder);
        let unit_key = SortKey::from_sort(&crate::sort::literal_sort(&Literal::Unit));
        let unit_sort = builder.sort(unit_key.clone());
        let carried_sort = if self.carried_key == unit_key {
            unit_sort
        } else {
            builder.sort(self.carried_key.clone())
        };
        let marker_call = builder.function(FunctionKey {
            name: self.marker.clone(),
            subtype: FunctionSubtype::Custom,
            inputs: self.input_keys.clone(),
            output: ValueShape::Scalar(unit_key),
        });
        ((input_sorts, extra), [carried_sort, unit_sort], marker_call)
    }
}

impl SubsumptionRuleSpec {
    fn build(self, catalog: &mut GeneratedSignatureCatalog) -> Vec<GeneratedRule> {
        let Self {
            span,
            function,
            proof_sort,
            proofs_enabled,
            marker,
            view,
            apply_name,
            apply_value,
            apply_proof,
            subsume_ruleset: subsume_rules,
            rebuilding_ruleset: rebuild_rules,
            rekeys,
        } = self;
        let output_key = SortKey::from_sort(function.output());
        let signatures = SubsumptionSignatures {
            input_keys: function.input.iter().map(SortKey::from_sort).collect(),
            carried_key: if proofs_enabled {
                SortKey {
                    name: proof_sort,
                    class: SortSemanticClass::Eq,
                }
            } else {
                SortKey::from_sort(&crate::sort::literal_sort(&Literal::Unit))
            },
            marker,
        };
        assert!(
            rekeys.iter().map(|rekey| rekey.position).eq(signatures
                .input_keys
                .iter()
                .enumerate()
                .filter_map(
                    |(position, key)| (key.class == SortSemanticClass::Eq).then_some(position)
                )),
            "invalid generated semantic emission: subsumption rekey plan mismatch at {span}"
        );

        // The frontend observes all key variables in the marker atom first,
        // followed by the view's value and proof tuple.
        let apply_signatures = signatures.clone();
        let apply = build_checked_rule(
            catalog,
            &span,
            (apply_name, subsume_rules, RuleEvalMode::Seminaive, false),
            move |builder| {
                let ((input_sorts, output_sort), [carried_sort, _], marker_call) = apply_signatures
                    .register_checked(builder, |builder| builder.sort(output_key.clone()));
                let view_call = builder.function(FunctionKey {
                    name: view,
                    subtype: FunctionSubtype::Custom,
                    inputs: apply_signatures.input_keys.clone(),
                    output: ValueShape::Tuple(vec![
                        output_key,
                        apply_signatures.carried_key.clone(),
                    ]),
                });
                let view_values = builder.values([output_sort, carried_sort]);
                let children = input_sorts
                    .iter()
                    .enumerate()
                    .map(|(index, &sort)| builder.local(format!("c{index}_"), sort))
                    .collect::<Vec<_>>();
                let value = builder.local(apply_value, output_sort);
                let proof = builder.local(apply_proof, carried_sort);
                let args = children.clone();
                let marker = builder.apply(marker_call, args.clone());
                builder.fact(marker);
                let row = builder.apply(view_values, [value, proof]);
                let view = builder.apply(view_call, args.clone());
                builder.eq(row, view);
                builder.change(Change::Subsume, view_call, args);
            },
        );
        let mut rules = vec![apply];

        for rekey in rekeys {
            let SubsumeRekeyRuleSpec {
                position,
                leader,
                proof,
                uf,
                name,
            } = rekey;
            let eq_key = signatures.input_keys[position].clone();
            let rule_signatures = signatures.clone();
            let metadata = (name, rebuild_rules.clone(), RuleEvalMode::Seminaive, true);
            let direct = build_checked_rule(catalog, &span, metadata, move |builder| {
                let ((input_sorts, _), [carried_sort, unit_sort], marker_call) =
                    rule_signatures.register_checked(builder, |_| ());
                let eq_sort = input_sorts[position];
                let uf_call = builder.function(FunctionKey {
                    name: uf,
                    subtype: FunctionSubtype::Custom,
                    inputs: vec![eq_key.clone()],
                    output: ValueShape::Tuple(vec![eq_key, rule_signatures.carried_key.clone()]),
                });
                let not_equal_call = builder.primitive("!=", [eq_sort, eq_sort], unit_sort);
                let uf_values = builder.values([eq_sort, carried_sort]);

                // Each re-key rule has its own local scope: children in
                // lexical key order, then the selected column's leader
                // and unused UF proof.
                let children = input_sorts
                    .iter()
                    .enumerate()
                    .map(|(index, &sort)| builder.local(format!("c{index}_"), sort))
                    .collect::<Vec<_>>();
                let leader = builder.local(leader, eq_sort);
                let proof = builder.local(proof, carried_sort);
                let old_args = children.clone();
                let mut updated_args = old_args.clone();
                updated_args[position] = leader;
                let selected = children[position];
                let marker = builder.apply(marker_call, old_args.clone());
                builder.fact(marker);
                let uf_row = builder.apply(uf_values, [leader, proof]);
                let uf = builder.apply(uf_call, [selected]);
                builder.eq(uf_row, uf);
                let unequal = builder.apply(not_equal_call, [selected, leader]);
                builder.fact(unequal);
                let unit = builder.lit(Literal::Unit);
                builder.set(marker_call, updated_args, unit);
                builder.change(Change::Delete, marker_call, old_args);
            });
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

struct CheckedRebuildSignatures<'id> {
    input_sorts: Vec<SortRef<'id>>,
    output_key: SortKey,
    output_sort: SortRef<'id>,
    carried_key: SortKey,
    carried_sort: SortRef<'id>,
    unit_sort: SortRef<'id>,
    view_call: FunctionRef<'id>,
    values_call: ValuesRef<'id>,
}

impl RebuildRuleCommonSpec {
    /// Register the signatures every FD-view rebuild shares in the current
    /// checked scope. Children are keys and the value is the
    /// `(output, Proof|Unit)` pair carried by the source view.
    fn register_checked<'id>(
        builder: &mut CheckedRuleBuilder<'_, 'id>,
        input_keys: Vec<SortKey>,
        output_key: SortKey,
        proof_sort: String,
        proofs_enabled: bool,
        view: String,
    ) -> CheckedRebuildSignatures<'id> {
        let unit_key = SortKey {
            name: "Unit".to_owned(),
            class: SortSemanticClass::Value,
        };
        let carried_key = if proofs_enabled {
            SortKey {
                name: proof_sort,
                class: SortSemanticClass::Eq,
            }
        } else {
            unit_key.clone()
        };
        let input_sorts = input_keys
            .iter()
            .cloned()
            .map(|sort| builder.sort(sort))
            .collect::<Vec<_>>();
        let output_sort = builder.sort(output_key.clone());
        let unit_sort = builder.sort(unit_key);
        let carried_sort = if proofs_enabled {
            builder.sort(carried_key.clone())
        } else {
            unit_sort
        };
        let view_call = builder.function(FunctionKey {
            name: view,
            subtype: FunctionSubtype::Custom,
            inputs: input_keys.clone(),
            output: ValueShape::Tuple(vec![output_key.clone(), carried_key.clone()]),
        });
        let values_call = builder.values([output_sort, carried_sort]);
        CheckedRebuildSignatures {
            input_sorts,
            output_key,
            output_sort,
            carried_key,
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
        let RebuildRuleCommonSpec {
            span,
            function,
            proof_sort,
            proofs_enabled,
            view,
            name,
            ruleset,
        } = self.common;
        let input_keys = function
            .input
            .iter()
            .map(SortKey::from_sort)
            .collect::<Vec<_>>();
        let output_key = SortKey::from_sort(function.output());
        assert!(
            self.keys.len() == input_keys.len()
                && self.position < input_keys.len()
                && input_keys[self.position].class == SortSemanticClass::EqContainer
                && self.proof.is_some() == proofs_enabled,
            "invalid generated semantic emission: container-key rebuild plan mismatch at {span}"
        );
        if let Some(proof) = &self.proof {
            assert!(
                proof.index == self.position
                    && proof.view_proof == self.view_proof
                    && proof.container == self.keys[self.position],
                "invalid generated semantic emission: container-key proof plan mismatch at {span}"
            );
        }
        let metadata = (name, ruleset, RuleEvalMode::Naive, true);
        build_checked_rule(catalog, &span, metadata, move |builder| {
            let signatures = RebuildRuleCommonSpec::register_checked(
                builder,
                input_keys,
                output_key,
                proof_sort,
                proofs_enabled,
                view,
            );
            let key_sort = signatures.input_sorts[self.position];
            let rebuild_call = builder.primitive(self.value_primitive, [key_sort], key_sort);
            let not_equal_call =
                builder.primitive("!=", [key_sort, key_sort], signatures.unit_sort);

            // The view tuple is observed before its key arguments; the canonical
            // value is first introduced by the second body equality.
            let value = builder.local(self.value, signatures.output_sort);
            let view_proof = builder.local(self.view_proof, signatures.carried_sort);
            let keys = self
                .keys
                .into_iter()
                .zip(signatures.input_sorts.iter().copied())
                .map(|(name, sort)| builder.local(name, sort))
                .collect::<Vec<_>>();
            let canonical = builder.local(self.canonical, key_sort);
            let old_args = keys.clone();
            let mut updated_args = old_args.clone();
            updated_args[self.position] = canonical;
            let selected = keys[self.position];
            let view_row = builder.apply(signatures.values_call, [value, view_proof]);
            let view = builder.apply(signatures.view_call, old_args.clone());
            builder.eq(view_row, view);
            let rebuilt = builder.apply(rebuild_call, [selected]);
            builder.eq(canonical, rebuilt);
            let unequal = builder.apply(not_equal_call, [selected, canonical]);
            builder.fact(unequal);

            let carried = if let Some(proof) = self.proof {
                let i64_sort = builder.sort(SortKey {
                    name: "i64".to_owned(),
                    class: SortSemanticClass::Value,
                });
                let projection_call = builder.primitive(
                    crate::proofs::proof_fresh::mint_prim_name(&proof.projection_constructor),
                    [signatures.carried_sort, i64_sort],
                    signatures.carried_sort,
                );
                let rebuild_proof_call = builder.primitive(
                    proof.rebuild_primitive,
                    [key_sort, signatures.carried_sort],
                    signatures.carried_sort,
                );
                let congruence_call = builder.primitive(
                    crate::proofs::proof_fresh::mint_prim_name(&proof.congruence_constructor),
                    [signatures.carried_sort, i64_sort, signatures.carried_sort],
                    signatures.carried_sort,
                );
                let position = builder.lit(Literal::Int(proof.index as i64));
                let anchor_value = builder.apply(projection_call, [view_proof, position]);
                let anchor = builder.bind(proof.anchor, anchor_value);
                let rebuild_value = builder.apply(rebuild_proof_call, [selected, anchor]);
                let rebuild_proof = builder.bind(proof.rebuild_proof, rebuild_value);
                let result_value =
                    builder.apply(congruence_call, [view_proof, position, rebuild_proof]);
                builder.bind(proof.result, result_value)
            } else {
                builder.lit(Literal::Unit)
            };
            // Re-keying must insert first: on a collision the view merge observes
            // the replacement before the stale key is removed.
            let row = builder.apply(signatures.values_call, [value, carried]);
            builder.set(signatures.view_call, updated_args, row);
            builder.change(Change::Delete, signatures.view_call, old_args);
        })
    }
}

#[derive(Clone)]
struct IndexedCanonicalStepSpec {
    position: usize,
    sort: ArcSort,
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
        let RebuildRuleCommonSpec {
            span,
            function,
            proof_sort,
            proofs_enabled,
            view,
            name,
            ruleset,
        } = self.common;
        let input_keys: Vec<_> = function.input.iter().map(SortKey::from_sort).collect();
        let output_key = SortKey::from_sort(function.output());
        let index_sort_key = SortKey::from_sort(&self.index_sort);
        assert!(
            self.keys.len() == input_keys.len()
                && index_sort_key.class == SortSemanticClass::Eq
                && index_sort_key.name == self.index.sort_name,
            "invalid generated semantic emission: indexed rebuild key or index sort mismatch at {span}"
        );
        for step in &self.children {
            assert!(
                step.position < input_keys.len()
                    && SortKey::from_sort(&step.sort) == input_keys[step.position]
                    && step.proof_step.is_some() == proofs_enabled,
                "invalid generated semantic emission: indexed rebuild child plan mismatch at {span}"
            );
        }
        if let Some(step) = &self.output {
            assert!(
                step.position == input_keys.len()
                    && SortKey::from_sort(&step.sort) == output_key
                    && step.proof_step.is_some() == proofs_enabled,
                "invalid generated semantic emission: indexed rebuild output plan mismatch at {span}"
            );
        }
        let step_count = self.children.len() + usize::from(self.output.is_some());
        assert_eq!(
            self.packed.as_ref().map(|packed| packed.narrowed.len()),
            (proofs_enabled && step_count > 0).then_some(step_count),
            "invalid generated semantic emission: indexed rebuild packed or narrowed proof count disagrees with proof mode at {span}"
        );
        let metadata = (name, ruleset, self.eval_mode, true);
        build_checked_rule(catalog, &span, metadata, move |builder| {
            // Recreate common handles in this scope before assembly.
            let input_sorts: Vec<_> = input_keys
                .iter()
                .cloned()
                .map(|sort| builder.sort(sort))
                .collect();
            let output_sort = builder.sort(output_key.clone());
            let unit_key = SortKey {
                name: "Unit".to_owned(),
                class: SortSemanticClass::Value,
            };
            let unit_sort = builder.sort(unit_key.clone());
            let (carried_key, carried_sort) = if proofs_enabled {
                let key = SortKey {
                    name: proof_sort,
                    class: SortSemanticClass::Eq,
                };
                (key.clone(), builder.sort(key))
            } else {
                (unit_key.clone(), unit_sort)
            };
            let view_values = builder.values([output_sort, carried_sort]);
            let view_call = builder.function(FunctionKey {
                name: view,
                subtype: FunctionSubtype::Custom,
                inputs: input_keys.clone(),
                output: ValueShape::Tuple(vec![output_key.clone(), carried_key.clone()]),
            });
            let index_sort = builder.sort(index_sort_key.clone());
            let uf_values = builder.values([index_sort, carried_sort]);
            let uf_call = builder.function(FunctionKey {
                name: self.uf,
                subtype: FunctionSubtype::Custom,
                inputs: vec![index_sort_key.clone()],
                output: ValueShape::Tuple(vec![index_sort_key.clone(), carried_key.clone()]),
            });
            let not_equal_call = builder.primitive("!=", [index_sort, index_sort], unit_sort);
            let mut index_inputs = vec![index_sort_key];
            index_inputs.extend(input_keys.iter().cloned());
            index_inputs.extend([output_key.clone(), carried_key]);
            let index_call = builder.function(FunctionKey {
                name: self.index.name,
                subtype: FunctionSubtype::Custom,
                inputs: index_inputs,
                output: ValueShape::Scalar(unit_key),
            });

            // Bind leader/proof before follower, then the indexed row in column order.
            let leader = builder.local(self.leader, index_sort);
            let leader_proof = builder.local(self.leader_proof, carried_sort);
            let follower = builder.local(self.follower, index_sort);
            let keys = self
                .keys
                .into_iter()
                .zip(input_sorts.iter().copied())
                .map(|(name, sort)| builder.local(name, sort))
                .collect::<Vec<_>>();
            let value = builder.local(self.value, output_sort);
            let row_proof = builder.local(self.row_proof, carried_sort);
            let mut index_args = vec![follower];
            index_args.extend(keys.iter().copied());
            index_args.extend([value, row_proof]);
            let uf_row = builder.apply(uf_values, [leader, leader_proof]);
            let uf_value = builder.apply(uf_call, [follower]);
            builder.eq(uf_row, uf_value);
            let unequal = builder.apply(not_equal_call, [follower, leader]);
            builder.fact(unequal);
            let index_value = builder.apply(index_call, index_args);
            builder.fact(index_value);

            let mut updated_args = keys.clone();
            let mut moved = Vec::new();
            let mut step_proofs = Vec::new();
            for step in self.children {
                let sort = input_sorts[step.position];
                let value_call = builder.primitive(step.value_primitive, [sort, sort], sort);
                let before = keys[step.position];
                let canonical_value = builder.apply(value_call, [before, before]);
                let canonical = builder.bind(step.canonical, canonical_value);
                if let Some((proof_name, proof_primitive)) = step.proof_step {
                    let proof_call =
                        builder.primitive(proof_primitive, [sort, carried_sort], carried_sort);
                    let proof_value = builder.apply(proof_call, [before, row_proof]);
                    let proof = builder.bind(proof_name, proof_value);
                    step_proofs.push(proof);
                    moved.push((sort, before, canonical));
                }
                updated_args[step.position] = canonical;
            }

            let mut updated_value = value;
            if let Some(step) = self.output {
                let sort = output_sort;
                let value_call = builder.primitive(step.value_primitive, [sort, sort], sort);
                let canonical_value = builder.apply(value_call, [value, value]);
                let canonical = builder.bind(step.canonical, canonical_value);
                if let Some((proof_name, proof_primitive)) = step.proof_step {
                    let proof_call =
                        builder.primitive(proof_primitive, [sort, carried_sort], carried_sort);
                    let proof_value = builder.apply(proof_call, [value, row_proof]);
                    let proof = builder.bind(proof_name, proof_value);
                    step_proofs.push(proof);
                    moved.push((sort, value, canonical));
                }
                updated_value = canonical;
            }

            let carried = if let Some(packed) = self.packed {
                let string_sort = builder.sort(SortKey {
                    name: "String".to_owned(),
                    class: SortSemanticClass::Value,
                });
                let i64_sort = builder.sort(SortKey {
                    name: "i64".to_owned(),
                    class: SortSemanticClass::Value,
                });
                let mut spelling = builder.lit(Literal::String(packed.skeleton));
                for (column, (result, (sort, before, after))) in
                    packed.narrowed.into_iter().zip(moved).enumerate()
                {
                    let drop_call = builder.primitive(
                        DROP_REFLEXIVE_STEP,
                        [string_sort, i64_sort, sort, sort],
                        string_sort,
                    );
                    let position = builder.lit(Literal::Int((column + 1) as i64));
                    let narrowed = builder.apply(drop_call, [spelling, position, before, after]);
                    spelling = builder.bind(result, narrowed);
                }
                let mut mint_inputs = vec![string_sort];
                mint_inputs.extend(std::iter::repeat_n(carried_sort, 1 + step_proofs.len()));
                let packed_call = builder.primitive(
                    crate::proofs::proof_fresh::mint_prim_name(&packed.constructor),
                    mint_inputs,
                    carried_sort,
                );
                let mut args = vec![spelling, row_proof];
                args.extend(step_proofs);
                let result = builder.apply(packed_call, args);
                builder.bind(packed.result, result)
            } else if proofs_enabled {
                row_proof
            } else {
                builder.lit(Literal::Unit)
            };

            // Whole-row rebuilds alone delete first: an e-class-only move
            // leaves the key unchanged, so replacement must come second.
            builder.change(Change::Delete, view_call, keys);
            let row = builder.apply(view_values, [updated_value, carried]);
            builder.set(view_call, updated_args, row);
        })
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
        let RebuildRuleCommonSpec {
            span,
            function,
            proof_sort,
            proofs_enabled,
            view,
            name,
            ruleset,
        } = self.common;
        let input_keys = function
            .input
            .iter()
            .map(SortKey::from_sort)
            .collect::<Vec<_>>();
        let output_key = SortKey::from_sort(function.output());
        assert!(
            self.keys.len() == input_keys.len()
                && output_key.class == SortSemanticClass::Eq
                && self.proof.is_some() == proofs_enabled,
            "invalid generated semantic emission: direct-output rebuild plan mismatch at {span}"
        );
        if let Some(proof) = &self.proof {
            assert!(
                proof.index == input_keys.len()
                    && proof.view_proof == self.view_proof
                    && proof.equality_proof == self.equality_proof,
                "invalid generated semantic emission: direct-output proof plan mismatch at {span}"
            );
        }
        let metadata = (name, ruleset, RuleEvalMode::Seminaive, true);
        build_checked_rule(catalog, &span, metadata, move |builder| {
            let signatures = RebuildRuleCommonSpec::register_checked(
                builder,
                input_keys,
                output_key,
                proof_sort,
                proofs_enabled,
                view,
            );
            let uf_call = builder.function(FunctionKey {
                name: self.uf,
                subtype: FunctionSubtype::Custom,
                inputs: vec![signatures.output_key.clone()],
                output: ValueShape::Tuple(vec![
                    signatures.output_key.clone(),
                    signatures.carried_key.clone(),
                ]),
            });
            let uf_values = builder.values([signatures.output_sort, signatures.carried_sort]);
            let not_equal_call = builder.primitive(
                "!=",
                [signatures.output_sort, signatures.output_sort],
                signatures.unit_sort,
            );

            let value = builder.local(self.value, signatures.output_sort);
            let view_proof = builder.local(self.view_proof, signatures.carried_sort);
            let keys = self
                .keys
                .into_iter()
                .zip(signatures.input_sorts.iter().copied())
                .map(|(name, sort)| builder.local(name, sort))
                .collect::<Vec<_>>();
            let canonical = builder.local(self.canonical, signatures.output_sort);
            let equality_proof = builder.local(self.equality_proof, signatures.carried_sort);
            let args = keys.clone();
            let view_row = builder.apply(signatures.values_call, [value, view_proof]);
            let view = builder.apply(signatures.view_call, args.clone());
            builder.eq(view_row, view);
            let uf_row = builder.apply(uf_values, [canonical, equality_proof]);
            let uf = builder.apply(uf_call, [value]);
            builder.eq(uf_row, uf);
            let unequal = builder.apply(not_equal_call, [value, canonical]);
            builder.fact(unequal);

            let carried = if let Some(proof) = self.proof {
                let i64_sort = builder.sort(SortKey {
                    name: "i64".to_owned(),
                    class: SortSemanticClass::Value,
                });
                let congruence_call = builder.primitive(
                    crate::proofs::proof_fresh::mint_prim_name(&proof.constructor),
                    [signatures.carried_sort, i64_sort, signatures.carried_sort],
                    signatures.carried_sort,
                );
                let position = builder.lit(Literal::Int(proof.index as i64));
                let result_value =
                    builder.apply(congruence_call, [view_proof, position, equality_proof]);
                builder.bind(proof.result, result_value)
            } else {
                builder.lit(Literal::Unit)
            };
            // Delete first so this maintenance rewrite cannot re-run the custom
            // view merge against the stale value it is replacing.
            builder.change(Change::Delete, signatures.view_call, args.clone());
            let row = builder.apply(signatures.values_call, [canonical, carried]);
            builder.set(signatures.view_call, args, row);
        })
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
        let RebuildRuleCommonSpec {
            span,
            function,
            proof_sort,
            proofs_enabled,
            view,
            name,
            ruleset,
        } = self.common;
        let input_keys = function
            .input
            .iter()
            .map(SortKey::from_sort)
            .collect::<Vec<_>>();
        let output_key = SortKey::from_sort(function.output());
        assert!(
            self.keys.len() == input_keys.len()
                && self.position == input_keys.len()
                && output_key.class == SortSemanticClass::EqContainer
                && self.proof.is_some() == proofs_enabled,
            "invalid generated semantic emission: container-output rebuild plan mismatch at {span}"
        );
        if let Some(proof) = &self.proof {
            assert!(
                proof.index == self.position
                    && proof.view_proof == self.view_proof
                    && proof.container == self.value,
                "invalid generated semantic emission: container-output proof plan mismatch at {span}"
            );
        }
        let metadata = (name, ruleset, RuleEvalMode::Naive, true);
        build_checked_rule(catalog, &span, metadata, move |builder| {
            let signatures = RebuildRuleCommonSpec::register_checked(
                builder,
                input_keys,
                output_key,
                proof_sort,
                proofs_enabled,
                view,
            );
            let rebuild_call = builder.primitive(
                self.value_primitive,
                [signatures.output_sort],
                signatures.output_sort,
            );
            let not_equal_call = builder.primitive(
                "!=",
                [signatures.output_sort, signatures.output_sort],
                signatures.unit_sort,
            );

            let value = builder.local(self.value, signatures.output_sort);
            let view_proof = builder.local(self.view_proof, signatures.carried_sort);
            let keys = self
                .keys
                .into_iter()
                .zip(signatures.input_sorts.iter().copied())
                .map(|(name, sort)| builder.local(name, sort))
                .collect::<Vec<_>>();
            let canonical = builder.local(self.canonical, signatures.output_sort);
            let args = keys.clone();
            let view_row = builder.apply(signatures.values_call, [value, view_proof]);
            let view = builder.apply(signatures.view_call, args.clone());
            builder.eq(view_row, view);
            let rebuilt = builder.apply(rebuild_call, [value]);
            builder.eq(canonical, rebuilt);
            let unequal = builder.apply(not_equal_call, [value, canonical]);
            builder.fact(unequal);

            let carried = if let Some(proof) = self.proof {
                let i64_sort = builder.sort(SortKey {
                    name: "i64".to_owned(),
                    class: SortSemanticClass::Value,
                });
                let projection_call = builder.primitive(
                    crate::proofs::proof_fresh::mint_prim_name(&proof.projection_constructor),
                    [signatures.carried_sort, i64_sort],
                    signatures.carried_sort,
                );
                let rebuild_proof_call = builder.primitive(
                    proof.rebuild_primitive,
                    [signatures.output_sort, signatures.carried_sort],
                    signatures.carried_sort,
                );
                let congruence_call = builder.primitive(
                    crate::proofs::proof_fresh::mint_prim_name(&proof.congruence_constructor),
                    [signatures.carried_sort, i64_sort, signatures.carried_sort],
                    signatures.carried_sort,
                );
                let position = builder.lit(Literal::Int(proof.index as i64));
                let anchor_value = builder.apply(projection_call, [view_proof, position]);
                let anchor = builder.bind(proof.anchor, anchor_value);
                let rebuild_value = builder.apply(rebuild_proof_call, [value, anchor]);
                let rebuild_proof = builder.bind(proof.rebuild_proof, rebuild_value);
                let result_value =
                    builder.apply(congruence_call, [view_proof, position, rebuild_proof]);
                builder.bind(proof.result, result_value)
            } else {
                builder.lit(Literal::Unit)
            };
            builder.change(Change::Delete, signatures.view_call, args.clone());
            let row = builder.apply(signatures.values_call, [canonical, carried]);
            builder.set(signatures.view_call, args, row);
        })
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

#[cfg(test)]
mod checked_builder_tests {
    use std::panic::{AssertUnwindSafe, catch_unwind};
    use std::sync::Arc;

    use super::*;
    use crate::ast::{GenericActions, GenericFact, GenericRule};
    use crate::proofs::generated_binder::{
        CallKey, GeneratedExpr, GeneratedVar, GeneratedVarRole, LocalId, PrimitiveKey,
    };

    fn expr_shape(expression: &GeneratedExpr, span: &Span) -> String {
        let expression_span = match expression {
            GenericExpr::Lit(actual, _)
            | GenericExpr::Var(actual, _)
            | GenericExpr::Call(actual, _, _) => actual,
        };
        assert_eq!(expression_span, span);
        match expression {
            GenericExpr::Var(_, variable) => format!("v{}", variable.id.0),
            GenericExpr::Lit(_, Literal::Int(value)) => format!("int:{value}"),
            GenericExpr::Lit(_, Literal::Unit) => "unit".to_owned(),
            GenericExpr::Lit(_, literal) => format!("lit:{literal:?}"),
            GenericExpr::Call(_, head, args) => {
                let head = match head {
                    CallKey::Function(function) => format!("fn:{}", function.name),
                    CallKey::Primitive(primitive) => format!("prim:{}", primitive.name),
                    CallKey::Values(_) => "values".to_owned(),
                };
                let args = args
                    .iter()
                    .map(|arg| expr_shape(arg, span))
                    .collect::<Vec<_>>()
                    .join(",");
                format!("{head}({args})")
            }
        }
    }

    fn rule_shape(rule: &GeneratedRule, span: &Span) -> String {
        assert_eq!(&rule.span, span);
        let mut locals = std::collections::BTreeMap::new();
        for fact in &rule.body {
            fact.visit_vars(&mut |_, variable| {
                locals.insert(
                    variable.id.0,
                    format!(
                        "v{}:{}:{}:{:?}",
                        variable.id.0, variable.name, variable.sort.name, variable.sort.class
                    ),
                );
            });
        }
        for action in &rule.head.0 {
            if let GenericAction::Let(_, variable, _) = action {
                locals.insert(
                    variable.id.0,
                    format!(
                        "v{}:{}:{}:{:?}",
                        variable.id.0, variable.name, variable.sort.name, variable.sort.class
                    ),
                );
            }
        }
        let body = rule
            .body
            .iter()
            .map(|fact| match fact {
                GenericFact::Eq(actual, left, right) => {
                    assert_eq!(actual, span);
                    format!("eq({},{})", expr_shape(left, span), expr_shape(right, span))
                }
                GenericFact::Fact(expression) => format!("fact({})", expr_shape(expression, span)),
            })
            .collect::<Vec<_>>()
            .join(";");
        let head = rule
            .head
            .0
            .iter()
            .map(|action| match action {
                GenericAction::Let(actual, variable, value) => {
                    assert_eq!(actual, span);
                    format!("let v{}={}", variable.id.0, expr_shape(value, span))
                }
                GenericAction::Set(actual, function, args, value) => {
                    assert_eq!(actual, span);
                    let CallKey::Function(function) = function else {
                        panic!("set target must be a function")
                    };
                    let args = args
                        .iter()
                        .map(|arg| expr_shape(arg, span))
                        .collect::<Vec<_>>()
                        .join(",");
                    format!(
                        "set fn:{}({args})={}",
                        function.name,
                        expr_shape(value, span)
                    )
                }
                GenericAction::Change(actual, change, function, args) => {
                    assert_eq!(actual, span);
                    let CallKey::Function(function) = function else {
                        panic!("change target must be a function")
                    };
                    let args = args
                        .iter()
                        .map(|arg| expr_shape(arg, span))
                        .collect::<Vec<_>>()
                        .join(",");
                    let change = match change {
                        Change::Delete => "delete",
                        Change::Subsume => "subsume",
                    };
                    format!("{change} fn:{}({args})", function.name)
                }
                action => panic!("unexpected generated rebuild action: {action:?}"),
            })
            .collect::<Vec<_>>()
            .join(";");
        format!(
            "name={};ruleset={};eval={:?};no_decomp={};include={}\nlocals=[{}]\nbody=[{body}]\nhead=[{head}]",
            rule.name,
            rule.ruleset,
            rule.eval_mode,
            rule.no_decomp,
            rule.include_subsumed,
            locals.into_values().collect::<Vec<_>>().join(",")
        )
    }

    fn subsumption_plan(
        span: &Span,
        label: &str,
        input: Vec<ArcSort>,
        proofs_enabled: bool,
    ) -> SubsumptionRuleSpec {
        let rekeys = input
            .iter()
            .enumerate()
            .filter(|(_, sort)| sort.is_eq_sort())
            .map(|(position, sort)| SubsumeRekeyRuleSpec {
                position,
                leader: format!("c{position}_leader_"),
                proof: format!("proof{position}"),
                uf: format!("UF-{}", sort.name()),
                name: format!("rekey-{label}-{position}"),
            })
            .collect();
        SubsumptionRuleSpec {
            span: span.clone(),
            function: FuncType {
                name: label.to_owned(),
                subtype: FunctionSubtype::Custom,
                input,
                outputs: vec![crate::sort::literal_sort(&Literal::Int(0))],
            },
            proof_sort: "Proof".to_owned(),
            proofs_enabled,
            marker: format!("{label}-subsumed"),
            view: format!("{label}-view"),
            apply_name: format!("apply-{label}"),
            apply_value: "value".to_owned(),
            apply_proof: "row-proof".to_owned(),
            subsume_ruleset: "subsume-rules".to_owned(),
            rebuilding_ruleset: "rebuild-rules".to_owned(),
            rekeys,
        }
    }

    #[test]
    fn subsumption_rules_pin_mixed_arity_proof_and_term_structures() {
        let span = crate::span!();
        let eq = |name: &str| -> ArcSort {
            Arc::new(crate::sort::EqSort {
                name: name.to_owned(),
            })
        };
        let i64_sort = crate::sort::literal_sort(&Literal::Int(0));
        let cases = [
            (
                subsumption_plan(
                    &span,
                    "proof",
                    vec![eq("E"), i64_sort.clone(), eq("K")],
                    true,
                ),
                vec![
                    "name=apply-proof;ruleset=subsume-rules;eval=Seminaive;no_decomp=false;include=false\n\
                     locals=[v0:c0_:E:Eq,v1:c1_:i64:Value,v2:c2_:K:Eq,v3:value:i64:Value,v4:row-proof:Proof:Eq]\n\
                     body=[fact(fn:proof-subsumed(v0,v1,v2));eq(values(v3,v4),fn:proof-view(v0,v1,v2))]\n\
                     head=[subsume fn:proof-view(v0,v1,v2)]",
                    "name=rekey-proof-0;ruleset=rebuild-rules;eval=Seminaive;no_decomp=false;include=true\n\
                     locals=[v0:c0_:E:Eq,v1:c1_:i64:Value,v2:c2_:K:Eq,v3:c0_leader_:E:Eq,v4:proof0:Proof:Eq]\n\
                     body=[fact(fn:proof-subsumed(v0,v1,v2));eq(values(v3,v4),fn:UF-E(v0));fact(prim:!=(v0,v3))]\n\
                     head=[set fn:proof-subsumed(v3,v1,v2)=unit;delete fn:proof-subsumed(v0,v1,v2)]",
                    "name=rekey-proof-2;ruleset=rebuild-rules;eval=Seminaive;no_decomp=false;include=true\n\
                     locals=[v0:c0_:E:Eq,v1:c1_:i64:Value,v2:c2_:K:Eq,v3:c2_leader_:K:Eq,v4:proof2:Proof:Eq]\n\
                     body=[fact(fn:proof-subsumed(v0,v1,v2));eq(values(v3,v4),fn:UF-K(v2));fact(prim:!=(v2,v3))]\n\
                     head=[set fn:proof-subsumed(v0,v1,v3)=unit;delete fn:proof-subsumed(v0,v1,v2)]",
                ],
            ),
            (
                subsumption_plan(&span, "term", vec![eq("K")], false),
                vec![
                    "name=apply-term;ruleset=subsume-rules;eval=Seminaive;no_decomp=false;include=false\n\
                     locals=[v0:c0_:K:Eq,v1:value:i64:Value,v2:row-proof:Unit:Value]\n\
                     body=[fact(fn:term-subsumed(v0));eq(values(v1,v2),fn:term-view(v0))]\n\
                     head=[subsume fn:term-view(v0)]",
                    "name=rekey-term-0;ruleset=rebuild-rules;eval=Seminaive;no_decomp=false;include=true\n\
                     locals=[v0:c0_:K:Eq,v1:c0_leader_:K:Eq,v2:proof0:Unit:Value]\n\
                     body=[fact(fn:term-subsumed(v0));eq(values(v1,v2),fn:UF-K(v0));fact(prim:!=(v0,v1))]\n\
                     head=[set fn:term-subsumed(v1)=unit;delete fn:term-subsumed(v0)]",
                ],
            ),
            (
                subsumption_plan(&span, "apply-only", vec![i64_sort], false),
                vec![
                    "name=apply-apply-only;ruleset=subsume-rules;eval=Seminaive;no_decomp=false;include=false\n\
                     locals=[v0:c0_:i64:Value,v1:value:i64:Value,v2:row-proof:Unit:Value]\n\
                     body=[fact(fn:apply-only-subsumed(v0));eq(values(v1,v2),fn:apply-only-view(v0))]\n\
                     head=[subsume fn:apply-only-view(v0)]",
                ],
            ),
        ];
        for (plan, expected) in cases {
            let rules = plan.build(&mut GeneratedSignatureCatalog::default());
            assert_eq!(
                rules
                    .iter()
                    .map(|rule| rule_shape(rule, &span))
                    .collect::<Vec<_>>(),
                expected
            );
        }

        let edits: [fn(&mut SubsumptionRuleSpec); 5] = [
            |plan| {
                plan.rekeys.pop();
            },
            |plan| plan.rekeys[1].position = 0,
            |plan| plan.rekeys.swap(0, 1),
            |plan| plan.rekeys[0].position = usize::MAX,
            |plan| plan.rekeys[0].position = 1,
        ];
        for edit in edits {
            let mut plan = subsumption_plan(
                &span,
                "rejected",
                vec![
                    eq("E"),
                    crate::sort::literal_sort(&Literal::Int(0)),
                    eq("K"),
                ],
                true,
            );
            edit(&mut plan);
            let mut catalog = GeneratedSignatureCatalog::default();
            let before = format!("{catalog:?}");
            let panic = catch_unwind(AssertUnwindSafe(|| plan.build(&mut catalog)))
                .expect_err("incoherent subsumption plan must panic");
            let message = panic
                .downcast_ref::<String>()
                .cloned()
                .or_else(|| {
                    panic
                        .downcast_ref::<&str>()
                        .map(|message| (*message).to_owned())
                })
                .expect("subsumption-plan panic must contain text");
            assert!(message.contains("subsumption rekey plan mismatch"));
            assert!(message.contains(&span.to_string()));
            assert_eq!(format!("{catalog:?}"), before, "catalog mutated");
        }
    }

    fn indexed_plan(span: &Span, proofs_enabled: bool) -> IndexedWholeRowRebuildSpec {
        let e: ArcSort = Arc::new(crate::sort::EqSort {
            name: "E".to_owned(),
        });
        IndexedWholeRowRebuildSpec {
            common: RebuildRuleCommonSpec {
                span: span.clone(),
                function: FuncType {
                    name: "F".to_owned(),
                    subtype: FunctionSubtype::Custom,
                    input: vec![e.clone()],
                    outputs: vec![e.clone()],
                },
                proof_sort: "Proof".to_owned(),
                proofs_enabled,
                view: "FView".to_owned(),
                name: "rebuild".to_owned(),
                ruleset: "rebuild-rules".to_owned(),
            },
            index: ViewIndex {
                name: "FIndex".to_owned(),
                sort_name: "E".to_owned(),
            },
            index_sort: e.clone(),
            uf: "UF-E".to_owned(),
            follower: "follower".to_owned(),
            leader: "leader".to_owned(),
            leader_proof: "leader-proof".to_owned(),
            keys: vec!["key".to_owned()],
            value: "value".to_owned(),
            row_proof: "row-proof".to_owned(),
            children: vec![IndexedCanonicalStepSpec {
                position: 0,
                sort: e.clone(),
                canonical: "canonical-key".to_owned(),
                value_primitive: "canonicalize-key".to_owned(),
                proof_step: proofs_enabled
                    .then(|| ("proof-key".to_owned(), "prove-key".to_owned())),
            }],
            output: Some(IndexedCanonicalStepSpec {
                position: 1,
                sort: e,
                canonical: "canonical-value".to_owned(),
                value_primitive: "canonicalize-value".to_owned(),
                proof_step: proofs_enabled
                    .then(|| ("proof-value".to_owned(), "prove-value".to_owned())),
            }),
            packed: proofs_enabled.then(|| IndexedPackedProofSpec {
                skeleton: "(. (.))".to_owned(),
                narrowed: vec!["narrow-key".to_owned(), "narrow-value".to_owned()],
                constructor: "Packed".to_owned(),
                result: "packed".to_owned(),
            }),
            eval_mode: RuleEvalMode::UnsafeSeminaive,
        }
    }

    fn rejected_plan(
        span: &Span,
        proofs_enabled: bool,
        expected: &str,
        edit: impl FnOnce(&mut IndexedWholeRowRebuildSpec),
    ) {
        let mut spec = indexed_plan(span, proofs_enabled);
        edit(&mut spec);
        let mut catalog = GeneratedSignatureCatalog::default();
        let panic = catch_unwind(AssertUnwindSafe(|| spec.build(&mut catalog)))
            .expect_err("incoherent indexed rebuild plan must panic");
        let message = panic
            .downcast_ref::<String>()
            .cloned()
            .or_else(|| {
                panic
                    .downcast_ref::<&str>()
                    .map(|message| (*message).to_owned())
            })
            .expect("indexed rebuild panic must contain text");
        assert!(message.contains(expected), "unexpected panic: {message}");
        assert!(
            message.contains(&span.to_string()),
            "missing span: {message}"
        );
    }

    #[test]
    fn indexed_whole_row_checked_builder_pins_proof_and_term_structures() {
        let span = crate::span!();
        let e: ArcSort = Arc::new(crate::sort::EqSort {
            name: "E".to_owned(),
        });
        let i64_sort = crate::sort::literal_sort(&Literal::Int(0));
        let e_key = SortKey::from_sort(&e);
        let i64_key = SortKey::from_sort(&i64_sort);
        let unit_key = SortKey {
            name: "Unit".to_owned(),
            class: SortSemanticClass::Value,
        };
        let proof_key = SortKey {
            name: "Proof".to_owned(),
            class: SortSemanticClass::Eq,
        };
        let mut catalog = GeneratedSignatureCatalog::default();
        let proof_rule = IndexedWholeRowRebuildSpec {
            common: RebuildRuleCommonSpec {
                span: span.clone(),
                function: FuncType {
                    name: "F".to_owned(),
                    subtype: FunctionSubtype::Custom,
                    input: vec![e.clone(), i64_sort.clone()],
                    outputs: vec![e.clone()],
                },
                proof_sort: "Proof".to_owned(),
                proofs_enabled: true,
                view: "FView".to_owned(),
                name: "rebuild-proof".to_owned(),
                ruleset: "rebuild-rules".to_owned(),
            },
            index: ViewIndex {
                name: "FIndex".to_owned(),
                sort_name: "E".to_owned(),
            },
            index_sort: e.clone(),
            uf: "UF-E".to_owned(),
            follower: "follower".to_owned(),
            leader: "leader".to_owned(),
            leader_proof: "leader-proof".to_owned(),
            keys: vec!["k0".to_owned(), "k1".to_owned()],
            value: "value".to_owned(),
            row_proof: "row-proof".to_owned(),
            children: vec![IndexedCanonicalStepSpec {
                position: 0,
                sort: e.clone(),
                canonical: "canonical-k0".to_owned(),
                value_primitive: "canonicalize-k0".to_owned(),
                proof_step: Some(("proof-k0".to_owned(), "prove-k0".to_owned())),
            }],
            output: Some(IndexedCanonicalStepSpec {
                position: 2,
                sort: e.clone(),
                canonical: "canonical-value".to_owned(),
                value_primitive: "canonicalize-value".to_owned(),
                proof_step: Some(("proof-value".to_owned(), "prove-value".to_owned())),
            }),
            packed: Some(IndexedPackedProofSpec {
                skeleton: "(. (.))".to_owned(),
                narrowed: vec!["narrow-1".to_owned(), "narrow-2".to_owned()],
                constructor: "Packed".to_owned(),
                result: "packed".to_owned(),
            }),
            eval_mode: RuleEvalMode::UnsafeSeminaive,
        }
        .build(&mut catalog);

        let local = |id, name: &str, sort: &SortKey| GeneratedVar {
            id: LocalId(id),
            name: name.to_owned(),
            sort: sort.clone(),
            role: GeneratedVarRole::Local,
        };
        let leader = local(0, "leader", &e_key);
        let leader_proof = local(1, "leader-proof", &proof_key);
        let follower = local(2, "follower", &e_key);
        let k0 = local(3, "k0", &e_key);
        let k1 = local(4, "k1", &i64_key);
        let value = local(5, "value", &e_key);
        let row_proof = local(6, "row-proof", &proof_key);
        let canonical_k0 = local(7, "canonical-k0", &e_key);
        let proof_k0 = local(8, "proof-k0", &proof_key);
        let canonical_value = local(9, "canonical-value", &e_key);
        let proof_value = local(10, "proof-value", &proof_key);
        let narrow_1 = local(
            11,
            "narrow-1",
            &SortKey {
                name: "String".to_owned(),
                class: SortSemanticClass::Value,
            },
        );
        let narrow_2 = local(
            12,
            "narrow-2",
            &SortKey {
                name: "String".to_owned(),
                class: SortSemanticClass::Value,
            },
        );
        let packed = local(13, "packed", &proof_key);
        let var = |variable: &GeneratedVar| GenericExpr::Var(span.clone(), variable.clone());
        let call = |head, args| GenericExpr::Call(span.clone(), head, args);
        let view_values = CallKey::Values(vec![e_key.clone(), proof_key.clone()]);
        let view_call = CallKey::Function(FunctionKey {
            name: "FView".to_owned(),
            subtype: FunctionSubtype::Custom,
            inputs: vec![e_key.clone(), i64_key.clone()],
            output: ValueShape::Tuple(vec![e_key.clone(), proof_key.clone()]),
        });
        let uf_values = CallKey::Values(vec![e_key.clone(), proof_key.clone()]);
        let uf_call = CallKey::Function(FunctionKey {
            name: "UF-E".to_owned(),
            subtype: FunctionSubtype::Custom,
            inputs: vec![e_key.clone()],
            output: ValueShape::Tuple(vec![e_key.clone(), proof_key.clone()]),
        });
        let unequal = CallKey::Primitive(PrimitiveKey {
            name: "!=".to_owned(),
            inputs: vec![e_key.clone(), e_key.clone()],
            output: unit_key.clone(),
        });
        let index_call = CallKey::Function(FunctionKey {
            name: "FIndex".to_owned(),
            subtype: FunctionSubtype::Custom,
            inputs: vec![
                e_key.clone(),
                e_key.clone(),
                i64_key.clone(),
                e_key.clone(),
                proof_key.clone(),
            ],
            output: ValueShape::Scalar(unit_key.clone()),
        });
        let canonicalize_k0 = CallKey::Primitive(PrimitiveKey {
            name: "canonicalize-k0".to_owned(),
            inputs: vec![e_key.clone(), e_key.clone()],
            output: e_key.clone(),
        });
        let prove_k0 = CallKey::Primitive(PrimitiveKey {
            name: "prove-k0".to_owned(),
            inputs: vec![e_key.clone(), proof_key.clone()],
            output: proof_key.clone(),
        });
        let canonicalize_value = CallKey::Primitive(PrimitiveKey {
            name: "canonicalize-value".to_owned(),
            inputs: vec![e_key.clone(), e_key.clone()],
            output: e_key.clone(),
        });
        let prove_value = CallKey::Primitive(PrimitiveKey {
            name: "prove-value".to_owned(),
            inputs: vec![e_key.clone(), proof_key.clone()],
            output: proof_key.clone(),
        });
        let drop_reflexive = CallKey::Primitive(PrimitiveKey {
            name: DROP_REFLEXIVE_STEP.to_owned(),
            inputs: vec![
                SortKey {
                    name: "String".to_owned(),
                    class: SortSemanticClass::Value,
                },
                i64_key.clone(),
                e_key.clone(),
                e_key.clone(),
            ],
            output: SortKey {
                name: "String".to_owned(),
                class: SortSemanticClass::Value,
            },
        });
        let mint = CallKey::Primitive(PrimitiveKey {
            name: crate::proofs::proof_fresh::mint_prim_name("Packed"),
            inputs: vec![
                SortKey {
                    name: "String".to_owned(),
                    class: SortSemanticClass::Value,
                },
                proof_key.clone(),
                proof_key.clone(),
                proof_key.clone(),
            ],
            output: proof_key.clone(),
        });
        assert_eq!(
            proof_rule,
            GenericRule {
                span: span.clone(),
                body: vec![
                    GenericFact::Eq(
                        span.clone(),
                        call(uf_values, vec![var(&leader), var(&leader_proof)],),
                        call(uf_call, vec![var(&follower)]),
                    ),
                    GenericFact::Fact(call(unequal, vec![var(&follower), var(&leader)],)),
                    GenericFact::Fact(call(
                        index_call,
                        vec![
                            var(&follower),
                            var(&k0),
                            var(&k1),
                            var(&value),
                            var(&row_proof),
                        ],
                    )),
                ],
                head: GenericActions(vec![
                    GenericAction::Let(
                        span.clone(),
                        canonical_k0.clone(),
                        call(canonicalize_k0, vec![var(&k0), var(&k0)],),
                    ),
                    GenericAction::Let(
                        span.clone(),
                        proof_k0.clone(),
                        call(prove_k0, vec![var(&k0), var(&row_proof)]),
                    ),
                    GenericAction::Let(
                        span.clone(),
                        canonical_value.clone(),
                        call(canonicalize_value, vec![var(&value), var(&value)],),
                    ),
                    GenericAction::Let(
                        span.clone(),
                        proof_value.clone(),
                        call(prove_value, vec![var(&value), var(&row_proof)]),
                    ),
                    GenericAction::Let(
                        span.clone(),
                        narrow_1.clone(),
                        call(
                            drop_reflexive.clone(),
                            vec![
                                GenericExpr::Lit(
                                    span.clone(),
                                    Literal::String("(. (.))".to_owned()),
                                ),
                                GenericExpr::Lit(span.clone(), Literal::Int(1)),
                                var(&k0),
                                var(&canonical_k0),
                            ],
                        ),
                    ),
                    GenericAction::Let(
                        span.clone(),
                        narrow_2.clone(),
                        call(
                            drop_reflexive,
                            vec![
                                var(&narrow_1),
                                GenericExpr::Lit(span.clone(), Literal::Int(2)),
                                var(&value),
                                var(&canonical_value),
                            ],
                        ),
                    ),
                    GenericAction::Let(
                        span.clone(),
                        packed.clone(),
                        call(
                            mint,
                            vec![
                                var(&narrow_2),
                                var(&row_proof),
                                var(&proof_k0),
                                var(&proof_value),
                            ],
                        ),
                    ),
                    GenericAction::Change(
                        span.clone(),
                        Change::Delete,
                        view_call.clone(),
                        vec![var(&k0), var(&k1)],
                    ),
                    GenericAction::Set(
                        span.clone(),
                        view_call,
                        vec![var(&canonical_k0), var(&k1)],
                        call(view_values, vec![var(&canonical_value), var(&packed)],),
                    ),
                ]),
                name: "rebuild-proof".to_owned(),
                ruleset: "rebuild-rules".to_owned(),
                eval_mode: RuleEvalMode::UnsafeSeminaive,
                no_decomp: false,
                include_subsumed: true,
            }
        );

        let mut catalog = GeneratedSignatureCatalog::default();
        let term_rule = IndexedWholeRowRebuildSpec {
            common: RebuildRuleCommonSpec {
                span: span.clone(),
                function: FuncType {
                    name: "T".to_owned(),
                    subtype: FunctionSubtype::Custom,
                    input: vec![e.clone()],
                    outputs: vec![i64_sort.clone()],
                },
                proof_sort: "unused-proof".to_owned(),
                proofs_enabled: false,
                view: "TView".to_owned(),
                name: "rebuild-term".to_owned(),
                ruleset: "rebuild-rules".to_owned(),
            },
            index: ViewIndex {
                name: "TIndex".to_owned(),
                sort_name: "E".to_owned(),
            },
            index_sort: e.clone(),
            uf: "UF-E-term".to_owned(),
            follower: "follower".to_owned(),
            leader: "leader".to_owned(),
            leader_proof: "leader-proof".to_owned(),
            keys: vec!["k0".to_owned()],
            value: "value".to_owned(),
            row_proof: "row-proof".to_owned(),
            children: vec![IndexedCanonicalStepSpec {
                position: 0,
                sort: e,
                canonical: "canonical-k0".to_owned(),
                value_primitive: "canonicalize-k0".to_owned(),
                proof_step: None,
            }],
            output: None,
            packed: None,
            eval_mode: RuleEvalMode::Naive,
        }
        .build(&mut catalog);
        let leader = local(0, "leader", &e_key);
        let leader_proof = local(1, "leader-proof", &unit_key);
        let follower = local(2, "follower", &e_key);
        let k0 = local(3, "k0", &e_key);
        let value = local(4, "value", &i64_key);
        let row_proof = local(5, "row-proof", &unit_key);
        let canonical_k0 = local(6, "canonical-k0", &e_key);
        let view_values = CallKey::Values(vec![i64_key.clone(), unit_key.clone()]);
        let view_call = CallKey::Function(FunctionKey {
            name: "TView".to_owned(),
            subtype: FunctionSubtype::Custom,
            inputs: vec![e_key.clone()],
            output: ValueShape::Tuple(vec![i64_key.clone(), unit_key.clone()]),
        });
        assert_eq!(
            term_rule,
            GenericRule {
                span: span.clone(),
                body: vec![
                    GenericFact::Eq(
                        span.clone(),
                        call(
                            CallKey::Values(vec![e_key.clone(), unit_key.clone()]),
                            vec![var(&leader), var(&leader_proof)],
                        ),
                        call(
                            CallKey::Function(FunctionKey {
                                name: "UF-E-term".to_owned(),
                                subtype: FunctionSubtype::Custom,
                                inputs: vec![e_key.clone()],
                                output: ValueShape::Tuple(vec![e_key.clone(), unit_key.clone(),]),
                            }),
                            vec![var(&follower)],
                        ),
                    ),
                    GenericFact::Fact(call(
                        CallKey::Primitive(PrimitiveKey {
                            name: "!=".to_owned(),
                            inputs: vec![e_key.clone(), e_key.clone()],
                            output: unit_key.clone(),
                        }),
                        vec![var(&follower), var(&leader)],
                    )),
                    GenericFact::Fact(call(
                        CallKey::Function(FunctionKey {
                            name: "TIndex".to_owned(),
                            subtype: FunctionSubtype::Custom,
                            inputs: vec![
                                e_key.clone(),
                                e_key.clone(),
                                i64_key.clone(),
                                unit_key.clone(),
                            ],
                            output: ValueShape::Scalar(unit_key.clone()),
                        }),
                        vec![var(&follower), var(&k0), var(&value), var(&row_proof)],
                    )),
                ],
                head: GenericActions(vec![
                    GenericAction::Let(
                        span.clone(),
                        canonical_k0.clone(),
                        call(
                            CallKey::Primitive(PrimitiveKey {
                                name: "canonicalize-k0".to_owned(),
                                inputs: vec![e_key.clone(), e_key.clone()],
                                output: e_key.clone(),
                            }),
                            vec![var(&k0), var(&k0)],
                        ),
                    ),
                    GenericAction::Change(
                        span.clone(),
                        Change::Delete,
                        view_call.clone(),
                        vec![var(&k0)],
                    ),
                    GenericAction::Set(
                        span.clone(),
                        view_call,
                        vec![var(&canonical_k0)],
                        call(
                            view_values,
                            vec![var(&value), GenericExpr::Lit(span.clone(), Literal::Unit),],
                        ),
                    ),
                ]),
                name: "rebuild-term".to_owned(),
                ruleset: "rebuild-rules".to_owned(),
                eval_mode: RuleEvalMode::Naive,
                no_decomp: false,
                include_subsumed: true,
            }
        );
    }

    #[test]
    fn remaining_rebuild_checked_builders_pin_structures_and_reject_incoherence() {
        let span = crate::span!();
        let mut egraph = EGraph::default();
        egraph
            .parse_and_run_program(None, "(datatype E (Mk)) (sort Container (Vec E))")
            .unwrap();
        let types = &egraph.type_info;
        let e = types.get_sort_by_name("E").unwrap().clone();
        let container = types.get_sort_by_name("Container").unwrap().clone();
        let i64_sort = crate::sort::literal_sort(&Literal::Int(0));
        let common = |family: &str, input: Vec<ArcSort>, output: ArcSort, proofs_enabled: bool| {
            let mode = if proofs_enabled { "proof" } else { "term" };
            RebuildRuleCommonSpec {
                span: span.clone(),
                function: FuncType {
                    name: format!("{family}-source"),
                    subtype: FunctionSubtype::Custom,
                    input,
                    outputs: vec![output],
                },
                proof_sort: "Proof".to_owned(),
                proofs_enabled,
                view: format!("{family}-{mode}-view"),
                name: format!("{family}-{mode}"),
                ruleset: "rebuild-rules".to_owned(),
            }
        };
        let container_proof =
            |view_proof: &str, index: usize, container: &str| ContainerRebuildProofPlan {
                view_proof: view_proof.to_owned(),
                index,
                container: container.to_owned(),
                projection_constructor: "Proj".to_owned(),
                rebuild_primitive: "prove-container".to_owned(),
                congruence_constructor: "Congr".to_owned(),
                rebuild_proof: "rebuild-proof".to_owned(),
                anchor: "anchor".to_owned(),
                result: "result".to_owned(),
            };
        let key_plan = |proofs_enabled| EqContainerKeyRebuildSpec {
            common: common(
                "key",
                vec![i64_sort.clone(), container.clone()],
                i64_sort.clone(),
                proofs_enabled,
            ),
            position: 1,
            keys: vec!["key".to_owned(), "container".to_owned()],
            value: "value".to_owned(),
            view_proof: "view-proof".to_owned(),
            canonical: "canonical".to_owned(),
            value_primitive: "rebuild-container".to_owned(),
            proof: proofs_enabled.then(|| container_proof("view-proof", 1, "container")),
        };
        let direct_plan = |proofs_enabled| CustomDirectOutputRebuildSpec {
            common: common("direct", vec![i64_sort.clone()], e.clone(), proofs_enabled),
            keys: vec!["key".to_owned()],
            value: "value".to_owned(),
            view_proof: "view-proof".to_owned(),
            canonical: "canonical".to_owned(),
            equality_proof: "equality-proof".to_owned(),
            uf: "UF-E".to_owned(),
            proof: proofs_enabled.then(|| CongruenceProofPlan {
                view_proof: "view-proof".to_owned(),
                index: 1,
                equality_proof: "equality-proof".to_owned(),
                constructor: "Congr".to_owned(),
                result: "result".to_owned(),
            }),
        };
        let output_plan = |proofs_enabled| CustomContainerOutputRebuildSpec {
            common: common(
                "output",
                vec![i64_sort.clone()],
                container.clone(),
                proofs_enabled,
            ),
            position: 1,
            keys: vec!["key".to_owned()],
            value: "value".to_owned(),
            view_proof: "view-proof".to_owned(),
            canonical: "canonical".to_owned(),
            value_primitive: "rebuild-container".to_owned(),
            proof: proofs_enabled.then(|| container_proof("view-proof", 1, "value")),
        };

        let projection = crate::proofs::proof_fresh::mint_prim_name("Proj");
        let congruence = crate::proofs::proof_fresh::mint_prim_name("Congr");
        let cases = [
            (
                key_plan(true).build(&mut GeneratedSignatureCatalog::default()),
                format!(
                    "name=key-proof;ruleset=rebuild-rules;eval=Naive;no_decomp=false;include=true\n\
                     locals=[v0:value:i64:Value,v1:view-proof:Proof:Eq,v2:key:i64:Value,v3:container:Container:EqContainer,v4:canonical:Container:EqContainer,v5:anchor:Proof:Eq,v6:rebuild-proof:Proof:Eq,v7:result:Proof:Eq]\n\
                     body=[eq(values(v0,v1),fn:key-proof-view(v2,v3));eq(v4,prim:rebuild-container(v3));fact(prim:!=(v3,v4))]\n\
                     head=[let v5=prim:{projection}(v1,int:1);let v6=prim:prove-container(v3,v5);let v7=prim:{congruence}(v1,int:1,v6);set fn:key-proof-view(v2,v4)=values(v0,v7);delete fn:key-proof-view(v2,v3)]"
                ),
            ),
            (
                key_plan(false).build(&mut GeneratedSignatureCatalog::default()),
                "name=key-term;ruleset=rebuild-rules;eval=Naive;no_decomp=false;include=true\n\
                 locals=[v0:value:i64:Value,v1:view-proof:Unit:Value,v2:key:i64:Value,v3:container:Container:EqContainer,v4:canonical:Container:EqContainer]\n\
                 body=[eq(values(v0,v1),fn:key-term-view(v2,v3));eq(v4,prim:rebuild-container(v3));fact(prim:!=(v3,v4))]\n\
                 head=[set fn:key-term-view(v2,v4)=values(v0,unit);delete fn:key-term-view(v2,v3)]"
                    .to_owned(),
            ),
            (
                direct_plan(true).build(&mut GeneratedSignatureCatalog::default()),
                format!(
                    "name=direct-proof;ruleset=rebuild-rules;eval=Seminaive;no_decomp=false;include=true\n\
                     locals=[v0:value:E:Eq,v1:view-proof:Proof:Eq,v2:key:i64:Value,v3:canonical:E:Eq,v4:equality-proof:Proof:Eq,v5:result:Proof:Eq]\n\
                     body=[eq(values(v0,v1),fn:direct-proof-view(v2));eq(values(v3,v4),fn:UF-E(v0));fact(prim:!=(v0,v3))]\n\
                     head=[let v5=prim:{congruence}(v1,int:1,v4);delete fn:direct-proof-view(v2);set fn:direct-proof-view(v2)=values(v3,v5)]"
                ),
            ),
            (
                direct_plan(false).build(&mut GeneratedSignatureCatalog::default()),
                "name=direct-term;ruleset=rebuild-rules;eval=Seminaive;no_decomp=false;include=true\n\
                 locals=[v0:value:E:Eq,v1:view-proof:Unit:Value,v2:key:i64:Value,v3:canonical:E:Eq,v4:equality-proof:Unit:Value]\n\
                 body=[eq(values(v0,v1),fn:direct-term-view(v2));eq(values(v3,v4),fn:UF-E(v0));fact(prim:!=(v0,v3))]\n\
                 head=[delete fn:direct-term-view(v2);set fn:direct-term-view(v2)=values(v3,unit)]"
                    .to_owned(),
            ),
            (
                output_plan(true).build(&mut GeneratedSignatureCatalog::default()),
                format!(
                    "name=output-proof;ruleset=rebuild-rules;eval=Naive;no_decomp=false;include=true\n\
                     locals=[v0:value:Container:EqContainer,v1:view-proof:Proof:Eq,v2:key:i64:Value,v3:canonical:Container:EqContainer,v4:anchor:Proof:Eq,v5:rebuild-proof:Proof:Eq,v6:result:Proof:Eq]\n\
                     body=[eq(values(v0,v1),fn:output-proof-view(v2));eq(v3,prim:rebuild-container(v0));fact(prim:!=(v0,v3))]\n\
                     head=[let v4=prim:{projection}(v1,int:1);let v5=prim:prove-container(v0,v4);let v6=prim:{congruence}(v1,int:1,v5);delete fn:output-proof-view(v2);set fn:output-proof-view(v2)=values(v3,v6)]"
                ),
            ),
            (
                output_plan(false).build(&mut GeneratedSignatureCatalog::default()),
                "name=output-term;ruleset=rebuild-rules;eval=Naive;no_decomp=false;include=true\n\
                 locals=[v0:value:Container:EqContainer,v1:view-proof:Unit:Value,v2:key:i64:Value,v3:canonical:Container:EqContainer]\n\
                 body=[eq(values(v0,v1),fn:output-term-view(v2));eq(v3,prim:rebuild-container(v0));fact(prim:!=(v0,v3))]\n\
                 head=[delete fn:output-term-view(v2);set fn:output-term-view(v2)=values(v3,unit)]"
                    .to_owned(),
            ),
        ];
        for (rule, expected) in cases {
            assert_eq!(rule_shape(&rule, &span), expected);
        }

        enum RejectedPlan {
            Key(bool, fn(&mut EqContainerKeyRebuildSpec)),
            Direct(bool, fn(&mut CustomDirectOutputRebuildSpec)),
            Output(bool, fn(&mut CustomContainerOutputRebuildSpec)),
        }
        use RejectedPlan::{Direct, Key, Output};
        let rejected = [
            Key(false, |p| p.keys.clear()),
            Key(false, |p| p.position = usize::MAX),
            Key(false, |p| p.position = 0),
            Key(false, |p| p.common.proofs_enabled = false),
            Key(true, |p| p.proof.as_mut().unwrap().index = 0),
            Key(true, |p| p.proof.as_mut().unwrap().view_proof.clear()),
            Key(true, |p| p.proof.as_mut().unwrap().container.clear()),
            Direct(false, |p| p.keys.clear()),
            Direct(false, |p| {
                p.common.function.outputs = p.common.function.input.clone()
            }),
            Direct(false, |p| p.common.proofs_enabled = false),
            Direct(true, |p| p.proof.as_mut().unwrap().index = 0),
            Direct(true, |p| p.proof.as_mut().unwrap().view_proof.clear()),
            Direct(true, |p| p.proof.as_mut().unwrap().equality_proof.clear()),
            Output(false, |p| p.keys.clear()),
            Output(false, |p| p.position = 0),
            Output(false, |p| {
                p.common.function.outputs = p.common.function.input.clone()
            }),
            Output(false, |p| p.common.proofs_enabled = false),
            Output(true, |p| p.proof.as_mut().unwrap().index = 0),
            Output(true, |p| p.proof.as_mut().unwrap().view_proof.clear()),
            Output(true, |p| p.proof.as_mut().unwrap().container.clear()),
        ];
        for rejected in rejected {
            let (family, proof_error) = match &rejected {
                Key(proof_error, _) => ("container-key", proof_error),
                Direct(proof_error, _) => ("direct-output", proof_error),
                Output(proof_error, _) => ("container-output", proof_error),
            };
            let phase = if *proof_error { "proof" } else { "rebuild" };
            let expected = format!("{family} {phase}");
            let mut catalog = GeneratedSignatureCatalog::default();
            let before = format!("{catalog:?}");
            let panic = catch_unwind(AssertUnwindSafe(|| match rejected {
                Key(_, edit) => {
                    let mut plan = key_plan(true);
                    edit(&mut plan);
                    plan.build(&mut catalog);
                }
                Direct(_, edit) => {
                    let mut plan = direct_plan(true);
                    edit(&mut plan);
                    plan.build(&mut catalog);
                }
                Output(_, edit) => {
                    let mut plan = output_plan(true);
                    edit(&mut plan);
                    plan.build(&mut catalog);
                }
            }))
            .expect_err("incoherent rebuild plan must panic");
            let message = panic
                .downcast_ref::<String>()
                .cloned()
                .or_else(|| {
                    panic
                        .downcast_ref::<&str>()
                        .map(|message| (*message).to_owned())
                })
                .expect("rebuild-plan panic must contain text");
            assert!(message.contains(&expected), "unexpected panic: {message}");
            assert!(
                message.contains(&span.to_string()),
                "missing span: {message}"
            );
            assert_eq!(format!("{catalog:?}"), before, "catalog mutated");
        }
    }

    #[test]
    fn indexed_whole_row_rejects_incoherent_producer_plans() {
        let span = crate::span!();
        let i64_sort = crate::sort::literal_sort(&Literal::Int(0));
        rejected_plan(&span, true, "key or index sort", |spec| {
            spec.keys.clear();
        });
        rejected_plan(&span, true, "key or index sort", |spec| {
            spec.index.sort_name = "i64".to_owned();
            spec.index_sort = i64_sort.clone();
        });
        rejected_plan(&span, true, "child plan", |spec| {
            spec.children[0].position = 1;
        });
        rejected_plan(&span, true, "child plan", |spec| {
            spec.children[0].sort = i64_sort.clone();
        });
        rejected_plan(&span, true, "child plan", |spec| {
            spec.children[0].proof_step = None;
        });
        rejected_plan(&span, true, "output plan", |spec| {
            spec.output.as_mut().unwrap().position = 0;
        });
        rejected_plan(&span, true, "output plan", |spec| {
            spec.output.as_mut().unwrap().sort = i64_sort.clone();
        });
        rejected_plan(&span, true, "output plan", |spec| {
            spec.output.as_mut().unwrap().proof_step = None;
        });
        rejected_plan(&span, true, "packed or narrowed", |spec| {
            spec.packed = None;
        });
        rejected_plan(&span, true, "packed or narrowed", |spec| {
            spec.packed.as_mut().unwrap().narrowed.pop();
        });
        rejected_plan(&span, false, "child plan", |spec| {
            spec.children[0].proof_step = Some(("proof".to_owned(), "prove".to_owned()));
        });
        rejected_plan(&span, false, "packed or narrowed", |spec| {
            spec.packed = Some(IndexedPackedProofSpec {
                skeleton: "()".to_owned(),
                narrowed: vec![],
                constructor: "Packed".to_owned(),
                result: "packed".to_owned(),
            });
        });
    }
}
