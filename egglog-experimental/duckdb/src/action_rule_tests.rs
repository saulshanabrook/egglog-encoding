//! Differential coverage for the exact native scalar 34-action rule family.

use std::collections::BTreeSet;

use anyhow::Result;
use egglog_ast::{
    core::{
        GenericAtom, GenericAtomTerm, GenericCoreAction, GenericCoreActions, GenericCoreRule, Query,
    },
    generic_ast::Change,
    span::Span,
};
use egglog_backend_trait::{
    Backend, BaseValueId, ColumnTy, DefaultVal, ExternalFunctionId, FunctionConfig, FunctionId,
    MergeAction, MergeFn, NativePrimitive, ReadMode, RuleActionCall, RuleBodyCall, RuleId,
    RuleSetRun, RuleSpec, RuleValue, RuleVar, Value,
};
use egglog_core_relations::Boxed;
use egglog_numeric_id::NumericId;
use ordered_float::OrderedFloat;

use crate::{EGraph, storage::sql_table};

type Term = GenericAtomTerm<RuleVar, RuleValue>;
type Action = GenericCoreAction<RuleActionCall, RuleVar, RuleValue>;

#[derive(Clone, Copy)]
struct ScalarTypes {
    unit: BaseValueId,
    string: BaseValueId,
}

#[derive(Clone, Copy)]
struct OrderedPrimitives {
    proof_min: ExternalFunctionId,
    proof_max: ExternalFunctionId,
    ordering_min: ExternalFunctionId,
    ordering_max: ExternalFunctionId,
    fresh: ExternalFunctionId,
}

struct Fixture<B> {
    backend: B,
    types: ScalarTypes,
    primitives: OrderedPrimitives,
    merge_label: Value,
    rule_label: Value,
    unit_value: Value,
    ast: FunctionId,
    sym: FunctionId,
    old: FunctionId,
    nil: FunctionId,
    trans: FunctionId,
    rule: FunctionId,
    cons: FunctionId,
    term: FunctionId,
    uf: FunctionId,
    view: FunctionId,
    key_count: usize,
}

impl<B: Backend> Fixture<B> {
    fn new(backend: B, prefix: &str) -> Result<Self> {
        Self::new_with_key_count(backend, prefix, 2)
    }

    fn new_with_key_count(backend: B, prefix: &str, key_count: usize) -> Result<Self> {
        Self::new_with_key_count_and_fake_token(backend, prefix, key_count, false)
    }

    fn new_with_fake_fresh_token(backend: B, prefix: &str) -> Result<Self> {
        Self::new_with_key_count_and_fake_token(backend, prefix, 2, true)
    }

    fn new_with_key_count_and_fake_token(
        mut backend: B,
        prefix: &str,
        key_count: usize,
        fake_fresh_token: bool,
    ) -> Result<Self> {
        let types = register_scalar_types(&mut backend);
        let merge_label = backend.base_values().get(Boxed::new(format!(
            "{prefix} merge label with 'quotes' and ; punctuation"
        )));
        let rule_label = backend.base_values().get(Boxed::new(format!(
            "{prefix} rule label '); DROP TABLE imaginary; --\nnext line"
        )));
        let unit_value = backend.base_values().get(());
        let mut primitives = register_ordered_primitives(&mut backend);
        if fake_fresh_token {
            primitives.fresh =
                backend.new_panic("non-fresh token must stay declarative".to_string());
        }

        // Deliberately register semantic roles in a non-program order. Native
        // admission and execution must use structure and FunctionId identity,
        // never generated names or a numeric-id pattern.
        let ast = assert_eq_unit_table(
            &mut backend,
            &format!("{prefix} shuffled ast role"),
            vec![ColumnTy::Id, ColumnTy::Id],
            types.unit,
        );
        let sym = assert_eq_unit_table(
            &mut backend,
            &format!("{prefix} shuffled sym role"),
            vec![ColumnTy::Id, ColumnTy::Id],
            types.unit,
        );
        let old = backend.add_table(FunctionConfig {
            schema: vec![ColumnTy::Id, ColumnTy::Id],
            n_vals: 1,
            n_identity_vals: None,
            default: DefaultVal::Fail,
            merge: MergeFn::Old,
            name: format!("{prefix} shuffled old lookup role"),
            can_subsume: false,
        });
        let nil = assert_eq_unit_table(
            &mut backend,
            &format!("{prefix} shuffled nil role"),
            vec![ColumnTy::Id],
            types.unit,
        );
        let trans = assert_eq_unit_table(
            &mut backend,
            &format!("{prefix} shuffled trans role"),
            vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Id],
            types.unit,
        );
        let rule = assert_eq_unit_table(
            &mut backend,
            &format!("{prefix} shuffled rule role"),
            vec![
                ColumnTy::Base(types.string),
                ColumnTy::Id,
                ColumnTy::Id,
                ColumnTy::Id,
                ColumnTy::Id,
            ],
            types.unit,
        );
        let cons = assert_eq_unit_table(
            &mut backend,
            &format!("{prefix} shuffled cons role"),
            vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Id],
            types.unit,
        );
        let term = assert_eq_unit_table(
            &mut backend,
            &format!("{prefix} shuffled term role"),
            vec![ColumnTy::Id; key_count + 1],
            types.unit,
        );

        let predicted_uf = backend.peek_next_function_id();
        let uf = backend.add_table(FunctionConfig {
            schema: vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Id],
            n_vals: 2,
            n_identity_vals: Some(1),
            default: DefaultVal::Fail,
            merge: ordered_union(
                primitives,
                merge_label,
                types,
                unit_value,
                sym,
                trans,
                predicted_uf,
                false,
            ),
            name: format!("{prefix} shuffled displaced owner role"),
            can_subsume: false,
        });
        assert_eq!(uf, predicted_uf);
        let view = backend.add_table(FunctionConfig {
            schema: vec![ColumnTy::Id; key_count + 2],
            n_vals: 2,
            n_identity_vals: Some(1),
            default: DefaultVal::Fail,
            merge: ordered_union(
                primitives,
                merge_label,
                types,
                unit_value,
                sym,
                trans,
                uf,
                true,
            ),
            name: format!("{prefix} selected body owner with hostile renaming"),
            can_subsume: true,
        });

        Ok(Self {
            backend,
            types,
            primitives,
            merge_label,
            rule_label,
            unit_value,
            ast,
            sym,
            old,
            nil,
            trans,
            rule,
            cons,
            term,
            uf,
            view,
            key_count,
        })
    }

    fn advance_fresh_to_100(&mut self) {
        for expected in 0..100 {
            assert_eq!(self.backend.fresh_id(), Value::new(expected));
        }
    }

    fn scalar_rule(&self, name: &str) -> RuleSpec {
        let string = ColumnTy::Base(self.types.string);
        let owner = binding(10, "matched opaque owner", ColumnTy::Id);
        let rewrite_owner = binding(11, "canonical rewrite owner", ColumnTy::Id);
        let view_proof = binding(20, "matched opaque view proof", ColumnTy::Id);
        let label = binding(31, "bound hostile label", string);
        let owner_proof = binding(41, "lookup proof", ColumnTy::Id);
        let f0 = binding(50, "fresh proof 00", ColumnTy::Id);
        let f1 = binding(60, "fresh proof 01", ColumnTy::Id);
        let f2 = binding(70, "fresh proof 02", ColumnTy::Id);
        let f3 = binding(80, "fresh proof 03", ColumnTy::Id);
        let proof_list = binding(90, "aliased proof list", ColumnTy::Id);
        let f4 = binding(100, "fresh term", ColumnTy::Id);
        let f5 = binding(110, "fresh lhs ast", ColumnTy::Id);
        let f6 = binding(120, "fresh rhs ast", ColumnTy::Id);
        let f7 = binding(130, "fresh first rule proof", ColumnTy::Id);
        let f8 = binding(140, "fresh owner ast", ColumnTy::Id);
        let f9 = binding(150, "fresh term ast", ColumnTy::Id);
        let f10 = binding(160, "fresh second rule proof", ColumnTy::Id);
        let f11 = binding(170, "fresh combined proof", ColumnTy::Id);
        let owner_alias = binding(180, "aliased guest owner", ColumnTy::Id);
        let f12 = binding(190, "fresh symmetric proof", ColumnTy::Id);
        let f13 = binding(200, "fresh final proof", ColumnTy::Id);
        let unit = || literal(self.unit_value, ColumnTy::Base(self.types.unit));
        let id = |value: u32| literal(Value::new(value), ColumnTy::Id);
        let fresh = |binding| {
            fresh_action(
                self.primitives.fresh,
                self.types.string,
                self.merge_label,
                binding,
            )
        };

        let body_keys = (0..self.key_count)
            .map(|index| id(u32::try_from(index).expect("test key index fits u32") + 1))
            .collect::<Vec<_>>();
        let constructed_keys = body_keys.iter().rev().cloned().collect::<Vec<_>>();
        let mut term_keys = constructed_keys.clone();
        term_keys.push(variable(f4.clone()));

        let actions = vec![
            // 00-09: label, Fail/Old lookup, then Sym/Trans/list proof.
            GenericCoreAction::LetAtomTerm(
                Span::Panic,
                label.clone(),
                literal(self.rule_label, string),
            ),
            GenericCoreAction::Let(
                Span::Panic,
                owner_proof.clone(),
                table_call(self.old, "renamed action-side old lookup"),
                vec![variable(rewrite_owner.clone())],
            ),
            fresh(f0.clone()),
            set_action(
                self.sym,
                vec![variable(owner_proof.clone()), variable(f0.clone())],
                vec![unit()],
            ),
            fresh(f1.clone()),
            set_action(
                self.trans,
                vec![
                    variable(f0.clone()),
                    variable(view_proof.clone()),
                    variable(f1.clone()),
                ],
                vec![unit()],
            ),
            fresh(f2.clone()),
            set_action(self.nil, vec![variable(f2.clone())], vec![unit()]),
            fresh(f3.clone()),
            set_action(
                self.cons,
                vec![
                    variable(f1.clone()),
                    variable(f2.clone()),
                    variable(f3.clone()),
                ],
                vec![unit()],
            ),
            // 10-19: proof-list alias, term/Ast/Rule constructors, then Old.
            GenericCoreAction::LetAtomTerm(Span::Panic, proof_list.clone(), variable(f3.clone())),
            fresh(f4.clone()),
            set_action(self.term, term_keys, vec![unit()]),
            fresh(f5.clone()),
            set_action(
                self.ast,
                vec![variable(f4.clone()), variable(f5.clone())],
                vec![unit()],
            ),
            fresh(f6.clone()),
            set_action(
                self.ast,
                vec![variable(f4.clone()), variable(f6.clone())],
                vec![unit()],
            ),
            fresh(f7.clone()),
            set_action(
                self.rule,
                vec![
                    variable(label.clone()),
                    variable(proof_list.clone()),
                    variable(f5.clone()),
                    variable(f6.clone()),
                    variable(f7.clone()),
                ],
                vec![unit()],
            ),
            set_action(
                self.old,
                vec![variable(f4.clone())],
                vec![variable(f7.clone())],
            ),
            // 20-28: owner/term Ast, second Rule, Trans, then reversed View.
            fresh(f8.clone()),
            set_action(
                self.ast,
                vec![variable(rewrite_owner.clone()), variable(f8.clone())],
                vec![unit()],
            ),
            fresh(f9.clone()),
            set_action(
                self.ast,
                vec![variable(f4.clone()), variable(f9.clone())],
                vec![unit()],
            ),
            fresh(f10.clone()),
            set_action(
                self.rule,
                vec![
                    variable(label),
                    variable(proof_list),
                    variable(f8),
                    variable(f9),
                    variable(f10.clone()),
                ],
                vec![unit()],
            ),
            fresh(f11.clone()),
            set_action(
                self.trans,
                vec![variable(f10), variable(f7.clone()), variable(f11.clone())],
                vec![unit()],
            ),
            set_action(
                self.view,
                constructed_keys,
                vec![variable(rewrite_owner.clone()), variable(f11.clone())],
            ),
            // 29-33 must remain ordinary actions before the queued View drains.
            GenericCoreAction::LetAtomTerm(
                Span::Panic,
                owner_alias,
                variable(rewrite_owner.clone()),
            ),
            fresh(f12.clone()),
            set_action(
                self.sym,
                vec![variable(f11), variable(f12.clone())],
                vec![unit()],
            ),
            fresh(f13.clone()),
            set_action(
                self.trans,
                vec![variable(f7), variable(f12), variable(f13)],
                vec![unit()],
            ),
        ];
        assert_eq!(actions.len(), 34);

        // Mirror core canonicalization: the eliminated body equality becomes a
        // leading owner alias, and every call-valued let is split into a call
        // binding plus an immediate passthrough alias.
        let mut lowered = Vec::with_capacity(50);
        lowered.push(GenericCoreAction::LetAtomTerm(
            Span::Panic,
            rewrite_owner,
            variable(owner.clone()),
        ));
        for (logical_ordinal, mut action) in actions.into_iter().enumerate() {
            if let GenericCoreAction::Let(_, call_binding, _, _) = &mut action {
                let final_binding = call_binding.clone();
                let temporary = binding(
                    1_000 + u32::try_from(logical_ordinal).expect("logical ordinal fits u32"),
                    &format!("lowered call temporary {logical_ordinal}"),
                    final_binding.ty,
                );
                *call_binding = temporary.clone();
                lowered.push(action);
                lowered.push(GenericCoreAction::LetAtomTerm(
                    Span::Panic,
                    final_binding,
                    variable(temporary),
                ));
            } else {
                lowered.push(action);
            }
        }
        assert_eq!(lowered.len(), 50);

        RuleSpec {
            name: name.to_string(),
            seminaive: true,
            no_decomp: false,
            core: GenericCoreRule {
                span: Span::Panic,
                body: Query {
                    atoms: vec![GenericAtom {
                        span: Span::Panic,
                        head: RuleBodyCall::Table {
                            id: self.view,
                            read: ReadMode::Live,
                        },
                        // Literal keys keep the differing-owner reverse row out
                        // of the match relation while action 28 still targets it.
                        args: body_keys
                            .into_iter()
                            .chain([variable(owner), variable(view_proof)])
                            .collect(),
                    }],
                },
                head: GenericCoreActions::new(lowered),
            },
        }
    }

    fn variable_key_rule(&self, name: &str) -> RuleSpec {
        assert_eq!(self.key_count, 2);
        let mut rule = self.scalar_rule(name);
        let first = binding(1, "first variable key", ColumnTy::Id);
        let second = binding(2, "second variable key", ColumnTy::Id);
        rule.core.body.atoms[0].args[0] = variable(first.clone());
        rule.core.body.atoms[0].args[1] = variable(second.clone());
        let GenericCoreAction::Set(_, _, term_keys, _) = &mut rule.core.head.0[19] else {
            unreachable!("exact lowered fixture action 19 is logical Term Set 12");
        };
        term_keys[0] = variable(second.clone());
        term_keys[1] = variable(first.clone());
        let GenericCoreAction::Set(_, _, view_keys, _) = &mut rule.core.head.0[42] else {
            unreachable!("exact lowered fixture action 42 is logical View Set 28");
        };
        view_keys[0] = variable(second);
        view_keys[1] = variable(first);
        rule
    }

    fn literal_key_rule(&self, name: &str, keys: [u32; 2]) -> RuleSpec {
        assert_eq!(self.key_count, 2);
        let mut rule = self.scalar_rule(name);
        let terms = keys.map(|key| literal(Value::new(key), ColumnTy::Id));
        rule.core.body.atoms[0].args[0] = terms[0].clone();
        rule.core.body.atoms[0].args[1] = terms[1].clone();
        let GenericCoreAction::Set(_, _, term_keys, _) = &mut rule.core.head.0[19] else {
            unreachable!("exact lowered fixture action 19 is logical Term Set 12");
        };
        term_keys[0] = terms[1].clone();
        term_keys[1] = terms[0].clone();
        let GenericCoreAction::Set(_, _, view_keys, _) = &mut rule.core.head.0[42] else {
            unreachable!("exact lowered fixture action 42 is logical View Set 28");
        };
        view_keys[0] = terms[1].clone();
        view_keys[1] = terms[0].clone();
        rule
    }
}

fn register_scalar_types(backend: &mut impl Backend) -> ScalarTypes {
    let unit = backend.base_values_mut().register_type::<()>();
    backend.base_values_mut().register_type::<bool>();
    backend.base_values_mut().register_type::<i64>();
    backend
        .base_values_mut()
        .register_type::<Boxed<OrderedFloat<f64>>>();
    let string = backend.base_values_mut().register_type::<Boxed<String>>();
    ScalarTypes { unit, string }
}

fn register_ordered_primitives(backend: &mut impl Backend) -> OrderedPrimitives {
    let proof_min = backend.register_native_primitive(NativePrimitive::SelectMinPayload);
    let proof_max = backend.register_native_primitive(NativePrimitive::SelectMaxPayload);
    let ordering_min = backend.register_native_primitive(NativePrimitive::OrderingMin);
    let ordering_max = backend.register_native_primitive(NativePrimitive::OrderingMax);
    let fresh = backend.register_get_fresh();
    OrderedPrimitives {
        proof_min,
        proof_max,
        ordering_min,
        ordering_max,
        fresh,
    }
}

fn assert_eq_unit_table(
    backend: &mut impl Backend,
    name: &str,
    mut keys: Vec<ColumnTy>,
    unit: BaseValueId,
) -> FunctionId {
    keys.push(ColumnTy::Base(unit));
    backend.add_table(FunctionConfig {
        schema: keys,
        n_vals: 1,
        n_identity_vals: None,
        default: DefaultVal::Fail,
        merge: MergeFn::AssertEq,
        name: name.to_string(),
        can_subsume: false,
    })
}

#[allow(clippy::too_many_arguments)]
fn ordered_union(
    primitives: OrderedPrimitives,
    label: Value,
    types: ScalarTypes,
    unit_value: Value,
    sym: FunctionId,
    trans: FunctionId,
    displaced: FunctionId,
    eclass_to_term: bool,
) -> MergeFn {
    let proof = |id, name: &str| MergeFn::Primitive {
        id,
        name: name.to_string(),
        input: vec![ColumnTy::Id; 4],
        output: ColumnTy::Id,
        args: vec![
            MergeFn::OldCol(0),
            MergeFn::OldCol(1),
            MergeFn::NewCol(0),
            MergeFn::NewCol(1),
        ],
    };
    let ordering = |id, name: &str| MergeFn::Primitive {
        id,
        name: name.to_string(),
        input: vec![ColumnTy::Id; 2],
        output: ColumnTy::Id,
        args: vec![MergeFn::OldCol(0), MergeFn::NewCol(0)],
    };
    let fresh = || MergeFn::Primitive {
        id: primitives.fresh,
        name: "renamed-scalar-merge-fresh".to_string(),
        input: vec![ColumnTy::Base(types.string)],
        output: ColumnTy::Id,
        args: vec![MergeFn::Const {
            value: label,
            ty: ColumnTy::Base(types.string),
        }],
    };
    let unit = || MergeFn::Const {
        value: unit_value,
        ty: ColumnTy::Base(types.unit),
    };
    let sym_input = if eclass_to_term { 1 } else { 0 };
    let (trans_first, trans_second) = if eclass_to_term { (0, 2) } else { (2, 1) };
    MergeFn::Block {
        actions: vec![
            MergeAction::Let {
                slot: 0,
                value: proof(primitives.proof_max, "renamed-scalar-select-max"),
            },
            MergeAction::Let {
                slot: 1,
                value: proof(primitives.proof_min, "renamed-scalar-select-min"),
            },
            MergeAction::Let {
                slot: 2,
                value: fresh(),
            },
            MergeAction::Set(
                sym,
                vec![MergeFn::LetVar(sym_input), MergeFn::LetVar(2), unit()],
            ),
            MergeAction::Let {
                slot: 3,
                value: fresh(),
            },
            MergeAction::Set(
                trans,
                vec![
                    MergeFn::LetVar(trans_first),
                    MergeFn::LetVar(trans_second),
                    MergeFn::LetVar(3),
                    unit(),
                ],
            ),
            MergeAction::Set(
                displaced,
                vec![
                    ordering(primitives.ordering_max, "renamed-scalar-ordering-max"),
                    ordering(primitives.ordering_min, "renamed-scalar-ordering-min"),
                    MergeFn::LetVar(3),
                ],
            ),
        ],
        result: Box::new(MergeFn::Columns(vec![
            ordering(primitives.ordering_min, "another-scalar-ordering-min"),
            MergeFn::LetVar(1),
        ])),
    }
}

fn binding(id: u32, name: &str, ty: ColumnTy) -> RuleVar {
    RuleVar {
        id,
        name: name.into(),
        ty,
    }
}

fn variable(binding: RuleVar) -> Term {
    GenericAtomTerm::Var(Span::Panic, binding)
}

fn literal(value: Value, ty: ColumnTy) -> Term {
    GenericAtomTerm::Literal(Span::Panic, RuleValue { value, ty })
}

fn table_call(id: FunctionId, name: &str) -> RuleActionCall {
    RuleActionCall::Table {
        id,
        name: name.into(),
    }
}

fn set_action(target: FunctionId, keys: Vec<Term>, values: Vec<Term>) -> Action {
    GenericCoreAction::Set(
        Span::Panic,
        table_call(target, "hostile diagnostic table name only"),
        keys,
        values,
    )
}

fn single_deferred_view_rule(old: FunctionId, view: FunctionId, name: &str) -> RuleSpec {
    let key = binding(910, "deferred key", ColumnTy::Id);
    let value = binding(911, "deferred value", ColumnTy::Id);
    RuleSpec {
        name: name.to_string(),
        seminaive: true,
        no_decomp: false,
        core: GenericCoreRule {
            span: Span::Panic,
            body: Query {
                atoms: vec![GenericAtom {
                    span: Span::Panic,
                    head: RuleBodyCall::Table {
                        id: old,
                        read: ReadMode::Live,
                    },
                    args: vec![variable(key.clone()), variable(value.clone())],
                }],
            },
            head: GenericCoreActions::new(vec![set_action(
                view,
                vec![variable(key.clone()), variable(value.clone())],
                vec![variable(key), variable(value)],
            )]),
        },
    }
}

fn fresh_action(
    token: ExternalFunctionId,
    string: BaseValueId,
    label: Value,
    binding: RuleVar,
) -> Action {
    GenericCoreAction::Let(
        Span::Panic,
        binding,
        RuleActionCall::Primitive {
            id: token,
            name: "renamed-scalar-head-fresh".into(),
            output: ColumnTy::Id,
        },
        vec![literal(label, ColumnTy::Base(string))],
    )
}

fn direct_canary_rule(fixture: &Fixture<EGraph>, name: &str) -> RuleSpec {
    let key = binding(900, "direct body key", ColumnTy::Id);
    let value = binding(901, "direct body value", ColumnTy::Id);
    RuleSpec {
        name: name.to_string(),
        seminaive: true,
        no_decomp: false,
        core: GenericCoreRule {
            span: Span::Panic,
            body: Query {
                atoms: vec![GenericAtom {
                    span: Span::Panic,
                    head: RuleBodyCall::Table {
                        id: fixture.old,
                        read: ReadMode::Live,
                    },
                    args: vec![variable(key.clone()), variable(value.clone())],
                }],
            },
            head: GenericCoreActions::new(vec![set_action(
                fixture.ast,
                vec![variable(key), variable(value)],
                vec![literal(
                    fixture.unit_value,
                    ColumnTy::Base(fixture.types.unit),
                )],
            )]),
        },
    }
}

fn selected_rejection(
    label: &str,
    mutate: impl FnOnce(&mut Fixture<EGraph>, &mut RuleSpec),
) -> Result<()> {
    let mut fixture = Fixture::new(EGraph::new()?, label)?;
    let mut invalid = fixture.scalar_rule(&format!("{label} invalid"));
    mutate(&mut fixture, &mut invalid);
    let error = fixture.backend.add_rule(invalid).unwrap_err();
    assert!(
        error.to_string().contains("scalar-mixed"),
        "{label} escaped selected admission: {error:#}"
    );
    assert_eq!(
        fixture
            .backend
            .add_rule(fixture.scalar_rule(&format!("{label} valid")))?,
        RuleId::new(0)
    );
    Ok(())
}

fn unselected_rejection(
    label: &str,
    mutate: impl FnOnce(&mut Fixture<EGraph>, &mut RuleSpec),
) -> Result<()> {
    let mut fixture = Fixture::new(EGraph::new()?, label)?;
    let mut invalid = fixture.scalar_rule(&format!("{label} invalid"));
    mutate(&mut fixture, &mut invalid);
    let error = fixture.backend.add_rule(invalid).unwrap_err();
    assert!(
        !error.to_string().contains("scalar-mixed"),
        "{label} was incorrectly selected: {error:#}"
    );
    assert_eq!(
        fixture
            .backend
            .add_rule(fixture.scalar_rule(&format!("{label} valid")))?,
        RuleId::new(0)
    );
    Ok(())
}

#[derive(Debug, Eq, PartialEq)]
struct Transcript {
    sym: Vec<Vec<u32>>,
    trans: Vec<Vec<u32>>,
    nil: Vec<Vec<u32>>,
    cons: Vec<Vec<u32>>,
    term: Vec<Vec<u32>>,
    ast: Vec<Vec<u32>>,
    rule: Vec<Vec<u32>>,
    old: Vec<Vec<u32>>,
    view: Vec<Vec<u32>>,
    uf: Vec<Vec<u32>>,
    next_fresh: u32,
}

fn scan_values(backend: &impl Backend, table: FunctionId) -> Vec<Vec<Value>> {
    let mut rows = Vec::new();
    backend.for_each_while_dyn(table, &mut |entry| {
        rows.push(entry.vals.to_vec());
        true
    });
    rows
}

fn id_rows(
    backend: &impl Backend,
    table: FunctionId,
    unit_terminated: bool,
    unit: Value,
) -> Vec<Vec<u32>> {
    let mut rows = scan_values(backend, table)
        .into_iter()
        .map(|mut row| {
            if unit_terminated {
                assert_eq!(row.pop(), Some(unit));
            }
            row.into_iter().map(NumericId::rep).collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    rows.sort();
    rows
}

fn rule_rows(
    backend: &impl Backend,
    table: FunctionId,
    unit: Value,
    label: Value,
) -> Vec<Vec<u32>> {
    let mut rows = scan_values(backend, table)
        .into_iter()
        .map(|mut row| {
            assert_eq!(row.pop(), Some(unit));
            assert_eq!(row.remove(0), label);
            row.into_iter().map(NumericId::rep).collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    rows.sort();
    rows
}

fn execute<B: Backend>(
    fixture: &mut Fixture<B>,
    reverse_owner: Option<(u32, u32)>,
) -> Result<Transcript> {
    execute_seeded(fixture, reverse_owner, &[])
}

fn execute_seeded<B: Backend>(
    fixture: &mut Fixture<B>,
    reverse_owner: Option<(u32, u32)>,
    uf_rows: &[[u32; 3]],
) -> Result<Transcript> {
    fixture.advance_fresh_to_100();
    let body_keys = (0..fixture.key_count)
        .map(|index| Value::new(u32::try_from(index).expect("test key index fits u32") + 1))
        .collect::<Vec<_>>();
    let mut body_row = body_keys.clone();
    body_row.extend([Value::new(20), Value::new(70)]);
    let mut initial = vec![
        (fixture.view, body_row),
        (fixture.old, vec![Value::new(20), Value::new(71)]),
    ];
    if let Some((owner, proof)) = reverse_owner {
        let mut reverse_row = body_keys.into_iter().rev().collect::<Vec<_>>();
        reverse_row.extend([Value::new(owner), Value::new(proof)]);
        initial.push((fixture.view, reverse_row));
    }
    initial.extend(uf_rows.iter().map(|row| {
        (
            fixture.uf,
            row.iter().copied().map(Value::new).collect::<Vec<_>>(),
        )
    }));
    fixture.backend.add_values(initial)?;
    let rule = fixture
        .backend
        .add_rule(fixture.scalar_rule("opaque exact scalar family"))?;
    let changed = fixture
        .backend
        .run_rules(RuleSetRun {
            name: Some("irreducible scalar transcript"),
            rules: &[rule],
        })?
        .changed();
    assert!(changed);

    Ok(collect_transcript(fixture))
}

fn collect_transcript<B: Backend>(fixture: &mut Fixture<B>) -> Transcript {
    Transcript {
        sym: id_rows(&fixture.backend, fixture.sym, true, fixture.unit_value),
        trans: id_rows(&fixture.backend, fixture.trans, true, fixture.unit_value),
        nil: id_rows(&fixture.backend, fixture.nil, true, fixture.unit_value),
        cons: id_rows(&fixture.backend, fixture.cons, true, fixture.unit_value),
        term: id_rows(&fixture.backend, fixture.term, true, fixture.unit_value),
        ast: id_rows(&fixture.backend, fixture.ast, true, fixture.unit_value),
        rule: rule_rows(
            &fixture.backend,
            fixture.rule,
            fixture.unit_value,
            fixture.rule_label,
        ),
        old: id_rows(&fixture.backend, fixture.old, false, fixture.unit_value),
        view: id_rows(&fixture.backend, fixture.view, false, fixture.unit_value),
        uf: id_rows(&fixture.backend, fixture.uf, false, fixture.unit_value),
        next_fresh: fixture.backend.fresh_id().rep(),
    }
}

fn expected_missing() -> Transcript {
    Transcript {
        sym: vec![vec![71, 100], vec![111, 112]],
        trans: vec![vec![100, 70, 101], vec![107, 112, 113], vec![110, 107, 111]],
        nil: vec![vec![102]],
        cons: vec![vec![101, 102, 103]],
        term: vec![vec![2, 1, 104]],
        ast: vec![
            vec![20, 108],
            vec![104, 105],
            vec![104, 106],
            vec![104, 109],
        ],
        rule: vec![vec![103, 105, 106, 107], vec![103, 108, 109, 110]],
        old: vec![vec![20, 71], vec![104, 107]],
        view: vec![vec![1, 2, 20, 70], vec![2, 1, 20, 111]],
        uf: vec![],
        next_fresh: 114,
    }
}

fn expected_differing_owner() -> Transcript {
    let mut expected = expected_missing();
    expected.sym.push(vec![111, 114]);
    expected.sym.sort();
    expected.trans.push(vec![72, 114, 115]);
    expected.trans.sort();
    expected.uf = vec![vec![30, 20, 115]];
    expected.next_fresh = 116;
    expected
}

fn expected_old_min_owner() -> Transcript {
    let mut expected = expected_missing();
    expected.sym.push(vec![72, 114]);
    expected.sym.sort();
    expected.trans.push(vec![111, 114, 115]);
    expected.trans.sort();
    expected.view[1] = vec![2, 1, 10, 72];
    expected.uf = vec![vec![20, 10, 115]];
    expected.next_fresh = 116;
    expected
}

fn execute_two_matches<B: Backend>(fixture: &mut Fixture<B>) -> Result<Transcript> {
    fixture.advance_fresh_to_100();
    fixture.backend.add_values(vec![
        (
            fixture.view,
            vec![Value::new(1), Value::new(2), Value::new(20), Value::new(70)],
        ),
        (
            fixture.view,
            vec![Value::new(3), Value::new(4), Value::new(21), Value::new(80)],
        ),
        (fixture.old, vec![Value::new(20), Value::new(71)]),
        (fixture.old, vec![Value::new(21), Value::new(72)]),
    ])?;
    let rule = fixture
        .backend
        .add_rule(fixture.variable_key_rule("two-match scalar topology"))?;
    assert!(
        fixture
            .backend
            .run_rules(RuleSetRun {
                name: Some("two-match scalar topology"),
                rules: &[rule],
            })?
            .changed()
    );
    Ok(collect_transcript(fixture))
}

fn watermark(backend: &EGraph, rule: RuleId) -> u64 {
    backend.rules[rule.rep() as usize]
        .as_ref()
        .expect("test rule remains registered")
        .watermark
}

fn scalar_scratch_count(backend: &EGraph) -> Result<u64> {
    backend.storage.with_connection(|connection| {
        connection
            .query_row(
                "SELECT count(*) FROM duckdb_tables()
                 WHERE table_name LIKE 'egglog_scalar_%'",
                [],
                |row| row.get(0),
            )
            .map_err(Into::into)
    })
}

fn derive_match_fresh(
    transcript: &Transcript,
    owner: u32,
    owner_proof: u32,
    view_proof: u32,
    reverse_keys: [u32; 2],
) -> [u32; 14] {
    let unique_last = |rows: &[Vec<u32>], prefix: &[u32]| {
        let matches = rows
            .iter()
            .filter(|row| row.starts_with(prefix))
            .collect::<Vec<_>>();
        assert_eq!(matches.len(), 1, "expected one row beginning {prefix:?}");
        *matches[0].last().expect("matched row is nonempty")
    };
    let f0 = unique_last(&transcript.sym, &[owner_proof]);
    let f1 = unique_last(&transcript.trans, &[f0, view_proof]);
    let cons = transcript
        .cons
        .iter()
        .find(|row| row[0] == f1)
        .expect("match has one PCons row");
    let f2 = cons[1];
    let f3 = cons[2];
    assert!(transcript.nil.contains(&vec![f2]));
    let f4 = unique_last(&transcript.term, &reverse_keys);
    let f7 = unique_last(&transcript.old, &[f4]);
    let f8 = unique_last(&transcript.ast, &[owner]);
    let first_rule = transcript
        .rule
        .iter()
        .find(|row| row[0] == f3 && row[3] == f7)
        .expect("match has its first Rule row");
    let f5 = first_rule[1];
    let f6 = first_rule[2];
    assert!(transcript.ast.contains(&vec![f4, f5]));
    assert!(transcript.ast.contains(&vec![f4, f6]));
    let f9s = transcript
        .ast
        .iter()
        .filter(|row| row[0] == f4 && row[1] != f5 && row[1] != f6)
        .map(|row| row[1])
        .collect::<Vec<_>>();
    assert_eq!(f9s.len(), 1);
    let f9 = f9s[0];
    let second_rule = transcript
        .rule
        .iter()
        .find(|row| row[0] == f3 && row[1] == f8 && row[2] == f9)
        .expect("match has its second Rule row");
    let f10 = second_rule[3];
    let f11 = unique_last(&transcript.trans, &[f10, f7]);
    let f12 = unique_last(&transcript.sym, &[f11]);
    let f13 = unique_last(&transcript.trans, &[f7, f12]);
    [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13]
}

#[test]
fn irreducible_missing_owner_matches_reference_exactly() -> Result<()> {
    let mut reference = Fixture::new(egglog_bridge::EGraph::default(), "reference missing")?;
    let mut duckdb = Fixture::new(EGraph::new()?, "duckdb missing")?;
    let expected = expected_missing();
    assert_eq!(execute(&mut reference, None)?, expected);
    assert_eq!(execute(&mut duckdb, None)?, expected);
    assert_eq!(duckdb.backend.last_rule_match_counts(), &[1]);
    assert_eq!(duckdb.backend.last_rule_insert_counts(), &[15]);
    Ok(())
}

#[test]
fn irreducible_differing_owner_drains_after_late_actions() -> Result<()> {
    let mut reference = Fixture::new(egglog_bridge::EGraph::default(), "reference collision")?;
    let mut duckdb = Fixture::new(EGraph::new()?, "duckdb collision")?;
    let expected = expected_differing_owner();
    assert_eq!(execute(&mut reference, Some((30, 72)))?, expected);
    assert_eq!(execute(&mut duckdb, Some((30, 72)))?, expected);
    assert_eq!(duckdb.backend.last_rule_match_counts(), &[1]);
    assert_eq!(duckdb.backend.last_rule_insert_counts(), &[15]);
    Ok(())
}

#[test]
fn equal_and_old_min_view_owners_match_reference() -> Result<()> {
    let mut reference_equal =
        Fixture::new(egglog_bridge::EGraph::default(), "reference equal owner")?;
    let mut duckdb_equal = Fixture::new(EGraph::new()?, "duckdb equal owner")?;
    let equal = expected_missing();
    assert_eq!(execute(&mut reference_equal, Some((20, 111)))?, equal);
    assert_eq!(execute(&mut duckdb_equal, Some((20, 111)))?, equal);

    let mut reference_old = Fixture::new(egglog_bridge::EGraph::default(), "reference old min")?;
    let mut duckdb_old = Fixture::new(EGraph::new()?, "duckdb old min")?;
    let old_min = expected_old_min_owner();
    assert_eq!(execute(&mut reference_old, Some((10, 72)))?, old_min);
    assert_eq!(execute(&mut duckdb_old, Some((10, 72)))?, old_min);
    Ok(())
}

#[test]
fn recursive_displaced_union_reaches_reference_fixed_point() -> Result<()> {
    let mut reference = Fixture::new(egglog_bridge::EGraph::default(), "reference recursive")?;
    let mut duckdb = Fixture::new(EGraph::new()?, "duckdb recursive")?;
    let uf_seed = [[30, 25, 80], [25, 10, 81]];
    let reference_transcript = execute_seeded(&mut reference, Some((30, 72)), &uf_seed)?;
    let duckdb_transcript = execute_seeded(&mut duckdb, Some((30, 72)), &uf_seed)?;
    assert_eq!(duckdb_transcript, reference_transcript);
    assert_eq!(duckdb_transcript.next_fresh, 120);
    assert_eq!(
        duckdb_transcript.uf,
        vec![vec![20, 10, 119], vec![25, 10, 81], vec![30, 20, 115]]
    );
    assert_eq!(duckdb.backend.last_rule_insert_counts(), &[15]);
    Ok(())
}

#[test]
fn nullary_and_twenty_seven_key_forms_match_reference() -> Result<()> {
    for (key_count, label) in [(0, "nullary"), (27, "wide")] {
        let mut reference = Fixture::new_with_key_count(
            egglog_bridge::EGraph::default(),
            &format!("reference {label}"),
            key_count,
        )?;
        let mut duckdb =
            Fixture::new_with_key_count(EGraph::new()?, &format!("duckdb {label}"), key_count)?;
        let reference_transcript = execute(&mut reference, None)?;
        let duckdb_transcript = execute(&mut duckdb, None)?;
        assert_eq!(duckdb_transcript, reference_transcript);
        assert_eq!(duckdb_transcript.next_fresh, 114);
        assert_eq!(duckdb.backend.last_rule_match_counts(), &[1]);
        assert_eq!(duckdb.backend.last_rule_insert_counts(), &[15]);
    }
    Ok(())
}

#[test]
fn two_matches_are_alpha_equivalent_and_fresh_action_major() -> Result<()> {
    let mut reference = Fixture::new(egglog_bridge::EGraph::default(), "reference two match")?;
    let mut duckdb = Fixture::new(EGraph::new()?, "duckdb two match")?;
    let reference_transcript = execute_two_matches(&mut reference)?;
    let duckdb_transcript = execute_two_matches(&mut duckdb)?;

    for transcript in [&reference_transcript, &duckdb_transcript] {
        assert_eq!(transcript.sym.len(), 4);
        assert_eq!(transcript.trans.len(), 6);
        assert_eq!(transcript.nil.len(), 2);
        assert_eq!(transcript.cons.len(), 2);
        assert_eq!(transcript.term.len(), 2);
        assert_eq!(transcript.ast.len(), 8);
        assert_eq!(transcript.rule.len(), 4);
        assert_eq!(transcript.old.len(), 4);
        assert_eq!(transcript.view.len(), 4);
        assert!(transcript.uf.is_empty());
        assert_eq!(transcript.next_fresh, 128);

        let first = derive_match_fresh(transcript, 20, 71, 70, [2, 1]);
        let second = derive_match_fresh(transcript, 21, 72, 80, [4, 3]);
        let all = first.into_iter().chain(second).collect::<BTreeSet<_>>();
        assert_eq!(all, (100..128).collect());
        assert!(transcript.view.contains(&vec![2, 1, 20, first[11]]));
        assert!(transcript.view.contains(&vec![4, 3, 21, second[11]]));
    }

    let first = derive_match_fresh(&duckdb_transcript, 20, 71, 70, [2, 1]);
    let second = derive_match_fresh(&duckdb_transcript, 21, 72, 80, [4, 3]);
    assert_eq!(
        first,
        std::array::from_fn(|rank| 100 + u32::try_from(rank).unwrap() * 2)
    );
    assert_eq!(
        second,
        std::array::from_fn(|rank| 101 + u32::try_from(rank).unwrap() * 2)
    );
    assert_eq!(duckdb.backend.last_rule_match_counts(), &[2]);
    assert_eq!(duckdb.backend.last_rule_insert_counts(), &[30]);
    Ok(())
}

#[test]
fn stable_prewave_becomes_seminaively_quiescent() -> Result<()> {
    let mut fixture = Fixture::new(EGraph::new()?, "duckdb quiescent")?;
    fixture.advance_fresh_to_100();
    fixture.backend.add_values(vec![
        (
            fixture.view,
            vec![Value::new(1), Value::new(2), Value::new(20), Value::new(70)],
        ),
        (fixture.old, vec![Value::new(20), Value::new(71)]),
    ])?;
    let rule = fixture
        .backend
        .add_rule(fixture.scalar_rule("quiescent scalar rule"))?;
    assert!(
        fixture
            .backend
            .run_rules(RuleSetRun {
                name: Some("first scalar run"),
                rules: &[rule],
            })?
            .changed()
    );
    assert_eq!(fixture.backend.last_rule_match_counts(), &[1]);
    assert_eq!(fixture.backend.last_rule_insert_counts(), &[15]);
    assert_eq!(fixture.backend.storage.next_fresh_id()?, 114);
    assert!(
        !fixture
            .backend
            .run_rules(RuleSetRun {
                name: Some("quiescent scalar rerun"),
                rules: &[rule],
            })?
            .changed()
    );
    assert_eq!(fixture.backend.last_rule_match_counts(), &[0]);
    assert_eq!(fixture.backend.last_rule_insert_counts(), &[0]);
    assert_eq!(fixture.backend.storage.next_fresh_id()?, 114);
    assert_eq!(scalar_scratch_count(&fixture.backend)?, 0);
    Ok(())
}

#[test]
fn lookup_reads_subsumed_durable_owner() -> Result<()> {
    let mut fixture = Fixture::new(EGraph::new()?, "duckdb subsumed lookup")?;
    fixture.advance_fresh_to_100();
    fixture.backend.add_values(vec![(
        fixture.view,
        vec![Value::new(1), Value::new(2), Value::new(20), Value::new(70)],
    )])?;
    fixture.backend.storage.with_connection(|connection| {
        connection.execute(
            &format!(
                "INSERT INTO {} VALUES (
                    CAST('20' AS UBIGINT), CAST('71' AS UBIGINT),
                    CAST('0' AS UBIGINT), TRUE
                )",
                sql_table(fixture.old)
            ),
            [],
        )?;
        Ok(())
    })?;
    let rule = fixture
        .backend
        .add_rule(fixture.scalar_rule("subsumed lookup scalar rule"))?;
    assert!(
        fixture
            .backend
            .run_rules(RuleSetRun {
                name: Some("subsumed lookup"),
                rules: &[rule],
            })?
            .changed()
    );
    assert!(
        id_rows(&fixture.backend, fixture.sym, true, fixture.unit_value).contains(&vec![71, 100])
    );
    assert_eq!(fixture.backend.last_rule_match_counts(), &[1]);
    assert_eq!(fixture.backend.last_rule_insert_counts(), &[15]);
    Ok(())
}

#[test]
fn missing_and_duplicate_lookups_abort_before_mutation() -> Result<()> {
    for duplicate in [false, true] {
        let mut fixture = Fixture::new(
            EGraph::new()?,
            if duplicate {
                "duckdb duplicate lookup"
            } else {
                "duckdb missing lookup"
            },
        )?;
        fixture.advance_fresh_to_100();
        let mut initial = vec![(
            fixture.view,
            vec![Value::new(1), Value::new(2), Value::new(20), Value::new(70)],
        )];
        if duplicate {
            initial.push((fixture.old, vec![Value::new(20), Value::new(71)]));
        }
        fixture.backend.add_values(initial)?;
        if duplicate {
            fixture.backend.storage.with_connection(|connection| {
                connection.execute(
                    &format!(
                        "INSERT INTO {} VALUES (
                            CAST('20' AS UBIGINT), CAST('72' AS UBIGINT),
                            CAST('0' AS UBIGINT), FALSE
                        )",
                        sql_table(fixture.old)
                    ),
                    [],
                )?;
                Ok(())
            })?;
        }
        let rule = fixture
            .backend
            .add_rule(fixture.scalar_rule("failing lookup scalar rule"))?;
        let generation = fixture.backend.storage.generation()?;
        let trace = fixture.backend.storage.latest_rule_sql();
        let error = fixture
            .backend
            .run_rules(RuleSetRun {
                name: Some("failing lookup"),
                rules: &[rule],
            })
            .unwrap_err();
        assert!(error.to_string().contains("exactly one pre-wave owner"));
        assert_eq!(fixture.backend.storage.generation()?, generation);
        assert_eq!(fixture.backend.storage.next_fresh_id()?, 100);
        assert_eq!(watermark(&fixture.backend, rule), 0);
        assert_eq!(fixture.backend.last_rule_match_counts(), &[]);
        assert_eq!(fixture.backend.last_rule_insert_counts(), &[]);
        assert_eq!(fixture.backend.storage.latest_rule_sql(), trace);
        assert_eq!(fixture.backend.table_size(fixture.sym), 0);
        assert_eq!(fixture.backend.table_size(fixture.trans), 0);
        assert_eq!(scalar_scratch_count(&fixture.backend)?, 0);
    }
    Ok(())
}

#[test]
fn same_run_old_set_is_invisible_to_later_lookup() -> Result<()> {
    let mut fixture = Fixture::new(EGraph::new()?, "duckdb same-run lookup")?;
    fixture.advance_fresh_to_100();
    fixture.backend.add_values(vec![
        (
            fixture.view,
            vec![Value::new(1), Value::new(2), Value::new(20), Value::new(70)],
        ),
        (
            fixture.view,
            vec![
                Value::new(3),
                Value::new(4),
                Value::new(104),
                Value::new(80),
            ],
        ),
        (fixture.old, vec![Value::new(20), Value::new(71)]),
    ])?;
    let producer = fixture
        .backend
        .add_rule(fixture.literal_key_rule("producer lookup rule", [1, 2]))?;
    let consumer = fixture
        .backend
        .add_rule(fixture.literal_key_rule("consumer lookup rule", [3, 4]))?;
    let generation = fixture.backend.storage.generation()?;
    let error = fixture
        .backend
        .run_rules(RuleSetRun {
            name: Some("same-run lookup isolation"),
            rules: &[producer, consumer],
        })
        .unwrap_err();
    assert!(error.to_string().contains("exactly one pre-wave owner"));
    assert_eq!(fixture.backend.storage.generation()?, generation);
    assert_eq!(fixture.backend.storage.next_fresh_id()?, 100);
    assert_eq!(watermark(&fixture.backend, producer), 0);
    assert_eq!(watermark(&fixture.backend, consumer), 0);
    assert_eq!(fixture.backend.table_size(fixture.sym), 0);
    assert_eq!(scalar_scratch_count(&fixture.backend)?, 0);
    Ok(())
}

#[test]
fn variable_call_and_fresh_label_names_are_diagnostic_only() -> Result<()> {
    let mut fixture = Fixture::new(EGraph::new()?, "duckdb diagnostic names")?;
    fixture.advance_fresh_to_100();
    fixture.backend.add_values(vec![
        (
            fixture.view,
            vec![Value::new(1), Value::new(2), Value::new(20), Value::new(70)],
        ),
        (fixture.old, vec![Value::new(20), Value::new(71)]),
    ])?;
    let mut rule = fixture.scalar_rule("diagnostic names scalar rule");
    let GenericAtomTerm::Var(_, owner) = &mut rule.core.body.atoms[0].args[2] else {
        unreachable!("fixture body owner is a variable");
    };
    owner.name = "same id and type, unrelated use-site name".into();
    for (rank, action) in rule
        .core
        .head
        .0
        .iter_mut()
        .filter(|action| matches!(action, GenericCoreAction::Let(..)))
        .enumerate()
    {
        let GenericCoreAction::Let(_, _, RuleActionCall::Primitive { name, .. }, arguments) =
            action
        else {
            continue;
        };
        *name = format!("diagnostic fresh call {rank}").into();
        let fresh_label = fixture.backend.base_values().get(Boxed::new(format!(
            "distinct label {rank} with quote ' and newline\n"
        )));
        arguments[0] = literal(fresh_label, ColumnTy::Base(fixture.types.string));
    }
    let id = fixture.backend.add_rule(rule)?;
    assert!(
        fixture
            .backend
            .run_rules(RuleSetRun {
                name: Some("diagnostic name execution"),
                rules: &[id],
            })?
            .changed()
    );
    assert_eq!(collect_transcript(&mut fixture), expected_missing());
    Ok(())
}

#[test]
fn a_distinct_live_context_fresh_token_is_accepted() -> Result<()> {
    let mut fixture = Fixture::new(EGraph::new()?, "duckdb context fresh token")?;
    fixture.advance_fresh_to_100();
    fixture.backend.add_values(vec![
        (
            fixture.view,
            vec![Value::new(1), Value::new(2), Value::new(20), Value::new(70)],
        ),
        (fixture.old, vec![Value::new(20), Value::new(71)]),
    ])?;
    let action_token = fixture.backend.register_get_fresh();
    let mut rule = fixture.scalar_rule("distinct live action fresh token");
    for action in &mut rule.core.head.0 {
        let GenericCoreAction::Let(_, _, RuleActionCall::Primitive { id, .. }, _) = action else {
            continue;
        };
        *id = action_token;
    }
    let id = fixture.backend.add_rule(rule)?;
    assert!(
        fixture
            .backend
            .run_rules(RuleSetRun {
                name: Some("distinct live action fresh token"),
                rules: &[id],
            })?
            .changed()
    );
    assert_eq!(collect_transcript(&mut fixture), expected_missing());
    Ok(())
}

#[test]
fn selected_mutation_matrix_preserves_rule_id_zero() -> Result<()> {
    selected_rejection("wrong seminaive", |_, rule| rule.seminaive = false)?;
    selected_rejection("wrong decomposition", |_, rule| rule.no_decomp = true)?;
    unselected_rejection("wrong body mode", |_, rule| {
        let RuleBodyCall::Table { read, .. } = &mut rule.core.body.atoms[0].head else {
            unreachable!();
        };
        *read = ReadMode::All;
    })?;
    selected_rejection("short action stream", |_, rule| {
        rule.core.head.0.pop();
    })?;
    selected_rejection("moved lookup", |_, rule| {
        rule.core.head.0.swap(2, 4);
    })?;
    selected_rejection("extra lookup", |_, rule| {
        rule.core.head.0[1] = rule.core.head.0[2].clone();
    })?;
    selected_rejection("use before binding", |_, rule| {
        let future = match &rule.core.head.0[7] {
            GenericCoreAction::Let(_, binding, ..) => variable(binding.clone()),
            _ => unreachable!(),
        };
        let GenericCoreAction::Set(_, _, keys, _) = &mut rule.core.head.0[6] else {
            unreachable!();
        };
        keys[0] = future;
    })?;
    selected_rejection("ssa rebinding", |_, rule| {
        let owner = match &rule.core.body.atoms[0].args[2] {
            GenericAtomTerm::Var(_, owner) => owner.clone(),
            _ => unreachable!(),
        };
        let GenericCoreAction::Let(_, binding, ..) = &mut rule.core.head.0[4] else {
            unreachable!();
        };
        *binding = owner;
    })?;
    selected_rejection("wrong fresh type", |fixture, rule| {
        let GenericCoreAction::Let(_, binding, ..) = &mut rule.core.head.0[4] else {
            unreachable!();
        };
        binding.ty = ColumnTy::Base(fixture.types.string);
    })?;
    selected_rejection("wrong set arity", |_, rule| {
        let GenericCoreAction::Set(_, _, keys, _) = &mut rule.core.head.0[6] else {
            unreachable!();
        };
        keys.pop();
    })?;
    selected_rejection("wrong head fresh token", |fixture, rule| {
        let token = fixture
            .backend
            .new_panic("wrong head token must remain declarative".to_string());
        let GenericCoreAction::Let(_, _, RuleActionCall::Primitive { id, .. }, _) =
            &mut rule.core.head.0[4]
        else {
            unreachable!();
        };
        *id = token;
    })?;
    selected_rejection("mixed live fresh tokens", |fixture, rule| {
        let token = fixture.backend.register_get_fresh();
        let GenericCoreAction::Let(_, _, RuleActionCall::Primitive { id, .. }, _) =
            &mut rule.core.head.0[7]
        else {
            unreachable!();
        };
        *id = token;
    })?;
    selected_rejection("wrong fresh signature", |fixture, rule| {
        let GenericCoreAction::Let(_, _, RuleActionCall::Primitive { output, .. }, _) =
            &mut rule.core.head.0[4]
        else {
            unreachable!();
        };
        *output = ColumnTy::Base(fixture.types.unit);
    })?;
    selected_rejection("different old target", |fixture, rule| {
        let replacement = fixture.backend.add_table(FunctionConfig {
            schema: vec![ColumnTy::Id, ColumnTy::Id],
            n_vals: 1,
            n_identity_vals: None,
            default: DefaultVal::Fail,
            merge: MergeFn::Old,
            name: "second exact Old target".to_string(),
            can_subsume: false,
        });
        let GenericCoreAction::Set(_, RuleActionCall::Table { id, .. }, _, _) =
            &mut rule.core.head.0[29]
        else {
            unreachable!();
        };
        *id = replacement;
    })?;
    selected_rejection("wrong ordinary config", |fixture, rule| {
        let GenericCoreAction::Set(_, RuleActionCall::Table { id, .. }, _, _) =
            &mut rule.core.head.0[12]
        else {
            unreachable!();
        };
        *id = fixture.old;
    })?;
    selected_rejection("second view set", |fixture, rule| {
        let GenericCoreAction::Set(_, RuleActionCall::Table { id, .. }, _, _) =
            &mut rule.core.head.0[46]
        else {
            unreachable!();
        };
        *id = fixture.view;
    })?;
    selected_rejection("wrong action kind", |fixture, rule| {
        rule.core.head.0[6] = GenericCoreAction::Change(
            Span::Panic,
            Change::Delete,
            table_call(fixture.sym, "wrong Delete action"),
            vec![],
        );
    })?;
    for index in [0, 3, 5, 8, 11, 14, 18, 21, 24, 27, 31, 34, 37, 40, 45, 48] {
        selected_rejection(&format!("scaffolding alias {index}"), move |_, rule| {
            let GenericCoreAction::LetAtomTerm(_, _, source) = &mut rule.core.head.0[index] else {
                unreachable!("scaffolding index {index} must be an SSA alias")
            };
            *source = literal(Value::new(4_000_000 + index as u32), ColumnTy::Id);
        })?;
    }
    Ok(())
}

#[test]
fn self_consistent_nonfresh_token_is_rejected_before_rule_id() -> Result<()> {
    let mut fixture =
        Fixture::new_with_fake_fresh_token(EGraph::new()?, "duckdb fake fresh graph")?;
    let error = fixture
        .backend
        .add_rule(fixture.scalar_rule("fake fresh scalar rule"))
        .unwrap_err();
    assert!(
        error
            .to_string()
            .contains("live registered get-fresh token"),
        "{error:#}"
    );
    assert_eq!(
        fixture
            .backend
            .add_rule(direct_canary_rule(&fixture, "valid after fake fresh"))?,
        RuleId::new(0)
    );
    Ok(())
}

#[test]
fn freed_fresh_token_reused_by_ordinary_callback_loses_authority() -> Result<()> {
    let mut fixture = Fixture::new(EGraph::new()?, "duckdb stale fresh provenance")?;
    let stale = fixture.primitives.fresh;
    fixture.backend.free_external_func(stale);
    let reused = fixture
        .backend
        .new_panic("reused ordinary token must remain declarative".into());
    assert_eq!(
        reused, stale,
        "the external registry should reuse the freed id"
    );

    let error = fixture
        .backend
        .add_rule(fixture.scalar_rule("stale fresh scalar rule"))
        .unwrap_err();
    assert!(
        error
            .to_string()
            .contains("live registered get-fresh token"),
        "{error:#}"
    );
    assert_eq!(
        fixture
            .backend
            .add_rule(direct_canary_rule(&fixture, "valid after stale fresh"))?,
        RuleId::new(0)
    );
    Ok(())
}

#[test]
fn scalar_plan_reauthenticates_ordered_union_merge_tokens_after_same_kind_reuse() -> Result<()> {
    let mut fixture = Fixture::new(EGraph::new()?, "duckdb stale merge provenance")?;
    let stale = fixture.primitives.proof_max;
    let rule = fixture
        .backend
        .add_rule(fixture.scalar_rule("stale merge-token scalar rule"))?;
    let generation = fixture.backend.storage.generation()?;
    let trace = fixture.backend.storage.latest_rule_sql();
    let watermark = fixture.backend.rules[rule.rep() as usize]
        .as_ref()
        .expect("registered rule")
        .watermark;

    fixture.backend.free_external_func(stale);
    let replacement = fixture
        .backend
        .register_native_primitive(NativePrimitive::SelectMaxPayload);
    assert_eq!(replacement, stale);
    let error = fixture
        .backend
        .run_rules(RuleSetRun {
            name: Some("same-kind merge token ABA"),
            rules: &[rule],
        })
        .unwrap_err();
    assert!(
        error
            .to_string()
            .contains("freed or reused authority token"),
        "{error:#}"
    );
    assert_eq!(fixture.backend.storage.generation()?, generation);
    assert_eq!(fixture.backend.storage.latest_rule_sql(), trace);
    assert_eq!(fixture.backend.storage.next_fresh_id()?, 0);
    assert_eq!(
        fixture.backend.rules[rule.rep() as usize]
            .as_ref()
            .expect("registered rule")
            .watermark,
        watermark
    );
    Ok(())
}

#[test]
fn non_subsumable_self_displacing_uf_continues_through_general_admission() -> Result<()> {
    let mut fixture = Fixture::new_with_key_count(EGraph::new()?, "duckdb non-subsume owner", 1)?;
    let mut rule = fixture.scalar_rule("non-subsume self-displacing near shape");
    let RuleBodyCall::Table { id, .. } = &mut rule.core.body.atoms[0].head else {
        unreachable!()
    };
    *id = fixture.uf;
    let GenericCoreAction::Set(_, RuleActionCall::Table { id, .. }, _, _) =
        &mut rule.core.head.0[42]
    else {
        unreachable!()
    };
    *id = fixture.uf;

    let error = fixture.backend.add_rule(rule).unwrap_err().to_string();
    assert!(error.contains("DuckDB scalar rule"), "{error}");
    assert!(
        error.contains("incompatible ordered-union target"),
        "{error}"
    );
    assert!(!error.contains("scalar-mixed"), "{error}");
    assert_eq!(
        fixture
            .backend
            .add_rule(fixture.scalar_rule("valid after non-subsume fallthrough"))?,
        RuleId::new(0)
    );
    Ok(())
}

#[test]
fn late_trailing_conflict_rolls_back_nonzero_watermark_then_retries() -> Result<()> {
    let mut fixture = Fixture::new(EGraph::new()?, "duckdb late conflict")?;
    fixture.advance_fresh_to_100();
    fixture.backend.add_values(vec![
        (
            fixture.view,
            vec![Value::new(1), Value::new(2), Value::new(20), Value::new(70)],
        ),
        (fixture.old, vec![Value::new(20), Value::new(71)]),
    ])?;
    let rule = fixture
        .backend
        .add_rule(fixture.scalar_rule("late conflict scalar rule"))?;
    assert!(
        fixture
            .backend
            .run_rules(RuleSetRun {
                name: Some("establish nonzero watermark"),
                rules: &[rule],
            })?
            .changed()
    );
    let retained_watermark = watermark(&fixture.backend, rule);
    assert_ne!(retained_watermark, 0);
    assert_eq!(fixture.backend.storage.next_fresh_id()?, 114);
    let generation = fixture.backend.storage.generation()?;
    fixture.backend.storage.with_connection(|connection| {
        connection.execute(
            &format!(
                "UPDATE {} SET __generation = CAST('{generation}' AS UBIGINT)
                 WHERE c0 = CAST('1' AS UBIGINT) AND c1 = CAST('2' AS UBIGINT)",
                sql_table(fixture.view)
            ),
            [],
        )?;
        // The next run's trailing action 31 is Sym(125,126)=Unit. A
        // physically malformed FALSE owner forces the latest direct conflict,
        // after earlier actions have already issued transactional writes.
        connection.execute(
            &format!(
                "INSERT INTO {} VALUES (
                    CAST('125' AS UBIGINT), CAST('126' AS UBIGINT), FALSE,
                    CAST('{generation}' AS UBIGINT), FALSE
                )",
                sql_table(fixture.sym)
            ),
            [],
        )?;
        Ok(())
    })?;
    let sizes = [
        fixture.backend.table_size(fixture.sym),
        fixture.backend.table_size(fixture.trans),
        fixture.backend.table_size(fixture.nil),
        fixture.backend.table_size(fixture.cons),
        fixture.backend.table_size(fixture.term),
        fixture.backend.table_size(fixture.ast),
        fixture.backend.table_size(fixture.rule),
        fixture.backend.table_size(fixture.old),
        fixture.backend.table_size(fixture.view),
        fixture.backend.table_size(fixture.uf),
    ];
    let trace = fixture.backend.storage.latest_rule_sql();
    let error = fixture
        .backend
        .run_rules(RuleSetRun {
            name: Some("late trailing conflict"),
            rules: &[rule],
        })
        .unwrap_err();
    assert!(error.to_string().contains("AssertEq conflict"));
    assert_eq!(fixture.backend.storage.generation()?, generation);
    assert_eq!(fixture.backend.storage.next_fresh_id()?, 114);
    assert_eq!(watermark(&fixture.backend, rule), retained_watermark);
    assert_eq!(fixture.backend.last_rule_match_counts(), &[1]);
    assert_eq!(fixture.backend.last_rule_insert_counts(), &[15]);
    assert_eq!(fixture.backend.storage.latest_rule_sql(), trace);
    assert_eq!(
        [
            fixture.backend.table_size(fixture.sym),
            fixture.backend.table_size(fixture.trans),
            fixture.backend.table_size(fixture.nil),
            fixture.backend.table_size(fixture.cons),
            fixture.backend.table_size(fixture.term),
            fixture.backend.table_size(fixture.ast),
            fixture.backend.table_size(fixture.rule),
            fixture.backend.table_size(fixture.old),
            fixture.backend.table_size(fixture.view),
            fixture.backend.table_size(fixture.uf),
        ],
        sizes
    );
    assert_eq!(scalar_scratch_count(&fixture.backend)?, 0);

    fixture.backend.storage.with_connection(|connection| {
        connection.execute(
            &format!(
                "DELETE FROM {} WHERE c0 = CAST('125' AS UBIGINT)
                 AND c1 = CAST('126' AS UBIGINT) AND c2 = FALSE",
                sql_table(fixture.sym)
            ),
            [],
        )?;
        Ok(())
    })?;
    assert!(
        fixture
            .backend
            .run_rules(RuleSetRun {
                name: Some("exact retry after late conflict"),
                rules: &[rule],
            })?
            .changed()
    );
    assert_eq!(fixture.backend.storage.next_fresh_id()?, 128);
    assert_eq!(fixture.backend.last_rule_match_counts(), &[1]);
    assert_eq!(fixture.backend.last_rule_insert_counts(), &[15]);
    assert_eq!(
        fixture
            .backend
            .lookup_row(fixture.sym, &[Value::new(125), Value::new(126)]),
        Some(vec![Value::new(125), Value::new(126), fixture.unit_value])
    );
    Ok(())
}

#[test]
fn collision_exhaustion_rolls_back_then_exact_retry_succeeds() -> Result<()> {
    let mut fixture = Fixture::new(EGraph::new()?, "duckdb collision exhaustion")?;
    fixture.backend.add_values(vec![
        (
            fixture.view,
            vec![Value::new(1), Value::new(2), Value::new(20), Value::new(70)],
        ),
        (
            fixture.view,
            vec![Value::new(2), Value::new(1), Value::new(30), Value::new(72)],
        ),
        (fixture.old, vec![Value::new(20), Value::new(71)]),
    ])?;
    let first_fresh = u64::from(u32::MAX) - 14;
    fixture.backend.storage.set_next_fresh_id(first_fresh)?;
    let rule = fixture
        .backend
        .add_rule(fixture.scalar_rule("collision exhaustion scalar rule"))?;
    let generation = fixture.backend.storage.generation()?;
    let error = fixture
        .backend
        .run_rules(RuleSetRun {
            name: Some("collision exhaustion"),
            rules: &[rule],
        })
        .unwrap_err();
    assert!(error.to_string().contains("merge collisions"));
    assert_eq!(fixture.backend.storage.generation()?, generation);
    assert_eq!(fixture.backend.storage.next_fresh_id()?, first_fresh);
    assert_eq!(watermark(&fixture.backend, rule), 0);
    assert_eq!(fixture.backend.last_rule_match_counts(), &[]);
    assert_eq!(fixture.backend.table_size(fixture.sym), 0);
    assert_eq!(fixture.backend.table_size(fixture.trans), 0);
    assert_eq!(fixture.backend.table_size(fixture.uf), 0);
    assert_eq!(fixture.backend.table_size(fixture.view), 2);
    assert_eq!(scalar_scratch_count(&fixture.backend)?, 0);

    fixture.backend.storage.set_next_fresh_id(100)?;
    assert!(
        fixture
            .backend
            .run_rules(RuleSetRun {
                name: Some("exact retry after collision exhaustion"),
                rules: &[rule],
            })?
            .changed()
    );
    assert_eq!(collect_transcript(&mut fixture), expected_differing_owner());
    assert_eq!(fixture.backend.last_rule_match_counts(), &[1]);
    assert_eq!(fixture.backend.last_rule_insert_counts(), &[15]);
    Ok(())
}

#[test]
fn mixed_scalar_and_direct_schedule_fails_before_mutation_in_both_orders() -> Result<()> {
    let mut fixture = Fixture::new(EGraph::new()?, "duckdb mixed schedule")?;
    fixture.advance_fresh_to_100();
    fixture.backend.add_values(vec![
        (
            fixture.view,
            vec![Value::new(1), Value::new(2), Value::new(20), Value::new(70)],
        ),
        (fixture.old, vec![Value::new(20), Value::new(71)]),
    ])?;
    let scalar = fixture
        .backend
        .add_rule(fixture.scalar_rule("mixed schedule scalar"))?;
    let direct = fixture
        .backend
        .add_rule(direct_canary_rule(&fixture, "mixed schedule direct"))?;
    let generation = fixture.backend.storage.generation()?;
    for rules in [[scalar, direct], [direct, scalar]] {
        let error = fixture
            .backend
            .run_rules(RuleSetRun {
                name: Some("mixed scalar and direct schedule"),
                rules: &rules,
            })
            .unwrap_err();
        assert!(error.to_string().contains("cannot mix scalar-mixed"));
        assert_eq!(fixture.backend.storage.generation()?, generation);
        assert_eq!(fixture.backend.storage.next_fresh_id()?, 100);
        assert_eq!(watermark(&fixture.backend, scalar), 0);
        assert_eq!(watermark(&fixture.backend, direct), 0);
        assert_eq!(fixture.backend.table_size(fixture.sym), 0);
        assert_eq!(fixture.backend.table_size(fixture.ast), 0);
        assert_eq!(scalar_scratch_count(&fixture.backend)?, 0);
    }
    Ok(())
}

#[test]
fn subsumed_view_owner_uses_the_shared_collision_kernel() -> Result<()> {
    let mut fixture = Fixture::new(EGraph::new()?, "duckdb subsumed View")?;
    fixture.advance_fresh_to_100();
    fixture.backend.add_values(vec![
        (
            fixture.view,
            vec![Value::new(1), Value::new(2), Value::new(20), Value::new(70)],
        ),
        (
            fixture.view,
            vec![Value::new(2), Value::new(1), Value::new(30), Value::new(72)],
        ),
        (fixture.old, vec![Value::new(20), Value::new(71)]),
    ])?;
    fixture.backend.storage.with_connection(|connection| {
        connection.execute(
            &format!(
                "UPDATE {} SET __subsumed = TRUE
                 WHERE c0 = CAST('2' AS UBIGINT) AND c1 = CAST('1' AS UBIGINT)",
                sql_table(fixture.view)
            ),
            [],
        )?;
        Ok(())
    })?;
    let rule = fixture
        .backend
        .add_rule(fixture.scalar_rule("subsumed View scalar rule"))?;
    assert!(
        fixture
            .backend
            .run_rules(RuleSetRun {
                name: Some("subsumed View owner"),
                rules: &[rule],
            })?
            .changed()
    );
    assert_eq!(collect_transcript(&mut fixture), expected_differing_owner());
    let remains_subsumed = fixture.backend.storage.with_connection(|connection| {
        connection
            .query_row(
                &format!(
                    "SELECT __subsumed FROM {} WHERE c0 = CAST('2' AS UBIGINT)
                     AND c1 = CAST('1' AS UBIGINT)",
                    sql_table(fixture.view)
                ),
                [],
                |row| row.get::<_, bool>(0),
            )
            .map_err(Into::into)
    })?;
    assert!(remains_subsumed);
    Ok(())
}

#[test]
fn unrelated_shapes_preserve_existing_fallthrough_diagnostics() -> Result<()> {
    let mut no_view_set = Fixture::new(EGraph::new()?, "duckdb no View head")?;
    let mut invalid = no_view_set.scalar_rule("unselected without View Set");
    let GenericCoreAction::Set(_, RuleActionCall::Table { id, .. }, _, _) =
        &mut invalid.core.head.0[42]
    else {
        unreachable!();
    };
    *id = no_view_set.old;
    let error = no_view_set.backend.add_rule(invalid).unwrap_err();
    assert!(!error.to_string().contains("scalar-mixed"));
    assert_eq!(
        no_view_set
            .backend
            .add_rule(no_view_set.scalar_rule("valid after unselected head"))?,
        RuleId::new(0)
    );

    let mut empty = Fixture::new(EGraph::new()?, "duckdb empty body")?;
    let mut invalid = empty.scalar_rule("unselected empty body");
    invalid.core.body.atoms.clear();
    let error = empty.backend.add_rule(invalid).unwrap_err();
    assert!(error.to_string().contains("empty body"));
    assert!(!error.to_string().contains("scalar-mixed"));
    assert_eq!(
        empty
            .backend
            .add_rule(empty.scalar_rule("valid after empty body"))?,
        RuleId::new(0)
    );
    Ok(())
}

fn execute_single_deferred_set<B: Backend>(fixture: &mut Fixture<B>) -> Result<Vec<Vec<Value>>> {
    fixture
        .backend
        .add_values(vec![(fixture.old, vec![Value::new(7), Value::new(70)])])?;
    let rule = fixture.backend.add_rule(single_deferred_view_rule(
        fixture.old,
        fixture.view,
        "single Set deferred ordered-union rule",
    ))?;
    assert!(
        fixture
            .backend
            .run_rules(RuleSetRun {
                name: Some("single Set deferred ordered-union schedule"),
                rules: &[rule],
            })?
            .changed()
    );
    Ok(scan_values(&fixture.backend, fixture.view))
}

#[test]
fn single_set_deferred_ordered_union_matches_reference() -> Result<()> {
    let mut reference = Fixture::new(
        egglog_bridge::EGraph::default(),
        "reference single deferred Set",
    )?;
    let mut duckdb = Fixture::new(EGraph::new()?, "duckdb single deferred Set")?;
    let expected = vec![vec![
        Value::new(7),
        Value::new(70),
        Value::new(7),
        Value::new(70),
    ]];
    assert_eq!(execute_single_deferred_set(&mut reference)?, expected);
    assert_eq!(execute_single_deferred_set(&mut duckdb)?, expected);
    assert_eq!(duckdb.backend.last_rule_match_counts(), &[1]);
    Ok(())
}

#[derive(Debug, Eq, PartialEq)]
struct TwoGraphTranscript {
    first_sym: Vec<Vec<u32>>,
    first_trans: Vec<Vec<u32>>,
    first_view: Vec<Vec<u32>>,
    first_uf: Vec<Vec<u32>>,
    second_sym: Vec<Vec<u32>>,
    second_trans: Vec<Vec<u32>>,
    second_view: Vec<Vec<u32>>,
    second_uf: Vec<Vec<u32>>,
    next_fresh: u32,
}

fn execute_two_independent_graphs<B: Backend>(
    backend: B,
    prefix: &str,
) -> Result<TwoGraphTranscript> {
    let mut first = Fixture::new(backend, &format!("{prefix} first graph"))?;
    first.advance_fresh_to_100();
    let first_old = first.old;
    let first_view = first.view;
    let first_sym = first.sym;
    let first_trans = first.trans;
    let first_uf = first.uf;
    let first_unit = first.unit_value;
    let first_rule = single_deferred_view_rule(first_old, first_view, "first deferred graph");

    let mut second = Fixture::new(first.backend, &format!("{prefix} second graph"))?;
    second.backend.add_values(vec![
        (first_old, vec![Value::new(1), Value::new(10)]),
        (
            first_view,
            vec![
                Value::new(1),
                Value::new(10),
                Value::new(30),
                Value::new(70),
            ],
        ),
        (second.old, vec![Value::new(2), Value::new(20)]),
        (
            second.view,
            vec![
                Value::new(2),
                Value::new(20),
                Value::new(40),
                Value::new(80),
            ],
        ),
    ])?;
    let first_rule = second.backend.add_rule(first_rule)?;
    let second_rule = second.backend.add_rule(single_deferred_view_rule(
        second.old,
        second.view,
        "second deferred graph",
    ))?;
    assert!(
        second
            .backend
            .run_rules(RuleSetRun {
                name: Some("two independent ordered-union graphs"),
                rules: &[second_rule, first_rule],
            })?
            .changed()
    );

    Ok(TwoGraphTranscript {
        first_sym: id_rows(&second.backend, first_sym, true, first_unit),
        first_trans: id_rows(&second.backend, first_trans, true, first_unit),
        first_view: id_rows(&second.backend, first_view, false, first_unit),
        first_uf: id_rows(&second.backend, first_uf, false, first_unit),
        second_sym: id_rows(&second.backend, second.sym, true, second.unit_value),
        second_trans: id_rows(&second.backend, second.trans, true, second.unit_value),
        second_view: id_rows(&second.backend, second.view, false, second.unit_value),
        second_uf: id_rows(&second.backend, second.uf, false, second.unit_value),
        next_fresh: second.backend.fresh_id().rep(),
    })
}

#[test]
fn two_independent_ordered_union_graphs_share_one_scalar_schedule() -> Result<()> {
    let reference = execute_two_independent_graphs(
        egglog_bridge::EGraph::default(),
        "reference two-graph schedule",
    )?;
    let duckdb = execute_two_independent_graphs(EGraph::new()?, "duckdb two-graph schedule")?;
    assert_eq!(duckdb, reference);

    // The higher FunctionIds were deliberately scheduled first, so collision
    // fresh ids prove queue order follows the scalar schedule, not target ids.
    assert_eq!(duckdb.second_sym, vec![vec![20, 100]]);
    assert_eq!(duckdb.second_trans, vec![vec![80, 100, 101]]);
    assert_eq!(duckdb.second_uf, vec![vec![40, 2, 101]]);
    assert_eq!(duckdb.first_sym, vec![vec![10, 102]]);
    assert_eq!(duckdb.first_trans, vec![vec![70, 102, 103]]);
    assert_eq!(duckdb.first_uf, vec![vec![30, 1, 103]]);
    assert_eq!(duckdb.next_fresh, 104);
    Ok(())
}
