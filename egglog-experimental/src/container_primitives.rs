use crate::either::{EitherContainer, EitherData, EitherSort};
use crate::maybe::{MaybeContainer, maybe_sorts};
use egglog::ast::{Literal, Span};
use egglog::constraint::{self, Constraint, TypeConstraint};
use egglog::prelude::{BaseSort, BoolSort, I64Sort};
use egglog::sort::{PairContainer, PairSort};
use egglog::{
    ArcSort, Atom, AtomTerm, Core, EGraph, Primitive, PurePrim, PureState, Term, TermDag, TermId,
    TypeInfo, Value,
};
use std::sync::Arc;

type TypeConstraints = Vec<Box<dyn Constraint<AtomTerm, ArcSort>>>;
type ConstraintChoice = Vec<Box<dyn Constraint<AtomTerm, ArcSort>>>;

pub fn add_container_primitives(egraph: &mut EGraph) {
    egraph.add_pure_primitive(
        PairMinBySecondI64,
        Some(Arc::new(validate_pair_min_by_second_i64)),
    );
    egraph.add_pure_primitive(
        MaybeEitherI64BoolMin,
        Some(Arc::new(validate_maybe_either_i64_bool_min)),
    );
    egraph.add_pure_primitive(
        MaybeEitherI64BoolMax,
        Some(Arc::new(validate_maybe_either_i64_bool_max)),
    );
}

fn arity_mismatch(
    name: &str,
    span: &Span,
    arguments: &[AtomTerm],
    expected: usize,
) -> TypeConstraints {
    vec![constraint::impossible(
        constraint::ImpossibleConstraint::ArityMismatch {
            atom: Atom {
                span: span.clone(),
                head: name.to_owned(),
                args: arguments.to_vec(),
            },
            expected,
        },
    )]
}

fn choose(choices: Vec<ConstraintChoice>) -> TypeConstraints {
    match choices.len() {
        0 => vec![constraint::xor(vec![])],
        1 => choices.into_iter().next().unwrap(),
        _ => vec![constraint::xor(
            choices.into_iter().map(constraint::and).collect(),
        )],
    }
}

fn assign_all(arguments: &[AtomTerm], sorts: &[ArcSort]) -> ConstraintChoice {
    arguments
        .iter()
        .cloned()
        .zip(sorts.iter().cloned())
        .map(|(argument, sort)| constraint::assign(argument, sort))
        .collect()
}

#[derive(Clone)]
struct PairMinBySecondI64;

impl Primitive for PairMinBySecondI64 {
    fn name(&self) -> &str {
        "pair-min-by-second-i64"
    }

    fn get_type_constraints(&self, span: &Span) -> Box<dyn TypeConstraint> {
        Box::new(PairI64SameSortTypeConstraint {
            name: self.name().to_owned(),
            span: span.clone(),
        })
    }
}

impl PurePrim for PairMinBySecondI64 {
    fn apply<'a, 'db>(&self, state: PureState<'a, 'db>, args: &[Value]) -> Option<Value> {
        let old = state
            .container_values()
            .get_val::<PairContainer>(args[0])?
            .clone();
        let new = state
            .container_values()
            .get_val::<PairContainer>(args[1])?
            .clone();
        let old_cost = state.base_values().unwrap::<i64>(old.second);
        let new_cost = state.base_values().unwrap::<i64>(new.second);

        if old_cost <= new_cost {
            Some(args[0])
        } else {
            Some(args[1])
        }
    }
}

struct PairI64SameSortTypeConstraint {
    name: String,
    span: Span,
}

impl TypeConstraint for PairI64SameSortTypeConstraint {
    fn get(&self, arguments: &[AtomTerm], typeinfo: &TypeInfo) -> TypeConstraints {
        if arguments.len() != 3 {
            return arity_mismatch(&self.name, &self.span, arguments, 3);
        }

        let choices = pair_i64_sorts(typeinfo)
            .into_iter()
            .map(|sort| assign_all(arguments, &[sort.clone(), sort.clone(), sort]))
            .collect();
        choose(choices)
    }
}

#[derive(Clone)]
struct MaybeEitherI64BoolMin;

impl Primitive for MaybeEitherI64BoolMin {
    fn name(&self) -> &str {
        "maybe-either-i64-bool-min"
    }

    fn get_type_constraints(&self, span: &Span) -> Box<dyn TypeConstraint> {
        Box::new(BoundSameSortTypeConstraint {
            name: self.name().to_owned(),
            span: span.clone(),
        })
    }
}

impl PurePrim for MaybeEitherI64BoolMin {
    fn apply<'a, 'db>(&self, state: PureState<'a, 'db>, args: &[Value]) -> Option<Value> {
        bound_merge(state, args, BoundMergeKind::Min)
    }
}

#[derive(Clone)]
struct MaybeEitherI64BoolMax;

impl Primitive for MaybeEitherI64BoolMax {
    fn name(&self) -> &str {
        "maybe-either-i64-bool-max"
    }

    fn get_type_constraints(&self, span: &Span) -> Box<dyn TypeConstraint> {
        Box::new(BoundSameSortTypeConstraint {
            name: self.name().to_owned(),
            span: span.clone(),
        })
    }
}

impl PurePrim for MaybeEitherI64BoolMax {
    fn apply<'a, 'db>(&self, state: PureState<'a, 'db>, args: &[Value]) -> Option<Value> {
        bound_merge(state, args, BoundMergeKind::Max)
    }
}

struct BoundSameSortTypeConstraint {
    name: String,
    span: Span,
}

impl TypeConstraint for BoundSameSortTypeConstraint {
    fn get(&self, arguments: &[AtomTerm], typeinfo: &TypeInfo) -> TypeConstraints {
        if arguments.len() != 3 {
            return arity_mismatch(&self.name, &self.span, arguments, 3);
        }

        let choices = bound_sorts(typeinfo)
            .into_iter()
            .map(|sort| assign_all(arguments, &[sort.clone(), sort.clone(), sort]))
            .collect();
        choose(choices)
    }
}

#[derive(Clone, Copy)]
enum BoundMergeKind {
    Min,
    Max,
}

impl BoundMergeKind {
    fn keep_i64_old(self, old: i64, new: i64) -> bool {
        match self {
            BoundMergeKind::Min => old <= new,
            BoundMergeKind::Max => old >= new,
        }
    }

    fn keep_bool_old(self, old: bool, new: bool) -> bool {
        match self {
            BoundMergeKind::Min => !old || new,
            BoundMergeKind::Max => old || !new,
        }
    }
}

fn bound_merge<'a, 'db>(
    state: PureState<'a, 'db>,
    args: &[Value],
    kind: BoundMergeKind,
) -> Option<Value> {
    let old = state
        .container_values()
        .get_val::<MaybeContainer>(args[0])?
        .clone();
    let new = state
        .container_values()
        .get_val::<MaybeContainer>(args[1])?
        .clone();

    let (Some(old_value), Some(new_value)) = (old.data, new.data) else {
        return match (old.data, new.data) {
            (None, _) => Some(args[0]),
            (_, None) => Some(args[1]),
            _ => unreachable!(),
        };
    };

    let old = state
        .container_values()
        .get_val::<EitherContainer>(old_value)?
        .clone();
    let new = state
        .container_values()
        .get_val::<EitherContainer>(new_value)?
        .clone();

    match (old.data, new.data) {
        (EitherData::Left(old_int), EitherData::Left(new_int)) => {
            let old_int = state.base_values().unwrap::<i64>(old_int);
            let new_int = state.base_values().unwrap::<i64>(new_int);
            let keep_old = kind.keep_i64_old(old_int, new_int);
            Some(if keep_old { args[0] } else { args[1] })
        }
        (EitherData::Right(old_bool), EitherData::Right(new_bool)) => {
            let old_bool = state.base_values().unwrap::<bool>(old_bool);
            let new_bool = state.base_values().unwrap::<bool>(new_bool);
            let keep_old = kind.keep_bool_old(old_bool, new_bool);
            Some(if keep_old { args[0] } else { args[1] })
        }
        _ => None,
    }
}

fn pair_i64_sorts(type_info: &TypeInfo) -> Vec<ArcSort> {
    let i64_sort = I64Sort.to_arcsort();
    type_info
        .get_arcsorts_by_presort::<PairSort>()
        .into_iter()
        .filter(|sort| {
            let inner_sorts = sort.inner_sorts();
            inner_sorts
                .get(1)
                .is_some_and(|second| type_info.same_sort(second, &i64_sort))
        })
        .collect()
}

fn bound_sorts(type_info: &TypeInfo) -> Vec<ArcSort> {
    let i64_sort = I64Sort.to_arcsort();
    let bool_sort = BoolSort.to_arcsort();
    maybe_sorts(type_info)
        .into_iter()
        .filter_map(|(sort, element)| {
            if !type_info.is_sort_from_presort::<EitherSort>(&element) {
                return None;
            }
            let inner_sorts = element.inner_sorts();
            let [left, right] = inner_sorts.as_slice() else {
                return None;
            };
            (type_info.same_sort(left, &i64_sort) && type_info.same_sort(right, &bool_sort))
                .then_some(sort)
        })
        .collect()
}

fn validate_pair_min_by_second_i64(termdag: &mut TermDag, args: &[TermId]) -> Option<TermId> {
    let [old, new] = args else {
        return None;
    };
    let old_cost = pair_second_i64(termdag, *old)?;
    let new_cost = pair_second_i64(termdag, *new)?;
    Some(if old_cost <= new_cost { *old } else { *new })
}

fn pair_second_i64(termdag: &TermDag, term: TermId) -> Option<i64> {
    match termdag.get(term) {
        Term::App(head, children) if head == "pair" && children.len() == 2 => {
            match termdag.get(children[1]) {
                Term::Lit(Literal::Int(value)) => Some(*value),
                _ => None,
            }
        }
        _ => None,
    }
}

fn validate_maybe_either_i64_bool_min(termdag: &mut TermDag, args: &[TermId]) -> Option<TermId> {
    validate_maybe_either_i64_bool_merge(termdag, args, BoundMergeKind::Min)
}

fn validate_maybe_either_i64_bool_max(termdag: &mut TermDag, args: &[TermId]) -> Option<TermId> {
    validate_maybe_either_i64_bool_merge(termdag, args, BoundMergeKind::Max)
}

fn validate_maybe_either_i64_bool_merge(
    termdag: &mut TermDag,
    args: &[TermId],
    kind: BoundMergeKind,
) -> Option<TermId> {
    let [old, new] = args else {
        return None;
    };
    match (bound_term(termdag, *old)?, bound_term(termdag, *new)?) {
        (BoundTerm::Dead, _) => Some(*old),
        (_, BoundTerm::Dead) => Some(*new),
        (BoundTerm::Int(old_int), BoundTerm::Int(new_int)) => {
            let keep_old = kind.keep_i64_old(old_int, new_int);
            Some(if keep_old { *old } else { *new })
        }
        (BoundTerm::Bool(old_bool), BoundTerm::Bool(new_bool)) => {
            let keep_old = kind.keep_bool_old(old_bool, new_bool);
            Some(if keep_old { *old } else { *new })
        }
        _ => None,
    }
}

enum BoundTerm {
    Dead,
    Int(i64),
    Bool(bool),
}

fn bound_term(termdag: &TermDag, term: TermId) -> Option<BoundTerm> {
    match termdag.get(term) {
        Term::App(head, children) if head == "maybe-none" && children.is_empty() => {
            Some(BoundTerm::Dead)
        }
        _ => {
            if let Some(value) = bound_int_term(termdag, term) {
                match termdag.get(value) {
                    Term::Lit(Literal::Int(value)) => Some(BoundTerm::Int(*value)),
                    _ => None,
                }
            } else if let Some(value) = bound_bool_term(termdag, term) {
                match termdag.get(value) {
                    Term::Lit(Literal::Bool(value)) => Some(BoundTerm::Bool(*value)),
                    _ => None,
                }
            } else {
                None
            }
        }
    }
}

fn bound_int_term(termdag: &TermDag, term: TermId) -> Option<TermId> {
    match termdag.get(term) {
        Term::App(head, children) if head == "maybe-some" && children.len() == 1 => {
            match termdag.get(children[0]) {
                Term::App(head, children) if head == "either-left" && children.len() == 1 => {
                    Some(children[0])
                }
                _ => None,
            }
        }
        _ => None,
    }
}

fn bound_bool_term(termdag: &TermDag, term: TermId) -> Option<TermId> {
    match termdag.get(term) {
        Term::App(head, children) if head == "maybe-some" && children.len() == 1 => {
            match termdag.get(children[0]) {
                Term::App(head, children) if head == "either-right" && children.len() == 1 => {
                    Some(children[0])
                }
                _ => None,
            }
        }
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{MaybeSort, new_experimental_egraph};
    use egglog::Error;
    use egglog::prelude::ContainerSort;
    use egglog::sort::{ContainerValues, EqSort};

    #[derive(Clone, Debug)]
    struct MaybeStorageDecoySort {
        name: String,
        element: ArcSort,
    }

    impl ContainerSort for MaybeStorageDecoySort {
        type Container = MaybeContainer;

        fn name(&self) -> &str {
            &self.name
        }

        fn is_eq_container_sort(&self) -> bool {
            self.element.is_eq_sort() || self.element.is_eq_container_sort()
        }

        fn inner_sorts(&self) -> Vec<ArcSort> {
            vec![self.element.clone()]
        }

        fn inner_values(
            &self,
            container_values: &ContainerValues,
            value: Value,
        ) -> Vec<(ArcSort, Value)> {
            container_values
                .get_val::<MaybeContainer>(value)
                .unwrap()
                .data
                .iter()
                .map(|value| (self.element.clone(), *value))
                .collect()
        }

        fn reconstruct_termdag(
            &self,
            _container_values: &ContainerValues,
            _value: Value,
            _termdag: &mut TermDag,
            _element_terms: Vec<TermId>,
        ) -> TermId {
            unreachable!("the authority decoy never reaches reconstruction")
        }

        fn serialized_name(&self, _container_values: &ContainerValues, _value: Value) -> String {
            self.name.clone()
        }
    }

    #[test]
    fn bound_specialization_requires_exact_maybe_and_either_presort_authority() {
        let mut egraph = new_experimental_egraph();
        egraph
            .parse_and_run_program(
                None,
                r#"
                (sort BoundValue (Either i64 bool))
                (sort Bound (Maybe BoundValue))
                (function best () Bound :merge (maybe-either-i64-bool-min old new))
                (set (best) (maybe-some (either-left 7)))
                (set (best) (maybe-some (either-left 3)))
                (check (= (best) (maybe-some (either-left 3))))
                "#,
            )
            .unwrap();

        let bound = egraph.get_sort_by_name("Bound").unwrap().clone();
        let bound_value = egraph.get_sort_by_name("BoundValue").unwrap().clone();
        assert!(egraph.type_info().is_sort_from_presort::<MaybeSort>(&bound));
        assert!(
            egraph
                .type_info()
                .is_sort_from_presort::<EitherSort>(&bound_value)
        );

        let storage_decoy = MaybeStorageDecoySort {
            name: "BoundStorageDecoy".to_owned(),
            element: bound_value,
        }
        .to_arcsort();
        egraph
            .add_arcsort(storage_decoy.clone(), egglog::span!())
            .unwrap();
        assert!(
            !egraph
                .type_info()
                .is_sort_from_presort::<MaybeSort>(&storage_decoy)
        );
        let same_name_decoy: ArcSort = Arc::new(EqSort {
            name: "Bound".to_owned(),
        });
        assert!(
            !egraph
                .type_info()
                .is_sort_from_presort::<MaybeSort>(&same_name_decoy)
        );

        let error = egraph
            .parse_and_run_program(
                None,
                "(function rejected () BoundStorageDecoy :merge (maybe-either-i64-bool-min old new))",
            )
            .unwrap_err();
        assert!(matches!(error, Error::TypeError(_)));
    }
}
