use egglog::ast::{Expr, Span};
use egglog::prelude::ContainerSort;
use egglog::sort::{ContainerValues, Presort, ValueRebuilder};
use egglog::{
    ArcSort, ContainerValue, EGraph, TermDag, TermId, TypeError, TypeInfo, Value,
    add_primitive_with_validator,
};
use std::any::TypeId;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
/// The selected alternative of an Either value.
pub enum EitherData {
    /// A value of the left sort.
    Left(Value),
    /// A value of the right sort.
    Right(Value),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
/// A tagged value of one of two sorts, stored in an e-graph.
pub struct EitherContainer {
    /// Whether a left value requires canonicalization during rebuilding.
    pub do_rebuild_left: bool,
    /// Whether a right value requires canonicalization during rebuilding.
    pub do_rebuild_right: bool,
    /// The selected alternative and its value.
    pub data: EitherData,
}

impl ContainerValue for EitherContainer {
    fn rebuild_contents(&mut self, rebuilder: &dyn ValueRebuilder) -> bool {
        match &mut self.data {
            EitherData::Left(value) if self.do_rebuild_left => {
                let old = *value;
                let new = rebuilder.rebuild_val(old);
                *value = new;
                old != new
            }
            EitherData::Right(value) if self.do_rebuild_right => {
                let old = *value;
                let new = rebuilder.rebuild_val(old);
                *value = new;
                old != new
            }
            _ => false,
        }
    }

    fn iter(&self) -> impl Iterator<Item = Value> + '_ {
        match self.data {
            EitherData::Left(value) | EitherData::Right(value) => Some(value).into_iter(),
        }
    }
}

#[derive(Clone, Debug)]
/// A named container sort with left and right alternatives.
pub struct EitherSort {
    name: String,
    left: ArcSort,
    right: ArcSort,
}

impl EitherSort {
    /// Return the sort of left values.
    pub fn left(&self) -> ArcSort {
        self.left.clone()
    }

    /// Return the sort of right values.
    pub fn right(&self) -> ArcSort {
        self.right.clone()
    }
}

impl Presort for EitherSort {
    fn presort_name() -> &'static str {
        "Either"
    }

    fn reserved_primitives() -> Vec<&'static str> {
        vec![
            "either-left",
            "either-right",
            "either-unwrap-left",
            "either-unwrap-right",
        ]
    }

    fn make_sort(
        typeinfo: &mut TypeInfo,
        name: String,
        args: &[Expr],
        span: Span,
    ) -> Result<ArcSort, TypeError> {
        if let [Expr::Var(left_span, left), Expr::Var(right_span, right)] = args {
            let left = typeinfo
                .get_sort_by_name(left)
                .ok_or(TypeError::UndefinedSort(left.clone(), left_span.clone()))?;
            let right = typeinfo
                .get_sort_by_name(right)
                .ok_or(TypeError::UndefinedSort(right.clone(), right_span.clone()))?;

            Ok(Self {
                name,
                left: left.clone(),
                right: right.clone(),
            }
            .to_arcsort())
        } else {
            Err(TypeError::BadPresortArguments(
                Self::presort_name().to_owned(),
                span,
            ))
        }
    }
}

impl ContainerSort for EitherSort {
    type Container = EitherContainer;

    fn name(&self) -> &str {
        &self.name
    }

    fn is_eq_container_sort(&self) -> bool {
        self.left.is_eq_sort()
            || self.right.is_eq_sort()
            || self.left.is_eq_container_sort()
            || self.right.is_eq_container_sort()
    }

    fn inner_sorts(&self) -> Vec<ArcSort> {
        vec![self.left.clone(), self.right.clone()]
    }

    fn inner_values(
        &self,
        container_values: &ContainerValues,
        value: Value,
    ) -> Vec<(ArcSort, Value)> {
        let either = container_values
            .get_val::<EitherContainer>(value)
            .unwrap()
            .clone();
        match either.data {
            EitherData::Left(value) => vec![(self.left.clone(), value)],
            EitherData::Right(value) => vec![(self.right.clone(), value)],
        }
    }

    fn register_primitives(&self, eg: &mut EGraph) {
        let arc = self.clone().to_arcsort();

        add_primitive_with_validator!(
            eg,
            "either-left" = {self.clone(): EitherSort} |left: # (self.left())| -> @EitherContainer (arc) {
                EitherContainer {
                    do_rebuild_left: self.ctx.left.is_eq_sort() || self.ctx.left.is_eq_container_sort(),
                    do_rebuild_right: self.ctx.right.is_eq_sort() || self.ctx.right.is_eq_container_sort(),
                    data: EitherData::Left(left),
                }
            },
            |termdag: &mut TermDag, args: &[TermId]| -> Option<TermId> {
                if args.len() == 1 {
                    Some(termdag.app("either-left".into(), args.to_vec()))
                } else {
                    None
                }
            }
        );

        add_primitive_with_validator!(
            eg,
            "either-right" = {self.clone(): EitherSort} |right: # (self.right())| -> @EitherContainer (arc) {
                EitherContainer {
                    do_rebuild_left: self.ctx.left.is_eq_sort() || self.ctx.left.is_eq_container_sort(),
                    do_rebuild_right: self.ctx.right.is_eq_sort() || self.ctx.right.is_eq_container_sort(),
                    data: EitherData::Right(right),
                }
            },
            |termdag: &mut TermDag, args: &[TermId]| -> Option<TermId> {
                if args.len() == 1 {
                    Some(termdag.app("either-right".into(), args.to_vec()))
                } else {
                    None
                }
            }
        );

        add_primitive_with_validator!(
            eg,
            "either-unwrap-left" = |xs: @EitherContainer (arc)| -?> # (self.left()) {
                match xs.data {
                    EitherData::Left(value) => Some(value),
                    EitherData::Right(_) => None,
                }
            },
            |termdag: &mut TermDag, args: &[TermId]| -> Option<TermId> {
                let [either] = args else {
                    return None;
                };
                match termdag.get(*either) {
                    Term::App(head, children) if head == "either-left" && children.len() == 1 => {
                        Some(children[0])
                    }
                    _ => None,
                }
            }
        );

        add_primitive_with_validator!(
            eg,
            "either-unwrap-right" = |xs: @EitherContainer (arc)| -?> # (self.right()) {
                match xs.data {
                    EitherData::Left(_) => None,
                    EitherData::Right(value) => Some(value),
                }
            },
            |termdag: &mut TermDag, args: &[TermId]| -> Option<TermId> {
                let [either] = args else {
                    return None;
                };
                match termdag.get(*either) {
                    Term::App(head, children) if head == "either-right" && children.len() == 1 => {
                        Some(children[0])
                    }
                    _ => None,
                }
            }
        );
    }

    fn reconstruct_termdag(
        &self,
        container_values: &ContainerValues,
        value: Value,
        termdag: &mut TermDag,
        element_terms: Vec<TermId>,
    ) -> TermId {
        assert_eq!(element_terms.len(), 1);
        let either = container_values.get_val::<EitherContainer>(value).unwrap();
        let head = match either.data {
            EitherData::Left(_) => "either-left",
            EitherData::Right(_) => "either-right",
        };
        termdag.app(head.into(), element_terms)
    }

    fn serialized_name(&self, container_values: &ContainerValues, value: Value) -> String {
        let either = container_values.get_val::<EitherContainer>(value).unwrap();
        match either.data {
            EitherData::Left(_) => "either-left".to_owned(),
            EitherData::Right(_) => "either-right".to_owned(),
        }
    }
}

/// Enumerate registered Either sorts paired with their left and right sorts.
pub fn either_sorts(type_info: &TypeInfo) -> Vec<(ArcSort, ArcSort, ArcSort)> {
    type_info
        .get_arcsorts_by(|sort| sort.value_type() == Some(TypeId::of::<EitherContainer>()))
        .into_iter()
        .filter_map(|sort| {
            let inner_sorts = sort.inner_sorts();
            let [left, right] = inner_sorts.as_slice() else {
                return None;
            };
            Some((sort, left.clone(), right.clone()))
        })
        .collect()
}
