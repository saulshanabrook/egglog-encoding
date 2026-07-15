use super::*;

fn bigrat_from_term(termdag: &TermDag, term: TermId) -> Option<BigRational> {
    let Term::App(name, args) = termdag.get(term) else {
        return None;
    };
    if name != "bigrat" || args.len() != 2 {
        return None;
    }
    let numer = bigint::bigint_from_term(termdag, args[0])?;
    let denom = bigint::bigint_from_term(termdag, args[1])?;
    (!denom.is_zero()).then(|| BigRational::new(numer, denom))
}

fn bigrat_term(termdag: &mut TermDag, value: BigRational) -> TermId {
    let numer = bigint::bigint_term(termdag, value.numer().clone());
    let denom = bigint::bigint_term(termdag, value.denom().clone());
    termdag.app("bigrat".to_owned(), vec![numer, denom])
}

fn bigrat_binary_validator(
    termdag: &mut TermDag,
    args: &[TermId],
    operation: impl FnOnce(BigRational, BigRational) -> Option<BigRational>,
) -> Option<TermId> {
    let [a, b] = args else { return None };
    let result = operation(
        bigrat_from_term(termdag, *a)?,
        bigrat_from_term(termdag, *b)?,
    )?;
    Some(bigrat_term(termdag, result))
}

fn bigrat_unary_validator(
    termdag: &mut TermDag,
    args: &[TermId],
    operation: impl FnOnce(BigRational) -> Option<BigRational>,
) -> Option<TermId> {
    let [a] = args else { return None };
    let result = operation(bigrat_from_term(termdag, *a)?)?;
    Some(bigrat_term(termdag, result))
}

fn bigrat_compare_validator(
    termdag: &mut TermDag,
    args: &[TermId],
    predicate: impl FnOnce(&BigRational, &BigRational) -> bool,
) -> Option<TermId> {
    let [a, b] = args else { return None };
    let a = bigrat_from_term(termdag, *a)?;
    let b = bigrat_from_term(termdag, *b)?;
    predicate(&a, &b).then(|| termdag.lit(Literal::Unit))
}

fn checked_bigrat_pow(a: Q, b: Q) -> Option<Q> {
    if !b.is_integer() {
        None
    } else if a.is_zero() {
        if b.is_zero() {
            Some(BigRational::one().into())
        } else if b.is_positive() {
            Some(BigRational::zero().into())
        } else {
            None
        }
    } else {
        let (base, exponent) = if b.is_negative() {
            (Q::new(a.recip()), Q::new(b.abs()))
        } else {
            (a, b)
        };
        let exponent = usize::try_from(exponent.to_i64()?).ok()?;
        num::traits::checked_pow(base.into_inner(), exponent).map(Q::new)
    }
}

fn checked_bigrat_log(a: Q) -> Option<Q> {
    a.is_one().then(|| Q::new(BigRational::zero()))
}

/// Rational numbers supporting these primitives:
/// - Arithmetic: `+`, `-`, `*`, `/`, `neg`, `abs`
/// - Exponential: `pow`, `log`, `sqrt`, `cbrt`
/// - Rounding: `floor`, `ceil`, `round`
/// - Con/Destruction: `bigrat`, `numer`, `denom`
/// - Comparisons: `<`, `>`, `<=`, `>=`
/// - Other: `min`, `max`, `to-f64`, `to-i64`
#[derive(Debug)]
pub struct BigRatSort;

impl BaseSort for BigRatSort {
    type Base = Q;

    fn name(&self) -> &str {
        "BigRat"
    }

    #[rustfmt::skip]
    fn register_primitives(&self, eg: &mut EGraph) {
        let add_validator = |dag: &mut TermDag, args: &[TermId]| bigrat_binary_validator(dag, args, |a, b| a.checked_add(&b));
        let sub_validator = |dag: &mut TermDag, args: &[TermId]| bigrat_binary_validator(dag, args, |a, b| a.checked_sub(&b));
        let mul_validator = |dag: &mut TermDag, args: &[TermId]| bigrat_binary_validator(dag, args, |a, b| a.checked_mul(&b));
        let div_validator = |dag: &mut TermDag, args: &[TermId]| bigrat_binary_validator(dag, args, |a, b| a.checked_div(&b));
        let min_validator = |dag: &mut TermDag, args: &[TermId]| bigrat_binary_validator(dag, args, |a, b| Some(a.min(b)));
        let max_validator = |dag: &mut TermDag, args: &[TermId]| bigrat_binary_validator(dag, args, |a, b| Some(a.max(b)));
        let neg_validator = |dag: &mut TermDag, args: &[TermId]| bigrat_unary_validator(dag, args, |a| Some(-a));
        let abs_validator = |dag: &mut TermDag, args: &[TermId]| bigrat_unary_validator(dag, args, |a| Some(a.abs()));
        let floor_validator = |dag: &mut TermDag, args: &[TermId]| bigrat_unary_validator(dag, args, |a| Some(a.floor()));
        let ceil_validator = |dag: &mut TermDag, args: &[TermId]| bigrat_unary_validator(dag, args, |a| Some(a.ceil()));
        let round_validator = |dag: &mut TermDag, args: &[TermId]| bigrat_unary_validator(dag, args, |a| Some(a.round()));
        let bigrat_validator = |dag: &mut TermDag, args: &[TermId]| -> Option<TermId> {
            let [numer, denom] = args else { return None };
            let numer = bigint::bigint_from_term(dag, *numer)?;
            let denom = bigint::bigint_from_term(dag, *denom)?;
            (!denom.is_zero()).then(|| bigrat_term(dag, BigRational::new(numer, denom)))
        };
        let pow_validator = |dag: &mut TermDag, args: &[TermId]| bigrat_binary_validator(dag, args, |a, b| checked_bigrat_pow(Q::new(a), Q::new(b)).map(Q::into_inner));
        let log_validator = |dag: &mut TermDag, args: &[TermId]| bigrat_unary_validator(dag, args, |a| checked_bigrat_log(Q::new(a)).map(Q::into_inner));
        let lt_validator = |dag: &mut TermDag, args: &[TermId]| bigrat_compare_validator(dag, args, |a, b| a < b);
        let gt_validator = |dag: &mut TermDag, args: &[TermId]| bigrat_compare_validator(dag, args, |a, b| a > b);

        add_primitive_with_validator!(eg, "+" = |a: Q, b: Q| -?> Q { a.checked_add(&b).map(Q::new) }, add_validator);
        add_primitive_with_validator!(eg, "-" = |a: Q, b: Q| -?> Q { a.checked_sub(&b).map(Q::new) }, sub_validator);
        add_primitive_with_validator!(eg, "*" = |a: Q, b: Q| -?> Q { a.checked_mul(&b).map(Q::new) }, mul_validator);
        add_primitive_with_validator!(eg, "/" = |a: Q, b: Q| -?> Q { a.checked_div(&b).map(Q::new) }, div_validator);

        add_primitive_with_validator!(eg, "min" = |a: Q, b: Q| -> Q { a.min(b) }, min_validator);
        add_primitive_with_validator!(eg, "max" = |a: Q, b: Q| -> Q { a.max(b) }, max_validator);
        add_primitive_with_validator!(eg, "neg" = |a: Q| -> Q { Q::new(-a.0) }, neg_validator);
        add_primitive_with_validator!(eg, "abs" = |a: Q| -> Q { Q::new(a.0.abs()) }, abs_validator);
        add_primitive_with_validator!(eg, "floor" = |a: Q| -> Q { Q::new(a.0.floor()) }, floor_validator);
        add_primitive_with_validator!(eg, "ceil" = |a: Q| -> Q { Q::new(a.0.ceil()) }, ceil_validator);
        add_primitive_with_validator!(eg, "round" = |a: Q| -> Q { Q::new(a.round()) }, round_validator);

        add_primitive_with_validator!(eg, "bigrat" = |a: Z, b: Z| -?> Q {
            if b.0.is_zero() {
                None
            } else {
                Some(Q::new(BigRational::new(a.0, b.0)))
            }
        }, bigrat_validator);
        add_primitive!(eg, "numer" = |a: Q| -> Z { Z::new(a.numer().clone()) });
        add_primitive!(eg, "denom" = |a: Q| -> Z { Z::new(a.denom().clone()) });
        add_primitive!(eg, "to-f64" = |a: Q| -> F { F::new(OrderedFloat(a.to_f64().unwrap())) });
        add_primitive!(eg, "to-i64" = |a: Q| -?> i64 { a.is_integer().then(|| a.to_integer()).and_then(|a| a.to_i64()) });

        add_primitive_with_validator!(eg, "pow" = |a: Q, b: Q| -?> Q { checked_bigrat_pow(a, b) }, pow_validator);
        add_primitive_with_validator!(eg, "log" = |a: Q| -?> Q { checked_bigrat_log(a) }, log_validator);
        add_primitive!(eg, "sqrt" = |a: Q| -?> Q {
            if a.numer().is_positive() && a.denom().is_positive() {
                let s1 = a.numer().sqrt();
                let s2 = a.denom().sqrt();
                let is_perfect = &(s1.clone() * s1.clone()) == a.numer() && &(s2.clone() * s2.clone()) == a.denom();
                if is_perfect {
                    Some(Q::new(BigRational::new(s1, s2)))
                } else {
                    None
                }
            } else {
                None
            }
        });
        add_primitive!(eg, "cbrt" = |a: Q| -?> Q {
            if a.is_one() {
                Some(Q::new(BigRational::one()))
            } else {
                todo!("cbrt of bigrat")
            }
        });

        add_primitive_with_validator!(eg, "<" = |a: Q, b: Q| -?> () { if a < b {Some(())} else {None} }, lt_validator);
        add_primitive_with_validator!(eg, ">" = |a: Q, b: Q| -?> () { if a > b {Some(())} else {None} }, gt_validator);
        add_primitive!(eg, "<=" = |a: Q, b: Q| -?> () { if a <= b {Some(())} else {None} });
        add_primitive!(eg, ">=" = |a: Q, b: Q| -?> () { if a >= b {Some(())} else {None} });
    }

    fn reconstruct_termdag(
        &self,
        base_values: &BaseValues,
        value: Value,
        termdag: &mut TermDag,
    ) -> TermId {
        let rat = base_values.unwrap::<Q>(value);
        bigrat_term(termdag, rat.0.clone())
    }
}

#[cfg(test)]
mod tests {
    use std::panic::{AssertUnwindSafe, catch_unwind};

    use super::*;

    #[test]
    fn unsupported_logarithm_is_partial() {
        assert!(checked_bigrat_log(Q::new(BigRational::from_integer(2.into()))).is_none());
    }

    #[test]
    fn zero_denominator_is_partial() {
        let result = catch_unwind(AssertUnwindSafe(|| {
            EGraph::default()
                .parse_and_run_program(None, r#"(let $invalid (bigrat (bigint 1) (bigint 0)))"#)
        }));

        assert!(
            result.is_ok(),
            "bigrat must not panic on a zero denominator"
        );
        assert!(result.unwrap().is_err());
    }
}
