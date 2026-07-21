use super::*;

pub(super) fn bigint_from_term(termdag: &TermDag, term: TermId) -> Option<BigInt> {
    let Term::App(name, args) = termdag.get(term) else {
        return None;
    };
    if name != "from-string" || args.len() != 1 {
        return None;
    }
    let Term::Lit(Literal::String(value)) = termdag.get(args[0]) else {
        return None;
    };
    value.parse().ok()
}

pub(super) fn bigint_term(termdag: &mut TermDag, value: BigInt) -> TermId {
    let value = termdag.lit(Literal::String(value.to_string()));
    termdag.app("from-string".to_owned(), vec![value])
}

fn bigint_binary_validator(
    termdag: &mut TermDag,
    args: &[TermId],
    operation: impl FnOnce(BigInt, BigInt) -> Option<BigInt>,
) -> Option<TermId> {
    let [a, b] = args else { return None };
    let result = operation(
        bigint_from_term(termdag, *a)?,
        bigint_from_term(termdag, *b)?,
    )?;
    Some(bigint_term(termdag, result))
}

fn bigint_compare_validator(
    termdag: &mut TermDag,
    args: &[TermId],
    predicate: impl FnOnce(&BigInt, &BigInt) -> bool,
) -> Option<TermId> {
    let [a, b] = args else { return None };
    let a = bigint_from_term(termdag, *a)?;
    let b = bigint_from_term(termdag, *b)?;
    predicate(&a, &b).then(|| termdag.lit(Literal::Unit))
}

#[derive(Debug)]
pub struct BigIntSort;

impl BaseSort for BigIntSort {
    type Base = Z;

    fn name(&self) -> &str {
        "BigInt"
    }

    #[rustfmt::skip]
    fn register_primitives(&self, eg: &mut EGraph) {
        let bigint_validator = |termdag: &mut TermDag, args: &[TermId]| -> Option<TermId> {
            let [arg] = args else { return None };
            let Term::Lit(Literal::Int(value)) = termdag.get(*arg) else { return None };
            Some(bigint_term(termdag, (*value).into()))
        };
        let add_validator = |dag: &mut TermDag, args: &[TermId]| bigint_binary_validator(dag, args, |a, b| Some(a + b));
        let sub_validator = |dag: &mut TermDag, args: &[TermId]| bigint_binary_validator(dag, args, |a, b| Some(a - b));
        let mul_validator = |dag: &mut TermDag, args: &[TermId]| bigint_binary_validator(dag, args, |a, b| Some(a * b));
        let div_validator = |dag: &mut TermDag, args: &[TermId]| bigint_binary_validator(dag, args, |a, b| (!b.is_zero()).then(|| a / b));
        let min_validator = |dag: &mut TermDag, args: &[TermId]| bigint_binary_validator(dag, args, |a, b| Some(a.min(b)));
        let max_validator = |dag: &mut TermDag, args: &[TermId]| bigint_binary_validator(dag, args, |a, b| Some(a.max(b)));
        let lt_validator = |dag: &mut TermDag, args: &[TermId]| bigint_compare_validator(dag, args, |a, b| a < b);
        let gt_validator = |dag: &mut TermDag, args: &[TermId]| bigint_compare_validator(dag, args, |a, b| a > b);

        add_replayable_primitive_with_validator!(eg, "bigint" = |a: i64| -> Z { Z::new(a.into()) }, bigint_validator);

        add_replayable_primitive_with_validator!(eg, "+" = |a: Z, b: Z| -> Z { a + b }, add_validator);
        add_replayable_primitive_with_validator!(eg, "-" = |a: Z, b: Z| -> Z { a - b }, sub_validator);
        add_replayable_primitive_with_validator!(eg, "*" = |a: Z, b: Z| -> Z { a * b }, mul_validator);
        add_replayable_primitive_with_validator!(eg, "/" = |a: Z, b: Z| -?> Z { (*b != BigInt::ZERO).then(|| a / b) }, div_validator);
        add_primitive!(eg, "%" = |a: Z, b: Z| -?> Z { (*b != BigInt::ZERO).then(|| a % b) });

        add_primitive!(eg, "&" = |a: Z, b: Z| -> Z { a & b });
        add_primitive!(eg, "|" = |a: Z, b: Z| -> Z { a | b });
        add_primitive!(eg, "^" = |a: Z, b: Z| -> Z { a ^ b });
        add_primitive!(eg, "<<" = |a: Z, b: i64| -> Z { (&*a).shl(b).into() });
        add_primitive!(eg, ">>" = |a: Z, b: i64| -> Z { (&*a).shr(b).into() });
        add_primitive!(eg, "not-Z" = |a: Z| -> Z { Z::new(!&*a) });

        add_primitive!(eg, "bits" = |a: Z| -> Z { Z::new(a.bits().into()) });

        add_replayable_primitive_with_validator!(eg, "<" = |a: Z, b: Z| -?> () { (a < b).then_some(()) }, lt_validator);
        add_replayable_primitive_with_validator!(eg, ">" = |a: Z, b: Z| -?> () { (a > b).then_some(()) }, gt_validator);
        add_primitive!(eg, "<=" = |a: Z, b: Z| -?> () { (a <= b).then_some(()) });
        add_primitive!(eg, ">=" = |a: Z, b: Z| -?> () { (a >= b).then_some(()) });

        add_primitive!(eg, "bool-=" = |a: Z, b: Z| -> bool { a == b });
        add_primitive!(eg, "bool-<" = |a: Z, b: Z| -> bool { a < b });
        add_primitive!(eg, "bool->" = |a: Z, b: Z| -> bool { a > b });
        add_primitive!(eg, "bool-<=" = |a: Z, b: Z| -> bool { a <= b });
        add_primitive!(eg, "bool->=" = |a: Z, b: Z| -> bool { a >= b });

        add_replayable_primitive_with_validator!(eg, "min" = |a: Z, b: Z| -> Z { a.min(b) }, min_validator);
        add_replayable_primitive_with_validator!(eg, "max" = |a: Z, b: Z| -> Z { a.max(b) }, max_validator);

        add_primitive!(eg, "to-string" = |a: Z| -> S { S::new(a.to_string()) });
        add_primitive!(eg, "from-string" = |a: S| -?> Z {
            a.as_str().parse::<BigInt>().ok().map(Z::new)
        });
    }

    fn reconstruct_termdag(
        &self,
        base_values: &BaseValues,
        value: Value,
        termdag: &mut TermDag,
    ) -> TermId {
        let bigint = base_values.unwrap::<Z>(value);
        bigint_term(termdag, bigint.0.clone())
    }
}
