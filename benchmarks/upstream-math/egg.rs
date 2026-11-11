// The original PLDI 2023 artifact Math language, 24 rules, and seven seeds.
// BigRational matches upstream Egglog core's built-in BigRat sort.

use egg::{Rewrite, Symbol, define_language, rewrite as rw};
use num_rational::BigRational;

define_language! {
    enum Math {
        "d" = Diff([egg::Id; 2]),
        "i" = Integral([egg::Id; 2]),

        "+" = Add([egg::Id; 2]),
        "-" = Sub([egg::Id; 2]),
        "*" = Mul([egg::Id; 2]),
        "/" = Div([egg::Id; 2]),
        "pow" = Pow([egg::Id; 2]),
        "ln" = Ln(egg::Id),
        "sqrt" = Sqrt(egg::Id),

        "sin" = Sin(egg::Id),
        "cos" = Cos(egg::Id),

        Constant(BigRational),
        Symbol(Symbol),
    }
}

fn rules() -> Vec<Rewrite<Math, ()>> {
    vec![
        rw!("comm-add";  "(+ ?a ?b)"        => "(+ ?b ?a)"),
        rw!("comm-mul";  "(* ?a ?b)"        => "(* ?b ?a)"),
        rw!("assoc-add"; "(+ ?a (+ ?b ?c))" => "(+ (+ ?a ?b) ?c)"),
        rw!("assoc-mul"; "(* ?a (* ?b ?c))" => "(* (* ?a ?b) ?c)"),
        rw!("sub-canon"; "(- ?a ?b)" => "(+ ?a (* -1 ?b))"),
        rw!("zero-add"; "(+ ?a 0)" => "?a"),
        rw!("zero-mul"; "(* ?a 0)" => "0"),
        rw!("one-mul";  "(* ?a 1)" => "?a"),
        rw!("cancel-sub"; "(- ?a ?a)" => "0"),
        rw!("distribute"; "(* ?a (+ ?b ?c))"        => "(+ (* ?a ?b) (* ?a ?c))"),
        rw!("factor"    ; "(+ (* ?a ?b) (* ?a ?c))" => "(* ?a (+ ?b ?c))"),
        rw!("pow-mul"; "(* (pow ?a ?b) (pow ?a ?c))" => "(pow ?a (+ ?b ?c))"),
        rw!("pow1"; "(pow ?x 1)" => "?x"),
        rw!("pow2"; "(pow ?x 2)" => "(* ?x ?x)"),
        rw!("d-add"; "(d ?x (+ ?a ?b))" => "(+ (d ?x ?a) (d ?x ?b))"),
        rw!("d-mul"; "(d ?x (* ?a ?b))" => "(+ (* ?a (d ?x ?b)) (* ?b (d ?x ?a)))"),
        rw!("d-sin"; "(d ?x (sin ?x))" => "(cos ?x)"),
        rw!("d-cos"; "(d ?x (cos ?x))" => "(* -1 (sin ?x))"),
        rw!("i-one"; "(i 1 ?x)" => "?x"),
        rw!("i-cos"; "(i (cos ?x) ?x)" => "(sin ?x)"),
        rw!("i-sin"; "(i (sin ?x) ?x)" => "(* -1 (cos ?x))"),
        rw!("i-sum"; "(i (+ ?f ?g) ?x)" => "(+ (i ?f ?x) (i ?g ?x))"),
        rw!("i-dif"; "(i (- ?f ?g) ?x)" => "(- (i ?f ?x) (i ?g ?x))"),
        rw!("i-parts"; "(i (* ?a ?b) ?x)" =>
            "(- (* ?a (i ?b ?x)) (i (* (d ?x ?a) (i ?b ?x)) ?x))"),
    ]
}

const START_EXPRESSIONS: &[&str] = &[
    "(i (ln x) x)",
    "(i (+ x (cos x)) x)",
    "(i (* (cos x) x) x)",
    "(d x (+ 1 (* 2 x)))",
    "(d x (- (pow x 3) (* 7 (pow x 2))))",
    "(+ (* y (+ x y)) (- (+ x 2) (+ x x)))",
    "(/ 1 (- (/ (+ 1 (sqrt five)) 2) (/ (- 1 (sqrt five)) 2)))",
];

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut args = std::env::args().skip(1);
    let n: usize = args.next().ok_or("usage: egg-math N (1–13)")?.parse()?;
    if !(1..=13).contains(&n) || args.next().is_some() {
        return Err("usage: egg-math N (1–13)".into());
    }
    let rules = rules();
    let mut runner = egg::Runner::<Math, ()>::default()
        .with_scheduler(egg::SimpleScheduler)
        .with_iter_limit(n)
        .with_node_limit(usize::MAX)
        .with_time_limit(std::time::Duration::MAX);
    for seed in START_EXPRESSIONS {
        runner = runner.with_expr(&seed.parse()?);
    }
    // Normalize seeds before running the requested rewrite iterations.
    runner.egraph.rebuild();
    runner = runner.run(&rules);
    if runner.iterations.len() != n
        || !matches!(runner.stop_reason, Some(egg::StopReason::IterationLimit(k)) if k == n)
    {
        return Err(format!(
            "Egg stopped before {n} complete iterations: {:?}",
            runner.stop_reason
        )
        .into());
    }
    Ok(())
}
