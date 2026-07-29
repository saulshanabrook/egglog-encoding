use super::*;

fn rewrite(lhs: Expr, rhs: Expr) -> Rewrite {
    Rewrite {
        span: Span::Panic,
        lhs,
        rhs,
        conditions: Vec::new(),
        name: String::new(),
    }
}

#[test]
fn rewrite_root_is_static_and_avoids_surface_variables() {
    assert_eq!(
        rewrite_root_name(&rewrite(
            Expr::Var(Span::Panic, "x".into()),
            Expr::Var(Span::Panic, "y".into()),
        )),
        "__rewrite_root"
    );
    assert_eq!(
        rewrite_root_name(&rewrite(
            Expr::Var(Span::Panic, "__rewrite_root".into()),
            Expr::Var(Span::Panic, "__rewrite_root_1".into()),
        )),
        "__rewrite_root_2"
    );
}
