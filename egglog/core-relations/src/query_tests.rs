use super::*;

#[test]
fn ephemeral_recipe_leaves_do_not_enter_pointer_memo() {
    let first = Variable::new(0);
    let second = Variable::new(1);
    let sort = ReplaySortId::new(0);
    let mut inputs = HashMap::default();
    inputs.insert(first, (RecipeInput::Binding(0), sort));
    inputs.insert(second, (RecipeInput::Binding(1), sort));
    let mut lowerer = RecipeLowerer {
        inputs,
        memo: HashMap::default(),
        observed_sorts: HashMap::default(),
    };

    for (variable, expected_binding) in [(first, 0), (second, 1)] {
        let root = Arc::new(RecipeExpr::Input(variable));
        assert!(matches!(
            lowerer.try_lower(&root, sort).as_deref(),
            Some(TermTemplate::Binding { binding }) if *binding == expected_binding
        ));
        assert!(
            lowerer.memo.is_empty() && lowerer.observed_sorts.is_empty(),
            "short-lived leaves must not be keyed by their reusable allocation address"
        );
    }
}
