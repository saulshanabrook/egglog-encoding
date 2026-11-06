use super::*;

fn r(entries: &[(i64, i64)]) -> Renaming {
    Renaming::new(entries.iter().copied()).unwrap()
}

#[test]
fn renamings_are_permutations() {
    let swap = r(&[(0, 1), (1, 0)]);
    assert!(swap.compose(&swap).is_identity());
    assert_eq!(swap.inverse(), swap);
    let cycle = r(&[(0, 1), (1, 2), (2, 0)]);
    assert_eq!(cycle.compose(&cycle.inverse()), Renaming::identity());
    assert_eq!(cycle.compose(&cycle), cycle.inverse());
    assert!(Renaming::new([(0, 1), (2, 1)]).is_none());
    assert!(Renaming::new([(0, 5)]).is_none());
    assert_eq!(
        Renaming::completing([(0, 5)]).unwrap(),
        r(&[(0, 5), (5, 0)])
    );
    assert_eq!(
        Renaming::completing([(0, 5), (5, 7)]).unwrap(),
        r(&[(0, 5), (5, 7), (7, 0)])
    );
    assert!(Renaming::completing([(0, 1), (2, 1)]).is_none());
    assert_eq!(cycle.restricted(&BTreeSet::from([0])), r(&[(0, 1), (1, 0)]));
    assert!(cycle.restricted(&BTreeSet::from([7])).is_identity());
}

#[test]
fn renaming_a_term_touches_every_slot() {
    let mut dag = TermDag::default();
    let s0 = slot_term(&mut dag, 0);
    let s3 = slot_term(&mut dag, 3);
    let lam = dag.app("Lam".into(), vec![s0, s3]);
    let renamed = rename(&mut dag, &r(&[(0, 1), (1, 0), (3, 4), (4, 3)]), lam);
    assert_eq!(dag.to_string(renamed), "(Lam $1 $4)");
    assert_eq!(all_slots(&dag, renamed), BTreeSet::from([1, 4]));
}

#[test]
fn patterns_instantiate_by_name() {
    let mut dag = TermDag::default();
    let x = dag.var("x".into());
    let lit = dag.var("$x".into());
    let pat = dag.app("Lam".into(), vec![lit, x]);
    assert_eq!(
        pattern_vars(&dag, pat),
        vec!["$x".to_string(), "x".to_string()]
    );
    let s7 = slot_term(&mut dag, 7);
    let null = dag.app("Null".into(), vec![]);
    let subst = HashMap::from_iter([("x".to_string(), null), ("$x".to_string(), s7)]);
    let t = instantiate(&mut dag, pat, &subst).unwrap();
    assert_eq!(dag.to_string(t), "(Lam $7 (Null))");
    assert!(is_subterm(&dag, null, t));
    let missing = HashMap::from_iter([("x".to_string(), null)]);
    assert_eq!(instantiate(&mut dag, pat, &missing), Err("$x".to_string()));
}
#[test]
fn completing_validates_the_whole_injection() {
    assert!(Renaming::completing([(0, 0), (1, 0)]).is_none());
    assert!(Renaming::completing([(0, 1), (0, 2)]).is_none());
    let m = Renaming::completing([(0, 1), (1, 2)]).unwrap();
    assert_eq!((m.apply(0), m.apply(1), m.apply(2)), (1, 2, 0));
}

#[test]
fn fresh_slots_skip_reserved_names_across_integer_boundary() {
    let mut fresh = FreshSlots::new([i64::MIN + 1, i64::MAX, -1]);
    fresh.reserve([i64::MIN]);
    assert_eq!(fresh.fresh(), i64::MAX - 1);
    assert_eq!(fresh.fresh(), i64::MAX - 2);
}
