from pathlib import Path
import shutil
root=Path('/Users/saul/p/egglog-encoding/benchmarks/local/eggcc-nontrivial-encoding-payoff/route-integration')
host=Path('/private/tmp/eggcc-route-candidate')
engine=Path('/private/tmp/encoding-route-candidate')
for source,dest in [(Path('/private/tmp/eggcc-affine-candidate'),host),(Path('/private/tmp/encoding-affine-candidate'),engine)]:
 assert not dest.exists()
 shutil.copytree(source,dest,ignore=shutil.ignore_patterns('target','.git','*.snap.new','__pycache__'))
for path in [host/'Cargo.toml',host/'dag_in_context/Cargo.toml']:
 path.write_text(path.read_text().replace('/private/tmp/encoding-affine-candidate','/private/tmp/encoding-route-candidate'))
s=(host/'dag_in_context/src/scoped_reasoning.rs').read_text()
s=s.replace('a reversible two-word affine key','a tagged paired routing key')
s=s.replace('RcExpr, TreeProgram, Type','RcExpr, TernaryOp, TreeProgram, Type')
s=s.replace('    Scale(Box<Word>, i64),','    Scale(Box<Word>, i64),\n    Select(Box<Selector>, Box<Word>, Box<Word>),')
s=s.replace('fn tuple_length', '#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]\nenum Selector {\n    LessThan(Box<Word>, Box<Word>),\n}\n\nfn tuple_length',1)
pos=s.index('        Expr::Bop(BinaryOp::Add, left, right)')
s=s[:pos]+'''        Expr::Top(TernaryOp::Select, predicate, left, right) => {
            let Expr::Bop(BinaryOp::LessThan, first, second) = predicate.as_ref() else {
                return None;
            };
            if predicate.get_ctx() != *expected {
                return None;
            }
            Some(Word::Select(
                Box::new(Selector::LessThan(
                    Box::new(translate(first, root, expected)?),
                    Box::new(translate(second, root, expected)?),
                )),
                Box::new(translate(left, root, expected)?),
                Box::new(translate(right, root, expected)?),
            ))
        }
'''+s[pos:]
start=s.index('/// Match `x + 2*y`')
end=s.index('/// Return the non-shared Add child',start)
s=s[:start]+s[end:]
start=s.index('fn odd_mul_child(')
end=s.index('#[derive(Clone, Copy',start)
s=s[:start]+s[end:]
s=s.replace('    TargetRescue,','    EqualityRescue,\n    DisequalityRescue,')
s=s.replace('            "target-rescue" => Self::TargetRescue,','            "equality-rescue" => Self::EqualityRescue,\n            "disequality-rescue" => Self::DisequalityRescue,')
s=s.replace('affine_marked','route_marked')
s=s.replace('    rescue: bool,\n) -> ([bool; 7], bool)', '    equality_rescue: bool,\n    disequality_rescue: bool,\n    equality_reasoning: bool,\n) -> ([bool; 7], bool)')
start=s.index('    let rows: Vec<ApplicationRow>')
end=s.index('    let mut equality =',start)
s=s[:start]+'''    let rows: Vec<ApplicationRow> = vec![
        ("Select", vec![18, 0, 1], vec![], 6, false),
        ("Select", vec![18, 1, 0], vec![], 7, false),
        ("Select", vec![18, 2, 3], vec![], 8, false),
        ("Select", vec![18, 3, 2], vec![], 9, false),
        ("Route", vec![18, 0, 1], vec![], 10, route_marked),
        ("Route", vec![18, 2, 3], vec![], 11, route_marked),
        ("Triple", vec![18, 6, 7], vec![], 12, false),
        ("Triple", vec![18, 8, 9], vec![], 13, false),
        ("Add", vec![2, 4], vec![], 14, false),
        ("Add", vec![0, 5], vec![], 15, false),
        ("OddMul", vec![4], vec![3], 16, mul_marked),
        ("OddMul", vec![5], vec![3], 17, mul_marked),
    ];
'''+s[end:]
s=s.replace('(0..18)','(0..19)')
s=s.replace('    if rescue {\n        disequality.insert((16, 17));\n    }','    if equality_rescue {\n        merge(&mut equality, 0, 2);\n    }\n    if disequality_rescue {\n        disequality.insert((4, 5));\n    }')
s=s.replace('                if left_name != right_name || left_params != right_params {','                if left_name != right_name || left_params != right_params\n                    || (!equality_reasoning && !left_children.is_empty())\n                {')
start=s.index('fn prove(mode: Mode)')
end=s.index('    let run_engine =',start)
s=s[:start]+'''fn prove(mode: Mode) -> Result<(bool, serde_json::Value), Error> {
    let route_marked = !matches!(mode, Mode::CancellationOff | Mode::EqualityRescue | Mode::DisequalityRescue);
    let mul_marked = mode != Mode::ForwardOff;
    let reverse = !matches!(mode, Mode::ReverseOff | Mode::DisequalityRescue);
    let identity = mode != Mode::IdentityOff;
    let equality_rescue = mode == Mode::EqualityRescue;
    let disequality_rescue = mode == Mode::DisequalityRescue;
    let mut program = format!(
        "(datatype Scope (ThisScope))\\n(datatype Word)\\n(datatype Selector)\\n(datatype Key)\\n(constructor P (Scope) Selector)\\n(constructor A (Scope) Word)\\n(constructor B (Scope) Word)\\n(constructor C (Scope) Word)\\n(constructor D (Scope) Word)\\n(constructor Z (Scope) Word)\\n(constructor W (Scope) Word)\\n(constructor Select (Selector Word Word) Word)\\n(constructor Route (Selector Word Word) Key {})\\n(constructor Triple (Selector Word Word) Key)\\n(constructor Add (Word Word) Word)\\n(constructor OddMul (Word i64) Word {})\\n(let p (P (ThisScope)))\\n(let a (A (ThisScope)))\\n(let b (B (ThisScope)))\\n(let c (C (ThisScope)))\\n(let d (D (ThisScope)))\\n(let z (Z (ThisScope)))\\n(let w (W (ThisScope)))\\n(let uab (Select p a b))\\n(let vab (Select p b a))\\n(let ucd (Select p c d))\\n(let vcd (Select p d c))\\n(let kab (Route p a b))\\n(let kcd (Route p c d))\\n(let pab (Triple p uab vab))\\n(let pcd (Triple p ucd vcd))\\n(let acz (Add c z))\\n(let aaw (Add a w))\\n(let mz (OddMul z 3))\\n(let mw (OddMul w 3))\\n",
        if route_marked { ":injective" } else { "" },
        if mul_marked { ":injective" } else { "" },
    );
    if identity {
        program.push_str("(union kab pab)\\n(union kcd pcd)\\n");
    }
    program.push_str("(union uab ucd)\\n(union vab vcd)\\n(disequal acz aaw)\\n");
    if equality_rescue {
        program.push_str("(union a c)\\n");
    }
    if disequality_rescue {
        program.push_str("(disequal z w)\\n");
    }
'''+s[end:]
s=s.replace('    let manual_result = manual(route_marked, mul_marked, reverse, identity, rescue);','    let manual_result = if matches!(mode, Mode::Manual | Mode::PrimitiveOnly) {\n        Some(manual(route_marked, mul_marked, reverse, identity, equality_rescue, disequality_rescue, mode == Mode::Manual))\n    } else { None };')
s=s.replace('        manual_result.1','        manual_result.unwrap().1')
s=s.replace('            known = manual_result.0;','            known = manual_result.unwrap().0;')
s=s.replace('            "matrix":[[1,2],[2,3]],\n            "determinant":-1,','            "key_law":"Route(p,a,b)=(p,Select(p,a,b),Select(p,b,a))",\n            "selector_sort":"equality-sort Selector; opaque dynamic value",')
s=s.replace('json!({\n            "mode"','json!({\n            "mode"',1)
s=s.replace('            "manual_receipts":if matches!(mode,Mode::SeedOnly|Mode::PrimitiveOnly){None}else{Some(manual_result.0)},\n            "manual_bottom":if matches!(mode,Mode::SeedOnly|Mode::PrimitiveOnly){None}else{Some(manual_result.1)},','            "manual_receipts":manual_result.map(|value|value.0),\n            "manual_bottom":manual_result.map(|value|value.1),')
s=s.replace('            "exact_target_rescue":rescue,','            "intermediate_equality_rescue":equality_rescue,\n            "intermediate_disequality_rescue":disequality_rescue,')
s=s.replace('            "primitive_only_marked_primitive_fields":[1,2,2,3,3],','            "primitive_only_marked_primitive_fields":[3],\n            "primitive_only_same_rows_seeds_identities":mode==Mode::PrimitiveOnly,\n            "primitive_only_equality_sort_reasoning":false,')
s=s.replace('/// Admit only the exact nested affine-key, mixed-Add and odd-product chain.','/// Admit only complementary Selects with a common localized tag and exact tail.')
start=s.index('            let (mut left_pair, mut right_pair) =')
end=s.index('            if [a.clone()',start)
s=s[:start]+'''            let (Word::Select(first_tag, a, b), Word::Select(right_tag, c, d)) =
                (first_left, first_right) else { return None; };
            if first_tag != right_tag { return None; }
            let (Some(second_left), Some(second_right)) = &translated_second else {
                return None;
            };
            let expected_left = Word::Select(first_tag.clone(), b.clone(), a.clone());
            let expected_right = Word::Select(first_tag.clone(), d.clone(), c.clone());
            if !((second_left == &expected_left && second_right == &expected_right)
                || (second_left == &expected_right && second_right == &expected_left)) {
                return None;
            }
            let (a,b,c,d) = (a.as_ref().clone(),b.as_ref().clone(),c.as_ref().clone(),d.as_ref().clone());
'''+s[end:]
s=s.replace('            let target_children = (odd_mul_child(target_left)?, odd_mul_child(target_right)?);','            let (Word::Scale(left_child,3), Word::Scale(right_child,3)) = (target_left,target_right) else { return None; };\n            let target_children = (left_child.as_ref().clone(), right_child.as_ref().clone());')
s=s.replace('exact affine components, contexts, mixed Add, or odd target mismatch','exact paired routing, common tag, contexts, mixed Add, or odd target mismatch')
s=s.replace('translate(first_left, &root, &root)','translate(first_left, root, root)').replace('translate(first_right, &root, &root)','translate(first_right, root, root)')
for ctx in ['second_scope','mixed_scope','target_scope']:
 s=s.replace('&root, &'+ctx,'root, '+ctx)
s=s.replace('Mode::TargetRescue,','Mode::EqualityRescue,\n            Mode::DisequalityRescue,')
s=s.replace('Mode::Encoding | Mode::Manual | Mode::TargetRescue | Mode::ApplicationOff','Mode::Encoding | Mode::Manual | Mode::EqualityRescue | Mode::DisequalityRescue | Mode::ApplicationOff')
s=s.replace('affine_chain_causal_controls','route_chain_causal_controls').replace('affine_manual_closure_respects_missing_edges','route_manual_closure_respects_missing_edges')
s=s.replace('            if mode == Mode::Encoding {\n                assert_eq!(\n                    receipt["manual_receipts"],\n                    json!([true, true, true, true, true, true, true]),\n                );','            if mode == Mode::Encoding {')
s=s.replace('manual(true, true, true, true, false)','manual(true, true, true, true, false, false, true)').replace('manual(false, true, true, true, false)','manual(false, true, true, true, false, false, true)').replace('manual(true, false, true, true, false)','manual(true, false, true, true, false, false, true)').replace('manual(true, true, false, true, false)','manual(true, true, false, true, false, false, true)').replace('manual(true, true, true, false, false)','manual(true, true, true, false, false, false, true)')
# All context values above are already borrowed from expression scopes.
s=s.replace('let root = first_predicate.get_ctx();','let root = first_predicate.get_ctx();')
(host/'dag_in_context/src/scoped_reasoning.rs').write_text(s)
shutil.copyfile(root.parent/'affine-integration/run.py',root/'run.py')
r=(root/'run.py').read_text().replace('affine-key','tagged Route').replace('eggcc-affine-candidate','eggcc-route-candidate')
(root/'run.py').write_text(r)
(root/'fixtures').mkdir()
previous=root.parent/'lossless-key-screens/20261019-three-total-keys/execution-02/routing'
shutil.copyfile(previous/'source.bril',root/'fixtures/source.bril')
for old,new in [('missing-first','omitted-first-output'),('missing-second','omitted-second-output'),('different-selector','swapped-payload-tag-omitted'),('even-target','even-multiplier'),('true-sum','wrong-branch')]:
 shutil.copyfile(previous/f'negative-{old}/source.bril',root/f'fixtures/{new}.bril')
# Different selectors with unchanged payloads is separately rejected even when an observed row has equal outcomes.
source=(root/'fixtures/source.bril').read_text()
negative=source.replace('  ucd: int = select p c d;','  s: bool = lt r q;\n  ucd: int = select s c d;').replace('  vcd: int = select p d c;','  vcd: int = select s d c;')
negative=negative.replace('# ARGS: 1 2 1 2 3 4 0 1','# ARGS: 0 1 1 0 0 0 0 1')
(root/'fixtures/selector-tag-mismatch.bril').write_text(negative)
print(host,engine)
