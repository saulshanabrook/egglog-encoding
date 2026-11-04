from pathlib import Path
import hashlib,json,tarfile,difflib
R=Path(__file__).resolve().parent; H=Path('/private/tmp/eggcc-alias-actual'); E=Path('/private/tmp/encoding-alias-actual')
old=(Path('/private/tmp/eggcc-alias-candidate')/'dag_in_context/src/scoped_alias.rs').read_text()
(R/'initial-installed-scoped_alias.rs').write_text(old)
s=(R/'inputs/scoped_alias.rs').read_text()
# Require one exact function signature: three i64 inputs followed by state,
# state-only output. Reject all foreign typed function contexts.
anchor='    fn word(&self, expr: &str, expected: &str, depth: usize) -> Option<Word> {'
s=s.replace(anchor,'''    fn tuple_signature(&self, ty: &str) -> Option<Vec<String>> {
        let mut list = self.unique(ty, "TupleT")?.first()?.clone();
        let mut types = Vec::new();
        for _ in 0..16 {
            if self.tagged(&list, "TNil") { return Some(types); }
            let row = self.unique(&list, "TCons")?;
            let names = ["IntT", "StateT"].into_iter().filter(|name| self.tagged(&row[0], name)).collect::<Vec<_>>();
            if names.len() != 1 { return None; }
            types.push(names[0].to_owned()); list = row[1].clone();
        }
        None
    }

'''+anchor)
s=s.replace('''        if self.unique(expected, "InFunc").is_some() {
            return Some(Word::Slot(expected.to_owned(), index));
        }''','''        if let Some(function) = self.unique(expected, "InFunc") {
            if self.unique(expected, "InIf").is_some() { return None; }
            let roots = self.nodes.values().filter(|n| n.op == "Function").collect::<Vec<_>>();
            if roots.len() != 1 || self.nodes[&roots[0].children[0]].eclass != function[0] { return None; }
            return Some(Word::Slot(expected.to_owned(), index));
        }''')
s=s.replace('''    let load_row = graph.operator(load, "Bop", "Load")?;''','''    let function = graph.nodes.values().find(|n| n.op == "Function")?;
    if graph.tuple_signature(&graph.nodes[&function.children[1]].eclass)? != ["IntT", "IntT", "IntT", "StateT"]
        || graph.tuple_signature(&graph.nodes[&function.children[2]].eclass)? != ["StateT"] { return None; }
    // The closed profile admits only the source's built-in expression forms.
    // Type/analysis rows are not executable forms. Calls and pointer memory
    // have separate checks above and below.
    for node in graph.nodes.values().filter(|n| n.eclass.starts_with("Expr-")) {
        if !matches!(node.op.as_str(), "Arg"|"Const"|"Empty"|"Single"|"Concat"|"Get"|"SubTuple"|"Uop"|"Bop"|"Top"|"Alloc"|"If"|"DoWhile"|"Function"|"Print") {
            // Only constructors have Expr-valued eclasses; functions such as
            // ExtractedExprCache are canonical aliases and must not be used
            // as execution edges. Their names are explicitly admitted here.
            if !matches!(node.op.as_str(), "ExtractedExpr"|"ExtractedExprCache"|"TermGet"|"TermBop"|"TermTop"|"TermUop"|"TermAlloc"|"TermPrint"|"TermIf"|"TermDoWhile"|"TermConcat"|"TermSingle"|"TermArg"|"TermConst"|"TermEmpty"|"TermSubTuple") { return None; }
        }
    }
    let load_row = graph.operator(load, "Bop", "Load")?;''',1)
s=s.replace('''        || !graph.tagged(&allocation_row[3], "IntT")''','''        || !graph.unique(&allocation_row[3], "PointerT").is_some_and(|p| p.len()==1 && graph.tagged(&p[0], "IntT"))''')
anchor='''    // Free must be outside the loop; all mutable operations inside it are the'''
s=s.replace(anchor,'''    let inner_regions = graph.nodes.values().filter(|n| n.op == "If" && n.children.len()==4)
        .filter(|n| graph.nodes[&n.children[0]].eclass == inner[1] && graph.nodes[&n.children[1]].eclass == inner[2])
        .filter(|n| graph.reachable(&loop_row[1], &n.eclass) && graph.reachable(&graph.nodes[&n.children[2]].eclass, load)).count();
    if inner_regions == 0 { return None; }
'''+anchor)
s=s.replace('''    SeedOnly,
    PrimitiveOnly,''','''    SeedOnly,
    SeedOff,
    PrimitiveOnly,''',1).replace('''                "seed-only" => Self::SeedOnly,''','''                "seed-only" => Self::SeedOnly,
                "seed-off" => Self::SeedOff,''',1)
start=s.index('fn prove(mode: Mode)');end=s.index('\npub(crate) fn apply',start)
s=s[:start]+'''/// The logical rows are instantiated from the revalidated demand certificate.
/// Class labels name opaque equality-sort inputs; they are never primitive
/// semantic comparisons or a substitute for the false masked-Eq seed.
#[derive(Clone)]
struct Imported {
    labels: [String; 4],
    metadata: Vec<(&'static str, i64, i64)>,
    source_seed: bool,
}
impl Imported {
    fn read(graph: &Graph, cert: &Certificate) -> Option<Self> {
        let pi = graph.operator(&cert.branch_pi, "Bop", "PtrAdd")?;
        let pj = graph.operator(&cert.branch_pj, "Bop", "PtrAdd")?;
        let si = graph.operator(&pi[1], "Bop", "Add")?;
        let sj = graph.operator(&pj[1], "Bop", "Add")?;
        let branch = graph.unique(&cert.branch, "InIf")?;
        let eq = graph.operator(&branch[1], "Bop", "Eq")?;
        let mi = graph.operator(&eq[0], "Bop", "Bitand")?;
        let mj = graph.operator(&eq[1], "Bop", "Bitand")?;
        let allocation = graph.unique(&cert.allocation, "Alloc")?;
        let size = graph.literal(&allocation[1])?;
        Some(Self {
            labels: [cert.local_i.clone(),cert.local_j.clone(),si[1].clone(),cert.allocation.clone()],
            metadata: vec![("mask",graph.literal(&mi[1])?,graph.literal(&mj[1])?),
                ("shift",graph.literal(&si[1])?,graph.literal(&sj[1])?),
                // The certificate independently reconstructed these exact
                // signed guard bounds for both imported source words.
                ("lower",0,0),("upper",2,2),("allocation-length",size,size),
                ("access-width-from-IntT",8,8)],
            source_seed: graph.tagged(&branch[0], "false"),
        })
    }
}
fn prove(mode: Mode, imported: &Imported) -> Result<([bool; 3], Json), Error> {
    let reverse = !matches!(mode,Mode::ReverseOff|Mode::IndexRescue|Mode::ShiftRescue|Mode::CellRescue);
    let shift = !matches!(mode,Mode::ShiftOff|Mode::ShiftRescue|Mode::CellRescue);
    let cell = !matches!(mode,Mode::CellOff|Mode::CellRescue);
    let rescue = match mode {Mode::IndexRescue=>Some((0,1)),Mode::ShiftRescue=>Some((6,7)),Mode::CellRescue=>Some((8,9)),_=>None};
    let ids = imported.labels.iter().enumerate().map(|(i,label)| imported.labels.iter().position(|other|other==label).unwrap_or(i)).collect::<Vec<_>>();
    let mut program = format!("(datatype A1Word)\\n(datatype A1Region)\\n(datatype A1Cell)\\n(constructor A1Opaque (i64) A1Word)\\n(constructor A1OpaqueRegion (i64) A1Region)\\n(constructor A1Mask (A1Word A1Word) A1Word)\\n(constructor A1Shift (A1Word) A1Word {})\\n(constructor A1Location (A1Region A1Word) A1Cell {})\\n(let $a1-left (A1Opaque {}))\\n(let $a1-right (A1Opaque {}))\\n(let $a1-one (A1Opaque {}))\\n(let $a1-region (A1OpaqueRegion {}))\\n(let $a1-ml (A1Mask $a1-left $a1-one))\\n(let $a1-mr (A1Mask $a1-right $a1-one))\\n(let $a1-sl (A1Shift $a1-left))\\n(let $a1-sr (A1Shift $a1-right))\\n(let $a1-cl (A1Location $a1-region $a1-sl))\\n(let $a1-cr (A1Location $a1-region $a1-sr))\\n",if shift {":injective"}else{""},if cell {":injective"}else{""},ids[0],ids[1],ids[2],ids[3]);
    if imported.source_seed && mode != Mode::SeedOff {program.push_str("(disequal $a1-ml $a1-mr)\\n");}
    if let Some(pair)=rescue {program.push_str(match pair {(0,1)=>"(disequal $a1-left $a1-right)\\n",(6,7)=>"(disequal $a1-sl $a1-sr)\\n",_=>"(disequal $a1-cl $a1-cr)\\n"});}
    let primitive_comparisons = if mode==Mode::PrimitiveOnly {imported.metadata.iter().map(|(field,left,right)|json!({"field":field,"left":left,"right":right,"equal":left==right})).collect::<Vec<_>>()}else{vec![]};
    let mut graph=new_experimental_egraph_with_options(false,DisequalityEncoding::Nee);
    graph.parse_and_run_program(None,&program)?;
    let mut known=[false;3];let mut bottom=false;let mut oracle=None;
    if mode==Mode::Manual {let result=manual(reverse,shift,cell,rescue);known=result.0;bottom=result.1;oracle=Some(result.0);}
    else if !matches!(mode,Mode::SeedOnly|Mode::PrimitiveOnly) {
        graph.parse_and_run_program(None,"(run-schedule (saturate injectivity))")?;
        bottom=match graph.parse_and_run_program(None,"(check-contradiction)"){Ok(_)=>true,Err(Error::CheckError(..))=>false,Err(e)=>return Err(e)};
        if !bottom {for (index,(a,b)) in [("$a1-left","$a1-right"),("$a1-sl","$a1-sr"),("$a1-cl","$a1-cr")].into_iter().enumerate() {
            if index==2 && mode==Mode::QueryOff {continue;}
            let name=format!("A1Known{index}");let predicate=if reverse {"known-disequal?"}else{"known-disequal-forward-only?"};
            graph.parse_and_run_program(None,&format!("(relation {name} ())\\n(ruleset {name}-query)\\n(rule (({predicate} {a} {b})) (({name})) :ruleset {name}-query :naive)\\n(run-schedule (run {name}-query))"))?;
            known[index]=graph.get_size(&name)>0;
        }}
    }
    if bottom {known=[false;3];}
    Ok((known,json!({"program":program,"imported_host_classes":imported.labels,"source_seed":imported.source_seed,"index_known":known[0],"shift_known":known[1],"cell_known":known[2],"bottom":bottom,"reverse_enabled":reverse,"shift_marked":shift,"cell_marked":cell,"same_graph_and_seed":mode!=Mode::SeedOff,"primitive_comparisons":primitive_comparisons,"primitive_mismatch_count":imported.metadata.iter().filter(|(_,a,b)|a!=b).count(),"manual_known":oracle,"query_status":if mode==Mode::QueryOff {"not-run"}else if known[2] {"proved"}else{"unknown-or-error"}})))
}
''' + s[end:]
s=s.replace('''            let (known, mut query) = prove(mode)?;''','''            let imported = Imported::read(&graph, cert).ok_or_else(|| Error::BackendError("A1 import certificate mismatch".to_owned()))?;
            let (known, mut query) = prove(mode, &imported)?;''')
s=s.replace('''            let (known, receipt) = prove(mode).unwrap();''','''            let fixture: Json = serde_json::from_str(include_str!("scoped_alias_graph.json")).unwrap();
            let graph = Graph::from_json(fixture).unwrap();
            let cert = certificate(&graph,"Expr-297").unwrap();
            let imported = Imported::read(&graph,&cert).unwrap();
            let (known, receipt) = prove(mode, &imported).unwrap();''')
# Register seed, contradiction, literal, context and lifetime boundaries.
pos=s.rfind('\n}')
s=s[:pos]+'''
    #[test]
    fn a1_seed_bottom_and_certificate_semantic_negatives() {
        let fixture: Json=serde_json::from_str(include_str!("scoped_alias_graph.json")).unwrap();
        let graph=Graph::from_json(fixture.clone()).unwrap();
        let cert=certificate(&graph,"Expr-297").unwrap();
        let imported=Imported::read(&graph,&cert).unwrap();
        assert_eq!(prove(Mode::SeedOff,&imported).unwrap().0,[false;3]);
        let mut absent=imported.clone();absent.source_seed=false;
        assert_eq!(prove(Mode::Encoding,&absent).unwrap().0,[false;3]);
        let mut collapse=imported.clone();collapse.labels[1]=collapse.labels[0].clone();
        let (known,receipt)=prove(Mode::Encoding,&collapse).unwrap();
        assert_eq!(known,[false;3]);assert_eq!(receipt["bottom"],true);
        let (_,null)=prove(Mode::PrimitiveOnly,&imported).unwrap();
        assert_eq!(null["primitive_comparisons"].as_array().unwrap().len(),6);
        assert_eq!(null["primitive_mismatch_count"],0);
        for op in ["Bitand","GreaterEq","LessThan","LessEq","Free","PointerT"] {
            let mut bad=fixture.clone();
            for node in bad["nodes"].as_object_mut().unwrap().values_mut() {if node["op"]==op {node["op"]=json!("A1Unsupported");}}
            assert!(certificate(&Graph::from_json(bad).unwrap(),"Expr-297").is_none(),"{op}");
        }
        let mut changed=Graph::from_json(fixture.clone()).unwrap();
        changed.gets.insert((cert.loop_expr.clone(),0),BTreeSet::from(["Expr-foreign-state".to_owned()]));
        assert!(certificate(&changed,"Expr-297").is_none());
        let mut changed=Graph::from_json(fixture).unwrap();
        for node in changed.nodes.values_mut().filter(|n|n.op=="If") {
            if node.children.len()==4 && graph.nodes[&node.children[0]].eclass==graph.unique(&cert.target_context,"InIf").unwrap()[1] {node.children.swap(2,3);}
        }
        assert!(certificate(&changed,"Expr-297").is_none());
    }
''' +s[pos:]
p=H/'dag_in_context/src/scoped_alias.rs';p.write_text(s)
(R/'revision-1-scoped_alias.rs').write_text(s)
(R/'revision-1.patch').write_text(''.join(difflib.unified_diff(old.splitlines(True),s.splitlines(True),fromfile='initial/scoped_alias.rs',tofile='revision-1/scoped_alias.rs')))
(R/'revision-1.json').write_text(json.dumps({'functional_revision':1,'reason':'initial positive retained certificate rejects Alloc PointerT(IntT); independent review requires linked import, real primitive comparisons and exact context/effect joins','initial_test':'commands/focused-initial/receipt.json','initial_installed_sha256':hashlib.sha256(old.encode()).hexdigest(),'revision_sha256':hashlib.sha256(s.encode()).hexdigest(),'further_functional_revisions_allowed':0},indent=2)+'\n')
