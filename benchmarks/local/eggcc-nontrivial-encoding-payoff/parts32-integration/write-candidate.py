from pathlib import Path
p=Path('/private/tmp/eggcc-parts32-candidate/dag_in_context/src/scoped_reasoning.rs')
s=p.read_text();start=s.index('#[derive(Clone, Debug, PartialEq, Eq)]\nenum Transport');end=s.index('#[derive(Clone, Copy, Debug, PartialEq, Eq)]\nenum Mode')
transport=s[start:end]
start=s.index('fn tuple_length(');end=s.index('/// Translate only total pure')
projection=s[start:end]
header='''//! A private, exact-scope Parts32 experiment. Only a checked final Eq=false
//! leaves the sidecar; no word or branch equality enters the compiler graph.
use std::{collections::BTreeSet, path::Path, sync::atomic::{AtomicUsize, Ordering}};
use egglog::{new_experimental_egraph_with_options, DisequalityEncoding, Error};
use serde_json::json;
use crate::schema::{Assumption, BaseType, BinaryOp, Constant, Expr, RcExpr, TreeProgram, Type};
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Word { Slot(usize), Constant(i64), Low(Box<Word>, i64), Difference(Box<Word>,Box<Word>), High(Box<Word>,i64,i64) }
'''
rest=r'''
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Mode { Off, PrimitiveOnly, ForwardOff, ReverseOff, IdentityOff, Rescue, QueryOff, Manual, Encoding, BridgeOff, ConsumerOff, IfConsumerOff }
impl Mode {
    fn from_env() -> Self {
        match std::env::var("EGGCC_SCOPED_MODE").as_deref().unwrap_or("off") {
            "off"=>Self::Off,"primitive-only"=>Self::PrimitiveOnly,"forward-off"=>Self::ForwardOff,
            "reverse-off"=>Self::ReverseOff,"identity-off"=>Self::IdentityOff,"high-rescue"=>Self::Rescue,
            "query-off"=>Self::QueryOff,"manual"=>Self::Manual,"encoding"=>Self::Encoding,
            "bridge-off"=>Self::BridgeOff,"consumer-off"=>Self::ConsumerOff,"if-consumer-off"=>Self::IfConsumerOff,
            other=>panic!("Unknown EGGCC_SCOPED_MODE: {other}")
        }
    }
}
/// Follow exact nested If input bindings back to one lexical root. No tuple
/// position is equated across contexts without its actual branch input.
fn translate(expr:&RcExpr, scope:&Assumption, invariants:&[Invariant]) -> Option<Word> {
    match expr.as_ref() {
        Expr::Const(Constant::Int(v),_,_)=>Some(Word::Constant(*v)),
        Expr::Arg(Type::Base(BaseType::IntT),ctx) if ctx==scope=>Some(Word::Slot(0)),
        Expr::Get(arg,i)=> {
            let Expr::Arg(Type::TupleT(fields),ctx)=arg.as_ref() else{return None};
            if fields.get(*i)!=Some(&BaseType::IntT){return None}
            if ctx==scope {Some(constant_slot(ctx,*i,invariants).map(Word::Constant).unwrap_or(Word::Slot(*i)))}
            else if let Assumption::InIf(_,_,input)=ctx {translate(&project(input,*i)?,scope,invariants)}
            else {None}
        }
        Expr::Bop(BinaryOp::Bitand,a,b)=> {
            let (a,b)=(translate(a,scope,invariants)?,translate(b,scope,invariants)?);
            match (a,b) {(Word::Constant(k),x)|(x,Word::Constant(k))=>Some(Word::Low(Box::new(x),k)),_=>None}
        }
        Expr::Bop(BinaryOp::Sub,a,b)=>Some(Word::Difference(Box::new(translate(a,scope,invariants)?),Box::new(translate(b,scope,invariants)?))),
        Expr::Bop(BinaryOp::Div,a,b)=> {
            let Word::Constant(d)=translate(b,scope,invariants)? else{return None};
            let Word::Difference(x,low)=translate(a,scope,invariants)? else{return None};
            let Word::Low(y,m)=*low else{return None};
            if x==y {Some(Word::High(x,m,d))}else{None}
        }
        _=>None
    }
}
/// A finite generic closure, using the same committed rows, equality seeds,
/// representation unions and marked constructor as the encoding graph.
fn manual(marked:bool, reverse:bool, identity:bool, seeded:bool, rescue:bool)->([bool;4],bool) {
    // outputs 0..9: x,y,lx,ly,hx,hy,Parts(x),Parts(y),Pair(lx,hx),Pair(ly,hy)
    let rows:Vec<(&str,Vec<usize>,Vec<i64>,usize,bool)>=vec![
        ("Low",vec![0],vec![4294967295],2,false),("Low",vec![1],vec![4294967295],3,false),
        ("High",vec![0],vec![4294967295,4294967296],4,false),("High",vec![1],vec![4294967295,4294967296],5,false),
        ("Parts32",vec![0],vec![],6,marked),("Parts32",vec![1],vec![],7,marked),
        ("Pair",vec![2,4],vec![],8,false),("Pair",vec![3,5],vec![],9,false)];
    let mut equality=(0..10).collect::<Vec<_>>();
    if identity {for (a,b) in [(6,8),(7,9)] {let old=equality[b];let new=equality[a];for x in &mut equality{if *x==old{*x=new}}}}
    if seeded {equality[3]=equality[2]}
    let mut neq=BTreeSet::new();if seeded{neq.insert((0,1));}if rescue{neq.insert((4,5));}
    loop {
        let before=(equality.clone(),neq.clone());
        for (an,ac,ap,ao,am) in &rows {for (bn,bc,bp,bo,_) in &rows {
            if an!=bn||ap!=bp{continue}
            let equal=ac.iter().zip(bc).all(|(a,b)|equality[*a]==equality[*b]);
            if equal {let old=equality[*bo];let new=equality[*ao];for x in &mut equality{if *x==old{*x=new}}}
            if *am&&equality[*ao]==equality[*bo] {for (a,b) in ac.iter().zip(bc){let old=equality[*b];let new=equality[*a];for x in &mut equality{if *x==old{*x=new}}}}
        }}
        neq=neq.into_iter().map(|(a,b)|{let(a,b)=(equality[a],equality[b]);if a<=b{(a,b)}else{(b,a)}}).collect();
        for (an,ac,ap,ao,am) in &rows {for (bn,bc,bp,bo,_) in &rows {
            if an!=bn||ap!=bp{continue}
            let (a,b)=(equality[*ao],equality[*bo]);let output=if a<=b{(a,b)}else{(b,a)};
            for (i,(a,b)) in ac.iter().zip(bc).enumerate() {
                let(a,b)=(equality[*a],equality[*b]);let child=if a<=b{(a,b)}else{(b,a)};
                if *am&&neq.contains(&child){neq.insert(output);}
                if reverse&&neq.contains(&output)&&ac.iter().zip(bc).enumerate().all(|(j,(a,b))|i==j||equality[*a]==equality[*b]){neq.insert(child);}
            }
        }}
        if before==(equality.clone(),neq.clone()){break}
    }
    let known=[(0,1),(6,7),(8,9),(4,5)].map(|(a,b)|{let(a,b)=(equality[a],equality[b]);neq.contains(&(a.min(b),a.max(b)))});
    (known,neq.iter().any(|(a,b)|a==b))
}
fn query(graph:&mut egglog::EGraph,name:&str,a:&str,b:&str,reverse:bool)->Result<bool,Error>{
    graph.parse_and_run_program(None,&format!("(relation {name} ())\n(ruleset {name}-query)\n(rule (({} {a} {b})) (({name})) :ruleset {name}-query :naive)\n(run-schedule (run {name}-query))",if reverse{"known-disequal?"}else{"known-disequal-forward-only?"}))?;
    Ok(graph.get_size(name)>0)
}
fn prove(mode:Mode)->Result<(bool,serde_json::Value),Error>{
    let marked=!matches!(mode,Mode::ForwardOff|Mode::Rescue);
    let reverse=!matches!(mode,Mode::ReverseOff|Mode::Rescue);
    let identity=mode!=Mode::IdentityOff;
    let seeded=mode!=Mode::PrimitiveOnly;
    let rescue=mode==Mode::Rescue;
    let mut program=format!("(datatype Scope (ThisScope))\n(datatype Word)\n(datatype Parts)\n(constructor X (Scope) Word)\n(constructor Y (Scope) Word)\n(constructor Low (Word i64) Word)\n(constructor High (Word i64 i64) Word)\n(constructor Parts32 (Word) Parts {})\n(constructor Pair (Word Word) Parts)\n(let x (X (ThisScope)))\n(let y (Y (ThisScope)))\n(let lx (Low x 4294967295))\n(let ly (Low y 4294967295))\n(let hx (High x 4294967295 4294967296))\n(let hy (High y 4294967295 4294967296))\n(let px (Parts32 x))\n(let py (Parts32 y))\n(let pairx (Pair lx hx))\n(let pairy (Pair ly hy))\n",if marked{":injective"}else{""});
    if identity{program.push_str("(union px pairx)\n(union py pairy)\n")}
    if seeded{program.push_str("(disequal x y)\n(union lx ly)\n")}
    if rescue{program.push_str("(disequal hx hy)\n")}
    program.push_str("(run-schedule (saturate injectivity))\n");
    let mut graph=new_experimental_egraph_with_options(false,DisequalityEncoding::Nee);
    graph.parse_and_run_program(None,&program)?;
    let bottom=match graph.parse_and_run_program(None,"(check-contradiction)"){Ok(_)=>true,Err(Error::CheckError(..))=>false,Err(e)=>return Err(e)};
    let manual_result=manual(marked,reverse,identity,seeded,rescue);
    let mut known=[false;4];
    if !bottom {
        if mode==Mode::Manual {known=manual_result.0}
        else {for (i,(name,a,b)) in [("WordKnown","x","y"),("PartsKnown","px","py"),("PairKnown","pairx","pairy"),("HighKnown","hx","hy")].into_iter().enumerate(){
            if i==3&&mode==Mode::QueryOff{continue}known[i]=query(&mut graph,name,a,b,reverse)?;
        }}
    }
    let export=!bottom&&known[3]&&mode!=Mode::BridgeOff;
    Ok((export,json!({"mode":format!("{mode:?}"),"encoding":"NEE","program":program,"primitive_metadata":{"mask":4294967295_i64,"divisor":4294967296_i64},"word_known":known[0],"parts_known":known[1],"pair_known":known[2],"high_known":if mode==Mode::QueryOff{None}else{Some(known[3])},"low_equal":seeded,"bottom":bottom,"manual_receipts":manual_result.0,"manual_bottom":manual_result.1,"export":export,"consumer_enabled":mode!=Mode::ConsumerOff,"reverse_enabled":reverse,"parts32_marked":marked,"representation_identity":identity,"rescue":rescue})))
}
/// Only a target nested under true low equality and false original word Eq can
/// be admitted. Both predicates and all projections are checked in exact scopes.
pub(crate) fn analyze(program:&TreeProgram)->Vec<RcExpr>{
    let mode=Mode::from_env();if mode==Mode::Off{return Vec::new()}
    static BOUNDARY:AtomicUsize=AtomicUsize::new(0);let boundary=BOUNDARY.fetch_add(1,Ordering::Relaxed);
    let types=program.typecheck();let invariants=loop_invariants(program);
    let mut stack=vec![program.entry.clone()];stack.extend(program.functions.clone());
    let(mut seen,mut exports,mut receipts)=(BTreeSet::new(),Vec::new(),Vec::new());
    while let Some(expr)=stack.pop(){if !seen.insert(std::rc::Rc::as_ptr(&expr)){continue}stack.extend(expr.children_exprs());
        let Expr::If(target,_,_,_)=expr.as_ref() else{continue};
        let Expr::Bop(BinaryOp::Eq,a,b)=target.as_ref() else{continue};
        if types.get(&std::rc::Rc::as_ptr(target))!=Some(&Type::Base(BaseType::BoolT)){continue}
        let target_scope=target.get_ctx();
        let Assumption::InIf(true,low_pred,low_input)=target_scope else{continue};
        let Expr::Bop(BinaryOp::Eq,la,lb)=low_pred.as_ref() else{continue};
        let word_scope=low_pred.get_ctx();
        let Assumption::InIf(false,word_pred,word_input)=word_scope else{continue};
        let Expr::Bop(BinaryOp::Eq,wa,wb)=word_pred.as_ref() else{continue};
        let root=word_pred.get_ctx();
        let Some(x)=translate(wa,root,&invariants) else{continue};let Some(y)=translate(wb,root,&invariants) else{continue};
        if matches!(x,Word::Constant(_))||matches!(y,Word::Constant(_)){continue}
        let lows=(translate(la,root,&invariants),translate(lb,root,&invariants));
        let highs=(translate(a,root,&invariants),translate(b,root,&invariants));
        let expected_lows=(Some(Word::Low(Box::new(x.clone()),4294967295)),Some(Word::Low(Box::new(y.clone()),4294967295)));
        let expected_highs=(Some(Word::High(Box::new(x.clone()),4294967295,4294967296)),Some(Word::High(Box::new(y.clone()),4294967295,4294967296)));
        let accepted=(lows==expected_lows||lows==(expected_lows.1.clone(),expected_lows.0.clone()))&&(highs==expected_highs||highs==(expected_highs.1.clone(),expected_highs.0.clone()));
        if !accepted{receipts.push(json!({"accepted":false,"reason":"exact partition, operands or parameter mismatch","lows":format!("{lows:?}"),"highs":format!("{highs:?}")}));continue}
        let(export,mut receipt)=match prove(mode){Ok(v)=>v,Err(e)=>(false,json!({"analysis_error":format!("{e:?}"),"export":false}))};
        receipt["accepted"]=json!(true);receipt["source_target"]=json!(target.to_string());receipt["source_word_predicate"]=json!(word_pred.to_string());receipt["source_low_predicate"]=json!(low_pred.to_string());receipt["root_scope"]=json!(root.to_string());receipt["word_scope"]=json!(word_scope.to_string());receipt["target_scope"]=json!(target_scope.to_string());receipt["word_input"]=json!(word_input.to_string());receipt["low_input"]=json!(low_input.to_string());receipt["translated_words"]=json!(format!("{x:?},{y:?}"));
        receipt["loop_invariants"]=json!(invariants.iter().map(|x|json!({"scope":x.scope.to_string(),"input_slot":x.index,"body_output_slot":x.index+1,"literal_initial_value":x.value,"proof":"literal initialization and unchanged both-branch same-index passthrough"})).collect::<Vec<_>>());
        receipts.push(receipt);if export{exports.push(target.clone())}
    }
    if let Ok(dir)=std::env::var("EGGCC_SCOPED_EVIDENCE"){std::fs::create_dir_all(&dir).unwrap();let path=Path::new(&dir).join(format!("boundary-{boundary:04}.json"));assert!(!path.exists());std::fs::write(path,serde_json::to_vec_pretty(&json!({"boundary":boundary,"mode":format!("{mode:?}"),"queries":receipts,"exports":exports.len()})).unwrap()).unwrap();}
    exports
}
#[cfg(test)]
mod tests{
 use super::*;
 #[test] fn parts32_generic_chain_causal_controls(){for mode in [Mode::Encoding,Mode::Manual,Mode::ForwardOff,Mode::ReverseOff,Mode::IdentityOff,Mode::Rescue,Mode::QueryOff,Mode::PrimitiveOnly,Mode::BridgeOff,Mode::ConsumerOff]{let(export,r)=prove(mode).unwrap();assert_eq!(export,matches!(mode,Mode::Encoding|Mode::Manual|Mode::Rescue|Mode::ConsumerOff),"{r}");if mode==Mode::ForwardOff{assert_eq!(r["parts_known"],false)}if mode==Mode::ReverseOff{assert_eq!(r["parts_known"],true);assert_eq!(r["high_known"],false)}if mode==Mode::Encoding{assert_eq!(r["manual_receipts"],json!([true,true,true,true]));assert_eq!(r["bottom"],false)}}}
 #[test] fn parts32_manual_closure_respects_missing_edges(){assert_eq!(manual(true,true,true,true,false).0,[true;4]);assert_eq!(manual(false,true,true,true,false).0,[true,false,false,false]);assert_eq!(manual(true,false,true,true,false).0,[true,true,true,false]);assert_eq!(manual(true,true,false,true,false).0,[true,true,false,false]);assert_eq!(manual(true,true,true,false,false).0,[false;4]);}
}
'''
p.write_text(header+transport+projection+rest)
# Extra read predicate is an inference-only knockout. It shares every graph row
# and seed with the ordinary query but disables every generic reverse edge.
p=Path('/private/tmp/encoding-parts32-candidate/egglog-experimental/src/disequality.rs');s=p.read_text()
s=s.replace('egraph.add_read_primitive(KnownDisequal(encoding), None);','egraph.add_read_primitive(KnownDisequal(encoding, true), None);\n    egraph.add_read_primitive(KnownDisequal(encoding, false), None);')
s=s.replace('struct KnownDisequal(DisequalityEncoding);','struct KnownDisequal(DisequalityEncoding, bool);')
s=s.replace('        "known-disequal?"\n    }','        if self.1 { "known-disequal?" } else { "known-disequal-forward-only?" }\n    }',1)
s=s.replace('known_disequal(&state, self.0, *lhs, *rhs)','known_disequal(&state, self.0, *lhs, *rhs, self.1)')
s=s.replace('    rhs: Value,\n) -> Result<bool, Error> {\n    let mut sorts','    rhs: Value,\n    allow_reverse: bool,\n) -> Result<bool, Error> {\n    let mut sorts',1)
s=s.replace('let reverse = !name.starts_with("@disequality-")','let reverse = allow_reverse && !name.starts_with("@disequality-")',1)
p.write_text(s)
# Keep the exact private witness but permit removing its downstream union.
p=Path('/private/tmp/eggcc-parts32-candidate/dag_in_context/src/lib.rs');s=p.read_text();s=s.replace('writeln!(printed, "(union {predicate_var} {false_var})").unwrap();','if std::env::var("EGGCC_SCOPED_MODE").as_deref() != Ok("consumer-off") {\n                writeln!(printed, "(union {predicate_var} {false_var})").unwrap();\n            }')
# Actual existing false-If rule knockout, separate from the private consumer.
s=s.replace('include_str!("optimizations/non_weakly_linear.egg"),','&if std::env::var("EGGCC_SCOPED_MODE").as_deref() == Ok("if-consumer-off") {\n            include_str!("optimizations/non_weakly_linear.egg").replace("(= pred (Const (Bool false) _ty ctx))", "(= pred (Const (Bool false) _ty ctx)) (Parts32FalseIfEnabled)")\n        } else { include_str!("optimizations/non_weakly_linear.egg").to_owned() },')
# define the never-seeded knockout relation in both modes, so only rule eligibility differs.
s=s.replace('include_str!("schema.egg"),','concat!(include_str!("schema.egg"), "\\n(relation Parts32FalseIfEnabled ())\\n"),',1)
p.write_text(s)
