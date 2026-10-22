//! Checking certificates produced outside this crate against a source program.
//!
//! The Lean model in `semantics/` lifts the provenance of its compiled programs back
//! to source-level proof trees, and exports each as a certificate: the tree's nodes
//! in postorder with shared subtrees, each stating an equality and justifying it by
//! nodes before it. [`check_certificates`] replays every node through this crate's
//! proof checker, so one proof is judged by both implementations.

use crate::{
    EGraph, TermDag, TermId,
    ast::{Literal, ResolvedNCommand},
    proofs::proof_format::{Justification, Proof, ProofId, ProofStore, Proposition},
    util::{HashMap, HashSet, IndexMap},
};
use egglog_numeric_id::NumericId;
use serde_json::Value;

/// How this crate's checker judged one certificate, beside its producer's verdict.
#[derive(Debug)]
pub struct CertificateVerdict {
    pub case: String,
    pub certificate: usize,
    /// The producer's verdict.
    pub expected: bool,
    pub accepted: bool,
    /// Why the certificate was rejected.
    pub rejection: Option<String>,
}

/// Check the certificates in `json`: an array of cases, each an egglog `program`
/// with `certificates` of `nodes` (`lhs`, `rhs`, `reason`), a `root`, and the
/// producer's `accepted` verdict. A term is `["f", [args…]]`, `{"int": n}` or
/// `{"bool": b}`; a reason names its `kind` and the earlier nodes it uses, and a
/// `rule` reason names the rule and lists its `subst` as `[variable, term]` pairs.
///
/// Fails when the file is malformed or a program does not resolve. A malformed
/// certificate is a rejection.
pub fn check_certificates(json: &str) -> Result<Vec<CertificateVerdict>, String> {
    let cases = serde_json::from_str::<Value>(json).map_err(|e| e.to_string())?;
    let cases = cases
        .as_array()
        .ok_or("the file is not an array of cases")?;
    let mut verdicts = vec![];
    for case in cases {
        let name = string(case, "case")?;
        let program = resolve(string(case, "program")?).map_err(|e| format!("{name}: {e}"))?;
        for (certificate, value) in array(case, "certificates")?.iter().enumerate() {
            let expected = field(value, "accepted")?
                .as_bool()
                .ok_or_else(|| format!("{name}: accepted is not a boolean"))?;
            let rejection = check_certificate(&program, value).err();
            verdicts.push(CertificateVerdict {
                case: name.to_string(),
                certificate,
                expected,
                accepted: rejection.is_none(),
                rejection,
            });
        }
    }
    Ok(verdicts)
}

/// The program as the proof checker reads it: resolved in proof mode, before
/// proof instrumentation.
fn resolve(source: &str) -> Result<Vec<ResolvedNCommand>, crate::Error> {
    let mut egraph = EGraph::default();
    let commands = egraph.parse_program(None, source)?;
    egraph.set_proof_checking_program(commands, false)?;
    Ok(egraph.proof_check_program)
}

fn check_certificate(program: &[ResolvedNCommand], certificate: &Value) -> Result<(), String> {
    let nodes = array(certificate, "nodes")?;
    let root = index(certificate, "root")?;
    if root >= nodes.len() {
        return Err(format!("root {root} is not a node"));
    }
    let mut dag = TermDag::default();
    let mut proofs = Vec::with_capacity(nodes.len());
    for (at, node) in nodes.iter().enumerate() {
        let lhs = term(&mut dag, field(node, "lhs")?)?;
        let rhs = term(&mut dag, field(node, "rhs")?)?;
        let justification = justification(&mut dag, field(node, "reason")?, at)
            .map_err(|e| format!("node {at}: {e}"))?;
        proofs.push(Proof {
            proposition: Proposition::new(lhs, rhs),
            justification,
        });
    }
    let mut store = ProofStore::new(dag, HashMap::default(), HashSet::default());
    let ids: Vec<ProofId> = proofs
        .into_iter()
        .enumerate()
        .map(|(at, proof)| {
            let id = store.id_to_proof.push(proof);
            debug_assert_eq!(id.index(), at);
            id
        })
        .collect();
    store
        .check_proofs(&ids, program)
        .map(|_| ())
        .map_err(|e| e.to_string())
}

/// A justification over nodes before `at`, which are the proof ids already pushed.
fn justification(dag: &mut TermDag, reason: &Value, at: usize) -> Result<Justification, String> {
    let earlier = |i: usize| {
        if i < at {
            Ok(ProofId::from_usize(i))
        } else {
            Err(format!("node {i} is not an earlier node"))
        }
    };
    Ok(match string(reason, "kind")? {
        "fiat" => Justification::Fiat,
        "symm" => Justification::Sym(earlier(index(reason, "proof")?)?),
        "trans" => Justification::Trans(
            earlier(index(reason, "left")?)?,
            earlier(index(reason, "right")?)?,
        ),
        "congr" => Justification::Congr {
            proof: earlier(index(reason, "base")?)?,
            child_index: index(reason, "index")?,
            child_proof: earlier(index(reason, "child")?)?,
        },
        "rule" => {
            let mut substitution = IndexMap::default();
            for binding in array(reason, "subst")? {
                let Some([Value::String(var), value]) = binding.as_array().map(Vec::as_slice)
                else {
                    return Err("a binding is not [variable, term]".to_string());
                };
                substitution.insert(var.clone(), term(dag, value)?);
            }
            let premise_proofs = array(reason, "premises")?
                .iter()
                .map(|premise| earlier(index_of(premise)?))
                .collect::<Result<_, _>>()?;
            Justification::Rule {
                name: string(reason, "rule")?.to_string(),
                premise_proofs,
                substitution,
            }
        }
        kind => return Err(format!("unsupported justification {kind}")),
    })
}

fn term(dag: &mut TermDag, value: &Value) -> Result<TermId, String> {
    match value {
        Value::Array(parts) => match parts.as_slice() {
            [Value::String(head), Value::Array(args)] => {
                let children = args
                    .iter()
                    .map(|arg| term(dag, arg))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(dag.app(head.clone(), children))
            }
            _ => Err("an application is not [head, [args…]]".to_string()),
        },
        Value::Object(fields) => {
            if let Some(n) = fields.get("int").and_then(Value::as_i64) {
                Ok(dag.lit(Literal::Int(n)))
            } else if let Some(b) = fields.get("bool").and_then(Value::as_bool) {
                Ok(dag.lit(Literal::Bool(b)))
            } else {
                Err("a literal is not {int} or {bool}".to_string())
            }
        }
        _ => Err("a term is not an application or a literal".to_string()),
    }
}

fn field<'a>(value: &'a Value, name: &str) -> Result<&'a Value, String> {
    value.get(name).ok_or_else(|| format!("missing {name}"))
}

fn array<'a>(value: &'a Value, name: &str) -> Result<&'a Vec<Value>, String> {
    field(value, name)?
        .as_array()
        .ok_or_else(|| format!("{name} is not an array"))
}

fn string<'a>(value: &'a Value, name: &str) -> Result<&'a str, String> {
    field(value, name)?
        .as_str()
        .ok_or_else(|| format!("{name} is not a string"))
}

fn index(value: &Value, name: &str) -> Result<usize, String> {
    index_of(field(value, name)?).map_err(|_| format!("{name} is not an index"))
}

fn index_of(value: &Value) -> Result<usize, String> {
    value
        .as_u64()
        .and_then(|n| usize::try_from(n).ok())
        .ok_or_else(|| "not an index".to_string())
}
