//! The artifact's non-saturating NEE algorithm with Egg equality explanations.
//! The four original author drivers remain byte-identical to the artifact.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use egg::{EGraph, Explanation, Pattern, RecExpr, Rewrite, Searcher, Subst, SymbolLang};

#[global_allocator]
static ALLOCATOR: benchmark_memory::LimitedAllocator = benchmark_memory::LimitedAllocator;

const NUMERALS: [&str; 5] = ["1", "2", "3", "4", "5"];

#[derive(Clone, Copy, PartialEq, Eq)]
enum Mode {
    Extract,
    Check,
}

#[derive(Clone, Copy)]
enum Witness {
    Initial(usize, usize),
    Input(usize),
}

struct Certificate {
    witness: Witness,
    left: RecExpr<SymbolLang>,
    right: RecExpr<SymbolLang>,
    explanation: Explanation<SymbolLang>,
}

impl Certificate {
    /// Bind the encoded contradiction to an input disequality and exact equality axioms.
    fn check(
        &mut self,
        expressions: &[&str],
        equalities: usize,
        disequalities: usize,
    ) -> Result<(), String> {
        let (left, right) = match self.witness {
            Witness::Initial(x, y) if x < y && y < 4 => (NUMERALS[x], NUMERALS[y]),
            Witness::Input(index) if index < disequalities => {
                let offset = 2 * (equalities + index);
                (expressions[offset], expressions[offset + 1])
            }
            _ => return Err("certificate does not name an asserted disequality".into()),
        };
        let expected_left: RecExpr<SymbolLang> =
            left.parse().map_err(|e| format!("invalid witness: {e}"))?;
        let expected_right: RecExpr<SymbolLang> =
            right.parse().map_err(|e| format!("invalid witness: {e}"))?;
        if self.left != expected_left || self.right != expected_right {
            return Err("certificate endpoints differ from its input disequality".into());
        }

        let flat = self.explanation.make_flat_explanation();
        if flat.first().map(|term| term.get_recexpr()) != Some(self.left.clone())
            || flat.last().map(|term| term.get_recexpr()) != Some(self.right.clone())
        {
            return Err("explanation endpoints differ from its contradiction witness".into());
        }
        let mut pending: Vec<_> = flat.iter().collect();
        let mut names = BTreeSet::new();
        while let Some(term) = pending.pop() {
            names.extend(term.forward_rule.iter().chain(&term.backward_rule).copied());
            pending.extend(&term.children);
        }
        let mut axioms: Vec<Rewrite<SymbolLang, ()>> = Vec::with_capacity(names.len());
        for name in names {
            let index: usize = name
                .as_str()
                .strip_prefix("input-equality-")
                .and_then(|text| text.parse().ok())
                .filter(|&index| {
                    index < equalities && name.as_str() == format!("input-equality-{index}")
                })
                .ok_or_else(|| format!("unknown explanation reason: {name}"))?;
            let lhs: RecExpr<SymbolLang> = expressions[2 * index]
                .parse()
                .map_err(|e| format!("invalid input axiom: {e}"))?;
            let rhs: RecExpr<SymbolLang> = expressions[2 * index + 1]
                .parse()
                .map_err(|e| format!("invalid input axiom: {e}"))?;
            axioms.push(Rewrite::new(
                name,
                Pattern::from(&lhs),
                Pattern::from(&rhs),
            )?);
        }
        // Egg accepts missing rule names, so every reason was whitelisted above.
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            self.explanation.check_proof(&axioms);
        }))
        .map_err(|_| "explanation does not follow its input equality axioms".into())
    }
}

#[derive(Default)]
struct Summary {
    check_requests: usize,
    produced_certificates: usize,
    verified_certificates: usize,
}

impl Summary {
    fn write(&self, path: &Path, success: bool) -> std::io::Result<()> {
        // All variable fields are booleans or integers, so no string escaping is needed.
        std::fs::write(
            path,
            format!(
                "{{\"schema_version\":1,\"success\":{success},\"check_requests\":{},\"extraction_requests\":0,\"produced_certificates\":{},\"verified_certificates\":{}}}\n",
                self.check_requests, self.produced_certificates, self.verified_certificates,
            ),
        )
    }
}

struct Outcome {
    contradiction: bool,
    nodes: usize,
    classes: usize,
    query_time: Duration,
    total_time: Duration,
    certificate: Option<Certificate>,
}

fn run(
    content: &str,
    equalities: usize,
    disequalities: usize,
    mode: Mode,
    summary: &mut Option<Summary>,
) -> Result<Outcome, String> {
    // Preserve the original whole-file read/split and equality-first assertion order.
    let expressions: Vec<_> = content.split('\n').collect();
    let needed = equalities
        .checked_add(disequalities)
        .and_then(|n| n.checked_mul(2));
    if needed.is_none_or(|needed| needed > expressions.len()) {
        return Err("not enough expressions to fill the e-graph".into());
    }
    let mut graph = EGraph::<SymbolLang, ()>::default()
        .with_explanations_enabled()
        .without_explanation_length_optimization();
    let mut assumptions = Vec::with_capacity(disequalities + 6);
    // The released loop omits numeral 5; retain its exact six initial constraints.
    for (x, &left) in NUMERALS.iter().enumerate() {
        for (y, &right) in NUMERALS.iter().enumerate().take(4).skip(x + 1) {
            graph.add_expr(&format!("(ne {left} {right})").parse().unwrap());
            assumptions.push((Witness::Initial(x, y), left, right));
        }
    }
    let start = Instant::now();
    for index in 0..equalities {
        let lhs: RecExpr<SymbolLang> = expressions[2 * index]
            .parse()
            .map_err(|e| format!("invalid equality {index}: {e}"))?;
        let rhs: RecExpr<SymbolLang> = expressions[2 * index + 1]
            .parse()
            .map_err(|e| format!("invalid equality {index}: {e}"))?;
        graph.union_instantiations(
            &Pattern::from(&lhs).ast,
            &Pattern::from(&rhs).ast,
            &Subst::default(),
            format!("input-equality-{index}"),
        );
    }
    for index in 0..disequalities {
        let offset = 2 * (equalities + index);
        let (left, right) = (expressions[offset], expressions[offset + 1]);
        let expression: RecExpr<SymbolLang> = format!("(ne {left} {right})")
            .parse()
            .map_err(|e| format!("invalid disequality {index}: {e}"))?;
        graph.add_expr(&expression);
        assumptions.push((Witness::Input(index), left, right));
    }
    graph.rebuild();
    let before = (graph.total_size(), graph.number_of_classes());
    let query_start = Instant::now();
    *summary = Some(Summary {
        check_requests: 1,
        ..Summary::default()
    });
    let contradiction = !"(ne ?a ?a)"
        .parse::<Pattern<_>>()
        .unwrap()
        .search(&graph)
        .is_empty();
    let mut certificate = None;
    if contradiction {
        for (witness, left, right) in assumptions {
            let lhs: RecExpr<SymbolLang> =
                left.parse().map_err(|e| format!("invalid witness: {e}"))?;
            let rhs: RecExpr<SymbolLang> =
                right.parse().map_err(|e| format!("invalid witness: {e}"))?;
            let (Some(a), Some(b)) = (graph.lookup_expr(&lhs), graph.lookup_expr(&rhs)) else {
                continue;
            };
            if graph.find(a) == graph.find(b) {
                let mut explanation = graph.explain_equivalence(&lhs, &rhs);
                explanation.make_flat_explanation();
                certificate = Some(Certificate {
                    witness,
                    left: lhs,
                    right: rhs,
                    explanation,
                });
                break;
            }
        }
        let proof = certificate
            .as_mut()
            .ok_or("contradiction has no asserted disequality witness")?;
        summary.as_mut().unwrap().produced_certificates = 1;
        if mode == Mode::Check {
            proof.check(&expressions, equalities, disequalities)?;
            summary.as_mut().unwrap().verified_certificates = 1;
        }
    }
    if before != (graph.total_size(), graph.number_of_classes()) {
        return Err("contradiction explanation changed the logical e-graph".into());
    }
    Ok(Outcome {
        contradiction,
        nodes: before.0,
        classes: before.1,
        query_time: query_start.elapsed(),
        total_time: start.elapsed(),
        certificate,
    })
}

fn main() {
    let args: Vec<_> = benchmark_memory::configure(std::env::args_os())
        .into_iter()
        .map(|arg| {
            arg.into_string()
                .expect("native workload arguments must be UTF-8")
        })
        .collect();
    let usage = "usage: egg-nee-proofs INPUT.in EQUALITIES DISEQUALITIES --proof-mode extract|check [--proof-summary PATH]";
    if args.len() == 2 && matches!(args[1].as_str(), "--help" | "-h") {
        println!("{usage}\nNative memory option: --memory-limit-bytes N");
        return;
    }
    let parsed = (|| -> Result<_, String> {
        if args.len() < 6 {
            return Err(usage.into());
        }
        let equalities = args[2].parse().map_err(|_| usage)?;
        let disequalities = args[3].parse().map_err(|_| usage)?;
        let mut mode = None;
        let mut summary_path = None;
        let mut options = args[4..].chunks_exact(2);
        for pair in &mut options {
            match pair[0].as_str() {
                "--proof-mode" if mode.is_none() => {
                    mode = Some(match pair[1].as_str() {
                        "extract" => Mode::Extract,
                        "check" => Mode::Check,
                        _ => return Err(usage.into()),
                    })
                }
                "--proof-summary" if summary_path.is_none() => {
                    summary_path = Some(PathBuf::from(&pair[1]))
                }
                _ => return Err(usage.into()),
            }
        }
        if !options.remainder().is_empty() {
            return Err(usage.into());
        }
        Ok((equalities, disequalities, mode.ok_or(usage)?, summary_path))
    })();
    let (equalities, disequalities, mode, summary_path) = parsed.unwrap_or_else(|error| {
        eprintln!("{error}");
        std::process::exit(2)
    });
    let mut summary = None;
    let result = std::fs::read_to_string(&args[1])
        .map_err(|e| format!("could not read {}: {e}", args[1]))
        .and_then(|content| run(&content, equalities, disequalities, mode, &mut summary));
    if let (Some(path), Some(summary)) = (summary_path, summary) {
        summary
            .write(&path, result.is_ok())
            .unwrap_or_else(|error| {
                eprintln!("could not write proof summary: {error}");
                std::process::exit(2)
            });
    }
    let outcome = result.unwrap_or_else(|error| {
        eprintln!("{error}");
        std::process::exit(2)
    });
    std::hint::black_box(&outcome.certificate);
    println!("method,base,diseq_num,contradiction,time_to_find_contradiction,full_time,number_nodes,number_classes,ratio_nodes_classes");
    println!(
        "nee-proofs,{equalities},{disequalities:0>8},{},{:.2?},{:.2?},{},{},{}",
        if outcome.contradiction { "Y" } else { "N" },
        outcome.query_time,
        outcome.total_time,
        outcome.nodes,
        outcome.classes,
        outcome.nodes as f32 / outcome.classes as f32,
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn contradiction_and_consistent_canaries_keep_query_semantics() {
        for mode in [Mode::Extract, Mode::Check] {
            for (content, contradiction) in [("1\n2\n", true), ("1\n1\n", false)] {
                let mut summary = None;
                let outcome = run(content, 1, 0, mode, &mut summary).unwrap();
                assert_eq!(outcome.contradiction, contradiction);
                let summary = summary.unwrap();
                assert_eq!(summary.check_requests, 1);
                assert_eq!(summary.produced_certificates, usize::from(contradiction));
                assert_eq!(
                    summary.verified_certificates,
                    usize::from(contradiction && mode == Mode::Check)
                );
            }
        }
    }

    #[test]
    fn congruence_proof_is_bound_to_the_original_disequality_and_axioms() {
        let content = "(f 1)\n(f 2)\n(g (f 1) 3)\n(g (f 2) 3)\n";
        let expressions: Vec<_> = content.split('\n').collect();
        let mut outcome = run(content, 1, 1, Mode::Extract, &mut None).unwrap();
        let certificate = outcome.certificate.as_mut().unwrap();
        certificate.check(&expressions, 1, 1).unwrap();
        let mut wrong_axioms = expressions.clone();
        wrong_axioms[1] = "(f 3)";
        assert!(certificate.check(&wrong_axioms, 1, 1).is_err());
        certificate.witness = Witness::Input(9);
        assert!(certificate.check(&expressions, 1, 1).is_err());
        certificate.witness = Witness::Input(0);
        certificate.right = "other".parse().unwrap();
        assert!(certificate.check(&expressions, 1, 1).is_err());
    }

    #[test]
    fn an_unknown_egg_reason_is_not_accepted_as_an_input_axiom() {
        let lhs: RecExpr<SymbolLang> = "1".parse().unwrap();
        let rhs: RecExpr<SymbolLang> = "2".parse().unwrap();
        let mut graph = EGraph::<SymbolLang, ()>::default().with_explanations_enabled();
        graph.union_instantiations(
            &Pattern::from(&lhs).ast,
            &Pattern::from(&rhs).ast,
            &Subst::default(),
            "untrusted",
        );
        graph.rebuild();
        let mut certificate = Certificate {
            witness: Witness::Initial(0, 1),
            explanation: graph.explain_equivalence(&lhs, &rhs),
            left: lhs,
            right: rhs,
        };
        assert!(certificate
            .check(&["1", "2"], 1, 0)
            .unwrap_err()
            .contains("unknown explanation reason"));
    }
}
