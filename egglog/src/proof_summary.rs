//! Optional execution counters for proof-production and validation runs.

use std::path::Path;
use std::sync::{Arc, Mutex};

#[derive(Default)]
struct Counts {
    depth: usize,
    checks: usize,
    extractions: usize,
    produced: usize,
    verified: usize,
}

/// Execution history shared across graph clones and push/pop snapshots.
/// Install this extension state only when requesting a machine-readable summary.
#[derive(Clone, Default)]
pub struct ProofSummary(Arc<Mutex<Counts>>);

/// A nested source execution; internal lowering queries are not source requests.
pub struct ProofSummaryScope {
    summary: ProofSummary,
    /// Whether this is the outermost source execution.
    pub source: bool,
}

impl Drop for ProofSummaryScope {
    fn drop(&mut self) {
        self.summary.0.lock().unwrap().depth -= 1;
    }
}

impl ProofSummary {
    /// Enter source execution while retaining counts through nested queries and snapshots.
    pub fn enter(&self) -> ProofSummaryScope {
        let mut counts = self.0.lock().unwrap();
        let source = counts.depth == 0;
        counts.depth += 1;
        ProofSummaryScope {
            summary: self.clone(),
            source,
        }
    }

    /// Record a dispatched source request; extraction is distinct from its internal check.
    pub fn request(&self, extraction: bool) {
        let mut counts = self.0.lock().unwrap();
        if extraction {
            counts.extractions += 1;
        } else {
            counts.checks += 1;
        }
    }

    /// Record completed certificates once, irrespective of repeated verification passes.
    pub fn certificates(&self, count: usize, verified: bool) {
        let mut counts = self.0.lock().unwrap();
        counts.produced += count;
        if verified {
            counts.verified += count;
        }
    }

    /// Write completed execution history; failures retain their completed prefix.
    pub fn write(&self, path: &Path, success: bool) -> std::io::Result<()> {
        let counts = self.0.lock().unwrap();
        let summary = serde_json::json!({
            "schema_version": 1,
            "success": success,
            "check_requests": counts.checks,
            "extraction_requests": counts.extractions,
            "produced_certificates": counts.produced,
            "verified_certificates": counts.verified,
        });
        serde_json::to_writer(std::fs::File::create(path)?, &summary)?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::EGraph;

    #[test]
    fn executed_requests_and_certificates_survive_scope_rollback() {
        for verify in [false, true] {
            let mut graph = if verify {
                EGraph::default().with_proofs_enabled().with_proof_testing()
            } else {
                EGraph::default().with_proof_extraction()
            };
            let summary = graph.extension_state_or_default::<ProofSummary>().clone();
            graph
                .parse_and_run_program(
                    None,
                    "(datatype E (A) (B)) (let a (A)) (union a (B))
                 (check (= a (B))) (extract a)
                 (push) (check (= a (A))) (pop)
                 (fail (check (= a (B))))",
                )
                .unwrap_err();
            let counts = summary.0.lock().unwrap();
            assert_eq!((counts.checks, counts.extractions), (2, 1));
            assert_eq!(counts.produced, 3);
            assert_eq!(counts.verified, if verify { 3 } else { 0 });
            assert_eq!(counts.depth, 0);
        }
    }

    #[test]
    fn included_source_requests_count_without_counting_internal_queries_or_fail() {
        let path = std::env::temp_dir().join(format!(
            "egglog-proof-summary-{}-{}.egg",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        std::fs::write(&path, "(check (= a (B))) (extract a)").unwrap();
        let mut graph = EGraph::default().with_proofs_enabled().with_proof_testing();
        let summary = graph.extension_state_or_default::<ProofSummary>().clone();
        let result = graph.parse_and_run_program(None, &format!(
            "(datatype E (A) (B) (C)) (let a (A)) (union a (B)) (include {path:?}) (fail (check (= a (C))))"));
        std::fs::remove_file(path).unwrap();
        result.unwrap();
        let counts = summary.0.lock().unwrap();
        assert_eq!(
            (
                counts.checks,
                counts.extractions,
                counts.produced,
                counts.verified
            ),
            (1, 1, 2, 2)
        );
        assert_eq!(counts.depth, 0);
    }
}
