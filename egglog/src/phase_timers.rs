//! TEMPORARY diagnostic timers. Not part of the shipped API.
//!
//! Accumulates nanoseconds into named global counters so a run can be broken
//! down without a sampling profiler. Enable the dump with `EGGLOG_PHASE_TIMERS=1`.

use std::sync::atomic::{AtomicU64, Ordering};
use std::time::Instant;

macro_rules! counters {
    ($($name:ident),* $(,)?) => {
        $(pub static $name: AtomicU64 = AtomicU64::new(0);)*
        #[allow(clippy::disallowed_macros)]
        pub fn dump() {
            if std::env::var("EGGLOG_PHASE_TIMERS").is_err() {
                return;
            }
            eprintln!("--- phase timers (ms) ---");
            $(eprintln!(
                "{:>28}  {:>10.1}",
                stringify!($name),
                $name.load(Ordering::Relaxed) as f64 / 1e6
            );)*
            eprintln!(
                "{:>28}  {:>10.1}",
                "RULESET_BUILD_per_iteration",
                egglog_bridge::RULESET_BUILD_NS.load(Ordering::Relaxed) as f64 / 1e6
            );
            eprintln!(
                "{:>28}  {:>10}",
                "count:N_ENCODED_CMDS",
                N_ENCODED_CMDS.load(Ordering::Relaxed)
            );
            eprintln!(
                "{:>28}  {:>10}",
                "count:N_RULES_ADDED",
                N_RULES_ADDED.load(Ordering::Relaxed)
            );
        }
    };
}

counters!(
    PARSE_TEXT_TO_AST,
    RESOLVE_COMMAND,
    RUN_COMMAND,
    DECLARE_FUNCTION,
    BACKEND_ADD_RULE,
    TYPECHECK_ORIGINAL,
    ENCODER_ADD_TERM_ENCODING,
    TYPECHECK_ENCODED,
    DESUGAR_ENCODED,
    EXTRACT_ROOT,
    PROOF_STORE_FROM_TERM,
    PROOF_REMOVE_GLOBALS,
    PROOF_SIMPLIFY,
);

/// Counts (not nanos): how many encoded commands/rules the pipeline processed.
pub static N_ENCODED_CMDS: AtomicU64 = AtomicU64::new(0);
pub static N_RULES_ADDED: AtomicU64 = AtomicU64::new(0);

/// Time `f`, adding the elapsed nanos to `counter`.
pub fn time<R>(counter: &'static AtomicU64, f: impl FnOnce() -> R) -> R {
    let start = Instant::now();
    let result = f();
    counter.fetch_add(start.elapsed().as_nanos() as u64, Ordering::Relaxed);
    result
}
