//! A replacement relational backend for the existing term encoder.
//!
//! [`Backend`] owns storage, planning and action execution, with Rust simulation
//! and Vulkan implementations. Opaque primitives and merge callbacks use a host
//! ABI. [`Matcher`] retains the earlier join-only experiment for comparison.

mod columns;
mod device;
mod device_actions;
mod runtime;
mod storage;
pub use runtime::{Backend, BackendStatistics};

/// Representation bound when no smaller optional row guard is requested.
/// Device allocation limits apply independently; u32::MAX is a reserved marker.
pub const MAX_ROW_COUNT: usize = (u32::MAX - 1) as usize;

use std::sync::{
    Arc,
    atomic::{AtomicUsize, Ordering},
};

use egglog_core_relations::{MatchBackend, MatchRelation};

pub use device::{AdapterMode, DeviceJoin};

/// A bulk matcher with either software reference joins or Vulkan compute joins.
pub struct Matcher {
    device: Option<Arc<DeviceJoin>>,
    max_rows: usize,
    plans: AtomicUsize,
    joins: AtomicUsize,
    fallbacks: AtomicUsize,
}

/// Counters are shared across cloned e-graphs using this matcher.
#[derive(Debug, Clone, Copy)]
pub struct Statistics {
    pub plans: usize,
    pub joins: usize,
    pub fallbacks: usize,
}

impl Matcher {
    /// Reference implementation of the same bulk matching contract; no driver
    /// or GPU is needed. This does not model GPU performance.
    pub fn simulated(max_rows: usize) -> Self {
        Self::new(None, max_rows)
    }

    pub fn vulkan(mode: AdapterMode, max_rows: usize) -> anyhow::Result<Self> {
        Ok(Self::new(Some(Arc::new(DeviceJoin::new(mode)?)), max_rows))
    }

    fn new(device: Option<Arc<DeviceJoin>>, max_rows: usize) -> Self {
        Self {
            device,
            max_rows,
            plans: AtomicUsize::new(0),
            joins: AtomicUsize::new(0),
            fallbacks: AtomicUsize::new(0),
        }
    }

    pub fn adapter(&self) -> &str {
        self.device
            .as_ref()
            .map_or("CPU reference simulator", |d| d.name())
    }

    pub fn statistics(&self) -> Statistics {
        Statistics {
            plans: self.plans.load(Ordering::Relaxed),
            joins: self.joins.load(Ordering::Relaxed),
            fallbacks: self.fallbacks.load(Ordering::Relaxed),
        }
    }

    fn evaluate_inner(&self, mut atoms: Vec<MatchRelation>) -> Result<MatchRelation, String> {
        let mut variables: Vec<_> = atoms
            .iter()
            .flat_map(|a| a.variables.iter().copied())
            .collect();
        variables.sort_unstable();
        variables.dedup();
        if atoms.iter().any(|a| a.rows.is_empty()) {
            return Ok(MatchRelation {
                variables,
                rows: vec![],
            });
        }
        if atoms.iter().any(|a| a.rows.len() > self.max_rows) {
            return Err("input exceeds the experimental bulk row limit".into());
        }
        atoms.sort_by_key(|a| a.rows.len());
        let mut result = if atoms.is_empty() {
            MatchRelation {
                variables: vec![],
                rows: vec![vec![]],
            }
        } else {
            atoms.remove(0)
        };
        while !atoms.is_empty() {
            let connected = atoms
                .iter()
                .any(|a| a.variables.iter().any(|v| result.variables.contains(v)));
            let mut best: Option<ReferenceCandidate> = None;
            for (i, right) in atoms.iter_mut().enumerate() {
                let keys: Vec<_> = result
                    .variables
                    .iter()
                    .enumerate()
                    .filter_map(|(l, v)| {
                        right.variables.iter().position(|r| r == v).map(|r| (l, r))
                    })
                    .collect();
                if connected && keys.is_empty() {
                    continue;
                }
                right.rows.sort_unstable_by(|a, b| {
                    keys.iter()
                        .map(|&(_, r)| a[r])
                        .cmp(keys.iter().map(|&(_, r)| b[r]))
                });
                let plan = plan_reference_join(&result, right, &keys)?;
                if best.as_ref().is_none_or(|old| plan.rows < old.plan.rows) {
                    best = Some(ReferenceCandidate {
                        atom: i,
                        keys,
                        plan,
                    });
                }
                if best
                    .as_ref()
                    .is_some_and(|candidate| candidate.plan.rows == 0)
                {
                    break;
                }
            }
            let ReferenceCandidate {
                atom: next,
                keys,
                plan,
            } = best.unwrap();
            let right = atoms.remove(next);
            let pairs = if let Some(device) = &self.device {
                device.join(&result, &right, &keys, self.max_rows)?
            } else {
                reference_join(plan, self.max_rows).map_err(|error| {
                    format!(
                        "{error}; joining {} rows {:?} with {} rows {:?}",
                        result.rows.len(),
                        result.variables,
                        right.rows.len(),
                        right.variables
                    )
                })?
            };
            self.joins.fetch_add(1, Ordering::Relaxed);
            let extra: Vec<_> = right
                .variables
                .iter()
                .enumerate()
                .filter(|(_, v)| !result.variables.contains(v))
                .map(|(i, _)| i)
                .collect();
            let mut rows = Vec::with_capacity(pairs.len());
            for [l, r] in pairs {
                let mut row = result.rows[l as usize].clone();
                row.extend(extra.iter().map(|&i| right.rows[r as usize][i]));
                rows.push(row);
            }
            result
                .variables
                .extend(extra.iter().map(|&i| right.variables[i]));
            rows.sort_unstable();
            rows.dedup();
            result.rows = rows;
            if result.rows.is_empty() {
                return Ok(MatchRelation {
                    variables,
                    rows: vec![],
                });
            }
        }
        Ok(result)
    }
}

impl MatchBackend for Matcher {
    fn evaluate(&self, atoms: Vec<MatchRelation>) -> Result<MatchRelation, String> {
        self.plans.fetch_add(1, Ordering::Relaxed);
        self.evaluate_inner(atoms)
    }

    fn on_fallback(&self, _reason: &str) {
        self.fallbacks.fetch_add(1, Ordering::Relaxed);
    }
}

struct ReferencePlan {
    ranges: Vec<(usize, usize)>,
    rows: usize,
}

struct ReferenceCandidate {
    atom: usize,
    keys: Vec<(usize, usize)>,
    plan: ReferencePlan,
}

fn plan_reference_join(
    left: &MatchRelation,
    right: &MatchRelation,
    keys: &[(usize, usize)],
) -> Result<ReferencePlan, String> {
    let mut ranges = Vec::with_capacity(left.rows.len());
    let mut rows = 0usize;
    for row in &left.rows {
        let cmp = |r: &Vec<_>| {
            keys.iter()
                .map(|&(_, j)| r[j])
                .cmp(keys.iter().map(|&(i, _)| row[i]))
        };
        let start = right.rows.partition_point(|r| cmp(r).is_lt());
        let end = right.rows.partition_point(|r| !cmp(r).is_gt());
        rows = rows
            .checked_add(end - start)
            .ok_or("join cardinality overflow")?;
        ranges.push((start, end));
    }
    Ok(ReferencePlan { ranges, rows })
}

fn reference_join(plan: ReferencePlan, max_rows: usize) -> Result<Vec<[u32; 2]>, String> {
    if plan.rows > max_rows {
        return Err(format!(
            "join exceeds the experimental bulk row limit ({}/{max_rows} rows)",
            plan.rows
        ));
    }
    let mut pairs = Vec::with_capacity(plan.rows);
    for (l, (start, end)) in plan.ranges.into_iter().enumerate() {
        for r in start..end {
            pairs.push([
                u32::try_from(l).map_err(|e| e.to_string())?,
                u32::try_from(r).map_err(|e| e.to_string())?,
            ]);
        }
    }
    Ok(pairs)
}
